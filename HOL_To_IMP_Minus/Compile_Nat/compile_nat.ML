(*TODO: signature*)
structure Compile_Nat = struct

type compiled_const = { ret_reg : string, arg_regs : string list, compiled : term }

fun map_compiled f (c : compiled_const) =
  {ret_reg = #ret_reg c, arg_regs = #arg_regs c, compiled = f (#compiled c) }

structure Compiled_Consts = Generic_Data
(
  type T = compiled_const Symtab.table;
  val empty = Symtab.empty
  val merge = Symtab.join (K fst)
);

fun declare_compiled_const name compiled_const =
  Local_Theory.declaration {syntax = false, pervasive = false, pos = Position.thread_data ()}
    (fn phi =>
      let
        val compiled_const' = map_compiled (Morphism.term phi) compiled_const
      in
        Compiled_Consts.map (fn tab => Symtab.update_new (name, compiled_const') tab)
      end)

fun get_compiled_const context f_name =
  Compiled_Consts.get context
  |> (fn tab => Symtab.lookup tab f_name)
  |> the
  handle Option.Option => error ("Unknown compiled constant: " ^ quote f_name)

(* We index Ifs, Lets, Calls with unique numbers such that we can easily
   invent new register names without passing a context around *)
datatype tc_ast = If of int * (tc_ast * tc_ast * tc_ast) |
                  Number of int |
                  Arg of int |
                  Let of (int * (string * (tc_ast * tc_ast))) |
                  LetBound of int |
                  Call of int * ((string * typ) * tc_ast list) |
                  TailCall of tc_ast list

fun tc_ast_of_term (f_name, f_typ) f_args t =
  let
    fun fold_step a (index, args_ast) =
        let val (index', a_ast) = index_tc_ast index a
        in (index', a_ast :: args_ast) end

    and index_tc_ast index (Call (_, (g, args))) =
        let val (index', rev_args') = fold fold_step args (index, [])
        in (index' + 1, Call (index', (g, rev rev_args'))) end
      | index_tc_ast index (If (_, (c, e1, e2))) =
        let val (index', [e2', e1', c']) = fold fold_step [c, e1, e2] (index, [])
        in (index' + 1, If (index', (c', e1', e2'))) end
      | index_tc_ast index (Let (_, (x, (e1, e2)))) =
        let val (index', [e2', e1']) = fold fold_step [e1, e2] (index, [])
        in (index' + 1, Let (index', (x, (e1', e2')))) end
      | index_tc_ast index (TailCall args) =
        let val (index', rev_args') = fold fold_step args (index, [])
        in (index', TailCall (rev rev_args')) end
      | index_tc_ast index t = (index, t)

    fun build_tc_ast t =
      if can HOLogic.dest_number t then Number (HOLogic.dest_number t |> snd)
      else
        case Term.head_of t of
          \<^Const_>\<open>HOL.If _\<close> =>
            (case Term.args_of t of
              [c, e1, e2] => If (~1, @{apply 3} build_tc_ast (c, e1, e2))
            | _ => raise TERM ("Only fully applied if allowed, got:", [t]))
        | \<^Const>\<open>HOL.Let _ _\<close> =>
            (case Term.args_of t of
              [e1, Abs (x, _, e2)] => Let (~1, (x, @{apply 2} build_tc_ast (e1, e2)))
            | _ => raise TERM ("Only Let with a lambda is allowed, got:", [t]))
        | Bound i => LetBound i
        | Var ((n, _), t) => Arg (Library.find_index (fn v' => (n, t) = v') f_args)
        | Const (g_name, g_typ) =>
          if (g_name, g_typ) = (f_name, f_typ)
            then TailCall (map build_tc_ast (Term.args_of t))
            else Call (~1, ((g_name, g_typ), map build_tc_ast (Term.args_of t)))
        | h => raise TERM ("Unexpected head of term:", [h])
  in
    t |> build_tc_ast |> index_tc_ast 0 |> snd
  end

fun IMP_Minus_of_tc_ast (f_ret_name, f_arg_names) lookup_fn e =
  let
    fun f_arg_reg i = nth f_arg_names i |> HOLogic.mk_string

    fun mk_Seq es = fold_rev (fn e1 => fn e2 => \<^Const>\<open>tSeq for e1 e2\<close>) es \<^Const>\<open>tSKIP\<close>

    fun mk_N n = \<^Const>\<open>N for \<open>HOLogic.mk_number \<^typ>\<open>nat\<close> n\<close>\<close>

    fun go _ cont (Number i) = cont \<^Const>\<open>A for \<open>mk_N i\<close>\<close>
      | go _ cont (Arg i) = cont \<^Const>\<open>A for \<^Const>\<open>V for \<open>f_arg_reg i\<close>\<close>\<close>
      | go bounds cont (If (idx, (cond, e1, e2))) =
        let
          val cond_reg = "If_" ^ Int.toString idx |> HOLogic.mk_string
          val cond_IMP = go bounds (fn rhs => \<^Const>\<open>tAssign for cond_reg rhs\<close>) cond
          val (e1_IMP, e2_IMP) = @{apply 2} (go bounds cont) (e1, e2)
          val if_IMP = \<^Const>\<open>tIf for cond_reg e1_IMP e2_IMP\<close>
        in
          mk_Seq [cond_IMP, if_IMP]
        end
      | go bounds cont (Let (idx, (x, (e1, e2)))) =
        let
          val x_reg = x ^ "_" ^ Int.toString idx |> HOLogic.mk_string
          val e1_IMP = go bounds (fn rhs => \<^Const>\<open>tAssign for x_reg rhs\<close>) e1
          val e2_IMP = go (x_reg :: bounds) cont e2
        in
          mk_Seq [e1_IMP, e2_IMP]
        end
      | go bounds cont (LetBound i) = cont \<^Const>\<open>A for \<^Const>\<open>V for \<open>nth bounds i\<close>\<close>\<close>
      | go bounds _ (TailCall es) =
        let
          val es_IMP =
            map_index (fn (i, e) => go bounds (fn rhs => \<^Const>\<open>tAssign for \<open>f_arg_reg i\<close> rhs\<close>) e) es
        in
          mk_Seq (es_IMP @ [\<^Const>\<open>tTAIL\<close>])
        end
      | go bounds cont (Call (idx, ((g_name, g_typ), es))) =
        let
          fun mk_boperand bop (bop_side, e) =
            let
              val reg =
                Term.term_name bop ^ bop_side ^ "_" ^ Int.toString idx
                |> HOLogic.mk_string
            in
              (reg, go bounds (fn rhs => \<^Const>\<open>tAssign for reg rhs\<close>) e)
            end
          fun mk_bop bop (e1, e2) =
            let
              val ((lhs_reg, lhs_IMP), (rhs_reg, rhs_IMP)) =
                @{apply 2} (mk_boperand bop) (("Lhs", e1), ("Rhs", e2))
            in
              mk_Seq [ lhs_IMP, rhs_IMP
                     , cont (bop $ \<^Const>\<open>V for lhs_reg\<close> $ \<^Const>\<open>V for rhs_reg\<close>)
                     ]
            end
      in
        case (Const (g_name, g_typ), es) of
          (\<^Const>\<open>Groups.plus \<^typ>\<open>nat\<close>\<close>, [e1, e2]) => mk_bop \<^Const>\<open>Plus\<close> (e1, e2)
        | (\<^Const>\<open>Groups.minus \<^typ>\<open>nat\<close>\<close>, [e1, e2]) => mk_bop \<^Const>\<open>Sub\<close> (e1, e2)
        | _ =>
          let
            val g_compiled = lookup_fn g_name
            val g_ret = #ret_reg g_compiled
            fun g_arg_reg i = nth (#arg_regs g_compiled) i |> HOLogic.mk_string
            fun g_arg_cont i rhs = \<^Const>\<open>tAssign for \<open>g_arg_reg i\<close> rhs\<close>
            val g_args_IMP =
              map_index (fn (i, e) => go bounds (g_arg_cont i) e) es
          in
            g_args_IMP @
            [ \<^Const>\<open>tCall for \<open>#compiled g_compiled\<close> \<open>HOLogic.mk_string g_ret\<close>\<close>
            , cont \<^Const>\<open>A for \<^Const>\<open>V for \<open>HOLogic.mk_string g_ret\<close>\<close>\<close>
            ]
            |> mk_Seq
          end
      end
  in
    go [] (fn rhs => \<^Const>\<open>tAssign for \<open>HOLogic.mk_string f_ret_name\<close> rhs\<close>) e
  end

fun define_compiled compiled_binding compiled lthy =
  let
    val pos = Binding.pos_of compiled_binding

    val def_attrs =
      \<^named_theorems>\<open>compiled_const_defs\<close>
      |> Named_Theorems.add |> Attrib.internal pos o K

    val ((fv, (def_name, def_thm)), lthy') =
      Local_Theory.define ((compiled_binding, NoSyn),
                          ((Thm.def_binding compiled_binding, [def_attrs]), compiled))
                          lthy
    val _ =
      Proof_Display.print_consts true pos lthy' (K false) [Term.dest_Free fv]
    val _ =
      Proof_Display.print_theorem pos lthy' (def_name, [def_thm])
  in
    lthy'
  end

fun reflect_eq thm =
  case Thm.concl_of thm of
    \<^Const>\<open>Trueprop for \<^Const>\<open>HOL.eq _ for _ _\<close>\<close> => @{thm eq_reflection} OF [thm]
  | \<^Const>\<open>Pure.eq _ for _ _\<close> => thm
  | t => raise TERM ("Unexpected head of term:", [Term.head_of t])

val compiled_const_suffix_cfg =
  Attrib.setup_config_string \<^binding>\<open>compiled_const_suffix\<close> (K "IMP_tailcall")

fun compile_cmd f_def basenamepos_opt lthy =
  let
    val pos = Position.thread_data ()

    val f_def = reflect_eq f_def
    val (args, def_body) =
      Local_Defs.abs_def_rule lthy f_def
      |> Thm.rhs_of |> Thm.term_of |> Term.strip_abs

    val (f_name, f_typ) = f_def |> Thm.lhs_of |> Thm.term_of |> Term.head_of |> Term.dest_Const

    val f_IMP_namepos = the_default (Long_Name.base_name f_name, pos) basenamepos_opt

    val f_ret_name = fst f_IMP_namepos ^ "_ret"
    fun mk_arg_name arg_name = fst f_IMP_namepos ^ "_" ^ arg_name
    val f_args = map (@{apply 2 (1)} mk_arg_name) args
    val f_args_vars = map (Var o @{apply 2 (1)} (fn n => (n, 0))) f_args

    val simp_thy = empty_simpset lthy |> Proof_Context.theory_of
    val simp_thms = map reflect_eq @{thms assoc_right_tSeq.simps tseq.simps rm_tSKIP.simps}
    val rewrite = Raw_Simplifier.rewrite_term simp_thy simp_thms []
    val f_IMP =
         def_body
      |> curry Term.subst_bounds (rev f_args_vars)
      |> tc_ast_of_term (f_name, f_typ) f_args
      |> IMP_Minus_of_tc_ast (f_ret_name, map fst f_args) (get_compiled_const (Context.Proof lthy))
      |> (fn t => rewrite \<^Const>\<open>assoc_right_tSeq for \<^Const>\<open>rm_tSKIP for t\<close>\<close>)

    val f_IMP_binding =
      f_IMP_namepos
      |>> (fn n => n ^ "_" ^ Config.get lthy compiled_const_suffix_cfg)
      |> Binding.make
    val lthy' = define_compiled f_IMP_binding f_IMP lthy
    val f_IMP_const =
      Binding.name_of f_IMP_binding
      |> Proof_Context.read_const {proper = false, strict = false} lthy'
      |> (fn t => \<^Const>\<open>tailcall_to_IMP_Minus for t\<close>)

    val f_compiled = { ret_reg = f_ret_name, arg_regs = map fst f_args
                     , compiled = f_IMP_const}
  in
    lthy'
    |> declare_compiled_const f_name f_compiled
  end

local
  val parser = Parse.thm -- Scan.option (\<^keyword>\<open>basename\<close> |-- Parse.name_position)
in
  val _ = Outer_Syntax.local_theory
    \<^command_keyword>\<open>compile_nat\<close>
    "compile and declare a constant"
    (parser >> (fn ((thm_ref, _), namepos_opt) => fn lthy =>
      let val thm = Proof_Context.get_fact lthy thm_ref |> the_single
      in compile_cmd thm namepos_opt lthy end))
end

local
  val parser =
    Parse.const --
    (\<^keyword>\<open>return_register\<close> |-- Parse.string) --
    (\<^keyword>\<open>argument_registers\<close> |-- Scan.repeat Parse.string) --
    (\<^keyword>\<open>compiled\<close> |-- Parse.term)
in
  val _ = Outer_Syntax.local_theory
    \<^command_keyword>\<open>declare_compiled_const\<close>
    "declare an already compiled constant"
    (parser >> (fn (((const, ret_reg), arg_regs), compiled) => fn lthy =>
      let
        val (const_name, const_ty) =
          Proof_Context.read_const {proper = false, strict = false} lthy const
          |> Term.dest_Const
        val compiled_term = Syntax.read_term lthy compiled

        val n_const_ty_args = Term.strip_type const_ty |> fst |> length
        val n_arg_regs = length arg_regs
        val pretty_int = Pretty.str o Int.toString
        val _ =
          if n_const_ty_args <> n_arg_regs
            then
              [ Pretty.str "The constant"
              , Pretty.quote (Syntax.pretty_term lthy (Const (const_name, const_ty)))
              , Pretty.str "takes", pretty_int n_const_ty_args, Pretty.str "arguments."
              , Pretty.str "Number of argument registers: ", pretty_int n_arg_regs
              ]
              |> Pretty.breaks |> Pretty.block
              |> Pretty.string_of |> error
            else ()

        val compiled_ty = Term.fastype_of compiled_term
        val _ =
          if compiled_ty <> \<^typ>\<open>com\<close>
            then
              Pretty.breaks
                [ Pretty.keyword2 "compiled", Pretty.str "must have type"
                , Pretty.quote (Syntax.pretty_typ lthy \<^typ>\<open>com\<close>)
                ] @ Pretty.str "." ::
              [ Pretty.brk 1, Pretty.str "Got type:", Pretty.brk 1
              , Pretty.quote (Syntax.pretty_typ lthy compiled_ty)
              ]
              |> Pretty.block
              |> Pretty.string_of |> error
            else ()

        val compiled_const = {ret_reg = ret_reg, arg_regs = arg_regs,
                              compiled = Syntax.read_term lthy compiled}
      in
        lthy
        |> declare_compiled_const const_name compiled_const
      end))
end

local
  val parser = Parse.opt_bang
in
  val _ = Outer_Syntax.local_theory
    \<^command_keyword>\<open>print_compiled_consts\<close>
    "print all declared compiled constants"
    (parser >> (fn verbose => fn lthy =>
      let
        val pretty_reg = Pretty.quote o Pretty.str
        fun pretty_ret_reg ret_reg = Pretty.block
          [ Pretty.keyword2 "return_register", Pretty.brk 1
          , pretty_reg ret_reg
          ]
        fun pretty_arg_regs arg_regs =
          [Pretty.keyword2 "argument_registers"] @
          map pretty_reg arg_regs
          |> Pretty.breaks
          |> Pretty.block
        fun pretty_compiled compiled =
          let
            fun unfold1_term thms t =
              Thm.cterm_of lthy t
              |> Thm.reflexive
              |> Conv.fconv_rule (Conv.try_conv (Conv.arg_conv (Conv.rewrs_conv thms)))
              |> Thm.cprop_of |> Thm.dest_equals |> snd |> Thm.term_of
            val compiled =
              if not verbose then compiled
                else
                  compiled
                  |> unfold1_term (\<^named_theorems>\<open>compiled_const_defs\<close> |> Named_Theorems.get lthy)
          in
            Pretty.block
              [ Pretty.keyword2 "compiled", Pretty.brk 1
              , Pretty.cartouche (Syntax.pretty_term lthy compiled)
              ]
          end
        fun pretty_compiled_const (name, {ret_reg, arg_regs, compiled}) =
          let val const = Proof_Context.read_const {proper = false, strict = false} lthy name
          in
            Syntax.pretty_term lthy const ::
            Pretty.fbrk ::
            Pretty.breaks
              [ pretty_ret_reg ret_reg
              , pretty_arg_regs arg_regs
              , pretty_compiled compiled
              ]
            |> Pretty.item
          end
        val _ =
          Compiled_Consts.get (Context.Proof lthy)
          |> Symtab.dest
          |> map pretty_compiled_const
          |> Pretty.big_list "Compiled constants:"
          |> Pretty.writeln
      in
        lthy
      end))
end

end