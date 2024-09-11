(*  Title:      HOL_To_IMP_Minus/compile_hol_nat_to_imp.ML
    Author:     Lukas Stevens, TU Muenchen

Compiler from HOL-tailrecursive functions on natural numbers to IMP with tailcalls.
*)
signature COMPILE_HOL_NAT_TO_IMP =
sig
  include HAS_LOGGER

  val get_compiled_const_def : Proof.context -> term -> thm option

  val update_compiled_const_def_attr : attribute
  val delete_compiled_const_def_attr : attribute

  type compiled_const = {arg_regs: string list, compiled: term, ret_reg: string}
  val get_compiled_const : Context.generic -> string -> compiled_const

  val compiled_const_suffix_cfg : string Config.T
  val declare_compiled_const : bstring -> compiled_const -> local_theory -> local_theory

  val register_sep_cfg : string Config.T
end

structure Compile_HOL_Nat_To_IMP : COMPILE_HOL_NAT_TO_IMP =
struct

val logger = Logger.setup_new_logger HOL_Nat_To_IMP_Minus_base_logger "Compile_HOL_Nat_To_IMP"

fun foldr_index f z = map_index I #> List.foldr (uncurry f) z

structure Compiled_Const_Defs = Generic_Data(
  type T = thm Termtab.table;
  val empty = Termtab.empty
  val merge = Termtab.join (K fst)
)

val get_compiled_const_def = Termtab.lookup o Compiled_Const_Defs.get o Context.Proof

val compiled_const_from_def = Thm.lhs_of #> Thm.term_of #> Term.head_of

fun update_compiled_const_def thm = compiled_const_from_def thm
  |> rpair thm
  |> Termtab.update_new
  |> Compiled_Const_Defs.map
val update_compiled_const_def_attr = Thm.declaration_attribute update_compiled_const_def

fun delete_compiled_const_def thm = compiled_const_from_def thm
  |> Termtab.delete
  |> Compiled_Const_Defs.map
val delete_compiled_const_def_attr = Thm.declaration_attribute delete_compiled_const_def

val compiled_const_def_binding = \<^binding>\<open>compiled_IMP_Minus_const_def\<close>

val setup_compiled_const_def_attr = Attrib.add_del
  update_compiled_const_def_attr delete_compiled_const_def_attr

val _ = Theory.setup (
  Attrib.setup compiled_const_def_binding setup_compiled_const_def_attr
    "add/del compiled IMP constant definition")

type compiled_const = { ret_reg : string, arg_regs : string list, compiled : term }

fun map_compiled f (c : compiled_const) =
  { ret_reg = #ret_reg c, arg_regs = #arg_regs c, compiled = f (#compiled c) }

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
        val name' =
          name
          |> Binding.name
          |> Morphism.binding phi
          |> Binding.name_of
        val compiled_const' = map_compiled (Morphism.term phi) compiled_const
      in Compiled_Consts.map (Symtab.update_new (name', compiled_const')) end)

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

(* is the given function called? *)
fun has_call to (Call (_, ((f, _), es))) = (f = to) orelse exists (has_call to) es
  | has_call to (If (_, (_, e1, e2))) = has_call to e1 orelse has_call to e2
  | has_call to (Let (_, (_, (e1, e2)))) = has_call to e1 orelse has_call to e2
  | has_call to (TailCall es) = exists (has_call to) es
  | has_call _ _ = false

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

    fun is_comb (_ $ _) = true
      | is_comb _ = false

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
        | Var ((n, _), typ) =>
            if is_comb t then
              raise TERM ("Call to function given as argument is not allowed, got:", [t])
            else Arg (Library.find_index (fn v' => (n, typ) = v') f_args)
        | Const (g_name, g_typ) =>
          if (g_name, g_typ) = (f_name, f_typ)
            then TailCall (map build_tc_ast (Term.args_of t))
            else Call (~1, ((g_name, g_typ), map build_tc_ast (Term.args_of t)))
        | h => raise TERM ("Unexpected head of term:", [h])
  in
    t |> build_tc_ast |> index_tc_ast 0 |> snd
  end

exception PARTIAL of string * string
exception NONTAIL of string

fun IMP_Minus_of_tc_ast (f_ret_name, f_arg_names) lookup_fn register_sep e =
  let
    fun mk_copy from_reg to_reg =
      \<^Const>\<open>tAssign for to_reg \<^Const>\<open>A for \<^Const>\<open>V for from_reg\<close>\<close>\<close>
    val mk_copies = List.map (uncurry mk_copy)

    fun mk_Seq es = fold_rev (fn e1 => fn e2 => \<^Const>\<open>tSeq for e1 e2\<close>) es \<^Const>\<open>tSKIP\<close>

    fun mk_N n = \<^Const>\<open>N for \<open>HOLogic.mk_number \<^typ>\<open>nat\<close> n\<close>\<close>

    val mk_reg = List.map Substring.full #> Substring.concatWith register_sep #> HOLogic.mk_string
    val mk_local_reg = cons "" #> mk_reg

    fun f_local_arg_reg i = mk_local_reg ["args", Int.toString i]
    fun f_arg_reg i = nth f_arg_names i |> HOLogic.mk_string

    val copy_f_args =
      map_index (fn (i, arg_name) => (HOLogic.mk_string arg_name, f_local_arg_reg i)) f_arg_names
      |> mk_copies |> mk_Seq

    (* compile the expression, then pass an aexp that evaluates to
        the value of the expression to the continuation *)

    fun go _ _ cont (Number i) = cont \<^Const>\<open>A for \<open>mk_N i\<close>\<close>
      | go _ _ cont (Arg i) = cont \<^Const>\<open>A for \<^Const>\<open>V for \<open>f_local_arg_reg i\<close>\<close>\<close>
      | go is_tail bounds cont (If (idx, (cond, e1, e2))) =
        let
          val cond_reg = mk_local_reg ["If", Int.toString idx]
          val cond_IMP = go false bounds (fn rhs => \<^Const>\<open>tAssign for cond_reg rhs\<close>) cond
          val (e1_IMP, e2_IMP) = @{apply 2} (go is_tail bounds cont) (e1, e2)
          val if_IMP = \<^Const>\<open>tIf for cond_reg e1_IMP e2_IMP\<close>
        in
          mk_Seq [cond_IMP, if_IMP]
        end
      | go is_tail bounds cont (Let (idx, (x, (e1, e2)))) =
        let
          val x_reg = mk_local_reg ["Let", Int.toString idx, x]
          val e1_IMP = go false bounds (fn rhs => \<^Const>\<open>tAssign for x_reg rhs\<close>) e1
          val e2_IMP = go is_tail (x_reg :: bounds) cont e2
        in
          mk_Seq [e1_IMP, e2_IMP]
        end
      | go _ bounds cont (LetBound i) = cont \<^Const>\<open>A for \<^Const>\<open>V for \<open>nth bounds i\<close>\<close>\<close>
      | go is_tail bounds _ (TailCall es) =
        let
          val _ = is_tail orelse raise NONTAIL "Recursive call must be in tail position"
          val es_IMP =
            map_index (fn (i, e) => go false bounds (fn rhs => \<^Const>\<open>tAssign for \<open>f_arg_reg i\<close> rhs\<close>) e) es
        in
          mk_Seq (es_IMP @ [\<^Const>\<open>tTAIL\<close>])
        end
      | go _ bounds cont (Call (idx, ((g_name, _), es))) =
        let
          val g_compiled = lookup_fn g_name
          val _ = List.length (#arg_regs g_compiled) = List.length es
            orelse raise PARTIAL ("Call must occur fully applied", g_name)
          val g_ret = #ret_reg g_compiled

          fun g_local_arg_reg i = mk_local_reg ["Call", Int.toString idx, Int.toString i]
          fun g_arg_cont reg rhs = \<^Const>\<open>tAssign for reg rhs\<close>
          fun g_go_reg reg = go false bounds (g_arg_cont reg)

          (* if g is called in e_j, then for i < j,
             the computation of e_i needs to be saved in a temporary variable *)
          fun g_do_arg (i, (arg_reg, e)) { calls, copies, needs_tmp } =
            if needs_tmp then
              { calls = g_go_reg (g_local_arg_reg i) e :: calls,
                copies = (g_local_arg_reg i, HOLogic.mk_string arg_reg) :: copies,
                needs_tmp = true }
            else
              { calls = g_go_reg (HOLogic.mk_string arg_reg) e :: calls,
                copies = copies,
                needs_tmp = has_call g_name e }
          val g_args =
            #arg_regs g_compiled ~~ es
            |> foldr_index g_do_arg { calls = [], copies = [], needs_tmp = false }
        in
          #calls g_args @
          mk_copies (#copies g_args) @
            [ \<^Const>\<open>tCall for \<open>#compiled g_compiled\<close> \<open>HOLogic.mk_string g_ret\<close>\<close>
            , cont \<^Const>\<open>A for \<^Const>\<open>V for \<open>HOLogic.mk_string g_ret\<close>\<close>\<close>
            ]
          |> mk_Seq
        end

    val body = go true [] (fn rhs => \<^Const>\<open>tAssign for \<open>HOLogic.mk_string f_ret_name\<close> rhs\<close>) e
  in
    mk_Seq [copy_f_args, body]
  end

fun define_compiled compiled_binding compiled lthy =
  let
    val pos = Binding.pos_of compiled_binding

    val def_attr = Attrib.internal pos
      (Thm.declaration_attribute o (update_compiled_const_def oo Morphism.thm))

    val ((fv, (def_name, def_thm)), lthy') =
      Local_Theory.define ((compiled_binding, NoSyn),
                          ((Thm.def_binding compiled_binding, [def_attr]), compiled))
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

val register_sep_cfg =
  Attrib.setup_config_string \<^binding>\<open>register_seperator\<close> (K ".")

fun compile_cmd f_def basenamepos_opt lthy =
  let
    val pos = Position.thread_data ()

    val f_def = reflect_eq f_def
    val (args, def_body) =
      Local_Defs.abs_def_rule lthy f_def
      |> Thm.rhs_of |> Thm.term_of |> Term.strip_abs

    val (f_name, f_typ) = f_def |> Thm.lhs_of |> Thm.term_of |> Term.head_of |> Term.dest_Const

    val f_IMP_namepos = the_default (Long_Name.base_name f_name, pos) basenamepos_opt

    val register_sep = Config.get lthy register_sep_cfg
    val f_ret_name = fst f_IMP_namepos ^ register_sep ^ "ret"
    fun mk_arg_name arg_name =
      fst f_IMP_namepos ^ register_sep ^ "args" ^ register_sep ^ arg_name
    val f_args = map (@{apply 2 (1)} mk_arg_name) args
    val f_args_vars = map (Var o @{apply 2 (1)} (fn n => (n, 0))) f_args

    val simp_thy = empty_simpset lthy |> Proof_Context.theory_of
    val simp_thms = map reflect_eq @{thms assoc_right_tSeq.simps tseq.simps rm_tSKIP.simps}
    val rewrite = Raw_Simplifier.rewrite_term simp_thy simp_thms []
    val f_IMP =
      def_body
      |> curry Term.subst_bounds (rev f_args_vars)
      |> tc_ast_of_term (f_name, f_typ) f_args
      |> IMP_Minus_of_tc_ast
          (f_ret_name, map fst f_args)
          (get_compiled_const (Context.Proof lthy))
          register_sep
      |> (fn t => rewrite \<^Const>\<open>assoc_right_tSeq for \<^Const>\<open>rm_tSKIP for t\<close>\<close>)

    val f_IMP_binding =
      f_IMP_namepos
      |>> suffix ("_" ^ Config.get lthy compiled_const_suffix_cfg)
      |> Binding.make
    val lthy' = define_compiled f_IMP_binding f_IMP lthy
    val f_IMP_const =
      Binding.name_of f_IMP_binding
      |> Proof_Context.read_const {proper = false, strict = false} lthy'
      |> (fn t => \<^Const>\<open>tailcall_to_IMP_Minus for t\<close>)

    val f_compiled = { ret_reg = f_ret_name, arg_regs = map fst f_args
                     , compiled = f_IMP_const }
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
            fun unfold1_term thms =
              Thm.cterm_of lthy
              #> Thm.reflexive
              #> Conv.fconv_rule (Conv.try_conv (Conv.arg_conv (Conv.rewrs_conv thms)))
              #> Thm.cprop_of #> Thm.dest_equals #> snd #> Thm.term_of
            val compiled = (verbose ? (Compiled_Const_Defs.get (Context.Proof lthy)
              |> Termtab.dest |> map snd |> unfold1_term))
              compiled
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
        val _ = @{log Logger.INFO} lthy (fn _ => Compiled_Consts.get (Context.Proof lthy)
          |> Symtab.dest
          |> map pretty_compiled_const
          |> Pretty.big_list "Compiled constants:"
          |> Pretty.string_of)
      in lthy end))
end

end