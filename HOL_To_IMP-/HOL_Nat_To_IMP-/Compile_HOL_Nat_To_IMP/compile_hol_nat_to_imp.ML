(*  Title:      HOL_To_IMP-/compile_hol_nat_to_imp.ML
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
  val get_compiled_const : Proof.context -> term -> compiled_const

  val compiled_const_suffix_cfg : string Config.T
  val declare_compiled_const : term -> compiled_const -> local_theory -> local_theory

  (* val register_sep_cfg : string Config.T *)
  (* val argument_sep_cfg : string Config.T *)
end

structure Compile_HOL_Nat_To_IMP : COMPILE_HOL_NAT_TO_IMP =
struct

structure HTHNU = HOL_To_HOL_Nat_Util

val logger = Logger.setup_new_logger HOL_Nat_To_IMP_Minus_base_logger "Compile_HOL_Nat_To_IMP"

structure Compiled_Const_Defs = Generic_Data(
  type T = thm Net.net;
  val empty = Net.empty
  val merge = Net.merge Thm.eq_thm
)

fun get_compiled_const_def ctxt t =
  case Net.match_term (Compiled_Const_Defs.get (Context.Proof ctxt)) t of
    [] => NONE
  | [thm] => SOME thm
  | thms => let val msg = "Found more than one compiled constant"
      in
        (Pretty.str msg
          :: map (Thm.pretty_thm ctxt) thms |> Pretty.block |> Pretty.writeln;
        error msg)
      end

val compiled_const_from_def = Thm.lhs_of #> Thm.term_of #> Term.head_of

fun update_compiled_const_def thm =
  let val key = compiled_const_from_def thm
  in Compiled_Const_Defs.map (Net.insert_term (K true) (key, thm)) end

val update_compiled_const_def_attr = Thm.declaration_attribute update_compiled_const_def

fun delete_compiled_const_def thm =
  let val key = compiled_const_from_def thm
  in Compiled_Const_Defs.map (Net.delete_term (K true) (key, thm)) end

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

fun pretty_compiled verbose ctxt compiled =
  let
    fun unfold1_term thms =
      Thm.cterm_of ctxt
      #> Thm.reflexive
      #> Conv.fconv_rule (Conv.try_conv (Conv.arg_conv (Conv.rewrs_conv thms)))
      #> Thm.cprop_of #> Thm.dest_equals #> snd #> Thm.term_of
    val compiled = (verbose ? (Compiled_Const_Defs.get (Context.Proof ctxt)
      |> Net.content |> unfold1_term))
      compiled
  in
    Pretty.block
      [ Pretty.keyword2 "compiled", Pretty.brk 1
      , Pretty.cartouche (Syntax.pretty_term ctxt compiled)
      ]
  end

fun pretty_compiled_const verbose ctxt {ret_reg, arg_regs, compiled} =
  Pretty.breaks
    [ pretty_ret_reg ret_reg
    , pretty_arg_regs arg_regs
    , pretty_compiled verbose ctxt compiled
    ]

fun pretty_compiled_const' verbose ctxt (const , compiled_const) =
  Syntax.pretty_term ctxt const ::
  Pretty.fbrk ::
  pretty_compiled_const verbose ctxt compiled_const
  |> Pretty.item

structure Compiled_Consts = Generic_Data
(
  type T = compiled_const Net.net;
  val empty = Net.empty
  val merge = Net.merge (op =)
);

fun declare_compiled_const const compiled_const =
  Local_Theory.declaration {syntax = false, pervasive = false, pos = Position.thread_data ()}
    (fn phi =>
      let
        val const' = Morphism.term phi const
        val compiled_const' = map_compiled (Morphism.term phi) compiled_const
      in Compiled_Consts.map (Net.insert_term (K true) (const', compiled_const')) end)

fun get_compiled_const ctxt f =
  case Net.match_term (Compiled_Consts.get (Context.Proof ctxt)) f of
    [] => error ("Unknown compiled constant: " ^ quote (@{make_string} f))
  | [compiled_const] => compiled_const
  | compiled_consts => let val msg = "Found more than one compiled constant"
      in
        (Pretty.str msg
          :: map (pair f #> pretty_compiled_const' false ctxt) compiled_consts
        |> Pretty.block |> Pretty.writeln;
        error msg)
      end

(* We index Ifs, Lets, Calls with unique numbers such that we can easily
   invent new register names without passing a context around *)
datatype tc_ast = If of int * (tc_ast * tc_ast * tc_ast) |
  Number of int |
  Arg of int |
  Let of (int * (string * (tc_ast * tc_ast))) |
  LetBound of int |
  Call of int * ((string * typ) * tc_ast list) |
  TailCall of int * tc_ast list

fun tc_ast_of_term head f_args t =
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
      | index_tc_ast index (TailCall (_, args)) =
        let val (index', rev_args') = fold fold_step args (index, [])
        in (index' + 1, TailCall (index', rev rev_args')) end
      | index_tc_ast index t = (index, t)

    fun is_comb (_ $ _) = true
      | is_comb _ = false

    fun if_case c e1 e2= If (~1, @{apply 3} build_tc_ast (c, e1, e2))
    and build_tc_ast t =
      if can HOLogic.dest_number t then Number (HOLogic.dest_number t |> snd)
      else
        case Term.head_of t of
          \<^Const_>\<open>HOL.If _\<close> =>
            (case Term.args_of t of
              [c, e1, e2] => if_case c e1 e2
            | _ => raise TERM ("Only fully applied if allowed, got:", [t]))
        | \<^Const_>\<open>HOL_To_HOL_Nat.If_nat _\<close> =>
            (case Term.args_of t of
              [c, e1, e2] => if_case c e1 e2
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
        | g as Const (g_name, g_typ) =>
          if g = head
            then TailCall (~1, map build_tc_ast (Term.args_of t))
            else Call (~1, ((g_name, g_typ), map build_tc_ast (Term.args_of t)))
        | h => raise TERM ("Unexpected head of term:", [h])
  in
    t |> build_tc_ast |> index_tc_ast 0 |> snd
  end

exception PARTIAL of string * string
exception NONTAIL of string

fun IMP_Minus_of_tc_ast (f_ret_name, f_arg_names) lookup_fn arg_sep register_sep e =
  let
    fun mk_Seq es = fold_rev (fn e1 => fn e2 => \<^Const>\<open>tSeq for e1 e2\<close>) es \<^Const>\<open>tSKIP\<close>

    fun mk_N n = \<^Const>\<open>N for \<open>HOLogic.mk_number \<^typ>\<open>nat\<close> n\<close>\<close>

    val mk_reg = List.map Substring.full #> Substring.concatWith register_sep #> HOLogic.mk_string
    val mk_local_reg = cons "" #> mk_reg

    (* compile the expression, then pass an aexp that evaluates to
        the value of the expression to the continuation *)
    fun go _ _ cont (Number i) = cont \<^Const>\<open>A for \<open>mk_N i\<close>\<close>
      | go _ _ cont (Arg i) = cont \<^Const>\<open>A for \<^Const>\<open>V for \<open>HOLogic.mk_string (nth f_arg_names i)\<close>\<close>\<close>
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
      | go is_tail bounds _ (TailCall (idx, es)) =
        let
          val _ = is_tail orelse raise NONTAIL "Recursive call must be in tail position"

          fun f_local_arg_reg i = mk_local_reg [arg_sep, Int.toString idx, Int.toString i]
        in
          mk_Seq [prepare_call bounds f_local_arg_reg f_arg_names es, \<^Const>\<open>tTAIL\<close>]
        end
      | go _ bounds cont (Call (idx, ((g_name, g_type), es))) =
        let
          val g_compiled = lookup_fn (Const (g_name, g_type))
          (* remove all type itself arguments *)
          val es = es |> filter_out (fn Call (_, ((_, T), _)) => HTHNU.is_itself T | _ => false)
          val _ = List.length (#arg_regs g_compiled) = List.length es
            orelse raise PARTIAL ("Call must occur fully applied", g_name)
          val g_ret = #ret_reg g_compiled

          fun g_local_arg_reg i = mk_local_reg ["Call", Int.toString idx, Int.toString i]
        in
          [ prepare_call bounds g_local_arg_reg (#arg_regs g_compiled) es
          , \<^Const>\<open>tCall for \<open>#compiled g_compiled\<close> \<open>HOLogic.mk_string g_ret\<close>\<close>
          , cont \<^Const>\<open>A for \<^Const>\<open>V for \<open>HOLogic.mk_string g_ret\<close>\<close>\<close>
          ]
          |> mk_Seq
        end
    and prepare_call bounds local_arg_reg arg_names args =
      let
        fun mk_copy from_reg to_reg =
          \<^Const>\<open>tAssign for to_reg \<^Const>\<open>A for \<^Const>\<open>V for from_reg\<close>\<close>\<close>
        val mk_copies = List.map (uncurry mk_copy)

        val args_IMP =
          map_index (fn (i, e) => go false bounds (fn rhs => \<^Const>\<open>tAssign for \<open>local_arg_reg i\<close> rhs\<close>) e) args
        val copy_args =
          map_index (fn (i, arg_name) => (local_arg_reg i, HOLogic.mk_string arg_name)) arg_names
          |> mk_copies
      in
        args_IMP @ copy_args |> mk_Seq
      end
  in
    go true [] (fn rhs => \<^Const>\<open>tAssign for \<open>HOLogic.mk_string f_ret_name\<close> rhs\<close>) e
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

val arg_sep_cfg =
  Attrib.setup_config_string \<^binding>\<open>argument_seperator\<close> (K "arg")

fun compile_cmd f_def optimized basenamepos_opt lthy =
  let
    val pos = Position.thread_data ()

    val f_def = reflect_eq f_def

    val (lhs, rhs) = f_def |> Thm.prop_of
      |> (fn t => yield_singleton (Variable.import_terms true) t lthy) |> fst
      |> HOL_Fun_To_HOL_Nat_Fun.mk_unconditional_eq

    val f_head = lhs |> head_of
    val f_name = f_head |> dest_Const_name

    val (args, def_body) =
      lhs |> strip_comb |> snd |> map Term.dest_Free
      |> List.foldr (I #-> Term.absfree) rhs |> Term.strip_abs

    val f_IMP_namepos = the_default (Long_Name.base_name f_name, pos) basenamepos_opt

    val register_sep = Config.get lthy register_sep_cfg
    val arg_sep = Config.get lthy arg_sep_cfg
    val f_ret_name = fst f_IMP_namepos ^ register_sep ^ "ret"
    fun mk_arg_name arg_name =
      fst f_IMP_namepos ^ register_sep ^ arg_sep ^ register_sep ^ arg_name
    val f_args = map (@{apply 2 (1)} mk_arg_name) args
    val f_args_vars = map (Var o @{apply 2 (1)} (fn n => (n, 0))) f_args

    val rewrite = Nbe.dynamic_value lthy
    val f_ret_name_str = HOLogic.mk_string f_ret_name
    fun preprocess_base t =
      \<^Const>\<open>pull_tIf_assoc_right for \<^Const>\<open>assoc_right_tSeq for \<^Const>\<open>rm_tSKIP for t\<close>\<close>\<close>
    fun preprocess t = if optimized then
        \<^Const>\<open>rm_tSKIP for \<^Const>\<open>bury for f_ret_name_str \<^Const>\<open>trans_assigns for
        \<open>preprocess_base t\<close>\<close>\<close>\<close>
      else preprocess_base t
    val f_IMP =
      def_body
      |> curry Term.subst_bounds (rev f_args_vars)
      |> tc_ast_of_term f_head f_args
      |> IMP_Minus_of_tc_ast
          (f_ret_name, map fst f_args)
          (get_compiled_const lthy)
          arg_sep
          register_sep
      |> preprocess
      |> rewrite
    val f_IMP_binding = Config.get lthy compiled_const_suffix_cfg
      |> Binding.name
      |> Transport_Util.add_suffix (f_IMP_namepos |> fst |> Binding.name)
    val lthy' = define_compiled f_IMP_binding f_IMP lthy
    val f_IMP_const = Binding.name_of f_IMP_binding
      |> HTHNU.read_const lthy'
      |> (fn t => \<^Const>\<open>tailcall_to_IMP_Minus for t\<close>)
    val f_compiled = { ret_reg = f_ret_name, arg_regs = map fst f_args,
                       compiled = f_IMP_const }
  in
    lthy'
    |> declare_compiled_const f_head f_compiled
  end

local
  val parser = Parse.opt_keyword "non-optimized" -- Parse.thm
    -- Scan.option (\<^keyword>\<open>basename\<close> |-- Parse.name_position)
in
  val _ = Outer_Syntax.local_theory
    \<^command_keyword>\<open>compile_nat\<close>
    "compile and declare a constant"
    (parser >> (fn ((optimized, (thm_ref, _)), namepos_opt) => fn lthy =>
      let val thm = Proof_Context.get_fact lthy thm_ref |> the_single
      in compile_cmd thm (not optimized) namepos_opt lthy end))
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
        val const = HTHNU.read_const lthy const
        val compiled_term = Proof_Context.read_term_pattern lthy compiled

        val n_const_ty_args = Term.strip_type (dest_Const_type const) |> fst |> length
        val n_arg_regs = length arg_regs
        val pretty_int = Pretty.str o Int.toString
        val _ =
          if n_const_ty_args <> n_arg_regs
            then
              [ Pretty.str "The constant"
              , Pretty.quote (Syntax.pretty_term lthy const)
              , Pretty.str "takes", pretty_int n_const_ty_args, Pretty.str "arguments."
              , Pretty.str "Number of argument registers: ", pretty_int n_arg_regs
              ]
              |> Pretty.breaks |> Pretty.block
              |> Pretty.string_of |> error
            else ()

        val compiled_ty = Term.fastype_of compiled_term
        val com_ty = \<^typ>\<open>com\<close>
        val _ =
          if compiled_ty <> com_ty
            then
              Pretty.breaks
                [ Pretty.keyword2 "compiled", Pretty.str "must have type"
                , Pretty.quote (Syntax.pretty_typ lthy com_ty)
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
        |> declare_compiled_const const compiled_const
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
        val _ = @{log Logger.INFO} lthy (fn _ => Compiled_Consts.get (Context.Proof lthy)
          |> Net.content
          |> map (pretty_compiled_const verbose lthy #> Pretty.item)
          |> Pretty.big_list "Compiled constants:"
          |> Pretty.string_of)
      in lthy end))
end

end
