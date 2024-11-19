(*  Title:      hol_to_hol_nat_util.ML
    Author:     Kevin Kappelmann, TU Muenchen
*)
signature HOL_TO_HOL_NAT_UTIL =
sig
  val cat_options: 'a option list -> 'a list

  val map_sort: (sort -> sort) -> typ -> typ
  val map_fun_types : (typ -> typ) -> typ -> typ

  val dest_eq_equals_prop : term -> term * term
  val dest_eq_equals_thm : thm -> term * term
  val app: term -> term -> term
  val term_binder_types: term -> typ list
  val fun_nargs: term -> int
  val read_const: Proof.context -> string -> term
  val const_from_binding: Proof.context -> binding -> term
  val is_itself : typ -> bool
  val is_TYPE : term -> bool

  val get_fun_simps: Proof.context -> term -> thm list option list

  val induction_var_tac: Proof.context -> term -> int -> tactic

  val prove_goal_schematics: string list -> (Proof.context -> tactic) -> Proof.context -> term -> thm
  val prove_goal: (Proof.context -> tactic) -> Proof.context -> term -> thm
  val prove_goals : (Proof.context -> tactic) -> Proof.context -> term list -> thm list

  val register_def: term -> local_theory -> (term * (string * thm)) * local_theory
  val register_fun: binding -> term -> term -> local_theory -> Proof.context
  val register_attrs_thms: Token.src list -> binding -> thm list -> local_theory ->
    (string * thm list) * local_theory
  val register_thms: binding -> thm list -> local_theory -> (string * thm list) * local_theory
  val register_attrs_transfer_thms : Token.src list -> binding -> thm list -> local_theory ->
    (string * thm list) * local_theory
  val register_transfer_thms : binding -> thm list -> local_theory ->
    (string * thm list) * local_theory
  val del_simps: thm list -> local_theory -> local_theory

  val binding_from_long_name: string -> binding
  val const_binding: string -> binding
  val term_binding: term -> binding
  val type_binding: typ -> binding
  val type_suffix_binding: binding -> typ -> binding

  val natT: typ
  val mk_nat: int -> term

  val compile_natC: string
  val compile_natS: string list
  val add_compile_nat_sort: typ -> typ

  val Rel_nat_iff_thm: thm
  val mk_Rel_nat: typ -> term
  val Rel_nat_binding: binding
  val mk_Rel_nat_type_binding: typ -> binding

  val mk_transfer_rel_fun: term -> term -> term
  val mk_transfer_rel_fun_types: typ -> typ -> typ -> typ -> term
  val mk_transfer_rel_fun_dummyT: term
  val transfer_fun_RelI: thm
  val transfer_fun_RelD: thm

  val mk_transport_rel_fun_types: typ -> typ -> typ -> typ -> term
  val mk_transport_rel_fun_dummyT: term
  val transport_fun_RelI: thm
  val transport_fun_RelD: thm

  val fun_rel_intro_tac: thm -> Proof.context -> int -> tactic
  val solve_fun_rel_tac : thm -> Proof.context -> int -> tactic
  val solve_Rel_nat_tac : thm -> Proof.context -> int -> tactic

  val mk_Rel_fun_from_type : ('a -> 'a -> 'a) -> (typ -> 'a) -> typ -> 'a

end

structure HOL_To_HOL_Nat_Util : HOL_TO_HOL_NAT_UTIL =
struct

structure BU = BNF_Util
structure HU = HOLogic
structure TrpU = Transport_Util

(*miscellaneous*)
fun cat_options opts = fold (fn NONE => I | SOME x => cons x) opts []

fun map_sort f (TVar (n, s)) = TVar (n, f s)
  | map_sort f (TFree (n, s)) = TFree (n, f s)
  | map_sort f (Type (n, Ts)) = Type (n, map (map_sort f) Ts)

fun map_fun_types f T = let val (Ts, T) = strip_type T
  in (map (map_fun_types f) Ts) ---> f T end

fun dest_eq_equals_prop t = case t of
    \<^Const>\<open>Trueprop for \<^Const>\<open>HOL.eq _ for lhs rhs\<close>\<close> => (lhs, rhs)
  | \<^Const>\<open>Pure.eq _ for lhs rhs\<close> => (lhs, rhs)
  | t => raise TERM ("Unknown equality:", [t])

val dest_eq_equals_thm = Thm.prop_of #> dest_eq_equals_prop

val app = curry (op $)

val term_binder_types = fastype_of #> binder_types
val fun_nargs = fastype_of #> binder_types #> length

val read_const = Proof_Context.read_const {proper = false, strict = false};
fun const_from_binding ctxt = Binding.name_of #> read_const ctxt

fun is_itself (Type (@{type_name itself}, _)) = true
  | is_itself _ = false
fun is_TYPE (Const (@{const_name Pure.type}, _)) = true
  | is_TYPE _ = false

fun get_fun_simps ctxt = Function_Common.retrieve_function_data ctxt #> map (snd #> #simps)

fun induction_var_tac ctxt var =
  Induction.induction_tac ctxt false [[SOME (NONE, (var, false))]] [] [] NONE []

fun prove_goal_schematics schematics tac ctxt t =
  Goal.prove ctxt schematics [] (HU.mk_Trueprop t) (#context #> tac)
val prove_goal = prove_goal_schematics []

fun prove_goals tac ctxt ts = Goal.prove_common ctxt NONE [] [] ts (#context #> tac)

(*registrations*)
fun register_def eq = Specification.definition NONE [] [] (Binding.empty_atts, eq)

fun register_fun binding_name lhs rhs lthy =
  let
    val fixes = [(binding_name, NONE, NoSyn)]
    val specs = [((Binding.empty_atts, BU.mk_Trueprop_eq (lhs, rhs)), [], [])]
  in Function_Fun.add_fun fixes specs Function_Fun.fun_config lthy end

fun register_attrs_thms attrs binding thms = Local_Theory.note ((binding, attrs), thms)
val register_thms = register_attrs_thms @{attributes []}

fun del_simps simps = register_attrs_thms @{attributes [simp del]} Binding.empty simps #> snd

fun register_attrs_transfer_thms attrs = register_attrs_thms (@{attributes [transfer_rule]} @ attrs)
val register_transfer_thms = register_attrs_transfer_thms []

(*bindings*)
val binding_from_long_name = Long_Name.base_name #> Binding.name
val type_binding = dest_Type #> fst #> binding_from_long_name
val const_binding = binding_from_long_name
val term_binding = Term.term_name #> Binding.name

fun type_suffix_binding base_binding = type_binding #> TrpU.add_suffix base_binding

(*natural numbers*)
val natT = \<^typ>\<open>nat\<close>
val mk_nat = HU.mk_number natT

(*compile to nat type class*)
val compile_natS = \<^sort>\<open>compile_nat\<close>
val compile_natC = \<^class>\<open>compile_nat\<close>

val add_compile_nat_sort = map_sort (fn \<^sort>\<open>type\<close> => compile_natS | s => insert (op =) compile_natC s)

val Rel_nat_iff_thm = @{thm Rel_nat_iff_eq_natify}
fun mk_Rel_nat T = \<^Const>\<open>Rel_nat T\<close>
val Rel_nat_binding  = const_binding @{const_name Rel_nat}
val mk_Rel_nat_type_binding  = type_suffix_binding Rel_nat_binding

(*function relator*)
val mk_transfer_rel_fun = BU.mk_rel_fun
fun mk_transfer_rel_fun_types A B C D = \<^Const>\<open>rel_fun A B C D\<close>
val mk_transfer_rel_fun_dummyT = mk_transfer_rel_fun_types dummyT dummyT dummyT dummyT
val transfer_fun_RelI = @{thm rel_funI}
val transfer_fun_RelD = @{thm rel_funD}

fun mk_transport_rel_fun_types A B C D = \<^Const>\<open>Fun_Rel_rel A B C D\<close>
val mk_transport_rel_fun_dummyT = mk_transport_rel_fun_types dummyT dummyT dummyT dummyT
val transport_fun_RelI = @{thm Fun_Rel_relI}
val transport_fun_RelD = @{thm Fun_Rel_relD}

fun fun_rel_intro_tac fun_RelI ctxt = REPEAT_ALL_NEW (resolve_tac ctxt [fun_RelI])
fun solve_fun_rel_tac fun_RelD ctxt = force_tac (ctxt addDs [fun_RelD] addsimps [@{thm rel_fun_eq}])
fun solve_Rel_nat_tac fun_RelD ctxt = solve_fun_rel_tac fun_RelD (ctxt addsimps [Rel_nat_iff_thm])

fun mk_Rel_fun_from_type mk_rel_fun base T = case T of
    \<^Type>\<open>fun A B\<close> =>
      mk_rel_fun (mk_Rel_fun_from_type mk_rel_fun base A) (mk_Rel_fun_from_type mk_rel_fun base B)
  | T => base T

end