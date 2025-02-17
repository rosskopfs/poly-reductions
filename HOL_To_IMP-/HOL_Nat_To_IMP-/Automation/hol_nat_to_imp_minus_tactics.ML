(*  Title:  Automation/hol_nat_to_imp_minus_tactics.ML
    Author: Kevin Kappelmann
    Author: Max Lang

HOL to IMP tactics with arguments from context.
*)
@{parse_entries (sig) PARSE_HOL_NAT_TO_IMP_MINUS_TACTICS_CONTEXT_ARGS
  [get_IMP_def, get_imp_minus_correct, get_HOL_eqs, get_fun_inducts]}

@{parse_entries (sig) PARSE_HOL_NAT_TO_IMP_MINUS_TACTICS_ARGS
  [IMP_def, imp_minus_correct, HOL_eqs, fun_inducts, mode]}

@{parse_entries (sig) PARSE_HOL_NAT_TO_IMP_PROOF_MODES
  [induction, simple, run_finish]}

signature HOL_NAT_TO_IMP_MINUS_TACTICS_BASE =
sig
include HAS_LOGGER

structure PA : PARSE_HOL_NAT_TO_IMP_MINUS_TACTICS_ARGS
structure PCA : PARSE_HOL_NAT_TO_IMP_MINUS_TACTICS_CONTEXT_ARGS

structure PM : PARSE_HOL_NAT_TO_IMP_PROOF_MODES
type mode = PM.key
val parse_mode : mode parser

type context_args = (HOL_Nat_To_IMP_Tailcalls_Tactics.IMP_def_retrieval,
  HOL_Nat_To_IMP_Tailcalls_Tactics.imp_minus_correct_retrieval,
  HOL_Nat_To_IMP_Tactics_Base.HOL_eqs_retrieval,
  HOL_Nat_To_IMP_Tailcalls_Tactics.fun_inducts_retrieval)
  PCA.entries
type args = (thm, thm list, thm list, thm list, mode) PA.entries

val correct_if_IMP_tailcall_correct_tac : HOL_Nat_To_IMP_Tailcalls_Tactics.IMP_def_retrieval ->
  Proof.context -> int -> tactic

val cook_tac : context_args -> mode option -> Proof.context -> int -> tactic

val context_arg_parsers : (ML_Code_Util.code parser, ML_Code_Util.code parser,
  ML_Code_Util.code parser, ML_Code_Util.code parser) PCA.entries
val arg_parsers : (thm context_parser, thm list context_parser, thm list context_parser,
  thm list context_parser, mode parser) PA.entries

end

structure HOL_Nat_To_IMP_Minus_Tactics_Base : HOL_NAT_TO_IMP_MINUS_TACTICS_BASE =
struct

val logger = Logger.setup_new_logger HOL_Nat_To_IMP_Tactics_Base.logger "HOL_Nat_To_IMP_Minus_Tactics_Base"

structure HTIT = HOL_Nat_To_IMP_Tailcalls_Tactics
structure TU = Tactic_Util
structure SUT = State_Update_Tracking
structure PU = Parse_Util

@{parse_entries (struct) PCA
  [get_IMP_def, get_imp_minus_correct, get_HOL_eqs, get_fun_inducts]}
@{parse_entries (struct) PA
  [IMP_def, imp_minus_correct, HOL_eqs, fun_inducts, mode]}

@{parse_entries (struct) PM
  [induction, simple, run_finish]}
type mode = PM.key
val parse_mode = PM.parse_key

type context_args = (HTIT.IMP_def_retrieval, HTIT.imp_minus_correct_retrieval,
  HOL_Nat_To_IMP_Tactics_Base.HOL_eqs_retrieval, HTIT.fun_inducts_retrieval)
  PCA.entries
type args = (thm, thm list, thm list, thm list, mode) PA.entries

(* destructors for IMP-Minus *)

val dest_terminates_with_res_IMP_Minus =
  \<^Const_fn>\<open>terminates_with_res_IMP_Minus for c s r v => \<open>{c=c, s=s, r=r, v=v}\<close>\<close>

val dest_tailcall_to_IMP_Minus =
  \<^Const_fn>\<open>tailcall_to_IMP_Minus for c => c\<close>

val dest_terminates_with_res_IMP_Minus_tailcall_to_IMP_Minus =
  dest_terminates_with_res_IMP_Minus #> (fn {c,...} => c) #> dest_tailcall_to_IMP_Minus

val dest_terminates_with_res_IMP_Minus_tailcall_to_IMP_Minus_prop =
  HOL_Nat_To_IMP_Util.dest_Trueprop #> dest_terminates_with_res_IMP_Minus_tailcall_to_IMP_Minus

fun correct_if_IMP_tailcall_correct_tac get_IMP_def ctxt =
  let fun tac c =
    let val solve_side_condition_tac =
      (HTIT.delete_IH_prems
      THEN' Simplifier.safe_simp_tac (ctxt addsimps (get_IMP_def ctxt c |> the_list)))
      |> SOLVED'
    in
      resolve_tac ctxt [@{thm terminates_with_res_IMP_Minus_if_terminates_with_res_IMP_TailcallI}]
      (*solve the invariant: invar f_IMP_tailcall*)
      THEN' solve_side_condition_tac
      (*solve the assumption: ''f.ret'' in vars f_IMP_tailcall*)
      THEN' solve_side_condition_tac
    end
  in
    HOL_Nat_To_IMP_Util.with_dest_concl_tac (fn _ => Pretty.block [
        Pretty.str "Could not find ",
        Syntax.pretty_term ctxt @{term terminates_with_res_IMP_Minus},
        Pretty.str " or ",
        Syntax.pretty_term ctxt @{term tailcall_to_IMP_Minus},
        Pretty.str " in conclusion."
      ] |> Pretty.string_of)
      dest_terminates_with_res_IMP_Minus_tailcall_to_IMP_Minus_prop ctxt tac
  end

val is_IMP_def_rec = Thm.concl_of
  #> HOL_To_HOL_Nat_Util.dest_eq_equals_prop #> snd
  #> Term.exists_subterm (curry (op aconv) @{term tTAIL})

fun cook_tac context_args mode ctxt =
  let
    val get_fun_inducts = PCA.get_get_fun_inducts context_args
    val get_IMP_def = PCA.get_get_IMP_def context_args
    val get_imp_minus_correct = PCA.get_get_imp_minus_correct context_args
    val get_HOL_eqs = PCA.get_get_HOL_eqs context_args
    val should_setup = case mode of
        SOME (PM.induction _) => true
      | SOME (PM.simple _) => true
      | SOME (PM.run_finish _) => false
      | NONE => true
    fun start_run_finish_tac {c,...}=
      let val is_induction = case mode of
          SOME (PM.induction _) => true
        | SOME (PM.simple _) => false
        | SOME (PM.run_finish _) => false
        | NONE => get_IMP_def ctxt c |> Option.map is_IMP_def_rec |> the_default false
      in
        HTIT.start_run_finish_tac is_induction get_fun_inducts get_IMP_def get_imp_minus_correct
          get_HOL_eqs ctxt
      end
  in
    (fn _ => fn st => (@{log Logger.INFO} ctxt (K "👨‍🍳 Cooking 👩‍🍳"); all_tac st))
    THEN' (if should_setup then correct_if_IMP_tailcall_correct_tac get_IMP_def ctxt else K all_tac)
    THEN' HTIT.with_dest_terminates_with_res_IMP_Tailcall_prop ctxt start_run_finish_tac
    THEN' (fn _ => fn st => if Thm.no_prems st
      then (@{log Logger.INFO} ctxt (K "Dinner served! 😍🍲😍"); all_tac st)
      else (@{log Logger.INFO} ctxt (K "Overcooked 🔥🤯"); all_tac st))
  end

val arg_parsers = {
  IMP_def = SOME PU.thm,
  imp_minus_correct = SOME
    (PU.nonempty_thms (K "must provide at least one IMP correctness theorem")),
  HOL_eqs = SOME (PU.nonempty_thms (K "must provide at least one equation for the HOL term")),
  fun_inducts = SOME (PU.nonempty_thms (K "must provide at least one induction rule")),
  mode = SOME parse_mode
}

val context_arg_parsers = {
  get_IMP_def = SOME (PU.nonempty_code (K "retrieval for IMP definition may not be empty")),
  get_imp_minus_correct = SOME (PU.nonempty_code
    (K "retrieval for IMP correctness theorems may not be empty")),
  get_HOL_eqs = SOME (PU.nonempty_code (K "retrieval for HOL term equations may not be empty")),
  get_fun_inducts = SOME (PU.nonempty_code (K "retrieval for induction rules may not be empty"))
}

end

signature HOL_NAT_TO_IMP_MINUS_TACTICS =
sig
  structure Data : GENERIC_DATA

  val get_args : Context.generic -> HOL_Nat_To_IMP_Minus_Tactics_Base.context_args
  val map_args : (HOL_Nat_To_IMP_Minus_Tactics_Base.context_args ->
    HOL_Nat_To_IMP_Minus_Tactics_Base.context_args) ->
    Context.generic -> Context.generic

  val get_get_IMP_def : Context.generic -> HOL_Nat_To_IMP_Tailcalls_Tactics.IMP_def_retrieval
  val map_get_IMP_def : (HOL_Nat_To_IMP_Tailcalls_Tactics.IMP_def_retrieval ->
    HOL_Nat_To_IMP_Tailcalls_Tactics.IMP_def_retrieval) -> Context.generic -> Context.generic

  val get_get_imp_minus_correct : Context.generic ->
    HOL_Nat_To_IMP_Tailcalls_Tactics.imp_minus_correct_retrieval
  val map_get_imp_minus_correct : (HOL_Nat_To_IMP_Tailcalls_Tactics.imp_minus_correct_retrieval ->
    HOL_Nat_To_IMP_Tailcalls_Tactics.imp_minus_correct_retrieval) -> Context.generic ->
    Context.generic

  val get_get_HOL_eqs : Context.generic -> HOL_Nat_To_IMP_Tactics_Base.HOL_eqs_retrieval
  val map_get_HOL_eqs : (HOL_Nat_To_IMP_Tactics_Base.HOL_eqs_retrieval ->
    HOL_Nat_To_IMP_Tactics_Base.HOL_eqs_retrieval) -> Context.generic -> Context.generic

  val get_get_fun_inducts : Context.generic -> HOL_Nat_To_IMP_Tailcalls_Tactics.fun_inducts_retrieval
  val map_get_fun_inducts : (HOL_Nat_To_IMP_Tailcalls_Tactics.fun_inducts_retrieval ->
    HOL_Nat_To_IMP_Tailcalls_Tactics.fun_inducts_retrieval) -> Context.generic -> Context.generic

  val cook_tac : HOL_Nat_To_IMP_Minus_Tactics_Base.mode option -> Proof.context -> int -> tactic

  val binding : binding

  val attribute : (ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code)
    HOL_Nat_To_IMP_Minus_Tactics_Base.PCA.entries * Position.T -> attribute
  val parse_attribute : attribute parser
  val setup_attribute : string option -> local_theory -> local_theory

  val parse_method : (Proof.context -> Method.method) context_parser
  val setup_method : string option -> local_theory -> local_theory
end

functor HOL_Nat_To_IMP_Minus_Tactics(A : sig
    structure FIA : FUNCTOR_INSTANCE_ARGS
    val init_args : HOL_Nat_To_IMP_Minus_Tactics_Base.context_args
  end) : HOL_NAT_TO_IMP_MINUS_TACTICS =
struct

structure HITA = HOL_Nat_To_IMP_Minus_Tactics_Base
structure PA = HITA.PA
structure PCA = HITA.PCA
structure PM = HITA.PM
structure FIU = Functor_Instance_Util(A.FIA)
structure MCU = ML_Code_Util
structure PU = Parse_Util

structure Data = Generic_Data(struct
  type T = HITA.context_args
  val empty = A.init_args
  val merge = fst
end)

val get_args = Data.get
val map_args = Data.map

val get_get_IMP_def = PCA.get_get_IMP_def o get_args
val map_get_IMP_def = map_args o PCA.map_get_IMP_def

val get_get_imp_minus_correct = PCA.get_get_imp_minus_correct o get_args
val map_get_imp_minus_correct = map_args o PCA.map_get_imp_minus_correct

val get_get_HOL_eqs = PCA.get_get_HOL_eqs o get_args
val map_get_HOL_eqs = map_args o PCA.map_get_HOL_eqs

val get_get_fun_inducts = PCA.get_get_fun_inducts o get_args
val map_get_fun_inducts = map_args o PCA.map_get_fun_inducts

fun cook_tac mode ctxt = HITA.cook_tac (get_args (Context.Proof ctxt)) mode ctxt

val binding = FIU.mk_binding_id_prefix "cook"

val parse_attribute_arg_entries =
  let
    val parsers = HITA.context_arg_parsers
    val parse_value = PCA.parse_entry (PCA.get_get_IMP_def parsers)
      (PCA.get_get_imp_minus_correct parsers) (PCA.get_get_HOL_eqs parsers)
      (PCA.get_get_fun_inducts parsers)
    val parse_entry = Parse_Key_Value.parse_entry PCA.parse_key PU.eq parse_value
  in PCA.parse_entries_required Parse.and_list1 [] parse_entry (PCA.empty_entries ()) end

fun attribute (entries, pos) =
  let
    fun code_PCA_op operation = MCU.flat_read ["HOL_Nat_To_IMP_Minus_Tactics_Base.PCA", ".", operation]
    val code_from_key = code_PCA_op o PCA.key_to_string
    fun code_from_entry (PCA.get_IMP_def c) = c
      | code_from_entry (PCA.get_imp_minus_correct c) = c
      | code_from_entry (PCA.get_HOL_eqs c) = c
      | code_from_entry (PCA.get_fun_inducts c) = c
    val code_entries = PCA.key_entry_entries_from_entries entries
      |> map (fn (k, v) => code_from_key k @ MCU.atomic (code_from_entry v))
      |> MCU.list
    val code =
      FIU.code_struct_op "map_args" @ MCU.atomic (code_PCA_op "merge_entries" @
      MCU.atomic (code_PCA_op "entries_from_entry_list" @ code_entries))
  in ML_Attribute.run_map_context (code, pos) end

val parse_attribute = (parse_attribute_arg_entries |> PU.position) >> attribute

val setup_attribute = Attrib.local_setup binding
  (Parse.!!! parse_attribute |> Scan.lift) o
  the_default ("set HOL to IMP tactics arguments (" ^ FIU.FIA.full_name ^ ")")

val parse_method_arg_entries =
  let
    val parsers = HITA.arg_parsers
    val parse_value = PA.parse_entry (PA.get_IMP_def parsers) (PA.get_imp_minus_correct parsers)
      (PA.get_HOL_eqs parsers) (PA.get_fun_inducts parsers) (PA.get_mode parsers |> Scan.lift)
    val parse_entry = Parse_Key_Value.parse_entry' (Scan.lift PA.parse_key) (Scan.lift PU.eq)
      parse_value
  in PA.parse_entries_required' Parse.and_list1' [] parse_entry (PA.empty_entries ()) end

val parse_method =
  let
    val default_entries = PA.empty_entries ()
    fun mk_retrieval t = Option.map (K o K o SOME) t
    fun merge_entries {IMP_def, imp_minus_correct, HOL_eqs, fun_inducts,...} =
      {get_IMP_def = mk_retrieval IMP_def, get_imp_minus_correct = mk_retrieval imp_minus_correct,
        get_HOL_eqs = mk_retrieval HOL_eqs, get_fun_inducts = mk_retrieval fun_inducts}
      |> PCA.merge_entries
      |> map_args
      |> Context.proof_map
  in
    (PU.optional' (parse_method_arg_entries |> Parse.!!!!) default_entries)
    >> (fn entries => merge_entries entries
      #> SIMPLE_METHOD' o cook_tac (PA.get_mode_safe entries))
  end

val setup_method = Method.local_setup binding parse_method o
  the_default ("HOL to IMP tactics (" ^ FIU.FIA.full_name ^ ")")

end
