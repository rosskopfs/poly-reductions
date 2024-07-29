(*  Title:  Refinements/hol_to_imp_tactics.ML
    Author: Kevin Kappelmann

HOL to IMP tactics with arguments from context.
*)
@{parse_entries (sig) PARSE_HOL_TO_IMP_TACTICS_CONTEXT_ARGS
  [get_IMP_def, get_func_corrects, get_HOL_eqs, get_HOL_inducts]}

@{parse_entries (sig) PARSE_HOL_TO_IMP_MINUS_TACTICS_ARGS
  [IMP_def, func_corrects, HOL_eqs, HOL_inducts, mode]}

@{parse_entries (sig) PARSE_HOL_TO_IMP_TAILCALLS_MODES
  [tailcall, nontailcall]}

signature HOL_TO_IMP_MINUS_TACTICS_ARGS =
sig
include HAS_LOGGER

(*
val preprocess_tac : HOL_To_IMP_Tailcalls_Tactics.IMP_def_retrieval -> Proof.context -> int ->
  tactic

(*retrieve induction rule for HOL constant*)
type HOL_inducts_retrieval = Proof.context -> term -> (thm list) option
val get_HOL_inducts : HOL_inducts_retrieval

val setup_induction_tac : HOL_inducts_retrieval -> Proof.context -> int -> tactic

structure PA : PARSE_HOL_TO_IMP_MINUS_TACTICS_ARGS
structure PCA : PARSE_HOL_TO_IMP_TACTICS_CONTEXT_ARGS

structure PM : PARSE_HOL_TO_IMP_TAILCALLS_MODES
type mode = PM.key
val parse_mode : mode parser

type context_args = (HOL_To_IMP_Tailcalls_Tactics.IMP_def_retrieval,
  HOL_To_IMP_Tailcalls_Tactics.func_corrects_retrieval,
  HOL_To_IMP_Tactics_Base.HOL_eqs_retrieval, HOL_inducts_retrieval) PCA.entries
type args = (thm, thm list, thm list, thm list, mode) PA.entries

val cook_tac : context_args -> mode -> Proof.context -> int -> tactic

val context_arg_parsers : (ML_Code_Util.code parser, ML_Code_Util.code parser,
  ML_Code_Util.code parser, ML_Code_Util.code parser) PCA.entries
val arg_parsers : (thm context_parser, thm list context_parser, thm list context_parser,
  thm list context_parser, mode parser) PA.entries
*)

end

structure HOL_To_IMP_Minus_Tactics_Args (* : HOL_TO_IMP_MINUS_TACTICS_ARGS *) =
struct

val logger = Logger.setup_new_logger HOL_To_IMP_Tactics_Base.logger "HOL_To_IMP_Minus_Tactics_Args"

structure GU = General_Util
structure HTIB = HOL_To_IMP_Tactics_Base
structure HTIU = HOL_To_IMP_Util
structure HTIT = HOL_To_IMP_Tailcalls_Tactics
structure TU = Tactic_Util
structure SUT = State_Update_Tracking
structure SUTIT = State_Update_Tracking_IMP_Tailcalls
structure PU = Parse_Util

type HOL_inducts_retrieval = Proof.context -> term -> (thm list) option
fun get_HOL_inducts ctxt = try (#inducts o Function.get_info ctxt) #> Option.join

@{parse_entries (struct) PCA
  [get_IMP_def, get_func_corrects, get_HOL_eqs, get_HOL_inducts]}
@{parse_entries (struct) PA
  [IMP_def, func_corrects, HOL_eqs, HOL_inducts, mode]}

@{parse_entries (struct) PM
  [tailcall, nontailcall]}
type mode = PM.key
val parse_mode = PM.parse_key

type context_args = (HTIT.IMP_def_retrieval, HTIT.func_corrects_retrieval,
  HTIB.HOL_eqs_retrieval, HOL_inducts_retrieval) PCA.entries
type args = (thm, thm list, thm list, thm list, mode) PA.entries

fun cook_tac context_args mode ctxt =
  let
    val get_HOL_inducts = PCA.get_get_HOL_inducts context_args
    val get_IMP_def = PCA.get_get_IMP_def context_args
    val get_func_corrects = PCA.get_get_func_corrects context_args
    val get_HOL_eqs = PCA.get_get_HOL_eqs context_args
    val is_tailcall = (case mode of PM.tailcall _ => true | PM.nontailcall _ => false)
  in
    (fn _ => fn st => (@{log Logger.INFO} ctxt (K "👨‍🍳 Cooking 👩‍🍳"); all_tac st))
    THEN' HTIT.correct_tac is_tailcall get_HOL_inducts get_IMP_def get_func_corrects get_HOL_eqs ctxt
    THEN' (fn _ => fn st => if Thm.no_prems st
      then (@{log Logger.INFO} ctxt (K "Dinner served! 😍🍲😍"); all_tac st)
      else (@{log Logger.INFO} ctxt (K "Overcooked 🔥🤯"); all_tac st))
  end

val arg_parsers = {
  IMP_def = SOME PU.thm,
  func_corrects = SOME
    (PU.nonempty_thms (K "must provide at least one functional correctness theorem")),
  HOL_eqs = SOME (PU.nonempty_thms (K "must provide at least one equation for the HOL term")),
  HOL_inducts = SOME (PU.nonempty_thms (K "must provide at least one induction rule")),
  mode = SOME parse_mode
}

val context_arg_parsers = {
  get_IMP_def = SOME (PU.nonempty_code (K "retrieval for IMP definition may not be empty")),
  get_func_corrects = SOME (PU.nonempty_code
    (K "retrieval for functional correctness theorems may not be empty")),
  get_HOL_eqs = SOME (PU.nonempty_code (K "retrieval for HOL term equations may not be empty")),
  get_HOL_inducts = SOME (PU.nonempty_code (K "retrieval for induction rules may not be empty"))
}

end

signature HOL_TO_IMP_TACTICS =
sig
  structure Data : GENERIC_DATA

  val get_args : Context.generic -> HOL_To_IMP_Minus_Tactics_Args.context_args
  val map_args : (HOL_To_IMP_Minus_Tactics_Args.context_args -> HOL_To_IMP_Minus_Tactics_Args.context_args) ->
    Context.generic -> Context.generic

  val get_get_IMP_def : Context.generic -> HOL_To_IMP_Tailcalls_Tactics.IMP_def_retrieval
  val map_get_IMP_def : (HOL_To_IMP_Tailcalls_Tactics.IMP_def_retrieval ->
    HOL_To_IMP_Tailcalls_Tactics.IMP_def_retrieval) -> Context.generic -> Context.generic

  val get_get_func_corrects : Context.generic -> HOL_To_IMP_Tailcalls_Tactics.func_corrects_retrieval
  val map_get_func_corrects : (HOL_To_IMP_Tailcalls_Tactics.func_corrects_retrieval ->
    HOL_To_IMP_Tailcalls_Tactics.func_corrects_retrieval) -> Context.generic -> Context.generic

  val get_get_HOL_eqs : Context.generic -> HOL_To_IMP_Tactics_Base.HOL_eqs_retrieval
  val map_get_HOL_eqs : (HOL_To_IMP_Tactics_Base.HOL_eqs_retrieval ->
    HOL_To_IMP_Tactics_Base.HOL_eqs_retrieval) -> Context.generic -> Context.generic

  val get_get_HOL_inducts : Context.generic -> HOL_To_IMP_Minus_Tactics_Args.HOL_inducts_retrieval
  val map_get_HOL_inducts : (HOL_To_IMP_Minus_Tactics_Args.HOL_inducts_retrieval ->
    HOL_To_IMP_Minus_Tactics_Args.HOL_inducts_retrieval) -> Context.generic -> Context.generic

  val cook_tac : HOL_To_IMP_Minus_Tactics_Args.mode -> Proof.context -> int -> tactic

  val binding : binding

  val attribute : (ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code)
    HOL_To_IMP_Minus_Tactics_Args.PCA.entries * Position.T -> attribute
  val parse_attribute : attribute parser
  val setup_attribute : string option -> local_theory -> local_theory

  val parse_method : (Proof.context -> Method.method) context_parser
  val setup_method : string option -> local_theory -> local_theory
end

functor HOL_To_IMP_Tactics(A : sig
    structure FIA : FUNCTOR_INSTANCE_ARGS
    val init_args : HOL_To_IMP_Minus_Tactics_Args.context_args
  end) : HOL_TO_IMP_TACTICS =
struct

structure HITA = HOL_To_IMP_Minus_Tactics_Args
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

val get_get_func_corrects = PCA.get_get_func_corrects o get_args
val map_get_func_corrects = map_args o PCA.map_get_func_corrects

val get_get_HOL_eqs = PCA.get_get_HOL_eqs o get_args
val map_get_HOL_eqs = map_args o PCA.map_get_HOL_eqs

val get_get_HOL_inducts = PCA.get_get_HOL_inducts o get_args
val map_get_HOL_inducts = map_args o PCA.map_get_HOL_inducts

fun cook_tac mode ctxt = HITA.cook_tac (get_args (Context.Proof ctxt)) mode ctxt

val binding = FIU.mk_binding_id_prefix "cook"

val parse_attribute_arg_entries =
  let
    val parsers = HITA.context_arg_parsers
    val parse_value = PCA.parse_entry (PCA.get_get_IMP_def parsers)
      (PCA.get_get_func_corrects parsers) (PCA.get_get_HOL_eqs parsers)
      (PCA.get_get_HOL_inducts parsers)
    val parse_entry = Parse_Key_Value.parse_entry PCA.parse_key PU.eq parse_value
  in PCA.parse_entries_required Parse.and_list1 [] parse_entry (PCA.empty_entries ()) end

fun attribute (entries, pos) =
  let
    fun code_PCA_op operation = MCU.flat_read ["HOL_To_IMP_Minus_Tactics_Args.PCA", ".", operation]
    val code_from_key = code_PCA_op o PCA.key_to_string
    fun code_from_entry (PCA.get_IMP_def c) = c
      | code_from_entry (PCA.get_func_corrects c) = c
      | code_from_entry (PCA.get_HOL_eqs c) = c
      | code_from_entry (PCA.get_HOL_inducts c) = c
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
    val parse_value = PA.parse_entry (PA.get_IMP_def parsers) (PA.get_func_corrects parsers)
      (PA.get_HOL_eqs parsers) (PA.get_HOL_inducts parsers) (PA.get_mode parsers |> Scan.lift)
    val parse_entry = Parse_Key_Value.parse_entry' (Scan.lift PA.parse_key) (Scan.lift PU.eq)
      parse_value
  in PA.parse_entries_required' Parse.and_list1' [] parse_entry (PA.empty_entries ()) end

val parse_method =
  let
    val default_entries = PA.empty_entries () |> fold PA.set_entry [PA.mode (PM.key PM.nontailcall)]
    fun mk_retrieval t = Option.map (K o K o SOME) t
    fun merge_entries {IMP_def, func_corrects, HOL_eqs, HOL_inducts,...} =
      {get_IMP_def = mk_retrieval IMP_def, get_func_corrects = mk_retrieval func_corrects,
        get_HOL_eqs = mk_retrieval HOL_eqs, get_HOL_inducts = mk_retrieval HOL_inducts}
      |> PCA.merge_entries
      |> map_args
      |> Context.proof_map
  in
    (PU.optional' (parse_method_arg_entries |> Parse.!!!!) default_entries)
    >> (fn entries => merge_entries entries
      #> SIMPLE_METHOD' o cook_tac (PA.get_mode entries))
  end

val setup_method = Method.local_setup binding parse_method o
  the_default ("HOL to IMP tactics (" ^ FIU.FIA.full_name ^ ")")

end
