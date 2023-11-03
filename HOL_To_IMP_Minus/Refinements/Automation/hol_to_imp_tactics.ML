(*  Title:  Views/IMP_Tailcalls/hol_to_imp_tactics.ML
    Author: Kevin Kappelmann

HOL to IMP tactics with arguments from context.
*)
@{parse_entries (sig) PARSE_HOL_TO_IMP_TACTICS_ARGS
  [IMP_defs, func_corrects, HOL_eqs, induction, mode]}

@{parse_entries (sig) PARSE_HOL_TO_IMP_CONTEXT_ARGS
  [IMP_defs, func_corrects, HOL_eqs, induction]}

@{parse_entries (sig) PARSE_HOL_TO_IMP_TAILCALLS_MODES
  [tailcall, nontailcall]}

signature HOL_TO_IMP_TACTICS_ARGS =
sig
  val preprocess_tac : thm list -> Proof.context -> int -> tactic

  structure PA : PARSE_HOL_TO_IMP_TACTICS_ARGS
  structure PCA : PARSE_HOL_TO_IMP_CONTEXT_ARGS
  val PCA_entries_from_PA_entries : ('a, 'b, 'c, 'd, 'e) PA.entries -> ('a, 'b, 'c, 'd) PCA.entries
  val PA_entries_from_PCA_entries : ('a, 'b, 'c, 'd) PCA.entries -> 'e ->
    ('a, 'b, 'c, 'd, 'e) PA.entries

  structure PM : PARSE_HOL_TO_IMP_TAILCALLS_MODES
  type mode = PM.key
  val parse_mode : mode parser

  type args = (thm list, thm list, thm list, HOL_To_IMP_Tailcalls_Tactics.induction_retrieval,
    mode) PA.entries
  type context_args = (Proof.context -> thm list, Proof.context -> thm list, Proof.context -> thm list,
    HOL_To_IMP_Tailcalls_Tactics.induction_retrieval) PCA.entries

  val cooker_tac : args -> Proof.context -> int -> tactic

  val arg_parsers : (thm list context_parser, thm list context_parser, thm list context_parser,
    thm list option context_parser, mode parser) PA.entries
end

structure HOL_To_IMP_Tactics_Args : HOL_TO_IMP_TACTICS_ARGS =
struct

structure HITT = HOL_To_IMP_Tailcalls_Tactics
structure PU = Parse_Util

fun preprocess_tac IMP_program_defs ctxt =
  eresolve_tac ctxt @{thms tailcall_to_IMP_Minus_correct_if_correct}
  THEN' REPEAT_DETERM_N 2 o (EqSubst.eqsubst_tac ctxt [0] IMP_program_defs
    THEN' Simplifier.simp_tac ctxt)

@{parse_entries (struct) PA
  [IMP_defs, func_corrects, HOL_eqs, induction, mode]}
@{parse_entries (struct) PCA
  [IMP_defs, func_corrects, HOL_eqs, induction]}

fun PCA_entries_from_PA_entries {IMP_defs = IMP_defs, func_corrects = func_corrects,
  HOL_eqs = HOL_eqs, induction = induction,...} =
  {IMP_defs = IMP_defs, func_corrects = func_corrects, HOL_eqs = HOL_eqs, induction = induction}
fun PA_entries_from_PCA_entries {IMP_defs = IMP_defs, func_corrects = func_corrects,
  HOL_eqs = HOL_eqs, induction = induction} mode = { IMP_defs = IMP_defs,
    func_corrects = func_corrects, HOL_eqs = HOL_eqs, induction = induction , mode = SOME mode}

@{parse_entries (struct) PM
  [tailcall, nontailcall]}

type mode = PM.key
val parse_mode = PM.parse_key

type args = (thm list, thm list, thm list, HITT.induction_retrieval, mode) PA.entries
type context_args = (Proof.context -> thm list, Proof.context -> thm list, Proof.context -> thm list,
  HITT.induction_retrieval) PCA.entries

fun cooker_tac args ctxt =
  let
    val IMP_program_defs = PA.get_IMP_defs args
    val IMP_func_corrects = PA.get_func_corrects args
    val HOL_eqs = PA.get_HOL_eqs args
  in
    K (print_tac ctxt "Cooking 👨‍🍳👩‍🍳")
    THEN' preprocess_tac IMP_program_defs ctxt
    THEN' (case PA.get_mode args of
      PM.tailcall _ => HITT.setup_induction_tac (PA.get_induction args) ctxt
      | _ => K all_tac)
    THEN_ALL_NEW HITT.start_run_finish_tac IMP_program_defs IMP_func_corrects HOL_eqs ctxt
    THEN' (fn _ => fn st => if Thm.nprems_of st = 0
      then (writeln "Dinner served! 😍😍😍"; all_tac st)
      else (writeln "Overcooked 🔥🤯"; all_tac st))
  end

val arg_parsers = {
  IMP_defs = SOME (PU.nonempty_thms (K "must provide at least one IMP definition")),
  func_corrects = SOME (PU.nonempty_thms
    (K "must provide at least one functional correctness theorem")),
  HOL_eqs = SOME (PU.nonempty_thms (K "must provide at least one equation for the HOL term")),
  induction = SOME (K "must provide at least one induction rule" |> PU.nonempty_thms |> PU.option'),
  mode = SOME parse_mode
}

end

signature HOL_TO_IMP_TACTICS =
sig
  structure Data : GENERIC_DATA

  val get_args : Context.generic -> HOL_To_IMP_Tactics_Args.context_args
  val map_args : (HOL_To_IMP_Tactics_Args.context_args -> HOL_To_IMP_Tactics_Args.context_args) ->
    Context.generic -> Context.generic

  val get_IMP_defs : Context.generic -> Proof.context -> thm list
  val map_IMP_defs : ((Proof.context -> thm list) -> Proof.context -> thm list) ->
    Context.generic -> Context.generic

  val get_func_corrects : Context.generic -> Proof.context -> thm list
  val map_func_corrects : ((Proof.context -> thm list) -> Proof.context -> thm list) ->
    Context.generic -> Context.generic

  val get_HOL_eqs : Context.generic -> Proof.context -> thm list
  val map_HOL_eqs : ((Proof.context -> thm list) -> Proof.context -> thm list) ->
    Context.generic -> Context.generic

  val get_induction : Context.generic -> HOL_To_IMP_Tailcalls_Tactics.induction_retrieval
  val map_induction : (HOL_To_IMP_Tailcalls_Tactics.induction_retrieval ->
    HOL_To_IMP_Tailcalls_Tactics.induction_retrieval) -> Context.generic -> Context.generic

  val cooker_context_args_tac : HOL_To_IMP_Tactics_Args.context_args ->
    HOL_To_IMP_Tactics_Args.mode -> Proof.context -> int -> tactic
  val cooker_tac : HOL_To_IMP_Tactics_Args.mode -> Proof.context -> int -> tactic

  val binding : binding

  val attribute : (ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code, ML_Code_Util.code)
    HOL_To_IMP_Tactics_Args.PCA.entries * Position.T -> attribute
  val parse_attribute : attribute parser
  val setup_attribute : string option -> local_theory -> local_theory

  val parse_method : (Proof.context -> Method.method) context_parser
  val setup_method : string option -> local_theory -> local_theory
end

functor HOL_To_IMP_Tactics(A : sig
    structure FIA : FUNCTOR_INSTANCE_ARGS
    val init_args : HOL_To_IMP_Tactics_Args.context_args
  end) : HOL_TO_IMP_TACTICS =
struct

structure HITA = HOL_To_IMP_Tactics_Args
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

val get_IMP_defs = PCA.get_IMP_defs o get_args
val map_IMP_defs = map_args o PCA.map_IMP_defs

val get_func_corrects = PCA.get_func_corrects o get_args
val map_func_corrects = map_args o PCA.map_func_corrects

val get_HOL_eqs = PCA.get_HOL_eqs o get_args
val map_HOL_eqs = map_args o PCA.map_HOL_eqs

val get_induction = PCA.get_induction o get_args
val map_induction = map_args o PCA.map_induction

fun cooker_context_args_tac context_args mode ctxt =
  let
    fun apply_ctxt f = f ctxt
    val context_args = context_args
      |> PCA.map_IMP_defs apply_ctxt
      |> PCA.map_func_corrects apply_ctxt
      |> PCA.map_HOL_eqs apply_ctxt
    val args = HITA.PA_entries_from_PCA_entries context_args mode
  in HITA.cooker_tac args ctxt end

fun cooker_tac mode ctxt = cooker_context_args_tac (get_args (Context.Proof ctxt)) mode ctxt

val binding = FIU.mk_binding_id_prefix "cooker"

val context_arg_parsers = {
  IMP_defs = SOME (PU.nonempty_code (K "retrieval for IMP definition may not be empty")),
  func_corrects = SOME (PU.nonempty_code
    (K "retrieval for functional correctness theorems may not be empty")),
  HOL_eqs = SOME (PU.nonempty_code (K "retrieval for HOL term equations may not be empty")),
  induction = SOME (PU.nonempty_code (K "retrieval for induction rules may not be empty"))
}

val parse_attribute_arg_entries =
  let
    val parsers = context_arg_parsers
    val parse_value = PCA.parse_entry (PCA.get_IMP_defs parsers)
      (PCA.get_func_corrects parsers) (PCA.get_HOL_eqs parsers) (PCA.get_induction parsers)
    val parse_entry = Parse_Key_Value.parse_entry PCA.parse_key PU.eq parse_value
  in PCA.parse_entries_required Parse.and_list1 [] parse_entry (PCA.empty_entries ()) end

fun attribute (entries, pos) =
  let
    fun code_PCA_op operation = MCU.flat_read ["HOL_To_IMP_Tactics_Args.PCA", ".", operation]
    val code_from_key = code_PCA_op o PCA.key_to_string
    fun code_from_entry (PCA.IMP_defs c) = c
      | code_from_entry (PCA.func_corrects c) = c
      | code_from_entry (PCA.HOL_eqs c) = c
      | code_from_entry (PCA.induction c) = c
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
    val parsers = HITA.arg_parsers |> HITA.PCA_entries_from_PA_entries
    val parse_value = PCA.parse_entry (PCA.get_IMP_defs parsers)
      (PCA.get_func_corrects parsers) (PCA.get_HOL_eqs parsers) (PCA.get_induction parsers)
    val parse_entry = Parse_Key_Value.parse_entry' (Scan.lift PCA.parse_key) (Scan.lift PU.eq) parse_value
  in PCA.parse_entries_required' Parse.and_list1' [] parse_entry (PCA.empty_entries ()) end

val parse_method =
  let
    val parse_mode = Scan.optional (PU.parenths (PA.get_mode HITA.arg_parsers |> Parse.!!!))
      (PM.key PM.nontailcall)
    fun ignore_ctxt opt = Option.map K opt
    val merge_entries = PCA.map_IMP_defs_safe ignore_ctxt
      #> PCA.map_func_corrects_safe ignore_ctxt
      #> PCA.map_HOL_eqs_safe ignore_ctxt
      #> PCA.map_induction_safe (Option.map (K o K))
      #> PCA.merge_entries
      #> map_args
      #> Context.proof_map
  in
    Scan.lift parse_mode
    -- (parse_method_arg_entries |> Parse.!!!! |> PU.option')
    >> (fn (mode, entries) => the_default I (Option.map merge_entries entries)
      #> SIMPLE_METHOD' o cooker_tac mode)
  end

val setup_method = Method.local_setup binding parse_method o
  the_default ("HOL to IMP tactics arguments (" ^ FIU.FIA.full_name ^ ")")

end