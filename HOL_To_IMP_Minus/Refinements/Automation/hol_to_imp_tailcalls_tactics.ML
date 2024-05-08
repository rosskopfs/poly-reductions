(*  Title:  Refinements/hol_to_imp_tailcalls_tactics.ML
    Author: Kevin Kappelmann

Tactics to run IMP-Tailcall programs, track their states changes, and prove their
correspondence with HOL programs.
*)
signature HOL_TO_IMP_TAILCALLS_TACTICS =
sig
include HAS_LOGGER

(*retrieve definition equality theorem from program constant*)
type IMP_def_retrieval = Proof.context -> term -> thm option
val get_IMP_def : IMP_def_retrieval

val start_tac : IMP_def_retrieval -> Proof.context -> int -> tactic
val seq_tac : Proof.context -> int -> tactic
val assign_tac : Proof.context -> int -> tactic

(*retrieve functional correctness theorem from program constant*)
type func_corrects_retrieval = Proof.context -> term -> thm list option
val get_func_corrects : func_corrects_retrieval

val call_tac : func_corrects_retrieval -> Proof.context -> int -> tactic

val if_tac : Proof.context -> int -> tactic

val run_single_tac : func_corrects_retrieval -> Proof.context -> int -> tactic

val run_tac : func_corrects_retrieval -> Proof.context -> int -> tactic

val start_run_tac : IMP_def_retrieval -> func_corrects_retrieval -> Proof.context -> int -> tactic

val finish_non_tailcall_tac : HOL_To_IMP_Tactics_Base.HOL_eqs_retrieval -> Proof.context -> int -> tactic

val tailcall_tac : Proof.context -> int -> tactic

val get_IMP_keys : HOL_To_IMP_Tactics_Base.IMP_keys_retrieval
val rewrite_insert_current_keys_eq_tac : Proof.context -> int -> tactic

val finish_tailcall_tac : HOL_To_IMP_Tactics_Base.HOL_eqs_retrieval -> Proof.context -> int -> tactic
val finish_tac : HOL_To_IMP_Tactics_Base.HOL_eqs_retrieval -> Proof.context -> int -> tactic

val start_run_finish_tac : IMP_def_retrieval  -> func_corrects_retrieval ->
  HOL_To_IMP_Tactics_Base.HOL_eqs_retrieval -> Proof.context -> int -> tactic

end

structure HOL_To_IMP_Tailcalls_Tactics : HOL_TO_IMP_TAILCALLS_TACTICS =
struct

val logger = Logger.setup_new_logger HOL_To_IMP_Tactics_Base.logger "HOL_To_IMP_Tailcalls_Tactics"

structure HTITB = HOL_To_IMP_Tactics_Base
structure GU = General_Util
structure TU = Tactic_Util
structure HTIU = HOL_To_IMP_Util
structure SUTIT = State_Update_Tracking_IMP_Tailcalls
structure SUT = State_Update_Tracking

structure Seq = HTIU.Seq

type IMP_def_retrieval = Proof.context -> term -> thm option
val get_IMP_def = Compile_Nat.get_compiled_const_def

val arg2_of_4_conv = Conv.fun_conv o Conv.fun_conv o Conv.arg_conv

fun big_step_program_conv get_IMP_def ctxt ct =
  let val get_def = Thm.term_of #> SUTIT.dest_IMP_big_step
    #> (fn ((c, _), _, _) => get_IMP_def ctxt c)
  in (case try get_def ct of
      SOME (SOME thm) => Conv.rewr_conv thm |> Conv.arg1_conv |> arg2_of_4_conv
    | SOME NONE => (@{log Logger.WARN} ctxt (K "Could not retrieve IMP definition equality theorem");
        Conv.no_conv)
    | NONE => (@{log Logger.WARN} ctxt (K "Could not destruct IMP big step state to retrieve theorem");
        Conv.no_conv)) ct
  end

fun big_step_program_prem_conv get_IMP_def i =
  Conversion_Util.repeat_forall_conv (fn _ => fn ctxt =>
    Conversion_Util.move_prem_to_front_conv i
    then_conv Conv.prems_conv 1
      (big_step_program_conv get_IMP_def ctxt |> HOLogic.Trueprop_conv))

fun rewrite_big_step_program_tac get_IMP_def =
  let fun tac ctxt prems = case GU.find_first_index (can SUTIT.dest_IMP_big_step_prop) prems of
      SOME (i, _) => CONVERSION (big_step_program_prem_conv get_IMP_def (i + 1) ctxt)
    | NONE => (@{log Logger.WARN} ctxt (fn _ => Pretty.block [
          Pretty.str "Could not find big step in premises ",
          SpecCheck_Show.list (Syntax.pretty_term ctxt) prems
        ] |> Pretty.string_of);
        K no_tac)
  in TU.FOCUS_PARAMS_CTXT' (TU.SUBGOAL_STRIPPED (fst o snd) o tac) end

fun start_tac get_IMP_def ctxt =
  rewrite_big_step_program_tac get_IMP_def ctxt
  THEN' SUTIT.init_state_eq_tac ctxt

val seq_tac = HTITB.seq_tac @{thms tSeq_E}

val assign_update_simps = @{thms AExp.aval.simps AExp.atomVal.simps}
val assign_tac = HTITB.assign_tac @{thms tAssignD} assign_update_simps

val if_tac = HTITB.if_tac @{thms tIf_E}

type func_corrects_retrieval = Proof.context -> term -> thm list option
val get_func_corrects = Option.map single oo HOL_To_IMP_Minus_Goal_Command.get_func_corrects

val dest_Call = \<^Const_fn>\<open>tCall for c k => \<open>(c, k)\<close>\<close>
val dest_Call_IMP_big_step_state =
  SUTIT.dest_IMP_big_step #> (fn ((c, _), _, _) => dest_Call c)

fun call_tac get_func_corrects =
  let fun focused_tac ctxt prems =
    case map_filter (try (HTIU.dest_Trueprop #> dest_Call_IMP_big_step_state)) prems of
      [] => (@{log Logger.TRACE} ctxt (fn _ => Pretty.block [
          Pretty.str "Could not find Call big step in premises ",
          HTIU.pretty_prems ctxt prems
        ] |> Pretty.string_of);
        K no_tac)
    | Calls =>
      let
        fun tac _ (SOME func_corrects) = eresolve_tac ctxt @{thms tCall_E}
              THEN' dresolve_tac ctxt func_corrects
              THEN' SUTIT.update_state_call_tac [] ctxt
          | tac called_term NONE = (@{log Logger.WARN} ctxt (fn _ => Pretty.block [
                Pretty.str "Could not find correctness theorem for ",
                Syntax.pretty_term ctxt called_term
              ] |> Pretty.string_of);
              K no_tac)
      in
        Seq.of_list Calls
        |> Seq.map (fn (c, _) => get_func_corrects ctxt c |> tac c)
        |> Seq.M.flat2
      end
  in TU.FOCUS_PARAMS_CTXT' (TU.SUBGOAL_STRIPPED (fst o snd) o focused_tac) end

fun run_single_tac get_func_corrects = HTITB.run_single_tac
  assign_tac if_tac [call_tac get_func_corrects]

fun run_tac get_func_corrects = HTITB.run_tac
  seq_tac assign_tac if_tac [call_tac get_func_corrects]

fun start_run_tac get_IMP_def get_func_corrects ctxt =
  start_tac get_IMP_def ctxt
  THEN' run_tac get_func_corrects ctxt

val finish_non_tailcall_tac = HTITB.finish_non_induction_tac

fun tailcall_tac ctxt = eresolve_tac ctxt @{thms tTail_E}

fun get_IMP_keys ctxt = dest_Const #> fst
  #> Compile_Nat.get_compiled_const (Context.Proof ctxt)
  #> #arg_regs
  #> map HTIU.mk_register

val rewrite_insert_current_keys_eq_tac = HTITB.rewrite_insert_current_keys_eq_tac' get_IMP_keys

fun finish_tailcall_tac get_HOL_eqs ctxt = tailcall_tac ctxt
  THEN' HTITB.finish_induction_tac get_HOL_eqs get_IMP_keys ctxt

fun finish_tac get_HOL_eqs ctxt =
  SOLVED' (finish_tailcall_tac get_HOL_eqs ctxt)
  ORELSE' finish_non_tailcall_tac get_HOL_eqs ctxt

fun start_run_finish_tac get_IMP_def get_func_corrects get_HOL_eqs ctxt =
  start_run_tac get_IMP_def get_func_corrects ctxt
  THEN_ALL_NEW finish_tac get_HOL_eqs ctxt

end
