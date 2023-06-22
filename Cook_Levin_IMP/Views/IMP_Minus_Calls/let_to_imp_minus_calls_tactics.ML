(*  Title:  Views/IMP_Minus/let_to_imp_minus_calls_tactics.ML
    Author: Kevin Kappelmann

Tactics to run IMP Minus with Calls programs, track their states changes, and prove their
correspondence with HOL-let programs.
*)
signature LET_TO_IMP_MINUS_CALLS_TACTICS =
sig

val if_split_tac : Proof.context -> int ->tactic
val Seq_assoc_right_tac: Proof.context -> int -> tactic

val start_tac: thm -> Proof.context -> int -> tactic

val seq_tac: Proof.context -> int -> tactic

val assign_tac: Proof.context -> int -> tactic

val call_tac: thm -> thm -> Proof.context -> int -> tactic

val if_tac: Proof.context -> int -> tactic

val step_update_state_tac: (thm * thm) list -> Proof.context -> int -> tactic

val run_tac: thm -> (thm * thm) list -> Proof.context -> int ->
  tactic

val finish_state_tac: thm -> thm -> Proof.context -> int -> tactic
val finish_tac: thm -> Proof.context -> int -> tactic

val run_finish_tac: (int -> tactic) -> thm -> thm -> thm ->
  (thm * thm) list -> Proof.context -> int -> tactic
val run_finish_tac': thm -> thm -> thm -> (thm * thm) list ->
  Proof.context -> int -> tactic

end

structure Let_To_IMP_Minus_Calls_Tactics : LET_TO_IMP_MINUS_CALLS_TACTICS =
struct

structure U = View_Util
structure SCL = State_Cook_Levin_IMP_Minus_Calls

fun if_split_tac ctxt =
  split_tac ctxt @{thms if_split}
  THEN_ALL_NEW
    (resolve_tac ctxt @{thms conjI}
    THEN_ALL_NEW resolve_tac ctxt @{thms impI})

fun Seq_assoc_right_tac ctxt =
  safe_full_simp_tac (View_Util.set_simps ctxt @{thms Seq'_assoc[symmetric]})

fun start_tac IMP_program_def ctxt =
  U.subst_first_asm_tac ctxt IMP_program_def
  THEN' Seq_assoc_right_tac ctxt
  THEN' SCL.init_state_eq_tac ctxt

fun seq_tac ctxt = eresolve_tac ctxt @{thms Seq'_tE}

fun assign_tac ctxt = dresolve_tac ctxt @{thms Assign'D}
  THEN' eresolve_tac ctxt @{thms conjE}
  THEN' SCL.update_state_assign_tac ctxt

fun call_tac correctness_thm state_def ctxt =
  let
    val simps = @{thms append_Nil com_add_prefix_empty_eq}
    val correctness_thm = correctness_thm
      |> Drule.infer_instantiate' ctxt (map SOME [@{cterm "[] :: vname"}, @{cterm "[] :: vname"}])
      |> Drule.infer_instantiate ctxt [(("vars", 0), @{cterm "{} :: AExp.vname set"})]
      |> Simplifier.full_simplify (ctxt addsimps simps)
  in
    eresolve_tac ctxt @{thms Call'_tE}
    THEN' eresolve_tac ctxt [correctness_thm]
    (*update state*)
    THEN' SCL.update_state_call_tac state_def ctxt
  end

fun if_tac ctxt =
  eresolve_tac ctxt @{thms If'_tE}
  THEN_ALL_NEW
    (SCL.rewrite_all_state_app_tac' U.subst_first_asm_tac ctxt
    THEN' Seq_assoc_right_tac ctxt)

fun step_update_state_tac correctness_thm_state_def_pairs ctxt =
  View_Util.TRY' (seq_tac ctxt)
  THEN' FIRST' (assign_tac ctxt :: if_tac ctxt ::
    map (fn p => uncurry call_tac p ctxt)
      correctness_thm_state_def_pairs)

fun run_tac IMP_program_def correctness_thm_state_def_pairs ctxt =
  start_tac IMP_program_def ctxt
  THEN' REPEAT_ALL_NEW (step_update_state_tac correctness_thm_state_def_pairs ctxt)

fun finish_tac HOL_program_def ctxt =
  let val finish_goal_tac = clarify_tac ctxt
    THEN' asm_full_simp_tac ctxt
  in
    SCL.rewrite_all_state_app_tac' U.subst_first_tac ctxt
    THEN' SCL.remove_state_eq_tac ctxt
    THEN' U.TRY' (U.subst_first_tac ctxt HOL_program_def)
    THEN' U.TRY' (REPEAT_ALL_NEW (U.subst_first_tac ctxt @{thm Let_def} ORELSE' if_split_tac ctxt))
    THEN_ALL_NEW finish_goal_tac
  end

fun finish_state_tac HOL_program_def state_def ctxt =
  Simplifier.safe_simp_tac (U.set_simps ctxt [state_def])
  THEN' finish_tac HOL_program_def ctxt

fun run_finish_tac before_finish_tac HOL_program_def state_def IMP_program_def
  correctness_thm_state_def_pairs ctxt =
  run_tac IMP_program_def correctness_thm_state_def_pairs ctxt
  THEN_ALL_NEW
    (before_finish_tac
    THEN_ALL_NEW finish_state_tac HOL_program_def state_def ctxt)

val run_finish_tac' = run_finish_tac (K all_tac)

end
