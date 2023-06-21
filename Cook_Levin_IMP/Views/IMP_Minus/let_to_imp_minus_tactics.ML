(*  Title:  Views/IMP_Minus/let_to_imp_minus_tactics.ML
    Author: Kevin Kappelmann

Tactics to run IMP Minus programs, track their states changes, and prove their
correspondence with HOL-let programs.
*)
signature LET_TO_IMP_MINUS_TACTICS =
sig

val if_split_tac : Proof.context -> int ->tactic
val Seq_assoc_right_tac: Proof.context -> int -> tactic

val IMP_Minus_start_tac: thm -> thm -> cterm -> cterm -> Proof.context -> int -> tactic

val IMP_Minus_seq_tac: Proof.context -> int -> tactic

val IMP_Minus_assign_tac: Proof.context -> int -> tactic

val IMP_Minus_invoke_subprogram_tac: thm -> thm -> cterm -> Proof.context -> int -> tactic

val IMP_Minus_if_tac: Proof.context -> int -> tactic

val IMP_Minus_step_update_view_tac: (thm * thm) list -> cterm -> Proof.context -> int -> tactic

val IMP_Minus_run_tac: thm -> thm -> (thm * thm) list -> cterm -> cterm -> Proof.context -> int ->
  tactic

val IMP_Minus_finish_state_tac: thm -> Proof.context -> int -> tactic
val IMP_Minus_finish_tac: Proof.context -> int -> tactic

val IMP_Minus_run_finish_tac: (int -> tactic) -> thm -> thm -> thm ->
  (thm * thm) list -> cterm -> cterm -> Proof.context -> int -> tactic
val IMP_Minus_run_finish_tac': thm -> thm -> thm -> (thm * thm) list ->
  cterm -> cterm -> Proof.context -> int -> tactic

end

structure Let_To_IMP_Minus_Tactics : LET_TO_IMP_MINUS_TACTICS =
struct

structure U = View_Util
structure VCL = View_Cook_Levin_IMP_Minus

fun if_split_tac ctxt =
  split_tac ctxt @{thms if_split}
  THEN_ALL_NEW
    (resolve_tac ctxt @{thms conjI}
    THEN_ALL_NEW resolve_tac ctxt @{thms impI})

fun Seq_assoc_right_tac ctxt =
  safe_full_simp_tac (View_Util.set_simps ctxt @{thms Seq_assoc[symmetric]})

fun IMP_Minus_start_tac HOL_program_def IMP_Minus_program_def cvars cprefix ctxt =
  let val cvars_prefixed = \<^instantiate>\<open>cprefix and cvars in cterm\<open>add_prefix cprefix ` cvars\<close>\<close>
  in
    U.subst_first_tac ctxt HOL_program_def
    THEN' U.subst_first_asm_tac ctxt IMP_Minus_program_def
    THEN' safe_full_simp_tac (View_Util.set_simps ctxt @{thms prefix_simps})
    THEN' Seq_assoc_right_tac ctxt
    THEN' VCL.init_view_eq_tac cvars_prefixed ctxt
  end

fun IMP_Minus_seq_tac ctxt = eresolve_tac ctxt @{thms Seq_tE}

fun IMP_Minus_assign_tac ctxt = dresolve_tac ctxt @{thms AssignD}
  THEN' eresolve_tac ctxt @{thms conjE}
  THEN' VCL.update_view_assign_tac ctxt

fun IMP_Minus_invoke_subprogram_tac correctness_thm state_def_thm cvars ctxt =
  let val correctness_thm =
    Drule.infer_instantiate ctxt [(("vars", 0), cvars)] correctness_thm
    |> Local_Defs.unfold ctxt @{thms atomize_ball}
  in
    eresolve_tac ctxt [correctness_thm]
    THEN' Subgoal.SUBPROOF (#context #> auto_tac) ctxt
    (*rewrite state definition and state retrievals in new premises*)
    THEN' U.subst_first_asm_tac ctxt state_def_thm
    THEN' VCL.rewrite_all_state_app_tac' U.subst_first_asm_tac ctxt
    (*update view*)
    THEN' VCL.update_view_invoke_subprogram_tac state_def_thm ctxt
  end

fun IMP_Minus_if_tac ctxt =
  eresolve_tac ctxt @{thms If_tE}
  THEN_ALL_NEW
    (VCL.rewrite_all_state_app_tac' U.subst_first_asm_tac ctxt
    THEN' Seq_assoc_right_tac ctxt)

fun IMP_Minus_step_update_view_tac correctness_thm_state_def_thm_pairs cvars ctxt =
  View_Util.TRY' (IMP_Minus_seq_tac ctxt)
  THEN' FIRST' (IMP_Minus_assign_tac ctxt :: IMP_Minus_if_tac ctxt ::
    map (fn p => uncurry IMP_Minus_invoke_subprogram_tac p cvars ctxt)
      correctness_thm_state_def_thm_pairs)

fun IMP_Minus_run_tac HOL_program_def IMP_loop_body_def correctness_thm_state_def_thm_pairs
  cvars cprefix ctxt =
  IMP_Minus_start_tac HOL_program_def IMP_loop_body_def cvars cprefix ctxt
  THEN' REPEAT_ALL_NEW (IMP_Minus_step_update_view_tac correctness_thm_state_def_thm_pairs cvars ctxt)

fun IMP_Minus_finish_tac ctxt =
  U.TRY' (REPEAT_ALL_NEW (U.subst_first_tac ctxt @{thm Let_def} ORELSE' if_split_tac ctxt))
  THEN_ALL_NEW
    (VCL.rewrite_all_state_app_tac' U.subst_first_tac ctxt
    THEN' VCL.remove_view_eq_tac ctxt
    THEN' asm_full_simp_tac ctxt)

fun IMP_Minus_finish_state_tac state_def_thm ctxt =
  REPEAT_ALL_NEW (U.subst_first_tac ctxt state_def_thm)
  THEN' (IMP_Minus_finish_tac ctxt)

fun IMP_Minus_run_finish_tac before_finish_tac HOL_program_def IMP_loop_body_def state_def_thm
  correctness_thm_state_def_thm_pairs cvars cprefix ctxt =
  IMP_Minus_run_tac HOL_program_def IMP_loop_body_def correctness_thm_state_def_thm_pairs cvars cprefix ctxt
  THEN_ALL_NEW
    (before_finish_tac
    THEN_ALL_NEW IMP_Minus_finish_state_tac state_def_thm ctxt)

val IMP_Minus_run_finish_tac' = IMP_Minus_run_finish_tac (K all_tac)

end
