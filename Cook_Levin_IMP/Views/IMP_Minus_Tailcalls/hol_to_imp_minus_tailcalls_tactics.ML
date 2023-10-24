(*  Title:  Views/IMP_Minus/hol_to_imp_minus_tailcalls_tactics.ML
    Author: Kevin Kappelmann

Tactics to run IMP Minus with Calls programs, track their states changes, and prove their
correspondence with HOL-let programs.
*)
signature HOL_TO_IMP_MINUS_TAILCALLS_TACTICS =
sig

val if_split_tac : Proof.context -> int ->tactic
val Seq_assoc_right_tac: Proof.context -> int -> tactic

val start_tac: thm -> Proof.context -> int -> tactic

val seq_tac: Proof.context -> int -> tactic

val assign_tac: Proof.context -> int -> tactic

val call_tac: thm -> Proof.context -> int -> tactic

val if_tac: Proof.context -> int -> tactic

val step_update_state_tac: thm list -> Proof.context -> int -> tactic

val run_tac: thm -> thm list -> Proof.context -> int ->
  tactic

val finish_tac: thm -> Proof.context -> int -> tactic

val run_finish_tac: (int -> tactic) -> thm -> thm -> thm list -> Proof.context -> int -> tactic
val run_finish_tac': thm -> thm -> thm list -> Proof.context -> int -> tactic

end

structure HOL_To_IMP_Minus_Tailcalls_Tactics : HOL_TO_IMP_MINUS_TAILCALLS_TACTICS =
struct

structure U = View_Util
structure SCL = State_Cook_Levin_IMP_Minus_Tailcalls

fun if_split_tac ctxt =
  split_tac ctxt @{thms if_split}
  THEN_ALL_NEW
    (resolve_tac ctxt @{thms conjI}
    THEN_ALL_NEW resolve_tac ctxt @{thms impI})

fun Seq_assoc_right_tac ctxt =
  safe_full_simp_tac (View_Util.set_simps ctxt @{thms tbig_step_t_tSeq_assoc})

(*TODO: move somewhere else*)
fun repeat_forall_conv cv =
  let fun conv fs ctxt =
    Conv.forall_conv (fn (f, ctxt) => conv (f :: fs) ctxt) ctxt
    else_conv (cv fs ctxt)
  in conv [] end

val arg2_of_4_conv = Conv.fun_conv o Conv.fun_conv o Conv.arg_conv

fun tbig_step_t_conv IMP_program_def ct = case Thm.term_of ct of
    \<^Const>\<open>tbig_step_t for _ \<^Const>\<open>Pair _ _ for _ _\<close> _ _\<close> =>
      arg2_of_4_conv (Conv.arg1_conv (Conv.rewr_conv IMP_program_def)) ct
  | _ => Conv.no_conv ct
fun tbig_step_t_prem_conv IMP_program_def i =
  repeat_forall_conv (Conv.prems_conv i (HOLogic.Trueprop_conv (tbig_step_t_conv IMP_program_def)) |> K |> K)

val is_IMP_big_step_state_prop =
  View_Util.try_bool (\<^Const_fn>\<open>tbig_step_t for _ _ _ _ => true\<close> o View_Util.dest_Trueprop)
  
fun rewrite_IMP_program_def_tac IMP_program_def = 
  let fun tac ctxt prems = case View_Util.find_first_index is_IMP_big_step_state_prop prems of
    SOME (i, _) => CONVERSION (tbig_step_t_prem_conv IMP_program_def (i + 1) ctxt)
   | NONE => (writeln "Could not find IMP big step premise"; K no_tac)
  in U.FOCUS_PARAMS_CTXT' (U.SUBGOAL_PREMS_CONCL fst o tac) end
  
fun start_tac IMP_program_def ctxt =
  rewrite_IMP_program_def_tac IMP_program_def ctxt
  (*TODO: assoc to the right just in case?*)
  (*THEN' Seq_assoc_right_tac ctxt*)
  THEN' SCL.init_state_eq_tac ctxt

fun seq_tac ctxt = eresolve_tac ctxt @{thms tSeq_tE}

fun assign_tac ctxt = dresolve_tac ctxt @{thms tAssignD}
  THEN' eresolve_tac ctxt @{thms conjE}
  THEN' SCL.update_state_assign_tac ctxt

fun call_tac correctness_thm ctxt =
  let
    (*TODO: remove unnecessary code*)
    (*val simps =  []*)
      (* @{thms append_Nil com_add_prefix_empty_eq} *)
    val correctness_thm = correctness_thm
      (*|> Drule.infer_instantiate' ctxt (map SOME [@{cterm "[] :: vname"}, @{cterm "[] :: vname"}])*)
      (*|> Drule.infer_instantiate ctxt [(("vars", 0), @{cterm "{} :: AExp.vname set"})]*)
      (*|> Simplifier.full_simplify (ctxt addsimps simps)*)
  in                      
    eresolve_tac ctxt @{thms tCall_tE}
    THEN' dresolve_tac ctxt [correctness_thm]
    (*update state*)
    THEN' SCL.update_state_call_tac ctxt
  end

fun if_tac ctxt =
  eresolve_tac ctxt @{thms tIf_tE}
  THEN_ALL_NEW
    (SCL.rewrite_all_state_app_tac' U.subst_first_asm_tac ctxt)

fun step_update_state_tac correctness_thm_state_def_pairs ctxt =
  View_Util.TRY' (seq_tac ctxt)
  THEN' FIRST' (assign_tac ctxt :: if_tac ctxt ::
    map (fn thm => call_tac thm ctxt) correctness_thm_state_def_pairs)

fun run_tac IMP_program_def correctness_thm_state_def_pairs ctxt =
  start_tac IMP_program_def ctxt
  THEN' REPEAT_ALL_NEW (step_update_state_tac correctness_thm_state_def_pairs ctxt)

fun finish_tac HOL_program_def ctxt =
  let val finish_goal_tac = 
    (*U.TRY' (clarify_tac ctxt)*)
    (*THEN' U.TRY'*)
    (*TODO: clarify needed?*)
      asm_full_simp_tac ctxt
  in
    SCL.rewrite_all_state_app_tac' U.subst_first_tac ctxt
    THEN' SCL.remove_state_eq_tac ctxt
    THEN' U.TRY' (U.subst_first_tac ctxt HOL_program_def)
    THEN' U.TRY' (REPEAT_ALL_NEW (U.subst_first_tac ctxt @{thm Let_def} ORELSE' if_split_tac ctxt))
    THEN_ALL_NEW finish_goal_tac
  end

fun run_finish_tac before_finish_tac HOL_program_def IMP_program_def
  correctness_thm_state_def_pairs ctxt =
  run_tac IMP_program_def correctness_thm_state_def_pairs ctxt
  THEN_ALL_NEW
    (before_finish_tac
    THEN_ALL_NEW finish_tac HOL_program_def ctxt)

val run_finish_tac' = run_finish_tac (K all_tac)

end
