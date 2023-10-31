(*  Title:  Views/IMP_Tailcalls/hol_to_imp_tailcalls_tactics.ML
    Author: Kevin Kappelmann

Tactics to run IMP-Tailcall programs, track their states changes, and prove their
correspondence with HOL programs.
*)
signature HOL_TO_IMP_TAILCALLS_TACTICS =
sig

val if_split_tac : Proof.context -> int ->tactic
val Seq_assoc_right_tac: Proof.context -> int -> tactic

val start_tac : thm -> Proof.context -> int -> tactic

val seq_tac : Proof.context -> int -> tactic

val assign_tac : Proof.context -> int -> tactic

val call_tac : thm -> Proof.context -> int -> tactic

val if_tac : Proof.context -> int -> tactic

val step_update_state_tac : thm list -> Proof.context -> int -> tactic

val run_tac : thm -> thm list -> Proof.context -> int -> tactic

val tailcall_tac : Proof.context -> int -> tactic

val finish_non_tailcall_tac : thm list -> Proof.context -> int -> tactic
val finish_tailcall_tac : thm list -> Proof.context -> int -> tactic
val finish_tac : thm list -> Proof.context -> int -> tactic

val run_finish_tac : thm list -> thm -> thm list -> Proof.context -> int -> tactic

end

structure HOL_To_IMP_Tailcalls_Tactics =
(*: HOL_TO_IMP_TAILCALLS_TACTICS =*)
struct

structure VU = View_Util
structure GU = General_Util
structure TU = Tactic_Util
structure SIT = State_IMP_Tailcalls

fun if_split_tac ctxt =
  split_tac ctxt @{thms if_split}
  THEN_ALL_NEW
    (resolve_tac ctxt @{thms conjI}
    THEN_ALL_NEW resolve_tac ctxt @{thms impI})

fun Seq_assoc_right_tac ctxt =
  safe_full_simp_tac (VU.set_simps ctxt @{thms tbig_step_t_tSeq_assoc})

(*TODO: move somewhere else*)
val arg2_of_4_conv = Conv.fun_conv o Conv.fun_conv o Conv.arg_conv

fun tbig_step_t_program_conv IMP_program_def ct =  if SIT.is_IMP_big_step_state (Thm.term_of ct)
  then arg2_of_4_conv (Conv.arg1_conv (Conv.rewr_conv IMP_program_def)) ct
  else Conv.no_conv ct
  
fun tbig_step_t_program_prem_conv IMP_program_def i =
  Conversion_Util.repeat_forall_conv (fn _ => fn _ =>
    Conversion_Util.move_prem_to_front_conv i
    then_conv Conv.prems_conv 1 (HOLogic.Trueprop_conv (tbig_step_t_program_conv IMP_program_def))
  )

fun rewrite_IMP_program_def_tac IMP_program_def = 
  let fun tac ctxt prems = case GU.find_first_index SIT.is_IMP_big_step_state_prop prems of
    SOME (i, _) => CONVERSION (tbig_step_t_program_prem_conv IMP_program_def (i + 1) ctxt)
   | NONE => (writeln "Could not find IMP big step premise"; K no_tac)
  in TU.FOCUS_PARAMS_CTXT' (TU.SUBGOAL_STRIPPED (fst o snd) o tac) end
  
fun start_tac IMP_program_def ctxt =
  rewrite_IMP_program_def_tac IMP_program_def ctxt
  (*TODO: assoc to the right just in case?*)
  (*THEN' Seq_assoc_right_tac ctxt*)
  THEN' SIT.init_state_eq_tac ctxt

fun seq_tac ctxt = eresolve_tac ctxt @{thms tSeq_tE}

fun assign_tac ctxt = dresolve_tac ctxt @{thms tAssignD}
  THEN' eresolve_tac ctxt @{thms conjE}
  THEN' SIT.update_state_assign_tac ctxt
                                            
fun call_tac correctness_thm ctxt = eresolve_tac ctxt @{thms tCall_tE}
  THEN' dresolve_tac ctxt [correctness_thm]
  (*update state*)
  THEN' SIT.update_state_call_tac ctxt

fun if_tac ctxt = eresolve_tac ctxt @{thms tIf_tE'}
  THEN_ALL_NEW (SIT.rewrite_all_state_app_tac' (fn ctxt => VU.subst_first_asm_tac ctxt o single) ctxt)

fun step_update_state_tac correctness_thm_state_def_pairs ctxt = TU.TRY' (seq_tac ctxt)
  THEN' FIRST' (assign_tac ctxt :: if_tac ctxt ::
    map (fn thm => call_tac thm ctxt) correctness_thm_state_def_pairs)

fun run_tac IMP_program_def correctness_thm_state_def_pairs ctxt =
  start_tac IMP_program_def ctxt
  THEN' REPEAT_ALL_NEW (step_update_state_tac correctness_thm_state_def_pairs ctxt)

fun simp_HOL_def_tac ctxt = asm_full_simp_tac (ctxt addsimps @{thms Let_def})

fun finish_non_tailcall_tac HOL_program_eqs ctxt =
  (SIT.rewrite_all_state_app_tac' (fn ctxt => VU.subst_first_tac ctxt o single) ctxt
  THEN' SIT.remove_state_eq_tac ctxt
  THEN' VU.subst_first_tac ctxt HOL_program_eqs
  THEN_ALL_NEW simp_HOL_def_tac ctxt)
  |> SOLVED'

(* tailcalls *)

fun tailcall_tac ctxt = eresolve_tac ctxt @{thms tTail_tE}

(*monadic code utils*)
structure SS = State_Seq
structure SSS = State_Stack_Seq
infix 1 SS_THEN
val op SS_THEN = op State_Seq_THEN
structure Seq_Monad = Monad(Seq_Monad_Base)

(*TODO: move somewhere else*)
fun mk_state_retrieval state key = state $ key
val mk_register = HOLogic.mk_string
fun mk_state_register_retrieval state = mk_state_retrieval state o mk_register

fun state_register_eq_thmsq state_eq_thm (state_SIMPS_TO_thm, state_SIMPS_TO_term) ctxt
  finish_eq_tac register term =
  let
    val goal = mk_state_register_retrieval state_SIMPS_TO_term register
      |> pair term
      |> HOLogic.mk_eq
      |> HOLogic.mk_Trueprop
      |> Thm.cterm_of ctxt
    val rewrite_eq_tac =
      SIT.rewrite_all_state_app_tac (VU.subst_first_tac ctxt o single) ctxt state_eq_thm state_SIMPS_TO_thm
      THEN' finish_eq_tac
  in (rewrite_eq_tac |> SOLVED' |> TU.apply_tac |> TU.HEADGOAL) goal end

fun rewrite_insert_current_registers_eq_tac register_terms =
  let
    fun register_eq_focused_tac SIMPS_TO_res {prems=[state_eq_thm], context=ctxt,...} =
      let
        val state_register_eq_thmsq =
          state_register_eq_thmsq state_eq_thm (apsnd Thm.term_of SIMPS_TO_res) ctxt
        fun rewrite_insert_tac eq_thm = VU.subst_first_tac ctxt [eq_thm]
          THEN' Tactic_Util.insert_tac [eq_thm] ctxt
        fun rewrite_insert_state_register_eq_tac prems =
          let val simp_tac = asm_full_simp_tac (ctxt addsimps prems)
          in 
            uncurry (state_register_eq_thmsq simp_tac)
            #> Seq.map rewrite_insert_tac
            #> Seq_Monad.flat2
          end
        fun focus_rewrite prems = map (rewrite_insert_state_register_eq_tac prems) register_terms
          |> EVERY'
      in TU.FOCUS_PREMS' (focus_rewrite o #prems) ctxt end
    val current_value_tac =
      SIT.interp_state_lhs_state_eq_SIMPS_TO_thm_result_state_seq
      SS_THEN SS.lift_state_single (fn SIMPS_TO_res =>
        fn ((state_eq_prem_index, _), ctxt) =>
        TU.focus_prems_tac [state_eq_prem_index + 1] (register_eq_focused_tac SIMPS_TO_res) ctxt)
      |> SS.eval
      #> Seq_Monad.flat2
  in TU.CSUBGOAL_STRIPPED (fst o snd) o (current_value_tac oo SSS.SRS.init) end

val rewrite_insert_current_registers_eq_tac' =
  let fun focused_tac ctxt concl = 
    let
      val (hol_term, args) = VU.dest_Trueprop concl |> VU.dest_eq |> snd |> strip_comb
      val registers = dest_Const hol_term |> fst
        |> Compile_Nat.get_compiled_const (Context.Proof ctxt)
        |> #arg_regs
    in rewrite_insert_current_registers_eq_tac (registers ~~ args) ctxt end
  in TU.FOCUS_PARAMS_CTXT' (TU.SUBGOAL_STRIPPED (snd o snd) o focused_tac) end

fun finish_tailcall_tac HOL_program_eqs ctxt =
  let val finish_goal_tac = Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN ctxt []
  in
    (tailcall_tac ctxt
    THEN' VU.subst_first_tac ctxt HOL_program_eqs
    THEN' TU.TRY' (simp_HOL_def_tac ctxt)
    THEN' rewrite_insert_current_registers_eq_tac' ctxt
    THEN_ALL_NEW finish_goal_tac)
    |> SOLVED'
  end

fun finish_tac HOL_program_eqs ctxt = finish_tailcall_tac HOL_program_eqs ctxt
  ORELSE' finish_non_tailcall_tac HOL_program_eqs ctxt

fun run_finish_tac HOL_program_eqs IMP_program_def
  correctness_thm_state_def_pairs ctxt =
  run_tac IMP_program_def correctness_thm_state_def_pairs ctxt
  THEN_ALL_NEW finish_tac HOL_program_eqs ctxt

end
