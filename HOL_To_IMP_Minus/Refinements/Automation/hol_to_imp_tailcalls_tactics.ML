(*  Title:  Views/IMP_Tailcalls/hol_to_imp_tailcalls_tactics.ML
    Author: Kevin Kappelmann

Tactics to run IMP-Tailcall programs, track their states changes, and prove their
correspondence with HOL programs.
*)
signature HOL_TO_IMP_TAILCALLS_TACTICS =
sig
include HAS_LOGGER

val if_split_tac : Proof.context -> int ->tactic

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

val step_update_state_tac : func_corrects_retrieval -> Proof.context -> int -> tactic

val run_tac : func_corrects_retrieval -> Proof.context -> int -> tactic

val start_run_tac : IMP_def_retrieval -> func_corrects_retrieval -> Proof.context -> int -> tactic

val tailcall_tac : Proof.context -> int -> tactic

val rewrite_insert_current_registers_eq_tac' : Proof.context -> int -> tactic

(*retrieve HOL equalities from HOL term (including possible arguments)*)
type HOL_eqs_retrieval = Proof.context -> term -> thm list option
val get_HOL_eqs : func_corrects_retrieval

val finish_non_tailcall_tac : HOL_eqs_retrieval -> Proof.context -> int -> tactic
val finish_tailcall_tac : HOL_eqs_retrieval -> Proof.context -> int -> tactic
val finish_tac : HOL_eqs_retrieval -> Proof.context -> int -> tactic

val start_run_finish_tac : IMP_def_retrieval  -> func_corrects_retrieval ->
  HOL_eqs_retrieval -> Proof.context -> int -> tactic

end

structure HOL_To_IMP_Tailcalls_Tactics : HOL_TO_IMP_TAILCALLS_TACTICS =
struct

val logger = Logger.setup_new_logger HOL_to_IMP_base_logger "HOL_To_IMP_Tailcalls_Tactics"

structure VU = View_Util
structure GU = General_Util
structure TU = Tactic_Util
structure HTIU = HOL_To_IMP_Util
structure SIT = State_IMP_Tailcalls

fun if_split_tac ctxt =
  split_tac ctxt @{thms if_split}
  THEN_ALL_NEW
    (resolve_tac ctxt @{thms conjI}
    THEN_ALL_NEW resolve_tac ctxt @{thms impI})

type IMP_def_retrieval = Proof.context -> term -> thm option
val get_IMP_def = Compile_Nat.get_compiled_const_def

val arg2_of_4_conv = Conv.fun_conv o Conv.fun_conv o Conv.arg_conv

fun tbig_step_t_program_conv get_IMP_def ctxt ct =
  let val get_def = Thm.term_of #> SIT.dest_IMP_big_step_state
    #> (fn ((c, _), _, _) => get_IMP_def ctxt c)
  in (case try get_def ct of
      SOME (SOME thm) => Conv.rewr_conv thm |> Conv.arg1_conv |> arg2_of_4_conv
    | SOME NONE => (@{log Logger.WARN} ctxt (K "Could not retrieve IMP definition equality theorem");
        Conv.no_conv)
    | NONE => (@{log Logger.WARN} ctxt (K "Could not destruct IMP big step state to retrieve theorem");
        Conv.no_conv)) ct
  end

fun tbig_step_t_program_prem_conv get_IMP_def i =
  Conversion_Util.repeat_forall_conv (fn _ => fn ctxt =>
    Conversion_Util.move_prem_to_front_conv i
    then_conv Conv.prems_conv 1
      (tbig_step_t_program_conv get_IMP_def ctxt |> HOLogic.Trueprop_conv))

fun rewrite_get_IMP_def_tac get_IMP_def =
  let fun tac ctxt prems = case GU.find_first_index SIT.is_IMP_big_step_state_prop prems of
      SOME (i, _) => CONVERSION (tbig_step_t_program_prem_conv get_IMP_def (i + 1) ctxt)
    | NONE => (@{log Logger.WARN} ctxt (fn _ => Pretty.block [
          Pretty.str "Could not find IMP big step premise in premises ",
          SpecCheck_Show.list (Syntax.pretty_term ctxt) prems
        ] |> Pretty.string_of);
        K no_tac)
  in TU.FOCUS_PARAMS_CTXT' (TU.SUBGOAL_STRIPPED (fst o snd) o tac) end

fun start_tac get_IMP_def ctxt =
  rewrite_get_IMP_def_tac get_IMP_def ctxt
  THEN' SIT.init_state_eq_tac ctxt

fun seq_tac ctxt = eresolve_tac ctxt @{thms tSeq_E}

fun assign_tac ctxt = dresolve_tac ctxt @{thms tAssignD}
  THEN' SIT.update_state_assign_tac ctxt

type func_corrects_retrieval = Proof.context -> term -> thm list option
val get_func_corrects = Option.map single oo HOL_To_IMP_Minus_Func_Correct_Thms.get_theorem

fun call_tac get_func_corrects =
  let fun focused_tac ctxt prems = (case get_first (try SIT.dest_IMP_big_step_state_prop) prems of
    SOME ((\<^Const>\<open>tCall for c _\<close>, _), _, _) =>
      case get_func_corrects ctxt c of
        SOME thms =>
          eresolve_tac ctxt @{thms tCall_E}
          THEN' dresolve_tac ctxt thms
          (*update state*)
          THEN' SIT.update_state_call_tac ctxt)
    handle Match => K no_tac
  in TU.FOCUS_PARAMS_CTXT' (TU.SUBGOAL_STRIPPED (snd #> fst) o focused_tac) end

fun if_tac ctxt = eresolve_tac ctxt @{thms tIf_E}
  THEN_ALL_NEW (SIT.rewrite_all_state_retrieval_tac' (fn ctxt => VU.subst_first_asm_tac ctxt o single) ctxt)

fun step_update_state_tac get_func_corrects ctxt = TU.TRY' (seq_tac ctxt)
  THEN' FIRST' [call_tac get_func_corrects ctxt, assign_tac ctxt, if_tac ctxt]

val run_tac = REPEAT_ALL_NEW oo step_update_state_tac

fun start_run_tac get_IMP_def get_func_corrects ctxt =
  start_tac get_IMP_def ctxt
  THEN' run_tac get_func_corrects ctxt

fun simp_HOL_def_tac ctxt = asm_full_simp_tac (ctxt addsimps @{thms Let_def})

type HOL_eqs_retrieval = Proof.context -> term -> thm list option
(*FIXME: create a more robust filter*)
fun get_HOL_eqs ctxt t =
  let val thms = Find_Theorems.find_theorems ctxt NONE NONE true [
      (*search for the head constant*)
      (true, Find_Theorems.Pattern (head_of t)),
      (*ignore conditional rules*)
      (false, Find_Theorems.Pattern @{term "(\<Longrightarrow>)"})
    ] |> snd |> map snd
  in if null thms then NONE else SOME thms end

val dest_eq_HOL_term = VU.dest_eq #> snd
val dest_eq_HOL_term_prop = VU.dest_Trueprop #> dest_eq_HOL_term

fun rewrite_HOL_eq_tac get_HOL_eqs =
  let fun tac ctxt concl = case try (dest_eq_HOL_term_prop #> get_HOL_eqs ctxt) concl of
      SOME (SOME thms) => VU.subst_first_tac ctxt thms
    | SOME NONE => (@{log Logger.WARN} ctxt (fn _ => Pretty.block [
        Pretty.str "Could not find HOL equality for HOL term in conclusion ",
        Syntax.pretty_term ctxt concl
      ] |> Pretty.string_of);
      K no_tac)
    | NONE => (@{log Logger.WARN} ctxt (fn _ => Pretty.block [
        Pretty.str "Could not destruct conclusion to find HOL equality ",
        Syntax.pretty_term ctxt concl
      ] |> Pretty.string_of);
      K no_tac)
  in TU.SUBGOAL_STRIPPED (snd o snd) o tac end

fun finish_non_tailcall_tac get_HOL_eqs ctxt =
  SIT.rewrite_all_state_retrieval_tac' (fn ctxt => VU.subst_first_tac ctxt o single) ctxt
  THEN' SIT.remove_state_eq_tac ctxt
  THEN' rewrite_HOL_eq_tac get_HOL_eqs ctxt
  THEN_ALL_NEW simp_HOL_def_tac ctxt

(* tailcalls *)

fun tailcall_tac ctxt = eresolve_tac ctxt @{thms tTail_E}

fun state_register_eq_thmsq state_eq_thm (state_SIMPS_TO_thm, state_SIMPS_TO_term) ctxt
  finish_eq_tac register term =
  let
    val goal = HTIU.mk_state_register_retrieval state_SIMPS_TO_term register
      |> pair term
      |> HOLogic.mk_eq
      |> HOLogic.mk_Trueprop
      |> Thm.cterm_of ctxt
    val rewrite_eq_tac =
      SIT.rewrite_all_state_retrieval_tac (VU.subst_first_tac ctxt o single) ctxt state_eq_thm state_SIMPS_TO_thm
      THEN' finish_eq_tac
  in (rewrite_eq_tac |> SOLVED' |> TU.apply_tac |> TU.HEADGOAL) goal end

open State_Seq_Abbrevs

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
      val (hol_term, args) = VU.dest_Trueprop concl |> dest_eq_HOL_term |> strip_comb
      val registers = dest_Const hol_term |> fst
        |> Compile_Nat.get_compiled_const (Context.Proof ctxt)
        |> #arg_regs
    in rewrite_insert_current_registers_eq_tac (registers ~~ args) ctxt end
  in TU.FOCUS_PARAMS_CTXT' (TU.SUBGOAL_STRIPPED (snd o snd) o focused_tac) end

fun finish_tailcall_tac get_HOL_eqs ctxt =
  let val finish_goal_tac = Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN ctxt []
  in
    tailcall_tac ctxt
    THEN' rewrite_HOL_eq_tac get_HOL_eqs ctxt
    THEN' TU.TRY' (simp_HOL_def_tac ctxt)
    THEN' rewrite_insert_current_registers_eq_tac' ctxt
    THEN' SIT.remove_state_eq_tac ctxt
    THEN_ALL_NEW finish_goal_tac
  end

fun finish_tac get_HOL_eqs ctxt = SOLVED' (finish_tailcall_tac get_HOL_eqs ctxt)
  ORELSE' finish_non_tailcall_tac get_HOL_eqs ctxt

fun start_run_finish_tac get_IMP_def get_func_corrects
  get_HOL_eqs ctxt =
  start_run_tac get_IMP_def get_func_corrects ctxt
  THEN_ALL_NEW finish_tac get_HOL_eqs ctxt

end
