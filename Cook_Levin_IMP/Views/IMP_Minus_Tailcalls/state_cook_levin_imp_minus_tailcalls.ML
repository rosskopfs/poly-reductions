(*  Title:  Views/IMP_Minus_Calls/state_cook_levin_imp_minus_tailcalls.ML
    Author: Kevin Kappelmann

Tracking of IMP Minus states changes with State equalities.
*)
signature STATE_COOK_LEVIN_IMP_MINUS_TAILCALLS =
sig

(* state equality utils *)
val is_STATE_eq_prop : term -> bool
val find_cstate_eq_prop : cterm list -> (int * cterm) option
val dest_STATE_eq_cprop : cterm -> cterm * cterm

val dest_STATE_cinterp_state : cterm -> cterm

(* interpretation of state *)
val interp_state_SIMPS_TO_thm_resultsq : Proof.context -> cterm ->
  (thm * cterm) Seq.seq

(* rewrite state retrieval based on state equality *)
val rewrite_state_app_tac : (thm -> int -> tactic) -> Proof.context -> thm ->
  thm -> int -> tactic
val rewrite_all_state_app_tac : (thm -> int -> tactic) -> Proof.context -> thm ->
  thm -> int -> tactic
val rewrite_all_state_app_tac' : (Proof.context -> thm -> int -> tactic) ->
  Proof.context -> int -> tactic

(* initialise state equality premise *)
val init_state_eq_thm : Proof.context -> cterm -> thm
val init_state_eq_tac : Proof.context -> int -> tactic

(* remove state equality premise *)
val remove_state_eq_tac : Proof.context -> int -> tactic

(* print state equality premise *)
val pretty_state_eq : Proof.context -> cterm -> Pretty.T
val print_state_eq_tac : Proof.context -> int -> tactic

(* update state equality according to a new update condition *)
val update_state_state_eq_updatesq : thm list -> Proof.context -> thm -> thm -> thm -> thm Seq.seq

(** update state equality following an assignment **)
val update_state_assign_tac : Proof.context -> int -> tactic

(* update state equality according to a new retrieval condition *)
val update_state_state_app_eqsq : (int -> tactic) -> Proof.context -> thm ->
  thm -> thm -> thm Seq.seq
val update_state_state_app_eq_tac : (int -> tactic) -> Proof.context -> int -> tactic

(* update state equality following a subprogram call *)
val update_state_call_tac : thm -> Proof.context -> int -> tactic

end

structure State_Cook_Levin_IMP_Minus_Tailcalls : STATE_COOK_LEVIN_IMP_MINUS_TAILCALLS =
struct

structure U = View_Util
structure SS = State_Seq
structure SSS = State_Stack_Seq
infix 1 SS_THEN
val op SS_THEN = op State_Seq_THEN

(* state equality utils *)

val is_STATE_eq_prop = U.try_bool
  (\<^Const_fn>\<open>HOL.eq _ for \<^Const>\<open>STATE for _\<close> \<^Const>\<open>STATE for _\<close>=> true\<close>
    o U.dest_Trueprop)
val find_cstate_eq_prop = U.find_first_index (is_STATE_eq_prop o Thm.term_of)
val dest_STATE_eq_cprop = U.cdest_eq o U.cdest_Trueprop

val dest_STATE_cinterp_state = Thm.dest_arg

val no_state_prem_msg = "Could not find STATE premise"

fun find_cstate_eq_prop_seq cprops =
  let fun f_none _ = writeln no_state_prem_msg
  in find_cstate_eq_prop cprops |> U.seq_of_opt f_none end

(* big step state utils *)

val is_IMP_big_step_state_prop =
  U.try_bool (\<^Const_fn>\<open>tbig_step_t for _ _ _ _ => true\<close> o U.dest_Trueprop)
val get_IMP_big_step_state =
  \<^Const_fn>\<open>tbig_step_t for _ \<^Const>\<open>Pair _ _ for _ state\<close> _ _ => state\<close>

val find_IMP_big_step_state = find_first is_IMP_big_step_state_prop
  #> Option.map (get_IMP_big_step_state o U.dest_Trueprop)

(* interpretation of state *)

val interp_reflect_thms = @{thms interp_state_State_eq}

fun simp_interp_state_tac ctxt =
  Simplifier.safe_simp_tac ctxt
  THEN' Simplifier.safe_simp_tac (U.set_simps ctxt interp_reflect_thms)
  THEN' Simplifier.safe_simp_tac ctxt

fun interp_state_SIMPS_TO_thm_resultsq ctxt =
  Simps_To.SIMPS_TO_thm_resultsq (simp_interp_state_tac ctxt) ctxt

fun interp_state_lhs_state_eq_SIMPS_TO_thm_resultsq ctxt =
  dest_STATE_eq_cprop
  #> fst
  #> dest_STATE_cinterp_state
  #> interp_state_SIMPS_TO_thm_resultsq ctxt

(* rewrite state retrieval based on state equality *)

structure Seq_Monad = Monad(Seq_Monad_Base)

fun state_app_eq_thmsq ctxt state_eq_thm state_lhs_state_SIMPS_TO_thm =
   @{thm STATE_state_app_eqI}
   |> HEADGOAL (U.resolve_all_tac ctxt [state_eq_thm, state_lhs_state_SIMPS_TO_thm])

fun rewrite_state_app_eq_thm_tac subst_tac ctxt state_app_eq_thm =
  subst_tac state_app_eq_thm
  THEN' Simps_To.SIMPS_TO_tac
    (simp_interp_state_tac ctxt
    THEN' Simplifier.simp_tac ctxt)

fun rewrite_state_app_tacsq subst_tac ctxt state_eq_thm state_lhs_state_SIMPS_TO_thm =
  state_app_eq_thmsq ctxt state_eq_thm state_lhs_state_SIMPS_TO_thm
  |> Seq.map (rewrite_state_app_eq_thm_tac subst_tac ctxt)

val rewrite_state_app_tac = Seq_Monad.flat2 oooo rewrite_state_app_tacsq

val rewrite_all_state_app_tac =
  Seq_Monad.flat2 o Seq.map (fn tac => REPEAT o CHANGED_PROP o tac) oooo rewrite_state_app_tacsq

val interp_state_lhs_state_eq_SIMPS_TO_thm_result_state_seq =
  SS.get ()
  SS_THEN SS.lift_state_monad (K o find_cstate_eq_prop_seq o SSS.S.SR.value)
  SS_THEN SSS.lift_push_state_monad fst (fn (_, cstate_eq_prem) => fn (_, ctxt) =>
    interp_state_lhs_state_eq_SIMPS_TO_thm_resultsq ctxt cstate_eq_prem)

fun rewrite_all_state_app_tac' subst_tac =
  let
    fun rewrite_focused_tac state_lhs_state_SIMPS_TO_thm {prems=[state_eq_thm], context=ctxt,...} =
      rewrite_all_state_app_tac (subst_tac ctxt) ctxt state_eq_thm state_lhs_state_SIMPS_TO_thm
    val rewrite_tac =
      interp_state_lhs_state_eq_SIMPS_TO_thm_result_state_seq
      SS_THEN SS.lift_state_single (fn (state_lhs_state_SIMPS_TO_thm, _) =>
        fn ((state_eq_prem_index, _), ctxt) =>
        U.focus_prems_tac [state_eq_prem_index] (rewrite_focused_tac state_lhs_state_SIMPS_TO_thm) ctxt)
      |> SS.eval
      #> Seq_Monad.flat2
  in U.FOCUS_PARAMS_CTXT' (U.CSUBGOAL_PREMS_CONCL fst o (rewrite_tac oo SSS.SRS.init)) end

(* initialise state equality premise *)

fun init_state_eq_thm ctxt IMP_state =
  let val cstate = \<^instantiate>\<open>IMP_state in
    cterm\<open>State IMP_state\<close> for IMP_state :: AExp.state\<close>
  in infer_instantiate' ctxt [SOME cstate] @{thm STATE_start} end

fun init_state_eq_tac ctxt =
  let
    fun tac (SOME IMP_state) = Thm.cterm_of ctxt IMP_state
        |> init_state_eq_thm ctxt
        |> U.insert_tac
      | tac NONE = (writeln "Could not find IMP state premise"; K no_tac)
  in U.SUBGOAL_PREMS_CONCL (find_IMP_big_step_state o fst) tac end

(* remove state equality premise *)

val remove_state_eq_tac =
  let
    fun tac (SOME (i, _)) = U.thin_tac i
      | tac NONE = (writeln no_state_prem_msg; K no_tac)
  in
    U.CSUBGOAL_PREMS_CONCL (find_cstate_eq_prop o fst) tac
    |> K
    |> U.FOCUS_PARAMS'
  end

(* print state equality premise *)

fun pretty_state_eq ctxt cstate_eq =
  let
    val simp_tac = Simplifier.safe_simp_tac (ctxt addsimps @{thms STATE_eq})
      THEN' simp_interp_state_tac ctxt
    val (_, simp_interp_state_eq) =
      Simps_To.SIMPS_TO_thm_resultsq simp_tac ctxt cstate_eq |> Seq.hd
  in Syntax.pretty_term ctxt (Thm.term_of simp_interp_state_eq) end

fun print_state_eq_tac ctxt =
  let
    fun tac (SOME (_, cstate_eq_prem)) = pretty_state_eq ctxt (U.cdest_Trueprop cstate_eq_prem)
        |> Pretty.writeln
        |> K o K all_tac
      | tac NONE = (writeln no_state_prem_msg; K no_tac)
  in U.CSUBGOAL_PREMS_CONCL (find_cstate_eq_prop o fst) tac end

(* update state equality according to a new update condition *)

fun update_state_state_eq_updatesq simp_thms ctxt state_eq_thm
  interp_state_lhs_state_eq_SIMPS_TO_thm assign_thm =
  let
    val simp_thms = simp_thms @ @{thms AExp.aval.simps AExp.atomVal.simps}
    val simp_tac = Simplifier.safe_simp_tac (U.set_simps ctxt simp_thms)
      THEN' rewrite_all_state_app_tac (U.subst_first_tac ctxt) ctxt
        state_eq_thm interp_state_lhs_state_eq_SIMPS_TO_thm
    val tac =
      U.resolve_all_tac ctxt [state_eq_thm, interp_state_lhs_state_eq_SIMPS_TO_thm, assign_thm]
      THEN' Simps_To.SIMPS_TO_tac simp_tac
      |> SOLVED' |> HEADGOAL
  in tac @{thm update_STATE_state_eq_update} end

(** update state equality following an assignment **)

val dest_assign_prem_prop = U.dest_eq o U.dest_Trueprop
val dest_assign_prem_rhs = \<^Const_fn>\<open>fun_upd _ _ for s k v => \<open>(s, (k, v))\<close>\<close>
fun is_assign_prem_prop state = U.try_bool (dest_assign_prem_prop #> snd #>
  dest_assign_prem_rhs #> fst #> rpair state #> Term.aconv)
fun find_cassign_prem_prop state_eq_lhs_state =
  U.find_first_index (is_assign_prem_prop state_eq_lhs_state o Thm.term_of)

val update_state_assign_tac =
  let
    fun find_assign_prem ctxt cstate_eq_lhs_state =
      let
        val state_eq_lhs_state = Thm.term_of cstate_eq_lhs_state
        fun f_none _ = Pretty.block [
            Pretty.str "Could not find assign premise for state ",
            Syntax.pretty_term ctxt state_eq_lhs_state
          ] |> Pretty.writeln
      in find_cassign_prem_prop state_eq_lhs_state #> U.seq_of_opt f_none end
    fun insert_new_state_eq_tac interp_state_lhs_state_eq_thm
      {prems=[state_eq_thm, assign_thm], context=ctxt,...} =
      update_state_state_eq_updatesq [] ctxt state_eq_thm interp_state_lhs_state_eq_thm assign_thm
      |> Seq.map U.insert_tac
      |> Seq_Monad.flat2
    val new_state_eq_tac =
      interp_state_lhs_state_eq_SIMPS_TO_thm_result_state_seq
      SS_THEN SSS.lift_push_state_monad fst (fn (_, cstate_eq_lhs_state) => fn ((_, cprems), ctxt) =>
        find_assign_prem ctxt cstate_eq_lhs_state cprems)
      SS_THEN SS.lift_state_single (fn (assign_prem_index, _) =>
        fn ((interp_state_lhs_state_eq_thm, (state_eq_prem_index, _)), ctxt) =>
        U.focus_delete_prems_tac [state_eq_prem_index, assign_prem_index]
          (insert_new_state_eq_tac interp_state_lhs_state_eq_thm)
          ctxt)
      |> SS.eval
      #> Seq_Monad.flat2
  in U.FOCUS_PARAMS_CTXT' (U.CSUBGOAL_PREMS_CONCL fst o (new_state_eq_tac oo SSS.SRS.init)) end

fun is_state_app_eq_prop state = U.try_bool
  (\<^Const_fn>\<open>HOL.eq _ for s_app _ => \<open>(head_of s_app) aconv state\<close>\<close> o U.dest_Trueprop)

fun find_state_app_eq_prop lhs_state =
  U.find_first_index (is_state_app_eq_prop lhs_state o Thm.term_of)

fun update_state_state_app_eqsq simp_tac ctxt state_eq_thm interp_state_lhs_state_eq_SIMPS_TO_thm
  state_app_eq_thm =
  let val tac =
    U.resolve_all_tac ctxt [state_eq_thm, interp_state_lhs_state_eq_SIMPS_TO_thm, state_app_eq_thm]
    THEN' Simps_To.SIMPS_TO_tac simp_tac
    |> SOLVED' |> HEADGOAL
  in tac @{thm update_STATE_state_app_eq} end

fun update_state_state_app_eq_tac simp_tac =
  let
    fun find_state_app_eq_prem ctxt cstate_lhs_state =
      let
        val state_lhs_state = Thm.term_of cstate_lhs_state
        fun f_none _ = Pretty.block [
            Pretty.str "Could not find state application premise for state ",
            Syntax.pretty_term ctxt state_lhs_state
          ] |> Pretty.writeln
      in find_state_app_eq_prop state_lhs_state #> U.seq_of_opt f_none end
    fun insert_new_state_eq_tac interp_state_lhs_state_eq_thm
      {prems=[state_eq_thm, state_app_eq_thm], context=ctxt,...} =
      update_state_state_app_eqsq simp_tac ctxt state_eq_thm interp_state_lhs_state_eq_thm state_app_eq_thm
      |> Seq.map U.insert_tac
      |> Seq_Monad.flat2
    val new_state_eq_tac =
      interp_state_lhs_state_eq_SIMPS_TO_thm_result_state_seq
      SS_THEN SSS.lift_push_state_monad fst (fn (_, cstate_eq_lhs_state) => fn ((_, cprems), ctxt) =>
        find_state_app_eq_prem ctxt cstate_eq_lhs_state cprems)
      SS_THEN SS.lift_state_single (fn (state_app_eq_prem_index, _) =>
        fn ((interp_state_lhs_state_eq_thm, (state_eq_prem_index, _)), ctxt) =>
        U.focus_delete_prems_tac [state_eq_prem_index, state_app_eq_prem_index]
          (insert_new_state_eq_tac interp_state_lhs_state_eq_thm)
          ctxt)
      |> SS.eval
      #> Seq_Monad.flat2
  in U.FOCUS_PARAMS_CTXT' (U.CSUBGOAL_PREMS_CONCL fst o (new_state_eq_tac oo SSS.SRS.init)) end

fun is_lhs_eq_prop lhs = U.try_bool
  (\<^Const_fn>\<open>HOL.eq _ for t _ => \<open>t aconv lhs\<close>\<close> o U.dest_Trueprop)

fun find_update_state_call_correctness_prem cassign_prem cprems =
  let val (_, (_, v)) = Thm.term_of cassign_prem
    |> U.dest_Trueprop |> U.dest_eq |> snd |> dest_assign_prem_rhs
  in U.find_first_index (is_lhs_eq_prop v o Thm.term_of) cprems end

fun update_state_call_tac imp_to_HOL_state_thm =
  let
    fun find_correctness_prem ctxt cassign_prem =
      let
        fun f_none _ = Pretty.block [
          Pretty.str "Could not find correctness premise for assignment ",
          Syntax.pretty_term ctxt (Thm.term_of cassign_prem)
        ] |> Pretty.writeln
      in find_update_state_call_correctness_prem cassign_prem #> U.seq_of_opt f_none end
    fun find_assign_prem ctxt cstate_eq_lhs_state =
      let
        val state_eq_lhs_state = Thm.term_of cstate_eq_lhs_state
        fun f_none _ = Pretty.block [
            Pretty.str "Could not find assign premise for state ",
            Syntax.pretty_term ctxt state_eq_lhs_state
          ] |> Pretty.writeln
      in find_cassign_prem_prop state_eq_lhs_state #> U.seq_of_opt f_none end
    fun insert_new_state_eq_tac interp_state_lhs_state_eq_thm
      {prems=[state_eq_thm, assign_thm, correctness_eq_thm], context=ctxt,...} =
        update_state_state_eq_updatesq [imp_to_HOL_state_thm, correctness_eq_thm] ctxt state_eq_thm
          interp_state_lhs_state_eq_thm assign_thm
        |> Seq.map U.insert_tac
        |> Seq_Monad.flat2
    val new_state_eq_tac =
      interp_state_lhs_state_eq_SIMPS_TO_thm_result_state_seq
      SS_THEN SSS.lift_push_state_monad fst (fn (_, cstate_eq_lhs_state) => fn ((_, cprems), ctxt) =>
        find_assign_prem ctxt cstate_eq_lhs_state cprems)
      SS_THEN SSS.lift_push_state_monad fst (fn (_, cassign_prem) => fn ((_, (_, cprems)), ctxt) =>
        find_correctness_prem ctxt cassign_prem cprems)
      SS_THEN SS.lift_state_single (fn (correctness_prem_index, _) =>
        fn ((assign_prem_index, (interp_state_lhs_state_eq_thm, (state_eq_prem_index, _))), ctxt) =>
        U.focus_delete_prems_tac [state_eq_prem_index, assign_prem_index, correctness_prem_index]
          (insert_new_state_eq_tac interp_state_lhs_state_eq_thm)
          ctxt)
      |> SS.eval
      #> Seq_Monad.flat2
  in U.FOCUS_PARAMS_CTXT' (U.CSUBGOAL_PREMS_CONCL fst o (new_state_eq_tac oo SSS.SRS.init)) end

end
