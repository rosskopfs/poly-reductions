(*  Title: view_cook_levin.ML
    Author: Kevin Kappelmann

Tracking of IMP Minus states changes with View equalities.
*)
signature VIEW_COOK_LEVIN_IMP_MINUS =
sig

(* view equality utils *)
val is_VIEW_eq_prop : term -> bool
val find_cview_eq_prop : cterm list -> (int * cterm) option
val dest_VIEW_eq_cprop : cterm -> cterm * cterm

val dest_VIEW_cview : cterm -> cterm

(* interpretation of view state *)
val interp_state_of_cview : cterm -> cterm
val interp_state_view_SIMPS_TO_thm_resultsq : Proof.context -> cterm ->
  (thm * cterm) Seq.seq

(* rewrite state retrieval based on view equality *)
val rewrite_state_app_tac : (thm -> int -> tactic) -> Proof.context -> thm ->
  thm -> int -> tactic
val rewrite_all_state_app_tac : (thm -> int -> tactic) -> Proof.context -> thm ->
  thm -> int -> tactic
val rewrite_all_state_app_tac' : (Proof.context -> thm -> int -> tactic) ->
  Proof.context -> int -> tactic

(* initialise view equality premise *)
val init_view_eq_thm : cterm -> Proof.context -> cterm -> thm
val init_view_eq_tac : cterm -> Proof.context -> int -> tactic

(* remove view equality premise *)
val remove_view_eq_tac : Proof.context -> int -> tactic

(* print view equality premise *)
val pretty_view_eq : Proof.context -> cterm -> Pretty.T
val print_view_eq_tac : Proof.context -> int -> tactic

(* update view equality according to a new update condition *)
val update_view_state_eq_updatesq : Proof.context -> thm -> thm -> thm -> thm Seq.seq

(** update view equality following an assignment **)
val update_view_assign_tac : Proof.context -> int -> tactic

(* update view equality according to a new retrieval condition *)
val update_view_state_app_eqsq : (int -> tactic) -> Proof.context -> thm ->
  thm -> thm -> thm Seq.seq
val update_view_state_app_eq_tac : (int -> tactic) -> Proof.context -> int -> tactic

(* update view equality following a subprogram invocation *)
val update_view_invoke_subprogram_vars_thmsq : Proof.context -> thm -> thm ->
  thm -> thm Seq.seq
val update_view_invoke_subprogram_tac : thm -> Proof.context -> int -> tactic

end

structure View_Cook_Levin_IMP_Minus : VIEW_COOK_LEVIN_IMP_MINUS =
struct

structure U = View_Util
structure SS = State_Seq
structure SSS = State_Stack_Seq
infix 1 SS_THEN
val op SS_THEN = op State_Seq_THEN

(* view equality utils *)

val is_VIEW_eq_prop = U.try_bool
  (\<^Const_fn>\<open>HOL.eq _ for \<^Const>\<open>VIEW for _\<close> \<^Const>\<open>VIEW for _\<close>=> true\<close>
    o U.dest_Trueprop)
val find_cview_eq_prop = U.find_first_index (is_VIEW_eq_prop o Thm.term_of)
val dest_VIEW_eq_cprop = U.cdest_eq o U.cdest_Trueprop

val dest_VIEW_cview = Thm.dest_arg o Thm.dest_arg

val no_view_prem_msg = "Could not find VIEW premise"

fun find_cview_eq_prop_seq cprops =
  let fun f_none _ = writeln no_view_prem_msg
  in find_cview_eq_prop cprops |> U.seq_of_opt f_none end

(* big step state utils *)

val is_IMP_big_step_state_prop =
  U.try_bool (\<^Const_fn>\<open>big_step_t for _ _ _ => true\<close> o U.dest_Trueprop)
val get_IMP_big_step_state =
  \<^Const_fn>\<open>big_step_t for \<^Const>\<open>Pair _ _ for _ state\<close> _ _ => state\<close>

val find_IMP_big_step_state = find_first is_IMP_big_step_state_prop
  #> Option.map (get_IMP_big_step_state o U.dest_Trueprop)

(* interpretation of view state *)

fun interp_state_of_cview cview = \<^instantiate>\<open>cview in
  cterm\<open>interp_state (view_state cview) :: AExp.state\<close>\<close>

val interp_reflect_thms = @{thms interp_state_State_eq interp_keys_Keys_eq}

fun mem_keys_tac ctxt =
  fast_force_tac (ctxt addsimps @{thms interp_keys_Keys_eq}) |> SOLVED'

fun simp_interp_view_tac ctxt =
  Simplifier.safe_simp_tac ctxt
  THEN' Simplifier.safe_simp_tac (U.set_simps ctxt @{thms interp_view_eq})
  THEN' Simplifier.safe_simp_tac (ctxt addsimps interp_reflect_thms)

fun interp_state_view_SIMPS_TO_thm_resultsq ctxt =
  interp_state_of_cview #> Simps_To.SIMPS_TO_thm_resultsq (simp_interp_view_tac ctxt) ctxt

fun interp_state_lhs_view_eq_SIMPS_TO_thm_resultsq ctxt =
  dest_VIEW_eq_cprop
  #> fst
  #> dest_VIEW_cview
  #> interp_state_view_SIMPS_TO_thm_resultsq ctxt

(* rewrite state retrieval based on view equality *)

structure Seq_Monad = Monad(Seq_Monad_Base)

fun rewrite_state_app_tac subst_tac ctxt view_eq_thm view_lhs_state_SIMPS_TO_thm =
  let val mk_rewrite_tac =
    HEADGOAL (U.resolve_all_tac ctxt [view_eq_thm, view_lhs_state_SIMPS_TO_thm])
    Seq_THEN Seq.single o (fn state_app_eqI =>
      subst_tac state_app_eqI
      THEN' mem_keys_tac ctxt
      THEN' Simps_To.SIMPS_TO_tac (
        simp_interp_view_tac ctxt
        THEN' Simplifier.simp_tac ctxt))
    #> Seq_Monad.flat2
  in mk_rewrite_tac @{thm VIEW_state_app_eqI} end

fun rewrite_all_state_app_tac subst_tac = REPEAT o CHANGED oooo rewrite_state_app_tac subst_tac

val interp_state_lhs_view_eq_SIMPS_TO_thm_result_state_seq =
  SS.get ()
  SS_THEN SS.lift_state_monad (K o find_cview_eq_prop_seq o SSS.S.SR.value)
  SS_THEN SSS.lift_push_state_monad fst (fn (_, cview_eq_prem) => fn (_, ctxt) =>
    interp_state_lhs_view_eq_SIMPS_TO_thm_resultsq ctxt cview_eq_prem)

fun rewrite_all_state_app_tac' subst_tac =
  let
    fun rewrite_focused_tac view_lhs_state_SIMPS_TO_thm {prems=[view_eq_thm], context=ctxt,...} =
      rewrite_all_state_app_tac (subst_tac ctxt) ctxt view_eq_thm view_lhs_state_SIMPS_TO_thm
    val rewrite_tac =
      interp_state_lhs_view_eq_SIMPS_TO_thm_result_state_seq
      SS_THEN SS.lift_state_single (fn (view_lhs_state_SIMPS_TO_thm, _) =>
        fn ((view_eq_prem_index, _), ctxt) =>
        U.focus_prems_tac [view_eq_prem_index] (rewrite_focused_tac view_lhs_state_SIMPS_TO_thm) ctxt)
      |> SS.eval
      #> Seq_Monad.flat2
  in U.FOCUS_PARAMS_CTXT' (U.CSUBGOAL_PREMS_CONCL fst o (rewrite_tac oo SSS.SRS.init)) end

(* initialise view equality premise *)

fun init_view_eq_thm ks ctxt IMP_state =
  let val cview = \<^instantiate>\<open>IMP_state and ks in
    cterm\<open>View (State IMP_state) (Keys ks)\<close> for IMP_state :: AExp.state\<close>
  in infer_instantiate' ctxt [SOME cview] @{thm VIEW_start} end

fun init_view_eq_tac ks ctxt =
  let
    fun tac (SOME IMP_state) = Thm.cterm_of ctxt IMP_state
        |> init_view_eq_thm ks ctxt
        |> U.insert_tac
      | tac NONE = (writeln "Could not find IMP state premise"; K no_tac)
  in U.SUBGOAL_PREMS_CONCL (find_IMP_big_step_state o fst) tac end

(* remove view equality premise *)

val remove_view_eq_tac =
  let
    fun tac (SOME (i, _)) = U.thin_tac i
      | tac NONE = (writeln no_view_prem_msg; K no_tac)
  in
    U.CSUBGOAL_PREMS_CONCL (find_cview_eq_prop o fst) tac
    |> K
    |> U.FOCUS_PARAMS'
  end

(* print view equality premise *)

fun pretty_view_eq ctxt cview_eq =
  let
    val simp_tac = Simplifier.safe_simp_tac (ctxt addsimps @{thms VIEW_eq})
      THEN' simp_interp_view_tac ctxt
    val (_, simp_interp_view_eq) =
      Simps_To.SIMPS_TO_thm_resultsq simp_tac ctxt cview_eq |> Seq.hd
  in Syntax.pretty_term ctxt (Thm.term_of simp_interp_view_eq) end

fun print_view_eq_tac ctxt =
  let
    fun tac (SOME (_, cview_eq_prem)) = pretty_view_eq ctxt (U.cdest_Trueprop cview_eq_prem)
        |> Pretty.writeln
        |> K o K all_tac
      | tac NONE = (writeln no_view_prem_msg; K no_tac)
  in U.CSUBGOAL_PREMS_CONCL (find_cview_eq_prop o fst) tac end

(* update view equality according to a new update condition *)

fun update_view_state_eq_updatesq ctxt view_eq_thm interp_state_lhs_view_eq_SIMPS_TO_thm
  state_eq_update_thm =
  let
    val assign_simps = @{thms AExp.aval.simps AExp.atomVal.simps}
    val simp_tac = Simplifier.safe_simp_tac (U.set_simps ctxt assign_simps)
      THEN' rewrite_all_state_app_tac (U.subst_first_tac ctxt) ctxt
        view_eq_thm interp_state_lhs_view_eq_SIMPS_TO_thm
    val tac =
      U.resolve_all_tac ctxt [view_eq_thm, interp_state_lhs_view_eq_SIMPS_TO_thm, state_eq_update_thm]
      THEN' Simps_To.SIMPS_TO_tac simp_tac
      |> SOLVED' |> HEADGOAL
  in tac @{thm update_VIEW_state_eq_update} end

(** update view equality following an assignment **)

val dest_assign_prem_prop = U.dest_eq o U.dest_Trueprop
val dest_assign_prem_rhs = \<^Const_fn>\<open>fun_upd _ _ for s k v => \<open>(s, (k, v))\<close>\<close>
fun is_assign_prem_prop state = U.try_bool (dest_assign_prem_prop #> snd #>
  dest_assign_prem_rhs #> fst #> rpair state #> Term.aconv)
fun find_cassign_prem_prop view_eq_lhs_state =
  U.find_first_index (is_assign_prem_prop view_eq_lhs_state o Thm.term_of)

val update_view_assign_tac =
  let
    fun find_assign_prem ctxt cview_eq_lhs_state =
      let
        val view_eq_lhs_state = Thm.term_of cview_eq_lhs_state
        fun f_none _ = Pretty.block [
            Pretty.str "Could not find assign premise for state ",
            Syntax.pretty_term ctxt view_eq_lhs_state
          ] |> Pretty.writeln
      in find_cassign_prem_prop view_eq_lhs_state #> U.seq_of_opt f_none end
    fun insert_new_view_eq_tac interp_state_lhs_view_eq_thm
      {prems=[view_eq_thm, assign_thm], context=ctxt,...} =
      update_view_state_eq_updatesq ctxt view_eq_thm interp_state_lhs_view_eq_thm assign_thm
      |> Seq.map U.insert_tac
      |> Seq_Monad.flat2
    val new_view_eq_tac =
      interp_state_lhs_view_eq_SIMPS_TO_thm_result_state_seq
      SS_THEN SSS.lift_push_state_monad fst (fn (_, cview_eq_lhs_state) => fn ((_, cprems), ctxt) =>
        find_assign_prem ctxt cview_eq_lhs_state cprems)
      SS_THEN SS.lift_state_single (fn (assign_prem_index, _) =>
        fn ((interp_state_lhs_view_eq_thm, (view_eq_prem_index, _)), ctxt) =>
        U.focus_delete_prems_tac [view_eq_prem_index, assign_prem_index]
          (insert_new_view_eq_tac interp_state_lhs_view_eq_thm)
          ctxt)
      |> SS.eval
      #> Seq_Monad.flat2
  in U.FOCUS_PARAMS_CTXT' (U.CSUBGOAL_PREMS_CONCL fst o (new_view_eq_tac oo SSS.SRS.init)) end

fun is_state_app_eq_prop state = U.try_bool
  (\<^Const_fn>\<open>HOL.eq _ for s_app _ => \<open>(head_of s_app) aconv state\<close>\<close> o U.dest_Trueprop)

fun find_state_app_eq_prop lhs_state =
  U.find_first_index (is_state_app_eq_prop lhs_state o Thm.term_of)

fun update_view_state_app_eqsq simp_tac ctxt view_eq_thm interp_state_lhs_view_eq_SIMPS_TO_thm
  state_app_eq_thm =
  let val tac =
    U.resolve_all_tac ctxt [view_eq_thm, interp_state_lhs_view_eq_SIMPS_TO_thm, state_app_eq_thm]
    THEN' Simps_To.SIMPS_TO_tac simp_tac
    |> SOLVED' |> HEADGOAL
  in tac @{thm update_VIEW_state_app_eq} end

fun update_view_state_app_eq_tac simp_tac =
  let
    fun find_state_app_eq_prem ctxt cview_lhs_state =
      let
        val view_lhs_state = Thm.term_of cview_lhs_state
        fun f_none _ = Pretty.block [
            Pretty.str "Could not find state application premise for state ",
            Syntax.pretty_term ctxt view_lhs_state
          ] |> Pretty.writeln
      in find_state_app_eq_prop view_lhs_state #> U.seq_of_opt f_none end
    fun insert_new_view_eq_tac interp_state_lhs_view_eq_thm
      {prems=[view_eq_thm, state_app_eq_thm], context=ctxt,...} =
      update_view_state_app_eqsq simp_tac ctxt view_eq_thm interp_state_lhs_view_eq_thm state_app_eq_thm
      |> Seq.map U.insert_tac
      |> Seq_Monad.flat2
    val new_view_eq_tac =
      interp_state_lhs_view_eq_SIMPS_TO_thm_result_state_seq
      SS_THEN SSS.lift_push_state_monad fst (fn (_, cview_eq_lhs_state) => fn ((_, cprems), ctxt) =>
        find_state_app_eq_prem ctxt cview_eq_lhs_state cprems)
      SS_THEN SS.lift_state_single (fn (state_app_eq_prem_index, _) =>
        fn ((interp_state_lhs_view_eq_thm, (view_eq_prem_index, _)), ctxt) =>
        U.focus_delete_prems_tac [view_eq_prem_index, state_app_eq_prem_index]
          (insert_new_view_eq_tac interp_state_lhs_view_eq_thm)
          ctxt)
      |> SS.eval
      #> Seq_Monad.flat2
  in U.FOCUS_PARAMS_CTXT' (U.CSUBGOAL_PREMS_CONCL fst o (new_view_eq_tac oo SSS.SRS.init)) end

fun update_view_invoke_subprogram_vars_thmsq ctxt view_eq_thm interp_state_lhs_view_eq_SIMPS_TO_thm
  correctness_prem_thm =
  let val tac =
    U.resolve_all_tac ctxt [view_eq_thm, interp_state_lhs_view_eq_SIMPS_TO_thm, correctness_prem_thm]
    THEN' (REPEAT_DETERM_N 2 o mem_keys_tac ctxt)
    |> SOLVED' |> HEADGOAL
  in tac @{thm update_VIEW_invoke_subprogram_vars} end

(*TODO: the following should be rewritten to use the state-sequence monad;
one can then also remove the 'EXTRACT_NONE' and 'extract_opt' terms from the Util structure*)
fun find_update_view_invoke_subprogram_correctness_prem ctxt view_lhs_state cprems =
  (let
    val IMP_state = map Thm.term_of cprems
      |> find_IMP_big_step_state
      |> U.extract_opt (K "Could not find IMP state premise")
    val update_view_invoke_subprogram_vars_thm =
      @{thm update_VIEW_invoke_subprogram_vars}
      |> infer_instantiate' ctxt (map (Thm.cterm_of ctxt |> Option.map)
        [NONE, NONE, SOME view_lhs_state, NONE, NONE, SOME IMP_state])
    val correctness_prem_of_thm =
      let val correctness_prem_index = 2
      in nth (Thm.cprems_of update_view_invoke_subprogram_vars_thm) correctness_prem_index end
    val correctness_prem = cprems
      |> U.find_first_index (Term.could_unify o apply2 Thm.term_of o pair correctness_prem_of_thm)
      |> U.extract_opt (K "Could not find vars correctness theorem premise")
  in SOME correctness_prem end)
  handle U.EXTRACT_NONE msg => (writeln (msg ()); NONE)

fun update_view_invoke_subprogram_tac imp_to_HOL_state_thm =
  let
    fun find_correctness_prem ctxt cview_eq_lhs_state =
      let
        val view_eq_lhs_state = Thm.term_of cview_eq_lhs_state
        fun f_none _ = Pretty.block [
          Pretty.str "Could not find vars correctness premise for state ",
          Syntax.pretty_term ctxt view_eq_lhs_state
        ] |> Pretty.writeln
      in
        find_update_view_invoke_subprogram_correctness_prem ctxt view_eq_lhs_state
        #> U.seq_of_opt f_none
      end
    fun find_new_state_app_eq_prem ctxt cnew_view_lhs_state =
      let
        val new_view_lhs_state = Thm.term_of cnew_view_lhs_state
        fun f_none _ = Pretty.block [
            Pretty.str "Could not find state application premise for new state ",
            Syntax.pretty_term ctxt new_view_lhs_state
          ] |> Pretty.writeln
      in find_state_app_eq_prop new_view_lhs_state #> U.seq_of_opt f_none end
    fun insert_update_new_view_eq_tac view_eq_thm interp_state_lhs_view_eq_thm
      new_view_eq_thm interp_state_lhs_new_view_eq_thm {prems=[correctness_prem], context=ctxt,...} =
      let val simp_tac =
        Simplifier.safe_simp_tac (ctxt addsimps [imp_to_HOL_state_thm])
        THEN' rewrite_all_state_app_tac (U.subst_first_tac ctxt) ctxt view_eq_thm
          interp_state_lhs_view_eq_thm
      in
        update_view_state_app_eqsq simp_tac ctxt new_view_eq_thm interp_state_lhs_new_view_eq_thm
          correctness_prem
        |> Seq.map U.insert_tac
        |> Seq_Monad.flat2
      end
    fun insert_new_view_eq_tac
      {prems=[view_eq_thm, correctness_prem_thm], context=ctxt, concl=concl,...} =
      SS.get ()
      SS_THEN SS.interp o SS.put o SSS.SRS.init ctxt
      SS_THEN SS.lift_state_monad (fn _ => fn (interp_state_lhs_view_eq_thm, ctxt) =>
        update_view_invoke_subprogram_vars_thmsq ctxt view_eq_thm interp_state_lhs_view_eq_thm
          correctness_prem_thm)
      SS_THEN SSS.lift_push_state_monad I (fn new_view_eq_thm => fn (_, ctxt) =>
        Thm.cprop_of new_view_eq_thm |> interp_state_lhs_view_eq_SIMPS_TO_thm_resultsq ctxt)
      SS_THEN SSS.lift_push_state_monad fst (fn (_, cnew_view_lhs_state) => fn (_, ctxt) =>
        find_new_state_app_eq_prem ctxt cnew_view_lhs_state (Drule.strip_imp_prems concl))
      SS_THEN SS.lift_state_single (fn (new_state_app_eq_prem_index, _) =>
        fn ((interp_state_lhs_new_view_eq_thm, (new_view_eq_thm, interp_state_lhs_view_eq_thm)),
          ctxt) =>
        U.focus_delete_prems_tac [new_state_app_eq_prem_index]
        (insert_update_new_view_eq_tac view_eq_thm interp_state_lhs_view_eq_thm
          new_view_eq_thm interp_state_lhs_new_view_eq_thm) ctxt)
      |> SS.eval
      #> Seq_Monad.flat2
    val new_view_eq_tac =
      interp_state_lhs_view_eq_SIMPS_TO_thm_result_state_seq
      SS_THEN SSS.lift_push_state_monad fst (fn (_, cview_eq_lhs_state) => fn ((_, cprems), ctxt) =>
        find_correctness_prem ctxt cview_eq_lhs_state cprems)
      SS_THEN SS.lift_state_single (fn (correctness_prem_index, _) =>
        fn ((interp_state_lhs_view_eq_thm, (view_eq_prem_index, _)), ctxt) =>
        U.focus_delete_prems_tac [view_eq_prem_index, correctness_prem_index]
          (U.flip insert_new_view_eq_tac interp_state_lhs_view_eq_thm) ctxt)
      |> SS.eval
      #> Seq_Monad.flat2
  in U.FOCUS_PARAMS_CTXT' (U.CSUBGOAL_PREMS_CONCL fst o (new_view_eq_tac oo SSS.SRS.init)) end

end
