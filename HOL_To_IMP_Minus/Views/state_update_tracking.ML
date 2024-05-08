(*  Title:  Views/state_update_tracking.ML
    Author: Kevin Kappelmann

Tracking of STATE equalities.
*)
signature STATE_UPDATE_TRACKING =
sig
include HAS_LOGGER

(* state equality utils *)
val dest_STATE : term -> term
val cdest_STATE : cterm -> cterm
val find_cstate_eq_prop : cterm list -> (int * cterm) option
val dest_STATE_eq_prop : term -> term * term
val dest_STATE_eq_cprop : cterm -> cterm * cterm

(* state retrieval utils *)
val mk_state_retrieval : term -> term -> term
val dest_state_retrieval : term -> term * term
val is_state_state_retrieval : term -> term -> bool
val is_state_state_retrieval_eq : term -> term -> bool
val is_state_state_retrieval_eq_prop : term -> term -> bool

(* interpretation of state *)
val interp_state_SIMPS_TO_thm_resultsq : Proof.context -> cterm ->
  (thm * cterm) Seq.seq

(* TODO: rename function *)
val state_eq_interp_lhs_state_eq_SIMPS_TO_thm_result_state_seq :
  Proof.context -> cterm list -> (thm * cterm * int) Seq.seq

(* rewrite state retrieval based on state equality *)
val rewrite_state_retrieval_tac : (thm -> int -> tactic) -> Proof.context -> thm ->
  thm -> int -> tactic
val rewrite_all_state_retrieval_tac : (thm -> int -> tactic) -> Proof.context -> thm ->
  thm -> int -> tactic
val rewrite_all_state_retrieval_tac' : (Proof.context -> thm -> int -> tactic) ->
  Proof.context -> int -> tactic

val state_retrieval_eq_thmsq : (int -> tactic) -> thm -> thm * term -> Proof.context -> term ->
  term -> thm Seq.seq

(* initialise STATE equality premise *)
val init_state_eq_thm : Proof.context -> cterm -> thm
val init_state_eq_tac : Proof.context -> cterm -> int -> tactic

(* remove state equality premise *)
val remove_state_eq_tac : Proof.context -> int -> tactic

(* print state equality premise *)
val pretty_state_eq : Proof.context -> cterm -> Pretty.T
val print_state_eq_tac : Proof.context -> int -> tactic

(* update state equality according to an update condition *)
val dest_update : term -> term * (term * term)
val dest_update_prem : term -> term * (term * (term * term))
val is_state_update_prem : term -> term -> bool
val find_cupdate_prem_prop : term -> cterm list -> (int * cterm) option

val update_state_state_eq_updatesq : thm list -> Proof.context -> thm -> thm -> thm -> thm Seq.seq
val update_state_state_update_tac : thm list -> Proof.context -> int -> tactic

(* update state equality according to a retrieval condition *)
val update_state_state_retrieval_eqsq : (int -> tactic) -> Proof.context -> thm ->
  thm -> thm -> thm Seq.seq
val update_state_state_retrieval_eq_tac : (int -> tactic) -> Proof.context -> int -> tactic

end

structure State_Update_Tracking : STATE_UPDATE_TRACKING =
struct

val logger = Logger.setup_new_logger Logger.root "State_Update_Tracking"

(*TODO: FIXME: use SIMPS_TO_UNIF instead of SIMPS_TO*)
fun finish_SIMPS_TO_tac ctxt = resolve_tac ctxt [@{thm SIMPS_TOI}]

structure HTIU = HOL_To_IMP_Util
structure GU = General_Util
structure TU = Tactic_Util

structure Seq = HTIU.Seq

val state_eq = curry (op aconv)

(* state equality utils *)
val dest_STATE = \<^Const_fn>\<open>STATE _ for s => s\<close>
val cdest_STATE = Thm.dest_arg

val dest_STATE_eq_prop = HTIU.dest_Trueprop #> HTIU.dest_eq #> tap (apply2 dest_STATE)
val dest_STATE_eq_cprop = HTIU.cdest_Trueprop #> HTIU.cdest_eq
val find_cstate_eq_prop = GU.find_first_index (can dest_STATE_eq_prop o Thm.term_of)

(* state retrieval utils *)
fun mk_state_retrieval state key = state $ key
val dest_state_retrieval = Term.dest_comb
fun is_state_state_retrieval state s_app = dest_state_retrieval s_app |> fst |> state_eq state

fun is_state_state_retrieval_eq state = GU.try_bool
  (HTIU.dest_eq #> fst #> is_state_state_retrieval state)
fun is_state_state_retrieval_eq_prop state = GU.try_bool
  (HTIU.dest_Trueprop #> is_state_state_retrieval_eq state)
fun find_state_state_retrieval_eq_prop lhs_state =
  GU.find_first_index (is_state_state_retrieval_eq_prop lhs_state o Thm.term_of)

(* interpretation of state *)

val interp_reflect_thms = @{thms interp_state_State_eq}

val safe_simp_tac = Simplifier.safe_simp_tac

fun simp_interp_state_tac ctxt =
  safe_simp_tac ctxt
  THEN' safe_simp_tac (HTIU.set_simps ctxt interp_reflect_thms)
  THEN' safe_simp_tac ctxt

fun interp_state_SIMPS_TO_thm_resultsq ctxt =
  Simps_To.SIMPS_TO_thm_resultsq (simp_interp_state_tac ctxt) ctxt

fun state_eq_interp_lhs_state_eq_SIMPS_TO_thm_resultsq ctxt = dest_STATE_eq_cprop
  #> fst #> cdest_STATE #> interp_state_SIMPS_TO_thm_resultsq ctxt

(* rewrite state retrieval based on state equality *)

fun state_retrieval_eq_if_SIMPS_TO_thmsq ctxt state_eq_thm state_lhs_state_SIMPS_TO_thm =
  @{thm STATE_state_app_eqI}
  |> HEADGOAL (HTIU.resolve_all_tac ctxt [state_eq_thm, state_lhs_state_SIMPS_TO_thm])

fun rewrite_state_retrieval_if_SIMPS_TO_tac subst_tac ctxt state_retrieval_eq_thm =
  subst_tac state_retrieval_eq_thm
  THEN' simp_interp_state_tac ctxt
  THEN' Simplifier.simp_tac ctxt
  THEN' finish_SIMPS_TO_tac ctxt

fun rewrite_state_retrieval_tacsq subst_tac ctxt state_eq_thm state_lhs_state_SIMPS_TO_thm =
  let open Seq open Seq.M in
    state_retrieval_eq_if_SIMPS_TO_thmsq
      ctxt state_eq_thm state_lhs_state_SIMPS_TO_thm
    BIND (fn thm =>
    rewrite_state_retrieval_if_SIMPS_TO_tac
      subst_tac ctxt thm
    |> pure)
  end

val rewrite_state_retrieval_tac = Seq.M.flat2 oooo rewrite_state_retrieval_tacsq

val rewrite_all_state_retrieval_tac =
  Seq.M.flat2 o Seq.map (fn tac => REPEAT o CHANGED_PROP o tac) oooo rewrite_state_retrieval_tacsq

fun state_retrieval_eq_thmsq finish_eq_tac state_eq_thm
  (state_lhs_state_SIMPS_TO_thm, state_lhs_state_SIMPS_TO_term) ctxt key term =
  let
    val goal = mk_state_retrieval state_lhs_state_SIMPS_TO_term key
      |> pair term
      |> HTIU.mk_eq
      |> HTIU.mk_Trueprop
      |> Thm.cterm_of ctxt
    val rewrite_eq_tac =
      rewrite_all_state_retrieval_tac (HTIU.subst_first_tac ctxt o single) ctxt
        state_eq_thm state_lhs_state_SIMPS_TO_thm
      THEN' finish_eq_tac
  in (rewrite_eq_tac |> SOLVED' |> TU.apply_tac |> TU.HEADGOAL) goal end

fun state_eq_not_in_prems_msg ctxt prems = Pretty.block [
    Pretty.str "Could not find STATE equality in premises ",
    HTIU.pretty_prems ctxt prems
  ] |> Pretty.string_of

fun state_eq_not_in_cprems_msg ctxt = state_eq_not_in_prems_msg ctxt o map Thm.term_of

fun state_eq_interp_lhs_state_eq_SIMPS_TO_thm_result_state_seq ctxt cprems =
  let open Seq open Seq.M in
    case find_cstate_eq_prop cprems of
      SOME (cstate_eq_prem_index, cstate_eq_prem) =>
        state_eq_interp_lhs_state_eq_SIMPS_TO_thm_resultsq ctxt cstate_eq_prem
        BIND (fn (thm, cterm) =>
          pure (thm, cterm, cstate_eq_prem_index))
    | NONE => (
        @{log Logger.WARN} ctxt (fn _ => state_eq_not_in_cprems_msg ctxt cprems);
        Seq.empty)
  end

fun rewrite_all_state_retrieval_tac' subst_tac =
  let
    open Seq open Seq.M
    fun rewrite_focused_tac state_lhs_state_SIMPS_TO_thm {prems=[state_eq_thm], context=ctxt,...} =
      rewrite_all_state_retrieval_tac (subst_tac ctxt) ctxt state_eq_thm state_lhs_state_SIMPS_TO_thm
    fun rewrite_tac ctxt cprems =
      state_eq_interp_lhs_state_eq_SIMPS_TO_thm_result_state_seq ctxt cprems
      BIND (fn (state_lhs_state_SIMPS_TO_thm, _, state_eq_prem_index) =>
        TU.focus_prems_tac [state_eq_prem_index + 1]
          (rewrite_focused_tac state_lhs_state_SIMPS_TO_thm) ctxt
        |> pure)
      |> flat2
  in TU.FOCUS_PARAMS_CTXT' (TU.CSUBGOAL_STRIPPED (fst o snd) o rewrite_tac) end

(* initialise state equality premise *)

fun init_state_eq_thm ctxt IMP_state =
  let
    val [acT, bcT] = Thm.ctyp_of_cterm IMP_state |> Thm.dest_ctyp
    val cstate = \<^instantiate>\<open>'a = acT and 'b = bcT
      and IMP_state in cterm\<open>State IMP_state\<close> for IMP_state :: \<open>'a \<Rightarrow> 'b\<close>\<close>
  in infer_instantiate' ctxt [SOME cstate] @{thm STATE_start} end

fun init_state_eq_tac ctxt = init_state_eq_thm ctxt
  #> (fn thms => TU.insert_tac [thms] ctxt)

(* remove state equality premise *)

val remove_state_eq_tac =
  let fun tac ctxt cprems = case find_cstate_eq_prop cprems of
      (SOME (i, _)) => TU.thin_tac (i + 1)
    | NONE => (@{log Logger.WARN} ctxt (fn _ => state_eq_not_in_cprems_msg ctxt cprems); K no_tac)
  in TU.FOCUS_PARAMS_CTXT' (TU.CSUBGOAL_STRIPPED (fst o snd) o tac) end

(* print state equality premise *)

fun pretty_state_eq ctxt cstate_eq =
  let
    val simp_tac = safe_simp_tac (ctxt addsimps @{thms STATE_eq})
      THEN' simp_interp_state_tac ctxt
    val (_, simp_interp_state_eq) =
      Simps_To.SIMPS_TO_thm_resultsq simp_tac ctxt cstate_eq |> Seq.hd
  in Syntax.pretty_term ctxt (Thm.term_of simp_interp_state_eq) end

val print_state_eq_tac =
  let fun tac ctxt cprems = case find_cstate_eq_prop cprems of
      (SOME (_, cstate_eq_prem)) => (@{log Logger.INFO} ctxt (fn _ =>
          pretty_state_eq ctxt (HTIU.cdest_Trueprop cstate_eq_prem) |> Pretty.string_of);
        K all_tac)
    | NONE => (@{log Logger.WARN} ctxt (fn _ => state_eq_not_in_cprems_msg ctxt cprems); K no_tac)
  in TU.FOCUS_PARAMS_CTXT' (TU.CSUBGOAL_STRIPPED (fst o snd) o tac) end

(* update state equality according to an update condition *)

fun update_state_state_eq_updatesq simp_thms ctxt state_eq_thm
  interp_state_lhs_state_eq_SIMPS_TO_thm update_thm =
  let
    val simp_tac = safe_simp_tac (HTIU.set_simps ctxt simp_thms)
      THEN' rewrite_all_state_retrieval_tac (HTIU.subst_first_tac ctxt o single) ctxt
        state_eq_thm interp_state_lhs_state_eq_SIMPS_TO_thm
    val tac =
      HTIU.resolve_all_tac ctxt [state_eq_thm, interp_state_lhs_state_eq_SIMPS_TO_thm, update_thm]
      THEN' simp_tac
      THEN' finish_SIMPS_TO_tac ctxt
      |> SOLVED' |> HEADGOAL
  in tac @{thm update_STATE_state_eq_update} end

val dest_update = \<^Const_fn>\<open>fun_upd _ _ for s k v => \<open>(s, (k, v))\<close>\<close>
val dest_update_prem = HTIU.dest_eq ##> dest_update
fun is_state_update_prem state = GU.try_bool (dest_update_prem #> snd #> fst #> state_eq state)
fun find_cupdate_prem_prop state = GU.try_bool
    (Thm.term_of #> HTIU.dest_Trueprop #> is_state_update_prem state)
  |> GU.find_first_index

fun update_state_state_update_tac simp_thms =
  let
    open Seq open Seq.M
    fun insert_new_state_eq_tac interp_state_lhs_state_eq_thm
        {prems=[state_eq_thm, update_thm], context=ctxt,...} =
      update_state_state_eq_updatesq simp_thms ctxt
        state_eq_thm interp_state_lhs_state_eq_thm update_thm
      BIND (fn thm =>
        TU.insert_tac [thm] ctxt |> pure)
      |> flat2
    fun new_state_eq_tac ctxt cprems =
      state_eq_interp_lhs_state_eq_SIMPS_TO_thm_result_state_seq ctxt cprems
      BIND (fn (interp_state_lhs_state_eq_thm, cstate_eq_lhs_state, state_eq_prem_index) =>
        find_cupdate_prem_prop (Thm.term_of cstate_eq_lhs_state) cprems
        |> HTIU.seq_of_opt (fn () => @{log Logger.WARN} ctxt (fn () =>
            Pretty.block [
              Pretty.str "Could not find update premise for state ",
              Syntax.pretty_term ctxt (Thm.term_of cstate_eq_lhs_state),
              Pretty.str " in premises ",
              HTIU.pretty_cprems ctxt cprems
            ] |> Pretty.string_of))
      BIND (fn (update_prem_index, _) =>
        TU.focus_delete_prems_tac
          (HTIU.successors [state_eq_prem_index, update_prem_index])
          (insert_new_state_eq_tac interp_state_lhs_state_eq_thm) ctxt
        |> pure))
      |> flat2
  in TU.FOCUS_PARAMS_CTXT' (TU.CSUBGOAL_STRIPPED (fst o snd) o new_state_eq_tac) end

(* update state equality according to a retrieval condition *)

fun update_state_state_retrieval_eqsq simp_tac ctxt state_eq_thm interp_state_lhs_state_eq_SIMPS_TO_thm
  state_retrieval_eq_thm =
  let val tac =
    HTIU.resolve_all_tac ctxt [state_eq_thm, interp_state_lhs_state_eq_SIMPS_TO_thm, state_retrieval_eq_thm]
    THEN' simp_tac
    THEN' finish_SIMPS_TO_tac ctxt
    |> SOLVED' |> HEADGOAL
  in tac @{thm update_STATE_state_app_eq} end

fun update_state_state_retrieval_eq_tac simp_tac =
  let
    open Seq open Seq.M
    fun insert_new_state_eq_tac interp_state_lhs_state_eq_thm
        {prems=[state_eq_thm, state_retrieval_eq_thm], context=ctxt,...} =
      update_state_state_retrieval_eqsq simp_tac ctxt
        state_eq_thm interp_state_lhs_state_eq_thm state_retrieval_eq_thm
      BIND (fn thm =>
        TU.insert_tac [thm] ctxt |> pure)
      |> flat2
    fun new_state_eq_tac ctxt cprems =
      state_eq_interp_lhs_state_eq_SIMPS_TO_thm_result_state_seq ctxt cprems
      BIND (fn (interp_state_lhs_state_eq_thm, cstate_eq_lhs_state, state_eq_prem_index) =>
        find_state_state_retrieval_eq_prop (Thm.term_of cstate_eq_lhs_state) cprems
        |> HTIU.seq_of_opt (fn () => @{log Logger.WARN} ctxt (fn () =>
            Pretty.block [
              Pretty.str "Could not find state retrieval premise for state ",
              Syntax.pretty_term ctxt (Thm.term_of cstate_eq_lhs_state),
              Pretty.str " in premises ",
              HTIU.pretty_cprems ctxt cprems
            ] |> Pretty.string_of))
      BIND (fn (state_retrieval_eq_prem_index, _) =>
        TU.focus_delete_prems_tac
          (HTIU.successors [state_eq_prem_index, state_retrieval_eq_prem_index])
          (insert_new_state_eq_tac interp_state_lhs_state_eq_thm) ctxt
        |> pure))
      |> flat2
  in TU.FOCUS_PARAMS_CTXT' (TU.CSUBGOAL_STRIPPED (fst o snd) o new_state_eq_tac) end

end
