(*  Title:  States/state_update_tracking.ML
    Author: Kevin Kappelmann

Tracking of STATE equalities.
*)
signature STATE_UPDATE_TRACKING =
sig
include HAS_LOGGER

val dest_STATE : term -> term
val cdest_STATE : cterm -> cterm

(*state retrieval utils*)
val mk_state_retrieval : term -> term -> term
val dest_state_retrieval : term -> term * term
val is_state_state_retrieval : term -> term -> bool

val STATE_interp_retrieve_key_eq_tac : (int -> tactic) -> Proof.context -> int -> tactic
val subst_STATE_interp_retrieve_key_tac : Proof.context -> int -> tactic
val subst_all_STATE_interp_retrieve_key_tac : Proof.context -> int -> tactic

val STATE_interp_update_eq_STATE_interp_fun_upd : (int -> tactic) -> Proof.context -> int -> tactic

end

structure State_Update_Tracking : STATE_UPDATE_TRACKING =
struct
structure HTIU = HOL_Nat_To_IMP_Util
val logger = Logger.setup_new_logger Logger.root "State_Update_Tracking"

val state_eq = curry (op aconv)

(* state equality utils *)
val dest_STATE = \<^Const_fn>\<open>STATE _ for s => s\<close>
val cdest_STATE = Thm.dest_arg

(* state retrieval utils *)
fun mk_state_retrieval state key = state $ key
val dest_state_retrieval = Term.dest_comb
fun is_state_state_retrieval state s_app = dest_state_retrieval s_app |> fst |> state_eq state

(* interpretation of state *)
val interp_reflect_thm = @{thm STATE_interp_state_State_eq}

fun SIMPS_TO_UNIF_STATE_interp_retrieve_key_tac ctxt = HTIU.SIMPS_TO_UNIF_refl_tac
  (safe_simp_tac (ctxt addsimps @{thm STATE_interp_update_retrieve_key_eq_if} :: [interp_reflect_thm]))
  ctxt

fun STATE_interp_retrieve_key_eq_tac finish_eq_tac ctxt =
  resolve_tac ctxt [@{thm STATE_interp_retrieve_key_eqI}]
  THEN' SIMPS_TO_UNIF_STATE_interp_retrieve_key_tac ctxt
  THEN' finish_eq_tac

fun subst_STATE_interp_retrieve_key_tac ctxt =
  HTIU.subst_first_tac ctxt [@{thm STATE_interp_retrieve_key_eqI}]
  THEN' SIMPS_TO_UNIF_STATE_interp_retrieve_key_tac ctxt
  THEN' HTIU.refl_tac ctxt

val subst_all_STATE_interp_retrieve_key_tac = REPEAT oo subst_STATE_interp_retrieve_key_tac

fun STATE_interp_update_eq_STATE_interp_fun_upd simp_tac ctxt =
  resolve_tac ctxt [@{thm STATE_interp_update_eq_STATE_interp_fun_updI}]
  THEN' HTIU.SIMPS_TO_UNIF_refl_tac simp_tac ctxt

end
