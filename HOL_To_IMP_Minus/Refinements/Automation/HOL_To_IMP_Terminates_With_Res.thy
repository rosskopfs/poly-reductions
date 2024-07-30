\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Terminates_With_Res
  imports
    IMP_Terminates_With
    State_Update_Tracking
    ML_Unification.Simps_To
begin

lemma terminates_with_res_IMP_Tailcall_start:
  assumes "terminates_with_res_IMP_Tailcall tc c (STATE (interp_state (State s))) r val"
  shows "terminates_with_res_IMP_Tailcall tc c s r val"
  using assms unfolding STATE_eq interp_state_State_eq by simp

(* todo: no simps_to_unif, remove *)
lemma terminates_with_res_tIf_processedI:
  assumes "s vb = v"
  and "PROP SIMPS_TO_UNIF (v \<noteq> 0) b1"
  and "PROP SIMPS_TO_UNIF (v = 0) b2"
  and "b1 \<Longrightarrow> terminates_with_res_IMP_Tailcall c c1 s r val"
  and "b2 \<Longrightarrow> terminates_with_res_IMP_Tailcall c c2 s r val"
  shows "terminates_with_res_IMP_Tailcall c (tIf vb c1 c2) s r val"
  using assms terminates_with_res_tIfI unfolding SIMPS_TO_UNIF_eq atomize_eq by auto

lemma terminates_with_res_tIf_processedI_2:
  assumes "PROP SIMPS_TO_UNIF (s vb) v"
  and "PROP SIMPS_TO_UNIF (v \<noteq> 0) b1"
  and "PROP SIMPS_TO_UNIF (v = 0) b2"
  and "b1 \<Longrightarrow> terminates_with_res_IMP_Tailcall c c1 s r val"
  and "b2 \<Longrightarrow> terminates_with_res_IMP_Tailcall c c2 s r val"
  shows "terminates_with_res_IMP_Tailcall c (tIf vb c1 c2) s r val"
  using assms terminates_with_res_tIfI unfolding SIMPS_TO_UNIF_eq atomize_eq by auto

lemma STATE_interp_update_eq_STATE_interp_fun_updI:
  assumes "PROP SIMPS_TO_UNIF val val'"
  shows "STATE (interp_state (update_state st k val')) = (STATE (interp_state st))(k := val)"
  using assms unfolding STATE_eq SIMPS_TO_UNIF_eq by (simp add: interp_state_State_eq)

lemma STATE_interp_retrieve_key_eqI:
  assumes "PROP SIMPS_TO_UNIF (interp_state st) s"
  and "s k = val"
  shows "(STATE (interp_state st)) k = val"
  using assms unfolding STATE_eq SIMPS_TO_UNIF_eq SIMPS_TO_eq by simp

lemma STATE_interp_retrieve_key_eqI_2:
  assumes "PROP SIMPS_TO_UNIF ((STATE (interp_state st)) k) val"
  shows "(STATE (interp_state st)) k = val"
  using assms unfolding STATE_eq SIMPS_TO_UNIF_eq SIMPS_TO_eq by simp

method SIMPS_TO uses simp =
  (simp add: simp)?,
  rule SIMPS_TOI

method SIMPS_TO_UNIF =
  rule SIMPS_TO_UNIFI,
    (SIMPS_TO simp: STATE_eq interp_state_State_eq)?,
    rule reflexive

method STATE_interp_update_eq_STATE_interp_fun_upd =
  rule STATE_interp_update_eq_STATE_interp_fun_updI,
  SIMPS_TO_UNIF

method STATE_interp_retrieve_key_eq =
  rule STATE_interp_retrieve_key_eqI,
  SIMPS_TO_UNIF,
  (simp add: STATE_eq interp_state_State_eq)

method terminates_with_res_IMP_Minus_start_base uses tailcall_def =
  rule terminates_with_res_IMP_Minus_if_terminates_with_res_IMP_TailcallI,
    subst tailcall_def,
    simp,
    subst tailcall_def,
    simp

method terminates_with_res_IMP_Minus_start uses tailcall_def =
  (terminates_with_res_IMP_Minus_start_base tailcall_def: tailcall_def),
  subst (2) tailcall_def,
  rule terminates_with_res_IMP_Tailcall_start

method terminates_with_res_tSeq =
  rule terminates_with_res_tSeqI

method terminates_with_res_tAssign =
  rule terminates_with_res_tAssignI,
  STATE_interp_update_eq_STATE_interp_fun_upd

method terminates_with_res_tIf =
  rule terminates_with_res_tIf_processedI,
  STATE_interp_retrieve_key_eq,
  SIMPS_TO_UNIF,
  SIMPS_TO_UNIF

method terminates_with_res_tTail =
  rule terminates_with_res_tTailI
  (*TODO: apply induction and finish*)

method terminates_with_tAssign =
  rule terminates_with_tAssignI,
  STATE_interp_update_eq_STATE_interp_fun_upd

method terminates_with_tCall uses correctness =
  rule terminates_with_tCallI,
  rule correctness,
  STATE_interp_update_eq_STATE_interp_fun_upd

method terminates_with_res_step uses correctness =
  (terminates_with_res_tSeq,
    (terminates_with_tAssign
    | terminates_with_tCall correctness: correctness)(* ? *))
  | terminates_with_res_tAssign
  | terminates_with_res_tIf

method terminates_with_res_IMP_Minus uses tailcall_def correctness =
  terminates_with_res_IMP_Minus_start tailcall_def: tailcall_def,
  ((terminates_with_res_step correctness: correctness)+,
  STATE_interp_retrieve_key_eq?)+

end