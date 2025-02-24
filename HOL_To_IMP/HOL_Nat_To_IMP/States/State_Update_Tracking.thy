\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory State_Update_Tracking
  imports
    HOL_Nat_To_IMP_Base
    States_Base
begin

paragraph \<open>Summary\<close>
text \<open>Using @{type state}s to track sequential state updates.\<close>

definition "STATE s \<equiv> s"

text \<open>@{term STATE} is just a wrapper that contains a state.\<close>

lemma STATE_eq: "STATE s = s" unfolding STATE_def by simp

text \<open>Prevent simplification of arguments\<close>
lemma STATE_cong [cong]: "STATE s = STATE s" by simp

lemma STATE_interp_retrieve_key_eqI:
  assumes "PROP SIMPS_TO_UNIF (STATE (interp_state st) k) val'"
  and "val' = val"
  shows "(STATE (interp_state st)) k = val"
  using assms unfolding STATE_eq SIMPS_TO_UNIF_eq SIMPS_TO_eq by simp

lemma STATE_interp_update_eq_STATE_interp_fun_updI:
  assumes "PROP SIMPS_TO_UNIF val val'"
  and "PROP SIMPS_TO_UNIF (update_state k val' st) s'"
  shows "STATE (interp_state s') = (STATE (interp_state st))(k := val)"
  using assms unfolding SIMPS_TO_UNIF_eq
  by (simp flip: interp_update_state_eq add: STATE_eq)

lemma STATE_interp_state_state_eq: "STATE (interp_state (state s)) = s"
  unfolding STATE_eq interp_state_state_eq by simp

lemma STATE_interp_update_retrieve_key_eq_if: "(STATE (interp_state (update_state k v s))) k' =
  (if k = k' then v else (STATE (interp_state s)) k')"
  unfolding STATE_eq SIMPS_TO_UNIF_eq SIMPS_TO_eq interp_update_state_eq by simp

lemma string_eq_eq_True: "(s :: string) = s \<equiv> True" by simp

ML_file\<open>state_update_tracking.ML\<close>

end
