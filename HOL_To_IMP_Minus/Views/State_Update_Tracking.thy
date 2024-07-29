\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory State_Update_Tracking
  imports
    Views_Base
    ML_Unification.Simps_To
    HOL_To_IMP_Base
begin

lemma interp_state_State_eq: "interp_state (State s) = s"
  unfolding interp_state_def by simp

paragraph \<open>Summary\<close>
text \<open>Using @{type state}s to track sequential state updates. More precisely,
we will keep track of an equality that relates intermediate states
to the initial state. This tracking happens in a protected premise, which we set up next.\<close>

definition "STATE s \<equiv> s"

text \<open>@{term STATE} is just a wrapper that contains a state.\<close>

lemma STATE_eq: "STATE s = s" unfolding STATE_def by simp

text \<open>Prevent simplification of arguments\<close>
lemma STATE_cong [cong]: "STATE s = STATE s" by simp

text \<open>In the beginning, we simply know that the state is equal to itself.\<close>

lemma STATE_start: "STATE (interp_state st) = STATE (interp_state st)" by simp

text \<open>The following is used to rewrite state retrievals according to a tracked
state equality.\<close>

lemma state_state_app_eqI:
  assumes "interp_state st = interp_state st'"
  and "interp_state st = s"
  and "interp_state st' k = val"
  shows "s k = val"
  using assms by simp

lemma STATE_state_app_eqI:
  assumes "STATE (interp_state st) = STATE (interp_state st')"
  and "PROP SIMPS_TO (interp_state st) s"
  and "PROP SIMPS_TO (interp_state st' k) val"
  shows "s k = val"
  using assms unfolding STATE_eq SIMPS_TO_eq atomize_eq
  by (fact state_state_app_eqI)

text \<open>The following is used to update a state equality according to a new
retrieval condition.\<close>

lemma update_state_state_app_eq:
  assumes "interp_state st = interp_state st'"
  and "interp_state st = s"
  and "s k = val" \<comment>\<open>the new retrieval condition\<close>
  and "val = val'"
  shows "interp_state st = interp_state (update_state st' k val')"
  using assms by auto

lemma update_STATE_state_app_eq:
  assumes "STATE (interp_state st) = STATE (interp_state st')"
  and  "PROP SIMPS_TO (interp_state st) s"
  and "s k = val"
  and "PROP SIMPS_TO val val'"
  shows "STATE (interp_state st) = STATE (interp_state (update_state st' k val'))"
  using assms unfolding STATE_eq SIMPS_TO_eq atomize_eq
  by (fact update_state_state_app_eq)

text \<open>The following is used to update a state equality according to a new
update condition.\<close>

lemma update_state_state_eq_update:
  assumes "interp_state st = interp_state st'"
  and "interp_state st = s"
  and "s' = s(k := val)" \<comment>\<open>the update condition\<close>
  and "val = val'"
  shows "interp_state (State s') = interp_state (update_state st' k val')"
  using assms by (simp add: interp_state_State_eq)

lemma update_STATE_state_eq_update:
  assumes "STATE (interp_state st) = STATE (interp_state st')"
  and  "PROP SIMPS_TO (interp_state st) s"
  and "s' = s(k := val)"
  and "PROP SIMPS_TO val val'"
  shows "STATE (interp_state (State s')) = STATE (interp_state (update_state st' k val'))"
  using assms unfolding STATE_eq SIMPS_TO_eq atomize_eq
  by (fact update_state_state_eq_update)

ML_file\<open>state_update_tracking.ML\<close>

(*TODO:
1. the framework currently only collects a big state equality without
simplifying it. As a result, every state retrieval needs to simplify
a (complex) series of update operations.
We could instead simplify the states themselves to speed up the proofs.
*)

(* TODO: where do these belong? *)

lemma STATE_interp_update_eq_STATE_interp_fun_updI:
  assumes "PROP SIMPS_TO_UNIF val val'"
  shows "STATE (interp_state (update_state st k val')) = (STATE (interp_state st))(k := val)"
  using assms unfolding STATE_eq SIMPS_TO_UNIF_eq by (simp add: interp_state_State_eq)

lemma STATE_interp_retrieve_key_eqI:
  assumes "PROP SIMPS_TO_UNIF (interp_state st) s"
  and "s k = val"
  shows "(STATE (interp_state st)) k = val"
  using assms unfolding STATE_eq SIMPS_TO_UNIF_eq SIMPS_TO_eq by simp

end
