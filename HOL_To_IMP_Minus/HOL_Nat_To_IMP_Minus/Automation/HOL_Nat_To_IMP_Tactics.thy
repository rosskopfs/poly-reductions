\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_Nat_To_IMP_Tactics
  imports
    HOL_Nat_To_IMP_Minus_Goal_Commands
    ML_Unification.ML_Unifiers
    ML_Unification.Unify_Resolve_Tactics
begin

paragraph \<open>Summary\<close>
text \<open>Tactics and methods to refine HOL programs on natural numbers to IMP-Minus
via IMP with tailcalls.\<close>

lemma terminates_with_res_IMP_Tailcall_start:
  assumes "terminates_with_res_IMP_Tailcall tc c (STATE (interp_state (State s))) r val"
  shows "terminates_with_res_IMP_Tailcall tc c s r val"
  using assms unfolding STATE_interp_state_State_eq by simp

lemma terminates_with_res_tIf_processedI:
  assumes "s vb = v"
  and "PROP SIMPS_TO_UNIF (v \<noteq> 0) b1"
  and "PROP SIMPS_TO_UNIF (\<not>b1) b2"
  and "b1 \<Longrightarrow> terminates_with_res_IMP_Tailcall c c1 s r val"
  and "b2 \<Longrightarrow> terminates_with_res_IMP_Tailcall c c2 s r val"
  shows "terminates_with_res_IMP_Tailcall c (tIf vb c1 c2) s r val"
  using assms terminates_with_res_tIfI unfolding SIMPS_TO_UNIF_eq atomize_eq by auto

(*isolates the return value into a separate subgoal for rewriting*)
lemma rewrite_terminates_with_res_IMP_Tailcall_value:
  assumes "PROP SIMPS_TO_UNIF v v'"
  and "terminates_with_res_IMP_Tailcall tc c s r v'"
  shows "terminates_with_res_IMP_Tailcall tc c s r v"
  using assms unfolding SIMPS_TO_UNIF_eq by simp

lemma SIMPS_TO_UNIF_SIMPS_TO_UNIF_cong:
  assumes "PROP SIMPS_TO_UNIF f g"
  and "PROP SIMPS_TO_UNIF x y"
  shows "PROP SIMPS_TO_UNIF (f x) (g y)"
  using assms unfolding SIMPS_TO_UNIF_eq by simp

ML\<open>
  local val id = "hol_to_imp" in
  @{functor_instance struct_name = HOL_To_IMP_Unification_Combine
    and functor_name = Unification_Combine
    and id = \<open>id\<close>}
  @{functor_instance struct_name = HOL_To_IMP_Unification
    and functor_name = Mixed_Unification
    and id = \<open>id\<close>
    and more_args = \<open>structure UC = HOL_To_IMP_Unification_Combine\<close>}
  end
\<close>
local_setup \<open>HOL_To_IMP_Unification_Combine.setup_attribute NONE\<close>

lemma rewrite_Rel_nat_lhs:
  assumes "PROP SIMPS_TO_UNIF lhs lhs'"
  and "Rel_nat lhs' rhs"
  shows "Rel_nat lhs rhs"
  using assms unfolding SIMPS_TO_UNIF_eq by simp

lemma transfer_inst: "x = y \<Longrightarrow> y = y"
  by simp

ML_file \<open>hol_nat_to_imp_tactics_base.ML\<close>
ML_file \<open>hol_nat_to_imp_tailcalls_tactics.ML\<close>
ML_file \<open>hol_nat_to_imp_minus_tactics.ML\<close>

ML\<open>
  @{functor_instance struct_name = Standard_HOL_Nat_To_IMP_Minus_Tactics
    and functor_name = HOL_Nat_To_IMP_Minus_Tactics
    and id = \<open>""\<close>
    and more_args = \<open>val init_args = {
      get_IMP_def = SOME HOL_Nat_To_IMP_Tailcalls_Tactics.get_IMP_def,
      get_imp_minus_correct = SOME HOL_Nat_To_IMP_Tailcalls_Tactics.get_imp_minus_correct,
      get_HOL_eqs = SOME HOL_Nat_To_IMP_Tactics_Base.get_HOL_eqs,
      get_fun_inducts = SOME HOL_Nat_To_IMP_Tailcalls_Tactics.get_fun_inducts
    }\<close>}
\<close>
local_setup \<open>Standard_HOL_Nat_To_IMP_Minus_Tactics.setup_attribute NONE\<close>
local_setup \<open>Standard_HOL_Nat_To_IMP_Minus_Tactics.setup_method NONE\<close>
ML \<open>
  structure HB = HOL_Nat_To_IMP_Tactics_Base
  structure HT = HOL_Nat_To_IMP_Tailcalls_Tactics
  structure HM = HOL_Nat_To_IMP_Minus_Tactics_Base
  structure SUT = State_Update_Tracking
\<close>


end
