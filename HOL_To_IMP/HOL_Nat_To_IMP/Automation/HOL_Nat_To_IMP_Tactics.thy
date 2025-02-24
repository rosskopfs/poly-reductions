\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_Nat_To_IMP_Tactics
  imports
    HOL_Nat_To_IMP_Goal_Commands
    HOL_To_HOL_Nat.HOL_To_HOL_Nat_Basics
    ML_Unification.ML_Unifiers
    ML_Unification.Unify_Resolve_Tactics
begin

paragraph \<open>Summary\<close>
text \<open>Tactics and methods to refine HOL programs on natural numbers to IMP (with while loops)
via IMP with tailcalls.\<close>

lemma terminates_with_res_IMP_Tailcall_start:
  assumes "terminates_with_res_IMP_Tailcall tc c (STATE (interp_state (state s))) r val"
  shows "terminates_with_res_IMP_Tailcall tc c s r val"
  using assms unfolding STATE_eq interp_state_state_eq by simp

lemma terminates_with_res_tIf_processedI:
  assumes "PROP SIMPS_TO_UNIF (s vb) v"
  and "PROP SIMPS_TO_UNIF (v \<noteq> False_nat) b"
  and "b \<Longrightarrow> v \<noteq> False_nat \<Longrightarrow> terminates_with_res_IMP_Tailcall c c1 s r val"
  and "\<not>b \<Longrightarrow> v = False_nat \<Longrightarrow> terminates_with_res_IMP_Tailcall c c2 s r val"
  shows "terminates_with_res_IMP_Tailcall c (tIf vb c1 c2) s r val"
  using assms terminates_with_res_tIfI unfolding SIMPS_TO_UNIF_eq atomize_eq False_nat_eq_zero by auto

(*rewriting of an if condition*)
lemma rewrite_ne_False_nat_if_Rel_nat:
  assumes "Rel_nat n b"
  shows "(n \<noteq> False_nat) = b"
  using assms Rel_nat_bool_iff False_nat_eq_zero True_nat_neq_zero
  unfolding SIMPS_TO_UNIF_eq atomize_eq by fastforce

lemma rewrite_Rel_nat_lhs:
  assumes "PROP SIMPS_TO_UNIF lhs lhs'"
  and "Rel_nat lhs' rhs"
  shows "Rel_nat lhs rhs"
  using assms unfolding SIMPS_TO_UNIF_eq by simp

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

definition "rel_fun_app_close x y \<equiv> x = y"

lemma rel_fun_app_closeI: "rel_fun_app_close x x"
  unfolding rel_fun_app_close_def by simp

lemma rel_fun_appI:
  assumes "(R ===> S) f g"
  and "R x y"
  and "rel_fun_app_close gy (g y)"
  shows "S (f x) gy"
  using rel_funD assms unfolding rel_fun_app_close_def by auto

lemma Rel_nat_fst_nat_app_if_Rel_nat_eqI:
  assumes "Rel_nat x y"
  and "(Rel_nat ===> (=)) fst_nat f"
  and "rel_fun_app_close fy (f y)"
  shows "Rel_nat (fst_nat x) fy"
  using assms Rel_nat_nat_eq_eq unfolding rel_fun_app_close_def by (auto dest: rel_funD)

named_theorems HOL_To_IMP_finish_simps
  "equations used to prove the equality of the results computed by the IMP-program
  and the HOL term as well as to close contradictory branches"

declare HOL_To_HOL_Nat.If_nat_def[HOL_To_IMP_finish_simps]

ML_file \<open>hol_nat_to_imp_tactics_gen.ML\<close>

lemma SIMPS_TO_if_TrueI:
  assumes "b"
  and "PROP SIMPS_TO x z"
  shows "PROP SIMPS_TO (if b then x else y) z"
  using assms unfolding SIMPS_TO_eq by simp

lemma SIMPS_TO_if_FalseI:
  assumes "\<not>b"
  and "PROP SIMPS_TO y z"
  shows "PROP SIMPS_TO (if b then x else y) z"
  using assms unfolding SIMPS_TO_eq by simp

ML_file \<open>hol_nat_to_imp_tailcalls_tactics.ML\<close>

context includes tcom_syntax
begin
fun vars_tcom_no_calls :: "tcom \<Rightarrow> vname \<Rightarrow> bool" where
"vars_tcom_no_calls (x ::= _) x' = (x = x')" |
"vars_tcom_no_calls (_ ;; c2) x = vars_tcom_no_calls c2 x" |
"vars_tcom_no_calls (IF _\<noteq>0 THEN c1 ELSE c2) x = (vars_tcom_no_calls c1 x \<or> vars_tcom_no_calls c2 x)" |
"vars_tcom_no_calls _ _ = False"
end

lemma mem_set_vars_if_vars_tcom_no_calls: "vars_tcom_no_calls c x \<Longrightarrow> x \<in> set (vars c)"
  by (induction c) auto

ML_file \<open>hol_nat_to_imp_tactics.ML\<close>

declaration (in HOL_Nat_To_IMP)
  \<open>K HOL_Nat_To_IMP_Tailcalls_Tactics.add_SIMPS_TO_if_assumption_loop\<close>

ML\<open>
  @{functor_instance struct_name = Standard_HOL_Nat_To_IMP_Tactics
    and functor_name = HOL_Nat_To_IMP_Tactics
    and id = \<open>""\<close>
    and more_args = \<open>val init_args = {
      get_IMP_def = SOME HOL_Nat_To_IMP_Tailcalls_Tactics.get_IMP_def,
      get_imp_correct = SOME HOL_Nat_To_IMP_Tailcalls_Tactics.get_imp_correct,
      get_HOL_eqs = SOME HOL_Nat_To_IMP_Tactics_Gen.get_HOL_eqs,
      get_fun_inducts = SOME HOL_Nat_To_IMP_Tailcalls_Tactics.get_fun_inducts
    }\<close>}
\<close>
local_setup \<open>Standard_HOL_Nat_To_IMP_Tactics.setup_attribute NONE\<close>
local_setup \<open>Standard_HOL_Nat_To_IMP_Tactics.setup_method NONE\<close>
ML \<open>
  structure HG = HOL_Nat_To_IMP_Tactics_Gen
  structure HT = HOL_Nat_To_IMP_Tailcalls_Tactics
  structure HM = HOL_Nat_To_IMP_Tactics_Base
  structure SUT = State_Update_Tracking
\<close>

end
