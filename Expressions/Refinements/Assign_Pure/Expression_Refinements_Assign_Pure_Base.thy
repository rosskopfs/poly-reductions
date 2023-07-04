\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expression_Refinements_Assign_Pure_Base
  imports
    Expression_Refinements_Base
begin

text \<open>TODO: add more\<close>
definition "refines_assign_pure eval_assign_impure_state eval_assign_pure_state e_impure e_pure \<equiv>
  refines_wrt_eval eval_assign_impure_state eval_assign_pure_state e_impure e_pure"

lemma refines_assign_pureI:
  assumes "\<And>s t sf v. eval_assign_impure_state e_impure s t sf v \<Longrightarrow>
    \<exists>t' sf'. eval_assign_pure_state e_pure s t' sf' v"
  shows "refines_assign_pure eval_assign_impure_state eval_assign_pure_state e_impure e_pure"
  using assms unfolding refines_assign_pure_def by (auto intro: refines_wrt_evalI)

lemma refines_assign_pureE:
  assumes "refines_assign_pure eval_assign_impure_state eval_assign_pure_state e_impure e_pure"
  and "eval_assign_impure_state e_impure s t sf v"
  obtains t' sf' where "eval_assign_pure_state e_pure s t' sf' v"
  using assms unfolding refines_assign_pure_def by (blast elim: refines_wrt_evalE)

definition "refines_assign_pure_fun eval_assign_impure_state eval_assign_pure_state \<equiv>
  refines_wrt_pred_fun (refines_assign_pure eval_assign_impure_state eval_assign_pure_state)"

lemma refines_assign_pure_funI:
  assumes "\<And>e. refines_assign_pure eval_assign_impure_state eval_assign_pure_state (f e) e"
  shows "refines_assign_pure_fun eval_assign_impure_state eval_assign_pure_state f"
  using assms unfolding refines_assign_pure_fun_def by blast

lemma refines_assign_pure_funE:
  assumes "refines_assign_pure_fun eval_assign_impure_state eval_assign_pure_state f"
  and "eval_assign_impure_state (f e_pure) s t sf v"
  obtains t' sf' where "eval_assign_pure_state e_pure s t' sf' v"
  using assms unfolding refines_assign_pure_fun_def by (blast elim: refines_assign_pureE)


end
