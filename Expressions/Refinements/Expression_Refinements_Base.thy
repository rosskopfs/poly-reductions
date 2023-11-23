\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expression_Refinements_Base
  imports
    Expressions_Base
begin

type_synonym ('i, 'o) refine_fn = "'i \<Rightarrow> 'o"

text \<open>AKA. antimonotone functions wrt. P\<close>
definition "refines_wrt_pred_fun P f \<equiv> \<forall>x. P (f x) x"

lemma refines_wrt_pred_funI[intro]:
  assumes "\<And>x. P (f x) x"
  shows "refines_wrt_pred_fun P f"
  using assms unfolding refines_wrt_pred_fun_def by auto

lemma refines_wrt_pred_funE[elim]:
  assumes "refines_wrt_pred_fun P f"
  obtains "P (f x) x"
  using assms unfolding refines_wrt_pred_fun_def by auto

definition "refines_wrt_eval eval1 eval2 e1 e2 \<equiv>
  \<forall>s t sf v. eval1 e1 s t sf v \<longrightarrow> (\<exists>t' sf'. eval2 e2 s t' sf' v)"

lemma refines_wrt_evalI:
  assumes "\<And>s t sf v. eval1 e1 s t sf v \<Longrightarrow> \<exists>t' sf'. eval2 e2 s t' sf' v"
  shows "refines_wrt_eval eval1 eval2 e1 e2"
  using assms unfolding refines_wrt_eval_def by auto

lemma refines_wrt_evalE:
  assumes "refines_wrt_eval eval1 eval2 e1 e2"
  and "eval1 e1 s t sf v"
  obtains t' sf' where "eval2 e2 s t' sf' v"
  using assms unfolding refines_wrt_eval_def by blast

definition "refines_wrt_eval_fun eval1 eval2 \<equiv> refines_wrt_pred_fun (refines_wrt_eval eval1 eval2)"

lemma refines_wrt_eval_funI:
  assumes "\<And>e. refines_wrt_eval eval1 eval2 (f e) e"
  shows "refines_wrt_eval_fun eval1 eval2 f"
  using assms unfolding refines_wrt_eval_fun_def by blast

lemma refines_wrt_eval_funE:
  assumes "refines_wrt_eval_fun eval1 eval2 f"
  obtains "refines_wrt_eval eval1 eval2 (f e) e"
  using assms unfolding refines_wrt_eval_fun_def by blast


end
