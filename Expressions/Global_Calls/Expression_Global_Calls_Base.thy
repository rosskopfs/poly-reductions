\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expression_Global_Calls_Base
  imports Expressions_Base
begin

datatype 'eb exp_global_call_base =
  EGCBase 'eb
| Global_Call

context
  fixes eval_eb :: "('t, 'r, 'si, 'sv, 'eb) eval_time"
  and eval_gc :: "('t, 'r, 'si, 'sv, 'gc) eval_time"
  and gc :: "'gc"
begin

inductive eval_exp_global_call_base ::
  "('t, 'r, 'si, 'sv, 'eb exp_global_call_base) eval_time"
where
  eval_exp_global_call_base_EGCBase[intro]: "eval_eb e s t s' r \<Longrightarrow>
    eval_exp_global_call_base (EGCBase e) s t s' r"
| eval_exp_global_call_base_Global_Call[intro]: "eval_gc gc s t s' r \<Longrightarrow>
    eval_exp_global_call_base Global_Call s t s' r"

inductive_cases eval_exp_global_call_base_ERCBase[elim]:
  "eval_exp_global_call_base (EGCBase e) s t s' r"
inductive_cases eval_exp_global_call_base_Global_CallE[elim]:
  "eval_exp_global_call_base Global_Call s t s' r"

end

lemma eval_exp_global_call_base_mono[mono]:
  assumes "\<And>e s t s' r. f1 e s t s' r \<longrightarrow> g1 e s t s' r"
  and "\<And>e s t s' r. f2 e s t s' r \<longrightarrow> g2 e s t s' r"
  shows "eval_exp_global_call_base f1 f2 gc e s t s' r \<longrightarrow> eval_exp_global_call_base g1 g2 gc e s t s' r"
  using assms by (induction e) blast+


end