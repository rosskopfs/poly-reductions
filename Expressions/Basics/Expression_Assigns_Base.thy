\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expression_Assigns_Base
  imports Expressions_Base
begin

datatype ('si, 'eb, 'ea) exp_assign_base =
  EABase 'eb
| Assign 'si 'ea

context
  fixes eval_eb :: "('t :: {one, plus}, 'sv, 'si, 'sv, 'eb) eval_time"
  and eval_ea :: "('t, 'sv, 'si, 'sv, 'ea) eval_time"
begin

inductive eval_exp_assign_base ::
  "('t, 'sv, 'si, 'sv, ('si, 'eb, 'ea) exp_assign_base) eval_time"
where
  eval_exp_assign_base_EABase[intro]: "eval_eb eb s t s' v \<Longrightarrow>
    eval_exp_assign_base (EABase eb) s t s' v"
| eval_exp_assign_base_Assign: "eval_ea ea s t s' v \<Longrightarrow>
    eval_exp_assign_base (Assign si ea) s (t + 1) (s'(si := v)) v"

inductive_cases eval_exp_assign_base_EABaseE[elim]:
  "eval_exp_assign_base (EABase eb) s t s' v"
inductive_cases eval_exp_assign_base_AssignE[elim]:
  "eval_exp_assign_base (Assign si ea) s t s' v"

lemma eval_exp_assign_base_AssignI[intro]:
  assumes "eval_ea ea s t' sea v'"
  and "s' = sea(si := v)"
  and "v = v'"
  and "t = t' + 1"
  shows "eval_exp_assign_base (Assign si ea) s t s' v"
  using assms eval_exp_assign_base.intros by auto

end

lemma eval_exp_assign_base_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  and "\<And>e s t s' v. f2 e s t s' v \<longrightarrow> g2 e s t s' v"
  shows "eval_exp_assign_base f1 f2 e s t s' v \<longrightarrow> eval_exp_assign_base g1 g2 e s t s' v"
proof
  assume "eval_exp_assign_base f1 f2 e s t s' v"
  from this assms show "eval_exp_assign_base g1 g2 e s t s' v"
    by (induction rule: eval_exp_assign_base.induct) fast+
qed


end