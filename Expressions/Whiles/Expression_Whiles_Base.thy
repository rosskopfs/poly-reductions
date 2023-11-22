\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expression_Whiles_Base
  imports Expressions_Base
begin

datatype ('eb, 'ewc, 'ew) exp_while_base =
  EWBase 'eb
| While 'ewc 'ew

context
  fixes eval_eb :: "('t :: {one,plus}, 'r, 'si, 'sv, 'eb) eval_time"
  and eval_ewc :: "('t, bool, 'si, 'sv, 'ewc) eval_time"
  and eval_ew :: "('t, 'r, 'si, 'sv, 'ew) eval_time"
  and r_while :: "'r"
begin

inductive eval_exp_while_base ::
  "('t, 'r, 'si, 'sv, ('eb, 'ewc, 'ew) exp_while_base) eval_time"
where
  eval_exp_while_base_EWBase[intro]: "eval_eb e s t s' v \<Longrightarrow>
    eval_exp_while_base (EWBase e) s t s' v"
| eval_exp_while_base_While_true: "eval_ewc ewc s1 t1 sc b \<Longrightarrow> b \<Longrightarrow>
    eval_ew ew sc t2 s2 vew \<Longrightarrow> eval_exp_while_base (While ewc ew) s2 t3 s3 v3 \<Longrightarrow>
    eval_exp_while_base (While ewc ew) s1 (t1 + 1 + t2 + t3) s3 v3"
| eval_exp_while_base_While_false: "eval_ewc ewc s t sc b \<Longrightarrow> \<not>b \<Longrightarrow>
    eval_exp_while_base (While ewc ew) s (t + 1) s r_while"

inductive_cases eval_exp_while_base_EWBaseE[elim]:
  "eval_exp_while_base (EWBase e) s t s' v"
inductive_cases eval_exp_while_base_WhileE[elim]:
  "eval_exp_while_base (While ewc ew) s t s' v"

lemma eval_exp_while_base_While_trueI[intro]:
  assumes "eval_ewc ewc s1 t1 sc b" "b"
  and "eval_ew ew sc t2 s2 vew" "eval_exp_while_base (While ewc ew) s2 t3 s3 v3"
  and "t = t1 + 1 + t2 + t3"
  shows "eval_exp_while_base (While ewc ew) s1 t s3 v3"
  using assms eval_exp_while_base.intros by auto

lemma eval_exp_while_base_While_falseI[intro]:
  assumes "eval_ewc ewc s t' sc b" "\<not>b"
  and "t = t' + 1"
  and "s = s'"
  and "v = r_while"
  shows "eval_exp_while_base (While ewc ew) s t s' v"
  using assms eval_exp_while_base.intros by auto

end

lemma eval_exp_while_base_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  and "\<And>e s t s' v. f2 e s t s' v \<longrightarrow> g2 e s t s' v"
  and "\<And>e s t s' v. f3 e s t s' v \<longrightarrow> g3 e s t s' v"
  shows "eval_exp_while_base f1 f2 f3 r_while e s t s' v \<longrightarrow> eval_exp_while_base g1 g2 g3 r_while e s t s' v"
proof
  assume "eval_exp_while_base f1 f2 f3 r_while e s t s' v"
  from this assms show "eval_exp_while_base g1 g2 g3 r_while e s t s' v"
    by (induction rule: eval_exp_while_base.induct; auto;
    metis eval_exp_while_base_While_true eval_exp_while_base_While_false)
qed


end