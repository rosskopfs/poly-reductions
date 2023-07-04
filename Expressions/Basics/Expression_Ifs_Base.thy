\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expression_Ifs_Base
  imports Expressions_Base
begin

datatype ('eb, 'eic, 'eit, 'eif) exp_if_base =
  EIBase 'eb
| If 'eic 'eit 'eif

context
  fixes eval_eb :: "('t :: {one, plus}, 'r, 'si, 'r, 'eb) eval_time"
  and eval_eic :: "('t, bool, 'si, 'r, 'eic) eval_time"
  and eval_eit :: "('t, 'r, 'si, 'r, 'eit) eval_time"
  and eval_eif :: "('t, 'r, 'si, 'r, 'eif) eval_time"
begin

inductive eval_exp_if_base ::
  "('t, 'r, 'si, 'r, ('eb, 'eic, 'eit, 'eif) exp_if_base) eval_time"
where
  eval_exp_if_base_EIBase[intro]: "eval_eb eb s t s' r \<Longrightarrow>
    eval_exp_if_base (EIBase eb) s t s' r"
| eval_exp_if_base_If_true: "eval_eic eic s t1 sc b \<Longrightarrow> b \<Longrightarrow>
    eval_eit eit sc t2 s' r \<Longrightarrow> eval_exp_if_base (If eic eit eif) s (t1 + 1 + t2) s' r"
| eval_exp_if_base_If_false: "eval_eic eic s t1 sc b \<Longrightarrow> \<not>b \<Longrightarrow>
    eval_eif eif sc t2 s' r \<Longrightarrow> eval_exp_if_base (If eic eit eif) s (t1 + 1 + t2) s' r"

inductive_cases eval_exp_if_base_EIBaseE[elim]:
  "eval_exp_if_base (EIBase eb) s t s' r"
inductive_cases eval_exp_if_base_IfE[elim]:
  "eval_exp_if_base (If eic eit eif) s t s' r"

lemma eval_exp_if_base_If_trueI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "b"
  and "eval_eit eit sc t2 s' r"
  and "t = t1 + 1 + t2"
  shows "eval_exp_if_base (If eic eit eif) s t s' r"
  using assms eval_exp_if_base.intros by auto

lemma eval_exp_if_base_If_falseI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "\<not>b"
  and "eval_eif eif sc t2 s' r"
  and "t = t1 + 1 + t2"
  shows "eval_exp_if_base (If eic eit eif) s t s' r"
  using assms eval_exp_if_base.intros by auto

end

lemma eval_exp_if_base_mono[mono]:
  assumes "\<And>e s t s' r. f1 e s t s' r \<longrightarrow> g1 e s t s' r"
  and "\<And>e s t s' r. f2 e s t s' r \<longrightarrow> g2 e s t s' r"
  and "\<And>e s t s' r. f3 e s t s' r \<longrightarrow> g3 e s t s' r"
  and "\<And>e s t s' r. f4 e s t s' r \<longrightarrow> g4 e s t s' r"
  shows "eval_exp_if_base f1 f2 f3 f4 e s t s' r \<longrightarrow> eval_exp_if_base g1 g2 g3 g4 e s t s' r"
proof
  assume "eval_exp_if_base f1 f2 f3 f4 e s t s' r"
  from this assms show "eval_exp_if_base g1 g2 g3 g4 e s t s' r"
    by (induction rule: eval_exp_if_base.induct) fast+
qed


type_synonym ('eb, 'eic, 'e) exp_if_base_hom = "('eb, 'eic, 'e, 'e) exp_if_base"

context
  fixes eval_eb :: "('t :: {one, plus}, 'r, 'si, 'r, 'eb) eval_time"
  and eval_eic :: "('t, bool, 'si, 'r, 'eic) eval_time"
  fixes eval_e :: "('t, 'r, 'si, 'r, 'e) eval_time"
begin

definition "eval_exp_if_base_hom \<equiv> eval_exp_if_base eval_eb eval_eic eval_e eval_e"

lemma eval_exp_if_base_hom_EIBaseI[intro]:
  assumes "eval_eb eb s t s' r"
  shows "eval_exp_if_base_hom (EIBase eb) s t s' r"
  using assms unfolding eval_exp_if_base_hom_def by auto

lemma eval_exp_if_base_hom_EIBaseE[elim]:
  assumes "eval_exp_if_base_hom (EIBase eb) s t s' r"
  obtains "eval_eb eb s t s' r"
  using assms unfolding eval_exp_if_base_hom_def by auto

lemma eval_exp_if_base_hom_If_trueI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "b"
  and "eval_e eit sc t2 s' r"
  and "t = t1 + 1 + t2"
  shows "eval_exp_if_base_hom (If eic eit eif) s t s' r"
  using assms unfolding eval_exp_if_base_hom_def by auto

lemma eval_exp_if_base_hom_If_falseI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "\<not>b"
  and "eval_e eif sc t2 s' r"
  and "t = t1 + 1 + t2"
  shows "eval_exp_if_base_hom (If eic eit eif) s t s' r"
  using assms unfolding eval_exp_if_base_hom_def by auto

lemma eval_exp_if_base_hom_IfE[elim]:
  assumes "eval_exp_if_base_hom (If eic eit eif) s t s' r"
  obtains sc b t1 t2 where "eval_eic eic s t1 sc b" "b" "eval_e eit sc t2 s' r" "t = t1 + 1 + t2"
    | sc b t1 t2 where "eval_eic eic s t1 sc b" "\<not>b" "eval_e eif sc t2 s' r" "t = t1 + 1 + t2"
  using assms unfolding eval_exp_if_base_hom_def by blast

lemma eval_exp_if_base_hom_induct[induct pred : eval_exp_if_base_hom,
  case_names EIBase If_true If_false]:
  assumes "eval_exp_if_base_hom e s t s' r"
  and "\<And>eb s t s' r. eval_eb eb s t s' r \<Longrightarrow> P (EIBase eb) s t s' r"
  and "\<And>eic s t1 sc b eit t2 s' r eif. eval_eic eic s t1 sc b \<Longrightarrow> b \<Longrightarrow> eval_e eit sc t2 s' r \<Longrightarrow>
    P (If eic eit eif) s (t1 + 1 + t2) s' r"
  and "\<And>eic s t1 sc b eif t2 s' r eit. eval_eic eic s t1 sc b \<Longrightarrow> \<not>b \<Longrightarrow> eval_e eif sc t2 s' r \<Longrightarrow>
    P (If eic eit eif) s (t1 + 1 + t2) s' r"
  shows "P e s t s' r"
  using assms unfolding eval_exp_if_base_hom_def by (rule eval_exp_if_base.induct)

end

lemma eval_exp_if_base_hom_mono[mono]:
  assumes "\<And>e s t s' r. f1 e s t s' r \<longrightarrow> g1 e s t s' r"
  and "\<And>e s t s' r. f2 e s t s' r \<longrightarrow> g2 e s t s' r"
  and "\<And>e s t s' r. f3 e s t s' r \<longrightarrow> g3 e s t s' r"
  shows "eval_exp_if_base_hom f1 f2 f3 e s t s' r \<longrightarrow> eval_exp_if_base_hom g1 g2 g3 e s t s' r"
  unfolding eval_exp_if_base_hom_def by (intro eval_exp_if_base_mono assms)



end