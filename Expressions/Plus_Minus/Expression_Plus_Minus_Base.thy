\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expression_Plus_Minus_Base
  imports Expressions_Base
begin

datatype ('eb, 'epl, 'epr, 'eml, 'emr) exp_plus_minus_base =
  EPMBase "'eb"
| Plus "'epl" "'epr"
| Minus "'eml" "'emr"

context
  fixes eval_eb :: "('t :: {plus, one}, 'r :: {plus,minus}, 'si, 'sv, 'eb) eval_time"
  and eval_epl :: "('t, 'r, 'si, 'sv, 'epl) eval_time"
  and eval_epr :: "('t, 'r, 'si, 'sv, 'epr) eval_time"
  and eval_eml :: "('t, 'r, 'si, 'sv, 'eml) eval_time"
  and eval_emr :: "('t, 'r, 'si, 'sv, 'emr) eval_time"
begin

inductive eval_exp_plus_minus_base ::
  "('t, 'r, 'si, 'sv, ('eb, 'epl, 'epr, 'eml, 'emr) exp_plus_minus_base) eval_time"
where
  eval_exp_plus_minus_base_EPMBase[intro]: "eval_eb eb s t s' r \<Longrightarrow>
    eval_exp_plus_minus_base (EPMBase eb) s t s' r"
| eval_exp_plus_minus_base_Plus: "eval_epl epl s t1 s1 r1 \<Longrightarrow>
    eval_epr epr s1 t2 s2 r2 \<Longrightarrow>
    eval_exp_plus_minus_base (Plus epl epr) s (t1 + t2 + 1) s2 (r1 + r2)"
| eval_exp_plus_minus_base_Minus: "eval_eml eml s t1 s1 r1 \<Longrightarrow>
    eval_emr emr s1 t2 s2 r2 \<Longrightarrow>
    eval_exp_plus_minus_base (Minus eml emr) s (t1 + t2 + 1) s2 (r1 - r2)"

inductive_cases eval_exp_plus_minus_base_EPMBaseE[elim]:
  "eval_exp_plus_minus_base (EPMBase eb) s t s' r"
inductive_cases eval_exp_plus_minus_base_PlusE[elim]:
  "eval_exp_plus_minus_base (Plus epl epr) s t s' r"
inductive_cases eval_exp_plus_minus_base_MinusE[elim]:
  "eval_exp_plus_minus_base (Minus eml emr) s t s' r"

lemma eval_exp_plus_minus_base_PlusI[intro]:
  assumes "eval_epl epl s t1 s1 r1"
  and "eval_epr epr s1 t2 s2 r2"
  and "s' = s2"
  and "r = r1 + r2"
  and "t = t1 + t2 + 1"
  shows "eval_exp_plus_minus_base (Plus epl epr) s t s' r"
  using assms eval_exp_plus_minus_base.intros by auto

lemma eval_exp_plus_minus_base_MinusI[intro]:
  assumes "eval_eml eml s t1 s1 r1"
  and "eval_emr emr s1 t2 s2 r2"
  and "s' = s2"
  and "r = r1 - r2"
  and "t = t1 + t2 + 1"
  shows "eval_exp_plus_minus_base (Minus eml emr) s t s' r"
  using assms eval_exp_plus_minus_base.intros by auto

end

lemma eval_exp_plus_minus_base_mono[mono]:
  assumes "\<And>e s t s' r. f1 e s t s' r \<longrightarrow> g1 e s t s' r"
  and "\<And>e s t s' r. f2 e s t s' r \<longrightarrow> g2 e s t s' r"
  and "\<And>e s t s' r. f3 e s t s' r \<longrightarrow> g3 e s t s' r"
  and "\<And>e s t s' r. f4 e s t s' r \<longrightarrow> g4 e s t s' r"
  and "\<And>e s t s' r. f5 e s t s' r \<longrightarrow> g5 e s t s' r"
  shows "eval_exp_plus_minus_base f1 f2 f3 f4 f5 e s t s' r \<longrightarrow> eval_exp_plus_minus_base g1 g2 g3 g4 g5 e s t s' r"
proof
  assume "eval_exp_plus_minus_base f1 f2 f3 f4 f5 e s t s' r"
  from this assms show "eval_exp_plus_minus_base g1 g2 g3 g4 g5 e s t s' r"
    by (induction rule: eval_exp_plus_minus_base.induct) fast+
qed


type_synonym ('eb, 'e) exp_plus_minus_base_hom =
  "('eb, 'e, 'e, 'e, 'e) exp_plus_minus_base"

definition "eval_exp_plus_minus_base_hom eval_eb eval_e \<equiv>
  eval_exp_plus_minus_base eval_eb eval_e eval_e eval_e eval_e"

lemma eval_exp_plus_minus_base_hom_mono[mono]:
  assumes "\<And>e s t s' r. f1 e s t s' r \<longrightarrow> g1 e s t s' r"
  and "\<And>e s t s' r. f2 e s t s' r \<longrightarrow> g2 e s t s' r"
  shows "eval_exp_plus_minus_base_hom f1 f2 e s t s' r \<longrightarrow> eval_exp_plus_minus_base_hom g1 g2 e s t s' r"
  unfolding eval_exp_plus_minus_base_hom_def by (intro eval_exp_plus_minus_base_mono assms)

lemma eval_exp_plus_minus_base_hom_EPMBaseI[intro]:
  assumes "eval_eb eb s t s' r"
  shows "eval_exp_plus_minus_base_hom eval_eb eval_e (EPMBase eb) s t s' r"
  using assms unfolding eval_exp_plus_minus_base_hom_def by auto

lemma eval_exp_plus_minus_base_hom_EPMBaseE[elim]:
  assumes "eval_exp_plus_minus_base_hom eval_eb eval_e (EPMBase eb) s t s' r"
  obtains "eval_eb eb s t s' r"
  using assms unfolding eval_exp_plus_minus_base_hom_def by auto

lemma eval_exp_plus_minus_base_hom_PlusI[intro]:
  assumes "eval_e epl s t1 s1 r1"
  and "eval_e epr s1 t2 s2 r2"
  and "s' = s2"
  and "r = r1 + r2"
  and "t = t1 + t2 + 1"
  shows "eval_exp_plus_minus_base_hom eval_eb eval_e (Plus epl epr) s t s' r"
  using assms unfolding eval_exp_plus_minus_base_hom_def by auto

lemma eval_exp_plus_minus_base_hom_PlusE[elim]:
  assumes "eval_exp_plus_minus_base_hom eval_eb eval_e (Plus epl epr) s t s' r"
  obtains t1 s1 r1 t2 s2 r2 where
    "eval_e epl s t1 s1 r1" "eval_e epr s1 t2 s2 r2" "s' = s2" "r = r1 + r2" "t = t1 + t2 + 1"
  using assms unfolding eval_exp_plus_minus_base_hom_def by auto

lemma eval_exp_plus_minus_base_hom_MinusI[intro]:
  assumes "eval_e eml s t1 s1 r1"
  and "eval_e emr s1 t2 s2 r2"
  and "s' = s2"
  and "r = r1 - r2"
  and "t = t1 + t2 + 1"
  shows "eval_exp_plus_minus_base_hom eval_eb eval_e (Minus eml emr) s t s' r"
  using assms unfolding eval_exp_plus_minus_base_hom_def by auto

lemma eval_exp_plus_minus_base_hom_MinusE[elim]:
  assumes "eval_exp_plus_minus_base_hom eval_eb eval_e (Minus eml emr) s t s' r"
  obtains t1 s1 r1 t2 s2 r2 where
    "eval_e eml s t1 s1 r1" "eval_e emr s1 t2 s2 r2" "s' = s2" "r = r1 - r2" "t = t1 + t2 + 1"
  using assms unfolding eval_exp_plus_minus_base_hom_def by auto

lemma eval_exp_plus_minus_base_hom_induct[induct pred : eval_exp_plus_minus_base_hom,
  case_names EPMBase Plus Minus]:
  assumes "eval_exp_plus_minus_base_hom eval_eb eval_e e s t s' r"
  and "\<And>eb s t s' r. eval_eb eb s t s' r \<Longrightarrow> P (EPMBase eb) s t s' r"
  and "\<And>epl s t1 s1 r1 epr t2 s2 r2. eval_e epl s t1 s1 r1 \<Longrightarrow>
    eval_e epr s1 t2 s2 r2 \<Longrightarrow> P (Plus epl epr) s (t1 + t2 + 1) s2 (r1 + r2)"
  and "\<And>eml s t1 s1 r1 emr t2 s2 r2. eval_e eml s t1 s1 r1 \<Longrightarrow>
    eval_e emr s1 t2 s2 r2 \<Longrightarrow> P (Minus eml emr) s (t1 + t2 + 1) s2 (r1 - r2)"
  shows "P e s t s' r"
  using assms unfolding eval_exp_plus_minus_base_hom_def
  by (rule eval_exp_plus_minus_base.induct)


end