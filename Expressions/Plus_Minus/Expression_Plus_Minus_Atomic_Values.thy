\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expression_Plus_Minus_Atomic_Values
  imports
    Expression_Atomic_Values_Base
    Expression_Plus_Minus_Base
begin

type_synonym ('si, 'sv, 'epl, 'epr, 'eml, 'emr) exp_plus_minus_atomic_val =
  "(('si, 'sv) exp_atomic_val_base,
    'epl, 'epr, 'eml, 'emr) exp_plus_minus_base"

definition [exp_smart_constructor_def]: "PMAVV v \<equiv> EPMBase (V v) :: ('si, 'sv, 'epl, 'epr, 'eml, 'emr) exp_plus_minus_atomic_val"
definition [exp_smart_constructor_def]: "PMAVSI si \<equiv> EPMBase (SI si) :: ('si, 'sv, 'epl, 'epr, 'eml, 'emr) exp_plus_minus_atomic_val"

context
  fixes eval_epl :: "('t :: {plus,zero,one}, 'sv :: {plus,minus}, 'si, 'sv, 'epl) eval_time"
  and eval_epr :: "('t, 'sv, 'si, 'sv, 'epr) eval_time"
  and eval_eml :: "('t, 'sv, 'si, 'sv, 'eml) eval_time"
  and eval_emr :: "('t, 'sv, 'si, 'sv, 'emr) eval_time"
begin

definition "eval_exp_plus_minus_atomic_val \<equiv>
  eval_exp_plus_minus_base eval_exp_atomic_val_base eval_epl eval_epr eval_eml eval_emr"

lemma eval_exp_plus_minus_atomic_val_PMAVVI[intro]:
  assumes "s = s'"
  and "v = v'"
  and "t = 0"
  shows "eval_exp_plus_minus_atomic_val (PMAVV v) s t s' v'"
  using assms unfolding eval_exp_plus_minus_atomic_val_def PMAVV_def by auto

lemma eval_exp_plus_minus_atomic_val_PMAVVE[elim]:
  assumes "eval_exp_plus_minus_atomic_val (PMAVV v) s t s' v'"
  obtains "s = s'" "v = v'" "t = 0"
  using assms unfolding eval_exp_plus_minus_atomic_val_def PMAVV_def by auto

lemma eeval_exp_atomic_val_baseval_exp_atomic_val_base_PMAVSII[intro]:
  assumes "s = s'"
  and "v' = s si"
  and "t = 1"
  shows "eval_exp_plus_minus_atomic_val (PMAVSI si) s t s' v'"
  using assms unfolding eval_exp_plus_minus_atomic_val_def PMAVSI_def by auto

lemma eeval_exp_atomic_val_baseval_exp_atomic_val_base_PMAVSIE[elim]:
  assumes "eval_exp_plus_minus_atomic_val (PMAVSI si) s t s' v'"
  obtains "s = s'" "v' = s si" "t = 1"
  using assms unfolding eval_exp_plus_minus_atomic_val_def PMAVSI_def by auto

lemma eval_exp_plus_minus_atomic_val_PlusI[intro]:
  assumes "eval_epl epl s t1 s1 v1"
  and "eval_epr epr s1 t2 s2 v2"
  and "s' = s2"
  and "v = v1 + v2"
  and "t = t1 + t2 + 1"
  shows "eval_exp_plus_minus_atomic_val (Plus epl epr) s t s' v"
  using assms unfolding eval_exp_plus_minus_atomic_val_def by auto

lemma eval_exp_plus_minus_atomic_val_PlusE[elim]:
  assumes "eval_exp_plus_minus_atomic_val (Plus epl epr) s t s' v"
  obtains t1 s1 v1 t2 s2 v2 where "eval_epl epl s t1 s1 v1" "eval_epr epr s1 t2 s2 v2" "s' = s2"
    "v = v1 + v2" "t = t1 + t2 + 1"
  using assms unfolding eval_exp_plus_minus_atomic_val_def by auto

lemma eval_exp_plus_minus_atomic_val_MinusI[intro]:
  assumes "eval_eml eml s t1 s1 v1"
  and "eval_emr emr s1 t2 s2 v2"
  and "s' = s2"
  and "v = v1 - v2"
  and "t = t1 + t2 + 1"
  shows "eval_exp_plus_minus_atomic_val (Minus eml emr) s t s' v"
  using assms unfolding eval_exp_plus_minus_atomic_val_def by auto

lemma eval_exp_plus_minus_atomic_val_MinusE[elim]:
  assumes "eval_exp_plus_minus_atomic_val (Minus eml emr) s t s' v"
  obtains t1 s1 v1 t2 s2 v2 where "eval_eml eml s t1 s1 v1" "eval_emr emr s1 t2 s2 v2" "s' = s2"
    "v = v1 - v2" "t = t1 + t2 + 1"
  using assms unfolding eval_exp_plus_minus_atomic_val_def by auto

lemma eval_exp_plus_minus_atomic_val_induct[induct pred : eval_exp_plus_minus_atomic_val,
  case_names PMAVV PMAVSI Plus Minus]:
  assumes "eval_exp_plus_minus_atomic_val e s t s' v"
  and "\<And>v s. P (PMAVV v) s 0 s v"
  and "\<And>si s. P (PMAVSI si) s 1 s (s si)"
  and "\<And>epl s t1 s1 v1 epr t2 s2 v2. eval_epl epl s t1 s1 v1 \<Longrightarrow>
    eval_epr epr s1 t2 s2 v2 \<Longrightarrow> P (Plus epl epr) s (t1 + t2 + 1) s2 (v1 + v2)"
  and "\<And>eml s t1 s1 v1 emr t2 s2 v2. eval_eml eml s t1 s1 v1 \<Longrightarrow>
    eval_emr emr s1 t2 s2 v2 \<Longrightarrow> P (Minus eml emr) s (t1 + t2 + 1) s2 (v1 - v2)"
  shows "P e s t s' v"
  using assms unfolding eval_exp_plus_minus_atomic_val_def
  apply (elim eval_exp_plus_minus_base.induct)
  apply (elim eval_exp_atomic_val_base.induct)
  by (fold exp_smart_constructor_def) assumption+

end

lemma eval_exp_plus_minus_atomic_val_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  and "\<And>e s t s' v. f2 e s t s' v \<longrightarrow> g2 e s t s' v"
  and "\<And>e s t s' v. f3 e s t s' v \<longrightarrow> g3 e s t s' v"
  and "\<And>e s t s' v. f4 e s t s' v \<longrightarrow> g4 e s t s' v"
  shows "eval_exp_plus_minus_atomic_val f1 f2 f3 f4 e s t s' v \<longrightarrow> eval_exp_plus_minus_atomic_val g1 g2 g3 g4 e s t s' v"
  unfolding eval_exp_plus_minus_atomic_val_def
  by (intro eval_exp_plus_minus_base_mono assms impI)

type_synonym ('si, 'sv, 'e) exp_plus_minus_atomic_val_hom =
  "('si, 'sv, 'e, 'e, 'e, 'e) exp_plus_minus_atomic_val"

context
  fixes eval_e :: "('t :: {plus,zero,one}, 'sv :: {plus,minus}, 'si, 'sv, 'e) eval_time"
begin

definition "eval_exp_plus_minus_atomic_val_hom \<equiv>
  eval_exp_plus_minus_atomic_val eval_e eval_e eval_e eval_e"

lemma eval_exp_plus_minus_atomic_val_hom_PMAVVI[intro]:
  assumes "s = s'"
  and "v = v'"
  and "t = 0"
  shows "eval_exp_plus_minus_atomic_val_hom (PMAVV v) s t s' v'"
  using assms unfolding eval_exp_plus_minus_atomic_val_hom_def by auto

lemma eval_exp_plus_minus_atomic_val_hom_PMAVVE[elim]:
  assumes "eval_exp_plus_minus_atomic_val_hom (PMAVV v) s t s' v'"
  obtains "s = s'" "v = v'" "t = 0"
  using assms unfolding eval_exp_plus_minus_atomic_val_hom_def by auto

lemma eeval_exp_atomic_val_hom_baseval_exp_atomic_val_hom_base_PMAVSII[intro]:
  assumes "s = s'"
  and "v' = s si"
  and "t = 1"
  shows "eval_exp_plus_minus_atomic_val_hom (PMAVSI si) s t s' v'"
  using assms unfolding eval_exp_plus_minus_atomic_val_hom_def by auto

lemma eeval_exp_atomic_val_hom_baseval_exp_atomic_val_hom_base_PMAVSIE[elim]:
  assumes "eval_exp_plus_minus_atomic_val_hom (PMAVSI si) s t s' v'"
  obtains "s = s'" "v' = s si" "t = 1"
  using assms unfolding eval_exp_plus_minus_atomic_val_hom_def by auto

lemma eval_exp_plus_minus_atomic_val_hom_PlusI[intro]:
  assumes "eval_e epl s t1 s1 v1"
  and "eval_e epr s1 t2 s2 v2"
  and "s' = s2"
  and "v = v1 + v2"
  and "t = t1 + t2 + 1"
  shows "eval_exp_plus_minus_atomic_val_hom (Plus epl epr) s t s' v"
  using assms unfolding eval_exp_plus_minus_atomic_val_hom_def by auto

lemma eval_exp_plus_minus_atomic_val_hom_PlusE[elim]:
  assumes "eval_exp_plus_minus_atomic_val_hom (Plus epl epr) s t s' v"
  obtains t1 s1 v1 t2 s2 v2 where "eval_e epl s t1 s1 v1" "eval_e epr s1 t2 s2 v2" "s' = s2"
    "v = v1 + v2" "t = t1 + t2 + 1"
  using assms unfolding eval_exp_plus_minus_atomic_val_hom_def by auto

lemma eval_exp_plus_minus_atomic_val_hom_MinusI[intro]:
  assumes "eval_e eml s t1 s1 v1"
  and "eval_e emr s1 t2 s2 v2"
  and "s' = s2"
  and "v = v1 - v2"
  and "t = t1 + t2 + 1"
  shows "eval_exp_plus_minus_atomic_val_hom (Minus eml emr) s t s' v"
  using assms unfolding eval_exp_plus_minus_atomic_val_hom_def by auto

lemma eval_exp_plus_minus_atomic_val_hom_MinusE[elim]:
  assumes "eval_exp_plus_minus_atomic_val_hom (Minus eml emr) s t s' v"
  obtains t1 s1 v1 t2 s2 v2 where "eval_e eml s t1 s1 v1" "eval_e emr s1 t2 s2 v2" "s' = s2"
    "v = v1 - v2" "t = t1 + t2 + 1"
  using assms unfolding eval_exp_plus_minus_atomic_val_hom_def by auto

lemma eval_exp_plus_minus_atomic_val_hom_induct[induct pred : eval_exp_plus_minus_atomic_val_hom,
  case_names PMAVV PMAVSI Plus Minus]:
  assumes "eval_exp_plus_minus_atomic_val_hom e s t s' v"
  and "\<And>v s. P (PMAVV v) s 0 s v"
  and "\<And>si s. P (PMAVSI si) s 1 s (s si)"
  and "\<And>epl s t1 s1 v1 epr t2 s2 v2. eval_e epl s t1 s1 v1 \<Longrightarrow>
    eval_e epr s1 t2 s2 v2 \<Longrightarrow> P (Plus epl epr) s (t1 + t2 + 1) s2 (v1 + v2)"
  and "\<And>eml s t1 s1 v1 emr t2 s2 v2. eval_e eml s t1 s1 v1 \<Longrightarrow>
    eval_e emr s1 t2 s2 v2 \<Longrightarrow> P (Minus eml emr) s (t1 + t2 + 1) s2 (v1 - v2)"
  shows "P e s t s' v"
  using assms unfolding eval_exp_plus_minus_atomic_val_hom_def
  by (rule eval_exp_plus_minus_atomic_val_induct)

end

lemma eval_exp_plus_minus_atomic_val_hom_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  shows "eval_exp_plus_minus_atomic_val_hom f1 e s t s' v \<longrightarrow> eval_exp_plus_minus_atomic_val_hom g1 e s t s' v"
  unfolding eval_exp_plus_minus_atomic_val_hom_def
  by (intro eval_exp_plus_minus_atomic_val_mono assms impI)


end