\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expressions_Whiles_Plus_Minus_Base
  imports
    Expression_Plus_Minus_Atomic_Values
    Expression_Whiles
begin

text\<open>WHILE programs with plus, minus, and atomic values\<close>
type_synonym ('si, 'sv, 'eb, 'ea, 'eic, 'ewc) exp_while_plus_minus_base =
  "('si,
    ('si, 'sv, 'eb) exp_plus_minus_atomic_val_hom,
    'ea, 'eic, 'ewc) exp_while"

definition [exp_smart_constructor_def]: "WPMBV v \<equiv> WBase (PMAVV v)"
definition [exp_smart_constructor_def]: "WPMBSI si \<equiv> WBase (PMAVSI si)"
definition [exp_smart_constructor_def]: "WPMBPlus epl epr \<equiv> WBase (Plus epl epr)"
definition [exp_smart_constructor_def]: "WPMBMinus eml emr \<equiv> WBase (Minus eml emr)"
definition [exp_smart_constructor_def]: "WPMBAssign \<equiv> WAssign"
definition [exp_smart_constructor_def]: "WPMBIf \<equiv> WIf"
definition [exp_smart_constructor_def]: "WPMBSeq \<equiv> WSeq"
definition [exp_smart_constructor_def]: "WPMBWhile \<equiv> WWhile"

context
  fixes eval_eb :: "('t :: {zero,one,plus}, 'sv :: {plus,minus}, 'si, 'sv, 'eb) eval_time"
  and eval_ea :: "('t, 'sv, 'si, 'sv, 'ea) eval_time"
  and eval_eic :: "('t, bool, 'si, 'sv, 'eic) eval_time"
  and eval_ewc :: "('t, bool, 'si, 'sv, 'ewc) eval_time"
  and r_while :: "'sv"
begin

definition "eval_exp_while_plus_minus_base \<equiv>
  eval_exp_while (eval_exp_plus_minus_atomic_val_hom eval_eb) eval_ea eval_eic eval_ewc r_while"

lemma eval_exp_while_plus_minus_base_WPMBVI[intro]:
  assumes "s = s'"
  and "v = v'"
  and "t = 0"
  shows "eval_exp_while_plus_minus_base (WPMBV v) s t s' v'"
  using assms unfolding eval_exp_while_plus_minus_base_def WPMBV_def by auto

lemma eval_exp_while_plus_minus_base_WPMBVE[elim]:
  assumes "eval_exp_while_plus_minus_base (WPMBV v) s t s' v'"
  obtains "s = s'" "v = v'" "t = 0"
  using assms unfolding eval_exp_while_plus_minus_base_def WPMBV_def by auto

lemma eval_exp_while_plus_minus_base_WPMBSII[intro]:
  assumes "s = s'"
  and "v' = s si"
  and "t = 1"
  shows "eval_exp_while_plus_minus_base (WPMBSI si) s t s' v'"
  using assms unfolding eval_exp_while_plus_minus_base_def WPMBSI_def by auto

lemma eval_exp_while_plus_minus_base_WPMBSIE[elim]:
  assumes "eval_exp_while_plus_minus_base (WPMBSI si) s t s' v'"
  obtains "s = s'" "v' = s si" "t = 1"
  using assms unfolding eval_exp_while_plus_minus_base_def WPMBSI_def by auto

lemma eval_exp_while_plus_minus_base_WPMBPlusI[intro]:
  assumes "eval_eb epl s t1 s1 v1"
  and "eval_eb epr s1 t2 s2 v2"
  and "s' = s2"
  and "v = v1 + v2"
  and "t = t1 + t2 + 1"
  shows "eval_exp_while_plus_minus_base (WPMBPlus epl epr) s t s' v"
  using assms unfolding eval_exp_while_plus_minus_base_def WPMBPlus_def by auto

lemma eval_exp_while_plus_minus_base_WPMBPlusE[elim]:
  assumes "eval_exp_while_plus_minus_base (WPMBPlus epl epr) s t s' v"
  obtains t1 s1 v1 t2 s2 v2 where "eval_eb epl s t1 s1 v1" "eval_eb epr s1 t2 s2 v2" "s' = s2"
    "v = v1 + v2" "t = t1 + t2 + 1"
  using assms unfolding eval_exp_while_plus_minus_base_def WPMBPlus_def by blast

lemma eval_exp_while_plus_minus_base_WPMBMinusI[intro]:
  assumes "eval_eb eml s t1 s1 v1"
  and "eval_eb emr s1 t2 s2 v2"
  and "s' = s2"
  and "v = v1 - v2"
  and "t = t1 + t2 + 1"
  shows "eval_exp_while_plus_minus_base (WPMBMinus eml emr) s t s' v"
  using assms unfolding eval_exp_while_plus_minus_base_def WPMBMinus_def by auto

lemma eval_exp_while_plus_minus_base_WPMBMinusE[elim]:
  assumes "eval_exp_while_plus_minus_base (WPMBMinus eml emr) s t s' v"
  obtains t1 s1 v1 t2 s2 v2 where "eval_eb eml s t1 s1 v1" "eval_eb emr s1 t2 s2 v2" "s' = s2"
    "v = v1 - v2" "t = t1 + t2 + 1"
  using assms unfolding eval_exp_while_plus_minus_base_def WPMBMinus_def by blast

lemma eval_exp_while_plus_minus_base_WPMBAssignI[intro]:
  assumes "eval_ea ea s t' sea v"
  and "s' = sea(si := v)"
  and "t = t' + 1"
  shows "eval_exp_while_plus_minus_base (WPMBAssign si ea) s t s' v"
  using assms unfolding eval_exp_while_plus_minus_base_def WPMBAssign_def by auto

lemma eval_exp_while_plus_minus_base_WPMBAssignE[elim]:
  assumes "eval_exp_while_plus_minus_base (WPMBAssign si ea) s t s' v"
  obtains t' sae v where "eval_ea ea s t' sae v" "s' = sae(si := v)" "t = t' + 1"
  using assms unfolding eval_exp_while_plus_minus_base_def WPMBAssign_def by auto

lemma eval_exp_while_plus_minus_base_WPMBSeqI[intro]:
  assumes "eval_exp_while_plus_minus_base esf s tf sf vf"
  and "eval_exp_while_plus_minus_base esb sf tb s' v"
  and "t = tf + tb"
  shows "eval_exp_while_plus_minus_base (WPMBSeq esf esb) s t s' v"
  using assms unfolding eval_exp_while_plus_minus_base_def WPMBSeq_def by auto

lemma eval_exp_while_plus_minus_base_WPMBSeqE[elim]:
  assumes "eval_exp_while_plus_minus_base (WPMBSeq esf esb) s t s' v"
  obtains tf sf vf tb where "eval_exp_while_plus_minus_base esf s tf sf vf" "eval_exp_while_plus_minus_base esb sf tb s' v" "t = tf + tb"
  using assms unfolding eval_exp_while_plus_minus_base_def WPMBSeq_def by auto

lemma eval_exp_while_plus_minus_base_WPMBIf_trueI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "b"
  and "eval_exp_while_plus_minus_base eit sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_exp_while_plus_minus_base (WPMBIf eic eit eif) s t s' v"
  using assms unfolding eval_exp_while_plus_minus_base_def WPMBIf_def by auto

lemma eval_exp_while_plus_minus_base_WPMBIf_falseI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "\<not>b"
  and "eval_exp_while_plus_minus_base eif sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_exp_while_plus_minus_base (WPMBIf eic eit eif) s t s' v"
  using assms unfolding eval_exp_while_plus_minus_base_def WPMBIf_def by auto

lemma eval_exp_while_plus_minus_base_WPMBIfE[elim]:
  assumes "eval_exp_while_plus_minus_base (WPMBIf eic eit eif) s t s' v"
  obtains sc b t1 t2 where "eval_eic eic s t1 sc b" "b" "eval_exp_while_plus_minus_base eit sc t2 s' v" "t = t1 + 1 + t2"
    | sc b t1 t2 where "eval_eic eic s t1 sc b" "\<not>b" "eval_exp_while_plus_minus_base eif sc t2 s' v" "t = t1 + 1 + t2"
  using assms unfolding eval_exp_while_plus_minus_base_def WPMBIf_def by auto

lemma eval_exp_while_plus_minus_base_While_trueI[intro]:
  assumes "eval_ewc ewc s t1 sc b" "b"
  and "eval_exp_while_plus_minus_base ewpm sc t2 s2 vew"
  and "eval_exp_while_plus_minus_base (WPMBWhile ewc ewpm) s2 t3 s' v"
  and "t = t1 + 1 + t2 + t3"
  shows "eval_exp_while_plus_minus_base (WPMBWhile ewc ewpm) s t s' v"
  using assms unfolding eval_exp_while_plus_minus_base_def WPMBWhile_def by auto

lemma eval_exp_while_plus_minus_base_While_falseI[intro]:
  assumes "eval_ewc ewc s t' sc b" "\<not>b"
  and "t = t' + 1"
  and "s = s'"
  and "v = r_while"
  shows "eval_exp_while_plus_minus_base (WPMBWhile ewc ewpm) s t s' v"
  using assms unfolding eval_exp_while_plus_minus_base_def WPMBWhile_def by auto

lemma eval_exp_while_plus_minus_base_WPMBWhileE[elim]:
  assumes "eval_exp_while_plus_minus_base (WPMBWhile ewc ewpm) s t s' v"
  obtains t1 sc b t2 s2 vew t3 v3 where "eval_ewc ewc s t1 sc b" "b"
      "eval_exp_while_plus_minus_base ewpm sc t2 s2 vew"
      "eval_exp_while_plus_minus_base (WPMBWhile ewc ewpm) s2 t3 s' v"
      "t = t1 + 1 + t2 + t3"
    | t' sc b where "eval_ewc ewc s t' sc b" "\<not>b" "s = s'" "v = r_while" "t = t' + 1"
  using assms unfolding eval_exp_while_plus_minus_base_def WPMBWhile_def by auto

lemma eval_exp_while_plus_minus_base_induct[induct pred : eval_exp_while_plus_minus_base, case_names
  WPMBV WPMBSI WPMBPlus WPMBMinus WAssign WSeq WIf_true WIf_false WWhile_true WWhile_false]:
  assumes "eval_exp_while_plus_minus_base ewpm s t s' v"
  and "\<And>v s. P (WPMBV v) s 0 s v"
  and "\<And>si s. P (WPMBSI si) s 1 s (s si)"
  and "\<And>epl s t1 s1 v1 epr t2 s2 v2. eval_eb epl s t1 s1 v1 \<Longrightarrow>
    eval_eb epr s1 t2 s2 v2 \<Longrightarrow> P (WPMBPlus epl epr) s (t1 + t2 + 1) s2 (v1 + v2)"
  and "\<And>eml s t1 s1 v1 emr t2 s2 v2. eval_eb eml s t1 s1 v1 \<Longrightarrow>
    eval_eb emr s1 t2 s2 v2 \<Longrightarrow> P (WPMBMinus eml emr) s (t1 + t2 + 1) s2 (v1 - v2)"
  and "\<And>ea s t s' v si. eval_ea ea s t s' v \<Longrightarrow> P (WPMBAssign si ea) s (t + 1) (s'(si := v)) v"
  and "\<And>esf s tf sf vf esb tb sb vb. eval_exp_while_plus_minus_base esf s tf sf vf \<Longrightarrow> P esf s tf sf vf \<Longrightarrow>
    eval_exp_while_plus_minus_base esb sf tb sb vb \<Longrightarrow> P esb sf tb sb vb \<Longrightarrow> P (WPMBSeq esf esb) s (tf + tb) sb vb"
  and "\<And>eic s t1 sc b eit t2 s' v eif. eval_eic eic s t1 sc b \<Longrightarrow> b \<Longrightarrow> eval_exp_while_plus_minus_base eit sc t2 s' v \<Longrightarrow>
    P eit sc t2 s' v \<Longrightarrow> P (WPMBIf eic eit eif) s (t1 + 1 + t2) s' v"
  and "\<And>eic s t1 sc b eif t2 s' v eit. eval_eic eic s t1 sc b \<Longrightarrow> \<not>b \<Longrightarrow> eval_exp_while_plus_minus_base eif sc t2 s' v \<Longrightarrow>
    P eif sc t2 s' v \<Longrightarrow> P (WPMBIf eic eit eif) s (t1 + 1 + t2) s' v"
  and "\<And>ewc ewpm s1 t1 sc b t2 s2 vew t3 s3 v3. eval_ewc ewc s1 t1 sc b \<Longrightarrow> b \<Longrightarrow>
    eval_exp_while_plus_minus_base ewpm sc t2 s2 vew \<Longrightarrow> P ewpm sc t2 s2 vew \<Longrightarrow>
    eval_exp_while_plus_minus_base (WPMBWhile ewc ewpm) s2 t3 s3 v3 \<Longrightarrow>
    P (WPMBWhile ewc ewpm) s2 t3 s3 v3 \<Longrightarrow> P (WPMBWhile ewc ewpm) s1 (t1 + 1 + t2 + t3) s3 v3"
  and "\<And>ewc ew s t sc b. eval_ewc ewc s t sc b \<Longrightarrow> \<not>b \<Longrightarrow> P (WPMBWhile ewc ew) s (t + 1) s r_while"
  shows "P ewpm s t s' v"
  using assms(1) unfolding eval_exp_while_plus_minus_base_def
  apply -
  apply (erule eval_exp_while_induct)
  apply (erule eval_exp_plus_minus_atomic_val_hom_induct)
  by (fold exp_smart_constructor_def eval_exp_while_plus_minus_base_def | blast intro: assms)+

end

lemma eval_exp_while_plus_minus_base_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  and "\<And>e s t s' v. f2 e s t s' v \<longrightarrow> g2 e s t s' v"
  and "\<And>e s t s' v. f3 e s t s' v \<longrightarrow> g3 e s t s' v"
  and "\<And>e s t s' v. f4 e s t s' v \<longrightarrow> g4 e s t s' v"
  shows "eval_exp_while_plus_minus_base f1 f2 f3 f4 r_while e s t s' v \<longrightarrow> eval_exp_while_plus_minus_base g1 g2 g3 g4 r_while e s t s' v"
  unfolding eval_exp_while_plus_minus_base_def
  by (intro eval_exp_while_mono eval_exp_plus_minus_atomic_val_hom_mono assms)


end
