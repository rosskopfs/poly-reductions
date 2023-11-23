\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expressions_Whiles_Plus_Minus
  imports
    Expressions_Whiles_Plus_Minus_Base
begin

datatype ('si, 'sv, 'eic, 'ewc) exp_while_plus_minus = EWPM
  "('si, 'sv,
    ('si, 'sv, 'eic, 'ewc) exp_while_plus_minus,
    ('si, 'sv, 'eic, 'ewc) exp_while_plus_minus,
    'eic, 'ewc) exp_while_plus_minus_base"

context
  fixes eval_ea :: "('t :: {zero,one,plus}, 'sv, 'si, 'sv  :: {minus, plus},
    ('si, 'sv, 'eic, 'ewc) exp_while_plus_minus) eval_time"
  and eval_eic :: "('t, bool, 'si, 'sv, 'eic) eval_time"
  and eval_ewc :: "('t, bool, 'si, 'sv, 'ewc) eval_time"
  and r_while :: "'sv"
begin

inductive eval_exp_while_plus_minus ::
  "('t, 'sv, 'si, 'sv, ('si, 'sv, 'eic, 'ewc) exp_while_plus_minus) eval_time"
where
  eval_exp_while_plus_minus_EWPM[intro]:
    "eval_exp_while_plus_minus_base eval_exp_while_plus_minus eval_ea eval_eic eval_ewc r_while e s t s' v \<Longrightarrow>
    eval_exp_while_plus_minus (EWPM e) s t s' v"

inductive_cases eval_exp_while_plus_minus_EWPME[elim]: "eval_exp_while_plus_minus (EWPM e) s t s' v"

definition [exp_smart_constructor_def]: "WPMV v \<equiv> EWPM (WPMBV v)"
definition [exp_smart_constructor_def]: "WPMSI si \<equiv> EWPM (WPMBSI si)"
definition [exp_smart_constructor_def]: "WPMPlus epl epr \<equiv> EWPM (WPMBPlus epl epr)"
definition [exp_smart_constructor_def]: "WPMMinus eml emr \<equiv> EWPM (WPMBMinus eml emr)"
definition [exp_smart_constructor_def]: "WPMAssign si ea \<equiv> EWPM (WPMBAssign si ea)"
definition [exp_smart_constructor_def]: "WPMSeq esf esb \<equiv> EWPM (WPMBSeq esf esb)"
definition [exp_smart_constructor_def]: "WPMIf eic eit eif \<equiv> EWPM (WPMBIf eic eit eif)"
definition [exp_smart_constructor_def]: "WPMWhile ewc ew \<equiv> EWPM (WPMBWhile ewc ew)"

lemma eval_exp_while_plus_minus_WPMVI[intro]:
  assumes "s = s'"
  and "v = v'"
  and "t = 0"
  shows "eval_exp_while_plus_minus (WPMV v) s t s' v'"
  using assms unfolding WPMV_def by auto

lemma eval_exp_while_plus_minus_WPMVE[elim]:
  assumes "eval_exp_while_plus_minus (WPMV v) s t s' v'"
  obtains "s = s'" "v = v'" "t = 0"
  using assms unfolding WPMV_def by auto

lemma eval_exp_while_plus_minus_WPMSII[intro]:
  assumes "s = s'"
  and "v' = s si"
  and "t = 1"
  shows "eval_exp_while_plus_minus (WPMSI si) s t s' v'"
  using assms unfolding WPMSI_def by auto

lemma eval_exp_while_plus_minus_WPMSIE[elim]:
  assumes "eval_exp_while_plus_minus (WPMSI si) s t s' v'"
  obtains "s = s'" "v' = s si" "t = 1"
  using assms unfolding WPMSI_def by auto

lemma eval_exp_while_plus_minus_WPMPlusI[intro]:
  assumes "eval_exp_while_plus_minus epl s t1 s1 v1"
  and "eval_exp_while_plus_minus epr s1 t2 s2 v2"
  and "s' = s2"
  and "v = v1 + v2"
  and "t = t1 + t2 + 1"
  shows "eval_exp_while_plus_minus (WPMPlus epl epr) s t s' v"
  using assms unfolding WPMPlus_def by auto

lemma eval_exp_while_plus_minus_WPMPlusE[elim]:
  assumes "eval_exp_while_plus_minus (WPMPlus epl epr) s t s' v"
  obtains t1 s1 v1 t2 s2 v2 where "eval_exp_while_plus_minus epl s t1 s1 v1"
    "eval_exp_while_plus_minus epr s1 t2 s2 v2" "s' = s2" "v = v1 + v2" "t = t1 + t2 + 1"
  using assms unfolding WPMPlus_def by blast

lemma eval_exp_while_plus_minus_WPMMinusI[intro]:
  assumes "eval_exp_while_plus_minus eml s t1 s1 v1"
  and "eval_exp_while_plus_minus emr s1 t2 s2 v2"
  and "s' = s2"
  and "v = v1 - v2"
  and "t = t1 + t2 + 1"
  shows "eval_exp_while_plus_minus (WPMMinus eml emr) s t s' v"
  using assms unfolding WPMMinus_def by auto

lemma eval_exp_while_plus_minus_WPMMinusE[elim]:
  assumes "eval_exp_while_plus_minus (WPMMinus eml emr) s t s' v"
  obtains t1 s1 v1 t2 s2 v2 where "eval_exp_while_plus_minus eml s t1 s1 v1"
    "eval_exp_while_plus_minus emr s1 t2 s2 v2" "s' = s2" "v = v1 - v2" "t = t1 + t2 + 1"
  using assms unfolding WPMMinus_def by blast

lemma eval_exp_while_plus_minus_WPMAssignI[intro]:
  assumes "eval_ea ea s t' sea v"
  and "s' = sea(si := v)"
  and "t = t' + 1"
  shows "eval_exp_while_plus_minus (WPMAssign si ea) s t s' v"
  using assms unfolding WPMAssign_def by auto

lemma eval_exp_while_plus_minus_WPMAssignE[elim]:
  assumes "eval_exp_while_plus_minus (WPMAssign si ea) s t s' v"
  obtains t' sae v where "eval_ea ea s t' sae v" "s' = sae(si := v)" "t = t' + 1"
  using assms unfolding WPMAssign_def by blast

lemma eval_exp_while_plus_minus_WPMSeqI[intro]:
  assumes "eval_exp_while_plus_minus (EWPM esf) s tf sf vf"
  and "eval_exp_while_plus_minus (EWPM esb) sf tb s' v"
  and "t = tf + tb"
  shows "eval_exp_while_plus_minus (WPMSeq esf esb) s t s' v"
  using assms unfolding WPMSeq_def by auto

lemma eval_exp_while_plus_minus_WPMSeqE[elim]:
  assumes "eval_exp_while_plus_minus (WPMSeq esf esb) s t s' v"
  obtains tf sf vf tb where "eval_exp_while_plus_minus (EWPM esf) s tf sf vf"
    "eval_exp_while_plus_minus (EWPM esb) sf tb s' v" "t = tf + tb"
  using assms unfolding WPMSeq_def by blast

lemma eval_exp_while_plus_minus_WPMIf_trueI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "b"
  and "eval_exp_while_plus_minus (EWPM eit) sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_exp_while_plus_minus (WPMIf eic eit eif) s t s' v"
  using assms unfolding WPMIf_def by auto

lemma eval_exp_while_plus_minus_WPMIf_falseI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "\<not>b"
  and "eval_exp_while_plus_minus (EWPM eif) sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_exp_while_plus_minus (WPMIf eic eit eif) s t s' v"
  using assms unfolding WPMIf_def by auto

lemma eval_exp_while_plus_minus_WPMIfE[elim]:
  assumes "eval_exp_while_plus_minus (WPMIf eic eit eif) s t s' v"
  obtains sc b t1 t2 where "eval_eic eic s t1 sc b" "b" "eval_exp_while_plus_minus (EWPM eit) sc t2 s' v" "t = t1 + 1 + t2"
    | sc b t1 t2 where "eval_eic eic s t1 sc b" "\<not>b" "eval_exp_while_plus_minus (EWPM eif) sc t2 s' v" "t = t1 + 1 + t2"
  using assms unfolding WPMIf_def by blast

lemma eval_exp_while_plus_minus_While_trueI[intro]:
  assumes "eval_ewc ewc s t1 sc b" "b"
  and "eval_exp_while_plus_minus (EWPM ewpm) sc t2 s2 vew"
  and "eval_exp_while_plus_minus (WPMWhile ewc ewpm) s2 t3 s' v"
  and "t = t1 + 1 + t2 + t3"
  shows "eval_exp_while_plus_minus (WPMWhile ewc ewpm) s t s' v"
  using assms unfolding WPMWhile_def by auto

lemma eval_exp_while_plus_minus_While_falseI[intro]:
  assumes "eval_ewc ewc s t' sc b" "\<not>b"
  and "t = t' + 1"
  and "s = s'"
  and "v = r_while"
  shows "eval_exp_while_plus_minus (WPMWhile ewc ewpm) s t s' v"
  using assms unfolding WPMWhile_def by auto

lemma eval_exp_while_plus_minus_WPMWhileE[elim]:
  assumes "eval_exp_while_plus_minus (WPMWhile ewc ewpm) s t s' v"
  obtains t1 sc b t2 s2 vew t3 v3 where "eval_ewc ewc s t1 sc b" "b"
      "eval_exp_while_plus_minus (EWPM ewpm) sc t2 s2 vew"
      "eval_exp_while_plus_minus (WPMWhile ewc ewpm) s2 t3 s' v"
      "t = t1 + 1 + t2 + t3"
    | t' sc b where "eval_ewc ewc s t' sc b" "\<not>b" "s = s'" "v = r_while" "t = t' + 1"
  using assms unfolding WPMWhile_def
  apply (elim eval_exp_while_plus_minus_EWPME)
  apply (erule eval_exp_while_plus_minus_base_WPMBWhileE)
  by blast+

lemma eval_exp_while_plus_minus_induct[induct pred : eval_exp_while_plus_minus, case_names
  WPMV WPMSI WPMPlus WPMMinus WAssign WSeq WIf_true WIf_false WWhile_true WWhile_false]:
  assumes "eval_exp_while_plus_minus ewpm s t s' v"
  and "\<And>v s. P (WPMV v) s 0 s v"
  and "\<And>si s. P (WPMSI si) s 1 s (s si)"
  and "\<And>epl s t1 s1 v1 epr t2 s2 v2. eval_exp_while_plus_minus epl s t1 s1 v1 \<Longrightarrow>
    P epl s t1 s1 v1 \<Longrightarrow> eval_exp_while_plus_minus epr s1 t2 s2 v2 \<Longrightarrow>
    P epr s1 t2 s2 v2 \<Longrightarrow> P (WPMPlus epl epr) s (t1 + t2 + 1) s2 (v1 + v2)"
  and "\<And>eml s t1 s1 v1 emr t2 s2 v2. eval_exp_while_plus_minus eml s t1 s1 v1 \<Longrightarrow>
    P eml s t1 s1 v1 \<Longrightarrow> eval_exp_while_plus_minus emr s1 t2 s2 v2 \<Longrightarrow>
    P emr s1 t2 s2 v2 \<Longrightarrow> P (WPMMinus eml emr) s (t1 + t2 + 1) s2 (v1 - v2)"
  and "\<And>ea s t s' v si. eval_ea ea s t s' v \<Longrightarrow> P (WPMAssign si ea) s (t + 1) (s'(si := v)) v"
  and "\<And>esf s tf sf vf esb tb sb vb. eval_exp_while_plus_minus (EWPM esf) s tf sf vf \<Longrightarrow>
    P (EWPM esf) s tf sf vf \<Longrightarrow> eval_exp_while_plus_minus (EWPM esb) sf tb sb vb \<Longrightarrow>
    P (EWPM esb) sf tb sb vb \<Longrightarrow> P (WPMSeq esf esb) s (tf + tb) sb vb"
  and "\<And>eic s t1 sc b eit t2 s' v eif. eval_eic eic s t1 sc b \<Longrightarrow> b \<Longrightarrow>
    eval_exp_while_plus_minus (EWPM eit) sc t2 s' v \<Longrightarrow>
    P (EWPM eit) sc t2 s' v \<Longrightarrow> P (WPMIf eic eit eif) s (t1 + 1 + t2) s' v"
  and "\<And>eic s t1 sc b eif t2 s' v eit. eval_eic eic s t1 sc b \<Longrightarrow> \<not>b \<Longrightarrow>
    eval_exp_while_plus_minus (EWPM eif) sc t2 s' v \<Longrightarrow>
    P (EWPM eif) sc t2 s' v \<Longrightarrow> P (WPMIf eic eit eif) s (t1 + 1 + t2) s' v"
  and "\<And>ewc ewpm s1 t1 sc b t2 s2 vew t3 s3 v3. eval_ewc ewc s1 t1 sc b \<Longrightarrow> b \<Longrightarrow>
    eval_exp_while_plus_minus (EWPM ewpm) sc t2 s2 vew \<Longrightarrow> P (EWPM ewpm) sc t2 s2 vew \<Longrightarrow>
    eval_exp_while_plus_minus (WPMWhile ewc ewpm) s2 t3 s3 v3 \<Longrightarrow>
    P (WPMWhile ewc ewpm) s2 t3 s3 v3 \<Longrightarrow> P (WPMWhile ewc ewpm) s1 (t1 + 1 + t2 + t3) s3 v3"
  and "\<And>ewc ew s t sc b. eval_ewc ewc s t sc b \<Longrightarrow> \<not>b \<Longrightarrow> P (WPMWhile ewc ew) s (t + 1) s r_while"
  shows "P ewpm s t s' v"
using assms(1)
proof (induction ewpm s t s' v rule: eval_exp_while_plus_minus.induct)
  let ?eval_exp_wpm_base =
    "eval_exp_while_plus_minus_base eval_exp_while_plus_minus eval_ea eval_eic eval_ewc r_while"
  note mono = mp[OF eval_exp_while_plus_minus_base_mono[of _ eval_exp_while_plus_minus], rotated -1]
  case (eval_exp_while_plus_minus_EWPM e s t s' v)
  then show ?case
  proof (induction rule: eval_exp_while_plus_minus_base_induct)
    case (WSeq esf s tf sf vf esb tb sb vb)
    have "?eval_exp_wpm_base esf s tf sf vf" by (intro mono[OF WSeq(1)]) auto
    moreover have "?eval_exp_wpm_base esb sf tb sb vb" by (intro mono[OF WSeq(2)]) auto
    ultimately show ?case by (fold exp_smart_constructor_def) (blast intro: assms WSeq)
  next
    case (WIf_true eic s t1 sc b eit t2 s' v eif)
    have "?eval_exp_wpm_base eit sc t2 s' v" by (intro mono[OF WIf_true(3)]) auto
    with WIf_true show ?case by (fold exp_smart_constructor_def) (blast intro: assms)
  next
    case (WIf_false eic s t1 sc b eif t2 s' v eit)
    have "?eval_exp_wpm_base eif sc t2 s' v" by (intro mono[OF WIf_false(3)]) auto
    with WIf_false show ?case by (fold exp_smart_constructor_def) (blast intro: assms)
  next
    case (WWhile_true ewc ewpm s1 t1 sc b t2 s2 vew t3 s3 v3)
    have "?eval_exp_wpm_base ewpm sc t2 s2 vew" by (intro mono[OF WWhile_true(3)]) auto
    moreover have "eval_exp_while_plus_minus (WPMWhile ewc ewpm) s2 t3 s3 v3"
      unfolding WPMWhile_def
      by (intro eval_exp_while_plus_minus.eval_exp_while_plus_minus_EWPM mono[OF WWhile_true(4)]) auto
    ultimately show ?case
      by (fold exp_smart_constructor_def)
      (blast intro: assms WWhile_true[folded exp_smart_constructor_def])
  qed (fold exp_smart_constructor_def, (blast intro: assms)+)
qed

end

lemma eval_exp_while_plus_minus_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  and "\<And>e s t s' v. f2 e s t s' v \<longrightarrow> g2 e s t s' v"
  and "\<And>e s t s' v. f3 e s t s' v \<longrightarrow> g3 e s t s' v"
  shows "eval_exp_while_plus_minus f1 f2 f3 r_while e s t s' v \<longrightarrow> eval_exp_while_plus_minus g1 g2 g3 r_while e s t s' v"
proof
  assume "eval_exp_while_plus_minus f1 f2 f3 r_while e s t s' v"
  from this assms show "eval_exp_while_plus_minus g1 g2 g3 r_while e s t s' v"
  proof (induction rule: eval_exp_while_plus_minus_induct)
    case WWhile_true
    then show ?case
    by - (rule eval_exp_while_plus_minus_While_trueI, fast+)
  qed fast+
qed


context
  fixes eval_eic :: "('t :: {zero,one,plus}, bool, 'si, 'sv :: {minus,plus}, 'eic) eval_time"
  and eval_ewc :: "('t, bool, 'si, 'sv, 'ewc) eval_time"
  and r_while :: "'sv"
begin

inductive eval_exp_while_plus_minus_assign_impure_state ::
  "('t, 'sv, 'si, 'sv, ('si, 'sv, 'eic, 'ewc) exp_while_plus_minus) eval_time"
where
  eval_exp_while_plus_minus_assign_impure_state[intro]:
    "eval_exp_while_plus_minus
      eval_exp_while_plus_minus_assign_impure_state eval_eic eval_ewc r_while e s t s' v \<Longrightarrow>
    eval_exp_while_plus_minus_assign_impure_state e s t s' v"

inductive_cases eval_exp_while_plus_minus_assign_impure_stateE[elim]:
  "eval_exp_while_plus_minus_assign_impure_state e s t s' v"

lemma eval_exp_while_plus_minus_assign_impure_state_WPMVI[intro]:
  assumes "s = s'"
  and "v = v'"
  and "t = 0"
  shows "eval_exp_while_plus_minus_assign_impure_state (WPMV v) s t s' v'"
  using assms by auto

lemma eval_exp_while_plus_minus_assign_impure_state_WPMVE[elim]:
  assumes "eval_exp_while_plus_minus_assign_impure_state (WPMV v) s t s' v'"
  obtains "s = s'" "v = v'" "t = 0"
  using assms by auto

lemma eval_exp_while_plus_minus_assign_impure_state_WPMSII[intro]:
  assumes "s = s'"
  and "v' = s si"
  and "t = 1"
  shows "eval_exp_while_plus_minus_assign_impure_state (WPMSI si) s t s' v'"
  using assms by auto

lemma eval_exp_while_plus_minus_assign_impure_state_WPMSIE[elim]:
  assumes "eval_exp_while_plus_minus_assign_impure_state (WPMSI si) s t s' v'"
  obtains "s = s'" "v' = s si" "t = 1"
  using assms by auto

lemma eval_exp_while_plus_minus_assign_impure_state_WPMPlusI[intro]:
  assumes "eval_exp_while_plus_minus_assign_impure_state epl s t1 s1 v1"
  and "eval_exp_while_plus_minus_assign_impure_state epr s1 t2 s2 v2"
  and "s' = s2"
  and "v = v1 + v2"
  and "t = t1 + t2 + 1"
  shows "eval_exp_while_plus_minus_assign_impure_state (WPMPlus epl epr) s t s' v"
  using assms by auto

lemma eval_exp_while_plus_minus_assign_impure_state_WPMPlusE[elim]:
  assumes "eval_exp_while_plus_minus_assign_impure_state (WPMPlus epl epr) s t s' v"
  obtains t1 s1 v1 t2 s2 v2 where "eval_exp_while_plus_minus_assign_impure_state epl s t1 s1 v1"
    "eval_exp_while_plus_minus_assign_impure_state epr s1 t2 s2 v2" "s' = s2" "v = v1 + v2" "t = t1 + t2 + 1"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_impure_state_WPMMinusI[intro]:
  assumes "eval_exp_while_plus_minus_assign_impure_state eml s t1 s1 v1"
  and "eval_exp_while_plus_minus_assign_impure_state emr s1 t2 s2 v2"
  and "s' = s2"
  and "v = v1 - v2"
  and "t = t1 + t2 + 1"
  shows "eval_exp_while_plus_minus_assign_impure_state (WPMMinus eml emr) s t s' v"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_impure_state_WPMMinusE[elim]:
  assumes "eval_exp_while_plus_minus_assign_impure_state (WPMMinus eml emr) s t s' v"
  obtains t1 s1 v1 t2 s2 v2 where "eval_exp_while_plus_minus_assign_impure_state eml s t1 s1 v1"
    "eval_exp_while_plus_minus_assign_impure_state emr s1 t2 s2 v2" "s' = s2" "v = v1 - v2" "t = t1 + t2 + 1"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_impure_state_WPMAssignI[intro]:
  assumes "eval_exp_while_plus_minus_assign_impure_state ea s t' sea v"
  and "s' = sea(si := v)"
  and "t = t' + 1"
  shows "eval_exp_while_plus_minus_assign_impure_state (WPMAssign si ea) s t s' v"
  using assms by auto

lemma eval_exp_while_plus_minus_assign_impure_state_WPMAssignE[elim]:
  assumes "eval_exp_while_plus_minus_assign_impure_state (WPMAssign si ea) s t s' v"
  obtains t' sae v where "eval_exp_while_plus_minus_assign_impure_state ea s t' sae v"
    "s' = sae(si := v)" "t = t' + 1"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_impure_state_WPMSeqI[intro]:
  assumes "eval_exp_while_plus_minus_assign_impure_state (EWPM esf) s tf sf vf"
  and "eval_exp_while_plus_minus_assign_impure_state (EWPM esb) sf tb s' v"
  and "t = tf + tb"
  shows "eval_exp_while_plus_minus_assign_impure_state (WPMSeq esf esb) s t s' v"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_impure_state_WPMSeqE[elim]:
  assumes "eval_exp_while_plus_minus_assign_impure_state (WPMSeq esf esb) s t s' v"
  obtains tf sf vf tb where "eval_exp_while_plus_minus_assign_impure_state (EWPM esf) s tf sf vf"
    "eval_exp_while_plus_minus_assign_impure_state (EWPM esb) sf tb s' v" "t = tf + tb"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_impure_state_WPMIf_trueI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "b"
  and "eval_exp_while_plus_minus_assign_impure_state (EWPM eit) sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_exp_while_plus_minus_assign_impure_state (WPMIf eic eit eif) s t s' v"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_impure_state_WPMIf_falseI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "\<not>b"
  and "eval_exp_while_plus_minus_assign_impure_state (EWPM eif) sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_exp_while_plus_minus_assign_impure_state (WPMIf eic eit eif) s t s' v"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_impure_state_WPMIfE[elim]:
  assumes "eval_exp_while_plus_minus_assign_impure_state (WPMIf eic eit eif) s t s' v"
  obtains sc b t1 t2 where "eval_eic eic s t1 sc b" "b" "eval_exp_while_plus_minus_assign_impure_state (EWPM eit) sc t2 s' v" "t = t1 + 1 + t2"
    | sc b t1 t2 where "eval_eic eic s t1 sc b" "\<not>b" "eval_exp_while_plus_minus_assign_impure_state (EWPM eif) sc t2 s' v" "t = t1 + 1 + t2"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_impure_state_While_trueI[intro]:
  assumes "eval_ewc ewc s t1 sc b" "b"
  and "eval_exp_while_plus_minus_assign_impure_state (EWPM ewpm) sc t2 s2 vew"
  and "eval_exp_while_plus_minus_assign_impure_state (WPMWhile ewc ewpm) s2 t3 s' v"
  and "t = t1 + 1 + t2 + t3"
  shows "eval_exp_while_plus_minus_assign_impure_state (WPMWhile ewc ewpm) s t s' v"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_impure_state_While_falseI[intro]:
  assumes "eval_ewc ewc s t' sc b" "\<not>b"
  and "t = t' + 1"
  and "s = s'"
  and "v = r_while"
  shows "eval_exp_while_plus_minus_assign_impure_state (WPMWhile ewc ewpm) s t s' v"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_impure_state_WPMWhileE[elim]:
  assumes "eval_exp_while_plus_minus_assign_impure_state (WPMWhile ewc ewpm) s t s' v"
  obtains t1 sc b t2 s2 vew t3 v3 where "eval_ewc ewc s t1 sc b" "b"
      "eval_exp_while_plus_minus_assign_impure_state (EWPM ewpm) sc t2 s2 vew"
      "eval_exp_while_plus_minus_assign_impure_state (WPMWhile ewc ewpm) s2 t3 s' v"
      "t = t1 + 1 + t2 + t3"
    | t' sc b where "eval_ewc ewc s t' sc b" "\<not>b" "s = s'" "v = r_while" "t = t' + 1"
  using assms
  apply (elim eval_exp_while_plus_minus_assign_impure_stateE)
  apply (erule eval_exp_while_plus_minus_WPMWhileE)
  by blast+

lemma eval_exp_while_plus_minus_assign_impure_state_induct[
  induct pred : eval_exp_while_plus_minus_assign_impure_state,
  case_names WPMV WPMSI WPMPlus WPMMinus WAssign WSeq WIf_true WIf_false WWhile_true WWhile_false]:
  assumes "eval_exp_while_plus_minus_assign_impure_state ewpm s t s' v"
  and "\<And>v s. P (WPMV v) s 0 s v"
  and "\<And>si s. P (WPMSI si) s 1 s (s si)"
  and "\<And>epl s t1 s1 v1 epr t2 s2 v2. eval_exp_while_plus_minus_assign_impure_state epl s t1 s1 v1 \<Longrightarrow>
    P epl s t1 s1 v1 \<Longrightarrow> eval_exp_while_plus_minus_assign_impure_state epr s1 t2 s2 v2 \<Longrightarrow>
    P epr s1 t2 s2 v2 \<Longrightarrow> P (WPMPlus epl epr) s (t1 + t2 + 1) s2 (v1 + v2)"
  and "\<And>eml s t1 s1 v1 emr t2 s2 v2. eval_exp_while_plus_minus_assign_impure_state eml s t1 s1 v1 \<Longrightarrow>
    P eml s t1 s1 v1 \<Longrightarrow> eval_exp_while_plus_minus_assign_impure_state emr s1 t2 s2 v2 \<Longrightarrow>
    P emr s1 t2 s2 v2 \<Longrightarrow> P (WPMMinus eml emr) s (t1 + t2 + 1) s2 (v1 - v2)"
  and "\<And>ea s t s' v si. eval_exp_while_plus_minus_assign_impure_state ea s t s' v \<Longrightarrow> P ea s t s' v \<Longrightarrow>
    P (WPMAssign si ea) s (t + 1) (s'(si := v)) v"
  and "\<And>esf s tf sf vf esb tb sb vb. eval_exp_while_plus_minus_assign_impure_state (EWPM esf) s tf sf vf \<Longrightarrow>
    P (EWPM esf) s tf sf vf \<Longrightarrow> eval_exp_while_plus_minus_assign_impure_state (EWPM esb) sf tb sb vb \<Longrightarrow>
    P (EWPM esb) sf tb sb vb \<Longrightarrow> P (WPMSeq esf esb) s (tf + tb) sb vb"
  and "\<And>eic s t1 sc b eit t2 s' v eif. eval_eic eic s t1 sc b \<Longrightarrow> b \<Longrightarrow>
    eval_exp_while_plus_minus_assign_impure_state (EWPM eit) sc t2 s' v \<Longrightarrow>
    P (EWPM eit) sc t2 s' v \<Longrightarrow> P (WPMIf eic eit eif) s (t1 + 1 + t2) s' v"
  and "\<And>eic s t1 sc b eif t2 s' v eit. eval_eic eic s t1 sc b \<Longrightarrow> \<not>b \<Longrightarrow>
    eval_exp_while_plus_minus_assign_impure_state (EWPM eif) sc t2 s' v \<Longrightarrow>
    P (EWPM eif) sc t2 s' v \<Longrightarrow> P (WPMIf eic eit eif) s (t1 + 1 + t2) s' v"
  and "\<And>ewc ewpm s1 t1 sc b t2 s2 vew t3 s3 v3. eval_ewc ewc s1 t1 sc b \<Longrightarrow> b \<Longrightarrow>
    eval_exp_while_plus_minus_assign_impure_state (EWPM ewpm) sc t2 s2 vew \<Longrightarrow>
    P (EWPM ewpm) sc t2 s2 vew \<Longrightarrow> eval_exp_while_plus_minus_assign_impure_state (WPMWhile ewc ewpm) s2 t3 s3 v3 \<Longrightarrow>
    P (WPMWhile ewc ewpm) s2 t3 s3 v3 \<Longrightarrow> P (WPMWhile ewc ewpm) s1 (t1 + 1 + t2 + t3) s3 v3"
  and "\<And>ewc ew s t sc b. eval_ewc ewc s t sc b \<Longrightarrow> \<not>b \<Longrightarrow> P (WPMWhile ewc ew) s (t + 1) s r_while"
  shows "P ewpm s t s' v"
using assms(1)
apply (elim eval_exp_while_plus_minus_assign_impure_stateE)
proof (induction ewpm s t s' v rule: eval_exp_while_plus_minus_induct)
  note mono = mp[OF eval_exp_while_plus_minus_mono[of _ eval_exp_while_plus_minus_assign_impure_state], rotated -1]
  case (WAssign ea s t s' v si)
  moreover then have "P ea s t s' v"
  proof (induction rule: eval_exp_while_plus_minus_assign_impure_state.induct)
    case (eval_exp_while_plus_minus_assign_impure_state e s t s' v)
    then show ?case
    proof (induction e s t s' v rule: eval_exp_while_plus_minus_induct)
      case (WPMPlus epl s t1 s1 v1 epr t2 s2 v2)
      moreover have "eval_exp_while_plus_minus_assign_impure_state epl s t1 s1 v1"
        using mono[OF WPMPlus(1)] by blast
      moreover have "eval_exp_while_plus_minus_assign_impure_state epr s1 t2 s2 v2"
        using mono[OF WPMPlus(2)] by blast
      ultimately show ?case by (blast intro: assms)
    next
      case (WPMMinus eml s t1 s1 v1 emr t2 s2 v2)
      moreover have "eval_exp_while_plus_minus_assign_impure_state eml s t1 s1 v1"
        using mono[OF WPMMinus(1)] by blast
      moreover have "eval_exp_while_plus_minus_assign_impure_state emr s1 t2 s2 v2"
        using mono[OF WPMMinus(2)] by blast
      ultimately show ?case by (blast intro: assms)
    next
      case (WSeq esf s tf sf vf esb tb sb vb)
      moreover have "eval_exp_while_plus_minus_assign_impure_state (EWPM esf) s tf sf vf"
        using mono[OF WSeq(1)] by blast
      moreover have "eval_exp_while_plus_minus_assign_impure_state (EWPM esb) sf tb sb vb"
        using mono[OF WSeq(2)] by blast
      ultimately show ?case by (blast intro: assms)
    next
      case (WIf_true eic s t1 sc b eit t2 s' v eif)
      moreover have "eval_exp_while_plus_minus_assign_impure_state (EWPM eit) sc t2 s' v"
        using mono[OF WIf_true(3)] by blast+
      ultimately show ?case by (blast intro: assms)
    next
      case (WIf_false eic s t1 sc b eif t2 s' v eit)
      moreover have "eval_exp_while_plus_minus_assign_impure_state (EWPM eif) sc t2 s' v"
        using mono[OF WIf_false(3)] by blast+
      ultimately show ?case by (blast intro: assms)
    next
      case (WWhile_true ewc ewpm s1 t1 sc b t2 s2 vew t3 s3 v3)
      moreover have "eval_exp_while_plus_minus_assign_impure_state (EWPM ewpm) sc t2 s2 vew"
        using mono[OF WWhile_true(3)] by blast
      moreover have "eval_exp_while_plus_minus_assign_impure_state (WPMWhile ewc ewpm) s2 t3 s3 v3"
        using mono[OF WWhile_true(4)] by blast
      ultimately show ?case by (blast intro: assms)
    qed (blast intro: assms)+
  qed
  ultimately show ?case by (blast intro: assms)
qed (blast intro: assms)+

end

lemma eval_exp_while_plus_minus_assign_impure_state_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  and "\<And>e s t s' v. f2 e s t s' v \<longrightarrow> g2 e s t s' v"
  shows "eval_exp_while_plus_minus_assign_impure_state f1 f2 r_while e s t s' v \<longrightarrow> eval_exp_while_plus_minus_assign_impure_state g1 g2 r_while e s t s' v"
proof
  assume "eval_exp_while_plus_minus_assign_impure_state f1 f2 r_while e s t s' v"
  from this assms show "eval_exp_while_plus_minus_assign_impure_state g1 g2 r_while e s t s' v"
  proof (induction rule: eval_exp_while_plus_minus_assign_impure_state_induct)
    case WWhile_true
    then show ?case
    by - (rule eval_exp_while_plus_minus_assign_impure_state_While_trueI, fast+)
  qed fast+
qed


context
  fixes eval_eic :: "('t :: {zero,one,plus}, bool, 'si, 'sv :: {minus,plus}, 'eic) eval_time"
  and eval_ewc :: "('t, bool, 'si, 'sv, 'ewc) eval_time"
  and r_while :: "'sv"
begin

inductive eval_exp_while_plus_minus_assign_pure_state ::
  "('t, 'sv, 'si, 'sv, ('si, 'sv, 'eic, 'ewc) exp_while_plus_minus) eval_time"
where
  eval_exp_while_plus_minus_assign_pure_state[intro]:
    "eval_exp_while_plus_minus
      (eval_pure_state eval_exp_while_plus_minus_assign_pure_state) eval_eic eval_ewc r_while e s t s' v \<Longrightarrow>
    eval_exp_while_plus_minus_assign_pure_state e s t s' v"

inductive_cases eval_exp_while_plus_minus_assign_pure_stateE[elim]:
  "eval_exp_while_plus_minus_assign_pure_state e s t s' v"

lemma eval_exp_while_plus_minus_assign_pure_state_WPMVI[intro]:
  assumes "s = s'"
  and "v = v'"
  and "t = 0"
  shows "eval_exp_while_plus_minus_assign_pure_state (WPMV v) s t s' v'"
  using assms by auto

lemma eval_exp_while_plus_minus_assign_pure_state_WPMVE[elim]:
  assumes "eval_exp_while_plus_minus_assign_pure_state (WPMV v) s t s' v'"
  obtains "s = s'" "v = v'" "t = 0"
  using assms by auto

lemma eval_exp_while_plus_minus_assign_pure_state_WPMSII[intro]:
  assumes "s = s'"
  and "v' = s si"
  and "t = 1"
  shows "eval_exp_while_plus_minus_assign_pure_state (WPMSI si) s t s' v'"
  using assms by auto

lemma eval_exp_while_plus_minus_assign_pure_state_WPMSIE[elim]:
  assumes "eval_exp_while_plus_minus_assign_pure_state (WPMSI si) s t s' v'"
  obtains "s = s'" "v' = s si" "t = 1"
  using assms by auto

lemma eval_exp_while_plus_minus_assign_pure_state_WPMPlusI[intro]:
  assumes "eval_exp_while_plus_minus_assign_pure_state epl s t1 s1 v1"
  and "eval_exp_while_plus_minus_assign_pure_state epr s1 t2 s2 v2"
  and "s' = s2"
  and "v = v1 + v2"
  and "t = t1 + t2 + 1"
  shows "eval_exp_while_plus_minus_assign_pure_state (WPMPlus epl epr) s t s' v"
  using assms by auto

lemma eval_exp_while_plus_minus_assign_pure_state_WPMPlusE[elim]:
  assumes "eval_exp_while_plus_minus_assign_pure_state (WPMPlus epl epr) s t s' v"
  obtains t1 s1 v1 t2 s2 v2 where "eval_exp_while_plus_minus_assign_pure_state epl s t1 s1 v1"
    "eval_exp_while_plus_minus_assign_pure_state epr s1 t2 s2 v2" "s' = s2" "v = v1 + v2" "t = t1 + t2 + 1"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_pure_state_WPMMinusI[intro]:
  assumes "eval_exp_while_plus_minus_assign_pure_state eml s t1 s1 v1"
  and "eval_exp_while_plus_minus_assign_pure_state emr s1 t2 s2 v2"
  and "s' = s2"
  and "v = v1 - v2"
  and "t = t1 + t2 + 1"
  shows "eval_exp_while_plus_minus_assign_pure_state (WPMMinus eml emr) s t s' v"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_pure_state_WPMMinusE[elim]:
  assumes "eval_exp_while_plus_minus_assign_pure_state (WPMMinus eml emr) s t s' v"
  obtains t1 s1 v1 t2 s2 v2 where "eval_exp_while_plus_minus_assign_pure_state eml s t1 s1 v1"
    "eval_exp_while_plus_minus_assign_pure_state emr s1 t2 s2 v2" "s' = s2" "v = v1 - v2" "t = t1 + t2 + 1"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_pure_state_WPMAssignI[intro]:
  assumes "eval_exp_while_plus_minus_assign_pure_state ea s t' s'' v"
  and "s' = s(si := v)"
  and "t = t' + 1"
  shows "eval_exp_while_plus_minus_assign_pure_state (WPMAssign si ea) s t s' v"
  using assms by auto

lemma eval_exp_while_plus_minus_assign_pure_state_WPMAssignE[elim]:
  assumes "eval_exp_while_plus_minus_assign_pure_state (WPMAssign si ea) s t s' v"
  obtains t' s'' v where "eval_exp_while_plus_minus_assign_pure_state ea s t' s'' v"
    "s' = s(si := v)" "t = t' + 1"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_pure_state_WPMSeqI[intro]:
  assumes "eval_exp_while_plus_minus_assign_pure_state (EWPM esf) s tf sf vf"
  and "eval_exp_while_plus_minus_assign_pure_state (EWPM esb) sf tb s' v"
  and "t = tf + tb"
  shows "eval_exp_while_plus_minus_assign_pure_state (WPMSeq esf esb) s t s' v"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_pure_state_WPMSeqE[elim]:
  assumes "eval_exp_while_plus_minus_assign_pure_state (WPMSeq esf esb) s t s' v"
  obtains tf sf vf tb where "eval_exp_while_plus_minus_assign_pure_state (EWPM esf) s tf sf vf"
    "eval_exp_while_plus_minus_assign_pure_state (EWPM esb) sf tb s' v" "t = tf + tb"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_pure_state_WPMIf_trueI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "b"
  and "eval_exp_while_plus_minus_assign_pure_state (EWPM eit) sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_exp_while_plus_minus_assign_pure_state (WPMIf eic eit eif) s t s' v"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_pure_state_WPMIf_falseI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "\<not>b"
  and "eval_exp_while_plus_minus_assign_pure_state (EWPM eif) sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_exp_while_plus_minus_assign_pure_state (WPMIf eic eit eif) s t s' v"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_pure_state_WPMIfE[elim]:
  assumes "eval_exp_while_plus_minus_assign_pure_state (WPMIf eic eit eif) s t s' v"
  obtains sc b t1 t2 where "eval_eic eic s t1 sc b" "b" "eval_exp_while_plus_minus_assign_pure_state (EWPM eit) sc t2 s' v" "t = t1 + 1 + t2"
    | sc b t1 t2 where "eval_eic eic s t1 sc b" "\<not>b" "eval_exp_while_plus_minus_assign_pure_state (EWPM eif) sc t2 s' v" "t = t1 + 1 + t2"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_pure_state_While_trueI[intro]:
  assumes "eval_ewc ewc s t1 sc b" "b"
  and "eval_exp_while_plus_minus_assign_pure_state (EWPM ewpm) sc t2 s2 vew"
  and "eval_exp_while_plus_minus_assign_pure_state (WPMWhile ewc ewpm) s2 t3 s' v"
  and "t = t1 + 1 + t2 + t3"
  shows "eval_exp_while_plus_minus_assign_pure_state (WPMWhile ewc ewpm) s t s' v"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_pure_state_While_falseI[intro]:
  assumes "eval_ewc ewc s t' sc b" "\<not>b"
  and "t = t' + 1"
  and "s = s'"
  and "v = r_while"
  shows "eval_exp_while_plus_minus_assign_pure_state (WPMWhile ewc ewpm) s t s' v"
  using assms by blast

lemma eval_exp_while_plus_minus_assign_pure_state_WPMWhileE[elim]:
  assumes "eval_exp_while_plus_minus_assign_pure_state (WPMWhile ewc ewpm) s t s' v"
  obtains t1 sc b t2 s2 vew t3 v3 where "eval_ewc ewc s t1 sc b" "b"
      "eval_exp_while_plus_minus_assign_pure_state (EWPM ewpm) sc t2 s2 vew"
      "eval_exp_while_plus_minus_assign_pure_state (WPMWhile ewc ewpm) s2 t3 s' v"
      "t = t1 + 1 + t2 + t3"
    | t' sc b where "eval_ewc ewc s t' sc b" "\<not>b" "s = s'" "v = r_while" "t = t' + 1"
  using assms
  apply (elim eval_exp_while_plus_minus_assign_pure_stateE)
  apply (erule eval_exp_while_plus_minus_WPMWhileE)
  by blast+

lemma eval_exp_while_plus_minus_assign_pure_state_induct[
  induct pred : eval_exp_while_plus_minus_assign_pure_state,
  case_names WPMV WPMSI WPMPlus WPMMinus WAssign WSeq WIf_true WIf_false WWhile_true WWhile_false]:
  assumes "eval_exp_while_plus_minus_assign_pure_state ewpm s t s' v"
  and "\<And>v s. P (WPMV v) s 0 s v"
  and "\<And>si s. P (WPMSI si) s 1 s (s si)"
  and "\<And>epl s t1 s1 v1 epr t2 s2 v2. eval_exp_while_plus_minus_assign_pure_state epl s t1 s1 v1 \<Longrightarrow>
    P epl s t1 s1 v1 \<Longrightarrow> eval_exp_while_plus_minus_assign_pure_state epr s1 t2 s2 v2 \<Longrightarrow>
    P epr s1 t2 s2 v2 \<Longrightarrow> P (WPMPlus epl epr) s (t1 + t2 + 1) s2 (v1 + v2)"
  and "\<And>eml s t1 s1 v1 emr t2 s2 v2. eval_exp_while_plus_minus_assign_pure_state eml s t1 s1 v1 \<Longrightarrow>
    P eml s t1 s1 v1 \<Longrightarrow> eval_exp_while_plus_minus_assign_pure_state emr s1 t2 s2 v2 \<Longrightarrow>
    P emr s1 t2 s2 v2 \<Longrightarrow> P (WPMMinus eml emr) s (t1 + t2 + 1) s2 (v1 - v2)"
  and "\<And>ea s t s' v si. eval_exp_while_plus_minus_assign_pure_state ea s t s' v \<Longrightarrow> P ea s t s' v \<Longrightarrow>
    P (WPMAssign si ea) s (t + 1) (s(si := v)) v"
  and "\<And>esf s tf sf vf esb tb sb vb. eval_exp_while_plus_minus_assign_pure_state (EWPM esf) s tf sf vf \<Longrightarrow>
    P (EWPM esf) s tf sf vf \<Longrightarrow> eval_exp_while_plus_minus_assign_pure_state (EWPM esb) sf tb sb vb \<Longrightarrow>
    P (EWPM esb) sf tb sb vb \<Longrightarrow> P (WPMSeq esf esb) s (tf + tb) sb vb"
  and "\<And>eic s t1 sc b eit t2 s' v eif. eval_eic eic s t1 sc b \<Longrightarrow> b \<Longrightarrow>
    eval_exp_while_plus_minus_assign_pure_state (EWPM eit) sc t2 s' v \<Longrightarrow>
    P (EWPM eit) sc t2 s' v \<Longrightarrow> P (WPMIf eic eit eif) s (t1 + 1 + t2) s' v"
  and "\<And>eic s t1 sc b eif t2 s' v eit. eval_eic eic s t1 sc b \<Longrightarrow> \<not>b \<Longrightarrow>
    eval_exp_while_plus_minus_assign_pure_state (EWPM eif) sc t2 s' v \<Longrightarrow>
    P (EWPM eif) sc t2 s' v \<Longrightarrow> P (WPMIf eic eit eif) s (t1 + 1 + t2) s' v"
  and "\<And>ewc ewpm s1 t1 sc b t2 s2 vew t3 s3 v3. eval_ewc ewc s1 t1 sc b \<Longrightarrow> b \<Longrightarrow>
    eval_exp_while_plus_minus_assign_pure_state (EWPM ewpm) sc t2 s2 vew \<Longrightarrow>
    P (EWPM ewpm) sc t2 s2 vew \<Longrightarrow> eval_exp_while_plus_minus_assign_pure_state (WPMWhile ewc ewpm) s2 t3 s3 v3 \<Longrightarrow>
    P (WPMWhile ewc ewpm) s2 t3 s3 v3 \<Longrightarrow> P (WPMWhile ewc ewpm) s1 (t1 + 1 + t2 + t3) s3 v3"
  and "\<And>ewc ew s t sc b. eval_ewc ewc s t sc b \<Longrightarrow> \<not>b \<Longrightarrow> P (WPMWhile ewc ew) s (t + 1) s r_while"
  shows "P ewpm s t s' v"
using assms(1)
apply (elim eval_exp_while_plus_minus_assign_pure_stateE)
proof (induction ewpm s t s' v rule: eval_exp_while_plus_minus_induct)
  note mono = mp[OF eval_exp_while_plus_minus_mono[of _ "eval_pure_state eval_exp_while_plus_minus_assign_pure_state"], rotated -1]
  case (WAssign ea s t s' v si)
  then obtain s'' where "eval_exp_while_plus_minus_assign_pure_state ea s t s'' v" "s' = s" by auto
  moreover from this(1) have "P ea s t s'' v"
  proof (induction rule: eval_exp_while_plus_minus_assign_pure_state.induct)
    case (eval_exp_while_plus_minus_assign_pure_state e s t s' v)
    then show ?case
    proof (induction e s t s' v rule: eval_exp_while_plus_minus_induct)
      case (WPMPlus epl s t1 s1 v1 epr t2 s2 v2)
      moreover have "eval_exp_while_plus_minus_assign_pure_state epl s t1 s1 v1"
        using mono[OF WPMPlus(1)] by blast
      moreover have "eval_exp_while_plus_minus_assign_pure_state epr s1 t2 s2 v2"
        using mono[OF WPMPlus(2)] by blast
      ultimately show ?case by (blast intro: assms)
    next
      case (WPMMinus eml s t1 s1 v1 emr t2 s2 v2)
      moreover have "eval_exp_while_plus_minus_assign_pure_state eml s t1 s1 v1"
        using mono[OF WPMMinus(1)] by blast
      moreover have "eval_exp_while_plus_minus_assign_pure_state emr s1 t2 s2 v2"
        using mono[OF WPMMinus(2)] by blast
      ultimately show ?case by (blast intro: assms)
    next
      case (WSeq esf s tf sf vf esb tb sb vb)
      moreover have "eval_exp_while_plus_minus_assign_pure_state (EWPM esf) s tf sf vf"
        using mono[OF WSeq(1)] by blast
      moreover have "eval_exp_while_plus_minus_assign_pure_state (EWPM esb) sf tb sb vb"
        using mono[OF WSeq(2)] by blast
      ultimately show ?case by (blast intro: assms)
    next
      case (WIf_true eic s t1 sc b eit t2 s' v eif)
      moreover have "eval_exp_while_plus_minus_assign_pure_state (EWPM eit) sc t2 s' v"
        using mono[OF WIf_true(3)] by blast+
      ultimately show ?case by (blast intro: assms)
    next
      case (WIf_false eic s t1 sc b eif t2 s' v eit)
      moreover have "eval_exp_while_plus_minus_assign_pure_state (EWPM eif) sc t2 s' v"
        using mono[OF WIf_false(3)] by blast+
      ultimately show ?case by (blast intro: assms)
    next
      case (WWhile_true ewc ewpm s1 t1 sc b t2 s2 vew t3 s3 v3)
      moreover have "eval_exp_while_plus_minus_assign_pure_state (EWPM ewpm) sc t2 s2 vew"
        using mono[OF WWhile_true(3)] by blast
      moreover have "eval_exp_while_plus_minus_assign_pure_state (WPMWhile ewc ewpm) s2 t3 s3 v3"
        using mono[OF WWhile_true(4)] by blast
      ultimately show ?case by (blast intro: assms)
    qed (blast intro: assms)+
  qed
  ultimately show ?case by (subst \<open>s' = s\<close>) (blast intro: assms)
qed (blast intro: assms)+

end

lemma eval_exp_while_plus_minus_assign_pure_state_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  and "\<And>e s t s' v. f2 e s t s' v \<longrightarrow> g2 e s t s' v"
  shows "eval_exp_while_plus_minus_assign_pure_state f1 f2 r_while e s t s' v \<longrightarrow> eval_exp_while_plus_minus_assign_pure_state g1 g2 r_while e s t s' v"
proof
  assume "eval_exp_while_plus_minus_assign_pure_state f1 f2 r_while e s t s' v"
  from this assms show "eval_exp_while_plus_minus_assign_pure_state g1 g2 r_while e s t s' v"
  proof (induction rule: eval_exp_while_plus_minus_assign_pure_state_induct)
    case WWhile_true
    then show ?case
    by - (rule eval_exp_while_plus_minus_assign_pure_state_While_trueI, fast+)
  qed fast+
qed


end
