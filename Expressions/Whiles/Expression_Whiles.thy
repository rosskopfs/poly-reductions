\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expression_Whiles
  imports
    Expression_If_Seq_Assigns_Base
    Expression_Whiles_Base
begin

datatype ('si, 'eb, 'ea, 'eic, 'ewc) exp_while = EW
  "(('si, 'eb, 'ea, 'eic,
      ('si, 'eb, 'ea, 'eic, 'ewc) exp_while) exp_if_seq_assign_base_hom,
    'ewc,
    ('si, 'eb, 'ea, 'eic, 'ewc) exp_while) exp_while_base"

context
  fixes eval_eb :: "('t :: {one,plus}, 'sv, 'si, 'sv, 'eb) eval_time"
  and eval_ea :: "('t, 'sv, 'si, 'sv, 'ea) eval_time"
  and eval_eic :: "('t, bool, 'si, 'sv, 'eic) eval_time"
  and eval_ewc :: "('t, bool, 'si, 'sv, 'ewc) eval_time"
  and eval_ewhile :: "('t, 'sv, 'si, 'sv, 'e) eval_time"
  and r_while :: "'sv"
begin

definition "eval_ewb_while \<equiv>
  eval_exp_while_base (eval_exp_if_seq_assign_base_hom eval_eb eval_ea eval_eic eval_ewhile)
  eval_ewc eval_ewhile r_while"

definition [exp_smart_constructor_def]: "WBBase eb \<equiv> EWBase (ISABBase eb)"
definition [exp_smart_constructor_def]: "WBAssign si ea \<equiv> EWBase (ISABAssign si ea)"
definition [exp_smart_constructor_def]: "WBSeq esf esb \<equiv> EWBase (ISABSeq esf esb)"
definition [exp_smart_constructor_def]: "WBIf eic eit eif \<equiv> EWBase (ISABIf eic eit eif)"

lemma eval_ewb_while_WBBaseI[intro]:
  assumes "eval_eb eb s t s' v"
  shows "eval_ewb_while (WBBase eb) s t s' v"
  using assms unfolding eval_ewb_while_def WBBase_def by auto

lemma eval_ewb_while_WBBaseE[elim]:
  assumes "eval_ewb_while (WBBase eb) s t s' v"
  obtains "eval_eb eb s t s' v"
  using assms unfolding eval_ewb_while_def WBBase_def by auto

lemma eval_ewb_while_WBAssignI[intro]:
  assumes "eval_ea ea s t' sea v"
  and "s' = sea(si := v)"
  and "t = t' + 1"
  shows "eval_ewb_while (WBAssign si ea) s t s' v"
  using assms unfolding eval_ewb_while_def WBAssign_def by auto

lemma eval_ewb_while_WBAssignE[elim]:
  assumes "eval_ewb_while (WBAssign si ea) s t s' v"
  obtains t' sae v where "eval_ea ea s t' sae v" "s' = sae(si := v)" "t = t' + 1"
  using assms unfolding eval_ewb_while_def WBAssign_def by blast

lemma eval_ewb_while_WBSeqI[intro]:
  assumes "eval_ewhile esf s tf sf vf"
  and "eval_ewhile esb sf tb s' v"
  and "t = tf + tb"
  shows "eval_ewb_while (WBSeq esf esb) s t s' v"
  using assms unfolding eval_ewb_while_def WBSeq_def by auto

lemma eval_ewb_while_WBSeqE[elim]:
  assumes "eval_ewb_while (WBSeq esf esb) s t s' v"
  obtains tf sf vf tb where "eval_ewhile esf s tf sf vf" "eval_ewhile esb sf tb s' v" "t = tf + tb"
  using assms unfolding eval_ewb_while_def WBSeq_def by blast

lemma eval_ewb_while_WBIf_trueI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "b"
  and "eval_ewhile eit sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_ewb_while (WBIf eic eit eif) s t s' v"
  using assms unfolding eval_ewb_while_def WBIf_def by auto

lemma eval_ewb_while_WBIf_falseI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "\<not>b"
  and " eval_ewhile eif sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_ewb_while (WBIf eic eit eif) s t s' v"
  using assms unfolding eval_ewb_while_def WBIf_def by auto

lemma eval_ewb_while_WBIfE[elim]:
  assumes "eval_ewb_while (WBIf eic eit eif) s t s' v"
   obtains sc b t1 t2 where "eval_eic eic s t1 sc b" "b" "eval_ewhile eit sc t2 s' v" "t = t1 + 1 + t2"
    | sc b t1 t2 where "eval_eic eic s t1 sc b" "\<not>b" "eval_ewhile eif sc t2 s' v" "t = t1 + 1 + t2"
  using assms unfolding eval_ewb_while_def WBIf_def by blast

lemma eval_ewb_while_While_trueI[intro]:
  assumes "eval_ewc ewc s t1 sc b" "b"
  and "eval_ewhile ew sc t2 s2 vew"
  and "eval_ewb_while (While ewc ew) s2 t3 s' v"
  and "t = t1 + 1 + t2 + t3"
  shows "eval_ewb_while (While ewc ew) s t s' v"
  using assms unfolding eval_ewb_while_def by auto

lemma eval_ewb_while_While_falseI[intro]:
  assumes "eval_ewc ewc s t' sc b" "\<not>b"
  and "t = t' + 1"
  and "s = s'"
  and "v = r_while"
  shows "eval_ewb_while (While ewc ew) s t s' v"
  using assms unfolding eval_ewb_while_def by auto

lemma eval_ewb_while_WhileE[elim]:
  assumes "eval_ewb_while (While ewc ew) s t s' v"
  obtains t1 sc b t2 s2 vew t3 v3 where "eval_ewc ewc s t1 sc b" "b" "eval_ewhile ew sc t2 s2 vew"
      "eval_ewb_while (While ewc ew) s2 t3 s' v"
      "t = t1 + 1 + t2 + t3"
    | t' sc b where "eval_ewc ewc s t' sc b" "\<not>b" "s = s'" "v = r_while" "t = t' + 1"
  using assms unfolding eval_ewb_while_def by auto

end

lemma eval_ewb_while_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  and "\<And>e s t s' v. f2 e s t s' v \<longrightarrow> g2 e s t s' v"
  and "\<And>e s t s' v. f3 e s t s' v \<longrightarrow> g3 e s t s' v"
  and "\<And>e s t s' v. f4 e s t s' v \<longrightarrow> g4 e s t s' v"
  and "\<And>e s t s' v. f5 e s t s' v \<longrightarrow> g5 e s t s' v"
  shows "eval_ewb_while f1 f2 f3 f4 f5 r_while e s t s' v \<longrightarrow> eval_ewb_while g1 g2 g3 g4 g5 r_while e s t s' v"
  unfolding eval_ewb_while_def by (intro eval_exp_while_base_mono eval_exp_if_seq_assign_base_hom_mono assms)

context
  fixes eval_eb :: "('t :: {one,plus}, 'sv, 'si, 'sv, 'eb) eval_time"
  and eval_ea :: "('t, 'sv, 'si, 'sv, 'ea) eval_time"
  and eval_eic :: "('t, bool, 'si, 'sv, 'eic) eval_time"
  and eval_ewc :: "('t, bool, 'si, 'sv, 'ewc) eval_time"
  and r_while :: "'sv"
begin

inductive eval_exp_while ::
  "('t, 'sv, 'si, 'sv, ('si, 'eb, 'ea, 'eic, 'ewc) exp_while) eval_time"
where
  eval_exp_while_EW[intro]: "eval_ewb_while eval_eb eval_ea eval_eic eval_ewc eval_exp_while r_while e s t s' v \<Longrightarrow>
    eval_exp_while (EW e) s t s' v"

inductive_cases eval_exp_while_EWE[elim]: "eval_exp_while (EW e) s t s' v"

definition [exp_smart_constructor_def]: "WBase eb \<equiv> EW (WBBase eb)"
definition [exp_smart_constructor_def]: "WAssign si ea \<equiv> EW (WBAssign si ea)"
definition [exp_smart_constructor_def]: "WIf eic eit eif \<equiv> EW (WBIf eic eit eif)"
definition [exp_smart_constructor_def]: "WSeq esf esb \<equiv> EW (WBSeq esf esb)"
definition [exp_smart_constructor_def]: "WWhile ewc ew \<equiv> EW (While ewc ew)"

lemma eval_exp_while_WBaseI[intro]:
  assumes "eval_eb eb s t s' v"
  shows "eval_exp_while (WBase eb) s t s' v"
  using assms unfolding WBase_def by auto

lemma eval_exp_while_WBaseE[elim]:
  assumes "eval_exp_while (WBase eb) s t s' v"
  obtains "eval_eb eb s t s' v"
  using assms unfolding WBase_def by auto

lemma eval_exp_while_WAssignI[intro]:
  assumes "eval_ea ea s t' sea v"
  and "s' = sea(si := v)"
  and "t = t' + 1"
  shows "eval_exp_while (WAssign si ea) s t s' v"
  using assms unfolding WAssign_def by auto

lemma eval_exp_while_WAssignE[elim]:
  assumes "eval_exp_while (WAssign si ea) s t s' v"
  obtains t' sae v where "eval_ea ea s t' sae v" "s' = sae(si := v)" "t = t' + 1"
  using assms unfolding WAssign_def by blast

lemma eval_exp_while_WSeqI[intro]:
  assumes "eval_exp_while esf s tf sf vf"
  and "eval_exp_while esb sf tb s' v"
  and "t = tf + tb"
  shows "eval_exp_while (WSeq esf esb) s t s' v"
  using assms unfolding WSeq_def by auto

lemma eval_exp_while_WSeqE[elim]:
  assumes "eval_exp_while (WSeq esf esb) s t s' v"
  obtains tf sf vf tb where "eval_exp_while esf s tf sf vf" "eval_exp_while esb sf tb s' v" "t = tf + tb"
  using assms unfolding WSeq_def by blast

lemma eval_exp_while_WIf_trueI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "b"
  and "eval_exp_while eit sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_exp_while (WIf eic eit eif) s t s' v"
  using assms unfolding WIf_def by auto

lemma eval_exp_while_WIf_falseI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "\<not>b"
  and "eval_exp_while eif sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_exp_while (WIf eic eit eif) s t s' v"
  using assms unfolding WIf_def by auto

lemma eval_exp_while_WIfE[elim]:
  assumes "eval_exp_while (WIf eic eit eif) s t s' v"
  obtains sc b t1 t2 where "eval_eic eic s t1 sc b" "b" "eval_exp_while eit sc t2 s' v" "t = t1 + 1 + t2"
    | sc b t1 t2 where "eval_eic eic s t1 sc b" "\<not>b" "eval_exp_while eif sc t2 s' v" "t = t1 + 1 + t2"
  using assms unfolding WIf_def by blast

lemma eval_exp_while_While_trueI[intro]:
  assumes "eval_ewc ewc s t1 sc b" "b"
  and "eval_exp_while ew sc t2 s2 vew"
  and "eval_exp_while (WWhile ewc ew) s2 t3 s' v"
  and "t = t1 + 1 + t2 + t3"
  shows "eval_exp_while (WWhile ewc ew) s t s' v"
  using assms unfolding WWhile_def by auto

lemma eval_exp_while_While_falseI[intro]:
  assumes "eval_ewc ewc s t' sc b" "\<not>b"
  and "t = t' + 1"
  and "s = s'"
  and "v = r_while"
  shows "eval_exp_while (WWhile ewc ew) s t s' v"
  using assms unfolding WWhile_def by auto

lemma eval_exp_while_WWhileE[elim]:
  assumes "eval_exp_while (WWhile ewc ew) s t s' v"
  obtains t1 sc b t2 s2 vew t3 v3 where "eval_ewc ewc s t1 sc b" "b" "eval_exp_while ew sc t2 s2 vew"
      "eval_exp_while (WWhile ewc ew) s2 t3 s' v"
      "t = t1 + 1 + t2 + t3"
    | t' sc b where "eval_ewc ewc s t' sc b" "\<not>b" "s = s'" "v = r_while" "t = t' + 1"
  using assms unfolding WWhile_def
  by (elim eval_exp_while_EWE)
  (erule eval_ewb_while_WhileE, auto simp flip: WWhile_def dest: eval_exp_while_EW)

lemma eval_exp_while_induct[induct pred : eval_exp_while, case_names WBase WAssign WSeq WIf_true
  WIf_false WWhile_true WWhile_false]:
  assumes "eval_exp_while ew s t s' v"
  and "\<And>eb s t s' v. eval_eb eb s t s' v \<Longrightarrow> P (WBase eb) s t s' v"
  and "\<And>ea s t s' v si. eval_ea ea s t s' v \<Longrightarrow> P (WAssign si ea) s (t + 1) (s'(si := v)) v"
  and "\<And>esf s tf sf vf esb tb sb vb. eval_exp_while esf s tf sf vf \<Longrightarrow> P esf s tf sf vf \<Longrightarrow>
    eval_exp_while esb sf tb sb vb \<Longrightarrow> P esb sf tb sb vb \<Longrightarrow> P (WSeq esf esb) s (tf + tb) sb vb"
  and "\<And>eic s t1 sc b eit t2 s' v eif. eval_eic eic s t1 sc b \<Longrightarrow> b \<Longrightarrow> eval_exp_while eit sc t2 s' v \<Longrightarrow>
    P eit sc t2 s' v \<Longrightarrow> P (WIf eic eit eif) s (t1 + 1 + t2) s' v"
  and "\<And>eic s t1 sc b eif t2 s' v eit. eval_eic eic s t1 sc b \<Longrightarrow> \<not>b \<Longrightarrow> eval_exp_while eif sc t2 s' v \<Longrightarrow>
    P eif sc t2 s' v \<Longrightarrow> P (WIf eic eit eif) s (t1 + 1 + t2) s' v"
  and "\<And>ewc ew s1 t1 sc b t2 s2 vew t3 s3 v3. eval_ewc ewc s1 t1 sc b \<Longrightarrow> b \<Longrightarrow>
    eval_exp_while ew sc t2 s2 vew \<Longrightarrow> P ew sc t2 s2 vew \<Longrightarrow> eval_exp_while (WWhile ewc ew) s2 t3 s3 v3 \<Longrightarrow>
    P (WWhile ewc ew) s2 t3 s3 v3 \<Longrightarrow> P (WWhile ewc ew) s1 (t1 + 1 + t2 + t3) s3 v3"
  and "\<And>ewc ew s t sc b. eval_ewc ewc s t sc b \<Longrightarrow> \<not>b \<Longrightarrow> P (WWhile ewc ew) s (t + 1) s r_while"
  shows "P ew s t s' v"
using assms
proof (elim eval_exp_while.induct, goal_cases)
  case 1 then show ?case
  apply (subst (asm) eval_ewb_while_def)
  proof (erule eval_exp_while_base.induct, goal_cases)
    case 1 then show ?case
    proof (elim eval_exp_if_seq_assign_base_hom_induct, goal_cases)
      case 2 then show ?case by (fold exp_smart_constructor_def)
    qed (fold exp_smart_constructor_def, auto)
  next
    case (2 ewc s1 t1 sc b ew t2 s2 vew t3 s3 v3)
    then have
      "eval_ewb_while eval_eb eval_ea eval_eic eval_ewc eval_exp_while r_while (While ewc ew) s2 t3 s3 v3"
      apply (fold eval_ewb_while_def)
      apply (rule mp[OF eval_ewb_while_mono[of _ eval_eb _ eval_ea _ eval_eic _ eval_ewc _ eval_exp_while]])
      by auto
    then have "eval_exp_while (WWhile ewc ew) s2 t3 s3 v3" by (auto simp add: WWhile_def)
    with 2 show ?case by (auto simp flip: WWhile_def)
  qed (fold exp_smart_constructor_def)
qed

end

lemma eval_exp_while_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  and "\<And>e s t s' v. f2 e s t s' v \<longrightarrow> g2 e s t s' v"
  and "\<And>e s t s' v. f3 e s t s' v \<longrightarrow> g3 e s t s' v"
  and "\<And>e s t s' v. f4 e s t s' v \<longrightarrow> g4 e s t s' v"
  shows "eval_exp_while f1 f2 f3 f4 r_while e s t s' v \<longrightarrow> eval_exp_while g1 g2 g3 g4 r_while e s t s' v"
proof
  assume "eval_exp_while f1 f2 f3 f4 r_while e s t s' v"
  from this assms show "eval_exp_while g1 g2 g3 g4 r_while e s t s' v"
  proof (induction rule: eval_exp_while_induct)
    case WWhile_true
    then show ?case
    by - (rule eval_exp_while_While_trueI, fast+)
  qed fast+
qed

end