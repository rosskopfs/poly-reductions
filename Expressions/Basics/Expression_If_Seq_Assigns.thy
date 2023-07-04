\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expression_If_Seq_Assigns
  imports Expression_If_Seq_Assigns_Base
begin

datatype ('si, 'eb, 'ea, 'eic) exp_if_seq_assign = EISA
  "('si, 'eb, 'ea, 'eic,
    ('si, 'eb, 'ea, 'eic) exp_if_seq_assign) exp_if_seq_assign_base_hom"

context
  fixes eval_eb :: "('t :: {one,plus}, 'sv, 'si, 'sv, 'eb) eval_time"
  and eval_ea :: "('t, 'sv, 'si, 'sv, 'ea) eval_time"
  and eval_eic :: "('t, bool, 'si, 'sv, 'eic) eval_time"
begin

inductive eval_exp_if_seq_assign ::
  "('t, 'sv, 'si, 'sv, ('si, 'eb, 'ea, 'eic) exp_if_seq_assign) eval_time"
where
  eval_exp_if_seq_assign_EISA[intro]:
    "eval_exp_if_seq_assign_base_hom eval_eb eval_ea eval_eic eval_exp_if_seq_assign e s t s' v \<Longrightarrow>
    eval_exp_if_seq_assign (EISA e) s t s' v"

inductive_cases eval_exp_if_seq_assign_EISAE[elim]: "eval_exp_if_seq_assign (EISA e) s t s' v"

definition [exp_smart_constructor_def]: "ISABase eb \<equiv> EISA (ISABBase eb)"
definition [exp_smart_constructor_def]: "ISAAssign si ea \<equiv> EISA (ISABAssign si ea)"
definition [exp_smart_constructor_def]: "ISASeq esf esb \<equiv> EISA (ISABSeq esf esb)"
definition [exp_smart_constructor_def]: "ISAIf eic eit eif \<equiv> EISA (ISABIf eic eit eif)"

lemma eval_exp_if_seq_assign_base_esf_hom_ISABaseI[intro]:
  assumes "eval_eb eb s t s' v"
  shows "eval_exp_if_seq_assign (ISABase eb) s t s' v"
  using assms unfolding ISABase_def by auto

lemma eval_exp_if_seq_assign_base_esf_hom_ISABaseE[elim]:
  assumes "eval_exp_if_seq_assign (ISABase eb) s t s' v"
  obtains "eval_eb eb s t s' v"
  using assms unfolding ISABase_def by auto

lemma eval_exp_if_seq_assign_ISAAssignI[intro]:
  assumes "eval_ea ea s t' sea v"
  and "s' = sea(si := v)"
  and "t = t' + 1"
  shows "eval_exp_if_seq_assign (ISAAssign si ea) s t s' v"
  using assms unfolding ISAAssign_def by auto

lemma eval_exp_if_seq_assign_ISAAssignE[elim]:
  assumes "eval_exp_if_seq_assign (ISAAssign si ea) s t s' v"
  obtains t' sae v where "eval_ea ea s t' sae v" "s' = sae(si := v)" "t = t' + 1"
  using assms unfolding ISAAssign_def by blast

lemma eval_exp_if_seq_assign_ISASeqI[intro]:
  assumes "eval_exp_if_seq_assign esf s tf sf vf"
  and "eval_exp_if_seq_assign esb sf tb s' v"
  and "t = tf + tb"
  shows "eval_exp_if_seq_assign (ISASeq esf esb) s t s' v"
  using assms unfolding ISASeq_def by auto

lemma eval_exp_if_seq_assign_ISASeqE[elim]:
  assumes "eval_exp_if_seq_assign (ISASeq esf esb) s t s' v"
  obtains tf sf vf tb where "eval_exp_if_seq_assign esf s tf sf vf" "eval_exp_if_seq_assign esb sf tb s' v" "t = tf + tb"
  using assms unfolding ISASeq_def by blast

lemma eval_exp_if_seq_assign_ISAIf_trueI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "b"
  and "eval_exp_if_seq_assign eit sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_exp_if_seq_assign (ISAIf eic eit eif) s t s' v"
  using assms unfolding ISAIf_def by auto

lemma eval_exp_if_seq_assign_ISAIf_falseI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "\<not>b"
  and "eval_exp_if_seq_assign eif sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_exp_if_seq_assign (ISAIf eic eit eif) s t s' v"
  using assms unfolding ISAIf_def by auto

lemma eval_exp_if_seq_assign_ISAIfE[elim]:
  assumes "eval_exp_if_seq_assign (ISAIf eic eit eif) s t s' v"
  obtains sc b t1 t2 where "eval_eic eic s t1 sc b" "b" "eval_exp_if_seq_assign eit sc t2 s' v" "t = t1 + 1 + t2"
    | sc b t1 t2 where "eval_eic eic s t1 sc b" "\<not>b" "eval_exp_if_seq_assign eif sc t2 s' v" "t = t1 + 1 + t2"
  using assms unfolding ISAIf_def by blast

lemma eval_exp_if_seq_assign_induct[induct pred : eval_exp_if_seq_assign, case_names
  ISABase ISAAssign ISASeq ISAIf_true ISAIf_false]:
  assumes "eval_exp_if_seq_assign eb s t s' v"
  and "\<And>eb s t s' v. eval_eb eb s t s' v \<Longrightarrow> P (ISABase eb) s t s' v"
  and "\<And>ea s t s' v si. eval_ea ea s t s' v \<Longrightarrow> P (ISAAssign si ea) s (t + 1) (s'(si := v)) v"
  and "\<And>esf s tf sf vf esb tb sb vb. eval_exp_if_seq_assign esf s tf sf vf \<Longrightarrow> P esf s tf sf vf \<Longrightarrow>
    eval_exp_if_seq_assign esb sf tb sb vb \<Longrightarrow> P esb sf tb sb vb \<Longrightarrow> P (ISASeq esf esb) s (tf + tb) sb vb"
  and "\<And>eic s t1 sc b eit t2 s' v eif. eval_eic eic s t1 sc b \<Longrightarrow> b \<Longrightarrow> eval_exp_if_seq_assign eit sc t2 s' v \<Longrightarrow>
    P eit sc t2 s' v \<Longrightarrow> P (ISAIf eic eit eif) s (t1 + 1 + t2) s' v"
  and "\<And>eic s t1 sc b eif t2 s' v eit. eval_eic eic s t1 sc b \<Longrightarrow> \<not>b \<Longrightarrow> eval_exp_if_seq_assign eif sc t2 s' v \<Longrightarrow>
    P eif sc t2 s' v \<Longrightarrow> P (ISAIf eic eit eif) s (t1 + 1 + t2) s' v"
  shows "P eb s t s' v"
using assms
proof (elim eval_exp_if_seq_assign.induct, goal_cases)
  case 1 then show ?case
    by (elim eval_exp_if_seq_assign_base_hom_induct)
    (fold exp_smart_constructor_def, blast+, auto)
qed

end

lemma eval_exp_if_seq_assign_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  and "\<And>e s t s' v. f2 e s t s' v \<longrightarrow> g2 e s t s' v"
  and "\<And>e s t s' v. f3 e s t s' v \<longrightarrow> g3 e s t s' v"
  shows "eval_exp_if_seq_assign f1 f2 f3 e s t s' v \<longrightarrow> eval_exp_if_seq_assign g1 g2 g3 e s t s' v"
proof
  assume "eval_exp_if_seq_assign f1 f2 f3 e s t s' v"
  from this assms show "eval_exp_if_seq_assign g1 g2 g3 e s t s' v"
  by (induction rule: eval_exp_if_seq_assign_induct) fast+
qed


end