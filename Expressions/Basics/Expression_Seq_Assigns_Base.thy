\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expression_Seq_Assigns_Base
  imports
    Expression_Assigns_Base
    Expression_Seqs_Base
begin

datatype ('si, 'eb, 'ea, 'esf, 'esb) exp_seq_assign_base = ESAB
  "(('si, 'eb, 'ea) exp_assign_base,
    'esf, 'esb) exp_seq_base"

context
  fixes eval_eb :: "('t :: {one, plus}, 'sv, 'si, 'sv, 'eb) eval_time"
  and eval_ea :: "('t, 'sv, 'si, 'sv, 'ea) eval_time"
  and eval_esf :: "('t, 'sv, 'si, 'sv, 'esf) eval_time"
  and eval_esb :: "('t, 'sv, 'si, 'sv, 'esb) eval_time"
begin

definition "eval_esb_seq_assign_base \<equiv>
  eval_exp_seq_base (eval_exp_assign_base eval_eb eval_ea) eval_esf eval_esb"

definition [exp_smart_constructor_def]: "SABBBase eb \<equiv> ESBase (EABase eb)"
definition [exp_smart_constructor_def]: "SABBAssign si ea \<equiv> ESBase (Assign si ea)"

lemma eval_esb_seq_assign_base_SABBBaseI[intro]:
  assumes "eval_eb eb s t s' v"
  shows "eval_esb_seq_assign_base (SABBBase eb) s t s' v"
  using assms unfolding eval_esb_seq_assign_base_def SABBBase_def by auto

lemma eval_esb_seq_assign_base_SABBBaseE[elim]:
  assumes "eval_esb_seq_assign_base (SABBBase eb) s t s' v"
  obtains "eval_eb eb s t s' v"
  using assms unfolding eval_esb_seq_assign_base_def SABBBase_def by auto

lemma eval_esb_seq_assign_base_SABBAssignI[intro]:
  assumes "eval_ea ea s t' sea v'"
  and "s' = sea(si := v)"
  and "v = v'"
  and "t = t' + 1"
  shows "eval_esb_seq_assign_base (SABBAssign si ea) s t s' v"
  using assms unfolding eval_esb_seq_assign_base_def SABBAssign_def by auto

lemma eval_esb_seq_assign_base_SABBAssignE[elim]:
  assumes "eval_esb_seq_assign_base (SABBAssign si ea) s t s' v"
  obtains t' sae v where "eval_ea ea s t' sae v" "s' = sae(si := v)" "t = t' + 1"
  using assms unfolding eval_esb_seq_assign_base_def SABBAssign_def by blast

lemma eval_esb_seq_assign_base_SeqI[intro]:
  assumes "eval_esf esf s tf sf vf"
  and "eval_esb esb sf tb s' v"
  and "t = tf + tb"
  shows "eval_esb_seq_assign_base (Seq esf esb) s t s' v"
  using assms unfolding eval_esb_seq_assign_base_def by blast

lemma eval_esb_seq_assign_base_SeqE[elim]:
  assumes "eval_esb_seq_assign_base (Seq esf esb) s t s' v"
  obtains tf sf vf tb where "eval_esf esf s tf sf vf" "eval_esb esb sf tb s' v" "t = tf + tb"
  using assms unfolding eval_esb_seq_assign_base_def by blast

lemma eval_esb_seq_assign_base_induct[induct pred : eval_esb_seq_assign_base,
  case_names SABBBase SABBAssign Seq]:
  assumes "eval_esb_seq_assign_base e s t s' v"
  and "\<And>eb s t s' v. eval_eb eb s t s' v \<Longrightarrow> P (SABBBase eb) s t s' v"
  and "\<And>ea s t s' v si. eval_ea ea s t s' v \<Longrightarrow> P (SABBAssign si ea) s (t + 1) (s'(si := v)) v"
  and "\<And>esf s tf sf vf esb tb sb vb. eval_esf esf s tf sf vf \<Longrightarrow>
    eval_esb esb sf tb sb vb \<Longrightarrow> P (Seq esf esb) s (tf + tb) sb vb"
  shows "P e s t s' v"
  using assms unfolding eval_esb_seq_assign_base_def
  by (elim eval_exp_seq_base.induct eval_exp_assign_base.induct)
  (fold exp_smart_constructor_def)

end

lemma eval_esb_seq_assign_base_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  and "\<And>e s t s' v. f2 e s t s' v \<longrightarrow> g2 e s t s' v"
  and "\<And>e s t s' v. f3 e s t s' v \<longrightarrow> g3 e s t s' v"
  and "\<And>e s t s' v. f4 e s t s' v \<longrightarrow> g4 e s t s' v"
  shows "eval_esb_seq_assign_base f1 f2 f3 f4 e s t s' v \<longrightarrow> eval_esb_seq_assign_base g1 g2 g3 g4 e s t s' v"
  unfolding eval_esb_seq_assign_base_def
  by (intro eval_exp_seq_base_mono eval_exp_assign_base_mono assms)

context
  fixes eval_eb :: "('t :: {one, plus}, 'sv, 'si, 'sv, 'eb) eval_time"
  and eval_ea :: "('t, 'sv, 'si, 'sv, 'ea) eval_time"
  and eval_esf :: "('t, 'sv, 'si, 'sv, 'esf) eval_time"
  and eval_esb :: "('t, 'sv, 'si, 'sv, 'esb) eval_time"
begin

inductive eval_exp_seq_assign_base ::
  "('t, 'sv, 'si, 'sv, ('si, 'eb, 'ea, 'esf, 'esb) exp_seq_assign_base) eval_time"
where
  eval_exp_seq_assign_base_ESAB[intro]:
    "eval_esb_seq_assign_base eval_eb eval_ea eval_esf eval_esb e s t s' v \<Longrightarrow>
    eval_exp_seq_assign_base (ESAB e) s t s' v"

inductive_cases eval_exp_seq_assign_base_ESABE[elim]: "eval_exp_seq_assign_base (ESAB e) s t s' v"

definition [exp_smart_constructor_def]: "SABBase eb \<equiv> ESAB (SABBBase eb)"
definition [exp_smart_constructor_def]: "SABAssign si ea \<equiv> ESAB (SABBAssign si ea)"
definition [exp_smart_constructor_def]: "SABSeq esf esb \<equiv> ESAB (Seq esf esb)"

lemma eval_exp_seq_assign_base_SABBaseI[intro]:
  assumes "eval_eb eb s t s' v"
  shows "eval_exp_seq_assign_base (SABBase eb) s t s' v"
  using assms unfolding SABBase_def by auto

lemma eval_exp_seq_assign_base_SABBaseE[elim]:
  assumes "eval_exp_seq_assign_base (SABBase eb) s t s' v"
  obtains "eval_eb eb s t s' v"
  using assms unfolding SABBase_def by auto

lemma eval_exp_seq_assign_base_SABAssignI[intro]:
  assumes "eval_ea ea s t' sea v'"
  and "s' = sea(si := v)"
  and "v = v'"
  and "t = t' + 1"
  shows "eval_exp_seq_assign_base (SABAssign si ea) s t s' v"
  using assms unfolding SABAssign_def by auto

lemma eval_exp_seq_assign_base_SABAssignE[elim]:
  assumes "eval_exp_seq_assign_base (SABAssign si ea) s t s' v"
  obtains t' sae v where "eval_ea ea s t' sae v" "s' = sae(si := v)" "t = t' + 1"
  using assms unfolding SABAssign_def by blast

lemma eval_exp_seq_assign_base_SABSeqI[intro]:
  assumes "eval_esf esf s tf sf vf"
  and "eval_esb esb sf tb s' v"
  and "t = tf + tb"
  shows "eval_exp_seq_assign_base (SABSeq esf esb) s t s' v"
  using assms unfolding SABSeq_def by blast

lemma eval_exp_seq_assign_base_SABSeqE[elim]:
  assumes "eval_exp_seq_assign_base (SABSeq esf esb) s t s' v"
  obtains tf sf vf tb where "eval_esf esf s tf sf vf" "eval_esb esb sf tb s' v" "t = tf + tb"
  using assms unfolding SABSeq_def by blast

lemma eval_exp_seq_assign_base_induct[induct pred : eval_exp_seq_assign_base,
  case_names SABBase SABAssign SABSeq]:
  assumes "eval_exp_seq_assign_base e s t s' v"
  and "\<And>eb s t s' v. eval_eb eb s t s' v \<Longrightarrow> P (SABBase eb) s t s' v"
  and "\<And>ea s t s' v si. eval_ea ea s t s' v \<Longrightarrow> P (SABAssign si ea) s (t + 1) (s'(si := v)) v"
  and "\<And>esf s tf sf vf esb tb sb vb. eval_esf esf s tf sf vf \<Longrightarrow>
    eval_esb esb sf tb sb vb \<Longrightarrow> P (SABSeq esf esb) s (tf + tb) sb vb"
  shows "P e s t s' v"
  using assms
  apply (elim eval_exp_seq_assign_base.induct)
  apply (erule eval_esb_seq_assign_base_induct)
  by (fold exp_smart_constructor_def) (blast intro: assms)+

end

lemma eval_exp_seq_assign_base_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  and "\<And>e s t s' v. f2 e s t s' v \<longrightarrow> g2 e s t s' v"
  and "\<And>e s t s' v. f3 e s t s' v \<longrightarrow> g3 e s t s' v"
  and "\<And>e s t s' v. f4 e s t s' v \<longrightarrow> g4 e s t s' v"
  shows "eval_exp_seq_assign_base f1 f2 f3 f4 e s t s' v \<longrightarrow> eval_exp_seq_assign_base g1 g2 g3 g4 e s t s' v"
proof
  assume "eval_exp_seq_assign_base f1 f2 f3 f4 e s t s' v"
  from this assms show "eval_exp_seq_assign_base g1 g2 g3 g4 e s t s' v"
    by (induction rule: eval_exp_seq_assign_base_induct) fast+
qed


type_synonym ('si, 'eb, 'ea, 'e) exp_seq_assign_base_hom =
  "('si, 'eb, 'ea, 'e, 'e) exp_seq_assign_base"

context
  fixes eval_eb :: "('t :: {one, plus}, 'sv, 'si, 'sv, 'eb) eval_time"
  and eval_ea :: "('t, 'sv, 'si, 'sv, 'ea) eval_time"
  and eval_e :: "('t, 'sv, 'si, 'sv, 'e) eval_time"
begin

definition "eval_exp_seq_assign_base_hom \<equiv> eval_exp_seq_assign_base eval_eb eval_ea eval_e eval_e"

lemma eval_exp_seq_assign_base_hom_SABBaseI[intro]:
  assumes "eval_eb eb s t s' v"
  shows "eval_exp_seq_assign_base_hom (SABBase eb) s t s' v"
  using assms unfolding eval_exp_seq_assign_base_hom_def by auto

lemma eval_exp_seq_assign_base_hom_SABBaseE[elim]:
  assumes "eval_exp_seq_assign_base_hom (SABBase eb) s t s' v"
  obtains "eval_eb eb s t s' v"
  using assms unfolding eval_exp_seq_assign_base_hom_def by auto

lemma eval_exp_seq_assign_base_hom_SABAssignI[intro]:
  assumes "eval_ea ea s t' sea v'"
  and "s' = sea(si := v)"
  and "v = v'"
  and "t = t' + 1"
  shows "eval_exp_seq_assign_base_hom (SABAssign si ea) s t s' v"
  using assms unfolding eval_exp_seq_assign_base_hom_def by auto

lemma eval_exp_seq_assign_base_hom_SABAssignE[elim]:
  assumes "eval_exp_seq_assign_base_hom (SABAssign si ea) s t s' v"
  obtains t' sae v where "eval_ea ea s t' sae v" "s' = sae(si := v)" "t = t' + 1"
  using assms unfolding eval_exp_seq_assign_base_hom_def by blast

lemma eval_exp_seq_assign_base_hom_SABSeqI[intro]:
  assumes "eval_e esf s tf sf vf"
  and "eval_e esb sf tb s' v"
  and "t = tf + tb"
  shows "eval_exp_seq_assign_base_hom (SABSeq esf esb) s t s' v"
  using assms unfolding eval_exp_seq_assign_base_hom_def by blast

lemma eval_exp_seq_assign_base_hom_SABSeqE[elim]:
  assumes "eval_exp_seq_assign_base_hom (SABSeq esf esb) s t s' v"
  obtains tf sf vf tb where "eval_e esf s tf sf vf" "eval_e esb sf tb s' v" "t = tf + tb"
  using assms unfolding eval_exp_seq_assign_base_hom_def by blast

lemma eval_exp_seq_assign_base_hom_induct[induct pred : eval_exp_seq_assign_base_hom,
  case_names SABBase SABAssign SABSeq]:
  assumes "eval_exp_seq_assign_base_hom e s t s' v"
  and "\<And>eb s t s' v. eval_eb eb s t s' v \<Longrightarrow> P (SABBase eb) s t s' v"
  and "\<And>ea s t s' v si. eval_ea ea s t s' v \<Longrightarrow> P (SABAssign si ea) s (t + 1) (s'(si := v)) v"
  and "\<And>esf s tf sf vf esb tb sb vb. eval_e esf s tf sf vf \<Longrightarrow>
    eval_e esb sf tb sb vb \<Longrightarrow> P (SABSeq esf esb) s (tf + tb) sb vb"
  shows "P e s t s' v"
  using assms unfolding eval_exp_seq_assign_base_hom_def by (rule eval_exp_seq_assign_base_induct)

end

lemma eval_exp_seq_assign_base_hom_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  and "\<And>e s t s' v. f2 e s t s' v \<longrightarrow> g2 e s t s' v"
  and "\<And>e s t s' v. f3 e s t s' v \<longrightarrow> g3 e s t s' v"
  shows "eval_exp_seq_assign_base_hom f1 f2 f3 e s t s' v \<longrightarrow> eval_exp_seq_assign_base_hom g1 g2 g3 e s t s' v"
  using assms unfolding eval_exp_seq_assign_base_hom_def by (intro eval_exp_seq_assign_base_mono)


end