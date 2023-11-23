\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expression_If_Seq_Assigns_Base
  imports
    Expression_Ifs_Base
    Expression_Seq_Assigns_Base
begin

datatype ('si, 'eb, 'ea, 'esf, 'esb, 'eic, 'eit, 'eif) exp_if_seq_assign_base = EISAB
  "(('si, 'eb, 'ea, 'esf, 'esb) exp_seq_assign_base,
    'eic, 'eit, 'eif) exp_if_base"

context
  fixes eval_eb :: "('t :: {one, plus}, 'sv, 'si, 'sv, 'eb) eval_time"
  and eval_ea :: "('t, 'sv, 'si, 'sv, 'ea) eval_time"
  and eval_esf :: "('t, 'sv, 'si, 'sv, 'esf) eval_time"
  and eval_esb :: "('t, 'sv, 'si, 'sv, 'esb) eval_time"
  and eval_eic :: "('t, bool, 'si, 'sv, 'eic) eval_time"
  and eval_eit :: "('t, 'sv, 'si, 'sv, 'eit) eval_time"
  and eval_eif :: "('t, 'sv, 'si, 'sv, 'eif) eval_time"
begin

definition "eval_eifb_if_seq_assign_base \<equiv>
  eval_exp_if_base (eval_exp_seq_assign_base eval_eb eval_ea eval_esf eval_esb) eval_eic eval_eit eval_eif"

definition [exp_smart_constructor_def]: "ISABBBase eb \<equiv> EIBase (SABBase eb)"
definition [exp_smart_constructor_def]: "ISABBAssign si ea \<equiv> EIBase (SABAssign si ea)"
definition [exp_smart_constructor_def]: "ISABBSeq esf esb \<equiv> EIBase (SABSeq esf esb)"

lemma eval_eifb_if_seq_assign_base_ISABBBaseI[intro]:
  assumes "eval_eb eb s t s' v"
  shows "eval_eifb_if_seq_assign_base (ISABBBase eb) s t s' v"
  using assms unfolding eval_eifb_if_seq_assign_base_def ISABBBase_def by auto

lemma eval_eifb_if_seq_assign_base_ISABBBaseE[elim]:
  assumes "eval_eifb_if_seq_assign_base (ISABBBase eb) s t s' v"
  obtains "eval_eb eb s t s' v"
  using assms unfolding eval_eifb_if_seq_assign_base_def ISABBBase_def by auto

lemma eval_eifb_if_seq_assign_base_ISABBAssignI[intro]:
  assumes "eval_ea ea s t' sea v'"
  and "s' = sea(si := v)"
  and "v = v'"
  and "t = t' + 1"
  shows "eval_eifb_if_seq_assign_base (ISABBAssign si ea) s t s' v"
  using assms unfolding eval_eifb_if_seq_assign_base_def ISABBAssign_def by auto

lemma eval_eifb_if_seq_assign_base_ISABBAssignE[elim]:
  assumes "eval_eifb_if_seq_assign_base (ISABBAssign si ea) s t s' v"
  obtains t' sae v where "eval_ea ea s t' sae v" "s' = sae(si := v)" "t = t' + 1"
  using assms unfolding eval_eifb_if_seq_assign_base_def ISABBAssign_def by blast

lemma eval_eifb_if_seq_assign_base_ISABBSeqI[intro]:
  assumes "eval_esf esf s tf sf vf"
  and "eval_esb esb sf tb s' v"
  and "t = tf + tb"
  shows "eval_eifb_if_seq_assign_base (ISABBSeq esf esb) s t s' v"
  using assms unfolding eval_eifb_if_seq_assign_base_def ISABBSeq_def by blast

lemma eval_eifb_if_seq_assign_base_ISABBSeqE[elim]:
  assumes "eval_eifb_if_seq_assign_base (ISABBSeq esf esb) s t s' v"
  obtains tf sf vf tb where "eval_esf esf s tf sf vf" "eval_esb esb sf tb s' v" "t = tf + tb"
  using assms unfolding eval_eifb_if_seq_assign_base_def ISABBSeq_def by blast

lemma eval_eifb_if_seq_assign_base_If_trueI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "b"
  and "eval_eit eit sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_eifb_if_seq_assign_base (If eic eit eif) s t s' v"
  using assms unfolding eval_eifb_if_seq_assign_base_def by blast

lemma eval_eifb_if_seq_assign_base_If_falseI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "\<not>b"
  and "eval_eif eif sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_eifb_if_seq_assign_base (If eic eit eif) s t s' v"
  using assms unfolding eval_eifb_if_seq_assign_base_def by blast

lemma eval_eifb_if_seq_assign_base_IfE[elim]:
  assumes "eval_eifb_if_seq_assign_base (If eic eit eif) s t s' v"
  obtains sc b t1 t2 where "eval_eic eic s t1 sc b" "b" "eval_eit eit sc t2 s' v" "t = t1 + 1 + t2"
    | sc b t1 t2 where "eval_eic eic s t1 sc b" "\<not>b" "eval_eif eif sc t2 s' v" "t = t1 + 1 + t2"
  using assms unfolding eval_eifb_if_seq_assign_base_def by blast

lemma eval_eifb_if_seq_assign_base_induct[induct pred : eval_eifb_if_seq_assign_base,
  case_names ISABBBase ISABBAssign ISABBSeq If_true If_false]:
  assumes "eval_eifb_if_seq_assign_base e s t s' v"
  and "\<And>eb s t s' v. eval_eb eb s t s' v \<Longrightarrow> P (ISABBBase eb) s t s' v"
  and "\<And>ea s t s' v si. eval_ea ea s t s' v \<Longrightarrow> P (ISABBAssign si ea) s (t + 1) (s'(si := v)) v"
  and "\<And>esf s tf sf vf esb tb sb vb. eval_esf esf s tf sf vf \<Longrightarrow>
    eval_esb esb sf tb sb vb \<Longrightarrow> P (ISABBSeq esf esb) s (tf + tb) sb vb"
  and "\<And>eic s t1 sc b eit t2 s' v eif. eval_eic eic s t1 sc b \<Longrightarrow> b \<Longrightarrow> eval_eit eit sc t2 s' v \<Longrightarrow>
    P (If eic eit eif) s (t1 + 1 + t2) s' v"
  and "\<And>eic s t1 sc b eif t2 s' v eit. eval_eic eic s t1 sc b \<Longrightarrow> \<not>b \<Longrightarrow> eval_eif eif sc t2 s' v \<Longrightarrow>
    P (If eic eit eif) s (t1 + 1 + t2) s' v"
  shows "P e s t s' v"
  using assms unfolding eval_eifb_if_seq_assign_base_def
  by (elim eval_exp_if_base.induct eval_exp_seq_assign_base_induct)
  (fold exp_smart_constructor_def)

end

lemma eval_eifb_if_seq_assign_base_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  and "\<And>e s t s' v. f2 e s t s' v \<longrightarrow> g2 e s t s' v"
  and "\<And>e s t s' v. f3 e s t s' v \<longrightarrow> g3 e s t s' v"
  and "\<And>e s t s' v. f4 e s t s' v \<longrightarrow> g4 e s t s' v"
  and "\<And>e s t s' v. f5 e s t s' v \<longrightarrow> g5 e s t s' v"
  and "\<And>e s t s' v. f6 e s t s' v \<longrightarrow> g6 e s t s' v"
  and "\<And>e s t s' v. f7 e s t s' v \<longrightarrow> g7 e s t s' v"
  shows "eval_eifb_if_seq_assign_base f1 f2 f3 f4 f5 f6 f7 e s t s' v \<longrightarrow> eval_eifb_if_seq_assign_base g1 g2 g3 g4 g5 g6 g7 e s t s' v"
  unfolding eval_eifb_if_seq_assign_base_def
  by (intro eval_exp_if_base_mono eval_exp_seq_assign_base_mono assms)


context
  fixes eval_eb :: "('t :: {one, plus}, 'sv, 'si, 'sv, 'eb) eval_time"
  and eval_ea :: "('t, 'sv, 'si, 'sv, 'ea) eval_time"
  and eval_esf :: "('t, 'sv, 'si, 'sv, 'esf) eval_time"
  and eval_esb :: "('t, 'sv, 'si, 'sv, 'esb) eval_time"
  and eval_eic :: "('t, bool, 'si, 'sv, 'eic) eval_time"
  and eval_eit :: "('t, 'sv, 'si, 'sv, 'eit) eval_time"
  and eval_eif :: "('t, 'sv, 'si, 'sv, 'eif) eval_time"
begin

inductive eval_exp_if_seq_assign_base ::
  "('t, 'sv, 'si, 'sv, ('si, 'eb, 'ea, 'esf, 'esb, 'eic, 'eit, 'eif) exp_if_seq_assign_base) eval_time"
where
  eval_exp_seq_assign_base_EISAB[intro]:
    "eval_eifb_if_seq_assign_base eval_eb eval_ea eval_esf eval_esb eval_eic eval_eit eval_eif e s t s' v \<Longrightarrow>
    eval_exp_if_seq_assign_base (EISAB e) s t s' v"

inductive_cases eval_exp_if_seq_assign_base_EISABE[elim]:
  "eval_exp_if_seq_assign_base (EISAB e) s t s' v"

definition [exp_smart_constructor_def]: "ISABBase eb \<equiv> EISAB (ISABBBase eb)"
definition [exp_smart_constructor_def]: "ISABAssign si ea \<equiv> EISAB (ISABBAssign si ea)"
definition [exp_smart_constructor_def]: "ISABSeq esf esb \<equiv> EISAB (ISABBSeq esf esb)"
definition [exp_smart_constructor_def]: "ISABIf eic eit eif \<equiv> EISAB (If eic eit eif)"

lemma eval_exp_if_seq_assign_base_ISABBaseI[intro]:
  assumes "eval_eb eb s t s' v"
  shows "eval_exp_if_seq_assign_base (ISABBase eb) s t s' v"
  using assms unfolding ISABBase_def by auto

lemma eval_exp_if_seq_assign_base_ISABBaseE[elim]:
  assumes "eval_exp_if_seq_assign_base (ISABBase eb) s t s' v"
  obtains "eval_eb eb s t s' v"
  using assms unfolding ISABBase_def by auto

lemma eval_exp_if_seq_assign_base_ISABAssignI[intro]:
  assumes "eval_ea ea s t' sea v'"
  and "s' = sea(si := v)"
  and "v = v'"
  and "t = t' + 1"
  shows "eval_exp_if_seq_assign_base (ISABAssign si ea) s t s' v"
  using assms unfolding ISABAssign_def by auto

lemma eval_exp_if_seq_assign_base_ISABAssignE[elim]:
  assumes "eval_exp_if_seq_assign_base (ISABAssign si ea) s t s' v"
  obtains t' sae v where "eval_ea ea s t' sae v" "s' = sae(si := v)" "t = t' + 1"
  using assms unfolding ISABAssign_def by blast

lemma eval_exp_if_seq_assign_base_ISABSeqI[intro]:
  assumes "eval_esf esf s tf sf vf"
  and "eval_esb esb sf tb s' v"
  and "t = tf + tb"
  shows "eval_exp_if_seq_assign_base (ISABSeq esf esb) s t s' v"
  using assms unfolding ISABSeq_def by blast

lemma eval_exp_if_seq_assign_base_ISABSeqE[elim]:
  assumes "eval_exp_if_seq_assign_base (ISABSeq esf esb) s t s' v"
  obtains tf sf vf tb where "eval_esf esf s tf sf vf" "eval_esb esb sf tb s' v" "t = tf + tb"
  using assms unfolding ISABSeq_def by blast

lemma eval_exp_if_seq_assign_base_ISABIf_trueI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "b"
  and "eval_eit eit sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_exp_if_seq_assign_base (ISABIf eic eit eif) s t s' v"
  using assms unfolding ISABIf_def by blast

lemma eval_exp_if_seq_assign_base_ISABIf_falseI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "\<not>b"
  and "eval_eif eif sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_exp_if_seq_assign_base (ISABIf eic eit eif) s t s' v"
  using assms unfolding ISABIf_def by blast

lemma eval_exp_if_seq_assign_base_ISABIfE[elim]:
  assumes "eval_exp_if_seq_assign_base (ISABIf eic eit eif) s t s' v"
  obtains sc b t1 t2 where "eval_eic eic s t1 sc b" "b" "eval_eit eit sc t2 s' v" "t = t1 + 1 + t2"
    | sc b t1 t2 where "eval_eic eic s t1 sc b" "\<not>b" "eval_eif eif sc t2 s' v" "t = t1 + 1 + t2"
  using assms unfolding ISABIf_def by blast

lemma eval_exp_if_seq_assign_base_induct[induct pred : eval_exp_if_seq_assign_base,
  case_names ISABBase ISABAssign ISABSeq ISABIf_true ISABIf_false]:
  assumes "eval_exp_if_seq_assign_base e s t s' v"
  and "\<And>eb s t s' v. eval_eb eb s t s' v \<Longrightarrow> P (ISABBase eb) s t s' v"
  and "\<And>ea s t s' v si. eval_ea ea s t s' v \<Longrightarrow> P (ISABAssign si ea) s (t + 1) (s'(si := v)) v"
  and "\<And>esf s tf sf vf esb tb sb vb. eval_esf esf s tf sf vf \<Longrightarrow>
    eval_esb esb sf tb sb vb \<Longrightarrow> P (ISABSeq esf esb) s (tf + tb) sb vb"
  and "\<And>eic s t1 sc b eit t2 s' v eif. eval_eic eic s t1 sc b \<Longrightarrow> b \<Longrightarrow> eval_eit eit sc t2 s' v \<Longrightarrow>
    P (ISABIf eic eit eif) s (t1 + 1 + t2) s' v"
  and "\<And>eic s t1 sc b eif t2 s' v eit. eval_eic eic s t1 sc b \<Longrightarrow> \<not>b \<Longrightarrow> eval_eif eif sc t2 s' v \<Longrightarrow>
    P (ISABIf eic eit eif) s (t1 + 1 + t2) s' v"
  shows "P e s t s' v"
  using assms
  apply (elim eval_exp_if_seq_assign_base.induct)
  apply (erule eval_eifb_if_seq_assign_base_induct)
  by (fold exp_smart_constructor_def) (blast intro: assms)+

end

lemma eval_exp_if_seq_assign_base_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  and "\<And>e s t s' v. f2 e s t s' v \<longrightarrow> g2 e s t s' v"
  and "\<And>e s t s' v. f3 e s t s' v \<longrightarrow> g3 e s t s' v"
  and "\<And>e s t s' v. f4 e s t s' v \<longrightarrow> g4 e s t s' v"
  and "\<And>e s t s' v. f5 e s t s' v \<longrightarrow> g5 e s t s' v"
  and "\<And>e s t s' v. f6 e s t s' v \<longrightarrow> g6 e s t s' v"
  and "\<And>e s t s' v. f7 e s t s' v \<longrightarrow> g7 e s t s' v"
  shows "eval_exp_if_seq_assign_base f1 f2 f3 f4 f5 f6 f7 e s t s' v \<longrightarrow> eval_exp_if_seq_assign_base g1 g2 g3 g4 g5 g6 g7 e s t s' v"
proof
  assume "eval_exp_if_seq_assign_base f1 f2 f3 f4 f5 f6 f7 e s t s' v"
  from this assms show "eval_exp_if_seq_assign_base g1 g2 g3 g4 g5 g6 g7 e s t s' v"
    by (induction rule: eval_exp_if_seq_assign_base_induct) fast+
qed


type_synonym ('si, 'eb, 'ea, 'eic, 'e) exp_if_seq_assign_base_hom =
  "('si, 'eb, 'ea, 'e, 'e, 'eic, 'e, 'e) exp_if_seq_assign_base"

context
  fixes eval_eb :: "('t :: {one, plus}, 'sv, 'si, 'sv, 'eb) eval_time"
  and eval_ea :: "('t, 'sv, 'si, 'sv, 'ea) eval_time"
  and eval_eic :: "('t, bool, 'si, 'sv, 'eic) eval_time"
  and eval_e :: "('t, 'sv, 'si, 'sv, 'e) eval_time"
begin

definition "eval_exp_if_seq_assign_base_hom \<equiv>
  eval_exp_if_seq_assign_base eval_eb eval_ea eval_e eval_e eval_eic eval_e eval_e"

lemma eval_exp_if_seq_assign_base_hom_ISABBaseI[intro]:
  assumes "eval_eb eb s t s' v"
  shows "eval_exp_if_seq_assign_base_hom (ISABBase eb) s t s' v"
  using assms unfolding eval_exp_if_seq_assign_base_hom_def by auto

lemma eval_exp_if_seq_assign_base_hom_ISABBaseE[elim]:
  assumes "eval_exp_if_seq_assign_base_hom (ISABBase eb) s t s' v"
  obtains "eval_eb eb s t s' v"
  using assms unfolding eval_exp_if_seq_assign_base_hom_def by auto

lemma eval_exp_if_seq_assign_base_hom_ISABAssignI[intro]:
  assumes "eval_ea ea s t' sea v'"
  and "s' = sea(si := v)"
  and "v = v'"
  and "t = t' + 1"
  shows "eval_exp_if_seq_assign_base_hom (ISABAssign si ea) s t s' v"
  using assms unfolding eval_exp_if_seq_assign_base_hom_def by auto

lemma eval_exp_if_seq_assign_base_hom_ISABAssignE[elim]:
  assumes "eval_exp_if_seq_assign_base_hom (ISABAssign si ea) s t s' v"
  obtains t' sae v where "eval_ea ea s t' sae v" "s' = sae(si := v)" "t = t' + 1"
  using assms unfolding eval_exp_if_seq_assign_base_hom_def by auto

lemma eval_exp_if_seq_assign_base_hom_ISABSeqI[intro]:
  assumes "eval_e esf s tf sf vf"
  and "eval_e esb sf tb s' v"
  and "t = tf + tb"
  shows "eval_exp_if_seq_assign_base_hom (ISABSeq esf esb) s t s' v"
  using assms unfolding eval_exp_if_seq_assign_base_hom_def by blast

lemma eval_exp_if_seq_assign_base_hom_ISABSeqE[elim]:
  assumes "eval_exp_if_seq_assign_base_hom (ISABSeq esf esb) s t s' v"
  obtains tf sf vf tb where "eval_e esf s tf sf vf" "eval_e esb sf tb s' v" "t = tf + tb"
  using assms unfolding eval_exp_if_seq_assign_base_hom_def by blast

lemma eval_exp_if_seq_assign_base_hom_ISABIf_trueI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "b"
  and "eval_e eit sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_exp_if_seq_assign_base_hom (ISABIf eic eit eif) s t s' v"
  using assms unfolding eval_exp_if_seq_assign_base_hom_def by blast

lemma eval_exp_if_seq_assign_base_hom_ISABIf_falseI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "\<not>b"
  and "eval_e eif sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_exp_if_seq_assign_base_hom (ISABIf eic eit eif) s t s' v"
  using assms unfolding eval_exp_if_seq_assign_base_hom_def by blast

lemma eval_exp_if_seq_assign_base_hom_ISABIfE[elim]:
  assumes "eval_exp_if_seq_assign_base_hom (ISABIf eic eit eif) s t s' v"
  obtains sc b t1 t2 where "eval_eic eic s t1 sc b" "b" "eval_e eit sc t2 s' v" "t = t1 + 1 + t2"
    | sc b t1 t2 where "eval_eic eic s t1 sc b" "\<not>b" "eval_e eif sc t2 s' v" "t = t1 + 1 + t2"
  using assms unfolding eval_exp_if_seq_assign_base_hom_def by blast

lemma eval_exp_if_seq_assign_base_hom_induct[induct pred : eval_exp_if_seq_assign_base_hom,
  case_names ISABBase ISABAssign ISABSeq ISABIf_true ISABIf_false]:
  assumes "eval_exp_if_seq_assign_base_hom e s t s' v"
  and "\<And>eb s t s' v. eval_eb eb s t s' v \<Longrightarrow> P (ISABBase eb) s t s' v"
  and "\<And>ea s t s' v si. eval_ea ea s t s' v \<Longrightarrow> P (ISABAssign si ea) s (t + 1) (s'(si := v)) v"
  and "\<And>esf s tf sf vf esb tb sb vb. eval_e esf s tf sf vf \<Longrightarrow>
    eval_e esb sf tb sb vb \<Longrightarrow> P (ISABSeq esf esb) s (tf + tb) sb vb"
  and "\<And>eic s t1 sc b eit t2 s' v eif. eval_eic eic s t1 sc b \<Longrightarrow> b \<Longrightarrow> eval_e eit sc t2 s' v \<Longrightarrow>
    P (ISABIf eic eit eif) s (t1 + 1 + t2) s' v"
  and "\<And>eic s t1 sc b eif t2 s' v eit. eval_eic eic s t1 sc b \<Longrightarrow> \<not>b \<Longrightarrow> eval_e eif sc t2 s' v \<Longrightarrow>
    P (ISABIf eic eit eif) s (t1 + 1 + t2) s' v"
  shows "P e s t s' v"
  using assms unfolding eval_exp_if_seq_assign_base_hom_def by (rule eval_exp_if_seq_assign_base_induct)

end

lemma eval_exp_if_seq_assign_base_hom_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  and "\<And>e s t s' v. f2 e s t s' v \<longrightarrow> g2 e s t s' v"
  and "\<And>e s t s' v. f3 e s t s' v \<longrightarrow> g3 e s t s' v"
  and "\<And>e s t s' v. f4 e s t s' v \<longrightarrow> g4 e s t s' v"
  shows "eval_exp_if_seq_assign_base_hom f1 f2 f3 f4 e s t s' v \<longrightarrow> eval_exp_if_seq_assign_base_hom g1 g2 g3 g4 e s t s' v"
  using assms unfolding eval_exp_if_seq_assign_base_hom_def by (intro eval_exp_if_seq_assign_base_mono)


end