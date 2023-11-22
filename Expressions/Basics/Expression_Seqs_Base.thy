\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expression_Seqs_Base
  imports Expressions_Base
begin

datatype ('eb, 'esf, 'esb) exp_seq_base =
  ESBase 'eb
| Seq 'esf 'esb

context
  fixes eval_eb :: "('t :: {plus}, 'r, 'si, 'sv, 'eb) eval_time"
  and eval_esf :: "('t, 'r, 'si, 'sv, 'esf) eval_time"
  and eval_esb :: "('t, 'r, 'si, 'sv, 'esb) eval_time"
begin

inductive eval_exp_seq_base ::
  "('t, 'r, 'si, 'sv, ('eb, 'esf, 'esb) exp_seq_base) eval_time"
where
  eval_exp_seq_base_ESBase[intro]: "eval_eb eb s t s' v \<Longrightarrow>
    eval_exp_seq_base (ESBase eb) s t s' v"
| eval_exp_seq_base_Seq: "eval_esf esf s tf sf vf \<Longrightarrow>
    eval_esb esb sf tb sb vb \<Longrightarrow> eval_exp_seq_base (Seq esf esb) s (tf + tb) sb vb"

inductive_cases eval_exp_seq_base_ESBaseE[elim]:
  "eval_exp_seq_base (ESBase eb) s t s' v"
inductive_cases eval_exp_seq_base_SeqE[elim]:
  "eval_exp_seq_base (Seq esf esb) s t s' v"

lemma eval_exp_seq_base_SeqI[intro]:
  assumes "eval_esf esf s tf sf vf"
  and "eval_esb esb sf tb s' v"
  and "t = tf + tb"
  shows "eval_exp_seq_base (Seq esf esb) s t s' v"
  using assms eval_exp_seq_base.intros by auto

end

lemma eval_exp_seq_base_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  and "\<And>e s t s' v. f2 e s t s' v \<longrightarrow> g2 e s t s' v"
  and "\<And>e s t s' v. f3 e s t s' v \<longrightarrow> g3 e s t s' v"
  shows "eval_exp_seq_base f1 f2 f3 e s t s' v \<longrightarrow> eval_exp_seq_base g1 g2 g3 e s t s' v"
proof
  assume "eval_exp_seq_base f1 f2 f3 e s t s' v"
  from this assms show "eval_exp_seq_base g1 g2 g3 e s t s' v"
    by (induction rule: eval_exp_seq_base.induct) fast+
qed


type_synonym ('eb, 'e) exp_seq_base_hom = "('eb, 'e, 'e) exp_seq_base"

context
  fixes eval_eb :: "('t :: {plus}, 'r, 'si, 'sv, 'eb) eval_time"
  and eval_e :: "('t, 'r, 'si, 'sv, 'eb) eval_time"
begin

definition "eval_exp_seq_base_hom \<equiv> eval_exp_seq_base eval_eb eval_e eval_e"

lemma eval_exp_seq_base_hom_ESBaseI[intro]:
  assumes "eval_eb eb s t s' v"
  shows "eval_exp_seq_base_hom (ESBase eb) s t s' v"
  using assms unfolding eval_exp_seq_base_hom_def by auto

lemma eval_exp_seq_base_hom_ESBaseE[elim]:
  assumes "eval_exp_seq_base_hom (ESBase eb) s t s' v"
  obtains "eval_eb eb s t s' v"
  using assms unfolding eval_exp_seq_base_hom_def by auto

lemma eval_exp_seq_base_hom_SeqI[intro]:
  assumes "eval_e esf s tf sf vf"
  and "eval_e esb sf tb s' v"
  and "t = tf + tb"
  shows "eval_exp_seq_base_hom (Seq esf esb) s t s' v"
  using assms unfolding eval_exp_seq_base_hom_def by auto

lemma eval_exp_seq_base_hom_SeqE[elim]:
  assumes "eval_exp_seq_base_hom (Seq esf esb) s t s' v"
  obtains tf sf vf tb where "eval_e esf s tf sf vf" "eval_e esb sf tb s' v" "t = tf + tb"
  using assms unfolding eval_exp_seq_base_hom_def by blast

lemma eval_exp_seq_base_hom_induct[induct pred : eval_exp_seq_base_hom, case_names ESBase Seq]:
  assumes "eval_exp_seq_base_hom e s t s' v"
  and "\<And>eb s t s' v. eval_eb eb s t s' v \<Longrightarrow> P (ESBase eb) s t s' v"
  and "\<And>esf s tf sf vf esb tb sb vb. eval_e esf s tf sf vf \<Longrightarrow>
    eval_e esb sf tb sb vb \<Longrightarrow> P (Seq esf esb) s (tf + tb) sb vb"
  shows "P e s t s' v"
  using assms unfolding eval_exp_seq_base_hom_def by (rule eval_exp_seq_base.induct)

end

lemma eval_exp_seq_base_hom_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  and "\<And>e s t s' v. f2 e s t s' v \<longrightarrow> g2 e s t s' v"
  shows "eval_exp_seq_base_hom f1 f2 e s t s' v \<longrightarrow> eval_exp_seq_base_hom g1 g2 e s t s' v"
  unfolding eval_exp_seq_base_hom_def by (intro eval_exp_seq_base_mono assms)


end