\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expression_Tail_Calls_Hom
  imports
    Expression_Tail_Calls
begin

type_synonym 'e exp_tcall_hom = "('e, 'e) exp_tcall"

context
  fixes eval_e :: "('t :: {plus}, 'r, 'si, 'sv, 'e) eval_time"
begin

definition "eval_exp_tcall_hom \<equiv> eval_exp_tcall eval_e eval_e"
definition "eval_efgcall_tcall_hom \<equiv> eval_efgcall_tcall eval_e eval_e"

lemma eval_exp_tcall_hom_TCI[intro]:
  assumes "eval_efgcall_tcall_hom (TC e) e s t s' v"
  shows "eval_exp_tcall_hom (TC e) s t s' v"
  using assms unfolding eval_exp_tcall_hom_def eval_efgcall_tcall_hom_def by blast

lemma eval_exp_tcall_hom_TCE[elim]:
  assumes "eval_exp_tcall_hom (TC e) s t s' v"
  obtains "eval_efgcall_tcall_hom (TC e) e s t s' v"
  using assms unfolding eval_exp_tcall_hom_def eval_efgcall_tcall_hom_def by blast

lemma eval_efgcall_tcall_hom_FGCBaseI[intro]:
  assumes "eval_e eb s t s' v"
  shows "eval_efgcall_tcall_hom etc (FGCBase eb) s t s' v"
  using assms unfolding eval_efgcall_tcall_hom_def by auto

lemma eval_efgcall_tcall_hom_FGCBaseE[elim]:
  assumes "eval_efgcall_tcall_hom etc (FGCBase eb) s t s' v"
  obtains "eval_e eb s t s' v"
  using assms unfolding eval_efgcall_tcall_hom_def by auto

lemma eval_efgcall_tcall_hom_FGCSeqI[intro]:
  assumes "eval_e esf s tf sf vf"
  and "eval_efgcall_tcall_hom etc esb sf tb s' v"
  and "t = tf + tb"
  shows "eval_efgcall_tcall_hom etc (FGCSeq esf esb) s t s' v"
  using assms unfolding eval_efgcall_tcall_hom_def by auto

lemma eval_efgcall_tcall_hom_FGCSeqE[elim]:
  assumes "eval_efgcall_tcall_hom etc (FGCSeq esf esb) s t s' v"
  obtains tf sf vf tb where "eval_e esf s tf sf vf"
    "eval_efgcall_tcall_hom etc esb sf tb s' v" "t = tf + tb"
  using assms unfolding eval_efgcall_tcall_hom_def by blast

lemma eval_efgcall_tcall_hom_FGCGlobal_CallI[intro]:
  assumes "eval_exp_tcall_hom etc s t s' v"
  shows "eval_efgcall_tcall_hom etc FGCGlobal_Call s t s' v"
  using assms unfolding eval_exp_tcall_hom_def eval_efgcall_tcall_hom_def by auto

lemma eval_efgcall_tcall_hom_FGCGlobal_CallE[elim]:
  assumes "eval_efgcall_tcall_hom etc FGCGlobal_Call s t s' v"
  obtains "eval_exp_tcall_hom etc s t s' v"
  using assms unfolding eval_exp_tcall_hom_def eval_efgcall_tcall_hom_def by auto

lemma not_eval_exp_tcall_hom_TC_FGCGlobal[iff]:
  "\<not>(eval_exp_tcall_hom (TC FGCGlobal_Call) s t s' v)"
  unfolding eval_exp_tcall_hom_def by blast

lemma not_eval_efgcall_tcall_hom_TC_FGCGlobal_Call_FGCGlobal_Call[iff]:
  "\<not>(eval_efgcall_tcall_hom (TC FGCGlobal_Call) FGCGlobal_Call s t s' v)"
  unfolding eval_efgcall_tcall_hom_def by blast

lemma eval_efgcall_tcall_hom_induct[induct pred : eval_efgcall_tcall_hom,
  case_names eq_TC FGCBase FGCSeq FGCGlobal_Call]:
  assumes "eval_efgcall_tcall_hom etc e s t s' v"
  and "etc = TC efgc"
  and "\<And>eb s t s' v. eval_e eb s t s' v \<Longrightarrow> P (FGCBase eb) s t s' v"
  and "\<And>esf s tf sf vf esb tb sb vb. eval_e esf s tf sf vf \<Longrightarrow>
    eval_efgcall_tcall_hom etc esb sf tb sb vb \<Longrightarrow> P esb sf tb sb vb \<Longrightarrow> P (FGCSeq esf esb) s (tf + tb) sb vb"
  and "\<And>s t s' v. eval_efgcall_tcall_hom etc efgc s t s' v \<Longrightarrow> P efgc s t s' v \<Longrightarrow>
    P FGCGlobal_Call s t s' v"
  shows "P e s t s' v"
  using assms unfolding eval_efgcall_tcall_hom_def by (rule eval_efgcall_tcall_induct)

corollary eval_exp_tcall_hom_induct[induct pred : eval_exp_tcall_hom, case_names Base Seq]:
  assumes "eval_exp_tcall_hom e s t s' v"
  and "\<And>eb s t s' v. eval_e eb s t s' v \<Longrightarrow> P e s t s' v"
  and "\<And>esf s tf sf vf esb tb sb vb. eval_e esf s tf sf vf \<Longrightarrow>
    eval_efgcall_tcall_hom e esb sf tb sb vb \<Longrightarrow> P e sf tb sb vb \<Longrightarrow> P e s (tf + tb) sb vb"
  shows "P e s t s' v"
  using assms unfolding eval_exp_tcall_hom_def eval_efgcall_tcall_hom_def
  by (rule eval_exp_tcall_induct)

end

lemma eval_exp_fgcall_eval_exp_tcall_hom_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  shows "eval_efgcall_tcall_hom f1 (TC efgc) e s t s' v \<longrightarrow>
    eval_efgcall_tcall_hom g1 (TC efgc) e s t s' v"
  using assms unfolding eval_efgcall_tcall_hom_def by (intro eval_efgcall_tcall_mono)

lemma eval_exp_tcall_hom_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  shows "eval_exp_tcall_hom f1 e s t s' v \<longrightarrow> eval_exp_tcall_hom g1 e s t s' v"
  using assms unfolding eval_exp_tcall_hom_def by (intro eval_exp_tcall_mono)


end