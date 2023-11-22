\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expression_Final_Global_Calls
  imports
    Expression_Seqs_Base
    Expression_Global_Calls_Base
begin

datatype ('eb, 'esf) exp_fgcall = EFGC
  "(('eb, 'esf,
      ('eb, 'esf) exp_fgcall) exp_seq_base)
    exp_global_call_base"

context
  fixes eval_eb :: "('t :: {plus}, 'r, 'si, 'sv, 'eb) eval_time"
  and eval_esf :: "('t, 'r, 'si, 'sv, 'esf) eval_time"
begin

definition "eval_egc_fgcall eval_efgcall \<equiv>
  eval_exp_global_call_base (eval_exp_seq_base eval_eb eval_esf eval_efgcall)"

definition [exp_smart_constructor_def]: "FGCBBase eb \<equiv> EGCBase (ESBase eb)"
definition [exp_smart_constructor_def]: "FGCBSeq esf esb \<equiv> EGCBase (Seq esf esb)"

lemma eval_exp_while_base_FGCBBaseI[intro]:
  assumes "eval_eb eb s t s' r"
  shows "eval_egc_fgcall eval_efgcall eval_gc gc (FGCBBase eb) s t s' r"
  using assms unfolding eval_egc_fgcall_def FGCBBase_def by auto

lemma eval_exp_while_base_FGCBBaseE[elim]:
  assumes "eval_egc_fgcall eval_efgcall eval_gc gc (FGCBBase eb) s t s' r"
  obtains "eval_eb eb s t s' r"
  using assms unfolding eval_egc_fgcall_def FGCBBase_def by auto

lemma eval_egc_fgcall_FGCBSeqI[intro]:
  assumes "eval_esf esf s tf sf rf"
  and "eval_efgcall esb sf tb s' r"
  and "t = tf + tb"
  shows "eval_egc_fgcall eval_efgcall eval_gc gc (FGCBSeq esf esb) s t s' r"
  using assms unfolding eval_egc_fgcall_def FGCBSeq_def by auto

lemma eval_egc_fgcall_FGCBSeqE[elim]:
  assumes "eval_egc_fgcall eval_efgcall eval_gc gc (FGCBSeq esf esb) s t s' r"
  obtains tf sf rf tb where "eval_esf esf s tf sf rf" "eval_efgcall esb sf tb s' r" "t = tf + tb"
  using assms unfolding eval_egc_fgcall_def FGCBSeq_def by blast

lemma eval_egc_fgcall_Global_CallI[intro]:
  assumes "eval_gc gc s t s' r"
  shows "eval_egc_fgcall eval_efgcall eval_gc gc Global_Call s t s' r"
  using assms unfolding eval_egc_fgcall_def by auto

lemma eval_egc_fgcall_Global_CallE[elim]:
  assumes "eval_egc_fgcall eval_efgcall eval_gc gc Global_Call s t s' r"
  obtains "eval_gc gc s t s' r"
  using assms unfolding eval_egc_fgcall_def by auto

end

lemma eval_egc_fgcall_mono[mono]:
  assumes "\<And>e s t s' r. f1 e s t s' r \<longrightarrow> g1 e s t s' r"
  and "\<And>e s t s' r. f2 e s t s' r \<longrightarrow> g2 e s t s' r"
  and "\<And>e s t s' r. f3 e s t s' r \<longrightarrow> g3 e s t s' r"
  and "\<And>e s t s' r. f4 e s t s' r \<longrightarrow> g4 e s t s' r"
  shows "eval_egc_fgcall f1 f2 f3 f4 gc e s t s' r \<longrightarrow> eval_egc_fgcall g1 g2 g3 g4 gc e s t s' r"
  unfolding eval_egc_fgcall_def by (intro eval_exp_global_call_base_mono eval_exp_seq_base_mono assms)

context
  fixes eval_eb :: "('t :: {plus}, 'r, 'si, 'sv, 'eb) eval_time"
  and eval_esf :: "('t, 'r, 'si, 'sv, 'esf) eval_time"
  and eval_gc :: "('t, 'r, 'si, 'sv, 'gc) eval_time"
  and gc :: "'gc"
begin

inductive eval_exp_fgcall ::
  "('t, 'r, 'si, 'sv, ('eb, 'esf) exp_fgcall) eval_time"
where
 eval_exp_fgcall_EFGC[intro]:
  "eval_egc_fgcall eval_eb eval_esf eval_exp_fgcall eval_gc gc e s t s' r
    \<Longrightarrow> eval_exp_fgcall (EFGC e) s t s' r"

inductive_cases eval_exp_fgcall_EFGCE[elim]: "eval_exp_fgcall (EFGC e) s t s' r"

definition [exp_smart_constructor_def]: "FGCBase eb \<equiv> EFGC (FGCBBase eb)"
definition [exp_smart_constructor_def]: "FGCSeq esf esb \<equiv> EFGC (FGCBSeq esf esb)"
definition [exp_smart_constructor_def]: "FGCGlobal_Call \<equiv> EFGC Global_Call"

lemma eval_exp_fgcall_FGCBaseI[intro]:
  assumes "eval_eb eb s t s' r"
  shows "eval_exp_fgcall (FGCBase eb) s t s' r"
  using assms unfolding FGCBase_def by auto

lemma eval_exp_fgcall_FGCBaseE[elim]:
  assumes "eval_exp_fgcall (FGCBase eb) s t s' r"
  obtains "eval_eb eb s t s' r"
  using assms unfolding FGCBase_def by auto

lemma eval_exp_fgcall_FGCSeqI[intro]:
  assumes "eval_esf esf s tf sf rf"
  and "eval_exp_fgcall esb sf tb s' r"
  and "t = tf + tb"
  shows "eval_exp_fgcall (FGCSeq esf esb) s t s' r"
  using assms unfolding FGCSeq_def by auto

lemma eval_exp_fgcall_FGCSeqE[elim]:
  assumes "eval_exp_fgcall (FGCSeq esf esb) s t s' r"
  obtains tf sf rf tb where "eval_esf esf s tf sf rf" "eval_exp_fgcall esb sf tb s' r" "t = tf + tb"
  using assms unfolding FGCSeq_def by blast

lemma eval_exp_fgcall_FGCGlobal_CallI[intro]:
  assumes "eval_gc gc s t s' r"
  shows "eval_exp_fgcall FGCGlobal_Call s t s' r"
  using assms unfolding FGCGlobal_Call_def by auto

lemma eval_exp_fgcall_FGCGlobal_CallE[elim]:
  assumes "eval_exp_fgcall FGCGlobal_Call s t s' r"
  obtains "eval_gc gc s t s' r"
  using assms unfolding FGCGlobal_Call_def by auto

lemma eval_exp_fgcall_induct[induct pred : eval_exp_fgcall, case_names FGCBase FGCSeq FGCGlobal_Call]:
  assumes "eval_exp_fgcall efgc s t s' r"
  and "\<And>eb s t s' r. eval_eb eb s t s' r \<Longrightarrow> P (FGCBase eb) s t s' r"
  and "\<And>esf s tf sf rf esb tb sb rb. eval_esf esf s tf sf rf \<Longrightarrow>
    eval_exp_fgcall esb sf tb sb rb \<Longrightarrow> P esb sf tb sb rb \<Longrightarrow> P (FGCSeq esf esb) s (tf + tb) sb rb"
  and "\<And>s t s' r. eval_gc gc s t s' r \<Longrightarrow> P FGCGlobal_Call s t s' r"
  shows "P efgc s t s' r"
using assms
proof (elim eval_exp_fgcall.induct, goal_cases)
  case 1 then show ?case
  apply (subst (asm) eval_egc_fgcall_def)
  proof (erule eval_exp_global_call_base.induct, goal_cases)
    case 1 then show ?case
    by (elim eval_exp_seq_base.induct, goal_cases) (fold exp_smart_constructor_def, auto)
  qed (fold exp_smart_constructor_def, auto)
qed

end

lemma eval_exp_fgcall_mono[mono]:
  assumes "\<And>e s t s' r. f1 e s t s' r \<longrightarrow> g1 e s t s' r"
  and "\<And>e s t s' r. f2 e s t s' r \<longrightarrow> g2 e s t s' r"
  and "\<And>e s t s' r. f3 e s t s' r \<longrightarrow> g3 e s t s' r"
  shows "eval_exp_fgcall f1 f2 f3 gc e s t s' r \<longrightarrow> eval_exp_fgcall g1 g2 g3 gc e s t s' r"
proof
  assume "eval_exp_fgcall f1 f2 f3 gc e s t s' r"
  from this assms show "eval_exp_fgcall g1 g2 g3 gc e s t s' r"
    by (induction rule: eval_exp_fgcall_induct) fast+
qed


end