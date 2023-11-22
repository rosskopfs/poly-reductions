\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expression_Tail_Calls
  imports
    Expression_Final_Global_Calls
begin

datatype ('eb, 'esf) exp_tcall = TC "('eb, 'esf) exp_fgcall"

context
  fixes eval_eb :: "('t :: {plus}, 'r, 'si, 'sv, 'eb) eval_time"
  and eval_esf :: "('t, 'r, 'si, 'sv, 'esf) eval_time"
begin

inductive eval_exp_tcall ::
  "('t, 'r, 'si, 'sv, ('eb, 'esf) exp_tcall) eval_time"
where
  eval_exp_tcall_TC: "eval_exp_fgcall eval_eb eval_esf eval_exp_tcall (TC e) e s t s' r \<Longrightarrow>
    eval_exp_tcall (TC e) s t s' r"

definition "eval_efgcall_tcall \<equiv> eval_exp_fgcall eval_eb eval_esf eval_exp_tcall"

lemma eval_exp_tcall_TCI[intro]:
  assumes "eval_efgcall_tcall (TC e) e s t s' r"
  shows "eval_exp_tcall (TC e) s t s' r"
  using assms eval_exp_tcall.intros unfolding eval_efgcall_tcall_def by blast

lemma eval_exp_tcall_TCE[elim]:
  assumes "eval_exp_tcall (TC e) s t s' r"
  obtains "eval_efgcall_tcall (TC e) e s t s' r"
  using assms eval_exp_tcall.cases unfolding eval_efgcall_tcall_def by blast

lemma eval_efgcall_tcall_FGCBaseI[intro]:
  assumes "eval_eb eb s t s' r"
  shows "eval_efgcall_tcall etc (FGCBase eb) s t s' r"
  using assms unfolding eval_efgcall_tcall_def by auto

lemma eval_efgcall_tcall_FGCBaseE[elim]:
  assumes "eval_efgcall_tcall etc (FGCBase eb) s t s' r"
  obtains "eval_eb eb s t s' r"
  using assms unfolding eval_efgcall_tcall_def by auto

lemma eval_efgcall_tcall_FGCSeqI[intro]:
  assumes "eval_esf esf s tf sf rf"
  and "eval_efgcall_tcall etc esb sf tb s' r"
  and "t = tf + tb"
  shows "eval_efgcall_tcall etc (FGCSeq esf esb) s t s' r"
  using assms unfolding eval_efgcall_tcall_def by auto

lemma eval_efgcall_tcall_FGCSeqE[elim]:
  assumes "eval_efgcall_tcall etc (FGCSeq esf esb) s t s' r"
  obtains tf sf rf tb where "eval_esf esf s tf sf rf"
    "eval_efgcall_tcall etc esb sf tb s' r" "t = tf + tb"
  using assms unfolding eval_efgcall_tcall_def by blast

lemma eval_efgcall_tcall_FGCGlobal_CallI[intro]:
  assumes "eval_exp_tcall etc s t s' r"
  shows "eval_efgcall_tcall etc FGCGlobal_Call s t s' r"
  using assms unfolding eval_efgcall_tcall_def by auto

lemma eval_efgcall_tcall_FGCGlobal_CallE[elim]:
  assumes "eval_efgcall_tcall etc FGCGlobal_Call s t s' r"
  obtains "eval_exp_tcall etc s t s' r"
  using assms unfolding eval_efgcall_tcall_def by auto

lemma not_eval_exp_tcall_TC_FGCGlobal_Call[iff]: "\<not>(eval_exp_tcall (TC FGCGlobal_Call) s t s' r)"
  by (rule notI, induction "TC FGCGlobal_Call :: ('eb, 'esf) exp_tcall" s t s' r
    rule: eval_exp_tcall.induct)
  (auto simp: exp_smart_constructor_def)

corollary not_eval_efgcall_tcall_TC_FGCGlobal_Call_FGCGlobal_Call[iff]:
  "\<not>(eval_efgcall_tcall (TC FGCGlobal_Call) FGCGlobal_Call s t s' r)"
  by blast

lemma eval_efgcall_tcall_induct[induct pred : eval_efgcall_tcall,
  case_names eq_TC FGCBase FGCSeq FGCGlobal_Call]:
  assumes "eval_efgcall_tcall etc e s t s' r"
  and [simp]: "etc = TC efgc"
  and "\<And>eb s t s' r. eval_eb eb s t s' r \<Longrightarrow> P (FGCBase eb) s t s' r"
  and "\<And>esf s tf sf rf esb tb sb rb. eval_esf esf s tf sf rf \<Longrightarrow>
    eval_efgcall_tcall etc esb sf tb sb rb \<Longrightarrow> P esb sf tb sb rb \<Longrightarrow> P (FGCSeq esf esb) s (tf + tb) sb rb"
  and "\<And>s t s' r. eval_efgcall_tcall etc efgc s t s' r \<Longrightarrow> P efgc s t s' r \<Longrightarrow>
    P FGCGlobal_Call s t s' r"
  shows "P e s t s' r"
using assms(1)[unfolded eval_efgcall_tcall_def]
proof (induction e s t s' r rule: eval_exp_fgcall_induct)
  case (FGCGlobal_Call s t s' r)
  from \<open>eval_exp_tcall etc s t s' r\<close>[simplified] have "P efgc s t s' r"
  proof (induction "TC efgc" s t s' r rule: eval_exp_tcall.induct)
    case (eval_exp_tcall_TC s t s' r)
    from \<open>eval_exp_fgcall _ _ _ _ efgc s t s' r\<close> show ?case
    proof (induction efgc s t s' r rule: eval_exp_fgcall_induct)
      case (FGCSeq esf s tf sf rf esb tb sb rb)
      then have "eval_efgcall_tcall etc esb sf tb sb rb" unfolding eval_efgcall_tcall_def
        by (intro mp[OF eval_exp_fgcall_mono[of _ eval_eb]]) auto
      with FGCSeq show ?case by (blast intro: assms)
    qed (auto intro!: assms)
  qed
  with FGCGlobal_Call show ?case by (auto intro!: assms)
qed (blast intro: assms[unfolded eval_efgcall_tcall_def])+

corollary eval_exp_tcall_induct[induct pred : eval_exp_tcall, case_names Base Seq]:
  assumes "eval_exp_tcall e s t s' r"
  and "\<And>eb s t s' r. eval_eb eb s t s' r \<Longrightarrow> P e s t s' r"
  and "\<And>esf s tf sf rf esb tb sb rb. eval_esf esf s tf sf rf \<Longrightarrow>
    eval_efgcall_tcall e esb sf tb sb rb \<Longrightarrow> P e sf tb sb rb \<Longrightarrow> P e s (tf + tb) sb rb"
  shows "P e s t s' r"
proof -
  from assms(1) obtain efgc efgc' where "eval_efgcall_tcall (TC efgc) efgc' s t s' r" "TC efgc = e"
    unfolding eval_efgcall_tcall_def by (cases e) auto
  then have "P (TC efgc) s t s' r"
    by (induction efgc' s t s' r rule: eval_efgcall_tcall_induct[of "TC efgc"])
    (simp; rule assms; blast)+
  with \<open>TC efgc = e\<close> show ?thesis by simp
qed

end

lemma eval_efgcall_tcall_mono[mono]:
  assumes "\<And>e s t s' r. f1 e s t s' r \<longrightarrow> g1 e s t s' r"
  and "\<And>e s t s' r. f2 e s t s' r \<longrightarrow> g2 e s t s' r"
  shows "eval_efgcall_tcall f1 f2 (TC efgc) e s t s' r \<longrightarrow>
    eval_efgcall_tcall g1 g2 (TC efgc) e s t s' r"
proof
  assume "eval_efgcall_tcall f1 f2 (TC efgc) e s t s' r"
  from this assms show "eval_efgcall_tcall g1 g2 (TC efgc) e s t s' r"
  by (induction rule: eval_efgcall_tcall_induct) fast+
qed

lemma eval_exp_tcall_mono[mono]:
  assumes "\<And>e s t s' r. f1 e s t s' r \<longrightarrow> g1 e s t s' r"
  and "\<And>e s t s' r. f2 e s t s' r \<longrightarrow> g2 e s t s' r"
  shows "eval_exp_tcall f1 f2 e s t s' r \<longrightarrow> eval_exp_tcall g1 g2 e s t s' r"
  apply (intro impI)
  apply (cases e, hypsubst)
  apply (rule eval_exp_tcall_TCI)
  apply (rule mp[OF eval_efgcall_tcall_mono])
  by (rule assms)+ fast


end