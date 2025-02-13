\<^marker>\<open>creator Fabian Huch\<close>
section "Big step semantics of IMP-- "

theory IMP_Minus_Minus_Big_StepT
  imports IMP_Minus_Minus_Small_StepT
begin

\<^marker>\<open>title "fig:imp_minus_def"\<close>
inductive
  big_step :: "com * state \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool"  ("_ \<Rightarrow>\<^bsup>_\<^esup> _" 55)
  where
Skip[intro!]: "(SKIP, s) \<Rightarrow>\<^bsup>0\<^esup> s" |
Assign[intro!]:  "(x ::= v, s) \<Rightarrow>\<^bsup>1\<^esup> (s(x \<mapsto> v))" |

Seq:    "(c\<^sub>1,s) \<Rightarrow>\<^bsup>n\<^sub>1\<^esup> s\<^sub>2 \<Longrightarrow> (c\<^sub>2,s\<^sub>2) \<Rightarrow>\<^bsup>n\<^sub>2\<^esup> s\<^sub>3 \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s) \<Rightarrow>\<^bsup>n\<^sub>1+n\<^sub>2+1\<^esup> s\<^sub>3" |

IfTrue:  "\<exists>b \<in> set bs. s b \<noteq> Some Zero \<Longrightarrow> (c\<^sub>1,s) \<Rightarrow>\<^bsup>n\<^esup> s' \<Longrightarrow> (IF bs \<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2,s) \<Rightarrow>\<^bsup>n+1\<^esup> s'" |
IfFalse: "\<forall>b \<in> set bs. s b = Some Zero \<Longrightarrow> (c\<^sub>2,s) \<Rightarrow>\<^bsup>n\<^esup> s' \<Longrightarrow> (IF bs \<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2,s) \<Rightarrow>\<^bsup>n+1\<^esup> s'" |
WhileTrue:
 "\<lbrakk>(\<exists>b \<in> set bs. s b \<noteq> Some Zero); (c,s) \<Rightarrow>\<^bsup>n\<^sub>1\<^esup> s\<^sub>2; 
  ((WHILE bs \<noteq>0 DO c),s\<^sub>2) \<Rightarrow>\<^bsup>n\<^sub>2\<^esup> s\<^sub>3 \<rbrakk> \<Longrightarrow>
  ((WHILE bs \<noteq>0 DO c), s)\<Rightarrow>\<^bsup>n\<^sub>1+n\<^sub>2+2\<^esup>s\<^sub>3" |
WhileFalse[intro!]:   "(\<forall>b \<in> set bs. s b = Some Zero) \<Longrightarrow> (WHILE bs \<noteq>0 DO c,s) \<Rightarrow>\<^bsup>1\<^esup> s"

lemmas big_step_induct = big_step.induct[split_format(complete)]

declare big_step.intros[intro]

inductive_cases SkipE[elim!]: "(SKIP,s) \<Rightarrow>\<^bsup>n\<^esup> t"
inductive_cases AssignE[elim!]: "(x ::= a,s) \<Rightarrow>\<^bsup>n\<^esup> t"
inductive_cases SeqE[elim!]: "(c1;;c2,s1) \<Rightarrow>\<^bsup>n\<^esup> s3"
inductive_cases IfE[elim!]: "(IF bs \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>n\<^esup> t"
inductive_cases WhileE[elim]: "(WHILE b \<noteq>0 DO c,s) \<Rightarrow>\<^bsup>n\<^esup> t"

lemma seq_comp[intro]:
  "(c,s) \<rightarrow>\<^bsup>n\<^esup> (SKIP,s\<^sub>2) \<Longrightarrow> (c\<^sub>2,s\<^sub>2) \<rightarrow>\<^bsup>n\<^sub>2\<^esup> (SKIP,s\<^sub>3) \<Longrightarrow> (c;;c\<^sub>2,s) \<rightarrow>\<^bsup>Suc (n+n\<^sub>2)\<^esup> (SKIP,s\<^sub>3)"
proof -
  assume *:"(c,s) \<rightarrow>\<^bsup>n\<^esup> (SKIP,s\<^sub>2)"
  from star_seq2[OF this, of c\<^sub>2] have 1:"(c;; c\<^sub>2, s) \<rightarrow>\<^bsup>1+n\<^esup> (c\<^sub>2, s\<^sub>2)"
    using rel_pow_sum[of small_step] by fastforce 
  assume "(c\<^sub>2,s\<^sub>2) \<rightarrow>\<^bsup>n\<^sub>2\<^esup> (SKIP,s\<^sub>3)"
  with 1 show ?thesis using rel_pow_sum by force
qed

declare fun_upd_apply[simp del]

declare IMP_Minus_Minus_Big_StepT.SeqE[elim!]
lemma step: "(c,s) \<rightarrow> (c',s') \<Longrightarrow> (c',s') \<Rightarrow>\<^bsup>n\<^esup> t \<Longrightarrow> (c,s) \<Rightarrow>\<^bsup>n+1\<^esup> t"
proof (induction c s c' s' arbitrary: t n rule: small_step_induct)
  case (Assign x v s)
  hence 0: "n=0 \<and> t=s(x \<mapsto> v)" by (cases n) auto
  thus ?case using big_step.Assign by auto
next
  case (Seq1 c\<^sub>2 s)
  then show ?case using Seq[of SKIP s 0 s ] by (auto intro!: Suc_eq_plus1)
next
  case (Seq2 c\<^sub>1 s c\<^sub>1' s' c\<^sub>2)
  then show ?case apply auto
    by (metis Seq Suc_eq_plus1 add_Suc)
next
  case (IfTrue bs s c\<^sub>1 c\<^sub>2)
  then show ?case by blast
next
  case (IfFalse bs s c\<^sub>1 c\<^sub>2)
  then show ?case by blast
next
  case (WhileTrue bs s c)
  then show ?case using big_step.intros(6) by fastforce
next
  case (WhileFalse bs s c)
  then show ?case using big_step.WhileFalse by force
qed

lemma "(c,s) \<Rightarrow>\<^bsup>n\<^esup> s' = (c,s) \<rightarrow>\<^bsup>n\<^esup> (SKIP,s')"
proof
  assume "(c,s) \<Rightarrow>\<^bsup>n\<^esup> s'"
  then show "(c,s) \<rightarrow>\<^bsup>n\<^esup> (SKIP,s')"
  proof (induction c s n s' rule: big_step_induct)
    case (Assign x v s)
    then show ?case by blast
  qed auto
next
  assume "(c,s) \<rightarrow>\<^bsup>n\<^esup> (SKIP,s')"
  then show "(c,s) \<Rightarrow>\<^bsup>n\<^esup> s'"
    by (induction n c s SKIP s' rule: rel_pow_induct) (auto dest: step)
qed

end