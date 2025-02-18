\<^marker>\<open>creator Bilel Ghorbel, Florian Kessler\<close>

section "Small step semantics of IMP "

subsection "Small step semantics definition"
theory Small_StepT  imports Main Com "IMP-.Rel_Pow" begin

paragraph "Summary"
text\<open>We give small step semantics with time for IMP.
Based on the small step semantics definition time for IMP\<close>

inductive
  small_step :: "com * state \<Rightarrow> com * state \<Rightarrow> bool"  (infix "\<rightarrow>" 55)
where
Assign:  "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))" |

Seq1:    "(SKIP;;c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |
Seq2:    "(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s') \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s) \<rightarrow> (c\<^sub>1';;c\<^sub>2,s')" |

IfTrue:  "s b \<noteq> 0 \<Longrightarrow> (IF b \<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>1,s)" |
IfFalse: "s b = 0 \<Longrightarrow> (IF b \<noteq>0  THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |

WhileTrue:   "s b \<noteq> 0 \<Longrightarrow> (WHILE b\<noteq>0 DO c,s) \<rightarrow>
            (c ;; WHILE b \<noteq>0 DO c,s)" |
WhileFalse:   "s b = 0 \<Longrightarrow> (WHILE b\<noteq>0 DO c,s) \<rightarrow>
            (SKIP,s)"

subsection "Transitive Closure"
abbreviation
  small_step_pow :: "com * state \<Rightarrow> nat \<Rightarrow> com * state \<Rightarrow> bool" ("_ \<rightarrow>\<^bsup>_\<^esup> _" 55)
  where "x \<rightarrow>\<^bsup>t\<^esup> y == (rel_pow  small_step t)  x y"

bundle small_step_syntax
begin
notation small_step (infix "\<rightarrow>" 55) and
         small_step_pow ("_ \<rightarrow>\<^bsup>_\<^esup> _" 55)
end

subsection\<open>Executability\<close>

code_pred small_step .

experiment begin
values "{(c',map t [''x'',''y'',''z''], n) |c' t n.
   ((''x'' ::= A (V ''z'');; ''y'' ::=A ( V ''x''),
    <''x'' := 3, ''y'' := 7, ''z'' := 5>) \<rightarrow>\<^bsup>n\<^esup> (c',t))}"
end
subsection\<open>Proof infrastructure\<close>

subsubsection\<open>Induction rules\<close>

text\<open>The default induction rule @{thm[source] small_step.induct} only works
for lemmas of the form \<open>a \<rightarrow> b \<Longrightarrow> \<dots>\<close> where \<open>a\<close> and \<open>b\<close> are
not already pairs \<open>(DUMMY,DUMMY)\<close>. We can generate a suitable variant
of @{thm[source] small_step.induct} for pairs by ``splitting'' the arguments
\<open>\<rightarrow>\<close> into pairs:\<close>
lemmas small_step_induct = small_step.induct[split_format(complete)]


subsubsection\<open>Proof automation\<close>

declare small_step.intros[simp,intro]


text\<open>Rule inversion:\<close>

inductive_cases SkipE[elim!]: "(SKIP,s) \<rightarrow> ct"
inductive_cases AssignE[elim!]: "(x::=a,s) \<rightarrow> ct"
inductive_cases SeqE[elim]: "(c1;;c2,s) \<rightarrow> ct"
inductive_cases IfE[elim!]: "(IF b\<noteq>0 THEN c1 ELSE c2,s) \<rightarrow> ct"
inductive_cases WhileE[elim]: "(WHILE b\<noteq>0 DO c, s) \<rightarrow> ct"

text\<open>A simple property:\<close>
lemma deterministic:
  "cs \<rightarrow> cs' \<Longrightarrow> cs \<rightarrow> cs'' \<Longrightarrow> cs'' = cs'"
  apply(induction arbitrary: cs'' rule: small_step.induct)
        apply blast+
     apply auto
  done

lemma small_step_t_deterministic: "cs \<rightarrow>\<^bsup> t \<^esup> cs' \<Longrightarrow> cs \<rightarrow>\<^bsup> t \<^esup> cs'' \<Longrightarrow> cs'' = cs'"
  apply(induction t arbitrary: cs)
  using deterministic apply auto
  by blast


subsection "Progress property"
text "every command costs time"
lemma small_step_progress: "(c, s) \<rightarrow>\<^bsup> p \<^esup> t \<Longrightarrow> t \<noteq> (c, s)  \<Longrightarrow> p > 0"
  apply(induction p) by auto

subsection "Sequence properties"
declare rel_pow_intros[simp,intro]

text "sequence property"
lemma star_seq2: "(c1,s) \<rightarrow>\<^bsup>t\<^esup> (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow>\<^bsup> t \<^esup> (c1';;c2,s')"
proof(induction t arbitrary: c1 c1' s s')
  case (Suc t)
  then obtain c1'' s'' where "(c1,s) \<rightarrow> (c1'', s'')"
                         and "(c1'', s'')  \<rightarrow>\<^bsup> t \<^esup>  (c1', s')" by auto
  moreover then have "(c1'';;c2, s'') \<rightarrow>\<^bsup> t \<^esup> (c1';;c2, s')" using Suc by simp
  ultimately show ?case by auto
qed auto

text "sequence time is one plus sum of the sub-commands times"
lemma seq_comp:
  "\<lbrakk> (c1,s1) \<rightarrow>\<^bsup> t1 \<^esup> (SKIP,s2); (c2,s2) \<rightarrow>\<^bsup> t2 \<^esup> (c3,s3) \<rbrakk>
   \<Longrightarrow> (c1;;c2, s1) \<rightarrow>\<^bsup> t1 + t2 +1 \<^esup> (c3,s3)"
proof (induction t1 arbitrary: c1 s1)
  case 0
  then have "(c1;;c2, s1) \<rightarrow> (c2, s2)" by auto
  then show ?case using 0  by simp
next
  case (Suc t1)
  then obtain c1' s1' where *: "(c1, s1) \<rightarrow> (c1',s1')" and "(c1',s1') \<rightarrow>\<^bsup> t1 \<^esup> (SKIP,s2)"
    using relpowp_Suc_E2 by auto
  then have "(c1';;c2, s1') \<rightarrow>\<^bsup> t1 + t2 + 1 \<^esup> (c3, s3)" using Suc by blast
  then show ?case using Suc by auto
qed

lemma small_step_cant_continue_after_reaching_SKIP: "(c1, s1) \<rightarrow>\<^bsup> t1 \<^esup> (SKIP, s2)
  \<Longrightarrow> (c1, s1) \<rightarrow>\<^bsup> t2 \<^esup> (c3, s3)
  \<Longrightarrow> t2 \<le> t1"
proof(rule ccontr)
  assume "(c1, s1) \<rightarrow>\<^bsup>t1\<^esup> (SKIP, s2)" "(c1, s1) \<rightarrow>\<^bsup>t2\<^esup> (c3, s3)" "\<not> t2 \<le> t1"
  then obtain t3 where "t2 = t1 + t3" "t3 > 0"
    by (metis less_imp_add_positive not_le)
  hence "(c1, s1) \<rightarrow>\<^bsup> t1 + t3 \<^esup> (c3, s3)"
    using \<open>(c1, s1) \<rightarrow>\<^bsup> t2 \<^esup> (c3, s3)\<close>
    by auto
  then obtain c4s4 where "(c1, s1) \<rightarrow>\<^bsup>t1\<^esup> c4s4" "c4s4 \<rightarrow>\<^bsup>t3\<^esup> (c3, s3)"
    using \<open>(c1, s1) \<rightarrow>\<^bsup>t2\<^esup> (c3, s3)\<close> rel_pow_sum_decomp[OF \<open>(c1, s1) \<rightarrow>\<^bsup> t1 + t3 \<^esup> (c3, s3)\<close>]
    by blast
  hence "c4s4 = (SKIP, s2)"
    using small_step_t_deterministic \<open>(c1, s1) \<rightarrow>\<^bsup>t1\<^esup> (SKIP, s2)\<close>
    by simp
  hence "t3 = 0"
    using \<open>c4s4 \<rightarrow>\<^bsup>t3\<^esup> (c3, s3)\<close>
    by (cases t3) auto
  thus False using \<open>t3 > 0\<close> by simp
qed

end