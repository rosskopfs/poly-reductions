\<^marker>\<open>creator Bilel Ghorbel, Florian Kessler\<close>

section "Small step semantics of IMP-- "

subsection "IMP-- Small step semantics definition"
theory IMP_Minus_Minus_Small_StepT
  imports Main IMP_Minus_Minus_Com "IMP_Minus.Rel_Pow"
begin

paragraph "Summary"
text\<open>We give small step semantics with time for IMP--.
Based on the small step semantics definition time for IMP-. In contrast to IMP-, we use partial
maps to represent states. That has the simple reason the we designed this with translation to
SAS++ in mind, which also uses partial states. \<close>

type_synonym state = "vname \<rightharpoonup> bit"

inductive
  small_step :: "com * state  \<Rightarrow> com * state \<Rightarrow> bool"  ("_ \<rightarrow> _" 55)
  where
Assign:  "(x ::= v, s) \<rightarrow> (SKIP, s(x \<mapsto> v))" |

Seq1:    "(SKIP;;c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |
Seq2:    "(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s') \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s) \<rightarrow> (c\<^sub>1';;c\<^sub>2,s')" |

IfTrue:  "\<exists>b \<in> set bs. s b \<noteq> Some Zero \<Longrightarrow> (IF bs \<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>1,s)" |
IfFalse: "\<forall>b \<in> set bs. s b = Some Zero \<Longrightarrow> (IF bs \<noteq>0  THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |

WhileTrue:   "(\<exists>b \<in> set bs. s b \<noteq> Some Zero) \<Longrightarrow> (WHILE bs \<noteq>0 DO c,s) \<rightarrow>
            (c ;; (WHILE bs \<noteq>0 DO c), s)" |
WhileFalse:   "(\<forall>b \<in> set bs. s b = Some Zero) \<Longrightarrow> (WHILE bs \<noteq>0 DO c,s) \<rightarrow>
            (SKIP,s)"

subsection "Transitive Closure"
abbreviation
  small_step_pow :: "com * state \<Rightarrow> nat \<Rightarrow> com * state \<Rightarrow> bool" ("_ \<rightarrow>\<^bsup>_\<^esup> _" 55)
  where "x \<rightarrow>\<^bsup>t\<^esup> y == (rel_pow small_step t) x y"

bundle small_step_syntax
begin
notation small_step (infix "\<rightarrow>" 55) and
         small_step_pow ("_ \<rightarrow>\<^bsup>_\<^esup> _" 55)
end

subsection\<open>Executability\<close>

code_pred small_step .

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
inductive_cases Assign[elim!]: "(x ::= v,s) \<rightarrow> ct"
inductive_cases SeqE[elim]: "(c1;;c2,s) \<rightarrow> ct"
inductive_cases IfE[elim!]: "(IF b\<noteq>0 THEN c1 ELSE c2,s) \<rightarrow> ct"
inductive_cases WhileE[elim]: "(WHILE b\<noteq>0 DO c, s) \<rightarrow> ct"

subsection "Sequence properties"
declare rel_pow_intros[simp,intro]

text\<open>A simple property:\<close>
lemma deterministic:
  "cs \<rightarrow> cs' \<Longrightarrow> cs \<rightarrow> cs'' \<Longrightarrow> cs'' = cs'"
apply(induction arbitrary: cs'' rule: small_step.induct)
  by blast+

text "sequence property"
lemma star_seq2: "(c1,s) \<rightarrow>\<^bsup>t\<^esup> (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow>\<^bsup> t \<^esup> (c1';;c2,s')"
proof(induction t arbitrary: c1 c1' s s')
  case (Suc t)
  then obtain c1'' s'' where "(c1,s) \<rightarrow> (c1'', s'')"
                         and "(c1'', s'')  \<rightarrow>\<^bsup> t \<^esup>  (c1', s')" by auto
  moreover then have "(c1'';;c2, s'') \<rightarrow>\<^bsup> t \<^esup> (c1';;c2, s')" using Suc by simp
  ultimately show ?case by auto
qed auto


lemma if_trueI[intro]:
  "is1 v = Some One \<Longrightarrow> v \<in> set x1 \<Longrightarrow> (IF x1\<noteq>0 THEN c11 ELSE c12, is1) \<rightarrow> (c11, is1)"
  by force

lemma if_falseI[intro]:
  "map_of (map (\<lambda>v. (v, Zero)) (remdups x1)) \<subseteq>\<^sub>m is1
    \<Longrightarrow> (IF x1\<noteq>0 THEN c11 ELSE c12, is1) \<rightarrow> (c12, is1)"
proof -
  assume "map_of (map (\<lambda>v. (v, Zero)) (remdups x1)) \<subseteq>\<^sub>m is1"
  have "v \<in> set (remdups x1) \<Longrightarrow> map_of (map (\<lambda>v. (v, Zero)) (remdups x1)) v = Some Zero" for v
    by(induction x1) (auto split: if_splits)
  hence "\<forall>v \<in> set x1. is1 v = Some Zero"
    apply(auto simp: map_le_def dom_map_of_conv_image_fst)
    by (metis (mono_tags, lifting) \<open>map_of (map (\<lambda>v. (v, Zero)) (remdups x1)) \<subseteq>\<^sub>m is1\<close> domI map_le_def)
  thus ?thesis by simp
qed

lemma while_trueI[intro]:
  "is1 v = Some One \<Longrightarrow> v \<in> set x1 \<Longrightarrow> (WHILE x1\<noteq>0 DO c1, is1) \<rightarrow> (c1 ;; WHILE x1\<noteq>0 DO c1, is1)"
  by force

lemma while_falseI[intro]:
  "map_of (map (\<lambda>v. (v, Zero)) (remdups x1)) \<subseteq>\<^sub>m is1
    \<Longrightarrow> (WHILE x1\<noteq>0 DO c1, is1) \<rightarrow> (SKIP, is1)"
proof -
  assume "map_of (map (\<lambda>v. (v, Zero)) (remdups x1)) \<subseteq>\<^sub>m is1"
  have "v \<in> set (remdups x1) \<Longrightarrow> map_of (map (\<lambda>v. (v, Zero)) (remdups x1)) v = Some Zero" for v
    by(induction x1) (auto split: if_splits)
  hence "\<forall>v \<in> set x1. is1 v = Some Zero"
    apply(auto simp: map_le_def dom_map_of_conv_image_fst)
    by (metis (mono_tags, lifting) \<open>map_of (map (\<lambda>v. (v, Zero)) (remdups x1)) \<subseteq>\<^sub>m is1\<close> domI map_le_def)
  thus ?thesis by simp
qed

subsection \<open>Functional definition\<close>

text \<open>We also give a definition of small step semantics as a function rather than as a relation.
    We show the equivalence between the two definitions. We also give some useful Lemmas to show
    that IMP-- terminates in some state. \<close>

fun small_step_fun:: "com * state \<Rightarrow> com * state" where
"small_step_fun (SKIP, s) = (SKIP, s)" |
"small_step_fun (x ::= v, s) = (SKIP, s(x \<mapsto> v))" |
"small_step_fun (c\<^sub>1;;c\<^sub>2,s) = (if c\<^sub>1 = SKIP then (c\<^sub>2,s)
  else  (fst (small_step_fun (c\<^sub>1, s)) ;;c\<^sub>2, snd (small_step_fun (c\<^sub>1, s))))" |
"small_step_fun (IF bs \<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2,s) = (if \<exists>b \<in> set bs. s b \<noteq> Some Zero then (c\<^sub>1,s) else (c\<^sub>2,s))" |
"small_step_fun (WHILE bs \<noteq>0 DO c,s) = (if  \<exists>b \<in> set bs. s b \<noteq> Some Zero
  then (c ;; (WHILE bs \<noteq>0 DO c), s) else (SKIP,s))"

fun t_small_step_fun:: "nat \<Rightarrow> com * state \<Rightarrow> com * state" where
"t_small_step_fun 0 = id" |
"t_small_step_fun (Suc t) = (t_small_step_fun t) \<circ> small_step_fun"

lemma t_small_step_fun_ge_0: "t > 0
  \<Longrightarrow> t_small_step_fun t (c, s) = t_small_step_fun (t - 1) (small_step_fun (c, s))"
proof-
  assume "t > 0"
  then obtain t' where "t = Suc t'" using lessE by blast
  thus ?thesis by simp
qed

lemma t_small_step_fun_small_step_fun: "t_small_step_fun t (small_step_fun cs)
  = t_small_step_fun (t + 1) cs"
  by simp

lemma small_step_fun_t_small_step_fun: "small_step_fun (t_small_step_fun t (c, s))
  = t_small_step_fun (t + 1) (c, s)"
proof(induction t arbitrary: c s)
  case (Suc t)
  let ?c' = "fst (small_step_fun (c, s))"
  let ?s' = "snd (small_step_fun (c, s))"
  have "small_step_fun (t_small_step_fun t (?c', ?s')) = t_small_step_fun t (small_step_fun (?c', ?s'))"
    using Suc t_small_step_fun_small_step_fun by presburger
  thus ?case by auto
qed auto

lemma t_small_step_fun_SKIP[simp]: "t_small_step_fun t (SKIP, s) = (SKIP, s)"
  apply(induction t)
  by auto

lemma t_small_step_fun_terminate_iff: "t_small_step_fun t (c1, s1) = (SKIP, s2) \<longleftrightarrow>
  ((c1 = SKIP \<and> s1 = s2) \<or> (t > 0 \<and> t_small_step_fun (t - 1) (small_step_fun (c1, s1))
    = (SKIP, s2)))"
  apply(auto simp: t_small_step_fun_ge_0)
   apply (metis One_nat_def id_apply less_Suc_eq_0_disj prod.inject t_small_step_fun.elims t_small_step_fun_ge_0)
  by (metis One_nat_def Pair_inject id_apply less_Suc_eq_0_disj t_small_step_fun.elims t_small_step_fun_ge_0)

lemma t_small_step_fun_decomposition: "t_small_step_fun (a + b) cs
  = t_small_step_fun a (t_small_step_fun b cs)"
  apply(induction a arbitrary: cs)
  by(auto simp: small_step_fun_t_small_step_fun)

lemma t_small_step_fun_increase_time: "t \<le> t' \<Longrightarrow> t_small_step_fun t (c1, s1) = (SKIP, s2)
  \<Longrightarrow> t_small_step_fun t' (c1, s1) = (SKIP, s2)"
  using t_small_step_fun_decomposition[where ?a="t' - t" and ?b="t"] by simp

lemma exists_terminating_iff: "(\<exists>t < Suc t'.
  t_small_step_fun t (c, s) = (SKIP, s'))
  \<longleftrightarrow>  t_small_step_fun t' (c, s) = (SKIP, s')"
  using t_small_step_fun_increase_time by (auto simp: less_Suc_eq_le)

lemma terminates_then_can_reach_SKIP_in_seq: "t_small_step_fun t (c1, s1) = (SKIP, s2)
  \<Longrightarrow> (\<exists>t' \<le> t. t_small_step_fun t' (c1 ;; c2, s1) = (SKIP ;; c2, s2))"
proof(induction t arbitrary: c1 s1)
  case (Suc t)
  have "c1 = SKIP \<or> c1 \<noteq> SKIP" by auto
  thus ?case using Suc
  proof (elim disjE)
    assume *: "c1 \<noteq> SKIP"
    let ?c1' = "fst (small_step_fun (c1, s1))"
    let ?s1' = "snd (small_step_fun (c1, s1))"
    have "t_small_step_fun t (?c1', ?s1') = (SKIP, s2)" using *
      by (metis Suc.prems Suc_eq_plus1 prod.collapse t_small_step_fun_small_step_fun)
    then obtain t' where "t' \<le> t \<and> t_small_step_fun t' (?c1' ;; c2, ?s1') = (SKIP ;; c2, s2)"
      using Suc by blast
    thus ?case using * by auto
  qed auto
qed auto

lemma seq_terminates_iff: "t_small_step_fun t (a ;; b, s1) = (SKIP, s2) \<longleftrightarrow>
  (\<exists>t' s3. t' < t \<and> t_small_step_fun t' (a, s1) = (SKIP, s3)
  \<and> t_small_step_fun (t - (t' + 1)) (b, s3) = (SKIP, s2))"
proof(induction t arbitrary: a s1)
  case (Suc t)
  show ?case
  proof
    assume *: "t_small_step_fun (Suc t) (a;; b, s1) = (SKIP, s2)"
    have "a = SKIP \<or> a \<noteq> SKIP" by auto
    thus "\<exists>t' s3. t' < Suc t \<and> t_small_step_fun t' (a, s1) = (SKIP, s3)
        \<and> t_small_step_fun (Suc t - (t' + 1)) (b, s3) = (SKIP, s2)"
    using * proof (elim disjE)
      assume **: "a \<noteq> SKIP"
      let ?a' = "fst (small_step_fun (a, s1))"
      let ?s1' = "snd (small_step_fun (a, s1))"
      have "t_small_step_fun t (?a' ;; b, ?s1') = (SKIP, s2)" using * **
        by (auto simp: t_small_step_fun_terminate_iff)
      then obtain t' s3 where "t' < t \<and> t_small_step_fun t' (?a', ?s1') = (SKIP, s3)
        \<and> t_small_step_fun (t - (t' + 1)) (b, s3) = (SKIP, s2)" using Suc by auto
      hence "t' + 1 < t + 1 \<and> t_small_step_fun (t' + 1) (a, s1) = (SKIP, s3)
        \<and> t_small_step_fun (t - (t' + 1)) (b, s3) = (SKIP, s2)" by(auto)
      thus ?thesis by auto
    qed auto
  next
    assume "\<exists>t' s3. t' < Suc t \<and> t_small_step_fun t' (a, s1) = (SKIP, s3)
      \<and> t_small_step_fun (Suc t - (t' + 1)) (b, s3) = (SKIP, s2)"
    then obtain t' s3 where t'_def: "t' < Suc t \<and> t_small_step_fun t' (a, s1) = (SKIP, s3)
      \<and> t_small_step_fun (Suc t - (t' + 1)) (b, s3) = (SKIP, s2)" by blast
    then obtain t'' where t''_def: "t'' \<le> t' \<and> t_small_step_fun t'' (a ;; b, s1) = (SKIP ;; b, s3)"
      using terminates_then_can_reach_SKIP_in_seq by blast
    hence "t_small_step_fun (t'' + ((Suc t - (t' + 1)) + 1)) (a ;; b, s1)
      = t_small_step_fun (Suc t - (t' + 1) + 1) (SKIP ;; b, s3)"
      using t_small_step_fun_decomposition[where ?b="t''"] t'_def by (metis add.commute)
    also have "... = t_small_step_fun (Suc t  - (t' + 1)) (b, s3)" using t'_def
      by(auto simp: t_small_step_fun_ge_0)
    also have "... = (SKIP, s2)" using t'_def by simp
    ultimately show "t_small_step_fun (Suc t) (a ;; b, s1) = (SKIP, s2)"
      apply -
      apply(rule t_small_step_fun_increase_time[where ?t="t'' + ((Suc t - (t' + 1)) + 1)"])
      using t'_def t''_def by(auto)
  qed
qed auto

lemma seq_terminates_when: "t1 + t2 < t \<Longrightarrow> t_small_step_fun t1 (a, s1) = (SKIP, s3)
  \<Longrightarrow> t_small_step_fun t2 (b, s3) = (SKIP, s2)
  \<Longrightarrow> t_small_step_fun t (a ;; b, s1) = (SKIP, s2)"
  apply(auto simp: seq_terminates_iff)
  by (metis Nat.add_diff_assoc2 add_lessD1 diff_Suc_Suc diff_add_inverse le_add_same_cancel1
      less_natE t_small_step_fun_increase_time zero_le)

lemma seq_terminates_when': "t_small_step_fun t1 (a, s1) = (SKIP, s3)
  \<Longrightarrow> t_small_step_fun t2 (b, s3) = (SKIP, s2)
  \<Longrightarrow> t1 + t2 < t
  \<Longrightarrow> t_small_step_fun t (a ;; b, s1) = (SKIP, s2)"
  apply(auto simp: seq_terminates_iff)
  by (metis Nat.add_diff_assoc2 add_lessD1 diff_Suc_Suc diff_add_inverse le_add_same_cancel1
      less_natE t_small_step_fun_increase_time zero_le)


lemma small_step_fun_small_step: "c1 \<noteq> SKIP \<Longrightarrow> small_step_fun (c1, s1) = (c2, s2)
  \<longleftrightarrow> (c1, s1) \<rightarrow> (c2, s2)"
  apply(induction c1 arbitrary: s1 c2 s2)
    apply auto
  apply fastforce
  by (metis SeqE fstI eq_snd_iff)+

lemma small_step_fun_small_step': "c1 \<noteq> SKIP \<Longrightarrow>
   (c1, s1) \<rightarrow> small_step_fun (c1, s1)"
  apply(induction c1 arbitrary: s1)
  by auto

lemma t_small_step_fun_t_small_step_equivalence: "(t_small_step_fun t (c1, s1) = (SKIP, s2))
  \<longleftrightarrow> (\<exists>t' \<le> t. (c1, s1) \<rightarrow>\<^bsup>t'\<^esup> (SKIP, s2))"
proof(induction t arbitrary: c1 s1 rule: nat_less_induct)
  case (1 n)
  hence IH: "t'' < n
     \<Longrightarrow> (t_small_step_fun t'' (c1, s1) = (SKIP, s2)) \<longleftrightarrow> (\<exists>t'\<le>t''. (c1, s1) \<rightarrow>\<^bsup>t'\<^esup> (SKIP, s2))"
    for t'' c1 s1 by simp
  show ?case
  proof(cases n)
    case (Suc t)
    have "c1 = SKIP \<or> c1 \<noteq> SKIP" by auto
    thus ?thesis
    proof(elim disjE)
      assume "c1 \<noteq> SKIP"
      show ?thesis
      proof
        assume "t_small_step_fun n (c1, s1) = (SKIP, s2)"
        hence "(c1, s1) \<rightarrow> small_step_fun (c1, s1)
          \<and> (\<exists>t' \<le> t. small_step_fun (c1, s1) \<rightarrow>\<^bsup>t'\<^esup> (SKIP, s2))"
          using IH[where ?c1.0="fst (small_step_fun (c1, s1))"
              and ?s1.0="snd (small_step_fun (c1, s1))" and ?t''=t]
          \<open>c1 \<noteq> SKIP\<close> small_step_fun_small_step' Suc by auto
        thus "\<exists>t' \<le> n. (c1, s1) \<rightarrow>\<^bsup>t'\<^esup> (SKIP, s2)" using Suc by auto
      next
        assume "\<exists>t' \<le> n. (c1, s1) \<rightarrow>\<^bsup>t'\<^esup> (SKIP, s2)"
        then obtain t' where t'_def: "t' \<le> n \<and> (c1, s1) \<rightarrow>\<^bsup>t'\<^esup> (SKIP, s2)" by blast
        then obtain t'' where t''_def: "t' = Suc t''" using \<open>c1 \<noteq> SKIP\<close> by (metis prod.inject rel_pow.cases)
        then obtain c3 s3 where "(c1, s1) \<rightarrow> (c3, s3) \<and> (c3, s3) \<rightarrow>\<^bsup>t''\<^esup> (SKIP, s2)"
          using t'_def by auto
        hence "small_step_fun (c1, s1) = (c3, s3) \<and> t_small_step_fun t'' (c3, s3) = (SKIP, s2)"
          using IH[where ?c1.0=c3 and ?s1.0=s3 and ?t''=t''] small_step_fun_small_step \<open>c1 \<noteq> SKIP\<close>
            t'_def t''_def by auto
        hence "t_small_step_fun (Suc t'') (c1, s1) = (SKIP, s2)" by simp
        thus "t_small_step_fun n (c1, s1) = (SKIP, s2)" using t'_def t''_def
           t_small_step_fun_increase_time by blast
      qed
    next
      assume "c1 = SKIP"
      thus ?thesis using rel_pow.cases by fastforce
    qed
  qed auto
qed

end