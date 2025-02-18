\<^marker>\<open>creator Mohammad Abdulaziz, Bilel Ghorbel, Florian Kessler\<close>
section "Big step semantics of IMP"
theory Big_StepT imports Main Com "HOL-Eisbach.Eisbach_Tools" begin

paragraph "Summary"
text\<open>We define big step semantics with time for IMP.
Based on the big step semantics definition with time of IMP\<close>

subsection "Big step semantics definition:"

text "In IMP Branching is only based on whether a variable's value equals 0."

inductive
  big_step_t :: "com \<times> state \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool"  ("_ \<Rightarrow>\<^bsup> _ \<^esup> _" 55)
where
Skip: "(SKIP,s) \<Rightarrow>\<^bsup> Suc (0::nat) \<^esup> s"|
Assign: "(x ::= a,s) \<Rightarrow>\<^bsup> Suc (Suc 0) \<^esup> s(x := aval a s)" |
Seq: "\<lbrakk> (c1,s1) \<Rightarrow>\<^bsup> x \<^esup> s2;  (c2,s2) \<Rightarrow>\<^bsup> y \<^esup> s3 ; z=x+y \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow>\<^bsup> z \<^esup> s3" |
IfTrue: "\<lbrakk> s b \<noteq> 0;  (c1,s) \<Rightarrow>\<^bsup> x \<^esup> t; y=x+1 \<rbrakk> \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> y \<^esup> t" |
IfFalse: "\<lbrakk> s b = 0; (c2,s) \<Rightarrow>\<^bsup> x \<^esup> t; y=x+1  \<rbrakk> \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> y \<^esup> t" |
WhileFalse: "\<lbrakk> s b = 0 \<rbrakk> \<Longrightarrow> (WHILE b \<noteq>0 DO c,s) \<Rightarrow>\<^bsup> Suc (Suc 0) \<^esup> s" |
WhileTrue: "\<lbrakk> s1 b \<noteq> 0;  (c,s1) \<Rightarrow>\<^bsup> x \<^esup> s2;  (WHILE b \<noteq>0 DO c, s2) \<Rightarrow>\<^bsup> y \<^esup> s3; 1+x+y=z  \<rbrakk>
    \<Longrightarrow> (WHILE b \<noteq>0 DO c, s1) \<Rightarrow>\<^bsup> z \<^esup> s3"

bundle big_step_syntax
begin
notation big_step_t ("_ \<Rightarrow>\<^bsup> _ \<^esup> _" 55)
end

code_pred big_step_t .

text "Some examples using the big step semantics"
experiment
begin

text "finding out the final state and running time of a command:"
schematic_goal ex: "(''x'' ::= A (N 5);; ''y'' ::= A (V ''x''), s) \<Rightarrow>\<^bsup> ?t \<^esup> ?s"
  apply(rule Seq)
    apply(rule Assign)
   apply simp
   apply(rule Assign)
  apply simp
  done


values "{(t, x). big_step_t (SKIP, \<lambda>_. 0) x t}"

values "{map t [''x''] |t x. (SKIP, <''x'' := 42>) \<Rightarrow>\<^bsup> x \<^esup> t}"

values "{map t [''x''] |t x. (''x'' ::=A (N 2), <''x'' := 42>) \<Rightarrow>\<^bsup> x \<^esup> t}"

values "{(map t [''x''],x) |t x. (WHILE ''x''\<noteq>0 DO ''x''::= Sub (V ''x'') (N 1),<''x'':=5>) \<Rightarrow>\<^bsup> x \<^esup> t }"

end

text "proof automation:"

text "Introduction rules:"
declare big_step_t.intros [intro]

text "Induction rules with pair splitting"
lemmas big_step_t_induct = big_step_t.induct[split_format(complete)]

subsection "Rule inversion"
inductive_cases Skip_tE[elim!]: "(SKIP,s) \<Rightarrow>\<^bsup> x \<^esup> t"
inductive_cases Assign_tE[elim!]: "(x ::= a,s) \<Rightarrow>\<^bsup> p \<^esup> t"
inductive_cases Seq_tE[elim!]: "(c1;;c2,s1) \<Rightarrow>\<^bsup> p \<^esup> s3"
inductive_cases If_tE[elim!]: "(IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup> x \<^esup> t"
inductive_cases While_tE[elim]: "(WHILE b \<noteq>0 DO c,s) \<Rightarrow>\<^bsup> x \<^esup> t"
lemma Seq': "\<lbrakk> (c1,s1) \<Rightarrow>\<^bsup> x \<^esup> s2;  (c2,s2) \<Rightarrow>\<^bsup> y \<^esup> s3  \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow>\<^bsup> x + y \<^esup> s3"
  by auto

text "Rule inversion use examples:"
lemma "(IF b \<noteq>0 THEN SKIP ELSE SKIP, s) \<Rightarrow>\<^bsup> x \<^esup> t \<Longrightarrow> t = s"
  by blast

lemma assumes "(IF b \<noteq>0 THEN SKIP ELSE SKIP, s) \<Rightarrow>\<^bsup> x \<^esup> t"
  shows "t = s"
  using assms apply cases by auto

lemma assign_t_simp:
  "((x ::= a,s) \<Rightarrow>\<^bsup> Suc(Suc 0) \<^esup>  s') \<longleftrightarrow> (s' = s(x := aval a s))"
  by (auto)

subsection "Determinism of Big semantics of IMP"
theorem big_step_t_determ2: "\<lbrakk> (c,s) \<Rightarrow>\<^bsup> p \<^esup> t; (c,s) \<Rightarrow>\<^bsup> q \<^esup> u \<rbrakk> \<Longrightarrow> (u = t \<and> p=q)"
  apply  (induction arbitrary: u q rule: big_step_t_induct)
    apply(elim Skip_tE) apply(simp)
    apply(elim Assign_tE) apply(simp)
  apply blast
    apply(elim If_tE) apply(simp) apply blast
    apply(elim If_tE)  apply (linarith) apply simp
    apply(erule While_tE) apply(simp) apply simp
  subgoal premises p for s1 b c x s2 y s3 z u q
    using p(7) apply(safe)
      apply(erule While_tE)
        using p(1-6) apply fast
        using p(1-6) apply (simp)
      apply(erule While_tE)
        using p(1-6) apply fast
        using p(1-6) by (simp)
done

lemma bigstep_det: "(c1, s) \<Rightarrow>\<^bsup> p1 \<^esup> t1 \<Longrightarrow> (c1, s) \<Rightarrow>\<^bsup> p \<^esup> t \<Longrightarrow> p1=p \<and> t1=t"
  using big_step_t_determ2 by simp

lemma seq_assign_t_simp:
  "((c ;; x ::= a, s) \<Rightarrow>\<^bsup> Suc(Suc t) \<^esup>  s')
  \<longleftrightarrow> (\<exists>s''. (c, s) \<Rightarrow>\<^bsup> t \<^esup> s'' \<and> s' = s''(x := aval a s''))"
proof
  assume "(c;; x ::= a, s) \<Rightarrow>\<^bsup> Suc (Suc t) \<^esup> s'"
  then obtain s'' where "(c, s) \<Rightarrow>\<^bsup> t \<^esup> s''" by auto
  have "s' = s''(x := aval a s'')" using \<open>(c;; x ::= a, s) \<Rightarrow>\<^bsup> Suc (Suc t) \<^esup> s'\<close>
    using bigstep_det \<open>(c, s) \<Rightarrow>\<^bsup> t \<^esup> s''\<close>
    by blast
  thus "\<exists>s''. (c, s) \<Rightarrow>\<^bsup> t \<^esup> s'' \<and> s' = s''(x := aval a s'')"
    using \<open>(c, s) \<Rightarrow>\<^bsup> t \<^esup> s''\<close>
    by blast
qed auto

lemma seq_assign_t_intro: "(c, s) \<Rightarrow>\<^bsup> t \<^esup> s'' \<Longrightarrow> s' = s''(x := aval a s'')
  \<Longrightarrow>(c ;; x ::= a, s) \<Rightarrow>\<^bsup> Suc(Suc t) \<^esup>  s'"
  using seq_assign_t_simp
  by auto

lemma seq_is_noop[simp]: "(SKIP, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<longleftrightarrow> (t = Suc 0 \<and> s = s')" by auto

lemma seq_skip[simp]: "(c ;; SKIP, s) \<Rightarrow>\<^bsup>Suc t\<^esup> s' \<longleftrightarrow> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s'" by auto

subsection "Progress property"
text "every command costs time"
lemma bigstep_progress: "(c, s) \<Rightarrow>\<^bsup> p \<^esup> t \<Longrightarrow> p > 0"
  apply(induct rule: big_step_t.induct, auto) done

subsection "abbreviations and properties"
abbreviation terminates ("\<down>") where "terminates cs \<equiv> (\<exists>n a. (cs \<Rightarrow>\<^bsup> n \<^esup> a))"
abbreviation thestate ("\<down>\<^sub>s") where "thestate cs \<equiv> (THE a. \<exists>n. (cs \<Rightarrow>\<^bsup> n \<^esup> a))"
abbreviation thetime ("\<down>\<^sub>t") where "thetime cs \<equiv> (THE n. \<exists>a. (cs \<Rightarrow>\<^bsup> n \<^esup> a))"


lemma bigstepT_the_cost: "(c, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<Longrightarrow> \<down>\<^sub>t(c, s) = t"
  using bigstep_det by blast

lemma bigstepT_the_state: "(c, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<Longrightarrow> \<down>\<^sub>s(c, s) = s'"
  using bigstep_det by blast

lemma SKIPnot: "(\<not> (SKIP, s) \<Rightarrow>\<^bsup> p \<^esup> t) \<longleftrightarrow> (s\<noteq>t \<or> p\<noteq>Suc 0)" by blast

lemma SKIPp: "\<down>\<^sub>t(SKIP,s) = Suc 0"
  apply(rule the_equality)
  apply fast
  apply auto done

lemma SKIPt: "\<down>\<^sub>s(SKIP,s) = s"
  apply(rule the_equality)
  apply fast
  apply auto done


lemma ASSp: "(THE p. Ex (big_step_t (x ::= e, s) p)) = Suc(Suc 0)"
  apply(rule the_equality)
  apply fast
  apply auto done

lemma ASSt: "(THE t. \<exists>p. (x ::= e, s) \<Rightarrow>\<^bsup> p \<^esup> t) = s(x := aval e s)"
  apply(rule the_equality)
  apply fast
  apply auto done

lemma ASSnot: "( \<not> (x ::= e, s) \<Rightarrow>\<^bsup> p \<^esup> t ) = (p\<noteq>Suc(Suc 0) \<or> t\<noteq>s(x := aval e s))"
  apply auto done

lemma If_THE_True: "Suc (THE n. \<exists>a. (c1, s) \<Rightarrow>\<^bsup> n \<^esup> a) =  (THE n. \<exists>a. (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> n \<^esup> a)"
     if T: "s b \<noteq> 0" and c1_t: "terminates (c1,s)" for s l
proof -
  from c1_t obtain p t where a: "(c1, s) \<Rightarrow>\<^bsup> p \<^esup> t" by blast
  with T have b: "(IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> p+1 \<^esup> t"  using IfTrue by simp
  from a bigstepT_the_cost have "(THE n. \<exists>a. (c1, s) \<Rightarrow>\<^bsup> n \<^esup> a) = p" by simp
  moreover from b bigstepT_the_cost have "(THE n. \<exists>a. (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> n \<^esup> a) = p+1" by simp
  ultimately show ?thesis by simp
qed

lemma If_THE_False:
 "Suc (THE n. \<exists>a. (c2, s) \<Rightarrow>\<^bsup> n \<^esup> a) =  (THE n. \<exists>a. (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> n \<^esup> a)"
     if T: "s b = 0" and c2_t: "\<down> (c2,s)" for s l
proof -
  from c2_t obtain p t where a: "(c2, s) \<Rightarrow>\<^bsup> p \<^esup> t"  by blast
  with T have b: "(IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> p+1 \<^esup> t"  using IfFalse by simp
  from a bigstepT_the_cost have "(THE n. \<exists>a. (c2, s) \<Rightarrow>\<^bsup> n \<^esup> a) = p" by simp
  moreover from b bigstepT_the_cost have "(THE n. \<exists>a. (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> n \<^esup> a) = p+1" by simp
  ultimately show ?thesis by simp
qed


lemma terminates_in_state_intro: "(c, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> s' = s'' \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s''"
  by simp

lemma terminates_in_time_state_intro: "(c, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> t = t' \<Longrightarrow> s' = s''
  \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup>t'\<^esup> s''"
  by simp

lemma terminates_in_time_state_intro': "(c', s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> t = t' \<Longrightarrow> s' = s'' \<Longrightarrow> c' = c
  \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup>t'\<^esup> s''"
  by simp

method dest_com  =
  (match premises in a: "\<lbrakk>loop_cond; state_upd\<rbrakk> \<Longrightarrow> (_, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
    for s s' t loop_cond state_upd \<Rightarrow> \<open>rule terminates_in_time_state_intro'[OF a]\<close>)

method dest_com' =
  (match premises in a[thin]: "\<lbrakk>loop_cond; state_upd; (_, s) \<Rightarrow>\<^bsup>t\<^esup> s'\<rbrakk> \<Longrightarrow> P"
    for s s' t loop_cond state_upd P  \<Rightarrow>
   \<open>match premises in b[thin]: "(While _ _, s2) \<Rightarrow>\<^bsup>t2\<^esup> s2'"
      for s2 s2' t2 \<Rightarrow> \<open>insert a[OF _ _ b]\<close>\<close>)


method dest_com_init_while =
  (match premises in a[thin]: "\<lbrakk>loop_cond; state_upd; ((_ ;; While _ _), s) \<Rightarrow>\<^bsup>t\<^esup> s'\<rbrakk> \<Longrightarrow> P"
    for s s' t loop_cond state_upd P  \<Rightarrow>
   \<open>match premises in b[thin]: "((_ ;; While _ _), s2) \<Rightarrow>\<^bsup>t2\<^esup> s2'"
      for s2 s2' t2 \<Rightarrow> \<open>insert a[OF _ _ b]\<close>\<close>)

(*method dest_com_init_while =
  (match premises in a[thin]: "\<lbrakk>loop_cond; state_upd; (v ::= a;; WHILE v \<noteq>0 DO _, s) \<Rightarrow>\<^bsup>t\<^esup> s'\<rbrakk> \<Longrightarrow> P"
    for v a s s' t loop_cond state_upd P  \<Rightarrow>
   \<open>match premises in b[thin]: "(v ::= a;; WHILE v \<noteq>0 DO _, s2) \<Rightarrow>\<^bsup>t2\<^esup> s2'"
      for s2 s2' t2 \<Rightarrow> \<open>insert a\<close>\<close>)*)

lemma terminates_split_if : "(P s \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup>t1\<^esup> s1 ) \<Longrightarrow>
(\<not> P s \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup>t2\<^esup> s2 ) \<Longrightarrow> (c,s) \<Rightarrow>\<^bsup>if P s then t1 else t2\<^esup>  if P s then s1 else s2"
  by auto

lemma AssignD':
"(x ::= a, s) \<Rightarrow>\<^bsup> 2 \<^esup> s' \<Longrightarrow> s' = s (x:= aval a s)"
  by (auto simp add: eval_nat_numeral)


lemma Seq'': "\<lbrakk> (c1,s1) \<Rightarrow>\<^bsup> x \<^esup> s2 \<and> P s2; P s2 \<Longrightarrow> (c2,s2) \<Rightarrow>\<^bsup> y \<^esup> s3 \<and> Q s3; Q s3 \<Longrightarrow> R s3 \<rbrakk>
             \<Longrightarrow> (c1;;c2, s1) \<Rightarrow>\<^bsup> x + y \<^esup> s3 \<and> R s3"
  by auto

lemma WhileI:
"\<lbrakk>(s1 b \<noteq> 0 \<Longrightarrow> (c,s1) \<Rightarrow>\<^bsup> x \<^esup> s2 \<and> (WHILE b \<noteq>0 DO c, s2) \<Rightarrow>\<^bsup> y \<^esup> s3);
  (s1 b = 0 \<Longrightarrow> s1 = s3);
  z = (if s1 b \<noteq> 0 then 1+x+y else 2)\<rbrakk>
        \<Longrightarrow> (WHILE b \<noteq>0 DO c, s1) \<Rightarrow>\<^bsup> z \<^esup> s3"
  by (auto simp add: WhileTrue WhileFalse numeral_2_eq_2)

lemma IfI:
"\<lbrakk>s b \<noteq> 0 \<Longrightarrow> (c1,s) \<Rightarrow>\<^bsup> x1 \<^esup> t1;
  s b = 0 \<Longrightarrow> (c2,s) \<Rightarrow>\<^bsup> x2 \<^esup> t2;
  y = (if s b \<noteq> 0 then x1 else x2) + 1;
  t = (if s b \<noteq> 0 then t1 else t2)\<rbrakk>
        \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> y \<^esup> t"
  by (auto simp add: IfTrue IfFalse)

lemma IfE:
"(IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> (if s b \<noteq> 0 then x1 else x2) + 1 \<^esup> (if s b \<noteq> 0 then s1 else s2) \<Longrightarrow>
 \<lbrakk>\<lbrakk>s b \<noteq> 0; (if s b \<noteq> 0 then x1 else x2) + 1 = x1 + 1;
  (if s b \<noteq> 0 then s1 else s2) = s1; (c1,s) \<Rightarrow>\<^bsup> x1 \<^esup> s1\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>s b = 0; (if s b \<noteq> 0 then x1 else x2) + 1 = x2 + 1;
   (if s b \<noteq> 0 then s1 else s2) = s2; (c2,s) \<Rightarrow>\<^bsup> x2 \<^esup> s2\<rbrakk> \<Longrightarrow> P\<rbrakk>
        \<Longrightarrow> P"
  by (auto simp add: IfTrue IfFalse)

thm Seq_tE

lemma IfD:
"(IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> (if s b \<noteq> 0 then x1 else x2) + 1 \<^esup> (if s b \<noteq> 0 then t1 else t2) \<Longrightarrow>
 \<lbrakk>\<lbrakk>s b \<noteq> 0; (c1,s) \<Rightarrow>\<^bsup> x1 \<^esup> t1\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>s b = 0; (c2,s) \<Rightarrow>\<^bsup> x2 \<^esup> t2\<rbrakk> \<Longrightarrow> P\<rbrakk>
        \<Longrightarrow> P"
  by (auto simp add: IfTrue IfFalse)




lemma AssignI:
"\<lbrakk>s' = s (x:= aval a s)\<rbrakk>
        \<Longrightarrow> (x ::= a, s) \<Rightarrow>\<^bsup> Suc (Suc 0) \<^esup> s'"
  by (auto simp add: Assign)

lemma AssignI':
"\<lbrakk>s' = s (x:= aval a s)\<rbrakk>
        \<Longrightarrow> (x ::= a, s) \<Rightarrow>\<^bsup> 2 \<^esup> s'"
  by (auto simp add: Assign eval_nat_numeral)

lemma AssignI'':
"\<lbrakk>s' = s (x:= aval a s)\<rbrakk>
        \<Longrightarrow> (x ::= a, s) \<Rightarrow>\<^bsup> 2 \<^esup> s' \<and> s' = s'"
  by (auto simp add: Assign eval_nat_numeral)

lemma AssignD: "(x ::= a, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<Longrightarrow> t = 2 \<and> s' = s(x := aval a s)"
  by auto

lemma compose_programs_1:
  "(c2, s2) \<Rightarrow>\<^bsup> y \<^esup> s3 \<Longrightarrow> (c1, s1) \<Rightarrow>\<^bsup> x \<^esup> s2 \<Longrightarrow>
    ((c1;; c2, s1) \<Rightarrow>\<^bsup> x + y \<^esup> s3 \<Longrightarrow> P)
   \<Longrightarrow> P"
  by auto

lemma compose_programs_2:
  "(c1, s1) \<Rightarrow>\<^bsup> x \<^esup> s2 \<Longrightarrow> (c2, s2) \<Rightarrow>\<^bsup> y \<^esup> s3 \<Longrightarrow>
    ((c1;; c2, s1) \<Rightarrow>\<^bsup> x + y \<^esup> s3 \<Longrightarrow> P)
   \<Longrightarrow> P"
  by auto

lemma While_tE_time:
"(WHILE b\<noteq>0 DO c, s) \<Rightarrow>\<^bsup> x \<^esup> t \<Longrightarrow>
  (x = Suc (Suc 0) \<Longrightarrow> t = s \<Longrightarrow> s b = 0 \<Longrightarrow> P) \<Longrightarrow>
  (\<And>x' s2 y. 0 < s b \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup> x' \<^esup> s2 \<Longrightarrow> (WHILE b\<noteq>0 DO c, s2) \<Rightarrow>\<^bsup> y \<^esup> t \<Longrightarrow> x = Suc (x' + y) \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma Seq_tE_While_init:
  "(WHILE v \<noteq>0 DO c2, s2) \<Rightarrow>\<^bsup> y \<^esup> s3 \<Longrightarrow> (c1, s1) \<Rightarrow>\<^bsup> x \<^esup> s2 \<Longrightarrow>
    ((c1;; WHILE v \<noteq>0 DO c2, s1) \<Rightarrow>\<^bsup> x + y \<^esup> s3 \<Longrightarrow> P)
   \<Longrightarrow> P"
  by auto

method dest_com_gen =
  (erule compose_programs_1[where ?c2.0 = "(Com.While _ _)"], assumption,
    erule compose_programs_2[where ?c1.0 = "(_;; Com.While _ _)"], assumption,
    (match premises
      in a[thin]:
      "(init_while_cond;;
                WHILE _ \<noteq>0 DO (loop_body;; init_while_cond);;
                after_loop, _) \<Rightarrow>\<^bsup>_\<^esup> _"
    for init_while_cond loop_body after_loop  \<Rightarrow>
      \<open>match premises in b[thin]: "\<lbrakk>loop_cond; state_upd; _\<rbrakk> \<Longrightarrow> P"
       for loop_cond state_upd P \<Rightarrow> \<open>subst b[OF _ _ a]\<close>\<close>))


method dest_com_gen_time =
  (erule compose_programs_1[where ?c2.0 = "(Com.While _ _)"], assumption,
    erule compose_programs_2[where ?c1.0 = "(_;; Com.While _ _)"], assumption,
    (match premises
      in a[thin]:
      "(init_while_cond;;
                WHILE _ \<noteq>0 DO (loop_body;; init_while_cond);;
                after_loop, _) \<Rightarrow>\<^bsup>_\<^esup> _"
    for init_while_cond loop_body after_loop  \<Rightarrow>
      \<open>match premises in b[thin]: "\<lbrakk>loop_cond; state_upd; _\<rbrakk> \<Longrightarrow> P"
       for loop_cond state_upd P \<Rightarrow> \<open>subst b[OF _ _ a, simplified add.assoc]\<close>\<close>))

end