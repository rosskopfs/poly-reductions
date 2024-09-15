theory big_step_Logt
  imports "IMP_Minus.AExp" "IMP_Minus.Com" "HOL-IMP.Star" Main  "IMP_Minus.Big_StepT"  
   Cook_Levin.Basics Cook_Levin.Combinations  Cook_Levin.Elementary   Cook_Levin.Arithmetic 
begin


fun aexp_time::"aexp\<Rightarrow>(vname\<Rightarrow>nat) \<Rightarrow>nat" where
"aexp_time (A a) s = Suc (nlength(atomVal a s)) "|
"aexp_time (Plus a1 a2) s =Suc (nlength( max (atomVal a1 s) (atomVal a2 s))+1)"|
"aexp_time (Sub a1 a2) s = Suc (nlength(max (atomVal a1 s) (atomVal  a2 s)))"|
"aexp_time (Parity a)  s= Suc (nlength(atomVal a s))"|
"aexp_time (RightShift a) s = Suc (nlength(atomVal a s))"


inductive
  big_step_Logt :: "com \<times> AExp.state \<Rightarrow> nat \<Rightarrow> AExp.state \<Rightarrow> bool"  ("_ \<Rightarrow>\<^bsup> _ \<^esup>\<^esup> _" 55)
where
Skip: "(SKIP,s) \<Rightarrow>\<^bsup> 0 \<^esup>\<^esup> s"|
Assign_vname: "(x ::= a, s) \<Rightarrow>\<^bsup>max (aexp_time a s) (Suc (nlength (s x))) \<^esup>\<^esup> s(x := aval a s)" |
Seq: "\<lbrakk> (c1,s1) \<Rightarrow>\<^bsup> x \<^esup>\<^esup> s2;  (c2,s2) \<Rightarrow>\<^bsup> y \<^esup>\<^esup> s3 ;z=x+y\<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow>\<^bsup>z \<^esup>\<^esup> s3" |
IfTrue: "\<lbrakk> s b \<noteq> 0;  (c1,s) \<Rightarrow>\<^bsup> x \<^esup>\<^esup> t; y=x+1 \<rbrakk> \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> y \<^esup>\<^esup> t" |
IfFalse: "\<lbrakk> s b = 0; (c2,s) \<Rightarrow>\<^bsup> x \<^esup>\<^esup> t; y=x+1  \<rbrakk> \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> y \<^esup>\<^esup> t" |
WhileFalse: "\<lbrakk> s b = 0 \<rbrakk> \<Longrightarrow> (WHILE b \<noteq>0 DO c,s) \<Rightarrow>\<^bsup> Suc (Suc 0)\<^esup>\<^esup> s" |
WhileTrue: "\<lbrakk> s1 b \<noteq> 0;  (c,s1) \<Rightarrow>\<^bsup> x\<^esup>\<^esup> s2;  (WHILE b \<noteq>0 DO c, s2) \<Rightarrow>\<^bsup> y \<^esup>\<^esup> s3; 1+x+y=z  \<rbrakk> 
    \<Longrightarrow> (WHILE b \<noteq>0 DO c, s1) \<Rightarrow>\<^bsup> z \<^esup>\<^esup> s3" 

declare big_step_Logt.intros [intro]

text "Induction rules with pair splitting"
lemmas big_step_Logt_induct = big_step_Logt.induct[split_format(complete)]

subsection "Rule inversion"
inductive_cases Skip_tE[elim!]: "(SKIP,s) \<Rightarrow>\<^bsup> x \<^esup>\<^esup> t"
inductive_cases Assign_tE[elim!]: "(x ::= a,s) \<Rightarrow>\<^bsup> p  \<^esup>\<^esup> t"
inductive_cases Seq_tE[elim!]: "(c1;;c2,s1) \<Rightarrow>\<^bsup> p \<^esup>\<^esup> s3"
inductive_cases If_tE[elim!]: "(IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup> x  \<^esup>\<^esup>  t"
inductive_cases While_tE[elim]: "(WHILE b \<noteq>0 DO c,s) \<Rightarrow>\<^bsup> x  \<^esup>\<^esup>  t"
lemma Seq': "\<lbrakk> (c1,s1) \<Rightarrow>\<^bsup> x  \<^esup>\<^esup>  s2;  (c2,s2) \<Rightarrow>\<^bsup> y  \<^esup>\<^esup>  s3  \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow>\<^bsup> x + y  \<^esup>\<^esup>  s3"
  by auto


text "Rule inversion use examples:"
lemma "(IF b \<noteq>0 THEN SKIP ELSE SKIP, s) \<Rightarrow>\<^bsup> x  \<^esup>\<^esup>  t \<Longrightarrow> t = s"
  by blast

lemma assumes "(IF b \<noteq>0 THEN SKIP ELSE SKIP, s) \<Rightarrow>\<^bsup> x  \<^esup>\<^esup>  t"
  shows "t = s"
  using assms apply cases by auto
(*
lemma assign_t_simp:
  "((x ::= a,s) \<Rightarrow>\<^bsup>Suc (nlength (aval a s))\<^esup>\<^esup>   s') \<longleftrightarrow> (s' = s(x := aval a s))"
  by (auto)

subsection "Determinism of Big semantics of IMP-"
theorem big_step_t_determ2: "\<lbrakk> (c,s) \<Rightarrow>\<^bsup> p \<^esup>\<^esup> t; (c,s) \<Rightarrow>\<^bsup> q \<^esup>\<^esup> u \<rbrakk> \<Longrightarrow> (u = t \<and> p=q)"
  apply  (induction arbitrary: u q rule: big_step_Logt_induct)
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

lemma bigstep_det: "(c1, s) \<Rightarrow>\<^bsup> p1\<^esup>\<^esup>t1 \<Longrightarrow> (c1, s) \<Rightarrow>\<^bsup> p \<^esup>\<^esup> t \<Longrightarrow> p1=p \<and> t1=t"
  using big_step_t_determ2 by simp


lemma seq_is_noop[simp]: "(SKIP, s) \<Rightarrow>\<^bsup>t\<^esup>\<^esup> s' \<longleftrightarrow> (t = Suc 0 \<and> s = s')" by auto

lemma seq_skip[simp]: "(c ;; SKIP, s) \<Rightarrow>\<^bsup>Suc t\<^esup>\<^esup> s' \<longleftrightarrow> (c, s) \<Rightarrow>\<^bsup>t\<^esup>\<^esup> s'" by auto

subsection "Progress property"
text "every command costs time"
lemma bigstep_progress: "(c, s) \<Rightarrow>\<^bsup> p \<^esup>\<^esup> t \<Longrightarrow> p > 0"
  apply(induct rule: big_step_Logt.induct, auto) done

lemma terminates_in_state_intro: "(c, s) \<Rightarrow>\<^bsup>t \<^esup>\<^esup> s' \<Longrightarrow> s' = s'' \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup>t \<^esup>\<^esup> s''"
  by simp

lemma terminates_in_time_state_intro: "(c, s) \<Rightarrow>\<^bsup>t \<^esup>\<^esup> s' \<Longrightarrow> t = t' \<Longrightarrow> s' = s'' 
  \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup>t' \<^esup>\<^esup> s''"
  by simp

lemma terminates_in_time_state_intro': "(c', s) \<Rightarrow>\<^bsup>t \<^esup>\<^esup> s' \<Longrightarrow> t = t' \<Longrightarrow> s' = s'' \<Longrightarrow> c' = c
  \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup>t' \<^esup>\<^esup> s''"
  by simp

method dest_com  = 
  (match premises in a: "\<lbrakk>loop_cond; state_upd\<rbrakk> \<Longrightarrow> (_, s) \<Rightarrow>\<^bsup>t \<^esup>\<^esup> s'"
    for s s' t loop_cond state_upd \<Rightarrow> \<open>rule terminates_in_time_state_intro'[OF a]\<close>)

method dest_com' = 
  (match premises in a[thin]: "\<lbrakk>loop_cond; state_upd; (_, s) \<Rightarrow>\<^bsup>t \<^esup>\<^esup>s'\<rbrakk> \<Longrightarrow> P" 
    for s s' t loop_cond state_upd P  \<Rightarrow>
   \<open>match premises in b[thin]: "(While _ _, s2) \<Rightarrow>\<^bsup>t2 \<^esup>\<^esup>s2'"
      for s2 s2' t2 \<Rightarrow> \<open>insert a[OF _ _ b]\<close>\<close>)


method dest_com_init_while = 
  (match premises in a[thin]: "\<lbrakk>loop_cond; state_upd; ((_ ;; While _ _), s) \<Rightarrow>\<^bsup>t \<^esup>\<^esup> s'\<rbrakk> \<Longrightarrow> P" 
    for s s' t loop_cond state_upd P  \<Rightarrow>
   \<open>match premises in b[thin]: "((_ ;; While _ _), s2) \<Rightarrow>\<^bsup>t2 \<^esup>\<^esup> s2'"
      for s2 s2' t2 \<Rightarrow> \<open>insert a[OF _ _ b]\<close>\<close>)



lemma terminates_split_if : "(P s \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup>t1 \<^esup>\<^esup> s1 ) \<Longrightarrow> 
(\<not> P s \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup>t2 \<^esup>\<^esup>s2 ) \<Longrightarrow> (c,s) \<Rightarrow>\<^bsup>if P s then t1 else t2 \<^esup>\<^esup>  if P s then s1 else s2"
  by auto

lemma AssignD': 
"(x ::= a, s) \<Rightarrow>\<^bsup> 2\<^esup>\<^esup> s' \<Longrightarrow> s' = s (x:= aval a s)"
  by (auto simp add: eval_nat_numeral)

lemma com_only_vars: "\<lbrakk>(c, s) \<Rightarrow>\<^bsup> t  \<^esup>\<^esup> s'; x \<notin> set (Max_Constant.all_variables c)\<rbrakk> \<Longrightarrow> s x = s' x"
  by (induction arbitrary: t rule: big_step_Logt_induct)  auto

lemma Seq'': "\<lbrakk> (c1,s1) \<Rightarrow>\<^bsup> x  \<^esup>\<^esup> s2 \<and> P s2; P s2 \<Longrightarrow> (c2,s2) \<Rightarrow>\<^bsup> y  \<^esup>\<^esup> s3 \<and> Q s3; Q s3 \<Longrightarrow> R s3 \<rbrakk>
             \<Longrightarrow> (c1;;c2, s1) \<Rightarrow>\<^bsup> x + y  \<^esup>\<^esup> s3 \<and> R s3"
  by auto

lemma WhileI:
"\<lbrakk>(s1 b \<noteq> 0 \<Longrightarrow> (c,s1) \<Rightarrow>\<^bsup> x  \<^esup>\<^esup> s2 \<and> (WHILE b \<noteq>0 DO c, s2) \<Rightarrow>\<^bsup> y  \<^esup>\<^esup> s3);
  (s1 b = 0 \<Longrightarrow> s1 = s3);
  z = (if s1 b \<noteq> 0 then 1+x+y else 2)\<rbrakk>
        \<Longrightarrow> (WHILE b \<noteq>0 DO c, s1) \<Rightarrow>\<^bsup> z  \<^esup>\<^esup> s3" 
  by (auto simp add: WhileTrue WhileFalse numeral_2_eq_2)

lemma IfI:
"\<lbrakk>s b \<noteq> 0 \<Longrightarrow> (c1,s) \<Rightarrow>\<^bsup> x1  \<^esup>\<^esup> t1;
  s b = 0 \<Longrightarrow> (c2,s) \<Rightarrow>\<^bsup> x2  \<^esup>\<^esup> t2;
  y = (if s b \<noteq> 0 then x1 else x2) + 1;
  t = (if s b \<noteq> 0 then t1 else t2)\<rbrakk>
        \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> y  \<^esup>\<^esup> t" 
  by (auto simp add: IfTrue IfFalse)

lemma IfE: 
"(IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> (if s b \<noteq> 0 then x1 else x2) + 1  \<^esup>\<^esup> (if s b \<noteq> 0 then s1 else s2) \<Longrightarrow> 
 \<lbrakk>\<lbrakk>s b \<noteq> 0; (if s b \<noteq> 0 then x1 else x2) + 1 = x1 + 1; 
  (if s b \<noteq> 0 then s1 else s2) = s1; (c1,s) \<Rightarrow>\<^bsup> x1  \<^esup>\<^esup> s1\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>s b = 0; (if s b \<noteq> 0 then x1 else x2) + 1 = x2 + 1;
   (if s b \<noteq> 0 then s1 else s2) = s2; (c2,s) \<Rightarrow>\<^bsup> x2  \<^esup>\<^esup>s2\<rbrakk> \<Longrightarrow> P\<rbrakk>
        \<Longrightarrow> P"
  by (auto simp add: IfTrue IfFalse)

thm Seq_tE

lemma IfD:
"(IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> (if s b \<noteq> 0 then x1 else x2) + 1  \<^esup>\<^esup> (if s b \<noteq> 0 then t1 else t2) \<Longrightarrow> 
 \<lbrakk>\<lbrakk>s b \<noteq> 0; (c1,s) \<Rightarrow>\<^bsup> x1  \<^esup>\<^esup> t1\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>s b = 0; (c2,s) \<Rightarrow>\<^bsup> x2  \<^esup>\<^esup> t2\<rbrakk> \<Longrightarrow> P\<rbrakk>
        \<Longrightarrow> P" 
  by (auto simp add: IfTrue IfFalse)




lemma AssignI:
"\<lbrakk>s' = s (x:= aval a s)\<rbrakk>
        \<Longrightarrow> (x ::= a, s) \<Rightarrow>\<^bsup> Suc (nlength (aval a s))  \<^esup>\<^esup> s'" 
  by (auto simp add: Assign)


lemma AssignD: "(x ::= a, s) \<Rightarrow>\<^bsup> t  \<^esup>\<^esup> s' \<Longrightarrow> t = Suc (nlength (aval a s)) \<and> s' = s(x := aval a s)"
  by auto

lemma compose_programs_1:
  "(c2, s2) \<Rightarrow>\<^bsup> y  \<^esup>\<^esup>s3 \<Longrightarrow> (c1, s1) \<Rightarrow>\<^bsup> x \<^esup>\<^esup> s2 \<Longrightarrow> 
    ((c1;; c2, s1) \<Rightarrow>\<^bsup> x + y  \<^esup>\<^esup>s3 \<Longrightarrow> P)
   \<Longrightarrow> P"
  by auto

lemma compose_programs_2:
  "(c1, s1) \<Rightarrow>\<^bsup> x  \<^esup>\<^esup> s2 \<Longrightarrow> (c2, s2) \<Rightarrow>\<^bsup> y  \<^esup>\<^esup> s3 \<Longrightarrow> 
    ((c1;; c2, s1) \<Rightarrow>\<^bsup> x + y  \<^esup>\<^esup> s3 \<Longrightarrow> P)
   \<Longrightarrow> P"
  by auto

lemma While_tE_time:
"(WHILE b\<noteq>0 DO c, s) \<Rightarrow>\<^bsup> x  \<^esup>\<^esup> t \<Longrightarrow>
  (x = Suc (Suc 0) \<Longrightarrow> t = s \<Longrightarrow> s b = 0 \<Longrightarrow> P) \<Longrightarrow>
  (\<And>x' s2 y. 0 < s b \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup> x'  \<^esup>\<^esup> s2 \<Longrightarrow> (WHILE b\<noteq>0 DO c, s2) \<Rightarrow>\<^bsup> y  \<^esup>\<^esup> t \<Longrightarrow> x = Suc (x' + y) \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma Seq_tE_While_init:
  "(WHILE v \<noteq>0 DO c2, s2) \<Rightarrow>\<^bsup> y  \<^esup>\<^esup> s3 \<Longrightarrow> (c1, s1) \<Rightarrow>\<^bsup> x  \<^esup>\<^esup> s2 \<Longrightarrow> 
    ((c1;; WHILE v \<noteq>0 DO c2, s1) \<Rightarrow>\<^bsup> x + y  \<^esup>\<^esup> s3 \<Longrightarrow> P)
   \<Longrightarrow> P"
  by auto


abbreviation TP0::"com\<Rightarrow>tape list" where
"TP0 prog\<equiv> IMPminus_state_to_TM_tape_list prog (\<lambda>x.(0::nat))"
*)

(*
An appropriate idd must satisfies the following condition:
(1) \forall x \in var_set prog, idd x \<ge>3 
\<and> Max(idd`(var_set prog))<last_tape 
*)
end