\<^marker>\<open>creator Bilel Ghorbel, Florian Kessler\<close>

section "Equivalence of big step and small step semantics"

theory Big_Step_Small_Step_Equivalence imports Big_StepT Small_StepT begin

paragraph "Introduction"
text "We show that the big and small step semantics with time we defined for IMP- are equivalent."

text "from Big step to small step semantics"
lemma big_to_small_helper: "(c, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<Longrightarrow> t = Suc t' \<Longrightarrow> (c, s) \<rightarrow>\<^bsup> t' \<^esup> (SKIP, s')"
proof (induction arbitrary: t' rule: big_step_t_induct)
  case (Skip s)
  then show ?case by simp
next
  case (Assign x a s)
  then have "t' = Suc 0" by auto
  moreover have "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))" by blast
  ultimately show ?case by blast
next
  case (Seq c1 s1 x s2 c2 y s3 z)
  then obtain x' y' where suc_ex: "x = Suc x'" "y = Suc y'"
    by (meson bigstep_progress gr0_implies_Suc)
  then have "(c1, s1) \<rightarrow>\<^bsup> x' \<^esup> (SKIP, s2)" using Seq by auto
  moreover have "(c2, s2) \<rightarrow>\<^bsup> y' \<^esup> (SKIP, s3)" using Seq suc_ex by auto
  ultimately have "(c1 ;; c2, s1) \<rightarrow>\<^bsup> (x' + y' + 1) \<^esup> (SKIP, s3)" using seq_comp by simp  
  then show ?case using Seq suc_ex by simp
next
  case (IfTrue s b c1 x t y c2)
  then obtain x' where "x = Suc x'" using bigstep_progress gr0_implies_Suc by blast
  then show ?case using IfTrue by auto
next
  case (IfFalse s b c2 x t y c1)
  then obtain x' where "x = Suc x'" by (meson bigstep_progress gr0_implies_Suc)
  then show ?case using IfFalse by auto
next
  case (WhileFalse s b c)
  then show ?case by fastforce
next
  case (WhileTrue s1 b c x s2 y s3 z)
  let ?w = "WHILE b \<noteq>0 DO c"
  obtain x' y' where suc_def:"x =Suc x'" "y = Suc y'"
    by (meson WhileTrue.hyps(2) WhileTrue.hyps(3) bigstep_progress gr0_implies_Suc)
  have "(?w, s1) \<rightarrow>\<^bsup> 1 \<^esup> (c ;; ?w, s1)" using WhileTrue by auto
  moreover have "(c ;; ?w, s1)\<rightarrow>\<^bsup> x' \<^esup> (SKIP ;; ?w, s2)" 
    using WhileTrue by (simp add: suc_def star_seq2) 
  moreover have "(SKIP ;; ?w, s2) \<rightarrow>\<^bsup> 1 \<^esup>(?w, s2)" by auto
  moreover have "(?w, s2) \<rightarrow>\<^bsup> y' \<^esup> (SKIP, s3)" using WhileTrue  \<open>y = Suc y'\<close> by blast
  ultimately have "(?w, s1) \<rightarrow>\<^bsup> 1 + x' + 1 + y'\<^esup> (SKIP, s3)" by (meson rel_pow_sum) 
  moreover have "t' = Suc (Suc (x' + y')) " using WhileTrue suc_def by auto 
  ultimately show ?case by simp
qed

lemma big_to_small: "(c, s) \<Rightarrow>\<^bsup> Suc t \<^esup> s' \<Longrightarrow> (c, s) \<rightarrow>\<^bsup> t \<^esup> (SKIP, s')"
  using big_to_small_helper by blast

text "from small to big semantics"
lemma small1_big_continue:
  "cs \<rightarrow> cs' \<Longrightarrow> cs' \<Rightarrow>\<^bsup> t \<^esup> cs'' \<Longrightarrow> cs \<Rightarrow>\<^bsup> Suc t \<^esup> cs''"
  apply (induction arbitrary: cs'' t rule:small_step.induct )
  apply auto
  apply fastforce
  done


lemma small_to_big :
 "cs \<rightarrow>\<^bsup> t \<^esup> (SKIP,s') \<Longrightarrow> cs \<Rightarrow>\<^bsup> Suc t \<^esup> s' "
  apply(induction t arbitrary:cs s')
   apply auto[1]
  using small1_big_continue by blast

text "Equivalence statement. We have a difference of 1 between big step and small step semantics
because in small step semantics, we count the number of times transformation rules have to be applied
until a configuration (SKIP, s') is reached, while in big step semantics the time for each step including
the last command is fully considered."
lemma equiv_small_big_pair:
 "(c,s) \<rightarrow>\<^bsup> t \<^esup> (SKIP,s') \<longleftrightarrow> (c,s) \<Rightarrow>\<^bsup> Suc t \<^esup> s' "
  using big_to_small small_to_big  by auto 

lemma equiv_small_big:
 "cs \<rightarrow>\<^bsup> t \<^esup> (SKIP,s') = cs \<Rightarrow>\<^bsup> Suc t \<^esup> s' "
  using equiv_small_big_pair
  by (metis old.prod.exhaust) 


lemma small_step_cant_run_longer_than_big_step: "(c, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<Longrightarrow> (c, s) \<rightarrow>\<^bsup> t' \<^esup> (c'', s'')
  \<Longrightarrow> t' \<le> t"
proof(rule ccontr)
  assume "(c, s) \<Rightarrow>\<^bsup> t \<^esup> s'" "(c, s) \<rightarrow>\<^bsup>t'\<^esup> (c'', s'')" "\<not> t' \<le> t"
  obtain t'' where "t = Suc t''" 
    using \<open>(c, s) \<Rightarrow>\<^bsup> t \<^esup> s'\<close> bigstep_progress gr0_implies_Suc 
    by force
  hence "(c, s) \<rightarrow>\<^bsup> t'' \<^esup> (SKIP, s')"
    using equiv_small_big_pair \<open>(c, s) \<Rightarrow>\<^bsup> t \<^esup> s'\<close> 
    by auto
  have "t'' < t'" 
    using \<open>t = Suc t''\<close> \<open>\<not> t' \<le> t\<close> 
    by simp
  thus False
    using small_step_cant_continue_after_reaching_SKIP \<open>(c, s) \<rightarrow>\<^bsup> t'' \<^esup> (SKIP, s')\<close>
        \<open>(c, s) \<rightarrow>\<^bsup>t'\<^esup> (c'', s'')\<close>
    by fastforce
qed

end