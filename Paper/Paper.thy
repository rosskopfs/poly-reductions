(*<*)
theory Paper
  imports Syntax
begin
(*>*)

text \<open>
  This is the alignment theory for the paper: 
  
  "Proof-Producing Translation of Functional Programs into a Time & Space Reasonable Model"
  
  Open this file in Isabelle/jEdit, as described in the supplied README.
  Formal elements referenced in the texts are all clickable to see the original definition.
  To get the statements as close to the informal text as possible, local notation is introduced,
  and implicit assumptions are stated via local context where necessary.
\<close>

section \<open>Preliminaries\<close>
                                
text \<open>Registers are of @{typ vname}, values of @{typ val}, state of @{typ state}.\<close>

text \<open>Atom evaluation function @{const atomVal} with the following equations:\<close>

lemma "\<lbrakk>C n\<rbrakk>\<^sub>s \<equiv> n" by simp
lemma "\<lbrakk>R r\<rbrakk>\<^sub>s \<equiv> s r" by simp

text \<open>Expression evaluation function @{const aval} with the following equations:\<close>

lemma "\<lbrakk>A\<^sub>1 + A\<^sub>2\<rbrakk>\<^sub>s = \<lbrakk>A\<^sub>1\<rbrakk>\<^sub>s + \<lbrakk>A\<^sub>2\<rbrakk>\<^sub>s" by simp
lemma "\<lbrakk>A\<^sub>1 - A\<^sub>2\<rbrakk>\<^sub>s = \<lbrakk>A\<^sub>1\<rbrakk>\<^sub>s - \<lbrakk>A\<^sub>2\<rbrakk>\<^sub>s" by simp

subsection \<open>Big-step semantics\<close>
text \<open>
  Commands also contain a no-op command ("SKIP") for technical reasons, which we skip in the paper
  as it is irrelevant. Shared rules (here from @{const big_step_t}):
\<close>
(*<*)unbundle no atom (*>*)

lemma Assign: 
  assumes "s' = s(r := \<lbrakk>a\<rbrakk>\<^sub>s)"
  shows "(r ::= a, s) \<Rightarrow>\<^bsup>2\<^esup> s'"
(*<*)using assms by (auto simp: numeral_eq_Suc)(*>*)

lemma IfT:
  assumes "s r \<noteq> 0" "(p\<^sub>1,s) \<Rightarrow>\<^bsup>n\<^esup> s'"
  shows "(IF r\<noteq>0 THEN p\<^sub>1 ELSE p\<^sub>2,s) \<Rightarrow>\<^bsup>n+1\<^esup> s'"
(*<*)using assms by fastforce(*>*)

lemma IfF:
  assumes "s r = 0" "(p\<^sub>2,s) \<Rightarrow>\<^bsup>n\<^esup> s'"
  shows "(IF r\<noteq>0 THEN p\<^sub>1 ELSE p\<^sub>2,s) \<Rightarrow>\<^bsup>n+1\<^esup> s'"
(*<*)using assms by fastforce(*>*)

lemma Seq:
  assumes "(p\<^sub>1,s) \<Rightarrow>\<^bsup>n\<^sub>1\<^esup> s'" "(p\<^sub>2,s') \<Rightarrow>\<^bsup>n\<^sub>2\<^esup> s''"
    shows "(p\<^sub>1;;p\<^sub>2,s) \<Rightarrow>\<^bsup>n\<^sub>1+n\<^sub>2+0\<^esup> s''" 
  (*<*)using assms by (auto intro: add_le_mono)(*>*)

subsection "Theorem 1"

text \<open>
\<open>a\<^bsub>max\<^esub>\<close> via @{const max_const} typeclass. The theorem @{thm IMP_space_growth} also needs the
implicit assumption that the state has a finite codomain.\<close>

context fixes s :: state assumes "finite (range s)" begin

theorem
  assumes "max {p\<^bsub>max\<^esub>, s\<^bsub>max \<^esub>} < 2^w"
      and "(p,s) \<Rightarrow>\<^bsup>n\<^esup> s'"
    shows "Max (range s') < 2^(w+n)"
(*<*)
proof -
  from assms(2) obtain n' where "big_step_t (p,s) n' s'" "n' \<le> n" by blast
  with IMP_space_growth have "Max (range s') < 2^(w+n')" using assms \<open>finite (range s)\<close> by auto
  with \<open>n' \<le> n\<close> show ?thesis using order_less_le_trans by fastforce
qed
(*>*)

end


section \<open>\<open>HOL\<^bsup>TC\<nat>\<close> to \<open>IMP\<^bsup>TC\<^esup>\<close>\<close>

subsection \<open>Fig. 5\<close>
text \<open>Commands as @{typ tcom}, semantics via @{const tbig_step_t}. Special rules:\<close>
(*<*)unbundle tcom_syntax(*>*)

lemma Call: 
  assumes "(pc,s) \<Rightarrow>\<^sub>r\<^bsup>n\<^esup> v" "s' = s(r := v)"
    shows "p \<turnstile> (CALL pc RETURN r,s) \<Rightarrow>\<^bsup>n+0\<^esup> s'"
  (*<*)using assms by (auto intro: le_trans)(*>*)

lemma Rec:
  assumes "p \<turnstile> (p,s) \<Rightarrow>\<^bsup>n\<^esup> s'"
    shows "p \<turnstile> (RECURSE,s) \<Rightarrow>\<^bsup>n+5\<^esup> s'"
  (*<*)using assms by (metis add.commute tTail add_le_mono1)(*>*)


section \<open>\<open>IMP\<^bsup>TC\<^esup>\<close> to \<open>IMP\<^sup>-\<close>\<close>

subsection \<open>Fig. 9\<close>
text \<open>Commands as @{typ com'}, semantics via @{const big_step_t'}. Special rules:\<close>
(*<*)unbundle no tcom_syntax unbundle com'_syntax(*>*)

lemma WhileF:
  assumes "s r = 0"
  shows "(WHILE r\<noteq>0 DO p,s) \<Rightarrow>\<^bsup>2\<^esup> s"
  (*<*)using assms by (auto simp: numeral_eq_Suc)(*>*)

lemma WhileT:
  assumes "s\<^sub>1 r \<noteq> 0" "(p,s\<^sub>1) \<Rightarrow>\<^bsup>n\<^sub>1\<^esup> s\<^sub>2" "(WHILE r\<noteq>0 DO p,s\<^sub>2) \<Rightarrow>\<^bsup>n\<^sub>2\<^esup> s\<^sub>3"
  shows "(WHILE r\<noteq>0 DO p,s\<^sub>1) \<Rightarrow>\<^bsup>n\<^sub>1+n\<^sub>2+1\<^esup> s\<^sub>3"
  (*<*)
  using assms by auto 
    (metis (mono_tags, lifting) WhileI add_Suc add_le_mono assms(1) not_less_eq_eq plus_1_eq_Suc)
  (*>*)

subsection \<open>Fig. 10:\<close>
text \<open>Full execution relation in @{const tail_step}. Shown rules:\<close>
(*<*)unbundle no com'_syntax unbundle tcom_syntax unbundle tail (*>*)

lemma
  assumes "s r \<noteq> 0" "(p\<^sub>1,s) \<Rightarrow>\<^bsup>n\<^esup> (s',b)"
  shows "(IF r\<noteq>0 THEN p\<^sub>1 ELSE p\<^sub>2,s) \<Rightarrow>\<^bsup>n+1\<^esup> (s',b)"
  (*<*)using assms by (auto intro: Suc_eq_plus1)(*>*)

lemma
  assumes "(p\<^sub>1,s) \<Rightarrow>\<^bsup>n\<^sub>1\<^esup> (s',\<zero>)" "(p\<^sub>2,s') \<Rightarrow>\<^bsup>n\<^sub>2\<^esup> (s',b)"
    shows "(p\<^sub>1;;p\<^sub>2,s) \<Rightarrow>\<^bsup>n\<^sub>1+n\<^sub>2+0\<^esup> (s',b)"
  (*<*)using assms by (auto intro: le_trans add_mono)(*>*)

lemma
  assumes "s' = s(r:= \<lbrakk>a\<rbrakk>\<^sub>s)"
  shows "(r ::= a,s) \<Rightarrow>\<^bsup>2\<^esup> (s',\<zero>)"
  (*<*)using assms by (auto simp: numeral_eq_Suc)(*>*)

lemma "(RECURSE,s) \<Rightarrow>\<^bsup>5\<^esup> (s,\<one>)"
  (*<*)by auto(*>*)

text \<open>Rules not shown:\<close>

lemma
  assumes "s r = 0" "(p\<^sub>2,s) \<Rightarrow>\<^bsup>n\<^esup> (s',b)"
  shows "(IF r\<noteq>0 THEN p\<^sub>1 ELSE p\<^sub>2,s) \<Rightarrow>\<^bsup>n+1\<^esup> (s',b)"
  (*<*)using assms by (auto intro: Suc_eq_plus1)(*>*)

lemma
  assumes "(pc,s) \<Rightarrow>\<^sub>r\<^bsup>n\<^esup> v" "s' = s(r := v)"
    shows "(CALL pc RETURN r,s) \<Rightarrow>\<^bsup>n+0\<^esup> (s',\<zero>)"
  (*<*)using assms by (auto intro: le_trans)(*>*)

subsection "Lemma 1"
text \<open>
  Proven in @{thm small_sound} and @{thm small_complete}, with the additional assumptions that
  the programs are actually tail-recursive (the type does not enforce this)
\<close>
context fixes tp p assumes "invar tp" "invar p" begin

lemma
  assumes "(p,s) \<Rightarrow>\<^bsup>n\<^esup> (s,\<zero>)"
    shows "tp \<turnstile> (p,s) \<Rightarrow>\<^bsup>n\<^esup> s"
(*<*)using assms small_complete[OF _ \<open>invar p\<close> \<open>invar tp\<close>] by blast(*>*)

lemma
  assumes "(p,s\<^sub>1) \<Rightarrow>\<^bsup>n\<^sub>1\<^esup> (s\<^sub>2,\<one>)" "tp \<turnstile> (tp,s\<^sub>2) \<Rightarrow>\<^bsup>n\<^sub>2\<^esup> s\<^sub>3"
    shows "tp \<turnstile> (p,s\<^sub>1) \<Rightarrow>\<^bsup>n\<^sub>1+n\<^sub>2\<^esup> s\<^sub>3"
  (*<*)
  using assms small_complete[OF _ \<open>invar p\<close> \<open>invar tp\<close>]  \<open>invar tp\<close> small_sound[OF _ \<open>invar tp\<close>] 
    add_mono tTrue by (auto intro: add_mono)
  (*>*)

end

subsection "Theorem 6"
text \<open>
  Definition in @{const compile}, correctness theorems @{thm compile_sound}
  and @{thm compile_complete_add}.
\<close>
(*<*)unbundle no total unbundle partial(*>*)

context fixes p assumes "invar p" begin

theorem "p \<turnstile> (p,s) \<Rightarrow>\<^bsub>regs p\<^esub>\<^bsup>n\<^esup> s' \<longleftrightarrow> (\<lparr>p\<rparr>\<^sub>\<circle>,s) \<Rightarrow>\<^bsub>regs p\<^esub>\<^bsup>n+7\<^esup> s'"
(*<*)
  apply standard
  subgoal
    using compile_sound[OF _ \<open>invar p\<close>]  unfolding eq_on_def 
    apply (auto intro: le_trans add_le_cancel_right)
    apply (smt (verit) add_le_cancel_right le_trans add.commute)
    done
  subgoal
    using compile_complete[OF _ \<open>invar p\<close>] unfolding eq_on_def
    apply (auto intro: le_trans add_le_cancel_right)
    by (smt (verit, best) le_diff_conv order_refl)
  done
(*>*)

end


subsection "Lemma 2"
text \<open>Lemma in @{thm neat_subst}.\<close>

lemma 
  assumes "inj m"
    shows "(p[(m x)/x],s)\<Rightarrow>\<^bsup>n\<^esup> s' \<Longrightarrow> (p,s o m)\<Rightarrow>\<^bsup>n\<^esup> s' o m"
  (*<*)using assms neat_subst by auto(*>*)


subsection "Theorem 7"
text \<open>
  Definition in @{const inline}, correctness theorems @{thm inline_sound} 
  and @{thm inline_complete}
\<close>
(*<*)unbundle partial2(*>*)

theorem "(p,s)\<Rightarrow>\<^bsub>regs p\<^esub>\<^bsup>n\<^esup> s' \<Longrightarrow> (\<lparr>p\<rparr>\<^sub>\<star>,s) \<Rightarrow>\<^bsub>regs p\<^esub>\<^bsup>(n+1)*(\<bar>p\<bar>+1)\<^esup> s'"
(*<*)
proof -
  assume "(p,s)\<Rightarrow>\<^bsub>regs p\<^esub>\<^bsup>n\<^esup> s'"
  then obtain n' s'' where "n' \<le> n" and s'': "big_step_t' (p,s) n' s''" "s'' = s' on set (regs p)" by blast
  from inline_sound[OF this(2)] obtain z t where 
    t: "big_step_t (\<lparr>p\<rparr>\<^sub>\<star>, s) z t" "t = s'' on set (regs p)" and 
    z: "n' \<le> z" "z \<le> (n'+1)*(1+\<bar>p\<bar>)"
    by blast
  from z \<open>n' \<le> n\<close> have "z \<le> (n+1)*(\<bar>p\<bar>+1)"
    by (metis Orderings.preorder_class.dual_order.trans
        Suc_eq_plus1 Suc_le_mono add_0 add_Suc
        mult_le_mono1)
  with s'' t show "(\<lparr>p\<rparr>\<^sub>\<star>,s) \<Rightarrow>\<^bsub>regs p\<^esub>\<^bsup>(n+1)*(\<bar>p\<bar>+1)\<^esup> s'" using t by blast
qed
(*>*)

text \<open>
  TODO: LTR directions does not get cheaper. 
  Change Semantics so call costs 2*(length (vars c))+5? Or change the text?
\<close>
theorem "(\<lparr>p\<rparr>\<^sub>\<star>,s) \<Rightarrow>\<^bsub>regs p\<^esub>\<^bsup>n\<^esup> s' \<Longrightarrow> (p,s)\<Rightarrow>\<^bsub>regs p\<^esub>\<^bsup>n\<^esup> s'"
(*<*)using inline_complete by (smt (verit, del_insts) eq_on_def le_trans)(*>*)


subsection "Fig. 11"
text \<open>Rules in @{const big_step}.\<close>
(*<*)unbundle no imp unbundle no tail unbundle minus unbundle no holb unbundle bitsb(*>*)

lemma
  assumes "b \<in> {\<zero>,\<one>}" "s' = s(r := Some b)"
  shows "(r ::= b, s) \<Rightarrow>\<^bsup>1\<^esup> s'"
 (*<*)using assms by blast(*>*)

lemma
  assumes "(p\<^sub>1,s) \<Rightarrow>\<^bsup>n\<^sub>1\<^esup> s'" "(p\<^sub>2,s') \<Rightarrow>\<^bsup>n\<^sub>2\<^esup> s''"
  shows "(p\<^sub>1;;p\<^sub>2,s) \<Rightarrow>\<^bsup>n\<^sub>1+n\<^sub>2+1\<^esup> s''"
(*<*)
  using assms by (metis big_step.Seq Suc_eq_plus1 Suc_le_mono add_mono_thms_linordered_semiring(1))
(*>*)

lemma
  assumes "s r \<noteq> Some \<zero>" "(p\<^sub>1,s) \<Rightarrow>\<^bsup>n\<^esup> s'"
  shows "(IF r\<noteq>0 THEN p\<^sub>1 ELSE p\<^sub>2,s) \<Rightarrow>\<^bsup>n+1\<^esup> s'"
 (*<*)using assms by (metis IfTrue Suc_eq_plus1 add_le_mono nle_le)(*>*)

lemma
  assumes "s r = Some \<zero>" "(p\<^sub>2,s) \<Rightarrow>\<^bsup>n\<^esup> s'"
  shows "(IF r\<noteq>0 THEN p\<^sub>1 ELSE p\<^sub>2,s) \<Rightarrow>\<^bsup>n+1\<^esup> s'"
 (*<*)using assms by (metis IfFalse Suc_eq_plus1 add_le_mono nle_le)(*>*)

lemma
  assumes "s r = Some \<zero>"
  shows "(WHILE r\<noteq>0 DO p,s) \<Rightarrow>\<^bsup>1\<^esup> s"
  using assms by blast

lemma
  assumes "s\<^sub>1 r \<noteq> Some \<zero>" "(p,s\<^sub>1) \<Rightarrow>\<^bsup>n\<^sub>1\<^esup> s\<^sub>2" "(WHILE r\<noteq>0 DO p,s\<^sub>2) \<Rightarrow>\<^bsup>n\<^sub>2\<^esup> s\<^sub>3"
  shows "(WHILE r\<noteq>0 DO p,s\<^sub>1) \<Rightarrow>\<^bsup>n\<^sub>1+n\<^sub>2+2\<^esup> s\<^sub>3"
(*<*)
  using assms using WhileTrue[of s\<^sub>1 r p _ s\<^sub>2 _ s\<^sub>3]
  by (metis Suc_le_mono add_2_eq_Suc' add_le_mono)
(*>*)


subsection "Lemma 3"
text \<open>Lemma in @{thm assignment_to_binary_correct}\<close>
(*<*)unbundle no aops unbundle no imp unbundle no total unbundle no tail unbundle no partial unbundle no partial2 unbundle minus(*>*)

context 
  fixes w::nat assumes "0 < w"
  fixes s::state assumes "finite (range s)"
begin


theorem
  assumes "max {a\<^bsub>max\<^esub>, \<lbrakk>a\<rbrakk>\<^sub>s, s\<^bsub>max \<^esub>} < 2^w"
  shows "(\<lparr>a\<rparr>\<^sup>w\<^bsub>r\<^esub>, \<lparr>s\<rparr>\<^sup>w) \<Rightarrow>\<^bsup>(50*(w+1))\<^esup> \<lparr>s(r := \<lbrakk>a\<rbrakk>\<^sub>s)\<rparr>\<^sup>w"
(*<*)
  using assms \<open>finite (range s)\<close> assignment_to_binary_correct[OF \<open>0<w\<close>,
      unfolded t_small_step_fun_t_small_step_equivalence[unfolded big_eq_small[symmetric]], of a s r]
  by auto
(*>*)

end

subsection "Theorem 8"
text \<open>Theorem in @{thm IMP_To_IMP_Minus}\<close>
(*<*)unbundle imp(*>*)

context fixes s::state assumes "finite (range s)" begin

theorem
  assumes "(p,s) \<Rightarrow>\<^bsup>n\<^esup> s'" "n < w" "max {s\<^bsub>max \<^esub>, p\<^bsub>max\<^esub>} * 2^n < 2^w"
  shows "(\<lparr>p\<rparr>\<^sup>w, \<lparr>s\<rparr>\<^sup>w) \<Rightarrow>\<^bsup>100*n*w+50\<^esup> \<lparr>s'\<rparr>\<^sup>w"
(*<*)
proof -
  from assms(1) obtain n' where *: "big_step_t (p,s) n' s'" "n' \<le> n" by blast
  with assms have **: "n' < w" "2 ^ n' * (omax (s\<^bsub>max \<^esub>) (p\<^bsub>max\<^esub>)) < 2 ^ w" 
    apply auto
    using Orderings.preorder_class.dual_order.strict_trans2
    by fastforce
  have "t_small_step_fun (100*w*n + 50)
     (\<lparr>p\<rparr>\<^sup>w, \<lparr>s\<rparr>\<^sup>w) =
    (SKIP, \<lparr>s'\<rparr>\<^sup>w)" using t_small_step_fun_increase_time[OF _ IMP_To_IMP_Minus[OF *(1) \<open>finite (range s)\<close> **]]
      \<open>n' \<le> n\<close> add_le_mono1 le_diff_conv nat_mult_le_cancel_disj trans_le_add1 by presburger
  thus ?thesis using t_small_step_fun_t_small_step_equivalence[unfolded big_eq_small[symmetric]]
    by (simp add: mult.commute mult.left_commute)
qed
(*>*)

end

end