(*<*)
theory Paper
  imports Syntax
begin
(*>*)

text \<open>
  This is the alignment theory for the paper:

  \<open>Proof-Producing Translation of Functional Programs into a Time & Space Reasonable Model\<close>

  Open this file in Isabelle/jEdit, as described in the supplied @{file "../README.md"}.
  Formal elements referenced in the texts are all clickable, leading to the original definition.
  To get the statements as close to the informal text as possible, local notation is introduced,
  and implicit assumptions are stated via local context where necessary.

  Text between (*<*)\<dots>(*>*) is needed by the system (e.g., small proofs relating the new statement 
  to the original theorem(s)), but can otherwise be ignored.
\<close>


section \<open>Preliminaries\<close>

text \<open>Registers are of @{typ vname}, values of @{typ val}, state of @{typ state}.\<close>

text \<open>Atom evaluation function @{const atomVal} with the following equations:\<close>
(*<*)context includes aops_syntax and atom_syntax begin(*>*)

lemma "\<lbrakk>C n\<rbrakk>\<^sub>s \<equiv> n" (*<*)by simp(*>*)
lemma "\<lbrakk>R r\<rbrakk>\<^sub>s \<equiv> s r" (*<*)by simp(*>*)

text \<open>Expression evaluation function @{const aval} with the following equations:\<close>

lemma "\<lbrakk>A\<^sub>1 + A\<^sub>2\<rbrakk>\<^sub>s = \<lbrakk>A\<^sub>1\<rbrakk>\<^sub>s + \<lbrakk>A\<^sub>2\<rbrakk>\<^sub>s" (*<*)by simp(*>*)
lemma "\<lbrakk>A\<^sub>1 - A\<^sub>2\<rbrakk>\<^sub>s = \<lbrakk>A\<^sub>1\<rbrakk>\<^sub>s - \<lbrakk>A\<^sub>2\<rbrakk>\<^sub>s" (*<*)by simp(*>*)

(*<*)end(*>*)

subsection \<open>Execution Relation (Big-Step Semantics)\<close>
text \<open>
  Commands also contain a no-op command (@{const SKIP}) for technical reasons, which we skip in the
  paper as it is irrelevant. Here are the shared rules (from @{const big_step_t}):
\<close>
(*<*)context includes orig_syntax and Com.com_syntax begin(*>*)

lemma Assign:
  assumes "s' = s(r := \<lbrakk>a\<rbrakk>\<^sub>s)"
  shows "(r ::= a, s) \<Rightarrow>\<^bsup>2\<^esup> s'"
(*<*)using assms by (auto simp: numeral_eq_Suc)(*>*)

lemma IfT:
  assumes "s r \<noteq> 0" "(p\<^sub>1,s) \<Rightarrow>\<^bsup>n\<^esup> s'"
  shows "(IF r\<noteq>0 THEN p\<^sub>1 ELSE p\<^sub>2,s) \<Rightarrow>\<^bsup>n+1\<^esup> s'"
(*<*)using assms by blast(*>*)

lemma IfF:
  assumes "s r = 0" "(p\<^sub>2,s) \<Rightarrow>\<^bsup>n\<^esup> s'"
  shows "(IF r\<noteq>0 THEN p\<^sub>1 ELSE p\<^sub>2,s) \<Rightarrow>\<^bsup>n+1\<^esup> s'"
(*<*)using assms by blast(*>*)

lemma Seq:
  assumes "(p\<^sub>1,s) \<Rightarrow>\<^bsup>n\<^sub>1\<^esup> s'" "(p\<^sub>2,s') \<Rightarrow>\<^bsup>n\<^sub>2\<^esup> s''"
    shows "(p\<^sub>1;;p\<^sub>2,s) \<Rightarrow>\<^bsup>n\<^sub>1+n\<^sub>2+0\<^esup> s''"
(*<*)using assms by auto(*>*)

(*<*)end(*>*)

subsection "Theorem 1"

text \<open>
  \<open>a\<^bsub>max\<^esub>\<close> via @{class max_const} typeclass. The theorem @{thm IMP_space_growth} also needs the
  implicit assumption that the state has a finite codomain.
\<close>

context (*<*)includes orig_syntax(*>*) 
  fixes s :: state assumes "finite (range s)"
begin

theorem
  assumes "max {p\<^bsub>max\<^esub>, s\<^bsub>max \<^esub>} < 2^w"
      and "(p,s) \<Rightarrow>\<^bsup>n\<^esup> s'"
    shows "s'\<^bsub>max \<^esub> < 2^(w+n)"
(*<*)
proof -
  from assms(2) obtain n' where "big_step_t (p,s) n' s'" "n' \<le> n" by blast
  with IMP_space_growth have "Max (range s') < 2^(w+n')" using assms \<open>finite (range s)\<close> by auto
  with \<open>n' \<le> n\<close> show ?thesis using order_less_le_trans by fastforce
qed
(*>*)

end


section \<open>\<open>HOL\<^bsup>(TC)\<^esup>\<close> to \<open>HOL\<^bsup>(TC)\<nat>\<^esup>\<close>\<close>

text \<open>
  Definition 1: @{const rel_fun} (function relator)
  Definition 2: @{class compile_nat} typeclass,
  Definition 3: Pairing function @{const pair_nat} with inverses @{const fst_nat} 
  and @{const snd_nat} and natural number datatype selector @{const nat_selector}.
\<close>

subsection "Theorem 3"

text \<open>Proof of partial Galois equivalence:\<close>
lemma
  defines "L_rel \<equiv> (=\<^bsub>in_dom (Rel_nat :: nat \<Rightarrow> ('a::compile_nat) \<Rightarrow> bool)\<^esub>)"
      and "R_rel \<equiv> (=\<^bsub>in_codom (Rel_nat :: nat \<Rightarrow> 'a \<Rightarrow> bool)\<^esub>)"
    shows "galois.galois_equivalence L_rel R_rel denatify natify"
(*<*)
proof -
  have eqs: "L_rel = (=\<^bsub>range (natify :: 'a :: compile_nat  \<Rightarrow> _)\<^esub>)" "R_rel = ((=) :: 'a \<Rightarrow> _)"
    unfolding L_rel_def R_rel_def using Rel_nat_def imageE by blast+
  show ?thesis unfolding eqs by (fact compile_nat_type_def.galois_equivalence)
qed
(*>*)

subsection \<open>Example 3 (Appendix)\<close>

text \<open>The type of lists is already compiled (see @{const Cons_nat}).
For illustration purposes, we compile a copy of the type:\<close>

datatype 'a listcopy = Nil_copy | Cons_copy 'a "'a listcopy"
datatype_compile_nat listcopy
print_theorems \<comment> \<open>move your cursor on the command to the left to see all generated theorems and constants\<close>

subsection \<open>Fig. 4\<close>

context HOL_To_HOL_Nat
begin

text \<open>The synthesis is fully automatic. We list the corresponding theorems from the figure below.
Here is the input function:\<close>

fun count_acc2 :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat" where
  "count_acc2 a [] n = n"
| "count_acc2 a (x#xs) n = count_acc2 a xs (if x = a then Suc n else n)"
(*<*) declare count_acc2.simps[simp del] (*>*)

text \<open>First, get a single equation (Listing 1.1):\<close>

case_of_simps count_acc2_eq : count_acc2.simps

text \<open>Now we use black-box and white-box transport to obtain the related constant and its
defining, tail-recursive equation:\<close>

function_compile_nat count_acc2_eq
print_theorems \<comment> \<open>move your cursor on the command to the left to see all generated theorems and constants\<close>

text \<open>Related constant from black-box transport (Listing 1.2):\<close>

lemma "(Rel_nat ===> Rel_nat ===> Rel_nat ===> Rel_nat) (count_acc2_nat TYPE('a :: compile_nat))
  (count_acc2 :: 'a \<Rightarrow> _)"
(*<*) by (fact count_acc2_related_transfer) (*>*)

text \<open>Theorem from white-box transport (Listing 1.3):\<close>

lemma
  assumes "Rel_nat a (a' :: 'a :: compile_nat)"
  and "Rel_nat xs (xs' :: 'a list)"
  and "Rel_nat n (n' :: nat)"
  shows "Rel_nat
    (case_list_nat n
      (\<lambda>x xs. count_acc2_nat TYPE('a) a xs (if x = a then Suc n else n))
      xs)
    (count_acc2 a' xs' n')"
(*<*) using assms Rel_nat_count_acc2_nat_unfolded[unfolded If_nat_def eq_nat_eq_False_nat_iff]
  by fastforce (*>*)

text \<open>Final tail-recursive equation (Listing 1.4), using that @{const Rel_nat} is left-unique,
as shown in @{thm left_unique_Rel_nat}:\<close>

lemma
  assumes "Rel_nat a (a' :: 'a :: compile_nat)"
  and "Rel_nat xs (xs' :: 'a list)"
  and "Rel_nat n (n' :: nat)"
  shows "count_acc2_nat TYPE('a) a xs n =
    case_list_nat n (\<lambda>x xs. count_acc2_nat TYPE('a) a xs (if x = a then Suc n else n)) xs"
(*<*) using assms count_acc2_nat_eq_unfolded[unfolded If_nat_def eq_nat_eq_False_nat_iff]
  by fastforce (*>*)

end


section \<open>\<open>HOL\<^bsup>TC\<nat>\<^esup>\<close> to \<open>IMP\<^bsup>TC\<^esup>\<close>\<close>

subsection \<open>Fig. 5\<close>
text \<open>Commands as @{typ tcom}, semantics via @{const tbig_step_t}. Special rules:\<close>
(*<*)context includes tcom_syntax and orig_syntax and partial_syntax begin(*>*)

lemma Call:
  assumes "(pc,s) \<Rightarrow>\<^sub>r\<^bsup>n\<^esup> v" "s' = s(r := v)"
  shows "p \<turnstile> (CALL pc RETURN r,s) \<Rightarrow>\<^bsup>n+0\<^esup> s'"
  (*<*)using assms by auto(*>*)

lemma Rec:
  assumes "p \<turnstile> (p,s) \<Rightarrow>\<^bsup>n\<^esup> s'"
  shows "p \<turnstile> (RECURSE,s) \<Rightarrow>\<^bsup>n+5\<^esup> s'"
  (*<*)using assms by (metis add.commute tTail)(*>*)

(*<*)end(*>*)

subsection \<open>Example 1\<close>

text \<open>See @{thm HOL_To_HOL_Nat.fun_pow_snd_nat_eq}.\<close>

subsection \<open>Compilation to \<open>IMP\<^bsup>TC\<^esup>\<close>\<close>

text \<open>See @{ML_structure Compile_HOL_Nat_To_IMP}.\<close>

subsection \<open>Execution Rules used for Symbolic Execution of \<open>IMP\<^bsup>TC\<^esup>\<close> Programs (Fig. 14, Appendix)\<close>

(*<*)context includes tcom_syntax and terminates_with_syntax begin(*>*)

theorem Assign1:
  assumes "(s(r := \<lbrakk>a\<rbrakk>\<^sub>s)) r' = v"
  shows "p \<turnstile> (r ::= a, s) \<Rightarrow>\<^bsub>r'\<^esub> v"
  using assms terminates_with_res_tAssignI by auto

lemma Seq1:
  assumes "p \<turnstile> (p1, s) \<Rightarrow> s'"
  and "p \<turnstile> (p2, s') \<Rightarrow>\<^bsub>r\<^esub> val"
  shows "p \<turnstile> (p1;; p2, s) \<Rightarrow>\<^bsub>r\<^esub> val"
  using assms by (rule terminates_with_res_tSeqI)

lemma IfT1:
  assumes "s r \<noteq> 0"
  and "p \<turnstile> (p1, s) \<Rightarrow>\<^bsub>r\<^esub> v"
  shows "p \<turnstile> (IF r\<noteq>0 THEN p1 ELSE p2, s) \<Rightarrow>\<^bsub>r\<^esub> v"
  using assms terminates_with_res_tIfI by auto

lemma IfF1:
  assumes "s r = 0"
  and "p \<turnstile> (p2, s) \<Rightarrow>\<^bsub>r\<^esub> v"
  shows "p \<turnstile> (IF r\<noteq>0 THEN p1 ELSE p2, s) \<Rightarrow>\<^bsub>r\<^esub> v"
  using assms terminates_with_res_tIfI by auto

lemma Call1:
  assumes "(pc, s) \<Rightarrow>\<^bsub>r\<^esub> v"
  and "(s(r := v)) r' = v'"
  shows "p \<turnstile> (CALL pc RETURN r, s) \<Rightarrow>\<^bsub>r'\<^esub> v'"
  using assms terminates_with_res_tCallI by auto

lemma Rec1:
  assumes "p \<turnstile> (p, s) \<Rightarrow>\<^bsub>r\<^esub> v"
  shows "p \<turnstile> (RECURSE, s) \<Rightarrow>\<^bsub>r\<^esub> v"
  using assms terminates_with_res_tTailI by auto

(*<*)end(*>*)

subsection \<open>Example 2\<close>

context HOL_Nat_To_IMP
begin

text \<open>First, unfold the case combinator to if-then-elses:\<close>

lemmas count_acc2_nat_eq = HTHN.count_acc2_nat_eq_unfolded[unfolded case_list_nat_def]

text \<open>Then, generate the \<open>IMP\<^bsup>TC\<^esup>\<close> program:\<close>

compile_nat (non-optimized) count_acc2_nat_eq \<comment> \<open>remove the non-optimized flag for a shorter program\<close>

text \<open>Then, prove the correctness. This is fully automatic, using the method @{method cook}.
Here, we pr
Here, we provide the corresponding
step-by-step proof from the paper. Here is the input function:
\<close>

HOL_To_IMP_correct HOL_To_HOL_Nat.count_acc2_nat
  text \<open>We prove correctness of the compiled \<open>IMP\<^bsup>W\<^esup>\<close> program. First, we reduce this proof to the
  correctness proof of the generated \<open>IMP\<^bsup>TC\<^esup>\<close> program.\<close>
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  text \<open>Initial goal (Listing 1.5)\<close>
  apply (tactic \<open>HT.setup_induction_tac HT.get_fun_inducts @{context} 1\<close>) defer
  text \<open>Cons-case (Listing 1.6)\<close>
  apply (tactic \<open>HT.start_case_tac HT.get_IMP_def @{context} 1\<close>)
  apply (tactic \<open>HT.run_tac HT.get_imp_correct @{context} 1\<close>)
  apply (tactic \<open>HT.run_HOL_fun_tac HG.get_HOL_eqs @{context} 1\<close>)
  text \<open>Goals after symbolic execution (Listing 1.7)\<close>
  apply (tactic \<open>HT.apply_IH_tac @{context} 1\<close>)
  text \<open>Relatedness goals after application of inductive hypothesis (Listing 1.8)\<close>
  apply (tactic \<open>HT.solve_IH_prem_tac @{context} 1\<close>)
  apply (tactic \<open>HT.solve_IH_prem_tac @{context} 1\<close>)
  apply (tactic \<open>HT.solve_IH_prem_tac @{context} 1\<close>)
  text \<open>Second subcase in Cons-case\<close>
  apply (tactic \<open>HT.finish_tac HG.get_HOL_eqs @{context} 1\<close>)
  text \<open>Nil-case\<close>
  apply (tactic \<open>HT.start_case_tac HT.get_IMP_def @{context} 1\<close>)
  apply (tactic \<open>HT.run_tac HT.get_imp_correct @{context} 1\<close>)
  apply (tactic \<open>HT.finish_tac HG.get_HOL_eqs @{context} 1\<close>)
  text \<open>Done! We do not close the proof because in the next command, we prove it again, automatically:\<close>
  oops

HOL_To_IMP_correct HOL_To_HOL_Nat.count_acc2_nat by cook

end

subsection \<open>Case Studies\<close>

text \<open>Can be found in @{dir "../HOL_To_IMP/Refinements"}.\<close>


section \<open>\<open>IMP\<^bsup>TC\<^esup>\<close> to \<open>IMP\<^sup>-\<close>\<close>

subsection \<open>Fig. 9\<close>
text \<open>Commands as @{typ com'}, semantics via @{const big_step_t'}. Special rules:\<close>
(*<*)context includes orig_syntax and Com.com_syntax begin(*>*)

lemma WhF:
  assumes "s r = 0"
  shows "(WHILE r\<noteq>0 DO p,s) \<Rightarrow>\<^bsup>2\<^esup> s"
  (*<*)using assms by (auto simp: numeral_eq_Suc)(*>*)

lemma WhT:
  assumes "s\<^sub>1 r \<noteq> 0" "(p,s\<^sub>1) \<Rightarrow>\<^bsup>n\<^sub>1\<^esup> s\<^sub>2" "(WHILE r\<noteq>0 DO p,s\<^sub>2) \<Rightarrow>\<^bsup>n\<^sub>2\<^esup> s\<^sub>3"
  shows "(WHILE r\<noteq>0 DO p,s\<^sub>1) \<Rightarrow>\<^bsup>n\<^sub>1+n\<^sub>2+1\<^esup> s\<^sub>3"
  (*<*)using assms by auto(*>*)

(*<*)end(*>*)

subsection \<open>Fig. 10:\<close>
text \<open>Full execution relation in @{const tail_step}. Shown rules:\<close>
(*<*)context includes hol_bin_syntax and tail_syntax and partial_syntax and tcom_syntax begin(*>*)

lemma
  assumes "s r \<noteq> 0" "(p\<^sub>1,s) \<Rightarrow>\<^bsup>n\<^esup> (s',b)"
  shows "(IF r\<noteq>0 THEN p\<^sub>1 ELSE p\<^sub>2,s) \<Rightarrow>\<^bsup>n+1\<^esup> (s',b)"
  (*<*)using assms by auto(*>*)

lemma
  assumes "(p\<^sub>1,s) \<Rightarrow>\<^bsup>n\<^sub>1\<^esup> (s',\<zero>)" "(p\<^sub>2,s') \<Rightarrow>\<^bsup>n\<^sub>2\<^esup> (s',b)"
    shows "(p\<^sub>1;;p\<^sub>2,s) \<Rightarrow>\<^bsup>n\<^sub>1+n\<^sub>2+0\<^esup> (s',b)"
  (*<*)using assms by auto(*>*)

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

(*<*)end(*>*)

subsection "Lemma 1"
text \<open>
  Proven in @{thm small_sound} and @{thm small_complete}, with the additional assumptions that
  the programs are actually tail-recursive (the type does not enforce this)
\<close>
context (*<*)includes orig_syntax and tail_syntax and hol_bin_syntax(*>*)
  fixes tp p assumes "invar tp" "invar p"
begin

lemma
  assumes "(p,s) \<Rightarrow>\<^bsup>n\<^esup> (s,\<zero>)"
    shows "tp \<turnstile> (p,s) \<Rightarrow>\<^bsup>n\<^esup> s"
(*<*)using assms small_complete[OF _ \<open>invar p\<close> \<open>invar tp\<close>] by blast(*>*)

lemma
  assumes "(p,s\<^sub>1) \<Rightarrow>\<^bsup>n\<^sub>1\<^esup> (s\<^sub>2,\<one>)" "tp \<turnstile> (tp,s\<^sub>2) \<Rightarrow>\<^bsup>n\<^sub>2\<^esup> s\<^sub>3"
    shows "tp \<turnstile> (p,s\<^sub>1) \<Rightarrow>\<^bsup>n\<^sub>1+n\<^sub>2\<^esup> s\<^sub>3"
  (*<*)
  using assms small_complete[OF _ \<open>invar p\<close> \<open>invar tp\<close>]  \<open>invar tp\<close> small_sound[OF _ \<open>invar tp\<close>]
    tTrue by auto
  (*>*)

end

subsection "Theorem 6"
text \<open>
  Definition in @{const compile}, correctness theorems @{thm compile_sound}
  and @{thm compile_complete_add}.
\<close>
context (*<*)includes partial_syntax(*>*)
  fixes p assumes "invar p"
begin

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

(*<*)context includes orig_syntax begin(*>*)

lemma
  assumes "inj m"
    shows "(p[(m x)/x],s)\<Rightarrow>\<^bsup>n\<^esup> s' \<Longrightarrow> (p,s o m)\<Rightarrow>\<^bsup>n\<^esup> s' o m"
  (*<*)using assms neat_subst by auto(*>*)

(*<*)end(*>*)

subsection "Theorem 7"
text \<open>
  Definition 5 in @{const inline}, correctness theorems @{thm inline_sound}
  and @{thm inline_complete}
\<close>
(*<*)context includes orig_syntax and partial_syntax begin(*>*)

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

theorem "(\<lparr>p\<rparr>\<^sub>\<star>,s) \<Rightarrow>\<^bsub>regs p\<^esub>\<^bsup>n\<^esup> s' \<Longrightarrow> (p,s)\<Rightarrow>\<^bsub>regs p\<^esub>\<^bsup>n\<^esup> s'"
(*<*)using inline_complete by (smt (verit, del_insts) eq_on_def le_trans)(*>*)

(*<*)end(*>*)

subsection "Fig. 11"
text \<open>Rules in @{const big_step}.\<close>
(*<*)context includes minus_syntax and com_syntax begin(*>*)

lemma
  assumes "b \<in> {\<zero>,\<one>}" "s' = s(r := Some b)"
  shows "(r ::= b, s) \<Rightarrow>\<^bsup>1\<^esup> s'"
  (*<*)using assms by blast(*>*)

lemma
  assumes "(p\<^sub>1,s) \<Rightarrow>\<^bsup>n\<^sub>1\<^esup> s'" "(p\<^sub>2,s') \<Rightarrow>\<^bsup>n\<^sub>2\<^esup> s''"
  shows "(p\<^sub>1;;p\<^sub>2,s) \<Rightarrow>\<^bsup>n\<^sub>1+n\<^sub>2+1\<^esup> s''"
  (*<*)using assms by blast(*>*)

lemma
  assumes "s r \<noteq> Some \<zero>" "(p\<^sub>1,s) \<Rightarrow>\<^bsup>n\<^esup> s'"
  shows "(IF r\<noteq>0 THEN p\<^sub>1 ELSE p\<^sub>2,s) \<Rightarrow>\<^bsup>n+1\<^esup> s'"
 (*<*)using assms by blast(*>*)

lemma
  assumes "s r = Some \<zero>" "(p\<^sub>2,s) \<Rightarrow>\<^bsup>n\<^esup> s'"
  shows "(IF r\<noteq>0 THEN p\<^sub>1 ELSE p\<^sub>2,s) \<Rightarrow>\<^bsup>n+1\<^esup> s'"
 (*<*)using assms by blast(*>*)

lemma
  assumes "s r = Some \<zero>"
  shows "(WHILE r\<noteq>0 DO p,s) \<Rightarrow>\<^bsup>1\<^esup> s"
  (*<*)using assms by blast(*>*)

lemma
  assumes "s\<^sub>1 r \<noteq> Some \<zero>" "(p,s\<^sub>1) \<Rightarrow>\<^bsup>n\<^sub>1\<^esup> s\<^sub>2" "(WHILE r\<noteq>0 DO p,s\<^sub>2) \<Rightarrow>\<^bsup>n\<^sub>2\<^esup> s\<^sub>3"
  shows "(WHILE r\<noteq>0 DO p,s\<^sub>1) \<Rightarrow>\<^bsup>n\<^sub>1+n\<^sub>2+2\<^esup> s\<^sub>3"
  (*<*)using assms by blast(*>*)

(*<*)end(*>*)

subsection "Lemma 3"
text \<open>Adder in @{const binary_adder}, lemma in @{thm assignment_to_binary_correct}\<close>

context (*<*)includes minus2_syntax(*>*)
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

context (*<*)includes imp_syntax and minus2_syntax(*>*)
  fixes s::state assumes "finite (range s)"
begin

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

(*<*)end(*>*)