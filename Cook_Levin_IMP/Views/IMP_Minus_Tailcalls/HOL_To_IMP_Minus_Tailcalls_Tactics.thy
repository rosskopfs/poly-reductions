\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Tailcalls_Tactics
  imports
    States_Cook_Levin_IMP_Minus_Tailcalls
    IMP_Minus.Compile_Nat
begin

unbundle Com.no_com_syntax
unbundle IMP_Tailcalls_Dynamic.tcom_syntax

lemma tSeq_assoc:
  "c \<turnstile> (tSeq (tSeq p1 p2) p3, s) \<Rightarrow>\<^bsup>t \<^esup> s' \<longleftrightarrow> c \<turnstile> (tSeq p1 (tSeq p2 p3), s) \<Rightarrow>\<^bsup>t \<^esup> s'"
  by auto

lemma tAssignD: "c \<turnstile> (x ::= a, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> t = 2 \<and> s' = s(x := aval a s)"
  by auto

ML_file \<open>hol_to_imp_minus_tailcalls_tactics.ML\<close>

ML \<open>
  structure H = HOL_To_IMP_Minus_Tailcalls_Tactics
\<close>

lemma Not_IMP_func_correct:
  includes tcom_syntax
  assumes "(inline (compile (not_IMP)), s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "s' ''not_ret'' = not_nat (s ''not_x'')"
  using assms
  apply -
  apply (erule inline)
  apply (erule compile_complete)
  apply (simp add: not_IMP_def)
  (*apply (simp only: set_vars_compile vars_tcom.simps)*)
  subgoal 
  apply (tactic \<open>H.start_tac @{thm not_IMP_def} @{context} 1\<close>)
  apply (tactic \<open>H.seq_tac @{context} 1\<close>)
  apply (tactic \<open>H.assign_tac @{context} 1\<close>)
  apply (tactic \<open>H.seq_tac @{context} 1\<close>)
  apply (tactic \<open>H.assign_tac @{context} 1\<close>)
  apply (tactic \<open>H.seq_tac @{context} 1\<close>)
  apply (tactic \<open>H.assign_tac @{context} 1\<close>)
  apply (tactic \<open>H.seq_tac @{context} 1\<close>)
  apply (tactic \<open>H.call_tac @{thm eq_IMP_func_correct} @{thm refl} @{context} 1\<close>)
  apply (tactic \<open>H.seq_tac @{context} 1\<close>)
  apply (tactic \<open>H.assign_tac @{context} 1\<close>)
  apply (tactic \<open>H.assign_tac @{context} 1\<close>)
  sorry
  done


end