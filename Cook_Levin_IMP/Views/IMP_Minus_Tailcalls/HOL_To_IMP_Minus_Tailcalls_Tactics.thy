\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Tailcalls_Tactics
  imports
    States_Cook_Levin_IMP_Minus_Tailcalls
    IMP_Minus.Compile_Nat
begin

lemma inline_compile_complete:
  assumes "(inline (compile c), s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  assumes "invar c"
  obtains t' s'' where
    "c \<turnstile> (c, s) \<Rightarrow>\<^bsup>t' - 7\<^esup> s''" "s' = s'' on set (vars c)"
    "t' \<le> t" "t \<le> (t' + 1) * (1 + size\<^sub>c (compile c))"
proof -
  from inline[OF assms(1)] obtain t' s'' where
    "(compile c, s) \<Rightarrow>'\<^bsup>t'\<^esup> s''"
    "s' = s'' on set (vars (compile c))" and
    t': "t' \<le> t" "t \<le> (t' + 1) * (1 + size\<^sub>c (compile c))"
    by blast
  from compile_complete[OF this(1) \<open>invar c\<close>] obtain s''' where
    "c \<turnstile> (c, s) \<Rightarrow>\<^bsup>t' - 7\<^esup> s'''" "s'' = s''' on set (vars c)"
    by blast
  with \<open>s' = s'' on set (vars (compile c))\<close> have "s' = s''' on set (vars c)"
    by (simp add: eq_on_def set_vars_compile)
  with \<open>c \<turnstile> (c, s) \<Rightarrow>\<^bsup>t' - 7\<^esup> s'''\<close> t' show ?thesis
    using that by blast
qed

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
  apply (erule inline_compile_complete)
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