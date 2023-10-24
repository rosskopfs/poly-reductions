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

lemma tAssignD: "c \<turnstile> (x ::= a, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> t = 2 \<and> s' = s(x := aval a s)"
  by auto

ML_file \<open>hol_to_imp_minus_tailcalls_tactics.ML\<close>

ML \<open>
  structure H = HOL_To_IMP_Minus_Tailcalls_Tactics
  structure SCL = State_Cook_Levin_IMP_Minus_Tailcalls
\<close>

lemma inline_compile_correct_if_correct:
  assumes "(inline (compile c), s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  and "invar c"
  and "x \<in> set (vars c)"
  and "\<And>t s'. c \<turnstile> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> s' x = v"
  shows "s' x = v"
proof -
  from inline_compile_complete[OF assms(1,2)] obtain t' s'' where
    c_eval: "c \<turnstile> (c, s) \<Rightarrow>\<^bsup>t' - 7\<^esup> s''" and "s' = s'' on set (vars c)" by blast
  with assms(3) have "s' x = s'' x" by blast
  also from c_eval assms(4) have "... = v" by auto
  finally show ?thesis .
qed

(*  apply (tactic \<open>H.start_tac @{thm not_IMP_def} @{context} 1\<close>)
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
  apply (tactic \<open>H.finish_tac @{thm not_nat_def} @{context} 1\<close>)*)

lemma not_IMP_func_correct:
  assumes "(inline (compile (not_IMP)), s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "s' ''not_ret'' = not_nat (s ''not_n'')"
  using assms                                 
  apply (rule inline_compile_correct_if_correct)
  apply (simp add: not_IMP_def)
  apply (simp add: not_IMP_def)
  apply (tactic \<open>H.run_finish_tac' @{thm not_nat_def} @{thm not_IMP_def}
    [@{thm eq_IMP_func_correct}] @{context} 1\<close>)
  done
  
definition max_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "max_nat x y \<equiv> if x - y \<noteq> 0 then x else y"  

compile_nat max_nat_def basename max

lemma max_IMP_func_correct:
  assumes "(inline (compile (max_IMP)), s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "s' ''max_ret'' = max_nat (s ''max_x'') (s ''max_y'')"
  using assms                                 
  apply (rule inline_compile_correct_if_correct)
  apply (simp add: max_IMP_def)
  apply (simp add: max_IMP_def)
  apply (tactic \<open>H.run_finish_tac' @{thm max_nat_def} @{thm max_IMP_def}
    [@{thm eq_IMP_func_correct}, @{thm not_IMP_func_correct}] @{context} 1\<close>)
  apply (simp_all add: not_nat_def eq_nat_def split: if_splits)
  done

  
definition test_let :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "test_let x y \<equiv> let u = 10; v = u + y in v + x"

compile_nat test_let_def

lemma let_let_IMP_func_correct:
  assumes "(inline (compile (test_let_IMP)), s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "s' ''test_let_ret'' = test_let (s ''test_let_x'') (s ''test_let_y'')"
  using assms                                 
  apply (rule inline_compile_correct_if_correct)
  apply (simp add: test_let_IMP_def)
  apply (simp add: test_let_IMP_def)
  apply (tactic \<open>H.run_finish_tac' @{thm test_let_def} @{thm test_let_IMP_def}
    [@{thm eq_IMP_func_correct}, @{thm not_IMP_func_correct}] @{context} 1\<close>)
  done


fun add_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add_nat x y z =
    (if x \<noteq> 0
      then add_nat (x - 1) y (z + 1)
      else (if y \<noteq> 0 then add_nat x (y - 1) (z + 1) else z))"

compile_nat add_nat.simps basename add

lemma let_let_IMP_func_correct:
  assumes "(inline (compile (add_IMP)), s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "s' ''add_ret'' = add_nat (s ''add_x'') (s ''add_y'') (s ''add_z'')"
  using assms                                 
  apply (rule inline_compile_correct_if_correct)
  apply (simp add: add_IMP_def)
  (*apply (simp add: add_IMP_def)*)
  (*apply (tactic \<open>H.run_finish_tac' @{thm test_let_def} @{thm test_let_IMP_def}*)
    (*[@{thm eq_IMP_func_correct}, @{thm not_IMP_func_correct}] @{context} 1\<close>)*)
  oops



end