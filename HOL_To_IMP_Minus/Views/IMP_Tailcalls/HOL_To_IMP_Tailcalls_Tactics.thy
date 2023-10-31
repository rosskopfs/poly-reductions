\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Tailcalls_Tactics
  imports
    States_IMP_Tailcalls
    Compile_Nat
    (*"HOL-Library.Simps_Case_Conv"*)
begin

lemma tailcall_to_IMP_Minus_complete:
  assumes "(tailcall_to_IMP_Minus c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  and "invar c"
  obtains t' s'' where
    "c \<turnstile> (c, s) \<Rightarrow>\<^bsup>t' - 7\<^esup> s''" "s' = s'' on set (vars c)"
    "t' \<le> t" "t \<le> (t' + 1) * (1 + size\<^sub>c (compile c))"
proof -
  from assms inline obtain t' s'' where
    "(compile c, s) \<Rightarrow>'\<^bsup>t'\<^esup> s''"
    "s' = s'' on set (vars (compile c))" and
    t': "t' \<le> t" "t \<le> (t' + 1) * (1 + size\<^sub>c (compile c))"
    unfolding tailcall_to_IMP_Minus_eq by blast
  from compile_complete[OF this(1) \<open>invar c\<close>] obtain s''' where
    "c \<turnstile> (c, s) \<Rightarrow>\<^bsup>t' - 7\<^esup> s'''" "s'' = s''' on set (vars c)"
    by blast
  with \<open>s' = s'' on set (vars (compile c))\<close> have "s' = s''' on set (vars c)"
    by (simp add: eq_on_def set_vars_compile)
  with \<open>c \<turnstile> (c, s) \<Rightarrow>\<^bsup>t' - 7\<^esup> s'''\<close> t' show ?thesis
    using that by blast
qed

lemma tailcall_to_IMP_Minus_correct_if_correct:
  assumes "(tailcall_to_IMP_Minus c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  and "invar c"
  and "x \<in> set (vars c)"
  and "\<And>t s'. c \<turnstile> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> s' x = v"
  shows "s' x = v"
proof -
  from tailcall_to_IMP_Minus_complete[OF assms(1,2)] obtain t' s'' where
    c_eval: "c \<turnstile> (c, s) \<Rightarrow>\<^bsup>t' - 7\<^esup> s''" and "s' = s'' on set (vars c)" by blast
  with assms(3) have "s' x = s'' x" by blast
  also from c_eval assms(4) have "... = v" by auto
  finally show ?thesis .
qed

context includes Com.no_com_syntax IMP_Tailcalls_Dynamic.tcom_syntax
begin

lemma tAssignD: "c \<turnstile> (x ::= a, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> t = 2 \<and> s' = s(x := aval a s)"
  by auto

theorem tIf_tE':
  assumes "c \<turnstile>(IF b\<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup>t\<^esup>  s'"
  obtains t' where "t = Suc t'" and "s b \<noteq> 0" and "c \<turnstile>(c1, s) \<Rightarrow>\<^bsup>t'\<^esup> s'"
    | t' where "t = Suc t'" and "s b = 0" and "c \<turnstile>(c2, s) \<Rightarrow>\<^bsup>t'\<^esup> s'"
  using assms by auto

ML_file \<open>hol_to_imp_tailcalls_tactics.ML\<close>

ML \<open>
  structure H = HOL_To_IMP_Tailcalls_Tactics
  structure SIT = State_IMP_Tailcalls
\<close>

(*lemma case_nat_eq_if: "(case n of 0 \<Rightarrow> x | Suc x \<Rightarrow> f x) = (if n = 0 then x else f (n - 1))"
  unfolding Nitpick.case_nat_unfold by simp

fun add_nat_pat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"add_nat_pat 0 0 z = z" |
"add_nat_pat 0 (Suc y) z = add_nat_pat 0 y (Suc z)" |
"add_nat_pat (Suc x) y z = add_nat_pat x y (Suc z)"
declare add_nat_pat.simps[simp del]
                        
case_of_simps add_nat_pat_eq[simplified Nitpick.case_nat_unfold] : add_nat_pat.simps
compile_nat add_nat_pat_eq basename add_pat

lemma add_nat_pat_IMP_func_correct[cl_func_correct]:
  assumes "(inline (compile (add_pat_IMP)), s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "s' ''add_pat_ret'' = add_nat_pat (s ''add_pat_x1a'') (s ''add_pat_x2a'') (s ''add_pat_x3ba'')"
  using assms                                 
  apply (rule inline_compile_correct_if_correct)
  apply (simp add: add_pat_IMP_def)
  apply (simp add: add_pat_IMP_def)
  subgoal for t s'
  apply (induction "(s ''add_pat_x1a'')" "(s ''add_pat_x2a'')" "(s ''add_pat_x3ba'')" arbitrary: s t rule: add_nat_pat.induct)
  apply simp
  apply (tactic \<open>H.run_finish_tac @{thms add_nat_pat.simps} @{thm add_pat_IMP_def} 
    @{thms cl_func_correct} @{context} 1\<close>)
  apply simp
  apply (tactic \<open>H.run_tac @{thm add_pat_IMP_def} @{thms cl_func_correct} @{context} 1\<close>)
  (*apply (tactic \<open>H.finish_non_tailcall_tac @{thms add_nat_pat.simps} @{context} 1\<close>)*)
  apply (tactic \<open>SIT.rewrite_all_state_app_tac' (fn ctxt => View_Util.subst_first_tac ctxt o single) @{context} 1\<close>)
  apply (tactic \<open>SIT.remove_state_eq_tac @{context} 1\<close>)
  (*apply (tactic \<open>View_Util.subst_first_tac @{context} @{thms add_nat_pat.simps} 1\<close>)*)
    (*THEN' VU.subst_first_tac ctxt HOL_program_eqs*)
    (*THEN' TU.TRY' (REPEAT_ALL_NEW (VU.subst_first_tac ctxt @{thm Let_def} ORELSE' if_split_tac ctxt))*)
    (*THEN_ALL_NEW finish_goal_tac)*)
  oops
*)
end
  

end
