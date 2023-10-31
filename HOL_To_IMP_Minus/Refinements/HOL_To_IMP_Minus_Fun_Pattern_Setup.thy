\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Fun_Pattern_Setup
  imports
    HOL_To_IMP_Minus_Primitives
    "HOL-Library.Simps_Case_Conv"
begin

context HOL_To_IMP_Minus
begin

lemma case_nat_eq_if: "(case n of 0 \<Rightarrow> x | Suc x \<Rightarrow> f x) = (if n = 0 then x else f (n - 1))"
  unfolding Nitpick.case_nat_unfold by simp

end

paragraph \<open>Example application:\<close>

experiment
begin

interpretation HOL_To_IMP_Minus .

fun add_nat_pat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"add_nat_pat 0 0 z = z" |
"add_nat_pat 0 (Suc y) z = add_nat_pat 0 y (z + 1)" |
"add_nat_pat (Suc x) y z = add_nat_pat x y (z + 1)"
declare add_nat_pat.simps[simp del]
                        
case_of_simps add_nat_pat_eq[simplified Nitpick.case_nat_unfold] : add_nat_pat.simps
compile_nat add_nat_pat_eq basename add_pat

lemma add_nat_pat_IMP_func_correct:
  assumes "(tailcall_to_IMP_Minus add_pat_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "s' ''add_pat_ret'' = add_nat_pat (s ''add_pat_x1a'') (s ''add_pat_x2a'') (s ''add_pat_x3ba'')"
  using assms                                 
  apply (rule tailcall_to_IMP_Minus_correct_if_correct)
  apply (subst compiled_const_defs, simp)
  apply (subst compiled_const_defs, simp)
  subgoal for t s'
  apply (induction "(s ''add_pat_x1a'')" "(s ''add_pat_x2a'')" "(s ''add_pat_x3ba'')" arbitrary: s t rule: add_nat_pat.induct)
  apply (tactic \<open>H.start_run_finish_pattern_fun_tac @{thms compiled_const_defs} @{thms func_correct} 
    @{thms add_nat_pat.simps} @{context} 1\<close>)+
  done
  done

end

end