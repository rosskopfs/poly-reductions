\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Datatypes
  imports
    HOL_To_IMP_Minus_Arithmetics
    "HOL-Library.Nat_Bijection"
begin

context HOL_To_IMP_Minus
begin

compile_nat triangle_def basename triangle

lemma triangle_IMP_func_correct [func_correct]:
  assumes "(tailcall_to_IMP_Minus triangle_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "s' ''triangle_ret'' = triangle (s ''triangle_n'')"
  using assms
  apply (rule tailcall_to_IMP_Minus_correct_if_correct)
  apply (subst compiled_const_defs, simp)
  apply (subst compiled_const_defs, simp)
  apply (tactic \<open>H.start_run_finish_no_pattern_fun_tac @{thms compiled_const_defs} @{thms func_correct} 
     @{thms triangle_def} @{context} 1\<close>)
  done

text \<open>up next: encoding of products, sums, etc. See @{term prod_encode}\<close>

end

end