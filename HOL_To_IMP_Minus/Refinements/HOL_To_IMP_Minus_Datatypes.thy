\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Datatypes
  imports
    HOL_To_IMP_Minus_Arithmetics
    "HOL-Library.Nat_Bijection"
begin

context HOL_To_IMP_Minus
begin

compile_nat triangle_def basename triangle

HOL_To_IMP_Minus_func_correct triangle
  apply preprocess_HOL_To_IMP_Minus_func_correct
  apply (tactic \<open>H.start_run_finish_no_pattern_fun_tac @{thms compiled_const_defs} @{thms IMP_Minus_func_correct}
     @{thms triangle_def} @{context} 1\<close>)
  done

text \<open>up next: encoding of products, sums, etc. See @{term prod_encode}\<close>

end

end