\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Datatypes
  imports
    HOL_To_IMP_Minus_Arithmetics
    "HOL-Library.Nat_Bijection"
begin

context HOL_To_IMP_Minus
begin

compile_nat triangle_def basename triangle

ML \<open>HOL_To_IMP_Minus_Func_Correct_Thms.get (Context.Proof @{context})\<close>

HOL_To_IMP_Minus_func_correct triangle
  apply preprocess_HOL_To_IMP_Minus_func_correct
  apply (start_run_finish triangle_def)
  done

text \<open>up next: encoding of products, sums, etc. See @{term prod_encode}\<close>

end

end