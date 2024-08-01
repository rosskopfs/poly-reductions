\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Datatypes
  imports
    HOL_To_IMP_Minus_Arithmetics
    "HOL-Library.Nat_Bijection"
begin

context HOL_To_IMP_Minus
begin

compile_nat triangle_def basename triangle

HOL_To_IMP_Minus_imp_minus_correct triangle by cook

text \<open>up next: encoding of products, sums, etc. See @{term prod_encode}\<close>

end

end
