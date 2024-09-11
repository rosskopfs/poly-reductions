\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Fun_Pattern_Setup
  imports
    HOL_To_IMP_Minus_Primitives
    "HOL-Library.Simps_Case_Conv"
begin

context HOL_To_IMP_Minus
begin

lemma case_nat_eq_if: "(case n of 0 \<Rightarrow> x | Suc x \<Rightarrow> f x) = (if n = 0 then x else f (n - 1))"
  by (cases n type: nat) auto

end

paragraph \<open>Example Application\<close>

experiment
begin

interpretation HOL_To_IMP_Minus .

fun add_nat_pat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"add_nat_pat 0 0 z = z" |
"add_nat_pat 0 (Suc y) z = add_nat_pat 0 y (z + 1)" |
"add_nat_pat (Suc x) y z = add_nat_pat x y (z + 1)"
declare add_nat_pat.simps[simp del]

print_statement add_nat_pat.induct

case_of_simps add_nat_pat_eq[unfolded case_nat_eq_if] : add_nat_pat.simps
compile_nat add_nat_pat_eq basename add_pat

HOL_To_IMP_Minus_correct add_nat_pat by (cook mode = tailcall)

end

end
