\<^marker>\<open>creator "Jay Neubrand"\<close>
\<^marker>\<open>creator "Andreas Vollert"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
theory HOL_To_HOL_Nat_Tests
  imports
    HOL_To_HOL_Nat_Basics
begin

context
  includes lifting_syntax
  notes transport_eq_id.partial_equivalence_rel_equivalenceI[per_intro del]
  and transport_eq_restrict_id.partial_equivalence_rel_equivalence[per_intro del]
begin

fun elemof :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "elemof _ [] = False"
| "elemof y (x#xs) = (if (y = x) then True else elemof y xs)"

case_of_simps elemof_eq_case : elemof.simps
function_compile_nat elemof_eq_case
print_theorems

lemma If_eq_case: "If = (\<lambda>b x y. (case b of True \<Rightarrow> x | False \<Rightarrow> y))"
  by (intro ext) simp

function_compile_nat If_eq_case
print_theorems

fun takeWhile :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "takeWhile P [] = []" |
  "takeWhile P (x # xs) = (if P x then x # takeWhile P xs else [])"

case_of_simps takeWhile_eq_case : takeWhile.simps
function_compile_nat takeWhile_eq_case
print_theorems

fun head :: "bool list \<Rightarrow> bool" where
  "head [] = undefined" |
  "head (x # _) = x"

case_of_simps head_eq_case : head.simps
function_compile_nat head_eq_case

fun plus :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "plus m 0 = m" |
  "plus m (Suc n) = Suc (plus m n)"

case_of_simps plus_eq_case : plus.simps
function_compile_nat plus_eq_case
print_theorems

end

end
