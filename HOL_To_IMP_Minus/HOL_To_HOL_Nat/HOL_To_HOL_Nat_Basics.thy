\<^marker>\<open>creator "Jay Neubrand"\<close>
\<^marker>\<open>creator "Andreas Vollert"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Basic Datatypes and Functions\<close>
theory HOL_To_HOL_Nat_Basics
  imports
    HOL_To_HOL_Nat_Base
begin

unbundle no_HOL_ascii_syntax

instantiation nat :: compile_nat
begin
  definition "natify_nat \<equiv> (id :: nat \<Rightarrow> nat)"
  definition "denatify_nat \<equiv> (id :: nat \<Rightarrow> nat)"
  instance by standard (simp add: natify_nat_def denatify_nat_def)
end

lemma Rel_nat_nat_self [transfer_rule]: "Rel_nat n n"
  unfolding Rel_nat_iff_eq_natify natify_nat_def by simp

lemma Rel_nat_nat_eq_eq: "Rel_nat = ((=) :: nat \<Rightarrow> nat \<Rightarrow> bool)"
  by (intro ext) (auto iff: Rel_nat_iff_eq_natify simp: natify_nat_def)

lemma Rel_nat_case_nat_nat [transfer_rule]:
  "rel_fun R (rel_fun (rel_fun Rel_nat R) (rel_fun Rel_nat R)) case_nat case_nat"
  by (fact case_nat_transfer[folded Rel_nat_nat_eq_eq])

lemma Rel_nat_zero_nat_zero [transfer_rule]: "Rel_nat (0 :: nat) (0 :: nat)"
  unfolding Rel_nat_iff_eq_natify natify_nat_def by (auto simp: natify_nat_def)

lemma Rel_nat_suc_nat_suc [transfer_rule]: "rel_fun Rel_nat Rel_nat Suc Suc"
  unfolding Rel_nat_iff_eq_natify natify_nat_def
  by (auto simp: natify_nat_def)

datatype_compile_nat bool

datatype_compile_nat list

datatype_compile_nat char

datatype_compile_nat prod

datatype_compile_nat num

datatype_compile_nat option

end
