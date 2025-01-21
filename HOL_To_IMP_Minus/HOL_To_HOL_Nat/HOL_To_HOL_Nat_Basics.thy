\<^marker>\<open>creator "Jay Neubrand"\<close>
\<^marker>\<open>creator "Andreas Vollert"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Basic Datatypes and Functions\<close>
theory HOL_To_HOL_Nat_Basics
  imports
    HOL_To_HOL_Nat_Base
begin

unbundle no HOL_ascii_syntax

instantiation nat :: compile_nat
begin
  definition "natify_nat \<equiv> (id :: nat \<Rightarrow> nat)"
  definition "denatify_nat \<equiv> (id :: nat \<Rightarrow> nat)"
  instance by standard (simp add: natify_nat_def denatify_nat_def)
end

lemma Rel_nat_nat_self [Rel_nat]: "Rel_nat n n"
  unfolding Rel_nat_iff_eq_natify natify_nat_def by simp

lemma Rel_nat_nat_eq_eq: "Rel_nat = ((=) :: nat \<Rightarrow> nat \<Rightarrow> bool)"
  by (intro ext) (auto iff: Rel_nat_iff_eq_natify simp: natify_nat_def)

lemma Rel_nat_zero_nat [Rel_nat, Rel_nat_compile_nat]: "Rel_nat (0 :: nat) (0 :: nat)"
  by (fact Rel_nat_nat_self)

lemma Rel_nat_suc_nat [Rel_nat, Rel_nat_compile_nat]: "(Rel_nat ===> Rel_nat) Suc Suc"
  unfolding Rel_nat_iff_eq_natify natify_nat_def
  by (auto simp: natify_nat_def)

lemma Rel_nat_case_nat [Rel_nat, Rel_nat_compile_nat]:
  "(R ===> (Rel_nat ===> R) ===> Rel_nat ===> R) case_nat case_nat"
  by (fact case_nat_transfer[folded Rel_nat_nat_eq_eq])

lemmas Rel_nat_nat = Rel_nat_nat_self Rel_nat_zero_nat Rel_nat_suc_nat Rel_nat_case_nat

text\<open>We instantiate @{typ bool} by hand to make sure that True gets mapped to a positive value and
False to zero. This is due to the fact that the compiler from HOL-Nat to IMP assumes such an
encoding of booleans as natural numbers.\<close>

definition "True_nat \<equiv> 1 :: nat"
definition "False_nat \<equiv> 0 :: nat"

lemma True_nat_neq_zero: "True_nat \<noteq> 0"
  unfolding True_nat_def by simp

lemma zero_lt_True_nat: "0 < True_nat"
  unfolding True_nat_def by simp

lemma False_nat_eq_zero: "False_nat = 0"
  unfolding False_nat_def by simp

lemma True_nat_ne_False_nat: "True_nat \<noteq> False_nat"
  using True_nat_neq_zero False_nat_eq_zero by simp

definition "case_bool_nat \<equiv> \<lambda>x y n. if n = False_nat then y else x"

instantiation bool :: compile_nat
begin
  definition "natify_bool b \<equiv> if b then True_nat else False_nat"
  definition "denatify_bool \<equiv> case_bool_nat True False"
  instance by standard
    (simp add: natify_bool_def denatify_bool_def True_nat_def False_nat_def case_bool_nat_def)
end

lemma natify_True_eq: "natify True = True_nat"
  unfolding natify_bool_def by simp

lemma natify_False_eq: "natify False = False_nat"
  unfolding natify_bool_def by simp

lemma natify_eq_zero_iff_not: "natify b = 0 \<longleftrightarrow> \<not>b"
  unfolding natify_bool_def using True_nat_neq_zero False_nat_eq_zero by (cases b) auto

lemma natify_neq_zero_iff: "natify b \<noteq> 0 \<longleftrightarrow> b"
  unfolding natify_bool_def using True_nat_neq_zero False_nat_eq_zero by (cases b) auto

lemma Rel_nat_bool_iff: "Rel_nat n b \<longleftrightarrow> (b \<longrightarrow> n = True_nat) \<and> (\<not>b \<longrightarrow> n = False_nat)"
  by (cases b) (auto simp: Rel_nat_iff_eq_natify natify_bool_def)

lemma Rel_nat_True_nat [Rel_nat, Rel_nat_compile_nat]: "Rel_nat True_nat True"
  using Rel_nat_bool_iff by simp

lemma Rel_nat_False_nat [Rel_nat, Rel_nat_compile_nat]: "Rel_nat False_nat False"
  using Rel_nat_bool_iff by simp

lemma Rel_nat_case_bool_nat [Rel_nat, Rel_nat_compile_nat]:
  "(R ===> R ===> Rel_nat ===> R) case_bool_nat case_bool"
  by (intro rel_funI)
  (auto simp: Rel_nat_bool_iff case_bool_nat_def True_nat_neq_zero False_nat_eq_zero)

lemmas Rel_nat_bool = Rel_nat_True_nat Rel_nat_False_nat Rel_nat_case_bool_nat

datatype_compile_nat list
print_theorems
datatype_compile_nat char

datatype_compile_nat prod

datatype_compile_nat option

datatype_compile_nat num

end
