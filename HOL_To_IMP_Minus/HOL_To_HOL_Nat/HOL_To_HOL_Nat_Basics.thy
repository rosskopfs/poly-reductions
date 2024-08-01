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

datatype_compile_nat bool

datatype_compile_nat list

datatype_compile_nat char

datatype_compile_nat prod

datatype_compile_nat num

datatype_compile_nat option

lemma If_related_self [trp_in_dom]:
  "(compile_nat_type_def.R \<Rrightarrow> compile_nat_type_def.R \<Rrightarrow> compile_nat_type_def.R \<Rrightarrow> compile_nat_type_def.R)
    HOL.If HOL.If"
  by simp

trp_term If_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where x = "HOL.If :: bool \<Rightarrow> 'a::compile_nat \<Rightarrow> _"
  by trp_prover

lemma rel_inv_iff_rel_uhint [uhint]:
  assumes "x \<equiv> y'"
  and "y \<equiv> x'"
  and "R \<equiv> R'"
  shows "R\<inverse> x y \<equiv> R' x' y'"
  using assms by simp

context
  includes lifting_syntax
begin

lemma If_nat_lifting [transfer_rule]: "(Rel_nat ===> Rel_nat ===> Rel_nat ===> Rel_nat)
  (If_nat TYPE('a :: compile_nat)) (HOL.If :: bool \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a)"
  unfolding rel_fun_eq_Fun_Rel_rel supply rel_inv_Fun_Rel_rel_eq[rec_uhint]
  by (urule If_nat_related')

lemma If_eq_case: "(if b then s else t) = (case b of True \<Rightarrow> s | False \<Rightarrow> t)"
  by simp

schematic_goal If_nat_synth:
  assumes [transfer_rule]: "(Rel_nat :: nat \<Rightarrow> bool \<Rightarrow> bool) bn b"
  and [transfer_rule]: "(Rel_nat :: nat \<Rightarrow> 'a \<Rightarrow> bool) sn s"
  and [transfer_rule]: "(Rel_nat :: nat \<Rightarrow> 'a \<Rightarrow> bool) tn t"
  shows "Rel_nat ?t ((HOL.If :: bool \<Rightarrow> 'a::compile_nat \<Rightarrow> 'a \<Rightarrow> 'a) b s t)"
  by (subst If_eq_case, transfer_prover)

lemma If_nat_synth_def:
  fixes b :: "bool" and s :: "'a::compile_nat" and t :: "'a"
  assumes [transfer_rule]: "Rel_nat bn b"
  and [transfer_rule]: "Rel_nat sn s"
  and [transfer_rule]: "Rel_nat tn t"
  shows "If_nat TYPE('a) bn sn tn = case_bool_nat sn tn bn"
  apply (rule HOL.trans[OF _ If_nat_synth[unfolded Rel_nat_def, symmetric]])
  using assms by (simp_all add: If_nat_app_eq Rel_nat_iff_eq_natify)

end

fun elemof :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "elemof _ [] = False"
| "elemof y (x#xs) = (if (y = x) then True else elemof y xs)"

function_compile_nat elemof
print_theorems
print_statement elemof_nat_synth_def[unfolded case_list_nat_def]

fun whatever :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where
  "whatever _ xs 0 = True"
| "whatever y [] n = (if False then True else True)"
| "whatever y (x#xs) n = (if (y = x) then True else True)"

(*does not work
function_compile_nat whatever
print_theorems
*)

end
