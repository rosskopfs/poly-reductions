\<^marker>\<open>creator "Jay Neubrand"\<close>
\<^marker>\<open>creator "Andreas Vollert"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
theory Lifting_Nat
  imports
    HOL_To_HOL_Nat_Setup
begin

unbundle lifting_syntax

(* TODO: still necessary? *)
lemma Domainp_nat_bool_rel [transfer_domain_rule]:
  "Domainp (Rel_nat :: _ \<Rightarrow> bool \<Rightarrow> _) = (\<lambda>x. x = False_nat \<or> x = True_nat)"
  unfolding Rel_nat_def natify_bool.simps
  by (auto split :bool.split)

(* TODO: still necessary? *)
lemma nat_bool_rel_conj [transfer_rule]: "(Rel_nat ===> Rel_nat ===> Rel_nat) max (\<and>)"
  unfolding Rel_nat_def natify_bool.simps
  by (simp add: pair_def True_nat_def prod_encode_0 rel_fun_def split: bool.split)

(* TODO: still necessary? *)
lemma nat_bool_rel_disj [transfer_rule]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) min (\<or>)"
  unfolding Rel_nat_def natify_bool.simps
  by (simp add: pair_def True_nat_def prod_encode_0 rel_fun_def split: bool.split)

fun elemof :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "elemof _ [] = False"
| "elemof y (x#xs) = (if (y = x) then True else elemof y xs)"

function_compile_nat elemof
print_theorems

(*
lemma elemof_related_self [trp_in_dom]:
  "(compile_nat_type_def.R \<Rrightarrow> compile_nat_type_def.R \<Rrightarrow> compile_nat_type_def.R) elemof elemof"
  unfolding Fun_Rel_rel_def
  by auto

trp_term elemof_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where x = "elemof :: ('a :: compile_nat) \<Rightarrow> _"
  by trp_prover

lemma elemof_nat_lifting[transfer_rule]:
  shows "(Rel_nat ===> Rel_nat ===> Rel_nat) (elemof_nat TYPE('a::compile_nat)) (elemof :: 'a \<Rightarrow> _)"
  unfolding rel_fun_eq_Fun_Rel_rel
  by (fact elemof_nat_related'[unfolded rel_inv_Fun_Rel_rel_eq[symmetric] rel_inv_iff_rel])

schematic_goal elemof_nat_synth:
  assumes [transfer_rule]: "(Rel_nat :: nat \<Rightarrow> 'a \<Rightarrow> bool) xn (denatify xn)"
  assumes [transfer_rule]: "(Rel_nat :: nat \<Rightarrow> 'a list \<Rightarrow> bool) xsn (denatify xsn)"
  shows "Rel_nat ?t ((elemof :: 'a::compile_nat \<Rightarrow> _) (denatify xn) (denatify xsn))"
  apply (subst elemof_case_def)
  by transfer_prover

lemma elemof_nat_synth_def:
  fixes x :: "'a::compile_nat " and xs :: "'a list"
  assumes "xn = natify_x"
  assumes "xsn = natify_xs"
  shows "elemof_nat TYPE('a) xn xsn
    = case_list_nat False_nat (\<lambda>y ys. if xn = y then True_nat else elemof_nat TYPE('a) xn ys) xsn"
  apply(rule HOL.trans[OF _ elemof_nat_synth[unfolded Rel_nat_def, symmetric]])
    apply(simp add: elemof_nat_app_eq assms; subst denatify_natify_id)+
  done *)

fun takeWhile :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "takeWhile P [] = []" |
  "takeWhile P (x # xs) = (if P x then x # takeWhile P xs else [])"

(* TODO: goals for higher-order set up the wrong way*)
function_compile_nat takeWhile
print_theorems

fun head :: "'a list \<Rightarrow> 'a" where
  "head [] = undefined" |
  "head (x # _) = x"

function_compile_nat head

fun append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "append xs [] = xs" |
  "append xs ys = rev_tr ys (rev_tr [] xs)"

function_compile_nat append

fun plus :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "plus m 0 = m" |
  "plus m (Suc n) = Suc (plus m n)"

(* TODO: Not working yet. Explicitly specify L in trp_term *)
function_compile_nat plus

thm plus_nat_synth_def[unfolded case_nat_nat_def]

end
