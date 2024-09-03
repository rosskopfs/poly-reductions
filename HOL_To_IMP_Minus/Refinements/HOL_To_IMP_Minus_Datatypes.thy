\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Datatypes
  imports
    HOL_To_IMP_Minus_Arithmetics
begin

locale HOL_To_HOL_Nat =
  notes transport_eq_id.partial_equivalence_rel_equivalenceI[per_intro del]
  and transport_eq_restrict_id.partial_equivalence_rel_equivalence[per_intro del]
begin

paragraph \<open>rev\<close>

fun rev_aux :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_aux acc [] = acc" |
  "rev_aux acc (x # xs) = rev_aux (x # acc) xs"

case_of_simps rev_aux_eq : rev_aux.simps

function_compile_nat rev_aux_eq

definition rev :: "'a list \<Rightarrow> 'a list" where
  "rev = rev_aux []"

function_compile_nat rev_def

paragraph \<open>zip\<close>

thm zip.simps
case_of_simps zip_eq : zip.simps
function_compile_nat zip_eq

end


context HOL_To_IMP_Minus
begin

compile_nat Cons_nat_def
HOL_To_IMP_Minus_correct Cons_nat by cook

compile_nat Nil_nat_def
HOL_To_IMP_Minus_correct Nil_nat by cook

thm HOL_To_HOL_Nat.rev_aux_nat_eq_unfolded
lemmas rev_aux_nat_eq = HOL_To_HOL_Nat.rev_aux_nat_eq_unfolded[simplified case_list_nat_def]
unconditional_nat rev_aux_nat_eq
compile_nat rev_aux_nat_unconditional.simps

(*
thm HOL_To_HOL_Nat.rev_nat_eq_unfolded
lemmas rev_nat_eq = HOL_To_HOL_Nat.rev_nat_eq_unfolded[simplified case_list_nat_def]
unconditional_nat rev_nat_eq
*)

end

end
