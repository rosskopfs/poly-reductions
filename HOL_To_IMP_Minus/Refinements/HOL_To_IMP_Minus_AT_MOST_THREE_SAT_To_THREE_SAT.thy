theory HOL_To_IMP_Minus_AT_MOST_THREE_SAT_To_THREE_SAT
  imports
    HOL_To_IMP_Minus_SAT_To_AT_MOST_THREE_SAT
    Karp21.AT_MOST_THREE_SAT_To_THREE_SAT
begin

context HOL_To_HOL_Nat
begin

case_of_simps to_at_least_3_clause_eq : to_at_least_3_clause.simps
function_compile_nat to_at_least_3_clause_eq

fun at_most_three_sat_to_three_sat_aux_acc where
  "at_most_three_sat_to_three_sat_aux_acc (x#xs) i acc =
    at_most_three_sat_to_three_sat_aux_acc xs (i + 1) (to_at_least_3_clause (remdups x) i @ acc)"
| "at_most_three_sat_to_three_sat_aux_acc [] i acc = acc"

lemma at_most_three_sat_to_three_sat_aux_acc_eq_at_most_three_sat_to_three_sat_aux_append:
  "at_most_three_sat_to_three_sat_aux_acc xs i acc = at_most_three_sat_to_three_sat_aux xs i @ acc"
  by (induction xs i acc rule: at_most_three_sat_to_three_sat_aux_acc.induct)
  (auto simp: at_most_three_sat_to_three_sat_aux_acc.simps)

case_of_simps at_most_three_sat_to_three_sat_aux_acc_eq :
  at_most_three_sat_to_three_sat_aux_acc.simps
function_compile_nat at_most_three_sat_to_three_sat_aux_acc_eq

lemma at_most_three_sat_to_three_sat_aux_eq_at_most_three_sat_to_three_sat_aux_acc_nil:
  "at_most_three_sat_to_three_sat_aux xs i = at_most_three_sat_to_three_sat_aux_acc xs i []"
  unfolding at_most_three_sat_to_three_sat_aux_acc_eq_at_most_three_sat_to_three_sat_aux_append
  by simp

function_compile_nat at_most_three_sat_to_three_sat_aux_eq_at_most_three_sat_to_three_sat_aux_acc_nil

end

context HOL_Nat_To_IMP_Minus
begin

lemmas to_at_least_3_clause_nat_eq = HTHN.to_at_least_3_clause_nat_eq_unfolded[unfolded
  case_list_nat_def]
compile_nat to_at_least_3_clause_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.to_at_least_3_clause_nat
  (* by cook *) \<comment>\<open>FIXME: too slow\<close>
  sorry

lemmas at_most_three_sat_to_three_sat_aux_acc_nat_eq =
  HTHN.at_most_three_sat_to_three_sat_aux_acc_nat_eq_unfolded[unfolded case_list_nat_def]
compile_nat at_most_three_sat_to_three_sat_aux_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.at_most_three_sat_to_three_sat_aux_acc_nat by cook

compile_nat HTHN.at_most_three_sat_to_three_sat_aux_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.at_most_three_sat_to_three_sat_aux_nat by cook

end

end
