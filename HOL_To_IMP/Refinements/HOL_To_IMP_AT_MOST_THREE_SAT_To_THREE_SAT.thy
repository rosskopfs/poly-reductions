\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_AT_MOST_THREE_SAT_To_THREE_SAT
  imports
    HOL_To_IMP_SAT_To_AT_MOST_THREE_SAT
    Karp21.AT_MOST_THREE_SAT_To_THREE_SAT
begin

context HOL_To_HOL_Nat
begin

definition "to_at_least_3_clause_empty1 i \<equiv>
  let
    R0 = RU (i, 0);
    R1 = RU (i, 1);
    R2 = RU (i, 2);
    PR0 = Pos R0;
    PR1 = Pos R1;
    NR1 = Neg R1;
    PR2 = Pos R2;
    NR2 = Neg R2
  in
    [[PR0, PR1, PR2],
    [PR0, PR1, NR2],
    [PR0, NR1, PR2],
    [PR0, NR1, NR2]]"

function_compile_nat to_at_least_3_clause_empty1_def

definition "to_at_least_3_clause_empty2 i \<equiv>
  let
    R0 = RU (i, 0);
    R1 = RU (i, 1);
    R2 = RU (i, 2);
    NR0 = Neg R0;
    PR1 = Pos R1;
    NR1 = Neg R1;
    PR2 = Pos R2;
    NR2 = Neg R2
  in
    [[NR0, PR1, PR2],
    [NR0, PR1, NR2],
    [NR0, NR1, PR2],
    [NR0, NR1, NR2]]"

function_compile_nat to_at_least_3_clause_empty2_def

definition "to_at_least_3_clause_single i x \<equiv>
  let
    R0 = RU (i, 0);
    R1 = RU (i, 1);
    PR0 = Pos R0;
    NR0 = Neg R0;
    PR1 = Pos R1;
    NR1 = Neg R1
  in
    [[x,PR0, PR1],
    [x, PR0, NR1],
    [x, NR0, PR1],
    [x, NR0, NR1]]"

function_compile_nat to_at_least_3_clause_single_def

definition "to_at_least_3_clause_double i x y \<equiv>
  [[x, y, Pos (RU (i, 0))], [x, y, Neg (RU (i, 0))]]"

function_compile_nat to_at_least_3_clause_double_def

lemma to_at_least_3_clause_eq: "to_at_least_3_clause xs i = (case xs of
  [] => to_at_least_3_clause_empty1 i @ to_at_least_3_clause_empty2 i
| [x] => to_at_least_3_clause_single i x
| [x, y] => to_at_least_3_clause_double i x y
| xs => [xs])"
  unfolding to_at_least_3_clause_empty1_def to_at_least_3_clause_empty2_def Let_def
    to_at_least_3_clause_single_def to_at_least_3_clause_double_def
  by (induction xs i rule: to_at_least_3_clause.induct) simp_all

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

context HOL_Nat_To_IMP
begin

compile_nat HTHN.to_at_least_3_clause_empty1_nat_eq_unfolded
HOL_To_IMP_correct HOL_To_HOL_Nat.to_at_least_3_clause_empty1_nat by cook

compile_nat HTHN.to_at_least_3_clause_empty2_nat_eq_unfolded
HOL_To_IMP_correct HOL_To_HOL_Nat.to_at_least_3_clause_empty2_nat by cook

compile_nat HTHN.to_at_least_3_clause_single_nat_eq_unfolded
HOL_To_IMP_correct HOL_To_HOL_Nat.to_at_least_3_clause_single_nat by cook

compile_nat HTHN.to_at_least_3_clause_double_nat_eq_unfolded
HOL_To_IMP_correct HOL_To_HOL_Nat.to_at_least_3_clause_double_nat by cook

lemmas to_at_least_3_clause_nat_eq = HTHN.to_at_least_3_clause_nat_eq_unfolded[
  unfolded case_list_nat_def]
compile_nat to_at_least_3_clause_nat_eq
HOL_To_IMP_correct HOL_To_HOL_Nat.to_at_least_3_clause_nat by (cook mode = induction)

lemmas at_most_three_sat_to_three_sat_aux_acc_nat_eq =
  HTHN.at_most_three_sat_to_three_sat_aux_acc_nat_eq_unfolded[unfolded case_list_nat_def]
compile_nat at_most_three_sat_to_three_sat_aux_acc_nat_eq
HOL_To_IMP_correct HOL_To_HOL_Nat.at_most_three_sat_to_three_sat_aux_acc_nat by cook

compile_nat HTHN.at_most_three_sat_to_three_sat_aux_nat_eq_unfolded
HOL_To_IMP_correct HOL_To_HOL_Nat.at_most_three_sat_to_three_sat_aux_nat by cook

end

end
