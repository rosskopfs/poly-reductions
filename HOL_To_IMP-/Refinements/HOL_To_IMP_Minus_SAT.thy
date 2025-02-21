\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Nico Lintner"\<close>
theory HOL_To_IMP_Minus_SAT
  imports
    HOL_To_IMP_Minus_Lists
    Karp21.SAT_List_Definition
begin

datatype_compile_nat lit

context HOL_To_HOL_Nat
begin

lemmas is_n_clause_list_eq = is_n_clause_list_def[unfolded is_n_clause_def,
    folded length_remdups_card_conv, unfolded list_length_eq_length]
function_compile_nat is_n_clause_list_eq

lemmas is_n_sat_list_eq = list_all_eq[of "is_n_clause_list n" for n,
  folded is_n_sat_list_def[unfolded Ball_set_list_all]]
function_compile_nat is_n_sat_list_eq

case_of_simps flip_lit_eq : flip_lit.simps
function_compile_nat flip_lit_eq

case_of_simps map_lit_eq : lit.map

end

context HOL_Nat_To_IMP_Minus
begin

declare Rel_nat_selector_lit[Rel_nat]

compile_nat Pos_nat_def
HOL_To_IMP_Minus_correct Pos_nat by cook

compile_nat Neg_nat_def
HOL_To_IMP_Minus_correct Neg_nat by cook

compile_nat HTHN.is_n_clause_list_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.is_n_clause_list_nat by cook

lemmas is_n_sat_list_nat_eq = HTHN.is_n_sat_list_nat_eq_unfolded[unfolded
  case_list_nat_def case_bool_nat_def]
compile_nat is_n_sat_list_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.is_n_sat_list_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction ya arbitrary: s)
  (tactic \<open>PARALLEL_ALLGOALS (HT.start_run_finish_case_tac HT.get_IMP_def HT.get_imp_minus_correct
    HB.get_HOL_eqs @{context})\<close>)

lemmas flip_lit_nat_eq = HTHN.flip_lit_nat_eq_unfolded[unfolded case_lit_nat_def]
compile_nat flip_lit_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.flip_lit_nat by cook

end

end
