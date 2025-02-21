\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_SAT_To_AT_MOST_THREE_SAT
  imports
    HOL_To_IMP_Minus_SAT
    Karp21.SAT_To_AT_MOST_THREE_SAT
begin

datatype_compile_nat red

context HOL_To_HOL_Nat
begin

definition "pos_RU_flip_lit i j l \<equiv> [Pos (RU (i, j)), flip_lit l]"
function_compile_nat pos_RU_flip_lit_def

definition "map_acc_pos_RU_flip_lit i j \<equiv> map_acc (pos_RU_flip_lit i j)"
lemmas map_acc_pos_RU_flip_lit_eq = map_acc_eq[of "pos_RU_flip_lit i j" for i j,
  folded map_acc_pos_RU_flip_lit_def]
function_compile_nat map_acc_pos_RU_flip_lit_eq

end

context HOL_Nat_To_IMP_Minus
begin

declare Rel_nat_selector_red[Rel_nat]

compile_nat RV_nat_def
HOL_To_IMP_Minus_correct RV_nat by cook

compile_nat RU_nat_def
HOL_To_IMP_Minus_correct RU_nat by cook

compile_nat HTHN.pos_RU_flip_lit_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.pos_RU_flip_lit_nat by cook

lemmas map_acc_pos_RU_flip_lit_nat_eq =
  HTHN.map_acc_pos_RU_flip_lit_nat_eq_unfolded[unfolded case_list_nat_def]
compile_nat map_acc_pos_RU_flip_lit_nat_eq

HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_acc_pos_RU_flip_lit_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction "HTHN.pos_RU_flip_lit y ya :: 'a red lit \<Rightarrow> _" _ _ arbitrary: s
    rule: HTHN.map_acc.induct)
  (cook mode = run_finish)

end

context HOL_To_HOL_Nat
begin

definition [termination_simp]: "to_at_most_3_clause_acc_body_rec_aux1 i j c d rest \<equiv>
  Neg (RU (i, j)) # c # d # rest"

lemmas to_at_most_3_clause_acc_body_rec_aux1_eq = to_at_most_3_clause_acc_body_rec_aux1_def
function_compile_nat to_at_most_3_clause_acc_body_rec_aux1_eq

definition "to_at_most_3_clause_acc_body_rec_aux2 a b c d rest i j acc \<equiv>
  (([a, b, Pos (RU (i, j))] # map (\<lambda>l. [Pos (RU (i, j)), flip_lit l]) (c # d # rest)) @ acc)"

lemmas to_at_most_3_clause_acc_body_rec_aux2_eq =
  to_at_most_3_clause_acc_body_rec_aux2_def[unfolded map_eq_map_acc_nil,
  folded pos_RU_flip_lit_def map_acc_pos_RU_flip_lit_def]
function_compile_nat to_at_most_3_clause_acc_body_rec_aux2_eq

fun to_at_most_3_clause_acc where
  "to_at_most_3_clause_acc (a # b # c # d # rest) i j acc =
    to_at_most_3_clause_acc (to_at_most_3_clause_acc_body_rec_aux1 i j c d rest) i (j + 1)
    (to_at_most_3_clause_acc_body_rec_aux2 a b c d rest i j acc)"
| "to_at_most_3_clause_acc xs i j acc = [xs] @ acc"
declare to_at_most_3_clause_acc.simps[simp del]

lemma to_at_most_3_clause_acc_eq_to_at_most_3_clause_append:
  "to_at_most_3_clause_acc xs i j acc = to_at_most_3_clause xs i j @ acc"
  by (induction xs i j acc rule: to_at_most_3_clause_acc.induct)
  (auto simp: to_at_most_3_clause_acc.simps
    to_at_most_3_clause_acc_body_rec_aux1_def to_at_most_3_clause_acc_body_rec_aux2_def)

case_of_simps to_at_most_3_clause_acc_eq : to_at_most_3_clause_acc.simps
function_compile_nat to_at_most_3_clause_acc_eq

lemma to_at_most_3_clause_eq_to_at_most_3_clause_acc_nil:
  "to_at_most_3_clause xs i j = to_at_most_3_clause_acc xs i j []"
  unfolding to_at_most_3_clause_acc_eq_to_at_most_3_clause_append by simp

function_compile_nat to_at_most_3_clause_eq_to_at_most_3_clause_acc_nil

end

context HOL_Nat_To_IMP_Minus
begin

compile_nat HTHN.to_at_most_3_clause_acc_body_rec_aux1_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.to_at_most_3_clause_acc_body_rec_aux1_nat by cook

compile_nat HTHN.to_at_most_3_clause_acc_body_rec_aux2_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.to_at_most_3_clause_acc_body_rec_aux2_nat by cook

lemmas to_at_most_3_clause_acc_nat_eq = HTHN.to_at_most_3_clause_acc_nat_eq_unfolded[unfolded
  case_list_nat_def]
compile_nat to_at_most_3_clause_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.to_at_most_3_clause_acc_nat
  by cook \<comment>\<open>FIXME: very slow, but terminates!\<close>

compile_nat HTHN.to_at_most_3_clause_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.to_at_most_3_clause_nat by cook

end

context HOL_To_HOL_Nat
begin

fun sat_to_at_most_three_sat_aux_acc where
  "sat_to_at_most_three_sat_aux_acc (x # xs) i acc =
    sat_to_at_most_three_sat_aux_acc xs (i + 1) (to_at_most_3_clause x i 0 @ acc)"
| "sat_to_at_most_three_sat_aux_acc [] i acc = acc"

declare sat_to_at_most_three_sat_aux_acc.simps[simp del]

lemma sat_to_at_most_three_sat_aux_acc_eq_sat_to_at_most_three_sat_aux_append:
  "sat_to_at_most_three_sat_aux_acc xs i acc = sat_to_at_most_three_sat_aux xs i @ acc"
  by (induction xs i acc rule: sat_to_at_most_three_sat_aux_acc.induct)
  (auto simp: sat_to_at_most_three_sat_aux_acc.simps)

case_of_simps sat_to_at_most_three_sat_aux_acc_eq : sat_to_at_most_three_sat_aux_acc.simps
function_compile_nat sat_to_at_most_three_sat_aux_acc_eq

lemma sat_to_at_most_three_sat_aux_eq_sat_to_at_most_three_sat_aux_acc_nil:
  "sat_to_at_most_three_sat_aux xs i = sat_to_at_most_three_sat_aux_acc xs i []"
  unfolding sat_to_at_most_three_sat_aux_acc_eq_sat_to_at_most_three_sat_aux_append by simp

function_compile_nat sat_to_at_most_three_sat_aux_eq_sat_to_at_most_three_sat_aux_acc_nil

end

context HOL_Nat_To_IMP_Minus
begin

lemmas sat_to_at_most_three_sat_aux_acc_nat_eq = HTHN.sat_to_at_most_three_sat_aux_acc_nat_eq_unfolded[unfolded
  case_list_nat_def]
compile_nat sat_to_at_most_three_sat_aux_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.sat_to_at_most_three_sat_aux_acc_nat by cook

compile_nat HTHN.sat_to_at_most_three_sat_aux_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.sat_to_at_most_three_sat_aux_nat by cook

end

context HOL_To_HOL_Nat
begin

definition "map_lit_RV \<equiv> map_lit RV"
lemmas map_lit_RV_eq = map_lit_eq[of RV, folded map_lit_RV_def]
function_compile_nat map_lit_RV_eq

definition "map_acc_map_lit_RV \<equiv> map_acc map_lit_RV"
lemmas map_acc_map_lit_RV_eq = map_acc_eq[of map_lit_RV, folded map_acc_map_lit_RV_def]
function_compile_nat map_acc_map_lit_RV_eq

definition "map_map_lit_RV \<equiv> map map_lit_RV"
lemmas map_map_lit_RV_eq = map_map_lit_RV_def[unfolded map_eq_map_acc_nil,
  folded map_acc_map_lit_RV_def]
function_compile_nat map_map_lit_RV_eq

definition "map_acc_map_map_lit_RV \<equiv> map_acc map_map_lit_RV"
lemmas map_acc_map_map_lit_RV_eq = map_acc_eq[of map_map_lit_RV, folded map_acc_map_map_lit_RV_def]
function_compile_nat map_acc_map_map_lit_RV_eq

definition "map_map_map_lit_RV \<equiv> map map_map_lit_RV"
lemmas map_map_map_lit_RV_eq = map_map_map_lit_RV_def[unfolded map_eq_map_acc_nil,
  folded map_acc_map_map_lit_RV_def]
function_compile_nat map_map_map_lit_RV_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas map_lit_RV_nat_eq = HTHN.map_lit_RV_nat_eq_unfolded[unfolded case_lit_nat_def]
compile_nat map_lit_RV_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_lit_RV_nat by cook

lemmas map_acc_map_lit_RV_nat_eq = HTHN.map_acc_map_lit_RV_nat_eq_unfolded[unfolded
  case_list_nat_def]
compile_nat map_acc_map_lit_RV_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_acc_map_lit_RV_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction "HTHN.map_lit_RV :: 'a lit \<Rightarrow> _" _ _ arbitrary: s rule: HTHN.map_acc.induct)
  (cook mode = run_finish)

compile_nat HTHN.map_map_lit_RV_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_map_lit_RV_nat by cook

lemmas map_acc_map_map_lit_RV_nat_eq = HTHN.map_acc_map_map_lit_RV_nat_eq_unfolded[unfolded
  case_list_nat_def]
compile_nat map_acc_map_map_lit_RV_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_acc_map_map_lit_RV_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction "HTHN.map_map_lit_RV :: 'a lit list \<Rightarrow> _" _ _ arbitrary: s
    rule: HTHN.map_acc.induct)
  (cook mode = run_finish)

compile_nat HTHN.map_map_map_lit_RV_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_map_map_lit_RV_nat by cook

end

context HOL_To_HOL_Nat
begin

lemmas sat_to_at_most_three_sat_eq = sat_to_at_most_three_sat_def[unfolded map_eq_map_acc_nil,
  folded map_lit_RV_def map_eq_map_acc_nil map_map_lit_RV_def map_map_map_lit_RV_def]
function_compile_nat sat_to_at_most_three_sat_eq

end

context HOL_Nat_To_IMP_Minus
begin

compile_nat HTHN.sat_to_at_most_three_sat_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.sat_to_at_most_three_sat_nat by cook

end

end
