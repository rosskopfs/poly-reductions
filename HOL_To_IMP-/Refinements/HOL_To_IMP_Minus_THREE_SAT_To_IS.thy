\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Nico Lintner"\<close>
theory HOL_To_IMP_Minus_THREE_SAT_To_IS
  imports
    HOL_To_IMP_Minus_SAT
    Karp21.THREE_SAT_To_IS_List
begin

context HOL_To_HOL_Nat
begin

definition "map_acc_rpair y \<equiv> map_acc (rpair y)"
lemmas map_acc_rpair_eq = map_acc_eq[of "rpair y" for y, folded map_acc_rpair_def]
function_compile_nat map_acc_rpair_eq

definition "case_prod_map_rpair \<equiv> \<lambda>(x, xs). map (rpair x) xs"
lemmas case_prod_map_rpair_eq = case_prod_map_rpair_def[unfolded map_eq_map_acc_nil,
    folded map_acc_rpair_def]
function_compile_nat case_prod_map_rpair_eq

definition "map_acc_case_prod_map_rpair \<equiv> map_acc case_prod_map_rpair"
lemmas map_acc_case_prod_map_rpair_eq = map_acc_eq[of "case_prod_map_rpair",
  folded map_acc_case_prod_map_rpair_def]
function_compile_nat map_acc_case_prod_map_rpair_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas map_acc_rpair_nat_eq = HTHN.map_acc_rpair_nat_eq_unfolded[unfolded case_list_nat_def]
compile_nat map_acc_rpair_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_acc_rpair_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction "HTHN.rpair y :: 'b \<Rightarrow> _" _ _ arbitrary: s rule: HTHN.map_acc.induct)
  (cook mode = run_finish)

lemmas case_prod_map_rpair_nat_eq = HTHN.case_prod_map_rpair_nat_eq_unfolded[unfolded
  case_prod_nat_def]
compile_nat case_prod_map_rpair_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.case_prod_map_rpair_nat by (cook mode = induction)

lemmas map_acc_case_prod_map_rpair_nat_eq =
  HTHN.map_acc_case_prod_map_rpair_nat_eq_unfolded[unfolded case_list_nat_def]
compile_nat map_acc_case_prod_map_rpair_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_acc_case_prod_map_rpair_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction "HTHN.case_prod_map_rpair :: ('a \<times> 'b list) \<Rightarrow> _" _ _ arbitrary: s
    rule: HTHN.map_acc.induct)
  (cook mode = run_finish)

end

context HOL_To_HOL_Nat
begin

definition "map_acc_product \<equiv> map_acc (\<lambda>x. List.product x x)"
lemmas map_acc_product_eq = map_acc_eq[of "\<lambda>x. List.product x x", folded map_acc_product_def]
function_compile_nat map_acc_product_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas map_acc_product_nat_eq = HTHN.map_acc_product_nat_eq_unfolded[unfolded case_list_nat_def]
compile_nat map_acc_product_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_acc_product_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction "\<lambda>x :: 'a list. List.product x x" _ _ arbitrary: s rule: HTHN.map_acc.induct)
  (cook mode = run_finish)

end

context HOL_To_HOL_Nat
begin
definition "prod_fsts_neq \<equiv> \<lambda>((a, _), (b, _)). a \<noteq> b"
function_compile_nat prod_fsts_neq_def

definition "filter_acc_prod_fsts_neq \<equiv> filter_acc prod_fsts_neq"
lemmas filter_prod_fsts_neq_acc_eq = filter_acc_eq[of prod_fsts_neq, folded
  filter_acc_prod_fsts_neq_def]
function_compile_nat filter_prod_fsts_neq_acc_eq

definition "filter_prod_fsts_neq \<equiv> filter prod_fsts_neq"
lemmas filter_prod_fsts_neq_eq = filter_prod_fsts_neq_def[unfolded filter_eq_filter_acc_nil,
  folded filter_acc_prod_fsts_neq_def]
function_compile_nat filter_prod_fsts_neq_eq

definition "map_acc_filter_prod_fsts_neq \<equiv> map_acc filter_prod_fsts_neq"
lemmas map_filter_prod_fsts_neq_acc_eq = map_acc_eq[of filter_prod_fsts_neq,
  folded map_acc_filter_prod_fsts_neq_def]
function_compile_nat map_filter_prod_fsts_neq_acc_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas prod_fsts_neq_nat_eq = HTHN.prod_fsts_neq_nat_eq_unfolded[unfolded case_prod_nat_def]
compile_nat prod_fsts_neq_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.prod_fsts_neq_nat by cook

lemmas filter_prod_fsts_neq_acc_nat_eq = HTHN.filter_acc_prod_fsts_neq_nat_eq_unfolded[unfolded
  case_bool_nat_def case_list_nat_def]
compile_nat filter_prod_fsts_neq_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.filter_acc_prod_fsts_neq_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction "HTHN.prod_fsts_neq :: ((('a \<times> 'b) \<times> ('a \<times> 'c)) \<Rightarrow> bool) " _ _ arbitrary: s
    rule: HTHN.filter_acc.induct)
  (cook mode = run_finish)

compile_nat HTHN.filter_prod_fsts_neq_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.filter_prod_fsts_neq_nat by cook

lemmas map_filter_prod_fsts_neq_acc_nat_eq = HTHN.map_acc_filter_prod_fsts_neq_nat_eq_unfolded
  [unfolded case_list_nat_def]
compile_nat map_filter_prod_fsts_neq_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_acc_filter_prod_fsts_neq_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction "HTHN.filter_prod_fsts_neq :: (('a \<times> 'b) \<times> 'a \<times> 'c) list \<Rightarrow> _" _ _ arbitrary: s
    rule: HTHN.map_acc.induct)
  (cook mode = run_finish)

end

context HOL_To_HOL_Nat
begin

definition "pair_list \<equiv> \<lambda>(a, b). [a, b]"
function_compile_nat pair_list_def

definition "map_acc_pair_list \<equiv> map_acc pair_list"
lemmas map_acc_pair_list_eq = map_acc_eq[of pair_list, folded map_acc_pair_list_def]
function_compile_nat map_acc_pair_list_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas pair_list_nat_eq = HTHN.pair_list_nat_eq_unfolded[unfolded case_prod_nat_def]
compile_nat pair_list_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.pair_list_nat by cook

lemmas map_acc_pair_list_nat_eq = HTHN.map_acc_pair_list_nat_eq_unfolded[unfolded
  case_list_nat_def]
compile_nat map_acc_pair_list_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_acc_pair_list_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction "HTHN.pair_list :: ('a \<times> 'a) \<Rightarrow> _" _ _ arbitrary: s rule: HTHN.map_acc.induct)
  (cook mode = run_finish)

end

context HOL_To_HOL_Nat
begin

definition "prod_product \<equiv> \<lambda>(a, b). List.product a b"
function_compile_nat prod_product_def

definition "map_acc_prod_product \<equiv> map_acc prod_product"
lemmas map_acc_prod_product_eq = map_acc_eq[of prod_product, folded map_acc_prod_product_def]
function_compile_nat map_acc_prod_product_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas prod_product_nat_eq = HTHN.prod_product_nat_eq_unfolded[unfolded case_prod_nat_def]
compile_nat prod_product_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.prod_product_nat by (cook mode = induction)

lemmas map_acc_prod_product_nat_eq = HTHN.map_acc_prod_product_nat_eq_unfolded[unfolded
  case_list_nat_def]
compile_nat map_acc_prod_product_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_acc_prod_product_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction "HTHN.prod_product :: 'a list \<times> 'b list \<Rightarrow> _" _ _ arbitrary: s
    rule: HTHN.map_acc.induct)
  (cook mode = run_finish)

end

context HOL_To_HOL_Nat
begin

case_of_simps conflict_lit_eq : conflict_lit.simps
function_compile_nat conflict_lit_eq

definition "prod_fsts_conflict_lit \<equiv> \<lambda>((a, _), (b, _)). conflict_lit a b"
lemma prod_fsts_conflict_lit_eq:
  "prod_fsts_conflict_lit x = conflict_lit (fst (fst x)) (fst (snd x))"
  unfolding prod_fsts_conflict_lit_def by auto
function_compile_nat prod_fsts_conflict_lit_eq

definition "filter_acc_prod_fsts_conflict_lit = filter_acc prod_fsts_conflict_lit"
lemmas filter_acc_prod_fsts_conflict_lit_eq = filter_acc_eq[
  of prod_fsts_conflict_lit, folded filter_acc_prod_fsts_conflict_lit_def]
function_compile_nat filter_acc_prod_fsts_conflict_lit_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas conflict_lit_nat_eq = HTHN.conflict_lit_nat_eq_unfolded[unfolded case_lit_nat_def]
compile_nat conflict_lit_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.conflict_lit_nat by cook

lemmas prod_fsts_conflict_lit_nat_eq = HTHN.prod_fsts_conflict_lit_nat_eq_unfolded[unfolded case_prod_nat_def]
compile_nat prod_fsts_conflict_lit_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.prod_fsts_conflict_lit_nat by cook

lemmas filter_acc_prod_fsts_conflict_lit_nat_eq =
  HTHN.filter_acc_prod_fsts_conflict_lit_nat_eq_unfolded[unfolded case_list_nat_def case_bool_nat_def]
compile_nat filter_acc_prod_fsts_conflict_lit_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.filter_acc_prod_fsts_conflict_lit_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction "HTHN.prod_fsts_conflict_lit :: ((('a lit \<times> 'b) \<times> ('a lit \<times> 'c)) \<Rightarrow> _) " _ _ arbitrary: s
    rule: HTHN.filter_acc.induct)
  (cook mode = run_finish)

end

context HOL_To_HOL_Nat
begin

lemmas sat_is_un_1_list_eq = sat_is_un_1_list_def[unfolded map_eq_map_acc_nil, folded
  map_acc_case_prod_map_rpair_def[unfolded case_prod_map_rpair_def rpair_def
    map_eq_map_acc_nil]
  map_acc_product_def
  map_acc_filter_prod_fsts_neq_def[unfolded filter_prod_fsts_neq_def prod_fsts_neq_def]
  map_acc_pair_list_def[unfolded pair_list_def]]
function_compile_nat sat_is_un_1_list_eq

lemmas sat_is_un_2_list_eq = sat_is_un_2_list_def[unfolded map_eq_map_acc_nil
  filter_eq_filter_acc_nil, folded
  map_acc_case_prod_map_rpair_def[unfolded case_prod_map_rpair_def rpair_def
    map_eq_map_acc_nil]
  map_acc_prod_product_def[unfolded prod_product_def]
  filter_acc_prod_fsts_conflict_lit_def[unfolded prod_fsts_conflict_lit_def]
  map_acc_pair_list_def[unfolded pair_list_def]]

function_compile_nat sat_is_un_2_list_eq

lemmas sat_is_list_eq = sat_is_list_def[unfolded list_length_eq_length]
function_compile_nat sat_is_list_eq

end

context HOL_Nat_To_IMP_Minus
begin

compile_nat HTHN.sat_is_un_1_list_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.sat_is_un_1_list_nat by cook

compile_nat HTHN.sat_is_un_2_list_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.sat_is_un_2_list_nat by cook

compile_nat HTHN.sat_is_list_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.sat_is_list_nat by cook

corollary sat_is_list_IMP_Minus_correct:
  assumes "Rel_nat (s ''sat_is_list_nat.args.x'') x"
  shows "terminates_with_res_IMP_Minus (tailcall_to_IMP_Minus sat_is_list_nat_IMP_tailcall) s
    ''sat_is_list_nat.ret'' (natify (sat_is_list x))"
proof -
  have "HTHN.sat_is_list_nat TYPE('a) (s ''sat_is_list_nat.args.x'') = natify (sat_is_list x)"
    using HTHN.sat_is_list_nat_eq_unfolded[OF assms]
      HTHN.Rel_nat_sat_is_list_nat_unfolded[OF assms]
    by (simp add: Rel_nat_iff_eq_natify)
  then show ?thesis using sat_is_list_nat_IMP_Minus_correct[of s, OF assms] by simp
qed

end

end
