theory HOL_To_IMP_Minus_THREE_SAT_To_IS_List
  imports
    HOL_To_IMP_Minus_Lists
    Karp21.THREE_SAT_To_IS_List
begin

context HOL_To_HOL_Nat
begin

declare Rel_nat_selector_prod[Rel_nat]

definition "map_rpair_acc y \<equiv> map_acc (rpair y)"
lemmas map_rpair_acc_eq = map_acc_eq[of "rpair y" for y, folded map_rpair_acc_def]
function_compile_nat map_rpair_acc_eq

definition "case_prod_map_rpair \<equiv> \<lambda>(x, xs). map (rpair x) xs"
lemmas case_prod_map_rpair_eq = case_prod_map_rpair_def[unfolded map_eq_map_acc_nil,
    folded map_rpair_acc_def]
function_compile_nat case_prod_map_rpair_eq

definition "map_case_prod_map_rpair_acc \<equiv> map_acc case_prod_map_rpair"
lemmas map_case_prod_map_rpair_acc_eq = map_acc_eq[of "case_prod_map_rpair",
  folded map_case_prod_map_rpair_acc_def]
function_compile_nat map_case_prod_map_rpair_acc_eq

definition "map_case_prod_map_rpair \<equiv> map case_prod_map_rpair"
lemmas map_case_prod_map_rpair_eq = map_case_prod_map_rpair_def[unfolded map_eq_map_acc_nil,
    folded map_case_prod_map_rpair_acc_def]
function_compile_nat map_case_prod_map_rpair_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas map_rpair_acc_nat_eq = HTHN.map_rpair_acc_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat map_rpair_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_rpair_acc_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction "HTHN.rpair y :: 'b \<Rightarrow> _" _ _ arbitrary: s rule: HOL_To_HOL_Nat.map_acc.induct)
  (tactic \<open>HT.start_run_finish_case_tac HT.get_IMP_def HT.get_imp_minus_correct
    HB.get_HOL_eqs @{context} 1\<close>)+

lemmas case_prod_map_rpair_nat_eq = HTHN.case_prod_map_rpair_nat_eq_unfolded[simplified case_prod_nat_def]
compile_nat case_prod_map_rpair_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.case_prod_map_rpair_nat by (cook mode = induction)
                                                         
lemmas map_case_prod_map_rpair_acc_nat_eq =
  HTHN.map_case_prod_map_rpair_acc_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat map_case_prod_map_rpair_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_case_prod_map_rpair_acc_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction "HTHN.case_prod_map_rpair :: ('a \<times> 'b list) \<Rightarrow> _" _ _ arbitrary: s
    rule: HOL_To_HOL_Nat.map_acc.induct)
  (tactic \<open>HT.start_run_finish_case_tac HT.get_IMP_def HT.get_imp_minus_correct
    HB.get_HOL_eqs @{context} 1\<close>)+

lemmas map_case_prod_map_rpair_nat_eq = HTHN.map_case_prod_map_rpair_nat_eq_unfolded
compile_nat map_case_prod_map_rpair_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_case_prod_map_rpair_nat by cook

end

context HOL_To_HOL_Nat
begin

definition "map_product_acc \<equiv> map_acc (\<lambda>x. List.product x x)"
lemmas map_product_acc_eq = map_acc_eq[of "\<lambda>x. List.product x x", folded map_product_acc_def]
function_compile_nat map_product_acc_eq

definition "map_product \<equiv> map (\<lambda>x. List.product x x)"
lemmas map_product_eq = map_product_def[unfolded map_eq_map_acc_nil, folded map_product_acc_def]
function_compile_nat map_product_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas map_product_acc_nat_eq = HTHN.map_product_acc_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat map_product_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_product_acc_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction "\<lambda>x::'a list. List.product x x" _ _ arbitrary: s
    rule: HOL_To_HOL_Nat.map_acc.induct) 
  (tactic \<open>HT.start_run_finish_case_tac HT.get_IMP_def HT.get_imp_minus_correct
    HB.get_HOL_eqs @{context} 1\<close>)+

lemmas map_product_nat_eq = HTHN.map_product_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat map_product_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_product_nat by cook

end

context HOL_To_HOL_Nat
begin
definition "prod_fsts_neq \<equiv> \<lambda>((a, _), (b, _)). a \<noteq> b"
function_compile_nat prod_fsts_neq_def

definition "filter_prod_fsts_neq_acc \<equiv> filter_acc prod_fsts_neq"
lemmas filter_prod_fsts_neq_acc_eq = filter_acc_eq[of prod_fsts_neq, folded filter_prod_fsts_neq_acc_def,unfolded]
function_compile_nat filter_prod_fsts_neq_acc_eq

definition "filter_prod_fsts_neq \<equiv> filter prod_fsts_neq"
lemmas filter_prod_fsts_neq_eq = filter_prod_fsts_neq_def[unfolded filter_eq_filter_acc_nil, folded filter_prod_fsts_neq_acc_def]
function_compile_nat filter_prod_fsts_neq_eq

definition "map_filter_prod_fsts_neq_acc \<equiv> map_acc filter_prod_fsts_neq"
lemmas map_filter_prod_fsts_neq_acc_eq = map_acc_eq[of filter_prod_fsts_neq, folded map_filter_prod_fsts_neq_acc_def]
function_compile_nat map_filter_prod_fsts_neq_acc_eq

definition "map_filter_prod_fsts_neq = map filter_prod_fsts_neq"
lemmas map_filter_prod_fsts_neq_eq = map_filter_prod_fsts_neq_def[unfolded map_eq_map_acc_nil, folded map_filter_prod_fsts_neq_acc_def]
function_compile_nat map_filter_prod_fsts_neq_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas prod_fsts_neq_nat_eq = HTHN.prod_fsts_neq_nat_eq_unfolded[simplified]
compile_nat prod_fsts_neq_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.prod_fsts_neq_nat by cook


lemmas filter_prod_fsts_neq_acc_nat_eq = HTHN.filter_prod_fsts_neq_acc_nat_eq_unfolded[simplified case_bool_nat_def case_list_nat_def]
compile_nat filter_prod_fsts_neq_acc_nat_eq
thm HOL_To_HOL_Nat.filter_acc.induct
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.filter_prod_fsts_neq_acc_nat
    apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  apply (induction "HTHN.prod_fsts_neq :: ((('a \<times> 'b) \<times> ('a \<times> 'c)) \<Rightarrow> bool) " y ya arbitrary: s
    rule: HOL_To_HOL_Nat.filter_acc.induct)
  subgoal by (tactic \<open>HT.start_run_finish_case_tac HT.get_IMP_def HT.get_imp_minus_correct
    HB.get_HOL_eqs @{context} 1\<close>)
  subgoal for x xs acc s
    apply (cases "HTHN.prod_fsts_neq x")
    apply (tactic \<open>HT.start_case_tac HT.get_IMP_def @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 2\<close>)+
    apply (tactic \<open>HT.run_HOL_fun_tac HB.get_HOL_eqs @{context} 1\<close>)
    apply (tactic \<open>HT.run_HOL_fun_tac HB.get_HOL_eqs @{context} 2\<close>)
    apply (auto simp add: HOL_To_IMP_finish_simps)
    apply (tactic \<open>HT.finish_tail_tac @{context} 1\<close>)
    apply (tactic \<open>HT.finish_tail_tac @{context} 2\<close>)+
    sorry
  done

lemmas filter_prod_fsts_neq_nat_eq = HTHN.filter_prod_fsts_neq_nat_eq_unfolded
compile_nat filter_prod_fsts_neq_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.filter_prod_fsts_neq_nat by cook

lemmas map_filter_prod_fsts_neq_acc_nat_eq = HTHN.map_filter_prod_fsts_neq_acc_nat_eq_unfolded[simplified]
compile_nat map_filter_prod_fsts_neq_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_filter_prod_fsts_neq_acc_nat
      apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction "HTHN.filter_prod_fsts_neq :: (('a \<times> 'b) \<times> 'a \<times> 'c) list \<Rightarrow> _" y ya arbitrary: s
    rule: HOL_To_HOL_Nat.map_acc.induct)
  (tactic \<open>HT.start_run_finish_case_tac HT.get_IMP_def HT.get_imp_minus_correct
    HB.get_HOL_eqs @{context} 1\<close>)+

lemmas map_filter_prod_fsts_neq_nat_eq = HTHN.map_filter_prod_fsts_neq_nat_eq_unfolded
compile_nat map_filter_prod_fsts_neq_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_filter_prod_fsts_neq_nat by cook

end

context HOL_To_HOL_Nat
begin

definition "pair_list \<equiv> \<lambda>(a, b). [a, b]"
function_compile_nat pair_list_def

definition "map_pair_list_acc \<equiv> map_acc pair_list"
lemmas map_pair_list_acc_eq = map_acc_eq[of pair_list, folded map_pair_list_acc_def]
function_compile_nat map_pair_list_acc_eq

definition "map_pair_list \<equiv> map pair_list"
lemmas map_pair_list_eq = map_pair_list_def[unfolded map_eq_map_acc_nil, folded map_pair_list_acc_def]
function_compile_nat map_pair_list_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas pair_list_nat_eq = HTHN.pair_list_nat_eq_unfolded[simplified]
compile_nat pair_list_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.pair_list_nat by cook

lemmas map_pair_list_acc_nat_eq = HTHN.map_pair_list_acc_nat_eq_unfolded[simplified]
compile_nat map_pair_list_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_pair_list_acc_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction "HTHN.pair_list :: ('a \<times> 'a) \<Rightarrow> _" y ya arbitrary: s
    rule: HOL_To_HOL_Nat.map_acc.induct) 
  (tactic \<open>HT.start_run_finish_case_tac HT.get_IMP_def HT.get_imp_minus_correct
    HB.get_HOL_eqs @{context} 1\<close>)+

lemmas map_pair_list_nat_eq = HTHN.map_pair_list_nat_eq_unfolded
compile_nat map_pair_list_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_pair_list_nat by cook

end

context HOL_To_HOL_Nat
begin

definition "prod_product \<equiv> \<lambda>(a, b). List.product a b"
function_compile_nat prod_product_def

definition "map_prod_product_acc \<equiv> map_acc prod_product"
lemmas map_prod_product_acc_eq = map_acc_eq[of prod_product, folded map_prod_product_acc_def]
function_compile_nat map_prod_product_acc_eq

definition "map_prod_product \<equiv> map prod_product"
lemmas map_prod_product_eq = map_prod_product_def[unfolded map_eq_map_acc_nil,
    folded map_prod_product_acc_def]
function_compile_nat map_prod_product_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas prod_product_nat_eq = HTHN.prod_product_nat_eq_unfolded[simplified case_prod_nat_def]
compile_nat prod_product_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.prod_product_nat by (cook mode = induction)

lemmas map_prod_product_acc_nat_eq = HTHN.map_prod_product_acc_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat map_prod_product_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_prod_product_acc_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction "HTHN.prod_product :: 'a list \<times> 'b list \<Rightarrow> _" y ya arbitrary: s
    rule: HOL_To_HOL_Nat.map_acc.induct) 
   (tactic \<open>HT.start_run_finish_case_tac HT.get_IMP_def HT.get_imp_minus_correct
    HB.get_HOL_eqs @{context} 1\<close>)+

lemmas map_prod_product_nat_eq = HTHN.map_prod_product_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat map_prod_product_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_prod_product_nat by cook

end

datatype_compile_nat lit

context HOL_To_HOL_Nat
begin

declare conflict_lit.simps[simp del]
case_of_simps conflict_lit_eq : conflict_lit.simps
function_compile_nat conflict_lit_eq

definition "prod_fsts_conflict_lit \<equiv> \<lambda>((a, _), (b, _)). conflict_lit a b"
lemma prod_fsts_conflict_lit_eq: "prod_fsts_conflict_lit x = conflict_lit (fst (fst x)) (fst (snd x))"
  unfolding prod_fsts_conflict_lit_def by auto
function_compile_nat prod_fsts_conflict_lit_eq

definition "filter_prod_fsts_conflict_lit_acc = filter_acc prod_fsts_conflict_lit"
lemmas filter_prod_fsts_conflict_lit_acc_eq = filter_acc_eq[of prod_fsts_conflict_lit,
    folded filter_prod_fsts_conflict_lit_acc_def]
function_compile_nat filter_prod_fsts_conflict_lit_acc_eq
thm filter_prod_fsts_conflict_lit_acc_nat_eq_unfolded

definition "filter_prod_fsts_conflict_lit = filter prod_fsts_conflict_lit"
lemmas filter_prod_fsts_conflict_lit_eq = filter_prod_fsts_conflict_lit_def[unfolded filter_eq_filter_acc_nil,
    folded filter_prod_fsts_conflict_lit_acc_def]
function_compile_nat filter_prod_fsts_conflict_lit_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas conflict_lit_nat_eq = HTHN.conflict_lit_nat_eq_unfolded[simplified case_lit_nat_def]
compile_nat conflict_lit_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.conflict_lit_nat by cook

lemmas prod_fsts_conflict_lit_nat_eq = HTHN.prod_fsts_conflict_lit_nat_eq_unfolded[simplified case_prod_nat_def]
compile_nat prod_fsts_conflict_lit_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.prod_fsts_conflict_lit_nat by cook

lemmas filter_prod_fsts_conflict_lit_acc_nat_eq =
  HTHN.filter_prod_fsts_conflict_lit_acc_nat_eq_unfolded[simplified case_list_nat_def case_bool_nat_def]
compile_nat filter_prod_fsts_conflict_lit_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.filter_prod_fsts_conflict_lit_acc_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  apply (induction "HTHN.prod_fsts_conflict_lit :: ((('a lit \<times> 'b) \<times> ('a lit \<times> 'c)) \<Rightarrow> _) " y ya arbitrary: s
    rule: HOL_To_HOL_Nat.filter_acc.induct)
  subgoal by (tactic \<open>HT.start_run_finish_case_tac HT.get_IMP_def HT.get_imp_minus_correct
    HB.get_HOL_eqs @{context} 1\<close>)
  subgoal for x xs acc s
    apply (cases "HTHN.prod_fsts_conflict_lit x")
    apply (tactic \<open>HT.start_case_tac HT.get_IMP_def @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 2\<close>)+
    apply (tactic \<open>HT.run_HOL_fun_tac HB.get_HOL_eqs @{context} 1\<close>)
    apply (tactic \<open>HT.run_HOL_fun_tac HB.get_HOL_eqs @{context} 2\<close>)
    apply (auto simp add: HOL_To_IMP_finish_simps)
    apply (tactic \<open>HT.finish_tail_tac @{context} 1\<close>)
    apply (tactic \<open>HT.finish_tail_tac @{context} 2\<close>)+
    sorry
  done

lemmas filter_prod_fsts_conflict_lit_nat_eq =
  HTHN.filter_prod_fsts_conflict_lit_nat_eq_unfolded
compile_nat filter_prod_fsts_conflict_lit_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.filter_prod_fsts_conflict_lit_nat by cook

end

context HOL_To_HOL_Nat
begin

lemmas is_n_clause_list_eq = is_n_clause_list_def[unfolded is_n_clause_def,
    folded length_remdups_card_conv, unfolded list_length_eq_length]
function_compile_nat is_n_clause_list_eq

lemmas is_n_sat_list_eq = list_all_eq[of "is_n_clause_list n" for n,
    folded is_n_sat_list_def[unfolded Ball_set_list_all]]
function_compile_nat is_n_sat_list_eq

definition "is_3_sat_list F \<equiv> is_n_sat_list (Suc (Suc 1)) F"
lemmas is_3_sat_list_eq = list_all_eq[of "is_n_clause_list (Suc (Suc 1))",
    folded is_3_sat_list_def[unfolded is_n_sat_list_def Ball_set_list_all]]
function_compile_nat is_3_sat_list_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas is_n_clause_list_nat_eq = HTHN.is_n_clause_list_nat_eq_unfolded
compile_nat is_n_clause_list_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.is_n_clause_list_nat by cook

lemmas is_n_sat_list_nat_eq = HTHN.is_n_sat_list_nat_eq_unfolded[simplified case_list_nat_def case_bool_nat_def]
compile_nat is_n_sat_list_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.is_n_sat_list_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction ya arbitrary: s)
   (tactic \<open>HT.start_run_finish_case_tac HT.get_IMP_def HT.get_imp_minus_correct
    HB.get_HOL_eqs @{context} 1\<close>)+

lemmas is_3_sat_list_nat_eq = HTHN.is_3_sat_list_nat_eq_unfolded[simplified case_list_nat_def case_bool_nat_def]
compile_nat is_3_sat_list_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.is_3_sat_list_nat by cook
(* why does this work? *)

end

context HOL_To_HOL_Nat
begin

lemmas sat_is_un_1_list_eq = sat_is_un_1_list_def[folded
    map_case_prod_map_rpair_def[unfolded case_prod_map_rpair_def rpair_def]
    map_product_def
    map_filter_prod_fsts_neq_def[unfolded filter_prod_fsts_neq_def prod_fsts_neq_def]
    map_pair_list_def[unfolded pair_list_def]]
function_compile_nat sat_is_un_1_list_eq

lemmas sat_is_un_2_list_eq = sat_is_un_2_list_def[folded
    map_case_prod_map_rpair_def[unfolded case_prod_map_rpair_def rpair_def]
    map_prod_product_def[unfolded prod_product_def]
    filter_prod_fsts_conflict_lit_def[unfolded prod_fsts_conflict_lit_def]
    map_pair_list_def[unfolded pair_list_def]]
function_compile_nat sat_is_un_2_list_eq

lemma If_eq_case: "HOL.If = (\<lambda>b x y. (case b of True \<Rightarrow> x | False \<Rightarrow> y))"
  by (intro ext) simp
lemma "3_eq_Suc_Suc_1": "3 = Suc (Suc 1)" by simp
lemmas sat_is_list_eq = sat_is_list_def[unfolded list_length_eq_length "3_eq_Suc_Suc_1" If_eq_case, folded is_3_sat_list_def]
function_compile_nat sat_is_list_eq
print_theorems

end

context HOL_Nat_To_IMP_Minus
begin

lemmas sat_is_un_1_list_nat_eq = HTHN.sat_is_un_1_list_nat_eq_unfolded[simplified]
compile_nat sat_is_un_1_list_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.sat_is_un_1_list_nat by cook

lemmas sat_is_un_2_list_nat_eq = HTHN.sat_is_un_2_list_nat_eq_unfolded[simplified]
compile_nat sat_is_un_2_list_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.sat_is_un_2_list_nat by cook
thm case_bool_nat_def
lemmas sat_is_list_nat_eq = HTHN.sat_is_list_nat_eq_unfolded[
    simplified case_bool_nat_def]
compile_nat sat_is_list_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.sat_is_list_nat by cook

lemma sat_is_list_IMP_Minus_correct:
  assumes "Rel_nat (s ''sat_is_list_nat.args.x'') x"
  shows "terminates_with_res_IMP_Minus
     (tailcall_to_IMP_Minus sat_is_list_nat_IMP_tailcall) s
     ''sat_is_list_nat.ret''
     (natify (sat_is_list x))"
proof -
  have "HTHN.sat_is_list_nat TYPE('a) (s ''sat_is_list_nat.args.x'') = natify (sat_is_list x)"
    using HOL_To_HOL_Nat.sat_is_list_nat_eq_unfolded[OF assms]
      HOL_To_HOL_Nat.Rel_nat_sat_is_list_nat_unfolded[OF assms]
    by (simp add: Rel_nat_iff_eq_natify)
  then show ?thesis
    using sat_is_list_nat_IMP_Minus_correct[of s x, OF assms] by argo
qed

end

end
