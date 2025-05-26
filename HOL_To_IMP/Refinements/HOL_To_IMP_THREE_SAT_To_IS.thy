\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Nico Lintner"\<close>
theory HOL_To_IMP_THREE_SAT_To_IS
  imports
    HOL_To_IMP_SAT
    Karp21.THREE_SAT_To_IS_List
begin

context HOL_To_HOL_Nat
begin       

lemmas sat_is_un_1_list_fo0_eq = sat_is_un_1_list_fo0_def[unfolded case_prod_unfold]
function_compile_nat sat_is_un_1_list_fo0_eq

definition "map_acc_sat_is_un_1_list_fo0 i_C l1 \<equiv> map_acc (sat_is_un_1_list_fo0 i_C l1)"
lemmas map_acc_sat_is_un_1_list_fo0_eq =
  map_acc_eq[of "sat_is_un_1_list_fo0 i_C l1" for i_C l1, folded map_acc_sat_is_un_1_list_fo0_def]  
function_compile_nat map_acc_sat_is_un_1_list_fo0_eq

lemmas sat_is_un_1_list_fo1_eq =
  sat_is_un_1_list_fo1_def[unfolded case_prod_unfold map_eq_map_acc_nil,
    folded map_acc_sat_is_un_1_list_fo0_def]
function_compile_nat sat_is_un_1_list_fo1_eq

definition "map_acc_sat_is_un_1_list_fo1 i_C \<equiv> map_acc (sat_is_un_1_list_fo1 i_C)"
lemmas map_acc_sat_is_un_1_list_fo1_eq =
  map_acc_eq[of "sat_is_un_1_list_fo1 i_C" for i_C, folded map_acc_sat_is_un_1_list_fo1_def]
function_compile_nat map_acc_sat_is_un_1_list_fo1_eq

lemmas sat_is_un_1_list_fo2_eq =
  sat_is_un_1_list_fo2_def[unfolded case_prod_unfold map_eq_map_acc_nil,
    folded map_acc_sat_is_un_1_list_fo1_def]
function_compile_nat sat_is_un_1_list_fo2_eq

definition "map_acc_sat_is_un_1_list_fo2 \<equiv> map_acc (sat_is_un_1_list_fo2)"
lemmas map_acc_sat_is_un_1_list_fo2_eq =
  map_acc_eq[of "sat_is_un_1_list_fo2", folded map_acc_sat_is_un_1_list_fo2_def]
function_compile_nat map_acc_sat_is_un_1_list_fo2_eq

lemmas sat_is_un_1_list_fo_eq =
  sat_is_un_1_list_fo_def[unfolded map_eq_map_acc_nil, folded map_acc_sat_is_un_1_list_fo2_def]
function_compile_nat sat_is_un_1_list_fo_eq

end

context HOL_Nat_To_IMP
begin

lemmas sat_is_un_1_list_fo0_nat_eq =
  HTHN.sat_is_un_1_list_fo0_nat_eq_unfolded[unfolded case_prod_nat_def]
compile_nat sat_is_un_1_list_fo0_nat_eq
HOL_To_IMP_correct HOL_To_HOL_Nat.sat_is_un_1_list_fo0_nat
  by cook

lemmas map_acc_sat_is_un_1_list_fo0_nat_eq =
  HTHN.map_acc_sat_is_un_1_list_fo0_nat_eq_unfolded[unfolded case_list_nat_def]
compile_nat map_acc_sat_is_un_1_list_fo0_nat_eq
HOL_To_IMP_correct HOL_To_HOL_Nat.map_acc_sat_is_un_1_list_fo0_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  apply(induction "sat_is_un_1_list_fo0 y ya" _ _ arbitrary: s rule: HTHN.map_acc.induct)
   apply(cook mode = run_finish)
  done

compile_nat HTHN.sat_is_un_1_list_fo1_nat_eq_unfolded
HOL_To_IMP_correct HOL_To_HOL_Nat.sat_is_un_1_list_fo1_nat
  by cook

lemmas map_acc_sat_is_un_1_list_fo1_nat_eq =
  HTHN.map_acc_sat_is_un_1_list_fo1_nat_eq_unfolded[unfolded case_list_nat_def]
compile_nat map_acc_sat_is_un_1_list_fo1_nat_eq
HOL_To_IMP_correct HOL_To_HOL_Nat.map_acc_sat_is_un_1_list_fo1_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  apply(induction "sat_is_un_1_list_fo1 y" _ _ arbitrary: s rule: HTHN.map_acc.induct)
   apply(cook mode = run_finish)
  done

compile_nat HTHN.sat_is_un_1_list_fo2_nat_eq_unfolded
HOL_To_IMP_correct HOL_To_HOL_Nat.sat_is_un_1_list_fo2_nat
  by cook

lemmas map_acc_sat_is_un_1_list_fo2_nat_eq =
  HTHN.map_acc_sat_is_un_1_list_fo2_nat_eq_unfolded[unfolded case_list_nat_def]
compile_nat map_acc_sat_is_un_1_list_fo2_nat_eq
HOL_To_IMP_correct HOL_To_HOL_Nat.map_acc_sat_is_un_1_list_fo2_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  apply(induction "sat_is_un_1_list_fo2 :: ('a \<times> 'b list) \<Rightarrow> _" _ _ arbitrary: s rule: HTHN.map_acc.induct)
   apply(cook mode = run_finish)
  done

compile_nat HTHN.sat_is_un_1_list_nat_eq_unfolded
HOL_To_IMP_correct HOL_To_HOL_Nat.sat_is_un_1_list_nat
  by cook

end

context HOL_To_HOL_Nat
begin

case_of_simps conflict_lit_eq : conflict_lit.simps
function_compile_nat conflict_lit_eq

lemmas sat_is_un_2_list_fo0_eq = sat_is_un_2_list_fo0_def[unfolded case_prod_unfold]
function_compile_nat sat_is_un_2_list_fo0_eq

definition "map_acc_sat_is_un_2_list_fo0 i_Ci j_Cj l1 \<equiv> map_acc (sat_is_un_2_list_fo0 i_Ci j_Cj l1)"
lemmas map_acc_sat_is_un_2_list_fo0_eq =                 
  map_acc_eq[of "sat_is_un_2_list_fo0 i_Ci j_Cj l1" for i_Ci j_Cj l1,
    folded map_acc_sat_is_un_2_list_fo0_def]  
function_compile_nat map_acc_sat_is_un_2_list_fo0_eq

lemmas sat_is_un_2_list_fo1_eq =
  sat_is_un_2_list_fo1_def[unfolded case_prod_unfold map_eq_map_acc_nil,
    folded map_acc_sat_is_un_2_list_fo0_def]
function_compile_nat sat_is_un_2_list_fo1_eq

definition "map_acc_sat_is_un_2_list_fo1 i_Ci j_Cj \<equiv> map_acc (sat_is_un_2_list_fo1 i_Ci j_Cj)"
lemmas map_acc_sat_is_un_2_list_fo1_eq =
  map_acc_eq[of "sat_is_un_2_list_fo1 i_Ci j_Cj" for i_Ci j_Cj, folded map_acc_sat_is_un_2_list_fo1_def]
function_compile_nat map_acc_sat_is_un_2_list_fo1_eq

lemmas sat_is_un_2_list_fo2_eq =
  sat_is_un_2_list_fo2_def[unfolded case_prod_unfold map_eq_map_acc_nil,
    folded map_acc_sat_is_un_2_list_fo1_def]
function_compile_nat sat_is_un_2_list_fo2_eq

definition "map_acc_sat_is_un_2_list_fo2 i_Ci \<equiv> map_acc (sat_is_un_2_list_fo2 i_Ci)"
lemmas map_acc_sat_is_un_2_list_fo2_eq =
  map_acc_eq[of "sat_is_un_2_list_fo2 i_Ci" for i_Ci, folded map_acc_sat_is_un_2_list_fo2_def]
function_compile_nat map_acc_sat_is_un_2_list_fo2_eq

lemmas sat_is_un_2_list_fo3_eq =
  sat_is_un_2_list_fo3_def[unfolded case_prod_unfold map_eq_map_acc_nil,
    folded map_acc_sat_is_un_2_list_fo2_def]
function_compile_nat sat_is_un_2_list_fo3_eq

definition "map_acc_sat_is_un_2_list_fo3 F \<equiv> map_acc (sat_is_un_2_list_fo3 F)"
lemmas map_acc_sat_is_un_2_list_fo3_eq =
  map_acc_eq[of "sat_is_un_2_list_fo3 F" for F, folded map_acc_sat_is_un_2_list_fo3_def]
function_compile_nat map_acc_sat_is_un_2_list_fo3_eq

lemmas sat_is_un_2_list_fo_eq =
  sat_is_un_2_list_fo_def[unfolded map_eq_map_acc_nil, folded map_acc_sat_is_un_2_list_fo3_def]
function_compile_nat sat_is_un_2_list_fo_eq


end

context HOL_Nat_To_IMP
begin

lemmas conflict_lit_nat_eq = HTHN.conflict_lit_nat_eq_unfolded[unfolded case_lit_nat_def]
compile_nat conflict_lit_nat_eq
HOL_To_IMP_correct HOL_To_HOL_Nat.conflict_lit_nat by cook

lemmas sat_is_un_2_list_fo0_nat_eq =
  HTHN.sat_is_un_2_list_fo0_nat_eq_unfolded[unfolded case_prod_nat_def]
compile_nat sat_is_un_2_list_fo0_nat_eq
HOL_To_IMP_correct HOL_To_HOL_Nat.sat_is_un_2_list_fo0_nat
  by cook

lemmas map_acc_sat_is_un_2_list_fo0_nat_eq =
  HTHN.map_acc_sat_is_un_2_list_fo0_nat_eq_unfolded[unfolded case_list_nat_def]
compile_nat map_acc_sat_is_un_2_list_fo0_nat_eq
HOL_To_IMP_correct HOL_To_HOL_Nat.map_acc_sat_is_un_2_list_fo0_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  apply(induction "sat_is_un_2_list_fo0 y ya yb" _ _ arbitrary: s rule: HTHN.map_acc.induct)
   apply(cook mode = run_finish)
  done

compile_nat HTHN.sat_is_un_2_list_fo1_nat_eq_unfolded
HOL_To_IMP_correct HOL_To_HOL_Nat.sat_is_un_2_list_fo1_nat
  by cook

lemmas map_acc_sat_is_un_2_list_fo1_nat_eq =
  HTHN.map_acc_sat_is_un_2_list_fo1_nat_eq_unfolded[unfolded case_list_nat_def]
compile_nat map_acc_sat_is_un_2_list_fo1_nat_eq
HOL_To_IMP_correct HOL_To_HOL_Nat.map_acc_sat_is_un_2_list_fo1_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  apply(induction "sat_is_un_2_list_fo1 y ya" _ _ arbitrary: s rule: HTHN.map_acc.induct)
   apply(cook mode = run_finish)
  done

compile_nat HTHN.sat_is_un_2_list_fo2_nat_eq_unfolded
HOL_To_IMP_correct HOL_To_HOL_Nat.sat_is_un_2_list_fo2_nat
  by cook

lemmas map_acc_sat_is_un_2_list_fo2_nat_eq =
  HTHN.map_acc_sat_is_un_2_list_fo2_nat_eq_unfolded[unfolded case_list_nat_def]
compile_nat map_acc_sat_is_un_2_list_fo2_nat_eq
HOL_To_IMP_correct HOL_To_HOL_Nat.map_acc_sat_is_un_2_list_fo2_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  apply(induction "sat_is_un_2_list_fo2 y" _ _ arbitrary: s rule: HTHN.map_acc.induct)
   apply(cook mode = run_finish)
  done

compile_nat HTHN.sat_is_un_2_list_fo3_nat_eq_unfolded
HOL_To_IMP_correct HOL_To_HOL_Nat.sat_is_un_2_list_fo3_nat
  by cook

lemmas map_acc_sat_is_un_2_list_fo3_nat_eq =
  HTHN.map_acc_sat_is_un_2_list_fo3_nat_eq_unfolded[unfolded case_list_nat_def]
compile_nat map_acc_sat_is_un_2_list_fo3_nat_eq
HOL_To_IMP_correct HOL_To_HOL_Nat.map_acc_sat_is_un_2_list_fo3_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  apply(induction "sat_is_un_2_list_fo3 y" _ _ arbitrary: s rule: HTHN.map_acc.induct)
   apply(cook mode = run_finish)
  done

compile_nat HTHN.sat_is_un_2_list_nat_eq_unfolded
HOL_To_IMP_correct HOL_To_HOL_Nat.sat_is_un_2_list_nat
  by cook

end

context HOL_To_HOL_Nat
begin

lemmas sat_is_list_eq = sat_is_list_def[unfolded list_length_eq_length]
function_compile_nat sat_is_list_eq

end

context HOL_Nat_To_IMP
begin

compile_nat HTHN.sat_is_list_nat_eq_unfolded
HOL_To_IMP_correct HOL_To_HOL_Nat.sat_is_list_nat by cook

corollary sat_is_list_IMP_correct:
  assumes [transfer_rule]: "Rel_nat (s ''sat_is_list_nat.arg.x'') x"
  shows "terminates_with_res_IMP (tailcall_to_IMP sat_is_list_nat_IMP_tailcall) s
    ''sat_is_list_nat.ret'' (natify (sat_is_list x))"
proof -
  have "Rel_nat (HTHN.sat_is_list_nat TYPE('a) (s ''sat_is_list_nat.arg.x'')) (sat_is_list x)"
    supply HTHN.sat_is_list_related_transfer[transfer_rule]
    by transfer_prover
  then show ?thesis
    unfolding Rel_nat_iff_eq_natify
    using sat_is_list_nat_IMP_correct[of s, OF assms] by simp
qed

end

end
