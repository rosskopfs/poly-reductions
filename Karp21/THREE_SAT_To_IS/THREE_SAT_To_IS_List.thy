\<^marker>\<open>creator "Nico Lintner"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
\<^marker>\<open>contributor "Lukas Stevens"\<close>
subsection \<open>Three Sat to Independent Set on Lists\<close>
theory THREE_SAT_To_IS_List
  imports
    IS_Definition_List
    THREE_SAT_To_IS
begin

subsubsection \<open>List Definition of @{term sat_is_un_1}\<close>

definition "sat_is_un_1_list F \<equiv>
  [[(l1, i), (l2, i)]. (i, C) \<leftarrow> enumerate 0 F, l1 \<leftarrow> C, l2 \<leftarrow> C, l1 \<noteq> l2]"

text \<open>@{term sat_is_un_1} is related to @{term sat_is_un_1_list}.\<close>

lemma rel_fun_sat_is_un_1_sat_is_un_1_list [transfer_rule]:
  "(list_all2 (Set_List_rel_eq) ===> Set_List_rel Set_List_rel_eq) sat_is_un_1 sat_is_un_1_list"
  unfolding sat_is_un_1_list_def sat_is_un_1_def
  apply transfer_prover_start
  apply transfer_step+
  by fastforce

subsubsection \<open>List Definition of @{term sat_is_un_2}\<close>

definition "sat_is_un_2_list F \<equiv>
  [[(l1, i), (l2, j)]. (i, Ci) \<leftarrow> enumerate 0 F, (j, Cj) \<leftarrow> enumerate 0 F,
    l1 \<leftarrow> Ci, l2 \<leftarrow> Cj, conflict_lit l1 l2]"

text \<open>@{term sat_is_un_2} is related to @{term sat_is_un_2_list}.\<close>

lemma rel_fun_sat_is_un_2_sat_is_un_2_list [transfer_rule]:
  "(list_all2 (Set_List_rel_eq) ===> Set_List_rel Set_List_rel_eq) sat_is_un_2 sat_is_un_2_list"
  unfolding sat_is_un_2_list_def sat_is_un_2_def
  apply transfer_prover_start
  apply transfer_step+
  by fastforce

subsubsection \<open>List Definition of @{term sat_is}\<close>

definition "sat_is_list F \<equiv> if is_n_sat_list 3 F
  then (sat_is_un_1_list F @ sat_is_un_2_list F, length F)
  else ([], 1)"

text \<open>@{term sat_is} is related to @{term sat_is_list}.\<close>

lemma sat_is_list_rel[transfer_rule]:
  "(list_all2 Set_List_rel_eq ===> (rel_prod (Set_List_rel Set_List_rel_eq) (=))) sat_is sat_is_list"
  unfolding sat_is_def sat_is_list_def
  by transfer_prover

subsection \<open>@{term sat_is_list} is a reduction from @{term three_sat_list} to
@{term independent_set_list}.\<close>

theorem is_reduction_sat_is_list: "is_reduction sat_is_list three_sat_list independent_set_list"
  unfolding three_sat_list_def independent_set_list_def
  using is_reduction_sat_is[unfolded three_sat_eq_Collect_three_sat_pred
    independent_set_eq_Collect_independent_set_pred] rel_fun_three_sat_pred_three_sat_list_pred
  apply (rule transfer_is_reduction_Collect)
  apply (transfer_prover, transfer_prover)
  by (fact list_all2_Set_List_rel_transl_list_list_list_set)

end
