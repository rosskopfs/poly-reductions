\<^marker>\<open>creator "Nico Lintner"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
subsection \<open>Independent Set To Vertex Cover on Lists\<close>
theory IS_To_VC_List
  imports
    IS_To_VC
    IS_Definition_List
    VC_Definition_List
begin

subsubsection \<open>List Definition of @{term is_vc}\<close>

definition "is_vc_list \<equiv> \<lambda>(E, k).
  if k > list_card (concat E) then (E, k) else (E, list_card (concat E) - k)"

text \<open>@{term is_vc} is related to @{term is_vc_list}.\<close>

lemma rel_is_vc_is_vc_list [transfer_rule]:
  "(rel_prod (Set_List_rel Set_List_rel_eq) (=) ===> rel_prod (Set_List_rel Set_List_rel_eq) (=))
    is_vc is_vc_list"
  unfolding is_vc_def is_vc_list_def by transfer_prover

theorem is_reduction_is_vc_list: "is_reduction is_vc_list independent_set_list vertex_cover_list"
proof -
  have 1:
    "rel_prod (Set_List_rel Set_List_rel_eq) (=) (transl_list_list_set_set (fst p), snd p) p" for p
    using Set_List_rel_Set_List_rel_eq_transl_list_list_set_set_self by (cases p) auto
  show ?thesis
  unfolding independent_set_list_def vertex_cover_list_def
  using is_reduction_is_vc[unfolded
    independent_set_eq_Collect_independent_set_pred
    vertex_cover_eq_Collect_vertex_cover_pred]
  apply (rule transfer_is_reduction_Collect)
  apply (transfer_prover, transfer_prover, transfer_prover)
  by (fact 1)
qed

end
