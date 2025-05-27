\<^marker>\<open>creator "Nico Lintner"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
theory VC_Definition_List
  imports
    IS_Definition_List
    VC_Definition
begin

subsection \<open>List Representation of Vertex Cover\<close>

definition "is_vertex_cover_list E V \<equiv> \<forall>e \<in> set E. \<exists>v \<in> set V. v \<in> set e"

lemma rel_fun_is_vertex_cover_vertex_cover_list [transfer_rule]:
  "(Set_List_rel Set_List_rel_eq ===> Set_List_rel_eq ===> (=)) is_vertex_cover is_vertex_cover_list"
  unfolding is_vertex_cover_def is_vertex_cover_list_def by transfer_prover

definition "vertex_cover_pred_list E k \<equiv> ugraph_list E \<and> k \<le> list_card (concat E) \<and>
  (\<exists>V \<in> set (subseqs (concat E)). list_card V \<le> k \<and> is_vertex_cover_list E V)"

lemma rel_fun_is_vertex_cover_pred_vertex_cover_pred_list [transfer_rule]:
  "(Set_List_rel Set_List_rel_eq ===> (=) ===> (=)) vertex_cover_pred vertex_cover_pred_list"
  unfolding vertex_cover_pred_def vertex_cover_pred_list_def by transfer_prover

definition "vertex_cover_list \<equiv> {(E, k). vertex_cover_pred_list E k}"

lemma vertex_cover_pred_le_Domainp_Set_List_rel_Set_List_rel_eq:
  "(\<lambda>E. vertex_cover_pred E k) \<le> Domainp (Set_List_rel Set_List_rel_eq)"
  apply (intro predicate1I DomainPI, rule Set_List_rel_Set_List_rel_eq_transl_set_set_list_list_selfI)
  by auto

lemma vertex_cover_pred_list_le_Rangep_Set_List_rel_Set_List_rel_eq:
  "(\<lambda>E. vertex_cover_pred_list E k) \<le> Rangep (Set_List_rel Set_List_rel_eq)"
  using Set_List_rel_Set_List_rel_eq_transl_list_list_set_set_self by fastforce

lemma rel_set_vertex_cover_vertex_cover_list[transfer_rule]:
  "rel_set (rel_prod (Set_List_rel Set_List_rel_eq) (=)) vertex_cover vertex_cover_list"
  unfolding vertex_cover_def vertex_cover_list_def
  apply (intro rel_set_Collect_Collect_if_rel_fun_if_le_Rangep_if_le_Domainp
    case_prod_le_DomainpI vertex_cover_pred_le_Domainp_Set_List_rel_Set_List_rel_eq
    case_prod_le_RangepI vertex_cover_pred_list_le_Rangep_Set_List_rel_Set_List_rel_eq)
  by auto transfer_prover

end
