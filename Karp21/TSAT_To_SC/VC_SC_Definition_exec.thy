theory VC_SC_Definition_exec
  imports VC_SC_Definition IS_Definition_exec
begin

subsection ‹list representation of vertex cover›

definition
  "is_vertex_cover_exec E V = list_all (\<lambda>e. list_ex (\<lambda>v. v ∈ set e) V) E"

definition
  "vertex_cover_pred_exec ≡ λ(E, k). ugraph_exec E ∧ k ≤ length (remdups (concat E)) ∧ 
    list_ex (λV. length (remdups V) ≤ k ∧ is_vertex_cover_exec E V) (subseqs (concat E))"

definition
  "vertex_cover_exec ≡ {E. vertex_cover_pred_exec E}"


subsection ‹‹vertex_cover› and ‹vertex_cover_exec› are related›

abbreviation
  "VC_List_rel ≡ IS_List_rel"
lemmas VC_List_rel_iff = IS_List_rel_iff

lemma is_vertex_cover_exec_rel[transfer_rule]:
    "(Set_List_rel Set_List_rel_eq ===> Set_List_rel_eq ===> (=)) is_vertex_cover is_vertex_cover_exec"
  unfolding is_vertex_cover_def is_vertex_cover_exec_def by transfer_prover

lemma vertex_cover_pred_exec_rel[transfer_rule]:
  "(VC_List_rel ===> (=)) vertex_cover_pred vertex_cover_pred_exec"
  unfolding VC_List_rel_iff vertex_cover_pred_def vertex_cover_pred_exec_def by transfer_prover

lemma vertex_cover_exec_rel[transfer_rule]: "rel_set VC_List_rel vertex_cover vertex_cover_exec"
  unfolding vertex_cover_unfold_pred vertex_cover_exec_def
proof (safe intro!: rel_setI, goal_cases)
  case (1 S k)
  with card_gt_0_iff have "finite S" "∀s \<in> S. finite s"
    unfolding vertex_cover_pred_def ugraph_def using card_gt_0_iff by fastforce+
  then obtain L where "S = set `  set L"
    by (metis (full_types) set_map ex_map_conv finite_list)
  then have [transfer_rule]: "VC_List_rel (S, k) (L, k)" by (auto simp: rel_set_def)
  moreover from 1 have "vertex_cover_pred_exec (L, k)" by transfer
  ultimately show ?case by blast
next
  case (2 L k)
  obtain S where "S = set ` set L" by blast
  then have [transfer_rule]: "VC_List_rel (S, k) (L, k)" by (auto simp: rel_set_def)
  moreover from 2 have "vertex_cover_pred (S, k)" by transfer
  ultimately show ?case by blast
qed

subsection ‹translating between list and set representations›

abbreviation
  "transl_VC_list_set ≡ transl_IS_list_set"

lemmas transl_VC_list_set_rel = transl_IS_list_set_rel



subsection ‹list representation of set cover›

definition
  "set_cover_pred_exec ≡ \<lambda>(T, k).
    \<exists>S \<in> Pow ((`) set ` set ` set T). ⋃ S = ⋃ ((`) set ` set ` set T) ∧ card S ≤ k"

definition
  "set_cover_exec ≡ {T. set_cover_pred_exec T}"


subsection ‹‹set_cover› and ‹set_cover_exec› are related›

definition
  "SC_List_rel ≡ rel_prod (Set_List_rel (Set_List_rel Set_List_rel_eq)) (=)"

lemma SC_List_relI[intro]:
  assumes "S = (`) set ` set ` set L"
  shows "SC_List_rel (S, k) (L, k)"
  unfolding SC_List_rel_def using assms by (auto simp: rel_set_def)

lemma SC_List_relE[elim]:
  assumes "SC_List_rel (S, k1) (L, k2)"
  obtains "S = (`) set ` set ` set L" "k1 = k2"
proof -
  have [dest]: "Set_List_rel (Set_List_rel_eq) S L ⟹ S = set ` set L" for S::"'a set set" and L::"'a list list"
    by (auto simp: rel_set_eq dest: rel_setD1 rel_setD2)
  assume "S = (`) set ` set ` set L ⟹ k1 = k2 ⟹ thesis"
  then show ?thesis using assms unfolding SC_List_rel_def rel_prod_inject
    by (fastforce dest: rel_setD1 rel_setD2)
qed

lemma SC_List_relD[dest]:
  assumes "SC_List_rel (S, k) (L, k)"
  obtains "S = (`) set ` set ` set L"
  using assms by (rule SC_List_relE)

lemma SC_List_rel_iff[simp]: "SC_List_rel = rel_prod (Set_List_rel (Set_List_rel Set_List_rel_eq)) (=)"
  unfolding SC_List_rel_def by simp

lemma set_cover_pred_exec_rel[transfer_rule]: "(SC_List_rel ===> (=)) set_cover_pred set_cover_pred_exec"
  unfolding SC_List_rel_iff set_cover_pred_def set_cover_pred_exec_def
  by (transfer_prover_start, transfer_step+) simp

end
