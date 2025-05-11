theory CHRN_To_CC_Poly
  imports
    CHRN_To_CC
    Poly_Library
    Polynomial_Reductions
    Undirected_Graph_Theory.Undirected_Graphs_Root
begin

definition "mop_union_set S k ≡ SPECT [ ⋃ S ↦ k * card S]"
definition "mop_edge_set E ≡ SPECT [ ∀e ∈ E. card e = 2 ↦ card E ]"

(* complement_edges V E = all_edges V - E ≡ card (V x V) - card E ≡ card V choose 2 - card E *)
definition "mop_complement_edges V E ≡ SPECT [ (sgraph.complement_edges V E) ↦ card V * card E ]"

definition "chrn_to_cc_poly ≡ λ(E, k). do {
  union ← mop_union_set E 2;
  b ← mop_edge_set E;
  if k ≤ card union + 1 ∧ k ≥ 3 ∧ b then do {
    s ← mop_complement_edges (union) E;
    RETURNT ((union, s), k)
  } else
    RETURNT (MALFORMED_GRAPH, k)
}"


lemma card_edges_union:
  assumes "∀ e ∈ E. card e = 2"
  shows "card (⋃ E) ≤ card E * 2"
by (metis (mono_tags, lifting) assms card_Union_le_sum_card dual_order.trans nrest_image_bound order_mono_setup.refl)

definition "size_CC ≡ (λ ((V, E), k). card E + card V + nat_encoded_size k)"
definition "size_chrN ≡ (λ (E, k). card E + nat_encoded_size k)"

find_theorems name: "complement_edges_def"

lemma
  assumes "∀ e ∈ E. card e = 2"
  shows "sgraph (⋃ E) E"
  unfolding sgraph_def graph_system_def sgraph_axioms_def
  using assms
by auto

find_theorems "card (?A - ?B)"
find_theorems "card (all_edges _)"
(* Undirected_Graph_Basics.card_all_edges: finite ?A ⟹ card (all_edges ?A) = card ?A choose 2 *)
(* Finite_Set.card_Diff_subset: finite ?B ⟹ ?B ⊆ ?A ⟹ card (?A - ?B) = card ?A - card ?B *)

lemma card_complement_edges:
  assumes "sgraph V E" and "finite V"
  shows "card (sgraph.complement_edges V E) = card V choose 2 - card E"
proof -
  have "sgraph.complement_edges V E = all_edges V - E"
    by (auto simp: assms sgraph.complement_edges_def)
  then have "card (sgraph.complement_edges V E) = card (all_edges V - E)"
    by presburger
  show ?thesis sorry
qed

(*
  2 * card E + (card E choose 2 - card E)
*)
definition "chrn_to_cc_space n ≡ 2 * n + n choose 2"

(*
  n : = card E + log k
  mop_union_set: 2 * card E
  mop_edge_set: card E
  mop_complement_edges: ??
*)
definition "chrn_to_cc_time n ≡ 2 * n + n" (* + TODO: *)

lemma chrn_to_cc_size: "size_CC (chrn_to_cc C) ≤ chrn_to_cc_space (size_chrN C)"
apply (auto simp: size_CC_def size_chrN_def chrn_to_cc_def chrn_to_cc_space_def)
apply (cases C; simp add: MALFORMED_GRAPH_def nat_encoded_size_def)
sorry

lemma chrn_to_cc_refines: "chrn_to_cc_poly C ≤ SPEC (λy. y = chrn_to_cc C) (λ_. chrn_to_cc_time (size_chrN C))"
sorry

theorem chrn_to_cc_ispolyred: "ispolyred chrn_to_cc_poly chromatic_number clique_cover size_chrN size_CC"
unfolding ispolyred_def
sorry

end
