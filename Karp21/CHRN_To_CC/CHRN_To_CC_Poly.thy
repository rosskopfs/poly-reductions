theory CHRN_To_CC_Poly
  imports
    CHRN_To_CC
    Poly_Library
    Polynomial_Reductions
    Undirected_Graph_Theory.Undirected_Graphs_Root
begin

definition "mop_union_set S k ≡ SPECT [ ⋃ S ↦ k * card S]"
definition "mop_edge_set E ≡ SPECT [ ∀e ∈ E. card e = 2 ↦ card E ]"

(* complement_edges V E = all_edges V - E = V × V - E :≡ card (V x V) - card E ≡ card V choose 2 - card E *)
(*
  res = {}
  for a in V {
    for b in V {
      // assume lookup and insertion constant
      if not {a, b} in E {
        res.insert({a, b})
      }
    }
  }
*)
definition "mop_complement_edges V E ≡
    SPECT [ (sgraph.complement_edges V E) ↦ card V * card V ]"

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
by (metis (mono_tags, lifting)
      assms card_Union_le_sum_card dual_order.trans nrest_image_bound order_mono_setup.refl)

lemma card_complement_edges: "card (sgraph.complement_edges V E) = (card V choose 2) - card E"
  by (metis card_Diff_subset card_all_edges finite_all_edges finite_subset
        sgraph.complement_edges_def sgraph.wellformed_all_edges)

definition "size_CC ≡ (λ ((V, E), k). card E + card V + nat_encoded_size k)"
definition "size_chrN ≡ (λ (E, k). card E + nat_encoded_size k)"

(* doubt i need this *)
lemma
  assumes "∀ e ∈ E. card e = 2"
  shows "sgraph (⋃ E) E"
  unfolding sgraph_def graph_system_def sgraph_axioms_def
  using assms
by auto

(*
  2 * card E + (card E choose 2 - card E)
*)
definition "chrn_to_cc_space n ≡ 2 * n + 4 * n * n"

(*
  n : = card E + log k
  mop_union_set: 2 * card E
  mop_edge_set: card E
  mop_complement_edges: (2 * card E) * (2 * card E)
*)
definition "chrn_to_cc_time n ≡ 2 * n + n + (4 * n * n)^2"

lemma chrn_to_cc_size: "size_CC (chrn_to_cc C) ≤ chrn_to_cc_space (size_chrN C)"
apply (auto simp: size_CC_def size_chrN_def chrn_to_cc_def chrn_to_cc_space_def)
apply (cases C; simp add: MALFORMED_GRAPH_def nat_encoded_size_def)
subgoal for a b
proof (rule impI)
  let ?A = "⋃ a"
  let ?card = "card ?A"
  let ?log = "floor_log b"

  assume assm: "(∀e∈a. card e = 2) ∧ 3 ≤ b ∧ b ≤ Suc ?card"

  from assm have card_A: "?card ≤ 2 * card a"
    by (simp add: card_edges_union mult.commute)

  have "card (sgraph.complement_edges ?A a) + ?card  = ((?card choose 2) - card a) + ?card"
    using card_complement_edges by metis
  also have "... ≤ (?card choose 2) + 2 * card a" using card_A card_complement_edges
    by linarith
  also have "... ≤ ?card * ?card + 2 * card a" using choose_2_upperbound
    by simp
  also have "... ≤ ((2 * card a) * (2 * card a)) + 2 * card a" using card_A mult_mono
    by fastforce
  also have "... = (4 * card a * card a) + 2 * card a" by auto
  also have "... ≤ (4 * (card a + ?log) * (card a)) + 2 * card a" by auto
  also have "... = 2 * card a + ((4 * card a + 4 * ?log) * card a)" by algebra
  also have "... ≤ 2 * card a + ((4 * card a + 4 * ?log) * (card a + ?log))" by fastforce
  also have "... ≤ 6 * card a + ((4 * card a + 4 * ?log) * (card a + ?log))" by fastforce
  also have "... ≤ 6 * card a + (4 + (4 * card a + 4 * ?log)) * (card a + ?log)" by auto
  finally show "card (sgraph.complement_edges ?A a) + ?card ≤
    5 * ?log +
    (5 + (6 * card a + (4 + (4 * card a + 4 * ?log)) * (card a + ?log)))"
    by linarith
qed
done

lemma chrn_to_cc_refines:
  "chrn_to_cc_poly C ≤ SPEC (λy. y = chrn_to_cc C) (λ_. chrn_to_cc_time (size_chrN C))"
sorry

theorem chrn_to_cc_ispolyred:
  "ispolyred chrn_to_cc_poly chromatic_number clique_cover size_chrN size_CC"
unfolding ispolyred_def
apply(rule exI[where x=chrn_to_cc])
apply(rule exI[where x=chrn_to_cc_time])
apply(rule exI[where x=chrn_to_cc_space])
apply safe
  subgoal using chrn_to_cc_refines by blast
  subgoal using chrn_to_cc_size by blast
  subgoal unfolding poly_def chrn_to_cc_time_def sorry
  subgoal unfolding poly_def chrn_to_cc_space_def apply(rule exI[where x=2]) by auto
  subgoal using is_reduction_chrn_to_cc .
done

end
