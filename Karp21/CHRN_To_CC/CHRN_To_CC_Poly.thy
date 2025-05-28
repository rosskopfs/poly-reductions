theory CHRN_To_CC_Poly
  imports
    CHRN_To_CC
    Poly_Library
    Polynomial_Reductions
    Undirected_Graph_Theory.Undirected_Graphs_Root
begin

definition "mop_edge_set E ≡ SPECT [ ∀e ∈ E. card e = 2 ↦ card E ]"

definition "chrn_to_cc_poly ≡ λ(E, k). do {
  b ← mop_edge_set E;
  if b then do {
    V ← mop_set_Union E;
    b' ← mop_leq k (card V + 1);
    if b' ∧ k ≥ 3 then do {
      all_edges ← mop_all_edges V;
      s ← mop_set_diff all_edges E;
      RETURNT ((V, s), k)
    } else
      RETURNT (MALFORMED_GRAPH, k)
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

definition "size_CC ≡ (λ((V, E), k). card E + card V + nat_encoded_size k)"
definition "size_chrN ≡ (λ (E, k). card E + nat_encoded_size k)"

definition "chrn_to_cc_space n ≡ 2 * n + 4 * n * n"
definition "chrn_to_cc_time n ≡ 3 * n + 8 * n * n"

lemma chrn_to_cc_size: "size_CC (chrn_to_cc C) ≤ chrn_to_cc_space (size_chrN C)"
apply (cases C)
apply (simp add: chrn_to_cc_def size_CC_def chrn_to_cc_space_def)
apply (intro impI conjI)
subgoal for a b
proof -
  let ?A = "⋃ a"
  let ?card = "card ?A"
  let ?lb = "nat_encoded_size b"
  assume assm: "(∀e∈a. card e = 2) ∧ 3 ≤ b ∧ b ≤ Suc (card (⋃ a))"

  then have card_A: "?card ≤ 2 * card a"
    by (simp add: card_edges_union mult.commute)
  from assm have size_upper: "?lb ≤ Suc ?card" using nat_encoded_size_leq_self
    by (metis Suc_leD numeral_1_eq_Suc_0 numeral_3_eq_3 numerals(1) one_add_one order_trans plus_1_eq_Suc)
  from assm have size_lower: "1 ≤ ?lb" using nat_encoded_size_def
    by force

  then have "card (sgraph.complement_edges ?A a) + ?card ≤ card (sgraph.complement_edges ?A a) + ?card + ?lb"
    by linarith
  also have "... ≤ ((?card choose 2) - card a) + ?card + ?lb" using card_complement_edges
    by (metis order_mono_setup.refl)
  also have "... ≤ (?card choose 2) + ?card + ?lb" by force
  also have "... ≤ ?card * ?card + ?card + ?lb" using choose_2_upperbound by fastforce
  also have "... ≤ ?card * ?card + ?card + ?card + 1" using size_upper by linarith
  also have "... = (?card + 1) * (?card + 1)" by algebra
  also have "... ≤ (2 * card a + 1) * (2 * card a + 1)"
    using card_A add_le_mono1 mult_le_mono by presburger
  also have "... ≤ (4 * card a + 1) * (card a + 1)" by auto
  also have "... ≤ (4 * card a + ?lb) * (card a + ?lb)"
    using size_lower mult_le_mono nat_add_left_cancel_le by presburger
  also have "... ≤ (4 * card a + 4 * ?lb) * (card a + ?lb)" by fastforce
  finally show ?thesis
    by (simp add: size_chrN_def)
qed
by (simp add: MALFORMED_GRAPH_def nat_encoded_size_def size_chrN_def chrn_to_cc_space_def)

lemma chrn_to_cc_refines:
  "chrn_to_cc_poly C
  ≤ SPEC (λy. y = chrn_to_cc C) (λ_. chrn_to_cc_time (size_chrN C))"
unfolding SPEC_def chrn_to_cc_poly_def chrn_to_cc_def size_chrN_def chrn_to_cc_time_def
  mop_edge_set_def mop_set_Union_def mop_all_edges_def mop_leq_def mop_set_diff_def
apply(rule T_specifies_I)
apply(vcg' \<open>-\<close> rules: T_SPEC)
apply simp_all
subgoal for a b
proof -
  let ?A = "⋃ a"
  let ?card = "card ?A"
  let ?lb = "nat_encoded_size b"
  assume assms: "∀e∈a. card e = 2" "b ≤ Suc ?card ∧ 3 ≤ b"

  have finite: "finite ?A"
    using assms(2) not_less_eq_eq by fastforce
  have is_sgraph: "sgraph ?A a" using assms(1)
    unfolding sgraph_def graph_system_def sgraph_axioms_def by blast

  show ?thesis
  apply (rule conjI)
  apply (simp add: is_sgraph sgraph.complement_edges_def)
  subgoal
  proof -
    have card_all_edges: "card (all_edges ?A) ≤ card ?A * card ?A"
      by (simp add: finite card_all_edges choose_2_upperbound)
    have size_lower: "1 ≤ ?lb" using nat_encoded_size_def assms by force
    have card_A: "?card ≤ 2 * card a" using assms(1)
      by (simp add: card_edges_union mult.commute)
    then have card_aa: "?card * ?card ≤ 4 * card a * card a"
      using mult_le_mono by fastforce

    have "3 * card a + 1 + (?card * ?card + card (all_edges ?A))
        ≤ 3 * card a + 1 + (4 * card a * card a + card (all_edges ?A))"
      using card_aa by linarith
    also have "... ≤ 3 * card a + 1 + (8 * card a * card a)" using card_aa card_all_edges by linarith
    also have "... ≤ 3 * card a + 3 * ?lb + (8 * card a * card a)" using size_lower
      by linarith
    also have "... ≤ 3 * card a + 3 * ?lb + (8 * (card a + ?lb) * (card a + ?lb))"
      by (simp add: mult_le_mono)
    finally show ?thesis
      by (simp add: one_enat_def)
  qed
  done
qed
subgoal for a b
unfolding MALFORMED_GRAPH_def
by (smt (verit, ccfv_threshold) One_nat_def Suc_1 add_2_eq_Suc' add_Suc_right add_le_mono
  card_edges_union dual_order.trans min_def mult.commute nat_encoded_size_def not_less_eq_eq
  not_numeral_le_zero one_le_mult_iff trans_le_add2)
subgoal for a b
unfolding MALFORMED_GRAPH_def by blast

done

theorem chrn_to_cc_ispolyred:
  "ispolyred chrn_to_cc_poly chromatic_number clique_cover size_chrN size_CC"
unfolding ispolyred_def
apply(rule exI[where x=chrn_to_cc])
apply(rule exI[where x=chrn_to_cc_time])
apply(rule exI[where x=chrn_to_cc_space])
apply safe
  subgoal using chrn_to_cc_refines by blast
  subgoal using chrn_to_cc_size by blast
  subgoal unfolding poly_def chrn_to_cc_time_def apply(rule exI[where x=2]) by auto
  subgoal unfolding poly_def chrn_to_cc_space_def apply(rule exI[where x=2]) by auto
  subgoal using is_reduction_chrn_to_cc .
done

end
