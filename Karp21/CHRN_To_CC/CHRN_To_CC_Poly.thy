theory CHRN_To_CC_Poly
  imports
    CHRN_To_CC
    Poly_Library
    Polynomial_Reductions
    Undirected_Graph_Theory.Undirected_Graphs_Root
begin

definition "mop_edge_set E \<equiv> SPECT [ \<forall>e \<in> E. card e = 2 \<mapsto> card E ]"

definition "chrn_to_cc_poly \<equiv> \<lambda>(E, k). do {
  b \<leftarrow> mop_edge_set E;
  if b then do {
    V \<leftarrow> mop_set_Union E;
    b' \<leftarrow> mop_leq k (card V + 1);
    if b' \<and> k \<ge> 3 then do {
      all_edges \<leftarrow> mop_all_edges V;
      s \<leftarrow> mop_set_diff all_edges E;
      RETURNT ((V, s), k)
    } else
      RETURNT (MALFORMED_GRAPH, k)
  } else
    RETURNT (MALFORMED_GRAPH, k)
}"

lemma card_edges_union:
  assumes "\<forall> e \<in> E. card e = 2"
  shows "card (\<Union> E) \<le> card E * 2"
by (metis (mono_tags, lifting)
      assms card_Union_le_sum_card dual_order.trans nrest_image_bound order_mono_setup.refl)

lemma card_complement_edges: 
  assumes "\<forall>e \<in> E. card e = 2"
  and "finite E"
  shows "card (sgraph.complement_edges (\<Union> E) E) = (card (\<Union> E) choose 2) - card E"
proof -
  interpret sgraph "\<Union> E" E using assms by unfold_locales auto
  show ?thesis using card_Diff_subset card_all_edges complement_edges_def wellformed_all_edges assms
    by (metis bot_nat_0.not_eq_extremum card.infinite finite_Union zero_less_numeral)
qed

definition "size_CC \<equiv> (\<lambda>((V, E), k). card E + card V + nat_encoded_size k)"
definition "size_chrN \<equiv> (\<lambda> (E, k). card E + nat_encoded_size k)"

definition "chrn_to_cc_space n \<equiv> 2 * n + 4 * n * n"
definition "chrn_to_cc_time n \<equiv> 4 * n + 8 * n * n"

lemma chrn_to_cc_size: "size_CC (chrn_to_cc C) \<le> chrn_to_cc_space (size_chrN C)"
apply (cases C)
apply (simp add: chrn_to_cc_def size_CC_def chrn_to_cc_space_def)
apply (intro impI conjI)
subgoal for a b
proof -
  let ?A = "\<Union> a"
  let ?card = "card ?A"
  let ?lb = "nat_encoded_size b"
  assume assm: "(\<forall>e\<in>a. card e = 2) \<and> 3 \<le> b \<and> b \<le> Suc (card (\<Union> a))"

  then have card_A: "?card \<le> 2 * card a"
    by (simp add: card_edges_union mult.commute)
  from assm have size_upper: "?lb \<le> Suc ?card" using nat_encoded_size_leq_self
    by (metis Suc_leD numeral_1_eq_Suc_0 numeral_3_eq_3 numerals(1) one_add_one order_trans plus_1_eq_Suc)
  from assm have size_lower: "1 \<le> ?lb" using nat_encoded_size_def
    by force

  then have "card (sgraph.complement_edges ?A a) + ?card \<le> card (sgraph.complement_edges ?A a) + ?card + ?lb"
    by linarith
  also have "... \<le> ((?card choose 2) - card a) + ?card + ?lb" using card_complement_edges
    by (metis Suc_leD assm card.infinite card_A le_zero_eq mult_0_right not_less_eq_eq numeral_3_eq_3)
  also have "... \<le> (?card choose 2) + ?card + ?lb" by force
  also have "... \<le> ?card * ?card + ?card + ?lb" using choose_2_upperbound by fastforce
  also have "... \<le> ?card * ?card + ?card + ?card + 1" using size_upper by linarith
  also have "... = (?card + 1) * (?card + 1)" by algebra
  also have "... \<le> (2 * card a + 1) * (2 * card a + 1)"
    using card_A add_le_mono1 mult_le_mono by presburger
  also have "... \<le> (4 * card a + 1) * (card a + 1)" by auto
  also have "... \<le> (4 * card a + ?lb) * (card a + ?lb)"
    using size_lower mult_le_mono nat_add_left_cancel_le by presburger
  also have "... \<le> (4 * card a + 4 * ?lb) * (card a + ?lb)" by fastforce
  finally show ?thesis
    by (simp add: size_chrN_def)
qed
by (simp add: MALFORMED_GRAPH_def nat_encoded_size_def size_chrN_def chrn_to_cc_space_def)

lemma chrn_to_cc_refines:
  "chrn_to_cc_poly C
  \<le> SPEC (\<lambda>y. y = chrn_to_cc C) (\<lambda>_. chrn_to_cc_time (size_chrN C))"
unfolding SPEC_def chrn_to_cc_poly_def chrn_to_cc_def size_chrN_def chrn_to_cc_time_def
  mop_edge_set_def mop_set_Union_def mop_all_edges_def mop_leq_def mop_set_diff_def
apply(rule T_specifies_I)
apply(vcg' \<open>-\<close> rules: T_SPEC)
apply (simp_all add: one_enat_def)
subgoal for a b
proof -
  let ?A = "\<Union> a"
  let ?card = "card ?A"
  let ?lb = "nat_encoded_size b"
  assume assms: "\<forall>e\<in>a. card e = 2" "b \<le> Suc ?card \<and> 3 \<le> b"

  have finite: "finite ?A"
    using assms(2) not_less_eq_eq by fastforce
  have is_sgraph: "sgraph ?A a" using assms(1)
    unfolding sgraph_def graph_system_def sgraph_axioms_def by blast

  show ?thesis
  apply (rule conjI)
  apply (simp add: is_sgraph sgraph.complement_edges_def)
  subgoal
  proof -
    have card_all_edges: "card (all_edges ?A) \<le> card ?A * card ?A"
      by (simp add: finite card_all_edges choose_2_upperbound)
    have size_lower: "1 \<le> ?lb" using nat_encoded_size_def assms by force
    have card_A: "?card \<le> 2 * card a" using assms(1)
      by (simp add: card_edges_union mult.commute)
    then have card_aa: "?card * ?card \<le> 4 * card a * card a"
      using mult_le_mono by fastforce

    have "4 * card a + 1 + (?card * ?card + card (all_edges ?A))
        \<le> 4 * card a + 1 + (4 * card a * card a + card (all_edges ?A))"
      using card_aa by linarith
    also have "... \<le> 4 * card a + 1 + (8 * card a * card a)" using card_aa card_all_edges by linarith
    also have "... \<le> 4 * card a + 4 * ?lb + (8 * card a * card a)" using size_lower
      by linarith
    also have "... \<le> 4 * card a + 4 * ?lb + (8 * (card a + ?lb) * (card a + ?lb))"
      by (simp add: mult_le_mono)
    finally show ?thesis
      by (simp add: one_enat_def)
  qed
  done
qed
subgoal for a b
unfolding MALFORMED_GRAPH_def
  by (metis One_nat_def nat_encoded_size_def numeral_One one_le_mult_iff one_le_numeral trans_le_add2)
subgoal for a bcard_complement_edges
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
