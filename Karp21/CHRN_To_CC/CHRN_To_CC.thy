theory CHRN_To_CC
  imports
    SAT_To_CLIQUE
    THREE_COL_To_CHRN
    Undirected_Graph_Theory.Undirected_Graphs_Root
begin

lemma sum_card_plus_one_ge_card:
  assumes "finite S"
    and fins: "\<forall>s\<in>S. finite s"
  shows "sum card S + 1 \<ge> card S"
proof -
  let ?S' = "S - {{}}"
  have "card s > 0" if "s \<in> ?S'" for s
    using that fins
    by (auto simp add: card_eq_0_iff)
  then have "sum card ?S' \<ge>  sum (\<lambda>_. 1::nat) ?S'"
    by (meson diff_is_0_eq diff_less less_one sum_mono)
  then have "sum card S  \<ge> card ?S'"
    by (metis Diff_subset assms(1) card_eq_sum sum.subset_diff trans_le_add2)
  then show ?thesis
    by (metis card_Diff_singleton_if le_diff_conv trans_le_add1)
qed

lemma partition_from_cover:
  assumes "finite S"  "\<Union>S = A"
  shows "\<exists>S'. (\<forall>s' \<in> S'. \<exists>s \<in> S. s' \<subseteq> s) \<and> disjoint S' \<and> \<Union>S' = A \<and> card S' \<le> card S"
  using assms
proof (induct S  arbitrary: A rule: finite_induct)
  case (insert x X)
  then obtain S' where S'_def: "(\<forall>s'\<in>S'. \<exists>a\<in>X. s' \<subseteq> a) \<and> disjoint S' \<and> \<Union> S' = \<Union> X
                             \<and> card S' \<le> card X"
    by fastforce
  let ?S' = "insert (x - \<Union>X) S'"
  have "(\<forall>s'\<in>?S'. \<exists>a\<in>(insert x X). s' \<subseteq> a) \<and> disjoint ?S' \<and> \<Union> ?S' = \<Union> (insert x X)"
    using S'_def unfolding disjoint_def by auto
  moreover have "card ?S' \<le> card (insert x X)"
    using insert S'_def
    by (simp add: card_insert_le_m1)
  ultimately show ?case
    using insert.prems by blast
qed(simp)

lemma subset_not_in_disjoint:
  assumes "A \<noteq> {}" "A \<subset> B" "B \<in> S" "disjoint S"
  shows "A \<notin> S"
  using assms disjointD by blast

lemma is_k_colorableI:
  assumes  "card c_Sets = k"
           "ugraph E"
           "\<Union> E = \<Union> c_Sets"
           "(\<forall>c\<in>c_Sets. \<forall>c'\<in>c_Sets. c \<noteq> c' \<longrightarrow> c \<inter> c' = {})"
           "(\<forall>c\<in>c_Sets. \<forall>v\<in>c. \<forall>v'\<in>c. {v, v'} \<notin> E)"
         shows "is_k_colorable E k c_Sets"
  using assms unfolding is_k_colorable_def is_colorable_def
  by blast

lemma one_more_color:
  assumes "is_k_colorable E k C_sets"
          "k  \<le> card (\<Union>E)"
  shows "\<exists>c. is_k_colorable E (k+1) c "
proof -
  obtain c_Sets where
    c_Sets_def: "card c_Sets = k"
                "ugraph E" "\<Union> E = \<Union> c_Sets"
                "\<forall>c\<in>c_Sets. \<forall>c'\<in>c_Sets. c \<noteq> c' \<longrightarrow> c \<inter> c' = {}"
                "(\<forall>c\<in>c_Sets. \<forall>v\<in>c. \<forall>v'\<in>c. {v, v'} \<notin> E)"
    using assms unfolding  is_k_colorable_def is_colorable_def
    by blast

  have fin: "finite c_Sets"
    using c_Sets_def
    by (metis \<open>ugraph E\<close> finite_UnionD ugraph_vertex_set_finite)
  show ?thesis
  proof (cases "{} \<in> c_Sets")
    case True
    have  "\<exists>c \<in> c_Sets. card c > 1"
    proof (rule ccontr)
      let ?c_Sets' = "c_Sets - {{}}"
      assume "\<not> (\<exists>c \<in> c_Sets. card c > 1)"
      then have "\<forall>c  \<in>  ?c_Sets'. card c = 1"
        by (metis DiffD1 Diff_insert_absorb One_nat_def Suc_lessI Union_upper
                  assms(2) c_Sets_def(1,3) card.remove card_gt_0_iff dual_order.strict_trans1 fin
                  finite_Int inf.absorb_iff2 mk_disjoint_insert zero_less_Suc)

      then have "sum card c_Sets = sum card ?c_Sets' + sum card {{}}"
        by (metis add.commute card_eq_0_iff finite.emptyI minus_nat.diff_0
                  plus_nat.add_0 sum.empty sum.insert_remove sum_diff1_nat)
      then have "sum card c_Sets = card ?c_Sets'"
        using \<open>\<forall>c\<in>c_Sets - {{}}. card c = 1\<close> by auto
      then have "sum card c_Sets < k"
        using card_Diff1_less[OF fin  True]
        by (auto simp add: \<open>card c_Sets = k\<close>[symmetric])
      moreover have "k \<le> sum card c_Sets"
        using card_Union_le_sum_card \<open>\<Union> E = \<Union> c_Sets\<close> \<open>k  \<le> card (\<Union>E)\<close>
        by (metis dual_order.trans)
      ultimately show False
        by auto
    qed
    then obtain c x where cx_def: "x \<in> c" "c \<in> c_Sets" "card c > 1" "c - {x} \<noteq> {}"
    by (metis card.empty card_Diff_singleton diff_is_0_eq elem_exists_non_empty_set leD
              less_numeral_extra(1) order_less_trans)

  let ?cs = "(c_Sets - {c}) \<union> {c - {x}, {x}}"
  have "c - {x} \<notin> c_Sets"
    using cx_def \<open>\<forall>c\<in>c_Sets. \<forall>c'\<in>c_Sets. c \<noteq> c' \<longrightarrow> c \<inter> c' = {}\<close>
    by(intro subset_not_in_disjoint[of _ c])(auto simp add: disjoint_def)
  moreover have "{x} \<notin> c_Sets"
    using cx_def \<open>\<forall>c\<in>c_Sets. \<forall>c'\<in>c_Sets. c \<noteq> c' \<longrightarrow> c \<inter> c' = {}\<close>
    by(intro subset_not_in_disjoint[of _ c])(auto simp add: disjoint_def)
  moreover have "card {c - {x}, {x}} = 2"
    using card_2_iff by auto
  ultimately have "card ?cs = k + 1"
   using fin \<open>card c_Sets = k\<close> card_Suc_Diff1[OF fin \<open>c \<in> c_Sets\<close>]
   by (intro card_Un_disjoint[THEN trans]) auto
  moreover have "{x} \<notin> E"
    using \<open>ugraph E\<close> unfolding ugraph_def by auto
  ultimately  show ?thesis
    using c_Sets_def cx_def ugraph_def card_2_iff
    by (intro exI[of _ ?cs] is_k_colorableI) (auto|force)
  next
    case False
    then have "is_k_colorable E (k+1) (insert {} c_Sets)"
       using c_Sets_def  card_insert_disjoint[OF fin]
       by (intro is_k_colorableI) auto
    then show ?thesis
      by blast
  qed
qed


lemma more_colors:
  assumes "is_k_colorable E k C_sets"
          "k'  \<le> card (\<Union>E) + 1"
          "k' \<ge> k"
        shows "\<exists>c. is_k_colorable E k' c "
  using assms
  by (induction k')
     (blast, metis Suc_eq_plus1 Suc_leD le_Suc_eq one_more_color)


definition clique_cover  where
  "clique_cover \<equiv> { ((V,E),l) |V E l. fin_ulgraph V E \<and> (\<exists>C. card C \<le> l \<and>
                           (\<forall>cl \<in> C. is_clique E cl) \<and>
                           \<Union> C = V)}"

lemma clique_cover_cert:
  assumes "card C \<le> l"
          "\<forall>cl \<in> C. is_clique E cl"
          "\<Union> C = V"
          "fin_ulgraph V E"
  shows "((V,E),l) \<in> clique_cover"
  unfolding clique_cover_def
  using assms by auto

lemma disjoint_clique_cover:
  assumes "((V,E),l) \<in> clique_cover"
  shows "\<exists>C. card C \<le> l \<and> disjoint C \<and>
                           (\<forall>cl \<in> C. is_clique E cl) \<and>
                           \<Union> C = V"
proof -
  obtain C where C_def: "card C \<le> l" "\<forall>cl \<in> C. is_clique E cl"
                           "\<Union> C = V" "fin_ulgraph V E"
    using assms unfolding clique_cover_def
    by blast
  have "finite C"
    using \<open>\<Union> C = V\<close> \<open>fin_ulgraph V E\<close> fin_graph_system.finV fin_ulgraph_def finite_UnionD
    by blast
  obtain S' where "(\<forall>s' \<in> S'. \<exists>s \<in> C. s' \<subseteq> s) \<and> disjoint S' \<and> \<Union>S' = V
                   \<and> card S' \<le> card C"
    by (metis C_def(3) \<open>finite C\<close> partition_from_cover)
  then show ?thesis using C_def
    unfolding is_clique_def
    by (intro exI[of _ S']) (auto, meson subset_iff)
qed


definition "MALFORMED_GRAPH \<equiv> ({},{{undefined}})"
definition chrn_to_cc  where
  "chrn_to_cc \<equiv> \<lambda>(E,k). if (\<forall>e\<in>E. card e = 2) \<and> k \<ge> 3 \<and> (k \<le> card (\<Union>E) + 1)
                        then ((\<Union>E, sgraph.complement_edges (\<Union>E) E), k)
                        else (MALFORMED_GRAPH,k)"

theorem chrn_to_cc_sound:
  assumes "(E,k) \<in> chromatic_number"
  shows "chrn_to_cc (E,k) \<in> clique_cover"
proof -
  obtain C_sets where C_sets_def:"is_k_colorable E k C_sets \<and> 3 \<le> k"
    using assms unfolding chromatic_number_def
    by blast
  have fin_UE: "finite (\<Union>E)"
      using C_sets_def ugraph_vertex_set_finite
      unfolding is_colorable_def is_k_colorable_def
      by force
  have card_e: "\<forall>e\<in>E. card e = 2"
    using assms unfolding is_k_colorable_def chromatic_number_def is_colorable_def ugraph_def
    by fast
  moreover{
    have "finite C_sets"
      using C_sets_def card.infinite unfolding is_k_colorable_def
      by fastforce
    moreover have "\<forall>s\<in>C_sets. finite s"
      using C_sets_def
      unfolding is_k_colorable_def is_colorable_def
      by (metis Union_upper fin_UE infinite_super)
    ultimately have "card C_sets \<le> sum card C_sets + 1"
      by (intro sum_card_plus_one_ge_card)
    moreover have "sum card C_sets = card (\<Union>E)"
      using C_sets_def
      unfolding is_k_colorable_def is_colorable_def
      by (simp add: \<open>\<forall>s\<in>C_sets. finite s\<close> card_Union_disjoint disjoint_def)
    ultimately have "k \<le> card (\<Union>E) + 1"
      using C_sets_def unfolding is_k_colorable_def
      by metis
  }
  moreover have "((\<Union>E, sgraph.complement_edges (\<Union>E) E), k) \<in> clique_cover"
  proof (intro clique_cover_cert[of C_sets])
    show "card C_sets \<le> k"
      by (metis C_sets_def is_k_colorable_def nle_le)
    have sg:"sgraph (\<Union>E) E"
      using C_sets_def
      unfolding is_k_colorable_def is_colorable_def ugraph_def
      by (unfold_locales) auto
    then show "\<forall>cl\<in>C_sets. is_clique (sgraph.complement_edges (\<Union> E) E) cl"
      using  C_sets_def
      unfolding is_clique_def sgraph.complement_edges_def[OF sg] ugraph_def
                all_edges_def is_k_colorable_def is_colorable_def
      by auto
    show "\<Union> C_sets = \<Union> E"
      using C_sets_def
      unfolding is_k_colorable_def is_colorable_def
      by auto
    show "fin_ulgraph (\<Union> E) (sgraph.complement_edges (\<Union> E) E)"
      using comp_sgraph.adj_to_edge_set_card_lim card_e fin_UE
      by (unfold_locales) (auto simp add: comp_sgraph.wellformed sg sgraph.complement_edges_def)
  qed
  ultimately show ?thesis
    using C_sets_def
    unfolding chrn_to_cc_def
    by auto
qed


theorem chrn_to_cc_complete:
  assumes "chrn_to_cc (E,k) \<in> clique_cover"
  shows "(E,k) \<in> chromatic_number"
proof (cases "(\<forall>e\<in>E. card e = 2) \<and> k \<ge> 3 \<and> k \<le> card (\<Union>E) + 1")
  case True
  have *: "chrn_to_cc (E,k) = ((\<Union>E,sgraph.complement_edges (\<Union> E) E),k)"
    using True  unfolding chrn_to_cc_def
    by force
  obtain C where
    "card C \<le> k"
    and cover:"\<forall>cl \<in> C. is_clique (sgraph.complement_edges (\<Union>E) E) cl"
    and "\<Union> C = \<Union>E"
    and "disjoint C"
    and fin: "fin_ulgraph (\<Union>E) (sgraph.complement_edges (\<Union>E) E)"
    using assms disjoint_clique_cover[of "\<Union>E" "sgraph.complement_edges (\<Union> E) E" k]
    unfolding  clique_cover_def *  by blast
  have *: "is_k_colorable E (card C) C"
  proof (intro is_k_colorableI)
    show  "ugraph E"
      using ugraph_def True fin fin_graph_system.finV fin_ulgraph_def finite_UnionD
      by fast
    have sg: "sgraph (\<Union>E) E"
      using True
      by (unfold_locales) auto
    show "\<forall>c \<in> C. \<forall>v \<in> c. \<forall>v' \<in> c. {v,v'} \<notin> E"
      using cover True
      unfolding is_clique_def all_edges_def sgraph.complement_edges_def[OF sg]
      by fastforce
    show "\<forall>c\<in>C. \<forall>c'\<in>C. c \<noteq> c' \<longrightarrow> c \<inter> c' = {}"
      using \<open>disjoint C\<close> disjointD by blast
  qed (use \<open>\<Union> C = \<Union>E\<close> in simp_all)

  then show ?thesis
    using True  more_colors \<open>card C \<le> k\<close> *
    unfolding chromatic_number_def
    by fast
next
  case False
  have "(MALFORMED_GRAPH,k) \<notin> clique_cover"
    unfolding MALFORMED_GRAPH_def clique_cover_def
              fin_ulgraph_def fin_graph_system_def graph_system_def
    by blast
  moreover have "chrn_to_cc (E,k) = (MALFORMED_GRAPH,k)"
    using False unfolding chrn_to_cc_def
    by force
  ultimately show ?thesis
    using assms False
    by auto
qed

theorem is_reduction_chrn_to_cc: "is_reduction chrn_to_cc chromatic_number clique_cover"
  unfolding is_reduction_def using chrn_to_cc_sound chrn_to_cc_complete by auto

end