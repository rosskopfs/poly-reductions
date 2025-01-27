theory HC_To_UHC_2
  imports UHC_Definitions
begin

subsection\<open>\<open>HC_to_UHC\<close>: \<open>G \<in> UHC \<longrightarrow> G \<in> HC\<close>\<close>

subsubsection\<open>Preliminaries\<close>

lemma is_hc_impl_length_c:
  assumes "is_hc G c" "card (verts G) > 1"
  shows "length c \<ge> card (verts G)"
proof -
  have "verts G \<subseteq> set c"
    using assms
    unfolding is_hc_def
    by auto
  then show ?thesis
    using card_length card_list_subset le_trans by blast
qed

lemma hc_G_geq_2_verts_impl_arcs:
  assumes "card (verts G) > 1" "(arcs G = {})"
  shows "G \<notin> hc"
  using assms unfolding hc_def is_hc_def pre_digraph.cycle_def pre_digraph.awalk_def by auto


context
  fixes G assumes in_uhc: "hc_to_uhc G \<in> uhc"
  fixes G' assumes G'_def: "G' = hc_to_uhc G"
  fixes Cyc1 assumes Cyc1_def: "is_uhc G' Cyc1"
  fixes Cy2 assumes Cy2_def: "Cy2 = rev Cyc1"
  fixes C1' assumes C1'_def: "C1' = to_cycle_hc Cyc1"
  fixes C2 assumes C2_def: "C2 = to_cycle_hc Cy2"
begin

lemma G'_properties:
  shows "symmetric G'" "finite (verts G')" "wf_digraph G'"
  using G'_def in_uhc uhc_def by auto

lemma G_properties:
  shows "wf_digraph G" "((tail G = fst \<and> head G = snd) \<or> arcs G = {})"
proof -
  show "wf_digraph G"
  proof(rule ccontr)
    assume a1: "\<not> wf_digraph G"
    then have "G' = (let x = (SOME x. x \<in> arcs G) in \<lparr>verts = {}, arcs = {((head G x, 0),
    (head G x, 1))}, tail = fst, head = snd\<rparr>)"
      using G'_def
      by (simp add: hc_to_uhc_def)
    then have "G' \<notin> uhc"
      using a1 else_not_in_uhc_1
      by blast
    then show False
      using G'_def in_uhc
      by simp
  qed
next
  show "((tail G = fst \<and> head G = snd) \<or> arcs G = {})"
  proof(rule ccontr)
    assume a1: "\<not> ((tail G = fst \<and> head G = snd) \<or> arcs G = {})"
    then have "G' = (let x = (SOME x. x \<in> arcs G) in \<lparr>verts = {},
      arcs = {((head G x, 0), (head G x, 1))}, tail = fst, head = snd\<rparr>)"
      using G'_def
      by (simp add: a1 hc_to_uhc_def)
    then have "G' \<notin> uhc"
      using a1 else_not_in_uhc_2
      by blast
    then show False
      using G'_def in_uhc
      by simp
  qed
qed

lemma finite_verts_G:
  shows "finite (verts G)"
proof(rule ccontr)
  assume a1: "\<not> finite (verts G)"
  then have "G' = \<lparr>verts = {(v, 0)|v. v \<in> verts G}, arcs = {}, tail = fst, head = snd\<rparr>"
    using G'_def G_properties
    by (simp add: hc_to_uhc_def)
  then have "G' \<notin> uhc"
    using a1 else_not_in_uhc_3
    by blast
  then show False
    using G'_def in_uhc
    by simp
qed


context
  assumes verts_G: "card (verts G) > 1"
begin

lemma G'_def_3:
  shows "G' = \<lparr>verts = {(v, (0::nat))|v. v \<in> verts G} \<union> {(v, 1)|v. v \<in> verts G}
        \<union> {(v, 2)|v. v \<in> verts G},
      arcs = {((v, 0), (v, 1))|v. v \<in> verts G} \<union>{((v, 1), (v, 0))|v. v \<in> verts G}\<union>
          {((v, 1), (v, 2))|v. v \<in> verts G}\<union>{((v, 2), (v, 1))|v. v \<in> verts G}\<union>
          {((v, 2), (u, 0))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e \<and> u \<noteq> v}\<union>
          {((u, 0), (v, 2))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e \<and> u \<noteq> v},
      tail = fst, head = snd\<rparr>"
  using G_properties G'_def verts_G
  by(auto simp add: hc_to_uhc_def)


lemma head_tail_G':
  shows "head G' = snd" "tail G' = fst"
  using G'_def_3
  by simp+


lemma is_uhc_lenght_Cycle_approx:
  assumes "is_uhc G' Cycle"  "card (verts G') > 1"
  shows "length Cycle \<ge> card (verts G')"
proof -
  have "\<forall>x \<in> verts G'. x \<in> set Cycle"
    using assms is_uhc_def
    by force
  then have "card (set Cycle) \<ge> card (verts G')"
    by (simp add: card_list_subset subsetI)
  then show ?thesis
    using card_length le_trans
    by blast
qed


lemma hd_pre_digraph_cas:
  assumes "pre_digraph.cas G' u (p) v" "p\<noteq> []"
  shows "fst (hd p) = u"
  using assms head_tail_G'
  by(induction p arbitrary: u)(auto simp add: pre_digraph.cas.simps)


lemma last_pre_digraph_cas:
  assumes "pre_digraph.cas G' u (p) v" "p\<noteq> []"
  shows "snd (last p) = v"
  using assms head_tail_G'
  by(induction p arbitrary: u)(auto simp add: pre_digraph.cas.simps)


lemma hd_last_C_G':
  assumes "is_uhc G' Cycle" "card (verts G') > 1"
  shows "hd Cycle = last Cycle"
  using assms
  unfolding is_uhc_def vwalk_cycle_def
  by fastforce


lemma is_uhc_impl_is_uhc_rev:
  assumes "is_uhc G' C"
  shows "is_uhc G' (rev C)"
proof -
  have "set C \<subseteq> verts G'"
    using assms is_uhc_def
    by fast
  then have 1: "set (rev C) \<subseteq> verts G'"
    by simp
  then show ?thesis
  proof(cases "card (verts G') \<le> 1")
    case True
    then show ?thesis
      using 1
      unfolding is_uhc_def
      by blast
  next
    case False
    then have a1: "card (verts G') > 1"
      by simp
    then have "hd C = last C" "distinct (tl C)"
      using assms is_uhc_def hd_last_C_G' assms False
      by auto
    then have 2: "distinct (tl (rev C))"
      using distinct_tl_rev_C
      by auto
    have "(\<forall>x\<in>verts G'. x \<in> set (C))"
      using assms is_uhc_def False
      by fast
    then have 3: "(\<forall>x\<in>verts G'. x \<in> set (rev C))"
      by simp
    have "vwalk_cycle G' C"
      using False is_uhc_def assms
      by blast
    then have "vwalk_cycle G' (rev C)"
      by (simp add: G'_properties(1) vwalk_cycle_rev)
    then show ?thesis
      using 1 2 3
      unfolding is_uhc_def
      by blast
  qed
qed


lemma uhc_Cy2:
  shows "is_uhc G' Cy2"
  using is_uhc_impl_is_uhc_rev Cy2_def Cyc1_def
  by simp


lemma verts_G_G':
  assumes "x \<in> verts G"
  shows "(x, 0) \<in> verts G'"  "(x, 1) \<in> verts G'"  "(x, 2) \<in> verts G'"
  using G'_def_3 assms
  by auto


lemma card_verts_G_G':
  shows "card (verts G') > 1"
  by (metis (no_types, opaque_lifting) G'_properties(2) verts_G card_greater_1_contains_two_elements
      contains_two_card_greater_1 prod.inject verts_G_G'(2))


lemma hd_last_Cyc1:
  shows "hd Cyc1 = last Cyc1"
  using verts_G card_verts_G_G' Cyc1_def hd_last_C_G'
  by blast


lemma distinct_tl_Cyc1:
  shows "distinct (tl Cyc1)"
  using verts_G Cyc1_def card_verts_G_G' is_uhc_def leD
  by blast


subsubsection\<open>Proof of theorem for specific cycle\<close>
text\<open>There are some lemmas taking care of cases where the cycle does not end
  with \<open>(x,2)\<close> or \<open>(x,0)\<close> for the reverse case, but with some other number. These cases
  blow up the paragraph.\<close>

context
  fixes Cy1 assumes Cy1_def: "is_uhc G' Cy1"
  fixes C1 assumes C1_def: "C1 = to_cycle_hc Cy1"
begin

lemma hd_last_Cy1:
  shows "hd Cy1 = last Cy1"
  using verts_G card_verts_G_G' Cy1_def hd_last_C_G'
  by blast


lemma distinct_tl_Cy1:
  shows "distinct (tl Cy1)"
  using verts_G Cy1_def card_verts_G_G' is_uhc_def leD
  by blast


lemma x_inG_x_i_in_Cy1:
  assumes "x \<in> verts G"
  shows "(x, 0) \<in> set Cy1"  "(x, 1) \<in> set Cy1"  "(x, 2) \<in> set Cy1"
  using assms Cy1_def card_verts_G_G' verts_G_G'
  unfolding is_uhc_def
  by auto


lemma length_Cy1:
  shows "length Cy1 \<ge> 2" "length Cy1 > 1"
proof -
  have "length Cy1 > 1"
    using verts_G card_verts_G_G' Cy1_def is_uhc_lenght_Cycle_approx
    by fastforce
  then show "length Cy1 > 1" "length Cy1 \<ge> 2"
    by auto
qed


lemma arcs_ends_G':
  shows "arcs_ends G' = arcs G'"
  by (simp add: Graph_Auxiliaries.arcs_ends_G' local.head_tail_G')


lemma sublist_Cy1_arcs_G':
  assumes "sublist [a, b] Cy1"
  shows "(a, b) \<in> arcs G'"
proof -
  have 1: "(a, b) \<in> set (vwalk_arcs Cy1)"
    using assms
    by (simp add: vwalk_sublist_in_arcs)
   have "set (vwalk_arcs Cy1) \<subseteq> arcs G'"
    using Cy1_def assms is_uhc_def arcs_ends_G' card_verts_G_G'
    unfolding vwalk_cycle_def  is_uhc_def
    by fastforce
  then show ?thesis
    using 1
    by auto
qed


lemma pre_1_edge:
  assumes "sublist [y, (x, 1)] Cy1"
  shows "y = (x, 0) \<or> y = (x, 2)"
proof -
  have "(y, (x, 1)) \<in> arcs G'"
    using assms sublist_Cy1_arcs_G'
    by simp
  then show ?thesis using G'_def_3
    by(auto)
qed


lemma pre_0_edges_helper:
  assumes "((x, 2), (y, 0)) \<in> arcs G'"
  shows "(x, y) \<in> arcs G"
  using assms G_properties G'_def_3
  by(auto)


lemma pre_0_edge:
  assumes "sublist [y, (x, 0)] Cy1"
  shows "y = (x, 1) \<or> (\<exists>z. y = (z, 2) \<and> (z, x) \<in> arcs G)"
proof -
  have y_in: "y \<in> verts G'"
    using assms
    by (metis G'_properties(3) local.arcs_ends_G' sublist_Cy1_arcs_G' wf_digraph.adj_in_verts(1))
  then obtain a b where ab_def: "(a, b) = y"
    using G'_def_3
    by auto
  then have 1: "b = 0 \<or> b = 1 \<or> b = 2"
    using y_in G'_def_3
    by force
  have "(y, (x, 0)) \<in> arcs G'"
    using assms sublist_Cy1_arcs_G'
    by auto
  then show ?thesis
  proof(cases "b = 0" )
    case True
    then have "((a, 0), (x, 0)) \<notin> arcs G'"
      using G'_def_3
      by simp
    then show ?thesis
      using True \<open>(y, x, 0) \<in> arcs G'\<close> ab_def
      by auto
  next
    case False
    then have 2: "b = 1 \<or> b = 2"
      using 1 by simp
    then show ?thesis
    proof(cases "b = 1")
      case True
      then have "((a, 1), (x, 0)) \<in> arcs G'"
        using ab_def
        by (simp add: \<open>(y, x, 0) \<in> arcs G'\<close>)
      then have "a = x"
        using G'_def_3
        by simp
      then show ?thesis using ab_def True
        by simp
    next
      case False
      then have 3: "b = 2"
        using 2
        by auto
      then have "((a, 2), (x, 0)) \<in> arcs G'"
        using ab_def
        by (simp add: \<open>(y, x, 0) \<in> arcs G'\<close>)
      then have "(a, x) \<in> arcs G"
        using pre_0_edges_helper assms
        by blast
      then show ?thesis
        using ab_def 3
        by(auto)
    qed
  qed
qed


lemma pre_2_edges_helper:
  assumes "((x, 0), (y, 2)) \<in> arcs G'" "card (verts G) > 1"
  shows "(y, x) \<in> arcs G"
  using assms G_properties G'_def_3
  by(auto)


lemma post_0_edge:
  assumes "sublist [(x, 0), y] Cy1" "card (verts G) > 1"
  shows "y = (x, 1) \<or>(\<exists>z. y = (z, 2) \<and> (z, x) \<in> arcs G)"
proof -
  have y_in: "y \<in> verts G'"
    using assms
    by (metis G'_properties(3) local.arcs_ends_G' sublist_Cy1_arcs_G' wf_digraph.adj_in_verts(2))
  then obtain a b where ab_def: "(a, b) = y"
    using G'_def_3 by auto
  then have 1: "b = 0 \<or> b = 1 \<or> b = 2"
    using y_in G'_def_3
    by force
  have in_arcs: "((x, 0), y) \<in> arcs G'"
    using assms sublist_Cy1_arcs_G'
    by auto
  then show ?thesis
  proof(cases "b = 0" )
    case True
    then have "((x, 0), (a, 0)) \<notin> arcs G'"
      using G'_def_3
      by simp
    then show ?thesis
      using True \<open>((x, 0), y) \<in> arcs G'\<close> ab_def
      by auto
  next
    case False
    then have 2: "b = 1 \<or> b = 2"
      using 1 by simp
    then show ?thesis
    proof(cases "b = 1")
      case True
      then have "((x, 0), (a, 1)) \<in> arcs G'"
        using ab_def
        by (simp add: in_arcs)
      then have "a = x"
        using G'_def_3
        by simp
      then show ?thesis using ab_def True
        by simp
    next
      case False
      then have 3: "b = 2"
        using 2
        by auto
      then have "((x, 0), (a, 2)) \<in> arcs G'"
        using ab_def
        by (simp add: in_arcs)
      then have "(a, x) \<in> arcs G"
        using pre_2_edges_helper assms
        by blast
      then show ?thesis
        using ab_def 3
        by(auto)
    qed
  qed
qed


lemma post_2_edge:
  assumes "sublist [(x, 2), y] Cy1" "card (verts G) > 1"
  shows "y = (x, 1) \<or> (\<exists>z. y = (z, 0) \<and> (x, z) \<in> arcs G)"
proof -
  have y_in: "y \<in> verts G'"
    using assms
    by (metis G'_properties(3) local.arcs_ends_G' sublist_Cy1_arcs_G' wf_digraph.adj_in_verts(2))
  then obtain a b where ab_def: "(a, b) = y"
    using G'_def_3
    by auto
  then have 1: "b = 0 \<or> b = 1 \<or> b = 2"
    using y_in G'_def_3
    by force
  have in_arcs: "((x, 2), y) \<in> arcs G'"
    using assms sublist_Cy1_arcs_G' by auto
  then show ?thesis
  proof(cases "b = 2" )
    case True
    then have "((x, 2), (a, 2)) \<notin> arcs G'"
      using G'_def_3
      by simp
    then show ?thesis
      using True in_arcs ab_def
      by auto
  next
    case False
    then have 2: "b = 0 \<or> b = 1"
      using 1 by simp
    then show ?thesis
    proof(cases "b = 1")
      case True
      then have "((x, 2), (a, 1)) \<in> arcs G'"
        using ab_def
        by (simp add: in_arcs)
      then have "a = x"
        using G'_def_3
        by simp
      then show ?thesis
        using ab_def True
        by simp
    next
      case False
      then have 3: "b = 0"
        using 2
        by auto
      then have "((x, 2), (a, 0)) \<in> arcs G'"
        using ab_def
        by (simp add: in_arcs)
      then have "(x, a) \<in> arcs G"
        using pre_0_edges_helper assms
        by blast
      then show ?thesis
        using ab_def 3
        by(auto)
    qed
  qed
qed


lemma post_1_edge:
  assumes "sublist [(x, 1), y] Cy1"
  shows "y = (x, 0) \<or> y = (x, 2)"
proof -
  have "((x, 1), y) \<in> arcs G'"
    using assms sublist_Cy1_arcs_G'
    by simp
  then show ?thesis
    using G'_def_3
    by(auto)
qed


lemma pre_1_cycle:
  assumes "x \<in> verts G"
  shows "(sublist [(x, 0), (x, 1)] Cy1) \<or> sublist [(x, 2), (x, 1)] Cy1"
proof -
  have 0: "length Cy1 \<ge> 2"
    using assms length_Cy1
    by auto
  have "(x, 1) \<in> set Cy1"
    using assms x_inG_x_i_in_Cy1 by simp
  then have "\<exists>y. sublist [y, (x, 1)] Cy1"
    using 0 hd_last_Cy1 assms
    by (meson List_Auxiliaries.b_in_Cycle_exists_sublist)
  then obtain y where y_def: "sublist [y, (x, 1)] Cy1"
    by blast
  then show ?thesis
    using pre_1_edge assms
    by blast
qed


lemma pre_0_cycle:
  assumes "x \<in> verts G"
  shows "(sublist [(x, 1), (x, 0)] Cy1) \<or> (\<exists>z. sublist [(z, 2), (x, 0)] Cy1 \<and> (z, x) \<in> arcs G)"
proof -
  have 0: "length Cy1 \<ge> 2"
    using assms length_Cy1
    by auto
  have "(x, 0) \<in> set Cy1"
    using assms x_inG_x_i_in_Cy1
    by simp
  then have "\<exists>y. sublist [y, (x, 0)] Cy1"
    using 0 hd_last_Cy1 assms
    by (meson List_Auxiliaries.b_in_Cycle_exists_sublist)
  then obtain y where y_def: "sublist [y, (x, 0)] Cy1"
    by blast
  then show ?thesis
    using pre_0_edge assms
    by blast
qed


lemma post_2_cycle:
  assumes "x \<in> verts G"
  shows "sublist [(x, 2), (x, 1)] Cy1 \<or> (\<exists>z. sublist [(x, 2), (z, 0)] Cy1 \<and> (x, z) \<in> arcs G)"
proof -
  have 0: "length Cy1 \<ge> 2"
    using assms length_Cy1
    by auto
  have "(x, 2) \<in> set Cy1"
    using assms x_inG_x_i_in_Cy1
    by simp
  then have "\<exists>y. sublist [(x, 2), y] Cy1"
    using 0 hd_last_Cy1 assms
    by (meson List_Auxiliaries.a_in_Cycle_exists_sublist)
  then obtain y where y_def: "sublist [(x, 2), y] Cy1"
    by blast
  then show ?thesis
    using post_2_edge assms verts_G
    by blast
qed


lemma post_0_cycle:
  assumes "x \<in> verts G" "card (verts G) > 1"
  shows "sublist [(x, 0), (x, 1)] Cy1 \<or> (\<exists>z. sublist [(x, 0), (z, 2)] Cy1 \<and> (z, x) \<in> arcs G)"
proof -
  have 0: "length Cy1 \<ge> 2"
    using assms length_Cy1
    by auto
  have "(x, 0) \<in> set Cy1"
    using assms x_inG_x_i_in_Cy1
    by simp
  then have "\<exists>y. sublist [(x, 0), y] Cy1"
    using 0 hd_last_Cy1 assms
    by (meson List_Auxiliaries.a_in_Cycle_exists_sublist)
  then obtain y where y_def: "sublist [(x, 0), y] Cy1"
    by blast
  then show ?thesis
    using post_0_edge assms
    by blast
qed


lemma post_1_cycle:
  assumes "x \<in> verts G"
  shows "(sublist [(x, 1), (x, 2)] Cy1) \<or> sublist [(x, 1), (x, 0)] Cy1"
proof -
  have 0: "length Cy1 \<ge> 2"
    using assms length_Cy1
    by auto
  have "(x, 1) \<in> set Cy1"
    using assms x_inG_x_i_in_Cy1
    by simp
  then have "\<exists>y. sublist [(x, 1), y] Cy1"
    using 0 hd_last_Cy1 assms
    by (meson List_Auxiliaries.a_in_Cycle_exists_sublist)
  then obtain y where y_def: "sublist [(x, 1), y] Cy1"
    by blast
  then show ?thesis
    using post_1_edge assms
    by blast
qed


lemma sublist_Cy1_for_x:
  assumes "x \<in> verts G"
  shows "(sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1) \<or>
         (sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
proof -
  have 0: "length Cy1 \<ge> 2"
    using length_Cy1
    by auto
  have inCy1: "(x, 1) \<in> set Cy1" "(x, 2) \<in> set Cy1" "(x, 0) \<in> set Cy1"
    using assms x_inG_x_i_in_Cy1
    by auto
  then have 1: "sublist [(x, 0), (x, 1)] Cy1 \<or> sublist [(x, 2), (x, 1)] Cy1"
    using 0 hd_last_Cy1 assms pre_1_cycle verts_G
    by blast
  have 2: "sublist [(x, 1), (x, 2)] Cy1 \<or> sublist [(x, 1), (x, 0)] Cy1"
    using 0 assms post_1_cycle
    by simp
  show ?thesis
  proof(cases "sublist [(x, 0), (x, 1)] Cy1")
    case True
    then have s1: "sublist [(x, 0), (x, 1)] Cy1"
      by auto
    then show ?thesis
    proof(cases "sublist [(x, 1), (x, 0)] Cy1")
      case True
      then have "Cy1 = [(x, 0), (x, 1), (x, 0)] \<or> Cy1 = [(x, 1), (x, 0), (x, 1)]"
        using distinct_tl_cyclic_sublist_cs_explisit s1 hd_last_Cy1 distinct_tl_Cy1
        by (simp add: distinct_tl_cyclic_sublist_cs_explisit)
      then have "(x, 2) \<in> set [(x, (0::nat)), (x, 1), (x, 0)] \<or>
      (x, 2) \<in> set [(x, (1::nat)), (x, 0), (x, 1)]"
        using assms inCy1
        by fastforce
      then show ?thesis
        by(auto)
    next
      case False
      then have "sublist [(x, 1), (x, 2)] Cy1"
        using 2
        by auto
      then show ?thesis
        using True
        by auto
    qed
  next
    case False
    then have 3: "sublist [(x, 2), (x, 1)] Cy1"
      using 1 by simp
    then show ?thesis proof(cases "sublist [(x, 1), (x, 0)] Cy1")
      case True
      then show ?thesis using 3 by simp
    next
      case False
      then have "sublist [(x, 1), (x, 2)] Cy1"
        using 2 by auto
      then have "Cy1 = [(x, 2), (x, 1), (x, 2)] \<or> Cy1 = [(x, 1), (x, 2), (x, 1)]"
        using distinct_tl_cyclic_sublist_cs_explisit 3 hd_last_Cy1 distinct_tl_Cy1
        by (simp add: distinct_tl_cyclic_sublist_cs_explisit)
      then have "(x, 0) \<in> set [(x, (2::nat)), (x, 1), (x, 2)]
        \<or> (x, 0) \<in> set [(x, (1::nat)), (x, 2), (x, 1)]"
        using assms inCy1
        by fastforce
      then show ?thesis
        by(auto)
    qed
  qed
qed


lemma x_1_in_C_x_in_to_cycle_hc:
  assumes "(x, 1) \<in> set C"
  shows "x \<in> set (to_cycle_hc C)"
  using assms by(induction C)(auto)


lemma v_in_set_to_cycle_hc_Cy1:
  assumes "v \<in> verts G"
  shows "v \<in> set (to_cycle_hc Cy1)"
proof -
  have "(v, 1) \<in> set Cy1"
    using assms x_inG_x_i_in_Cy1(2)
    by auto
  then show ?thesis
    using x_1_in_C_x_in_to_cycle_hc
    by metis
qed


lemma v_in_set_to_cycle_hc_Cy2:
  assumes "v \<in> verts G"
  shows "v \<in> set (to_cycle_hc Cy2)"
  using assms Cy2_def v_in_set_to_cycle_hc_Cy1
  using G'_def HC_To_UHC_2.v_in_set_to_cycle_hc_Cy1 local.in_uhc uhc_Cy2 verts_G
  by fastforce


lemma hd_to_cycle_hc_if_x_1_hd_C:
  assumes "hd C = (x, 1)" "C \<noteq> []"
  shows "to_cycle_hc C = x # (to_cycle_hc (tl C))"
  using assms by(induction C)(auto)


lemma x_not_hd_C1_x_not_hd_Cy1:
  assumes "x \<noteq> hd C1" "Cy1 \<noteq> []"
  shows "(x, 1) \<noteq> hd Cy1"
proof (rule ccontr)
  assume "\<not> (x, 1) \<noteq> hd Cy1"
  then have "to_cycle_hc Cy1 = x # (to_cycle_hc (tl Cy1))"
    using assms hd_to_cycle_hc_if_x_1_hd_C
    by metis
  then have "x = hd C1"
    using C1_def
    by simp
  then show False
    using assms
    by simp
qed


lemma longer_sublists_Cy1:
  assumes "x \<in> verts G" "x \<noteq> hd C1"
  shows "sublist [(x, 0), (x, 1), (x, 2)] Cy1 \<or> sublist [(x, 2), (x, 1), (x, 0)] Cy1"
proof -
  have 1: "(sublist [(x, (1::nat)), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1) \<or>
         (sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
    using assms sublist_Cy1_for_x
    by(auto)
  have 2: "(x, 1) \<noteq> hd Cy1"
    using assms length_Cy1(2) x_not_hd_C1_x_not_hd_Cy1
    by fastforce
  then show ?thesis
  proof(cases "(sublist [(x, (1::nat)), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1)")
    case True
    then have "sublist [(x, 0), (x, 1), (x, 2)] Cy1"
      using sublist_ab_bc_b_not_head 2 distinct_tl_Cy1
      by metis
    then show ?thesis
      by simp
  next
    case False
    then have "(sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
      using 1
      by auto
    then have "sublist [(x, 2), (x, 1), (x, 0)] Cy1"
      using sublist_ab_bc_b_not_head 2 distinct_tl_Cy1
      by metis
    then show ?thesis
      by auto
  qed
qed


lemma x_in_verts_x_in_C1:
  assumes "x \<in> verts G"
  shows "x \<in> set C1"
  using assms
  by (simp add: C1_def v_in_set_to_cycle_hc_Cy1)


lemma in_to_cycle_hc_in_C:
  assumes "x \<in> set (to_cycle_hc C)"
  shows "(x, (1::nat))\<in> set C"
  using assms by(induction C)(auto split: if_split_asm)


lemma in_Cy1_in_verts_G':
  assumes "x \<in> set Cy1"
  shows "x \<in> verts G'"
  using Cy1_def assms
  unfolding is_uhc_def
  by blast


lemma x_in_C1_in_verts_G:
  assumes "x \<in> set C1"
  shows "x \<in> verts G"
  using assms C1_def in_to_cycle_hc_in_C in_Cy1_in_verts_G' G'_def_3
  by fastforce


lemma b_1_not_in_C_not_in_cycle_hc:
  assumes "(b, 1) \<notin> set C"
  shows "b \<notin> set (to_cycle_hc C)"
  using assms by(induction C)(auto split: if_split_asm)


lemma distinct_C_distinct_to_cycle_hc_C:
  assumes "distinct (C)"
  shows "distinct (to_cycle_hc C)"
  using assms by(induction C)(auto simp add: b_1_not_in_C_not_in_cycle_hc)



lemma last_a_1_last_to_cycle_hc:
  assumes "last C = (a, 1)" "C \<noteq> []"
  shows "last (to_cycle_hc C) = a"
  using assms apply(induction C) apply(auto split: if_split_asm)
  using last_in_set x_1_in_C_x_in_to_cycle_hc
  by fastforce


lemma hd_noteq_1_eq_tl_cycle:
  assumes "hd C = (a, i)" "i \<noteq> 1"
  shows "to_cycle_hc C = to_cycle_hc (tl C)"
  using assms by(induction C)(auto)


lemma distinct_C1:
  shows "distinct (tl C1) \<and> hd C1 = last C1 \<or> distinct C1"
proof -
  have 1: "distinct (to_cycle_hc (tl Cy1))"
    using distinct_C_distinct_to_cycle_hc_C distinct_tl_Cy1
    by auto
  obtain a b where ab_def: "hd Cy1 = (a, b)"
    by (meson surj_pair)
  then show ?thesis
  proof(cases "b = 1")
    case True
    then have "last Cy1 = (a, 1)"
      using hd_last_Cy1 ab_def
      by auto
    then have 2: "last C1 = a"
      using last_a_1_last_to_cycle_hc C1_def length_Cy1(2)
      by fastforce
    have "Cy1 \<noteq> []"
      using length_C_vwalk_arcs_not_empty length_Cy1(2) vwalk_arcs.simps(1)
      by blast
    then have "to_cycle_hc Cy1 = a # (to_cycle_hc (tl Cy1))"
      using ab_def True
      by (simp add: hd_to_cycle_hc_if_x_1_hd_C)
    then have "hd C1 = last C1" "distinct (tl C1)"
      using 1 2 C1_def
      by auto
    then show ?thesis
      by simp
  next
    case False
    then have "to_cycle_hc Cy1 = to_cycle_hc (tl Cy1)"
      using ab_def hd_noteq_1_eq_tl_cycle
      by fast
    then show ?thesis
      using 1 C1_def
      by auto
  qed
qed


lemma in_cy1_in_verts_G:
  assumes "(x, i) \<in> set Cy1"
  shows "x \<in> verts G"
  using assms in_Cy1_in_verts_G' G'_def_3
  by auto


lemma sublist_x_y_z_to_cycle_hc:
  assumes "sublist [x, y] (to_cycle_hc C)" "sublist [x, z] (to_cycle_hc C)"
    "distinct (tl (to_cycle_hc C)) \<and> hd (to_cycle_hc C) = last (to_cycle_hc C)
    \<or> distinct (to_cycle_hc C)"
  shows "y = z"
proof(cases "distinct (to_cycle_hc C)")
  case True
  then show ?thesis
    using assms
    by (meson distinct_C_distinct_to_cycle_hc_C two_sublist_distinct_same_last)
next
  case False
  then have "distinct (tl (to_cycle_hc C)) \<and> hd (to_cycle_hc C) = last (to_cycle_hc C)"
    using assms
    by auto
  then show ?thesis
    using assms
    by (meson two_sublist_same_first_distinct_tl)
qed


lemma distinct_tl_c_to_cycle_hc:
  assumes "distinct (tl C)" "to_cycle_hc C = to_cycle_hc (tl C)"
  shows "distinct (to_cycle_hc C)"
  using assms
  by (simp add: distinct_C_distinct_to_cycle_hc_C)


lemma hd_C_not_eq_1_equal_tl:
  assumes "hd C = (a, b)" "b \<noteq> 1" "C \<noteq> []"
  shows "to_cycle_hc C = to_cycle_hc (tl C)"
  using assms
  by (metis list.collapse to_cycle_hc.simps(1))


lemma sublist_2_0_in_C1_helper:
  assumes "sublist [(x, (1::nat)), (x, 2), (y, 0), (y, 1)] C"
  shows "sublist [x, y] (to_cycle_hc C)"
  using assms
proof(induction C)
  case Nil
  then show ?case
    by (simp add: sublist_def)
next
  case (Cons a C)
  then have 1: "a = (x, 1) \<or> sublist [(x, 1), (x, 2), (y, 0), (y, 1)] C"
    using sublist_cons_impl_sublist_list by metis
  have "\<exists>p1 p2. p1 @ [(x, 1), (x, 2), (y, 0), (y, 1)]@ p2 = (a#C)"
    using sublist_def Cons by metis
  then obtain p1 p2 where p_def: "p1 @ [(x, 1), (x, 2), (y, 0), (y, 1)]@ p2 = (a#C)"
    by auto
  then show ?case proof(cases "p1 \<noteq> []" )
    case True
    then have "tl p1 @ [(x, 1), (x, 2), (y, 0), (y, 1)]@ p2 = (C)"
      using p_def
      by (metis list.sel(3) tl_append2)
    then have "sublist [(x, 1), (x, 2), (y, 0), (y, 1)] C"
      using sublist_def
      by blast
    then have "sublist [x, y] (to_cycle_hc C)"
      using Cons
      by auto
    then show ?thesis
      by (metis sublist_cons surj_pair to_cycle_hc.simps(1))
  next
    case False
    then have 2: "p1 = []"
      by simp
    then have "(x, 1) = a"
      using 1 p_def
      by simp
    then have "[(x, 1), (x, 2), (y, 0), (y, 1)] @ p2 = (a#C)"
      using 2 p_def
      by simp
    then have "to_cycle_hc (a#C) = x # to_cycle_hc ([(x, (2::nat)), (y, 0), (y, 1)] @ p2)"
      by fastforce
    then have "... = x # to_cycle_hc ([(y, 0), (y, 1)] @ p2)"
      by(auto)
    then have "... = x # to_cycle_hc ([(y, 1)] @ p2)"
      by simp
    then have "... = x # y # to_cycle_hc p2"
      by auto
    then have "to_cycle_hc (a#C) = x # y # to_cycle_hc p2"
      by (simp add: \<open>to_cycle_hc (a # C) = x # to_cycle_hc ([(x, 2), (y, 0), (y, 1)] @ p2)\<close>)
    then have "to_cycle_hc (a#C) = [] @ [x, y] @ (to_cycle_hc p2)"
      by simp
    then show ?thesis
      using sublist_def
      by metis
  qed
qed


lemma sublist_2_0_in_C1_helper_2:
  assumes "sublist [(x, (1::nat)), (x, 0), (y, 2), (y, 1)] C"
  shows "sublist [x, y] (to_cycle_hc C)"
  using assms
proof(induction C)
  case Nil
  then show ?case
    by (simp add: sublist_def)
next
  case (Cons a C)
  then have 1: "a = (x, 1) \<or> sublist [(x, 1), (x, 0), (y, 2), (y, 1)] C"
    using sublist_cons_impl_sublist_list by metis
  have "\<exists>p1 p2. p1 @ [(x, 1), (x, 0), (y, 2), (y, 1)]@ p2 = (a#C)"
    using sublist_def Cons by metis
  then obtain p1 p2 where p_def: "p1 @ [(x, 1), (x, 0), (y, 2), (y, 1)]@ p2 = (a#C)"
    by auto
  then show ?case
  proof(cases "p1 \<noteq> []" )
    case True
    then have "tl p1 @ [(x, 1), (x, 0), (y, 2), (y, 1)]@ p2 = (C)"
      using p_def
      by (metis list.sel(3) tl_append2)
    then have "sublist [(x, 1), (x, 0), (y, 2), (y, 1)] C"
      using sublist_def
      by blast
    then have "sublist [x, y] (to_cycle_hc C)"
      using Cons
      by auto
    then show ?thesis
      by (metis sublist_cons surj_pair to_cycle_hc.simps(1))
  next
    case False
    then have 2: "p1 = []" by simp
    then have "(x, 1) = a"
      using 1 p_def
      by simp
    then have "[(x, 1), (x, 0), (y, 2), (y, 1)] @ p2 = (a#C)"
      using 2 p_def
      by simp
    then have "to_cycle_hc (a#C) = x # to_cycle_hc ([(x, (0::nat)), (y, 2), (y, 1)] @ p2)"
      by fastforce
    then have "... = x # to_cycle_hc ([(y, 2), (y, 1)] @ p2)"
      by(auto)
    then have "... = x # to_cycle_hc ([(y, 1)] @ p2)"
      by simp
    then have "... = x # y # to_cycle_hc p2"
      by auto
    then have "to_cycle_hc (a#C) = x # y # to_cycle_hc p2"
      by (simp add: \<open>to_cycle_hc (a # C) = x # to_cycle_hc ([(x, 0), (y, 2), (y, 1)] @ p2)\<close>)
    then have "to_cycle_hc (a#C) = [] @ [x, y] @ (to_cycle_hc p2)"
      by simp
    then show ?thesis
      using sublist_def
      by metis
  qed
qed


lemma sublist_i_j_last:
  assumes  "(sublist [(x, i), (y, j)] C)" "distinct C"
    "last C = (y, j)"
  shows "\<exists>p1. C = p1 @ [(x, i), (y, j)]"
  using assms
proof(induction C)
  case Nil
  then show ?case
    by (simp add: sublist_def)
next
  case (Cons a C)
  then have Cne: "C \<noteq> []"
    using last_ConsL vwalk_sublist_in_arcs by fastforce
  then show ?case proof(cases "a = (x, i)")
    case True
    then have "(x, i) = hd (a#C)"
      by simp
    then have "(y, j) = hd C"
      using Cons
      by (metis list.inject list.sel(1) sublist_hd_last_only_2_elems)
    then have "hd C = last C"
      using Cons
      by (simp add: Cne)
    then have "C = [(y, j)]"
      using Cons
      by (metis \<open>(x, i) = hd (a # C)\<close> list.sel(1) list.sel(3) sublist_hd_last_only_2_elems)
    then have "(a#C) = [] @ [(x, i), (y, j)]"
      using True
      by simp
    then show ?thesis
      using True
      by simp
  next
    case False
    then have 1: "sublist [(x, i), (y, j)] C"
      using Cons
      by (metis sublist_cons_impl_sublist)
    have "last (a # C) = last C"
      using Cne by simp
    then show ?thesis
      using Cons 1
      by auto
  qed
qed


lemma to_Cycle_noteq_eqmpty_impl_last_eq:
  assumes "(to_cycle_hc C) \<noteq> []"
  shows "last(to_cycle_hc ((b,c)#C)) = last (to_cycle_hc C)"
  using assms by(auto)


lemma no_one_to_cycle_empty:
  assumes "\<not> (\<exists>x. (x, 1) \<in> set C)"
  shows "to_cycle_hc C = []"
  using assms by(induction C)(auto)


lemma last_x1_x0_last_to_cycle_hc:
  assumes "C = p1 @ [(x, (1::nat)), (x, 0)]"
  shows "last (to_cycle_hc C) = x"
  using assms
proof(induction C arbitrary: p1)
  case Nil
  then show ?case
    by auto
next
  case (Cons a C)
  obtain b c where bc_def: "a = (b, c)"
    by fastforce
  then show ?case
  proof(cases "\<exists>p1. C = p1 @[(x, 1), (x, 0)]")
    case True
    then obtain p2 where p2_def: "C = p2 @ [(x, 1), (x, 0)]"
      by auto
    then have 1: "last (to_cycle_hc C) = x"
      using Cons
      by auto
    have "to_cycle_hc C \<noteq> []"
      by (metis True in_set_conv_decomp list.distinct(1) list.set_cases x_1_in_C_x_in_to_cycle_hc)
    then have "last (to_cycle_hc (a#C)) = last (to_cycle_hc C)"
      using to_Cycle_noteq_eqmpty_impl_last_eq bc_def
      by auto
    then show ?thesis
      using Cons 1
      by(auto)
  next
    case False
    then have "p1 = []"
      using Cons
      by (metis list.sel(3) tl_append2)
    then have C_def: "C = [(x, 0)]"
      using Cons
      by simp
    then have "to_cycle_hc (a # C) = [x]"
    proof -
      have 1: "to_cycle_hc (a # C) = x # (to_cycle_hc C)"
        using Cons.prems \<open>p1 = []\<close>
        by auto
      have "\<not> (\<exists> z. (z, 1) \<in> set C)"
        using C_def by(auto)
      then have "to_cycle_hc C = []"
        using no_one_to_cycle_empty C_def
        by auto
      then show ?thesis
        using 1
        by simp
    qed
    then show ?thesis by simp
  qed
qed


lemma last_x1_x2_last_to_cycle_hc:
  assumes "C = p1 @ [(x, (1::nat)), (x, 2)]"
  shows "last (to_cycle_hc C) = x"
  using assms
proof(induction C arbitrary: p1)
  case Nil
  then show ?case
    by auto
next
  case (Cons a C)
  obtain b c where bc_def: "a = (b, c)"
    by fastforce
  then show ?case
  proof(cases "\<exists>p1. C = p1 @[(x, 1), (x, 2)]")
    case True
    then obtain p2 where p2_def: "C = p2 @ [(x, 1), (x, 2)]"
      by auto
    then have 1: "last (to_cycle_hc C) = x"
      using Cons
      by auto
    have "to_cycle_hc C \<noteq> []"
      by (metis True in_set_conv_decomp list.distinct(1) list.set_cases x_1_in_C_x_in_to_cycle_hc)
    then have "last (to_cycle_hc (a#C)) = last (to_cycle_hc C)"
      using to_Cycle_noteq_eqmpty_impl_last_eq bc_def
      by auto
    then show ?thesis
      using Cons 1
      by(auto)
  next
    case False
    then have "p1 = []"
      using Cons
      by (metis list.sel(3) tl_append2)
    then have C_def: "C = [(x, 2)]"
      using Cons
      by simp
    then have "to_cycle_hc (a # C) = [x]"
    proof -
      have 1: "to_cycle_hc (a # C) = x # (to_cycle_hc C)"
        using Cons.prems \<open>p1 = []\<close>
        by auto
      have "\<not> (\<exists> z. (z, 1) \<in> set C)"
        using C_def
        by(auto)
      then have "to_cycle_hc C = []"
        using no_one_to_cycle_empty C_def
        by auto
      then show ?thesis
        using 1
        by simp
    qed
    then show ?thesis
      by simp
  qed
qed


lemma last_x1_x0_y2_last_to_cycle_hc:
  assumes "C = p1 @ [(x, (1::nat)), (x, 0), (y, 2)]"
  shows "last (to_cycle_hc C) = x"
  using assms
proof(induction C arbitrary: p1)
  case Nil
  then show ?case
    by auto
next
  case (Cons a C)
  obtain b c where bc_def: "a = (b, c)"
    by fastforce
  then show ?case
  proof(cases "\<exists>p1. C = p1 @[(x, 1), (x, 0), (y, 2)]")
    case True
    then obtain p2 where p2_def: "C = p2 @ [(x, 1), (x, 0), (y, 2)]"
      by auto
    then have 1: "last (to_cycle_hc C) = x"
      using Cons
      by auto
    have "to_cycle_hc C \<noteq> []"
      by (metis True in_set_conv_decomp list.distinct(1) list.set_cases x_1_in_C_x_in_to_cycle_hc)
    then have "last (to_cycle_hc (a#C)) = last (to_cycle_hc C)"
      using to_Cycle_noteq_eqmpty_impl_last_eq bc_def
      by auto
    then show ?thesis
      using Cons 1
      by(auto)
  next
    case False
    then have "p1 = []"
      using Cons
      by (metis list.sel(3) tl_append2)
    then have C_def: "C = [(x, 0), (y, 2)]"
      using Cons
      by simp
    then have "to_cycle_hc (a # C) = [x]"
    proof -
      have 1: "to_cycle_hc (a # C) = x # (to_cycle_hc C)"
        using Cons.prems \<open>p1 = []\<close>
        by auto
      have "\<not> (\<exists> z. (z, 1) \<in> set C)"
        using C_def by(auto)
      then have "to_cycle_hc C = []"
        using no_one_to_cycle_empty C_def
        by auto
      then show ?thesis
        using 1
        by simp
    qed
    then show ?thesis
      by simp
  qed
qed


lemma last_x1_x2_y0_last_to_cycle_hc:
  assumes "C = p1 @ [(x, (1::nat)), (x, 2), (y, 0)]"
  shows "last (to_cycle_hc C) = x"
  using assms
proof(induction C arbitrary: p1)
  case Nil
  then show ?case
    by auto
next
  case (Cons a C)
  obtain b c where bc_def: "a = (b, c)"
    by fastforce
  then show ?case
  proof(cases "\<exists>p1. C = p1 @[(x, 1), (x, 2), (y, 0)]")
    case True
    then obtain p2 where p2_def: "C = p2 @ [(x, 1), (x, 2), (y, 0)]"
      by auto
    then have 1: "last (to_cycle_hc C) = x"
      using Cons
      by auto
    have "to_cycle_hc C \<noteq> []"
      by (metis True in_set_conv_decomp list.distinct(1) list.set_cases x_1_in_C_x_in_to_cycle_hc)
    then have "last (to_cycle_hc (a#C)) = last (to_cycle_hc C)"
      using to_Cycle_noteq_eqmpty_impl_last_eq bc_def
      by auto
    then show ?thesis
      using Cons 1
      by(auto)
  next
    case False
    then have "p1 = []"
      using Cons
      by (metis list.sel(3) tl_append2)
    then have C_def: "C = [(x, 2), (y, 0)]"
      using Cons
      by simp
    then have "to_cycle_hc (a # C) = [x]"
    proof -
      have 1: "to_cycle_hc (a # C) = x # (to_cycle_hc C)"
        using Cons.prems \<open>p1 = []\<close>
        by auto
      have "\<not> (\<exists> z. (z, 1) \<in> set C)"
        using C_def by(auto)
      then have "to_cycle_hc C = []"
        using no_one_to_cycle_empty C_def
        by auto
      then show ?thesis
        using 1
        by simp
    qed
    then show ?thesis
      by simp
  qed
qed


lemma sublist_i_j_last_distinct_tl:
  assumes  "(sublist [(x, i), (y, j)] C)" "distinct (tl C)" "(x, i) \<noteq> hd C"
    "last C = (y, j)"
  shows "\<exists>p1. C = p1 @ [(x, i), (y, j)]"
  using assms
proof(induction C)
  case Nil
  then show ?case
    by (simp add: sublist_def)
next
  case (Cons a C)
  then have Cne: "C \<noteq> []"
    using last_ConsL by (metis list.sel(1) sublist_code(2) sublist_cons_impl_sublist)
  have "a \<noteq> (x, i)"
    using Cons
    by simp
  then have 1: "sublist [(x, i), (y, j)] C"
    using Cons sublist_cons_impl_sublist
    by (metis sublist_cons_impl_sublist)
  have "last (a # C) = last C"
    using Cne
    by simp
  then have "\<exists>p1. C = p1 @ [(x,i), (y, j)]"
    using 1 Cons
    by (simp add: sublist_i_j_last)
  then show ?case
    using Cons 1
    by auto
qed


lemma sublist_i_j_k_last:
  assumes  "(sublist [(x, i), (y, j)] C)" "distinct C"
    "C = p1 @ [(y, j), (z, k)]"
  shows "\<exists>p1. C = p1 @ [(x, i), (y, j), (z, k)]"
  using assms
proof(induction C arbitrary: p1)
  case Nil
  then show ?case
    by (simp add: sublist_def)
next
  case (Cons a C)
  then have Cne: "C \<noteq> []"
    using last_ConsL vwalk_sublist_in_arcs
    by fastforce
  then show ?case proof(cases "a = (x, i)")
    case True
    then have "(x, i) = hd (a#C)"
      by simp
    then have 2: "(y, j) = hd C"
      using Cons
      by (metis append_self_conv2 list.sel(1) sublist3_hd_lists sublist_def)
    have 3: "p1 \<noteq> []"
      using Cons True sublist_not_cyclic_for_distinct
      by force
    have "C = tl (p1 @ [(y, j), (z, k)])"
      using Cons
      by (metis list.sel(3))
    then have "C = (tl p1) @ [(y, j), (z, k)]"
      using 3
      by simp
    then have "hd ((tl p1) @ [(y, j), (z, k)]) = (y, j)" "distinct ((tl p1) @ [(y, j), (z, k)])"
      using Cons 2
       apply presburger
      using Cons.prems(2) \<open>C = tl p1 @ [(y, j), (z, k)]\<close>
      by auto
    then have "tl p1 = []"
      by (metis \<open>C = tl p1 @ [(y, j), (z, k)]\<close> append.right_neutral append_is_Nil_conv hd_Cons_tl
          hd_append2 self_append_conv2 sublist_v1_hd_v2_hd_tl_lists)
    have "C = [(y, j), (z, k)]"
      using Cons 2 \<open>C = tl p1 @ [(y, j), (z, k)]\<close> \<open>tl p1 = []\<close>
      by fastforce
    then have "(a#C) = [] @ [(x, i), (y, j), (z, k)]"
      using True
      by simp
    then show ?thesis
      using True
      by simp
  next
    case False
    then have 1: "sublist [(x, i), (y, j)] C"
      using Cons
      by (metis sublist_cons_impl_sublist)
    have 2: "C = tl (p1 @ [(y, j), (z, k)])"
      using Cons
      by (metis list.sel(3))
    then have "p1 \<noteq> []"
      using "1" vwalk_sublist_in_arcs
      by fastforce
    then have 3: "C = (tl p1) @ [(y, j), (z, k)]"
      using 2 by simp
    then have "\<exists>p2. C = p2 @ [(x, i), (y, j), (z, k)]"
      using Cons 1
      by auto
    then show ?thesis
      using Cons 1
      by force
  qed
qed


lemma sublist_i_j_k_last_distinct_tl:
  assumes "distinct (tl C)" "(x, i) \<noteq> hd C" "(y, j) \<noteq> hd C" "sublist [(x, i), (y, j)] C"
    "\<exists> p1. C = p1 @ [(y, j), (z, k)]"
  shows "\<exists> p2. C = p2 @ [(x, i), (y, j), (z, k)]"
  using assms
proof(induction C)
  case Nil
  then show ?case
    by (simp add: sublist_def)
next
  case (Cons a C)
  then have Cne: "C \<noteq> []"
    using last_ConsL vwalk_sublist_in_arcs
    by force
  have "a \<noteq> (x, i)"
    using Cons
    by simp
  then have 1: "sublist [(x, i), (y, j)] C"
    using Cons sublist_cons_impl_sublist
    by (metis sublist_cons_impl_sublist)
  have dC: "distinct C"
    using Cons
    by simp
  obtain p1 where "(a#C) = p1 @ [(y, j), (z, k)]"
    using Cons
    by auto
  then have "p1 \<noteq> []"
    using Cons
    by auto
  then have "C = (tl p1) @ [(y, j), (z, k)]"
    by (metis \<open>a # C = p1 @ [(y, j), (z, k)]\<close> list.sel(3) tl_append2)
  then have "\<exists>p1. C = p1 @ [(x,i), (y, j), (z, k)]"
    using 1 Cons dC sublist_i_j_k_last
    by fast
  then show ?case
    using Cons 1
    by auto
qed


lemma sublist_2_0_in_C1:
  assumes "sublist [(x, 2), (y, 0)] Cy1"
  shows "sublist [x, y] C1 \<or> y = hd C1 \<and> x = last C1"
proof -
  have "(x, 2) \<in> set Cy1"
    using assms
    by (meson in_sublist_impl_in_list list.set_intros(1))
  then have "x \<in> verts G"
    using assms in_cy1_in_verts_G
    by simp
  then have 1: "(sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1) \<or>
      (sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
    using assms sublist_Cy1_for_x
    by simp
  have "\<not> (sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
    using distinct_tl_Cy1 hd_last_Cy1 assms two_sublist_same_first_distinct_tl
    by fastforce
  then have sx: "(sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1)"
    using 1
    by (metis Pair_inject assms distinct_tl_Cy1 hd_last_Cy1 two_sublist_same_first_distinct_tl)

  have "(y, 0) \<in> set Cy1"
    using assms
    by (meson in_sublist_impl_in_list list.set_intros)
  then have "y \<in> verts G"
    using assms in_cy1_in_verts_G
    by simp
  then have 1: "(sublist [(y, 1), (y, 2)] Cy1 \<and> sublist [(y, 0), (y, 1)] Cy1) \<or>
      (sublist [(y, 1), (y, 0)] Cy1 \<and> sublist [(y, 2), (y, 1)] Cy1)"
    using assms sublist_Cy1_for_x
    by simp
  have "\<not> (sublist [(y, 2), (y, 1)] Cy1 \<and> sublist [(y, 1), (y, 0)] Cy1)"
    using distinct_tl_Cy1 hd_last_Cy1 assms two_sublist_distinct_same_first
    by fastforce
  then have sy: "(sublist [(y, 0), (y, 1)] Cy1 \<and> sublist [(y, 1), (y, 2)] Cy1)"
    using 1
    by auto
  then have s1: "sublist [(x, 2), (y, 0), (y, 1)] Cy1 \<or> hd Cy1 = (y, 0)"
    using assms distinct_tl_Cy1 sublist_ab_bc_b_not_head by force
  then show ?thesis
  proof
    assume a1: "sublist [(x, 2), (y, 0), (y, 1)] Cy1"
    then have "sublist [(x, 1), (x, 2), (y, 0), (y, 1)] Cy1 \<or> hd Cy1 = (x, 2)"
      using distinct_tl_Cy1 sublist_ab_bcs_b_not_head sx
      by metis
    then show ?thesis
    proof
      assume a2: "sublist [(x, 1), (x, 2), (y, 0), (y, 1)] Cy1"
      then show ?thesis
        using sublist_2_0_in_C1_helper C1_def
        by fast
    next
      have tltlCy1: "tl (tl Cy1) \<noteq> []"
        using a1
        by (metis \<open>(x, 2) \<in> set Cy1\<close> assms distinct.simps(2) distinct_singleton
            hd_Cons_tl hd_last_Cy1 last_ConsL last_tl length_Cy1(1) length_geq_2_tt_not_empty
            old.prod.inject set_ConsD sublist_hd_tl_equal_b_hd_tl zero_neq_numeral)
      assume a2: "hd Cy1 = (x, 2)"
      then have "to_cycle_hc Cy1 = to_cycle_hc (tl Cy1)"
        using a1 distinct_tl_Cy1 hd_C_not_eq_1_equal_tl
        by fastforce
      then have "hd (tl Cy1) = (y, 0)"
        using a1 a2 assms distinct_tl_Cy1 hd_last_Cy1 sublist_hd_tl_equal_b_hd_tl
        by force
      then have "to_cycle_hc (tl Cy1) = to_cycle_hc (tl (tl Cy1))"
        using hd_C_not_eq_1_equal_tl
        by (metis list.sel(2) zero_neq_one)
      then have "to_cycle_hc Cy1 = to_cycle_hc (tl (tl Cy1))"
        by (simp add: \<open>to_cycle_hc Cy1 = to_cycle_hc (tl Cy1)\<close>)
      have "hd (tl (tl Cy1)) = (y, 1)"
        using a2 a1 distinct_tl_Cy1 sublist_hd_tl_equal_b_hd_tl_2 hd_last_Cy1
        by fastforce
      then have "hd (to_cycle_hc (tl (tl Cy1))) = y"
        using hd_to_cycle_hc_if_x_1_hd_C tltlCy1
        by fastforce
      then have "hd C1 = y"
        by (simp add: C1_def \<open>to_cycle_hc Cy1 = to_cycle_hc (tl (tl Cy1))\<close>)

      have x1_neq_hcCy1: "(x, 1) \<noteq> hd(Cy1)"
        using a2
        by auto
      have "last Cy1 = (x, 2)"
        using a2 hd_last_Cy1
        by simp
      then have "\<exists>p1. Cy1 = p1 @ [(x, 1), (x,2)]"
        using sublist_i_j_last_distinct_tl sx distinct_tl_Cy1 a2 x1_neq_hcCy1
        by fast
      then have "last (to_cycle_hc Cy1) = x"
        using last_x1_x2_last_to_cycle_hc
        by fast
      then show ?thesis
        using C1_def \<open>hd C1 = y\<close>
        by auto
    qed
  next
    assume a1: "hd Cy1 = (y, 0)"
    then have "hd (tl Cy1) = (y, 1)"
      using distinct_tl_Cy1 sy hd_last_Cy1 sublist_hd_tl_equal_b_hd_tl
      by force
    have "to_cycle_hc Cy1 = to_cycle_hc (tl Cy1)"
      using a1 distinct_tl_Cy1 hd_C_not_eq_1_equal_tl
      by (metis less_not_refl less_one list.sel(2))
    then have "hd (to_cycle_hc Cy1) = y"
      by (metis C1_def \<open>hd (tl Cy1) = (y, 1)\<close> \<open>x \<in> verts G\<close> distinct.simps(2)
          distinct_singleton hd_to_cycle_hc_if_x_1_hd_C list.distinct(1) list.sel(1)
          to_cycle_hc.elims x_in_verts_x_in_C1)
    then have 1: "y = hd C1"
      using C1_def
      by simp
    have x1_neq_hcCy1: "(x, 2) \<noteq> hd(Cy1)" "(x, 1) \<noteq> hd(Cy1)"
      using a1
      by auto
    have "last Cy1 = (y, 0)"
      using a1 hd_last_Cy1
      by simp
    then have "\<exists>p1. Cy1 = p1 @ [(x, 2), (y,0)]"
      using sublist_i_j_last_distinct_tl distinct_tl_Cy1 x1_neq_hcCy1 assms
      by fast
    then have "\<exists>p1. Cy1 = p1 @ [(x, 1), (x, 2), (y, 0)]"
      using sublist_i_j_k_last_distinct_tl distinct_tl_Cy1 x1_neq_hcCy1 sx
      by fast
    then have "last (to_cycle_hc Cy1) = x"
      using last_x1_x2_y0_last_to_cycle_hc
      by fast
    then show ?thesis
      using C1_def 1
      by simp
  qed
qed


lemma sublist_2_0_in_C1_2:
  assumes "sublist [(x, 0), (y, 2)] Cy1"
  shows "sublist [x, y] C1 \<or> y = hd C1 \<and> x = last C1"
proof -
  have "(x, 0) \<in> set Cy1"
    using assms
    by (meson in_sublist_impl_in_list list.set_intros(1))
  then have "x \<in> verts G"
    using assms in_cy1_in_verts_G
    by simp
  then have 1: "(sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1) \<or>
      (sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
    using assms sublist_Cy1_for_x
    by simp
  have "\<not> (sublist [(x, 2), (x, 0)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1)"
    using distinct_tl_Cy1 hd_last_Cy1 assms two_sublist_same_first_distinct_tl
    by fastforce
  then have sx: "(sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
    using 1
    by (metis Pair_inject assms distinct_tl_Cy1 hd_last_Cy1 two_sublist_distinct_same_first
        two_sublist_same_first_distinct_tl)
  have "(y, 2) \<in> set Cy1"
    using assms
    by (meson in_sublist_impl_in_list list.set_intros)
  then have "y \<in> verts G"
    using assms in_cy1_in_verts_G
    by simp
  then have 1: "(sublist [(y, 1), (y, 2)] Cy1 \<and> sublist [(y, 0), (y, 1)] Cy1) \<or>
      (sublist [(y, 1), (y, 0)] Cy1 \<and> sublist [(y, 2), (y, 1)] Cy1)"
    using assms sublist_Cy1_for_x
    by simp
  have "\<not> (sublist [(y, 0), (y, 1)] Cy1 \<and> sublist [(y, 1), (y, 2)] Cy1)"
    using distinct_tl_Cy1 hd_last_Cy1 assms two_sublist_distinct_same_first
    by fastforce
  then have sy: "(sublist [(y, 1), (y, 0)] Cy1 \<and> sublist [(y, 2), (y, 1)] Cy1)"
    using 1
    by auto
  then have s1: "sublist [(x, 0), (y, 2), (y, 1)] Cy1 \<or> hd Cy1 = (y, 2)"
    using assms distinct_tl_Cy1 sublist_ab_bc_b_not_head by force
  then show ?thesis
  proof
    assume a1: "sublist [(x, 0), (y, 2), (y, 1)] Cy1"
    then have "sublist [(x, 1), (x, 0), (y, 2), (y, 1)] Cy1 \<or> hd Cy1 = (x, 0)"
      using distinct_tl_Cy1 sublist_ab_bcs_b_not_head sx
      by metis
    then show ?thesis
    proof
      assume a2: "sublist [(x, 1), (x, 0), (y, 2), (y, 1)] Cy1"
      then show ?thesis using sublist_2_0_in_C1_helper_2 C1_def
        by fast
    next
      have tltlCy1: "tl (tl Cy1) \<noteq> []"
        using a1
        by (metis \<open>(x, 0) \<in> set Cy1\<close> assms distinct.simps(2) distinct_singleton
            hd_Cons_tl hd_last_Cy1 last_ConsL last_tl length_Cy1(1) length_geq_2_tt_not_empty
            old.prod.inject set_ConsD sublist_hd_tl_equal_b_hd_tl zero_neq_numeral)
      assume a2: "hd Cy1 = (x, 0)"
      then have "to_cycle_hc Cy1 = to_cycle_hc (tl Cy1)"
        using a1 distinct_tl_Cy1 hd_C_not_eq_1_equal_tl
        by (metis less_numeral_extra(1) less_numeral_extra(3) list.sel(2))
      then have "hd (tl Cy1) = (y, 2)"
        using a1 a2 assms distinct_tl_Cy1 hd_last_Cy1 sublist_hd_tl_equal_b_hd_tl
        by force
      then have "to_cycle_hc (tl Cy1) = to_cycle_hc (tl (tl Cy1))"
        using hd_C_not_eq_1_equal_tl
        by fastforce
      then have "to_cycle_hc Cy1 = to_cycle_hc (tl (tl Cy1))"
        by (simp add: \<open>to_cycle_hc Cy1 = to_cycle_hc (tl Cy1)\<close>)
      have "hd (tl (tl Cy1)) = (y, 1)"
        using a2 a1 distinct_tl_Cy1 sublist_hd_tl_equal_b_hd_tl_2 hd_last_Cy1
        by fastforce
      then have "hd (to_cycle_hc (tl (tl Cy1))) = y"
        using hd_to_cycle_hc_if_x_1_hd_C tltlCy1
        by fastforce
      then have "hd C1 = y"
        by (simp add: C1_def \<open>to_cycle_hc Cy1 = to_cycle_hc (tl (tl Cy1))\<close>)
      have x1_neq_hcCy1: "(x, 1) \<noteq> hd(Cy1)"
        using a2
        by auto
      have "last Cy1 = (x, 0)"
        using a2 hd_last_Cy1
        by simp
      then have "\<exists>p1. Cy1 = p1 @ [(x, 1), (x,0)]"
        using sublist_i_j_last_distinct_tl sx distinct_tl_Cy1 a2 x1_neq_hcCy1
        by fast
      then have "last (to_cycle_hc Cy1) = x"
        using last_x1_x0_last_to_cycle_hc
        by fast
      then show ?thesis
        using C1_def \<open>hd C1 = y\<close>
        by auto
    qed
  next
    assume a1: "hd Cy1 = (y, 2)"
    then have "hd (tl Cy1) = (y, 1)"
      using distinct_tl_Cy1 sy hd_last_Cy1 sublist_hd_tl_equal_b_hd_tl
      by force
    have "to_cycle_hc Cy1 = to_cycle_hc (tl Cy1)"
      using a1 distinct_tl_Cy1 hd_C_not_eq_1_equal_tl
      by fastforce
    then have "hd (to_cycle_hc Cy1) = y"
      by (metis C1_def \<open>hd (tl Cy1) = (y, 1)\<close> \<open>x \<in> verts G\<close> distinct.simps(2)
          distinct_singleton hd_to_cycle_hc_if_x_1_hd_C list.distinct(1) list.sel(1)
          to_cycle_hc.elims x_in_verts_x_in_C1)
    then have 1: "y = hd C1"
      using C1_def
      by simp
    have x1_neq_hcCy1: "(x, 0) \<noteq> hd(Cy1)" "(x, 1) \<noteq> hd(Cy1)"
      using a1
      by auto
    have "last Cy1 = (y, 2)"
      using a1 hd_last_Cy1
      by simp
    then have "\<exists>p1. Cy1 = p1 @ [(x, 0), (y,2)]"
      using sublist_i_j_last_distinct_tl distinct_tl_Cy1 x1_neq_hcCy1 assms
      by fast
    then have "\<exists>p1. Cy1 = p1 @ [(x, 1), (x, 0), (y, 2)]"
      using sublist_i_j_k_last_distinct_tl distinct_tl_Cy1 x1_neq_hcCy1 sx
      by fast
    then have "last (to_cycle_hc Cy1) = x"
      using last_x1_x0_y2_last_to_cycle_hc
      by fast
    then show ?thesis
      using C1_def 1
      by simp
  qed
qed


lemma sublists_x_z_noteq:
  assumes "sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1"
    "sublist [(x, 2), (z, 0)] Cy1"
  shows "x \<noteq> z"
  using assms sublist_Cy1_arcs_G' G'_def_3
  by fastforce


lemma sublists_x_z_noteq_2:
  assumes "sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1"
    "sublist [(x, 0), (z, 2)] Cy1"
  shows "x \<noteq> z"
  using assms sublist_Cy1_arcs_G' G'_def_3
  by fastforce


lemma sublist_predecessor:
  assumes "sublist [x, y] C1" "sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1"
  shows "sublist [(x, 2), (y, 0)] Cy1 \<or> sublist [(x, 0), (y, 2)] Cy1"
proof(rule ccontr)
  assume a1: "\<not> (sublist [(x, 2), (y, 0)] Cy1 \<or> sublist [(x, 0), (y, 2)] Cy1)"
  have in_Cy1: "(x, 1) \<in> set Cy1" "(y, 1) \<in> set Cy1"
    using assms
    by (metis C1_def in_set_vwalk_arcsE in_to_cycle_hc_in_C vwalk_sublist_in_arcs)+
  then have "(sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1) \<or>
      (sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
    using assms(1)
    by (intro sublist_Cy1_for_x) (auto intro: x_in_C1_in_verts_G sublist_implies_in_set)
  then have "\<not> sublist [(x, 2), (x, 1)] Cy1"
    using distinct_tl_Cy1 hd_last_Cy1 assms
    by (metis Pair_inject less_numeral_extra(3) pos2 two_sublist_distinct_same_first)
  then obtain z where z_def: "sublist [(x, 2), (z, 0)] Cy1 \<and> (x, z) \<in> arcs G"
    by (metis Cy1_def G'_def HC_To_UHC_2.x_in_C1_in_verts_G in_Cy1(1) local.in_uhc post_2_cycle
        verts_G x_1_in_C_x_in_to_cycle_hc)
  then have zy: "z \<noteq> y"
    using a1
    by blast
  then have sxz: "sublist [x, z] C1 \<or> z = hd C1 \<and> x = last C1"
    using sublist_2_0_in_C1 z_def
    by simp
  then have xnoteqz: "x \<noteq> z"
    using sublists_x_z_noteq \<open>sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1\<close>
      sublists_x_z_noteq z_def
    by blast
  then show False
  proof(cases "sublist [x, z] C1")
    case True
    then show ?thesis
      using zy C1_def assms distinct_C1 sublist_x_y_z_to_cycle_hc
      by fastforce
  next
    case False
    then have "z = hd C1 \<and> x = last C1"
      using sxz
      by simp
    then show ?thesis
      using assms distinct_C1 xnoteqz distinct_sublist_last_first_of_sublist_false
      by force
  qed
qed


lemma sublist_predecessor_2:
  assumes "sublist [x, y] C1" "sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1"
  shows "sublist [(x, 0), (y, 2)] Cy1"
proof(rule ccontr)
  assume a1: "\<not> (sublist [(x, 0), (y, 2)] Cy1)"
  have in_Cy1: "(x, 1) \<in> set Cy1" "(y, 1) \<in> set Cy1"
    using assms
     apply(metis in_set_vwalk_arcsE vwalk_sublist_in_arcs)
    using assms
    by (metis C1_def in_set_vwalk_arcsE in_to_cycle_hc_in_C vwalk_sublist_in_arcs)
  then have "(sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1) \<or>
      (sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
    using assms(1)
    by (intro sublist_Cy1_for_x) (auto intro: x_in_C1_in_verts_G sublist_implies_in_set)
  then have "\<not> sublist [(x, 0), (x, 1)] Cy1"
    using distinct_tl_Cy1 hd_last_Cy1 assms
    by (metis Pair_inject less_numeral_extra(3) pos2 two_sublist_distinct_same_first)
  then obtain z where z_def: "sublist [(x, 0), (z, 2)] Cy1 \<and> (z, x) \<in> arcs G"
    by (metis Cy1_def G'_def HC_To_UHC_2.x_in_C1_in_verts_G in_Cy1(1)
        local.in_uhc post_0_cycle verts_G x_1_in_C_x_in_to_cycle_hc)
  then have zy: "z \<noteq> y"
    using a1
    by blast
  then have sxz: "sublist [x, z] C1 \<or> z = hd C1 \<and> x = last C1"
    using sublist_2_0_in_C1_2 z_def
    by simp
  then have xnoteqz: "x \<noteq> z"
    using sublists_x_z_noteq \<open>sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1\<close>
      sublists_x_z_noteq_2 z_def
    by blast
  then show False
  proof(cases "sublist [x, z] C1")
    case True
    then show ?thesis
      using zy C1_def assms distinct_C1 sublist_x_y_z_to_cycle_hc
      by fastforce
  next
    case False
    then have "z = hd C1 \<and> x = last C1"
      using sxz
      by simp
    then show ?thesis
      using assms distinct_C1 xnoteqz distinct_sublist_last_first_of_sublist_false
      by force
  qed
qed


lemma sublist_forall_1:
  assumes "y = hd C1" "sublist [(y, 0), (y, 1)] Cy1" "sublist [(y, 1), (y, 2)] Cy1" "x = C1!i"
    "i < length C1"
  shows "sublist [(x, 0), (x, 1)] Cy1 \<and>sublist [(x, 1), (x, 2)] Cy1"
  using assms
proof(induction i arbitrary: x)
  case 0
  then have "x = hd C1"
    by (simp add: hd_conv_nth)
  then show ?case
    using assms
    by simp
next
  case (Suc i)
  then have 1: "sublist [(C1!i, 0), (C1!i, 1)] Cy1 \<and>sublist [(C1!i, 1), (C1!i, 2)] Cy1"
    by (simp add: Suc.prems(5))
  have in_verts: "x \<in> verts G"
    using x_in_C1_in_verts_G
    by (simp add: Suc.prems(4) Suc.prems(5))
  have "sublist [C1!i, x] C1"
    using Suc sublist_indixes
    by blast
  then have sublists_x_y: "sublist [(C1!i, 2), (x, 0)] Cy1"
    using 1 two_sublist_same_first_distinct_tl[OF distinct_tl_Cy1]
    by (fastforce dest!: sublist_predecessor simp: hd_last_Cy1)
  then have "sublist [(C1!i, 2), (x, 0)] Cy1" proof(cases "sublist [(C1!i, 2), (x, 0)] Cy1")
    case True
    then show ?thesis
      by simp
  next
    case False
    then have "sublist [(C1!i, 0), (x, 2)] Cy1"
      using sublists_x_y
      by simp
    then show ?thesis
      using 1 distinct_tl_Cy1 hd_last_Cy1 two_sublist_same_first_distinct_tl
      by fastforce
  qed
  then have "\<not> sublist [(x, 1), (x, 0)] Cy1"
    using distinct_tl_Cy1 hd_last_Cy1 two_sublist_distinct_same_first
    by fastforce
  then show ?case
    using sublist_Cy1_for_x in_verts
    by blast
qed


lemma sublist_forall_2:
  assumes "y = hd C1" "sublist [(y, 2), (y, 1)] Cy1" "sublist [(y, 1), (y, 0)] Cy1" "x = C1!i"
    "i < length C1"
  shows "sublist [(x, 2), (x, 1)] Cy1 \<and>sublist [(x, 1), (x, 0)] Cy1"
  using assms
proof(induction i arbitrary: x)
  case 0
  then have "x = hd C1"
    by (simp add: hd_conv_nth)
  then show ?case
    using assms
    by simp
next
  case (Suc i)
  then have 1: "sublist [(C1!i, 2), (C1!i, 1)] Cy1 \<and>sublist [(C1!i, 1), (C1!i, 0)] Cy1"
    by (simp add: Suc.prems(5))
  have in_verts: "x \<in> verts G"
    using x_in_C1_in_verts_G
    by (simp add: Suc.prems(4) Suc.prems(5))
  have "sublist [C1!i, x] C1"
    using Suc sublist_indixes
    by blast
  then have sublists_x_y: "sublist [(C1!i, 2), (x, 0)] Cy1 \<or> sublist [(C1!i, 0), (x, 2)] Cy1"
    using sublist_predecessor sublist_predecessor_2 1
    by simp
  then have "sublist [(C1!i, 0), (x, 2)] Cy1"
  proof(cases "sublist [(C1!i, 0), (x, 2)] Cy1")
    case True
    then show ?thesis
      by simp
  next
    case False
    then have "sublist [(C1!i, 2), (x, 0)] Cy1"
      using sublists_x_y
      by simp
    then show ?thesis
      using 1 distinct_tl_Cy1 hd_last_Cy1 two_sublist_same_first_distinct_tl
      by fastforce
  qed
  then have "\<not> sublist [(x, 1), (x, 2)] Cy1"
    using distinct_tl_Cy1 hd_last_Cy1
    by (meson old.prod.inject two_sublist_distinct_same_first zero_neq_one)
  then show ?case
    using sublist_Cy1_for_x in_verts
    by blast
qed


lemma sulbist_forall:
  shows "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1) \<or>
          (\<forall>x \<in> verts G. sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
proof -
  have "Cy1 \<noteq> []"
    using length_Cy1(2)
    by auto
  then have "C1 \<noteq> []"
    using verts_G x_in_verts_x_in_C1
    by fastforce
  then obtain x where x_def: "(x) = hd (C1)"
    by simp
  then have "x \<in> verts G"
    by (simp add: \<open>C1 \<noteq> []\<close> x_in_C1_in_verts_G)
  then have "(sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1) \<or>
         (sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
    using sublist_Cy1_for_x
    by simp
  then show ?thesis
  proof
    assume "(sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1)"
    then show ?thesis
      using sublist_forall_1 by (metis in_set_implies_is_nth x_def x_in_verts_x_in_C1)
  next
    assume "(sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
    then show ?thesis
      using sublist_forall_2 by (metis x_def in_set_implies_is_nth x_in_verts_x_in_C1)
  qed
qed


lemma length_C1:
  shows "length C1 \<ge> 2"
proof -
  have "card (set C1) > 1"
    using x_in_verts_x_in_C1
    by (meson List.finite_set card_greater_1_contains_two_elements contains_two_card_greater_1 verts_G)
  then have "card (set C1) \<ge> 2"
    by simp
  then show ?thesis
    by (meson card_length dual_order.strict_trans2 leD not_le_imp_less)
qed


lemma C1_not_eqmpty:
  shows "C1 \<noteq> []"
  using length_C1
  by auto


lemma in_C1_in_arcs:
  assumes "(x, y) \<in> set (vwalk_arcs C1)"  "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] Cy1
      \<and> sublist [(x, 0), (x, 1)] Cy1)"
  shows "(x, y) \<in> arcs G"
proof -
  have 1: "sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1"
    "sublist [(y, 1), (y, 2)] Cy1 \<and> sublist [(y, 0), (y, 1)] Cy1"
    using assms
    by (meson in_set_vwalk_arcsE x_in_C1_in_verts_G) +
  have "sublist [x, y] C1"
    using assms sublist_for_edges by metis
  then have "sublist [(x, 2), (y, 0)] Cy1"
    using assms  1
    by (metis (no_types, lifting) distinct_tl_Cy1 hd_last_Cy1 not_Cons_self2 one_eq_numeral_iff
        semiring_norm(85) sublist_predecessor to_cycle_hc.simps(1)
        two_sublist_same_first_distinct_tl)
  then have "((x, 2), (y, 0)) \<in> arcs G'"
    by (simp add: sublist_Cy1_arcs_G')
  then show ?thesis
    using pre_0_edges_helper verts_G
    by auto
qed


lemma in_C1_in_arcs_2:
  assumes  "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1)"
  shows "set (vwalk_arcs C1) \<subseteq> arcs G"
  using assms in_C1_in_arcs
  by fastforce


lemma arcs_G_not_empty:
  assumes  "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1)"
  shows "arcs G \<noteq> {}"
proof
  assume "arcs G = {}"
  then have "set (vwalk_arcs C1) = {}"
    using assms in_C1_in_arcs_2
    by simp
  then have "length C1 \<le> 1"
    using vwalk_arcs_empty_length_p
    by auto
  then have "card (set C1) \<le> 1"
    using card_length dual_order.trans
    by blast
  then have "card (verts G) \<le> 1"
    by (meson List.finite_set card_greater_1_contains_two_elements contains_two_card_greater_1
        less_le_not_le verts_G x_in_verts_x_in_C1)
  then show False
    using dual_order.strict_trans1 verts_G
    by blast
qed


lemma arcs_ends_eq_arcs_G:
  assumes  "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1)"
  shows "arcs_ends G = arcs G"
  using arcs_ends_G' arcs_G_not_empty assms G_properties
  by (simp add: Graph_Auxiliaries.arcs_ends_G')


lemma vwalk_C1_G:
  assumes  "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1)"
  shows "vwalk C1 G"
proof
  have 1: "set C1 \<subseteq> verts G"
    by (simp add: subsetI x_in_C1_in_verts_G)
  have 2: "set (vwalk_arcs C1) \<subseteq> arcs G"
    using in_C1_in_arcs_2 assms
    by simp
  have 3: "C1 \<noteq> []"
    by (simp add: C1_not_eqmpty)
  then show "set C1 \<subseteq> verts G" "set (vwalk_arcs C1) \<subseteq> arcs_ends G" "C1 \<noteq> []"
    using 1 2 arcs_ends_eq_arcs_G in_C1_in_arcs_2 assms
    by auto
qed


lemma last_C1_eq_hd_C1_vwalk_cycle:
  assumes "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1)"
    "last C1 = hd C1"
  shows "vwalk_cycle G C1"
  unfolding vwalk_cycle_def
  using vwalk_C1_G distinct_C1 assms length_C1 distinct_C1
  by(auto simp add: distinct_tl)


lemma pre_0_helper:
  assumes "x \<in> verts G" "sublist [(x, (1::nat)), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1"
  shows "\<exists>y. sublist [(y, 2), (x, 0)] Cy1 \<and> (y, x) \<in> arcs G"
proof -
  have 1: "(sublist [(x, 1), (x, 0)] Cy1) \<or> (\<exists>z. sublist [(z, 2), (x, 0)] Cy1 \<and> (z, x) \<in> arcs G)"
    using assms pre_0_cycle
    by simp
  then show ?thesis
  proof (cases "sublist [(x, 1), (x, 0)] Cy1")
    case True
    then have "(x, (2::nat)) = (x, 0)"
      using assms distinct_tl_Cy1 hd_last_Cy1 two_sublist_same_first_distinct_tl
      by fastforce
    then show ?thesis
      using assms
      by auto
  next
    case False
    then have "(\<exists>z. sublist [(z, 2), (x, 0)] Cy1 \<and> (z, x) \<in> arcs G)"
      using 1
      by auto
    then show ?thesis
      by simp
  qed
qed


lemma post_2_helper:
  assumes "x \<in> verts G" "sublist [(x, (1::nat)), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1"
  shows "\<exists>y. sublist [(x, 2), (y, 0)] Cy1 \<and> (x, y) \<in> arcs G"
proof -
  have 1: "(sublist [(x, 2), (x, 1)] Cy1) \<or> (\<exists>z. sublist [(x, 2), (z, 0)] Cy1 \<and> (x, z) \<in> arcs G)"
    using assms post_2_cycle
    by simp
  then show ?thesis
  proof (cases "sublist [(x, 2), (x, 1)] Cy1")
    case True
    then have "(x, (2::nat)) = (x, 0)"
      using assms distinct_tl_Cy1 hd_last_Cy1 distinct_tl_cyclic_sublist_cs_explisit
        x_inG_x_i_in_Cy1(1)
      by fastforce
    then show ?thesis
      using assms
      by auto
  next
    case False
    then have "(\<exists>z. sublist [(x, 2), (z, 0)] Cy1 \<and> (x, z) \<in> arcs G)"
      using 1
      by auto
    then show ?thesis
      by simp
  qed
qed


lemma last_C1_hd_C1_in_arcs:
  assumes "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1)"
    "last C1 \<noteq> hd C1"
  shows "(last C1, hd C1) \<in> arcs G"
proof -
  have distinct: "distinct C1"
    using distinct_C1 assms
    by argo
  have ne: "C1 \<noteq> []"
    using assms
    by (simp add: C1_not_eqmpty)
  have neCy1: "Cy1 \<noteq> []"
    using C1_def ne to_cycle_hc.simps(2)
    by blast
  have "\<exists>i x. last Cy1 = (i, x)"
    by simp
  then obtain x i where xi_def: "last Cy1 = (x, i)"
    by blast
  then have 01: "x \<in> verts G"
    using in_cy1_in_verts_G last_in_set neCy1
    by fastforce
  then have 0: "sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1"
    using assms
    by metis
  have "i = 0 \<or> i = 1 \<or> i = 2"
  proof -
    have "(x, i) \<in> set Cy1"
      using xi_def last_in_set neCy1
      by fastforce
    then have "(x, i) \<in> verts G'"
      by (simp add: in_Cy1_in_verts_G')
    then show ?thesis
      using G'_def_3
      by auto
  qed
  then show ?thesis
  proof
    assume a0: "i = 0"
    then have 1: "hd Cy1 = (x, 0)" "last Cy1 = (x, 0)"
      using hd_last_Cy1 xi_def
      by auto
    then have "sublist [(x, 0), (x, 1)] Cy1"
      using assms(1) in_cy1_in_verts_G list.set_sel(1) neCy1 by metis
    then have "\<exists>p1. Cy1 = [(x, 0), (x, 1)] @ p1"
      using hd_C_sublist_hd
      by (metis "1"(1) distinct_tl_Cy1 hd_last_Cy1)
    then have 2: "hd C1 = x"
      using C1_def tl_append2
      by auto
    have "\<exists>y. sublist [(y, 2), (x, 0)] Cy1 \<and> (y, x) \<in> arcs G"
      using assms 1 0 01 pre_0_helper
      by simp
    then obtain y where y_def: "sublist [(y, 2), (x, 0)] Cy1 \<and> (y, x) \<in> arcs G"
      by auto
    then have "sublist [(y, 1), (y, 2)] Cy1"
      using assms(1) in_cy1_in_verts_G by (meson sublist_implies_in_set(1))
    then have "\<exists>p2. Cy1 = p2 @ [(y, 1), (y, 2), (x, 0)]"
      using 1 y_def distinct_tl_Cy1
      by (simp add: sublist_i_j_k_last_distinct_tl sublist_i_j_last_distinct_tl)
    then have "last C1 = y"
      using C1_def last_x1_x2_y0_last_to_cycle_hc
      by fastforce
    then show ?thesis
      using y_def 2
      by simp
  next
    assume "i = 1 \<or> i = 2"
    then show ?thesis
    proof
      assume "i = 1"
      then have 1: "hd Cy1 = (x, 1)" "last Cy1 = (x, 1)"
        using hd_last_Cy1 xi_def
        by auto
      then have "hd C1 = x" "last C1 = x"
        using neCy1 x_not_hd_C1_x_not_hd_Cy1
         apply force
        by (simp add: "1"(2) C1_def last_a_1_last_to_cycle_hc neCy1)
      then show ?thesis
        using assms
        by blast
    next
      assume "i = 2"
      then have 1: "hd Cy1 = (x, 2)" "last Cy1 = (x, 2)"
        using hd_last_Cy1 xi_def
        by auto
      then have "sublist [(x, 0), (x, 1)] Cy1"
        using assms(1) in_cy1_in_verts_G list.set_sel(1) neCy1 by metis
      then have "\<exists>p1. Cy1 = p1 @ [(x, 1), (x, 2)]"
        using 1 distinct_tl_Cy1 sublist_i_j_last_distinct_tl 0
        by (simp add: sublist_i_j_last_distinct_tl)
      then have 2: "last C1 = x"
        using C1_def
        by (meson last_x1_x2_last_to_cycle_hc)
      have "\<exists>y. sublist [(x, 2), (y, 0)] Cy1 \<and> (x, y) \<in> arcs G"
        using assms 1 0 01 post_2_helper
        by simp
      then obtain y where y_def: "sublist [(x, 2), (y, 0)] Cy1 \<and> (x, y) \<in> arcs G"
        by auto
      then have "sublist [(y, 0), (y, 1)] Cy1"
        using 1 assms(1) distinct_tl_Cy1 in_cy1_in_verts_G
        by (metis sublist_implies_in_set(2))
      then have "sublist [(x, 2), (y, 0), (y, 1)] Cy1"
        using 1
        by (simp add: distinct_tl_Cy1 sublist_ab_bc_b_not_head y_def)
      then have "\<exists>p2. Cy1 = [(x, 2), (y, 0), (y, 1)] @ p2"
        using 1 y_def distinct_tl_Cy1 hd_last_Cy1 hd_C_sublist_hd
        by fast
      then have "hd C1 = y"
        using C1_def
        by fastforce
      then show ?thesis
        using y_def 2
        by simp
    qed
  qed
qed


lemma vwalk_last_C1_G:
  assumes  "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1)"
    "last C1 \<noteq> hd C1"
  shows "vwalk (last C1 # C1) G"
  using C1_not_eqmpty in_C1_in_arcs_2 last_C1_hd_C1_in_arcs arcs_ends_eq_arcs_G in_C1_in_arcs_2
  by (metis G_properties(1) assms(1) assms(2) vwalk_C1_G
      wf_digraph.vwalk_wf_digraph_consI x_in_C1_in_verts_G x_in_verts_x_in_C1)


lemma last_C1_neq_hd_C1_vwalk_cycle:
  assumes "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1)"
    "last C1 \<noteq> hd C1"
  shows "vwalk_cycle G (last C1 # C1)"
  unfolding vwalk_cycle_def
  using vwalk_last_C1_G last_C1_hd_C1_in_arcs distinct_C1 assms length_C1 distinct_C1
  by(auto simp add: distinct_tl)

end


subsubsection\<open>Proof for given cycle\<close>
text\<open>It may be necessary, to revert the given cycle, if it is of the
  form ...(x, 2)(x, 1)(x,0).... Then the above lemmas can be used.\<close>

lemma always_exist_vwalk_cycle:
  shows "(\<exists>c. vwalk_cycle G c \<and>  (\<forall>x\<in>verts G. x \<in> set c) \<and> set c \<subseteq> verts G \<and> distinct (tl c))"
proof(cases  "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] Cyc1 \<and> sublist [(x, 0), (x, 1)] Cyc1)")
  case True
  then have a1: "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] Cyc1 \<and> sublist [(x, 0), (x, 1)] Cyc1)"
    by auto
  then show ?thesis
  proof(cases "hd C1' = last C1'")
    case True
    then have 1: "vwalk_cycle G C1'"
      using a1 C1'_def Cyc1_def last_C1_eq_hd_C1_vwalk_cycle
      by auto
    have 2: "distinct (tl C1')"
      using a1 C1'_def Cyc1_def distinct_C1 distinct_tl
      by auto
    have 3: "(\<forall>x\<in>verts G. x \<in> set C1')"
      using a1 C1'_def Cyc1_def x_in_verts_x_in_C1
      by blast
    have 4: "set C1' \<subseteq> verts G"
      using C1'_def Cyc1_def x_in_C1_in_verts_G
      by auto
    then show ?thesis using 1 2 3 4
      by blast
  next
    case False
    then have 1: "vwalk_cycle G (last C1' # C1')"
      using a1 C1'_def Cyc1_def last_C1_neq_hd_C1_vwalk_cycle
      by auto
    have 2: "distinct (tl (last C1' # C1'))"
      using a1 C1'_def Cyc1_def distinct_C1 distinct_tl False
      by auto
    have 3: "(\<forall>x\<in>verts G. x \<in> set (last C1' #C1'))"
      using a1 C1'_def Cyc1_def x_in_verts_x_in_C1
      by simp
    have 4: "set (last C1' #C1') \<subseteq> verts G"
      using C1'_def Cyc1_def x_in_C1_in_verts_G C1_not_eqmpty
      by auto
    then show ?thesis using 1 2 3 4
      by blast
  qed
next
  case False
  then have "(\<forall>x \<in> verts G. sublist [(x, 2), (x, 1)] Cyc1 \<and> sublist [(x, 1), (x, 0)] Cyc1)"
    using Cyc1_def sulbist_forall
    by blast
  then have "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] (rev Cyc1) \<and> sublist [(x, 0), (x, 1)] (rev Cyc1))"
    by (simp add: sublist_rev_right)
  then have a1: "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] Cy2 \<and> sublist [(x, 0), (x, 1)] Cy2)"
    by (simp add: Cy2_def)
  then show ?thesis
  proof(cases "hd C2 = last C2")
    case True
    then have 1: "vwalk_cycle G C2"
      using a1 uhc_Cy2 C2_def last_C1_eq_hd_C1_vwalk_cycle
      by auto
    have 2: "distinct (tl C2)"
      using a1 C2_def uhc_Cy2 distinct_C1 distinct_tl
      by auto
    have 3: "(\<forall>x\<in>verts G. x \<in> set C2)"
      using a1 uhc_Cy2 C2_def x_in_verts_x_in_C1
      by blast
    have 4: "set C2 \<subseteq> verts G"
      using C2_def uhc_Cy2 x_in_C1_in_verts_G
      by auto
    then show ?thesis
      using 1 2 3 4
      by blast
  next
    case False
    then have 1: "vwalk_cycle G (last C2 # C2)"
      using a1 C2_def uhc_Cy2 last_C1_neq_hd_C1_vwalk_cycle
      by auto
    have 2: "distinct (tl (last C2 # C2))"
      using a1 C2_def uhc_Cy2 distinct_C1 distinct_tl False
      by auto
    have 3: "(\<forall>x\<in>verts G. x \<in> set (last C2 #C2))"
      using a1 C2_def uhc_Cy2 x_in_verts_x_in_C1
      by simp
    have 4: "set (last C2 #C2) \<subseteq> verts G"
      using C2_def uhc_Cy2 x_in_C1_in_verts_G C1_not_eqmpty
      by auto
    then show ?thesis
      using 1 2 3 4
      by blast
  qed
qed


lemma arcs_G_neq_empty:
  shows "arcs G \<noteq> {}"
proof(cases  "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] Cyc1 \<and> sublist [(x, 0), (x, 1)] Cyc1)")
  case True
  then have a1: "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] Cyc1 \<and> sublist [(x, 0), (x, 1)] Cyc1)"
    by auto
  then show ?thesis
    using Cyc1_def C1'_def arcs_G_not_empty
    by blast
next
  case False
  then have "(\<forall>x \<in> verts G. sublist [(x, 2), (x, 1)] Cyc1 \<and> sublist [(x, 1), (x, 0)] Cyc1)"
    using Cyc1_def sulbist_forall
    by blast
  then have "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] (rev Cyc1)
     \<and> sublist [(x, 0), (x, 1)] (rev Cyc1))"
    by (simp add: sublist_rev_right)
  then have a1: "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] Cy2 \<and> sublist [(x, 0), (x, 1)] Cy2)"
    by (simp add: Cy2_def)
  then show ?thesis
    using Cy2_def C2_def arcs_G_not_empty uhc_Cy2
    by blast
qed


lemma head_tail_G:
  shows "head G = snd" "tail G = fst"
  using arcs_G_neq_empty G_properties
  by auto


lemma exists_cycle:
  shows "(\<exists>c. pre_digraph.cycle G (vwalk_arcs c) \<and>  (\<forall>x\<in>verts G. x \<in> set c)
  \<and> set c \<subseteq> verts G \<and> distinct (tl c))"
  using head_tail_G always_exist_vwalk_cycle
  using vwalk_cycle_impl_cycle
  by auto


lemma in_hc_1:
  shows "G \<in> hc"
proof -
  have 1: "wf_digraph G" " (tail G = fst \<and> head G = snd \<or> arcs G = {})"
    by (simp add: G_properties)+
  have 2: "finite (verts G)"
    using card_eq_0_iff verts_G
    by fastforce
  then show ?thesis
    using exists_cycle 1 2 hc_def is_hc_def
    by auto
qed

end

subsubsection\<open>Only one vertex in the graph\<close>
context
  assumes verts_G: "\<not> card (verts G) > 1"
begin

lemma is_hc_G_empty:
  shows "is_hc G []"
  using is_hc_def verts_G
  by fastforce


lemma in_hc_2:
  shows "G \<in> hc"
  using hc_def finite_verts_G G_properties is_hc_G_empty
  by blast
end

lemma in_hc:
  shows "G \<in> hc"
  using in_hc_1 in_hc_2
  by blast

end
end