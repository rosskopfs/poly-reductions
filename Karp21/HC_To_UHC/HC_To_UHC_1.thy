theory HC_To_UHC_1
  imports UHC_Definitions
begin

subsection\<open>\<open>G \<in> hc \<longrightarrow> hc_to_uhc G \<in> uhc\<close>\<close>

subsubsection\<open>Preliminaries\<close>

fun to_cycle_uhc::"('a, ('a \<times> 'a)) pre_digraph \<Rightarrow> 'a list \<Rightarrow> ('a \<times> nat) list" where
  "to_cycle_uhc G [] = []" |
  "to_cycle_uhc G (v#vs) = [(v, 0), (v, 1), (v, 2)] @ to_cycle_uhc G vs"


context
  fixes G assumes in_hc: "G \<in> hc" "card (verts G) > 1"
  fixes Cycle assumes Cycle_def: "is_hc G Cycle"
  fixes G' assumes G'_def: "G' = hc_to_uhc G"
  fixes Cy assumes Cy_def: "Cy = (hd Cycle, 2) # to_cycle_uhc G (tl Cycle)"
begin

lemma G'_def_2:
  shows "G' = \<lparr>verts = {(v, (0::nat))|v. v \<in> verts G} \<union> {(v, 1)|v. v \<in> verts G}
      \<union> {(v, 2)|v. v \<in> verts G},
    arcs = {((v, 0), (v, 1))|v. v \<in> verts G} \<union>{((v, 1), (v, 0))|v. v \<in> verts G}\<union>
      {((v, 1), (v, 2))|v. v \<in> verts G}\<union>{((v, 2), (v, 1))|v. v \<in> verts G}\<union>
      {((v, 2), (u, 0))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e \<and> u \<noteq> v}\<union>
      {((u, 0), (v, 2))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e \<and> u \<noteq> v},
    tail = fst, head = snd\<rparr>"
  using in_hc G'_def
  unfolding hc_def hc_to_uhc_def
  by(auto)

lemma wf_digraph_G:
  shows "wf_digraph G" "((tail G = fst \<and> head G = snd) \<or> arcs G = {})"
  using in_hc hc_def
  by auto

lemma finite_verts_G:
  shows "finite (verts G)"
  using in_hc hc_def
  by auto

lemma wf_digraph_G':
  shows "wf_digraph G'"
  using G'_def_2 wf_digraph_def wf_digraph_G
  by(auto simp add: G'_def_2 wf_digraph_def)

lemma symmetric_G':
  shows "symmetric G'"
  using G'_def_2
  unfolding symmetric_def sym_def arcs_ends_def arc_to_ends_def
  by auto

lemma head_tail_G':
  shows "head G' = snd" "tail G' = fst"
  using G'_def_2
  by auto

lemma Cycle_subset:
  shows "set Cycle \<subseteq> verts G"
  using Cycle_def is_hc_def
  by metis

lemma Cycle_not_empty:
  assumes  "card (verts G) > 1"
  shows "Cycle \<noteq> []"
  using Cycle_def is_hc_def
  by (metis assms leD vwalk_arcs.simps(1) wf_digraph.cycle_conv wf_digraph_G(1))

lemma last_pre_digraph_cas:
  assumes "pre_digraph.cas G u (p) v" "p\<noteq> []" "arcs G \<noteq> {}"
  shows "snd (last p) = v"
  using assms wf_digraph_G
  by (auto simp add: last_pre_digraph_cas)

lemma hd_pre_digraph_cas:
  assumes "pre_digraph.cas G u (p) v" "p\<noteq> []" "arcs G \<noteq> {}"
  shows "fst (hd p) = u"
  using assms wf_digraph_G
  by (auto simp add: hd_pre_digraph_cas)

lemma hd_last_Cycle:
  assumes "card (verts G) > 1" "arcs G \<noteq> {}"
  shows "hd Cycle = last Cycle"
proof (cases "length Cycle = 1")
  case True
  then show ?thesis
    using True assms Cycle_not_empty
    by (metis List.finite_set assms(1) card_length
        contains_two_card_greater_1 last_in_set leD list.set_sel(1))
next
  case False
  have "Cycle \<noteq> []"
    using assms Cycle_not_empty
    by blast
  then have "length Cycle \<noteq> 1" "length Cycle \<noteq> 0"
    using assms False
    by(auto)
  then have "length Cycle \<ge> 2"
    by linarith
  then have arcs_not_epmty: "(vwalk_arcs Cycle) \<noteq> []"
    using vwalk_arcs_empty_length_p
    by force
  then obtain u where u_def: "pre_digraph.awalk G u (vwalk_arcs Cycle) u"
    using Cycle_def in_hc
    unfolding is_hc_def pre_digraph.cycle_def
    by auto
  then have 1: "pre_digraph.cas G u (vwalk_arcs Cycle) u"
    using pre_digraph.awalk_def
    by force
  then have "snd (last (vwalk_arcs Cycle)) = u"
    using arcs_not_epmty last_pre_digraph_cas assms
    by auto
  then have 2: "last Cycle = u"
    by (meson last_vwalk_arcs_last_p arcs_not_epmty)
  have "fst (hd (vwalk_arcs Cycle)) = u"
    using arcs_not_epmty hd_pre_digraph_cas 1 assms
    by auto
  then have 3: "hd Cycle = u"
    by (meson hd_vwalk_arcs_last_p arcs_not_epmty)
  then show ?thesis using 2 3
    by simp
qed

lemma finite_subset_verts_G':
  shows "finite {(v, i) |v. v \<in> verts G}"
  using finite_verts_G
  by simp

lemma distinct_tail_cycle:
  shows "distinct (tl Cycle)"
  using Cycle_def is_hc_def
  by auto

lemma finite_verts_G':
  shows "finite (verts G')"
  using G'_def_2 finite_verts_G finite_subset_verts_G'
  by fastforce

lemma vwalk_arcs_Cycle_subseteq_arcs_G:
  assumes "card (verts G) > 1"
  shows "set (vwalk_arcs Cycle) \<subseteq> arcs G"
  using Cycle_def assms
  unfolding is_hc_def pre_digraph.cycle_def pre_digraph.awalk_def
  by auto

lemma no_arcs_impl_at_most_one_vertex:
  assumes "arcs G = {}"
  shows "card (verts G) \<le> 1"
  using Cycle_def assms
  unfolding is_hc_def pre_digraph.cycle_def pre_digraph.awalk_def
  by auto

lemma arcs_G'_subset_verts_verts:
  shows "arcs G' \<subseteq> (verts G' \<times> verts G')"
  using wf_digraph_G' head_tail_G' wf_digraph.head_in_verts wf_digraph.tail_in_verts
  by fastforce

lemma arcsG_empty_exists_cycleG':
  assumes "arcs G = {}"
  shows "\<exists>Cy. is_uhc G' Cy"
  using no_arcs_impl_at_most_one_vertex assms in_hc
  by simp

lemma non_empty_arcs_card_verts_G:
  assumes "arcs G \<noteq> {}"
  shows "card (verts G) \<ge> 1"
  using assms wf_digraph_G finite_verts_G in_hc
  by simp

lemma card_verts_G'_2:
  assumes "card (verts G) > 1"
  shows "card (verts G') > 1"
proof -
  obtain v where "v \<in> verts G"
    using assms not_one_le_zero
    by fastforce
  then have "(v, 0) \<in> verts G'" "(v, 1) \<in> verts G'"
    using G'_def_2
    by auto
  then show ?thesis
    using finite_verts_G'
    by (meson contains_two_card_greater_1 prod.inject zero_neq_one)
qed

lemma not_in_cycle_not_in_uhc_cycle:
  assumes "a \<notin> set C"
  shows "(a, i) \<notin> set (to_cycle_uhc G C)"
  using assms
  apply(induction C)
  by(auto)

lemma distinct_C_distinct_uhc_cycle:
  assumes "distinct C"
  shows "distinct (to_cycle_uhc G C)"
  using assms by(induction C)(auto simp add: not_in_cycle_not_in_uhc_cycle)

lemma distinct_Cy:
  shows "distinct (tl Cy)"
  using Cy_def distinct_tail_cycle distinct_C_distinct_uhc_cycle
  by simp

lemma subset_G_to_uhc_subset_G':
  assumes "set C \<subseteq> verts G"
  shows "set (to_cycle_uhc G C) \<subseteq> verts G'"
  using assms by(induction C)(auto simp add: G'_def_2)

lemma set_Cy_subset_G':
  assumes  "card (verts G) > 1"
  shows "set Cy \<subseteq> verts G'"
proof -
  have 0: "Cy = (hd Cycle, 2) # to_cycle_uhc G (tl Cycle)"
    using Cy_def
    by simp
  then have 1: "set (to_cycle_uhc G (tl Cycle)) \<subseteq> verts G'"
    using Cycle_subset subset_G_to_uhc_subset_G'
    by (meson list_set_tl subset_code(1))
  have "hd Cycle \<in> verts G"
    using Cycle_subset Cycle_not_empty assms
    by auto
  then have "(hd Cycle, 2) \<in> verts G'"
    using G'_def_2
    by fastforce
  then show ?thesis
    using 1 0
    by auto
qed

lemma x_in_C_impl_x_in_to_cycle_uhc_i:
  assumes "x \<in> set C" "i\<le>2"
  shows "(x, i) \<in> set (to_cycle_uhc G C)"
  using assms by(induction C)(auto)

lemma card_verts_impl_length_Cycle:
  assumes "card (verts G) > 1"  "arcs G \<noteq> {}"
  shows "length Cycle > 2"
proof -
  have hl: "hd Cycle = last Cycle"
    using assms
    by (simp add: hd_last_Cycle)
  obtain u v where 1: "u \<in> verts G" "v \<in> verts G" "u \<noteq> v"
    using assms card_greater_1_contains_two_elements
    by blast
  then have "u \<in> set Cycle" "v \<in> set Cycle"
    using Cycle_def assms is_hc_def
    by fastforce+
  then have "u \<in> set (tl Cycle)" "v \<in> set (tl Cycle)"
    using hl
    by (metis 1(3) Cycle_not_empty List.insert_def hd_Cons_tl in_hc(2) in_set_insert
        insert_Nil last_ConsR last_in_set list.distinct(1) list.sel(1, 3) list.set_cases)+
  then have "card (set (tl Cycle)) > 1"
    using 1
    by (meson List.finite_set contains_two_card_greater_1)
  then have "length (tl Cycle) > 1"
    using  \<open>u \<in> set (tl Cycle)\<close>
    by (metis card_length leD length_pos_if_in_set
        less_numeral_extra(3) less_one linorder_neqE_nat)
  then show ?thesis
    by simp
qed

lemma all_verts_G'_in_Cy:
  assumes  "card (verts G) > 1" "arcs G \<noteq> {}"
  shows "(\<forall>x\<in>verts G'. x \<in> set Cy)"
proof
  fix x assume x_in: "x \<in> verts G'"
  then obtain a where a_def: "x = (a, 0) \<or> x = (a, 1) \<or>  x = (a, 2)"
    using G'_def_2
    by auto
  then have "a \<in> verts G"
    using G'_def_2  x_in
    by force
  then have "a \<in> set (tl Cycle)"
    using hd_last_eq_in_tl hd_last_Cycle assms card_verts_impl_length_Cycle Cycle_def is_hc_def
    by fastforce
  then have "(a, 0) \<in> set ( to_cycle_uhc G (tl Cycle))"
    "(a, 1) \<in> set ( to_cycle_uhc G (tl Cycle))"
    "(a, 2) \<in> set ( to_cycle_uhc G (tl Cycle))"
    using x_in_C_impl_x_in_to_cycle_uhc_i
    by auto
  then show "x\<in> set Cy"
    using a_def Cy_def
    by force
qed

lemma c_not_empty_to_cycle_not_empty:
  assumes "C \<noteq> []"
  shows "to_cycle_uhc G C \<noteq> []"
  using assms
  apply(induction C)
  by(auto)

lemma last_to_cycle_uhc:
  assumes "C \<noteq> []"
  shows "last (to_cycle_uhc G C) = (last C, 2)"
  using assms by(induction C)(auto simp add: c_not_empty_to_cycle_not_empty)

lemma hd_last_Cy:
  assumes "arcs G \<noteq> {}" "card (verts G) > 1"
  shows "hd Cy = last Cy"
proof -
  have 1: "hd Cycle = last Cycle"
    using hd_last_Cycle assms
    by blast
  have 2: "Cycle \<noteq> []"
    using assms Cycle_not_empty
    by blast
  then show ?thesis
  proof(cases "length Cycle = 1")
    case True
    then have "Cy = [(hd Cycle, 2)]"
      using Cy_def 2
      by (metis length_1_set_L list.sel(3) list.set_sel(1) to_cycle_uhc.simps(1))
    then show ?thesis
      by simp
  next
    case False
    then have "length Cycle > 1"
      using 1  2
      by (simp add: nat_neq_iff)
    then have 3: "tl Cycle \<noteq> []"
      by (metis length_tl less_numeral_extra(3) list.size(3) zero_less_diff)
    then have 4: "hd Cycle = last (tl Cycle)"
      using 1
      by (simp add: last_tl)
    have 5: "last Cycle = last (tl Cycle)"
      using 1 4
      by auto
    have 6: "last (to_cycle_uhc G (tl Cycle)) = (last (tl Cycle), 2)"
      using 3 last_to_cycle_uhc
      by(auto simp add:3 last_to_cycle_uhc)
    then have "last Cy =  (last Cycle, 2)"
      using 1 5 6 Cy_def c_not_empty_to_cycle_not_empty
      by auto
    then show ?thesis
      using 1 Cy_def
      by auto
  qed
qed


subsubsection\<open>@{term Cy} is a @{term pre_digraph.cycle}\<close>

lemma vwalk_arcs_Cy_not_empty:
  assumes "arcs G \<noteq> {}" "card (verts G) > 1"
  shows "vwalk_arcs Cy \<noteq> []"
proof -
  have "length Cycle > 2"
    using assms
    by (simp add: card_verts_impl_length_Cycle)
  then have "tl Cycle \<noteq> []"
    using length_geq_2_tt_not_empty
    by force
  then have "to_cycle_uhc G (tl Cycle) \<noteq> []"
    by (simp add: c_not_empty_to_cycle_not_empty)
  then have "length Cy > 1"
    using Cy_def
    by auto
  then show ?thesis
    using length_C_vwalk_arcs_not_empty
    by fast
qed

lemma at_least_two_nodes_vwalk_arcs_awalk_verts:
  assumes "length C > 1"
  shows "(pre_digraph.awalk_verts G' u (vwalk_arcs C)) = C"
  using head_tail_G' at_least_two_nodes_vwalk_arcs_awalk_verts assms
  by fast

lemma distinct_impl_distinct_awalk:
  assumes "distinct (tl C)"
  shows  "distinct (tl (pre_digraph.awalk_verts G' u (vwalk_arcs C)))"
  using assms
proof(induction C)
  case Nil
  then show ?case
    unfolding pre_digraph.awalk_verts_def
    by auto
next
  case (Cons a C)
  then show ?case
  proof(cases "C = []")
    case True
    then show ?thesis
      by (simp add: pre_digraph.awalk_verts.simps(1))
  next
    case False
    then have "length (a#C) > 1"
      by simp
    then show ?thesis
      using at_least_two_nodes_vwalk_arcs_awalk_verts Cons
      by presburger
  qed
qed

lemma distinct_tl_awalk_cy:
  shows"distinct (tl (pre_digraph.awalk_verts G' u (vwalk_arcs Cy)))"
  using distinct_impl_distinct_awalk distinct_Cy
  by simp

lemma cas_to_cycle_uhc:
  assumes "L = (to_cycle_uhc G C)" "L \<noteq> []"
  shows "pre_digraph.cas G' (hd L) (vwalk_arcs L) (last L)"
  using assms
proof(induction C arbitrary: L)
  case Nil
  then show ?case
    by auto
next
  case (Cons a C)
  have L_def: "L = [(a, 0), (a,1), (a,2)] @ (to_cycle_uhc G C)"
    using Cons
    by auto
  then have "hd L = (a, 0)"
    by auto
  then have 1: "(vwalk_arcs L) = ((a, 0), (a, 1))# ((a, 1), (a, 2))#
    (vwalk_arcs ((a, 2) # to_cycle_uhc G C))"
    using L_def vwalk_arcs.simps
    by auto
  then show ?case
  proof(cases "C = []")
    case True
    then have "last L = (a, 2)"
      using L_def
      by simp
    then have "vwalk_arcs L = ((a, 0), (a, 1))# ((a, 1), (a, 2)) # []"
      using 1 True
      by simp
    then have "pre_digraph.cas G' (a, (0::nat)) (vwalk_arcs L) (a, 2)"
      using G'_def_2
      by (simp add: pre_digraph.cas.simps(1, 2))
    then show ?thesis
      by (simp add: \<open>hd L = (a, 0)\<close> \<open>last L = (a, 2)\<close>)
  next
    case False
    then have to_cy_not_empty: "(to_cycle_uhc G C) \<noteq> []"
      by (simp add: c_not_empty_to_cycle_not_empty)
    then have 2: "pre_digraph.cas G'  (hd (to_cycle_uhc G (C)))
        (vwalk_arcs (to_cycle_uhc G (C))) (last (to_cycle_uhc G (C)))"
      using Cons
      by auto
    then have "(vwalk_arcs L) = ((a, 0), (a, 1))# ((a, 1), (a, 2))# ((a, 2), hd (to_cycle_uhc G C))
        # (vwalk_arcs (to_cycle_uhc G C))"
      using 1 to_cy_not_empty
      by auto
    then show ?thesis
      using L_def G'_def_2 2 to_cy_not_empty
      by(simp add: pre_digraph.cas.simps)
  qed
qed

lemma cas_Cy:
  assumes "arcs G \<noteq> {}" "card (verts G) > 1"
  shows  "pre_digraph.cas G' (hd Cycle, 2) (vwalk_arcs Cy) (hd Cycle, 2)"
proof -
  have "Cycle \<noteq> []"
    using assms
    by (simp add: Cycle_not_empty)
  then have tl_Cy_not_empty: "tl Cy \<noteq> []"
    using assms Cy_def vwalk_arcs_Cy_not_empty
    by auto
  then have 1: "pre_digraph.cas G' (hd (tl Cy)) (vwalk_arcs (tl Cy)) (last Cy)"
    using cas_to_cycle_uhc Cy_def
    by simp
  have 2: "hd Cy = (hd Cycle, 2)"
    using Cy_def
    by simp
  then have 3: "last Cy = (hd Cycle, 2)"
    using assms hd_last_Cy by auto
  have "pre_digraph.cas G' (hd Cycle, 2) (vwalk_arcs Cy) (last Cy)"
    using 1 2 G'_def_2
    by (metis (no_types, lifting) Cy_def tl_Cy_not_empty assms hd_vwalk_arcs_last_p
        head_tail_G' list.sel(1) list.sel(3) pre_digraph.cas_simp snd_conv
        vwalk_arcs_Cons vwalk_arcs_Cy_not_empty)
  then show ?thesis
    using 3
    by simp
qed

lemma hd_to_cycle_uhc:
  assumes "C \<noteq> []"
  shows "hd (to_cycle_uhc G C) = (hd C, 0)"
  using assms by(induction C)(auto)

lemma sublist_Cycle_in_arcs:
  assumes "card (verts G) > 1" "sublist [a, b] Cycle"
  shows "(a, b) \<in> arcs G"
proof -
  have 1: "(a, b) \<in> set (vwalk_arcs Cycle)"
    using assms by (simp add: vwalk_sublist_in_arcs)
  have "set (vwalk_arcs Cycle) \<subseteq> arcs G"
    using Cycle_def assms
    unfolding pre_digraph.cycle_def is_hc_def pre_digraph.awalk_def
    by auto
  then show ?thesis
    using 1
    by auto
qed

lemma hd_hd_tl_Cycle_in_arcs:
  assumes "tl Cycle \<noteq> []" "card (verts G) > 1"
  shows "(hd Cycle, hd (tl Cycle)) \<in> arcs G"
proof -
  have 1: "(hd Cycle, hd (tl Cycle)) \<in> set (vwalk_arcs Cycle)"
    using assms
    by (metis Nil_tl in_set_member list.collapse member_rec(1) vwalk_arcs_Cons)
  have "set (vwalk_arcs Cycle) \<subseteq> arcs G"
    using Cycle_def assms
    unfolding pre_digraph.cycle_def is_hc_def pre_digraph.awalk_def
    by auto
  then show ?thesis using 1
    by auto
qed

lemma hd_Cy_noteq_hd_tl_Cy:
  assumes "arcs G \<noteq> {}" "card (verts G) > 1"
  shows "hd (tl Cycle) \<noteq> hd Cycle"
proof (rule ccontr)
  have hl: "hd Cycle = last Cycle"
    using hd_last_Cycle assms
    by simp
  assume a1: "\<not> hd (tl Cycle) \<noteq> hd Cycle"
  then have 1: "hd (tl Cycle) = last Cycle"
    using hl
    by simp
  have "tl Cycle \<noteq> []"
    using card_verts_impl_length_Cycle assms length_geq_2_tt_not_empty
    by force
  then have "tl Cycle = [hd Cycle]"
    using distinct_tail_cycle 1 a1
    by (metis  append.right_neutral last_tl list.set_sel(1) sublist_set_last_ls1_2)
  then have cy_def: "Cycle= [hd Cycle, hd Cycle]"
    using distinct_tail_cycle hl
    by (metis Nil_tl list.discI list.exhaust_sel)
  have "length [hd Cycle, hd Cycle] = 2"
    by simp
  then have "length Cycle = 2"
    using cy_def
    by(auto)
  then show False
    using assms card_verts_impl_length_Cycle
    by auto
qed

lemma uv_in_G_in_G':
  assumes "u\<noteq> v"
    "(u, v) \<in> arcs G"
  shows "((u, 2), (v, 0)) \<in> arcs G'"
  using assms G'_def_2 wf_digraph_G(2)
  by auto

lemma hd_Cy_hd_tl_in_arcs_G':
  assumes "arcs G \<noteq> {}" "card (verts G) > 1" "sublist [a, b] Cy" "a = hd Cy"
  shows "(a, b) \<in> arcs G'"
proof -
  have tail_head_G:
    "tail G = fst" "head G = snd"
    using wf_digraph_G assms by simp+
  have a_def: "a = (hd Cycle, 2)"
    using assms Cy_def
    by simp
  have Cycle_not_empty: "Cycle \<noteq> []"
    using assms
    by (simp add: Cycle_not_empty)
  have tl_Cycle_not_empty: "tl Cycle \<noteq> []"
    using assms Cy_def vwalk_arcs_Cy_not_empty
    by auto
  have "distinct (tl Cy)" "a = last Cy"
    using assms hd_last_Cy
     apply (simp add: distinct_Cy hd_last_Cy)
    using assms hd_last_Cy
    by blast
  then have "b = hd (tl Cy)"
    using sublist_hd_tl_equal_b_hd_tl assms
    by fast
  then have b_def: "b = (hd (tl Cycle), 0)"
    using Cy_def hd_to_cycle_uhc tl_Cycle_not_empty
    by(auto)
  then have "(hd Cycle, hd (tl Cycle)) \<in> arcs G"
    "head G (hd Cycle, hd (tl Cycle)) = (hd (tl Cycle))"
    "tail G (hd Cycle, hd (tl Cycle)) = (hd (Cycle))"
    using assms hd_hd_tl_Cycle_in_arcs tl_Cycle_not_empty
      apply blast
    using assms tail_head_G
    by auto
  then have "((hd Cycle, 2), (hd (tl Cycle), 0)) \<in> arcs G'"
    using G'_def_2 tail_head_G hd_Cy_noteq_hd_tl_Cy uv_in_G_in_G' in_hc(2)
    by auto
  then show ?thesis
    using a_def b_def
    by simp
qed

lemma in_Cycle_in_verts:
  assumes "a \<in> set Cycle"
  shows "a \<in> verts G"
  using Cycle_def is_hc_def assms
  by fast

lemma helper_arcs_first_list:
  assumes "sublist [(a, i), (b, j)] [(c, 0), (c, (1::nat)), (c, 2)]"
  shows "(a = b \<and> a \<in> set (c#C) \<and> b \<in> set (c#C) \<and> ((i = 0 \<and> j = 1) \<or> (i = 1 \<and> j = 2)))"
proof -
  have distinct: "distinct [(c, (0::nat)), (c, 1), (c, 2)]"
    by(auto)
  have in_set: "(a, i) \<in> set [(c, 0), (c, 1), (c, 2)]" "(b, j) \<in> set [(c, 0), (c, 1), (c, 2)]"
    using assms
    by (meson in_sublist_impl_in_list list.set_intros)+
  then have "a = c" "b = c"
    by auto
  then have 1: "a = b" "a \<in> set (c#C)" "b \<in> set (c#C)"
    by auto
  have "((i = 0 \<and> j = 1) \<or> (i = 1 \<and> j = 2))"
  proof(cases "i = 0")
    case True
    then have "[(c, (0::nat)), (c, 1), (c, 2)] = (a, i) #  [(c, 1), (c, 2)]"
      by (simp add: \<open>a = c\<close>)
    then have "(b, j) = (c, 1)"
      using assms vwalk_sublist_in_arcs
      by fastforce
    then show ?thesis
      using True
      by blast
  next
    case False
    then have "i = 1 \<or> i = 2"
      using in_set
      by auto
    then show ?thesis
    proof
      assume "i = 1"
      then have "(b, j) = (c, 2)"
        using \<open>b = c\<close> assms vwalk_sublist_in_arcs
        by fastforce
      then show ?thesis
        using \<open>i = 1\<close>
        by auto
    next
      assume "i = 2"
      then have "False"
        using assms vwalk_sublist_in_arcs
        by fastforce
      then show ?thesis
        by simp
    qed
  qed
  then show ?thesis
    using 1
    by auto
qed

lemma to_cycle_uhc_sublist_sublist_of_C:
  assumes "L = to_cycle_uhc G C" "sublist [(a, i), (b, j)] L" "distinct L"
  shows "(sublist [a, b] C \<and> i = 2 \<and> j = 0) \<or> (a = b \<and> a \<in> set C \<and> b \<in> set C
    \<and> ((i = 0 \<and> j = 1) \<or> (i = 1 \<and> j = 2)))"
  using assms
proof(induction C arbitrary: L)
  case Nil
  then have "L \<noteq> []"
    by (simp add: sublist_def)
  then show ?case using Nil
    by simp
next
  case (Cons c C)
  then have "L = [(c, 0), (c, 1), (c, 2)] @ to_cycle_uhc G C"
    by simp
  then have 1: "sublist [(a, i), (b, j)] ([(c, 0), (c, 1), (c, 2)] @ to_cycle_uhc G C)"
    "distinct ([(c, 0), (c, 1), (c, 2)] @ to_cycle_uhc G C)"
    "[(c, 0), (c, 1), (c, 2)] \<noteq> []"
    using Cons by auto
  then have "sublist [(a, i), (b, j)] [(c, 0), (c, 1), (c, 2)] \<or>
    sublist [(a, i), (b, j)] (to_cycle_uhc G C) \<or>
    (a, i) = (c, 2) \<and> (b, j) = hd (to_cycle_uhc G C)"
    by - (drule sublist_append_using_or, auto)
  then show ?case
  proof
    assume "sublist [(a, i), (b, j)] [(c, 0), (c, 1), (c, 2)]"
    then have "a = b \<and> a \<in> set (c # C) \<and> b \<in> set (c # C) \<and> (i = 0 \<and> j = 1 \<or> i = 1 \<and> j = 2)"
      using helper_arcs_first_list
      by metis
    then show ?thesis using helper_arcs_first_list 1
      by blast
  next
    assume "sublist [(a, i), (b, j)] (to_cycle_uhc G C) \<or> (a, i) = (c, 2)
        \<and> (b, j) = hd (to_cycle_uhc G C)"
    then show ?thesis
    proof
      assume "sublist [(a, i), (b, j)] (to_cycle_uhc G C)"
      then have "(sublist [a, b] C \<and> i = 2 \<and> j = 0) \<or> (a = b \<and> a \<in> set C \<and> b \<in> set C
        \<and> ((i = 0 \<and> j = 1) \<or> (i = 1 \<and> j = 2)))"
        using Cons
        by simp
      then show ?thesis
        by (meson list.set_intros(2) sublist_cons)
    next
      assume a1: "(a, i) = (c, 2) \<and> (b, j) = hd (to_cycle_uhc G C)"
      then have "(to_cycle_uhc G C) \<noteq> []"
        using Cons \<open>L = [(c, 0), (c, 1), (c, 2)] @ to_cycle_uhc G C\<close>
        by (metis append.right_neutral helper_arcs_first_list one_eq_numeral_iff
            semiring_norm(85) zero_neq_numeral)
      then have C_not_empty: "C \<noteq> []"
        by auto
      then have b_def: "(b, j) = (hd C, 0)"
        using hd_to_cycle_uhc a1
        by simp
      then have "[]@[a, b]@(tl C) = c#C"
        using a1 C_not_empty
        by simp
      then have "sublist [a, b] (c # C)"
        using sublist_def by metis
      then show ?thesis
        using a1 b_def
        by force
    qed
  qed
qed

lemma sublist_disitnct_not_eq:
  assumes "sublist [a, b] C" "distinct C"
  shows "a \<noteq> b"
  using assms by(rule sublist_implies_in_set_a)

lemma sublist_ab_a_noteq_b:
  assumes "sublist [a, b] Cycle" "1 < card (verts G)" "arcs G \<noteq> {}"
  shows "a \<noteq> b"
proof(cases "a = hd Cycle")
  case True
  then have "distinct (tl Cycle)" "a = last Cycle"
    using distinct_tail_cycle hd_last_Cycle assms
    by simp+
  then have "b = hd (tl Cycle)"
    using sublist_hd_tl_equal_b_hd_tl assms
    by (simp add: sublist_hd_tl_equal_b_hd_tl local.hd_last_Cycle)
  then show ?thesis
    using True assms(3) hd_Cy_noteq_hd_tl_Cy in_hc(2)
    by auto
next
  case False
  then have "sublist [a, b] (tl Cycle)"
    using assms
    by (metis hd_Cons_tl list.sel(2) sublist_cons_impl_sublist)
  then show ?thesis using distinct_tail_cycle sublist_disitnct_not_eq
    by fastforce
qed

lemma Cy_arcs_in_arcs_G':
  assumes "arcs G \<noteq> {}" "card (verts G) > 1"
  shows "set (vwalk_arcs Cy) \<subseteq> arcs G'"
proof
  have d_tl_C: "distinct (tl Cycle)"
    using assms
    by (simp add: distinct_tail_cycle)
  then have dL: "distinct (to_cycle_uhc G (tl Cycle))"
    using distinct_C_distinct_uhc_cycle
    by simp
  have tail_head_G:
    "tail G = fst" "head G = snd"
    using wf_digraph_G assms
    by simp+
  fix x assume x_def: "x \<in> set (vwalk_arcs Cy)"
  then have "\<exists>a b. x = (a, b)"
    by (meson prod_cases3)
  then obtain a b where ab_def: "x = (a, b)"
    by auto
  then have sublist: "sublist [a, b] Cy"
    using x_def sublist_for_edges
    by metis
  then have "a = hd Cy \<or> sublist [a, b] (tl Cy)"
    by (metis ab_def distinct.simps(2) distinct_singleton hd_Cons_tl
        in_set_vwalk_arcsE sublist_cons_impl_sublist x_def)
  then show "x \<in> arcs G'"
  proof
    assume "a = hd Cy"
    then show ?thesis
      using hd_Cy_hd_tl_in_arcs_G' assms ab_def sublist
      by(auto)
  next
    assume "sublist [a, b] (tl Cy)"
    then have s_tcu: "sublist [a, b] (to_cycle_uhc G (tl Cycle))"
      using Cy_def
      by simp
    obtain a1 a2 b1 b2 where ab_def_2: "a = (a1, a2)" "b = (b1, b2)"
      by fastforce
    then have "(sublist [a1, b1] (tl Cycle) \<and> a2 = 2 \<and> b2 = 0)
      \<or> (a1 = b1 \<and>a1 \<in> set (tl Cycle) \<and> b1 \<in> set (tl Cycle)
      \<and> ((a2 = 0 \<and> b2 = 1) \<or> (a2 = 1 \<and> b2 = 2)))"
      using to_cycle_uhc_sublist_sublist_of_C s_tcu ab_def_2 dL
      by simp
    then show ?thesis
    proof
      assume a1: "(sublist [a1, b1] (tl Cycle) \<and> a2 = 2 \<and> b2 = 0)"
      then have "sublist [a1, b1] Cycle"
        by (metis hd_Cons_tl list.sel(2) sublist_cons)
      then have "(a1, b1) \<in> arcs G" "a1 \<noteq> b1"
        using sublist_Cycle_in_arcs assms sublist_ab_a_noteq_b
        by auto
      then have "((a1, 2), (b1, 0)) \<in> arcs G'"
        using G'_def_2 tail_head_G sublist_ab_a_noteq_b
        by force
      then have "((a1, a2), (b1, b2)) \<in> arcs G'"
        using a1 by auto
      then show ?thesis using ab_def_2 ab_def
        by auto
    next
      assume a1: "(a1 = b1 \<and> a1 \<in> set (tl Cycle) \<and> b1 \<in> set (tl Cycle)
        \<and> ((a2 = 0 \<and> b2 = 1) \<or> (a2 = 1 \<and> b2 = 2)))"
      then have a_eq_b: "a1 = b1" "((a2 = 0 \<and> b2 = 1) \<or> (a2 = 1 \<and> b2 = 2))" "a1 \<in> verts G"
        using in_Cycle_in_verts
        by (auto simp add: a1 in_Cycle_in_verts list_set_tl)
      then have "((a1, 0), (a1, 1)) \<in> arcs G'"  "((a1, 1), (a1, 2)) \<in> arcs G'"
        using G'_def_2
        by simp+
      then show ?thesis
        using a_eq_b ab_def ab_def_2
        by auto
    qed
  qed
qed

lemma pre_digraph_cycle_Cy_G':
  assumes "arcs G \<noteq> {}" "card (verts G) > 1"
  shows "pre_digraph.cycle G' (vwalk_arcs Cy)"
  using assms vwalk_arcs_Cy_not_empty distinct_tl_awalk_cy Cy_def set_Cy_subset_G'
    Cy_arcs_in_arcs_G' cas_Cy
  unfolding pre_digraph.cycle_def pre_digraph.awalk_def
  by fastforce


subsubsection\<open>@{term Cy} is a @{term vwalk_cycle}\<close>

lemma card_verts_length_Cy:
  assumes "card (verts G) > 1"
  shows "length Cy > 1"
  using assms card_verts_G'_2
  by (metis all_verts_G'_in_Cy card_length dual_order.antisym
      le_0_eq less_one no_arcs_impl_at_most_one_vertex
      not_le not_le_imp_less not_less_iff_gr_or_eq set_Cy_subset_G' subsetI
      vwalk_arcs_Cy_not_empty vwalk_arcs_from_length_1)

lemma vwalk_cycle_Cy_G':
  assumes "arcs G \<noteq> {}" "card (verts G) > 1"
  shows "vwalk_cycle G' Cy"
proof -
  have 1: "length Cy > 1"
    using assms card_verts_length_Cy
    by (auto)
  have "pre_digraph.cycle G' (vwalk_arcs Cy)"
    using assms pre_digraph_cycle_Cy_G'
    by auto
  then show ?thesis
    using 1 cycle_implies_vwalk_cycle head_tail_G' wf_digraph_G'
    by fastforce
qed


subsubsection\<open>@{term G'} is in \<open>UHC\<close>\<close>

lemma is_uhc_Cy_G':
  assumes "arcs G \<noteq> {}" "card (verts G) > 1"
  shows "is_uhc G' Cy"
  using assms distinct_Cy set_Cy_subset_G' all_verts_G'_in_Cy vwalk_cycle_Cy_G'
    cycle_implies_vwalk_cycle
  unfolding is_uhc_def
  by presburger

lemma arcsG_non_empty_exists_cycleG':
  assumes "arcs G \<noteq> {}" "card (verts G) > 1"
  shows "\<exists>c.  is_uhc G' c"
  using assms is_uhc_Cy_G'
  by auto

lemma in_uhc: "hc_to_uhc G \<in> uhc"
  using head_tail_G' wf_digraph_G' G'_def symmetric_G' finite_verts_G'
    arcsG_empty_exists_cycleG' in_hc arcsG_non_empty_exists_cycleG'
  unfolding uhc_def by auto

end
end