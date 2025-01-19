theory VC_To_FNS
  imports Main Graph_Theory.Digraph Graph_Theory.Arc_Walk
    "../VC_Set_To_VC_List/VC_Set_To_VC_List" "Poly_Reductions_Lib.Graph_Auxiliaries"
begin

section\<open>VC To FNS\<close>
subsubsection\<open>Preliminaries\<close>

definition "del_verts G vs = foldr (\<lambda>v G. pre_digraph.del_vert G v) vs G"

lemma e_in_arcs_del_verts_e_in_arcs:
  assumes "e \<in> arcs (del_verts G R)"
  shows "e \<in> arcs G"
  using assms unfolding del_verts_def
  by(induction R arbitrary: G)(auto simp add: pre_digraph.arcs_del_vert)

lemma foldr_del_vert:
  shows "(pre_digraph.del_vert (foldr (\<lambda>v G. pre_digraph.del_vert G v) R G) v) =
    (foldr (\<lambda>v G. pre_digraph.del_vert G v) (v#R) G)"
  by(induction R arbitrary: G)(auto)

lemma e_not_in_del_vert_head_e:
  shows "e \<notin> arcs (pre_digraph.del_vert G (head G e))"
  unfolding pre_digraph.del_vert_def by simp

lemma head_del_verts_eq_head_before:
  shows "head (del_verts G R) e = head G e"
  unfolding del_verts_def pre_digraph.del_vert_def by(induction R arbitrary: G)(auto)

lemma tail_del_verts_eq_tail_before:
  shows "tail (del_verts G R) e = tail G e"
  unfolding del_verts_def pre_digraph.del_vert_def by(induction R arbitrary: G)(auto)

lemma e_in_arcs_del_verts_impl_not_vertex_in_E:
  assumes "e \<in> arcs (del_verts G R)"
  shows "head G e \<notin> set R \<and> tail G e \<notin> set R"
  using assms tail_del_verts_eq_tail_before head_del_verts_eq_head_before
  by (induction R arbitrary: G) (force simp add: pre_digraph.arcs_del_vert del_verts_def)+

lemma e_in_arcs_not_in_R:
  assumes "e \<in> arcs G" "head G e \<notin> set R" "tail G e \<notin> set R"
  shows "e \<in> arcs (del_verts G R)"
  using assms
proof(induction R arbitrary: G)
  case Nil
  then show ?case
    unfolding del_verts_def
    by auto
next
  case (Cons a R)
  then have e_in: "e \<in> arcs (pre_digraph.del_vert G a)"
    by (simp add: pre_digraph.del_vert_def)
  then have "e \<in> arcs (foldr (\<lambda> v G. pre_digraph.del_vert G v) R G)"
    using Cons
    unfolding del_verts_def
    by (simp add: pre_digraph.head_del_vert pre_digraph.tail_del_vert)
  then show ?case
    by (metis (mono_tags, lifting) e_in del_verts_def
        foldr_del_vert head_del_verts_eq_head_before mem_Collect_eq pre_digraph.arcs_del_vert
        tail_del_verts_eq_tail_before)
qed

subsubsection \<open>Main Definitions\<close>

definition
  "is_fns (G::('a,'b) pre_digraph) (R:: 'a list)  \<equiv> \<not>(\<exists>p. pre_digraph.cycle (del_verts G R) p) "

definition
  "fns \<equiv> {(G, k). \<exists>R. wf_digraph G \<and> length R < k \<and> is_fns G R \<and> set R \<subseteq> verts G}"

definition "vc_to_fns \<equiv> \<lambda>(E, k).(if ugraph E \<and> k \<le> card (\<Union> E)
  then (\<lparr>verts = {v. v \<in> \<Union> E}, arcs = {(u, v)| u v. {u, v} \<in> E}, tail = fst, head = snd \<rparr>, k+1)
  else (\<lparr>verts = {}, arcs = {}, tail = fst, head = snd \<rparr>, 0))"

lemma else_not_in_fns:
  shows "(\<lparr>verts = {}, arcs = {}, tail = fst, head = snd \<rparr>, 0) \<notin> fns"
  using fns_def by auto


subsection \<open>From VC to FNS\<close>

context
  fixes E k assumes in_vc: "(E, k) \<in> vertex_cover"
  fixes G k' assumes G_def: "(G, k') = vc_to_fns (E, k)"
  fixes Cov assumes Cov_def: "Cov \<subseteq> \<Union> E" "card Cov \<le> k" "is_vertex_cover E Cov"
  fixes R assumes R_def: "R = set_to_list Cov"
begin

lemma G_def_2:
  shows "G = \<lparr>verts = {v. v \<in> \<Union> E}, arcs = {(u, v)| u v. {u, v} \<in> E}, tail = fst, head = snd\<rparr>"
proof -
  have ugraph: "ugraph E" "k \<le> card (\<Union> E)"
    using in_vc vertex_cover_def
    by auto
  then have "vc_to_fns (E, k)
    = (\<lparr>verts = {v. v \<in> \<Union> E}, arcs = {(u, v)| u v. {u, v} \<in> E}, tail = fst, head = snd \<rparr>, k+1)"
    by(auto simp add: vc_to_fns_def)
  then show ?thesis
    using G_def
    by simp
qed

lemma wf_digraph_G:
  shows "wf_digraph G"
  using G_def_2 by(auto simp add: wf_digraph_def)

lemma ugraph_E_card_k:
  shows "ugraph E" "k \<le> card (\<Union> E)"
  using in_vc vertex_cover_def by auto

lemma finite_E:
  shows "finite (\<Union> E)"
  using ugraph_vertex_set_finite ugraph_E_card_k by auto

lemma k_k':
  shows "k' = k+1"
  using ugraph_E_card_k G_def unfolding vc_to_fns_def by simp

lemma finite_Cov:
  shows "finite Cov"
  using Cov_def finite_E by (meson finite_subset)

lemma distinct_R:
  shows "distinct R"
  using R_def set_to_list_def distinct_set_to_list finite_Cov by auto

lemma card_R_equal:
  shows "length R = card Cov"
  using R_def set_to_list_def distinct_R distinct_card finite_Cov set_set_to_list by fastforce

lemma card_R:
  shows "length R < k+1"
  using card_R_equal Cov_def by simp

lemma in_arcs_G_imp_in_set_R:
  assumes "e \<in> arcs G"
  shows "head G e \<in> set R \<or> tail G e \<in> set R"
proof -
  obtain v u where vu_def: "v = head G e" "u = tail G e"
    by auto
  then obtain e' where e'_def: "e' = {v, u}"
    by auto
  then have "e' \<in> E"
    using G_def_2 assms vu_def
    by(auto simp add: G_def_2 insert_commute)
  then have "u \<in> Cov \<or> v \<in> Cov"
    using Cov_def e'_def
    unfolding is_vertex_cover_def
    by fast
  then show ?thesis
    using vu_def R_def finite_Cov set_set_to_list
    by auto
qed

lemma arcs_del_g_empty:
  shows "arcs (del_verts G R) = {}"
  using in_arcs_G_imp_in_set_R e_in_arcs_del_verts_impl_not_vertex_in_E
    e_in_arcs_del_verts_e_in_arcs
  by fast

lemma is_fns_R:
  shows "is_fns G R"
  using empty_arcs_impl_no_cycle arcs_del_g_empty is_fns_def by metis

lemma R_subset_verts:
  shows "set R \<subseteq> verts G"
  using R_def Cov_def G_def_2 set_set_to_list finite_Cov unfolding set_to_list_def by auto

lemma in_fns_context:
  shows "vc_to_fns (E, k) \<in> fns"
  using fns_def card_R wf_digraph_G is_fns_R k_k' G_def R_subset_verts by fastforce

end


subsection\<open>From FNS to VC\<close>

context
  fixes G k' assumes G_def: "(G, k') \<in> fns"
  fixes E k assumes Ek_def: "(G, k') = vc_to_fns (E, k)"
  fixes R assumes R_def: "is_fns G R" "length R < k'" "set R \<subseteq> verts G"
  fixes Cov assumes Cov_def: "Cov = set R"
begin

lemma cardE_k:
  shows "k \<le> card (\<Union> E)"
  using Ek_def G_def by(auto split: if_split_asm simp: else_not_in_fns vc_to_fns_def)

lemma ugraphE:
  shows "ugraph E"
  using Ek_def G_def unfolding vc_to_fns_def by(auto split: if_split_asm simp add: else_not_in_fns)

lemma G_def_3:
  shows "G = \<lparr>verts = {v. v \<in> \<Union> E}, arcs = {(u, v)| u v. {u, v} \<in> E},
    tail = fst, head = snd\<rparr>" "k' = k+1"
  using Ek_def G_def
  by(auto split: if_split_asm simp add: else_not_in_fns vc_to_fns_def)

lemma wf_digraph_G_2:
  shows "wf_digraph G"
  using G_def fns_def by auto

lemma e_in_E_e_explicit:
  assumes "e \<in> E"
  shows "\<exists>u v. e = {u ,v} \<and> u \<noteq> v"
  using ugraphE assms unfolding ugraph_def by (simp add: e_in_E_e_explicit)

lemma G_symmetric:
  assumes "(u, v) \<in> arcs G"
  shows "(v, u) \<in> arcs G"
  using assms G_def_3 by (auto simp add: assms G_def_3 insert_commute)

lemma wf_digraph_del_verts:
  assumes "wf_digraph G'"
  shows "wf_digraph (del_verts G' E')"
  using assms unfolding del_verts_def
  by(induction E' arbitrary: G')(auto simp add: wf_digraph.wf_digraph_del_vert)

lemma cycle_in_R:
  assumes "(u, v) \<in> arcs G" "(v, u) \<in> arcs G" "u \<noteq> v"
  shows "u \<in> set R \<or> v \<in> set R"
proof(rule ccontr)
  assume "\<not>(u \<in> set R \<or> v \<in> set R)"
  then have "u \<notin> set R \<and> v \<notin> set R"
    by auto
  then have 1: "(v, u) \<in> arcs (del_verts G R)"  "(u, v) \<in> arcs (del_verts G R)" "u \<noteq> v"
    using G_def_3 e_in_arcs_not_in_R assms
    by force+
  have 2: "tail (del_verts G R) = fst" "head (del_verts G R) = snd"
    using G_def_3
    by(auto simp add: tail_del_verts_eq_tail_before head_del_verts_eq_head_before)
  have "wf_digraph (del_verts G R)"
    using wf_digraph_G_2 wf_digraph_del_verts
    by auto
  then have "pre_digraph.cycle (del_verts G R) [(v, u), (u, v)]"
    using edge_cycle 1 2
    by fast
  then show False
    using R_def is_fns_def
    by blast
qed

lemma G_fst_snd:
  shows "tail G = fst" "head G = snd"
  using G_def_3 by auto

lemma in_arcs_one_in_R:
  assumes "e \<in> arcs G" "e = (u, v)" "u \<noteq> v"
  shows "u \<in> set R \<or> v \<in> set R"
  using assms G_symmetric cycle_in_R by blast

lemma Cov_properties:
  shows "Cov \<subseteq> \<Union> E" "card Cov \<le> k" "is_vertex_cover E Cov"
proof -
  have "set R \<subseteq> \<Union> E"
    using R_def G_def_3
    by auto
  then show "Cov \<subseteq> \<Union> E"
    using Cov_def
    by simp
next
  have "length R \<le> k"
    using R_def G_def_3
    by linarith
  then show "card Cov \<le> k"
    using Cov_def card_length dual_order.trans
    by blast
next
  have "\<forall>e\<in>E. \<exists>v\<in>Cov. v \<in> e"
  proof
    fix e assume 1: "e \<in> E"
    then obtain u v where 2: "e = {u, v}" "u \<noteq> v"
      using e_in_E_e_explicit by metis
    then have "(u, v) \<in> arcs G"
      using G_def_3 1
      by auto
    then have "u \<in> set R \<or> v \<in> set R"
      using in_arcs_one_in_R 2
      by simp
    then show "\<exists>v\<in> Cov. v\<in> e"
      using Cov_def 2
      by auto
  qed
  then show "is_vertex_cover E Cov"
    using is_vertex_cover_def
    by auto
qed

lemma in_vc_context:
  shows "(E, k) \<in> vertex_cover"
  using vertex_cover_def ugraphE cardE_k Cov_properties by blast

end


subsection\<open>Main theorem\<close>

lemma in_fns:
  assumes "(E, k) \<in> vertex_cover"
  shows "vc_to_fns (E, k) \<in> fns"
proof -
  obtain G k' where 1: "(G, k') = vc_to_fns (E, k)"
    using assms
    by (metis surjective_pairing)
  obtain Cov where 2: "Cov \<subseteq> \<Union> E" "card Cov \<le> k" "is_vertex_cover E Cov"
    using assms
    by(auto simp add: vertex_cover_def)
  obtain R where 3: "R = set_to_list Cov"
    by simp
  then show ?thesis
    using 1 2 3 in_fns_context assms
    by blast
qed

lemma in_vc:
  assumes "vc_to_fns (E ,k) \<in> fns"
  shows "(E, k) \<in> vertex_cover"
proof -
  obtain G k' where 1: "(G, k') = vc_to_fns (E, k)"
    by (metis surj_pair)
  then obtain R where 2: "is_fns G R" "length R < k'" "set R \<subseteq> verts G"
    using assms fns_def
    by(auto simp add: assms fns_def)
  then obtain Cov where 3: "Cov = set R"
    by auto
  then show ?thesis
    using in_vc_context 1 2 3 assms
    by metis
qed

theorem is_reduction_vc_to_fns:
  "is_reduction vc_to_fns vertex_cover fns"
  unfolding is_reduction_def using in_vc in_fns by auto

end
