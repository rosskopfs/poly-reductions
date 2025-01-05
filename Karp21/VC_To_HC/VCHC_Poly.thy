theory VCHC_Poly
  imports "../THREE_SAT_To_SC/TSTSC_Poly" "Poly_Reductions_Lib.Set_Auxiliaries" VC_To_HC
begin

subsection \<open>The reduction from \<open>VC\<close> to \<open>HC\<close> is polynomial\<close>

definition "mop_check_distinct E = SPECT [distinct E \<mapsto> length E]"

definition "mop_verts_G E k = SPECT [{Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}
          \<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e}
    \<mapsto> k + 2*(2*(length E))]"

definition "mop_arcs_G E k = SPECT [
            {(Edge v e 0, Edge v e 1)|v e. e\<in> set E \<and> v \<in> e} \<union>
            {(Edge v e 0, Edge u e 0)|u v e. e\<in>set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
            {(Edge v e 1, Edge u e 1)|u v e. e\<in> set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
            {(Edge v e1 1, Edge v e2 0)| v e1 e2. next_edge v E e1 e2} \<union>
            {(Edge v e 1, Cover n)| v e n. last_edge v e E \<and> n< k}\<union>
            {(Cover n, Edge v e 0)| v e n. first_edge v e E \<and> n < k} \<union>
            {(Cover i, Cover j) |i j.  i < k \<and> j < k}
    \<mapsto> (2*(length E)) + (2*(length E)) + (2*(length E)) + (2*(length E)) + 2*  (length E) * k + k*k]"

(*One can decide "last" for every edge in O(n) if I start from the end and keep track of an array,
whether the last occurrence has already been found*)


definition "vc_hc_alg = (\<lambda>(E,k).
  do {
    b \<leftarrow> mop_check_ugraph (set E);
    d \<leftarrow> mop_check_distinct E;
    V  \<leftarrow> mop_get_vertices (set E);
    cV \<leftarrow> mop_set_card V;
    if b \<and> k \<le> cV \<and> d then
      do {
          verts \<leftarrow> mop_verts_G E k;
          arcs \<leftarrow> mop_arcs_G E k;
          RETURNT (\<lparr>verts = verts, arcs = arcs, tail = fst, head = snd\<rparr>)
      }
    else RETURNT (\<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>)
  } )"

definition "space_verts n = 6 * n"
definition "space_edges n = 6 * n * 6 * n"
  (*at most complete Graph*)

definition "size_hc = (\<lambda>G. card (verts G) + card (arcs G))"
definition "size_vc = (\<lambda>(E,k). length E)"
definition "vc_to_hc_space n  = n + space_verts n + space_edges n + n + 2"
  (*Space for E, verts of G, edges of G, an additional list of length 2*n for last and first,
  2 for case of else*)

(*k \<le> 2*(length E) *)
definition "vc_hc_time n = 1+ n + (2 * n + 1) + 1 + (2*n + 2*(2*(n)))
    +(2*n) + (2*n) + (2*n) + (2*n) + 2* (n) *  (2*n) + (2*n)*(2*n)"


lemma finite_card_3_sets:
  assumes "finite A" "finite B" "finite C"
  shows "card (A \<union> B \<union> C) \<le> card A + card B + card C"
  using assms
  by (metis (no_types, lifting) add.commute card_Un_le le_trans nat_add_left_cancel_le)

context
  fixes E k assumes ek_def: "ugraph (set E)" "k \<le> card (\<Union> (set E))" "distinct E"
  fixes F assumes F_def: "F = \<lparr>verts = {Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union>
             {Edge v e 1|v e. e\<in> set E \<and> v \<in> e},
          arcs = {(Edge v e 0, Edge v e 1)|v e. e\<in> set E \<and> v \<in> e} \<union>
            {(Edge v e 0, Edge u e 0)|u v e. e\<in>set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
            {(Edge v e 1, Edge u e 1)|u v e. e\<in> set E \<and> v \<in> e \<and> u \<in> e  \<and> u \<noteq> v} \<union>
            {(Edge v e1 1, Edge v e2 0)| v e1 e2. next_edge v E e1 e2} \<union>
            {(Edge v e 1, Cover n)| v e n. last_edge v e E \<and> n< k}\<union>
            {(Cover n, Edge v e 0)| v e n i. first_edge v e E \<and> n < k} \<union>
            {(Cover i, Cover j) |i j.  i < k \<and> j < k},
          tail = fst, head = snd\<rparr>"
begin

lemma is_wf_digraph:
  shows "wf_digraph F"
  by (fastforce simp: F_def first_edge_def next_edge_def last_edge_def wf_digraph_def)

lemma arcs_subset_graph:
  shows "arcs F \<subseteq> (verts F) \<times> (verts F)"
proof -
  have 1: "wf_digraph F"
    using F_def is_wf_digraph by fast
  have "head F = snd" "tail F = fst"
    using F_def by auto
  then show ?thesis
    using arcs_subset_eq_verts_times_verts 1 by blast
qed

lemma ugraph_card_verts_smaller_2_length:
  shows "card (\<Union> (set E)) \<le> 2 * (length E)"
proof -
  have "\<forall>e\<in> set E. card e = 2"
    using ek_def unfolding ugraph_def by simp
  then have "card (\<Union> (set E)) \<le> 2 * card (set E)"
    by (auto simp add: card_union_if_all_subsets_card_i)
  then show ?thesis
    by (meson card_length le_trans mult_le_mono2)
qed

lemma k_smaller_2_length:
  shows "k \<le> 2 * length E"
proof -
  have "\<forall>e\<in> set E. card e = 2"
    using ugraph_def ek_def by blast
  then have "k \<le> 2* (length E)"
    using ek_def ugraph_card_verts_smaller_2_length le_trans by blast
  then show ?thesis
    using card_length le_trans mult_le_mono by blast
qed

lemma card_Cov:
  assumes "(M::('a, 'a set) hc_node set) = {Cover i|i. i< k}"
  shows "card M \<le> 2 * length E"
proof -
  define S where S_def: "S= {i|i. i<k}"
  define T::"('a, 'a set) hc_node set set" where T_def: "T = {{Cover j|j. j = i}|i. i\<in> S}"
  have card_S: "card S = k"
    using S_def by simp
  have 1: "M = \<Union> T"
    using S_def T_def assms by auto
  then have 10: "card M = card (\<Union> T)"
    by auto
  have 2: "\<forall>i. card {Cover j|j. j = i} = 1" by simp
  then have 3: "\<forall>S' \<in> T. card S' \<le> 1"
    using T_def by fastforce
  have finS: "finite S"
    using S_def by simp
  then have fin: "finite T"
    using fin_Cov T_def by simp
  have "card T \<le> card S"
    using finS card_dep_on_other_set T_def by fast
  then have cardT: "card T \<le> k"
    using card_S by blast
  have "card (\<Union> T) \<le> card T"
    using 3 card_union_if_all_subsets_card_1 fin by blast
  then have 4: "card (\<Union> T) \<le> k"
    using cardT by simp
  then show ?thesis
    using 10 k_smaller_2_length assms by fastforce
qed

lemma fin_verts:
  shows "finite (verts F)"
  using ek_def by (auto simp: F_def ugraph_def dest: finite_verts_finite_edges)

lemma fin_max_arcs:
  shows "finite ((verts F) \<times> (verts F))"
  using fin_verts by blast

lemma card_verts:
  assumes "(M1::('a, 'a set)hc_node set) = {Cover i|i. i< k}"
  shows "card (verts F) \<le> 6 * length E"
proof -
  have 1: "\<forall>e\<in> set E. card e = 2"
    using ek_def ugraph_def
    by blast
  have fin: "finite (verts F)"
    using fin_verts 1 F_def by auto
  then have fin1: "finite M1" "finite {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}"
    "finite {Edge v e 1|v e. e\<in> set E \<and> v \<in> e}"
    using assms 1 by (auto dest: finite_verts_finite_edges)
  then have 2: "card (M1 \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e})
    \<le> card M1 +card {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}+card {Edge v e 1|v e. e\<in> set E \<and> v \<in> e}"
    using finite_card_3_sets fin1 by blast
  have 3: "card M1 \<le> 2* length E"
    using card_Cov assms by blast
  have 4: "card {Edge v e 0|v e. e\<in> set E \<and> v \<in> e} \<le> 2 * length E"
    using 1 by (auto intro!: card_verts_set_Edge_i)
  have 5: "card {Edge v e 1|v e. e\<in> set E \<and> v \<in> e} \<le> 2 * length E"
    using card_verts_set_Edge_i 1 by blast
  have "verts F = (M1 \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e})"
    using F_def assms by auto
  then show ?thesis
    using 2 3 4 5 F_def by simp
qed

lemma card_arcs:
  "card (arcs F) \<le> (6 * length E) * (6 * length E)"(is "card ?A \<le> (6 * length E) * (6 * length E)")
proof -
  have a1: "\<forall>e\<in> set E. card e = 2"
    using ugraph_def ek_def by metis
  obtain B where B_def: "B = (verts F)"
    by auto
  have fB: "finite B"
    using fin_verts B_def a1 by fast
  have fBB: "finite (B \<times> B)"
    using fin_max_arcs B_def a1 by blast
  have "?A \<subseteq> B \<times> B"
    using arcs_subset_graph B_def by auto
  then have cardA: "card ?A \<le> card (B \<times> B)"
    using card_mono fBB by(auto simp add: fin_max_arcs card_mono)
  have 1: "card B \<le> 6 * length E"
    using card_verts B_def ek_def by blast
  then have "card (B \<times> B) = (card B) * (card B)"
    using card_cartesian_product by blast
  then have "card (B \<times> B) \<le>  6 * length E *card B"
    using 1 by auto
  then have "card (B \<times> B) \<le>  6 * length E * 6 * length E"
    using 1 order_subst1 by fastforce
  then have "card ?A \<le> 6 * length E * 6 * length E"
    using cardA by linarith
  then show ?thesis
    by linarith
qed

lemma aux:
  shows "card (verts F) + card (arcs F) \<le> Suc (Suc (8 * length E + 36 * length E * length E))"
proof -
  have 1: "card (verts F) \<le> 6 * length E"
    using card_verts by auto
  have "card (arcs F) \<le> 6 * length E * 6 * length E"
    using card_arcs by auto
  then show ?thesis
    using 1 by linarith
qed

end


lemma aux2:
  assumes "ugraph (set E)" "k \<le> card (\<Union> (set E))" "distinct E"
  shows "card
         ({Cover i |i. i < k} \<union>
          {Edge v e 0 |v e. e \<in> set E \<and> v \<in> e} \<union>
          {Edge v e (Suc 0) |v e.
           e \<in> set E \<and> v \<in> e}) +
        card
         ({(Edge v e 0, Edge v e (Suc 0)) |v e.
           e \<in> set E \<and> v \<in> e} \<union>
          {(Edge v e 0, Edge u e 0) |u v e.
           e \<in> set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
          {(Edge v e (Suc 0), Edge u e (Suc 0)) |u v
           e. e \<in> set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
          {(Edge v e1 (Suc 0), Edge v e2 0) |v e1
           e2. next_edge v E e1 e2} \<union>
          {(Edge v e (Suc 0), Cover n) |v e n.
           last_edge v e E \<and> n < k} \<union>
          {(Cover n, Edge v e 0) |v e n.
           first_edge v e E \<and> n < k} \<union>
          {(Cover i, Cover j) |i j. i < k \<and> j < k})
        \<le> Suc (Suc (8 * length E +
                     36 * length E * length E))"
proof -
  obtain F where f_def: "F = \<lparr>verts = {Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union>
             {Edge v e 1|v e. e\<in> set E \<and> v \<in> e},
          arcs = {(Edge v e 0, Edge v e 1)|v e. e\<in> set E \<and> v \<in> e} \<union>
            {(Edge v e 0, Edge u e 0)|u v e. e\<in>set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
            {(Edge v e 1, Edge u e 1)|u v e. e\<in> set E \<and> v \<in> e \<and> u \<in> e  \<and> u \<noteq> v} \<union>
            {(Edge v e1 1, Edge v e2 0)| v e1 e2. next_edge v E e1 e2} \<union>
            {(Edge v e 1, Cover n)| v e n. last_edge v e E \<and> n< k}\<union>
            {(Cover n, Edge v e 0)| v e n i. first_edge v e E \<and> n < k} \<union>
            {(Cover i, Cover j) |i j.  i < k \<and> j < k},
          tail = fst, head = snd\<rparr>"
    by auto
  then show ?thesis
    using assms aux by fastforce
qed

lemma vc_to_hc_size: "size_hc (vc_hc (E, k)) \<le> vc_to_hc_space (size_vc (E, k))"
  by (auto simp: size_vc_def vc_hc_def vc_to_hc_space_def size_hc_def
       space_verts_def space_edges_def aux2)

lemma time_ugraph_to_hc:
  assumes "ugraph (set E)" "k \<le> card (\<Union> (set E))" "distinct E"
  shows "2 * card (set E) + (k + (2 * length E * k + k * k))
    \<le> 4 * length E + 8 * (length E * length E)"
proof -
  have 1: "k \<le> 2* length E"
    using assms k_smaller_2_length by blast
  have "2 * card (set E) + (k + (2 * length E * k + k * k)) \<le>
    2 * card (set E) + ((2*length E) + (2 * length E * k + k * k))"
    by(auto simp add: 1)
  also have "... \<le> 2 * length E + ((2*length E) + (2 * length E * k + k * k))"
    by (simp add: card_length)
  also have "... \<le> 4 * length E + (2 * length E * k + k * k)"
    by auto
  also have "... \<le> 4 * length E + (2 * length E * (2 * length E)+ k * k)"
    using 1 by force
  also have "... \<le> 4 * length E + (4 * length E * length E + (2 * length E) * k)"
    using 1 by simp
  also have "... \<le> 4 * length E + (4 * length E * length E + 2 * length E * 2 * length E)"
    using 1 by fastforce
  also have "... \<le> 4 * length E + 8 * length E * length E"
    by simp
  finally show ?thesis
    by linarith
qed

lemma vc_to_hc_refines:
  "vc_hc_alg (E, k) \<le> SPEC (\<lambda>y. y = (vc_hc (E, k))) (\<lambda>_. vc_hc_time (size_vc (E, k)))"
  unfolding SPEC_def
  unfolding vc_hc_alg_def vc_hc_def
    mop_check_ugraph_def mop_check_distinct_def mop_get_vertices_def mop_set_card_def
    mop_verts_G_def mop_arcs_G_def
  apply(rule T_specifies_I)
  apply(vcg' \<open>-\<close> rules: T_SPEC )
  apply(auto simp: vc_hc_time_def one_enat_def size_vc_def time_ugraph_to_hc)
  by (simp add: card_length mult_le_mono trans_le_add1)+

theorem vc_to_hc_ispolyred: "ispolyred vc_hc_alg vertex_cover_list hc size_vc size_hc"
  unfolding ispolyred_def
  apply(rule exI[where x=vc_hc])
  apply(rule exI[where x=vc_hc_time])
  apply(rule exI[where x=vc_to_hc_space])
  apply(safe)
  subgoal using vc_to_hc_refines by blast
  subgoal using vc_to_hc_size by blast
  subgoal unfolding poly_def vc_hc_time_def apply(rule exI[where x=2]) by auto
  subgoal unfolding poly_def vc_to_hc_space_def space_verts_def space_edges_def
    apply(rule exI[where x=2]) by auto
  subgoal using is_reduction_vc_to_hc .
  done

end