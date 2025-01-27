section\<open>Graph Auxiliaries\<close>
theory Graph_Auxiliaries
  imports
    List_Auxiliaries
    Graph_Theory.Vertex_Walk
begin

lemma last_vwalk_arcs_last_p:
  assumes "snd (last (vwalk_arcs p)) = v" "(vwalk_arcs p) \<noteq> []"
  shows "last p = v"
  using assms
proof(induction p)
  case Nil
  then show ?case
    by simp
next
  case (Cons a p)
  then show ?case
  proof(cases "p = []")
    case True
    then have "vwalk_arcs (a#p) = []"
      by simp
    then show ?thesis
      using Cons
      by auto
  next
    case False
    then have 1: "p \<noteq> []"
      by simp
    then have 2: "vwalk_arcs (a#p) = (a, hd p)#vwalk_arcs p"
      using vwalk_arcs_Cons
      by auto
    then show ?thesis
    proof(cases "vwalk_arcs p = []")
      case True
      then have 3: "(last (vwalk_arcs (a#p))) = (a, hd p)"
        using 2
        by simp
      have "last p = hd p" using True 1
        by (metis hd_rev list.distinct(1) list.exhaust rev_singleton_conv vwalk_arcs_Cons)
      then show ?thesis
        using 3 Cons False
        by auto
    next
      case False
      then have "snd (last (vwalk_arcs (a#p))) = snd (last (vwalk_arcs p))"
        by (simp add: 2)
      then have "snd (last (vwalk_arcs p)) = v"
        using Cons
        by simp
      then have 3: "last p = v"
        using Cons False
        by simp
      have "p \<noteq> []"
        by (simp add: 1)
      then have "last (a#p) = last p"
        by auto
      then show ?thesis
        using 3
        by simp
    qed
  qed
qed

lemma hd_vwalk_arcs_last_p:
  assumes "fst (hd (vwalk_arcs p)) = v" "(vwalk_arcs p) \<noteq> []"
  shows "hd p = v"
  using assms
proof(induction p)
  case Nil
  then show ?case
    by simp
next
  case (Cons a p)
  then show ?case
  proof(cases "p = []")
    case True
    then have "vwalk_arcs (a#p) = []"
      by simp
    then show ?thesis
      using Cons
      by auto
  next
    case False
    then have 1: "p\<noteq> []"
      by simp
    then have 2: "vwalk_arcs (a#p) = (a, hd p)#vwalk_arcs p"
      using vwalk_arcs_Cons
      by auto
    then have "fst (hd (vwalk_arcs (a#p))) = a"
      by simp
    then show ?thesis
      using Cons
      by simp
  qed
qed

lemma vwalk_arcs_empty_length_p:
  assumes "vwalk_arcs p = []"
  shows "length p \<le> 1"
  using assms vwalk_arcs_Cons by(induction p; fastforce)

lemma length_C_vwalk_arcs_not_empty:
  assumes "length C > 1"
  shows "vwalk_arcs C \<noteq> []"
  using assms vwalk_arcs_empty_length_p by fastforce

lemma vwalk_sublist_in_arcs:
  assumes "sublist [a, b] Cy"
  shows "(a, b) \<in> set (vwalk_arcs Cy)"
  using assms
  by (induction Cy; simp add: sublist_def)
     (metis in_set_vwalk_arcs_append1 list.set_intros(1) vwalk_arcs.simps(3))

lemma vwalk_arcs_from_length_1:
  assumes "length C = 1"
  shows "vwalk_arcs C = []"
  using assms
  by (metis length_1_set_L list.set_intros(1) vwalk_arcs.simps(1) vwalk_arcs.simps(2)
      vwalk_to_vpath.cases)

lemma at_least_two_nodes_vwalk_arcs_awalk_verts:
  assumes "length C > 1" "head G' = snd" "tail G' = fst"
  shows "(pre_digraph.awalk_verts G' u (vwalk_arcs C)) = C"
  using assms
proof(induction C arbitrary: u)
  case Nil
  then show ?case
    by auto
next
  case (Cons a C)
  then have 1: "vwalk_arcs (a#C) = (a, hd C) # vwalk_arcs C"
    by auto
  then show ?case
  proof(cases "length C > 1")
    case True
    then have 2: "pre_digraph.awalk_verts G' (hd C) (vwalk_arcs C) = C"
      using Cons
      by simp
    have "pre_digraph.awalk_verts G' u (vwalk_arcs (a#C)) =
      tail G' (a, hd C) # (pre_digraph.awalk_verts G' (head G' (a, hd C)) (vwalk_arcs C))"
      using 1
      by (simp add: pre_digraph.awalk_verts.simps(2))
    then have "pre_digraph.awalk_verts G' u (vwalk_arcs (a#C))
      = a # (pre_digraph.awalk_verts G' (head G' (a, hd C)) (vwalk_arcs C))"
      using assms
      by fastforce
    then have "pre_digraph.awalk_verts G' u (vwalk_arcs (a#C))
      = a # (pre_digraph.awalk_verts G' (hd C) (vwalk_arcs C))"
      using assms
      by fastforce
    then show ?thesis
      using 2
      by simp
  next
    case False
    then have lC: "length C = 1"
      using Cons linorder_neqE_nat
      by auto
    then have hd_C: "C = [hd C]"
      by (metis "1" list.sel(1) neq_Nil_conv vwalk_arcs.simps(2) vwalk_arcs_Cons
          vwalk_arcs_from_length_1)
    then have "vwalk_arcs (a#C) = (a, hd C) #[]"
      using 1 lC vwalk_arcs_from_length_1
      by auto
    then have 2: "pre_digraph.awalk_verts G' u (vwalk_arcs (a#C))
      = pre_digraph.awalk_verts G' u [(a, hd C)]"
      by argo
    then have 3: "... = (tail G' (a, hd C)) # (pre_digraph.awalk_verts G' (head G' (a, hd C)) [])"
      by (simp add: pre_digraph.awalk_verts.simps(2))
    then have 4: "... =  (tail G' (a, hd C)) # [(head G' (a, hd C))]"
      by (simp add: pre_digraph.awalk_verts.simps)
    then have 5: "... = a #  [(head G' (a, hd C))]"
      using assms
      by fastforce
    then have 6: "... = a # [(hd C)]"
      using assms
      by auto
    then show ?thesis
      using assms 2 3 4 5 6 hd_C
      by argo
  qed
qed

lemma arc_to_ends_G':
  assumes "head G' = snd" "tail G' = fst"
  shows "arc_to_ends G' e = e"
  using arc_to_ends_def assms by (simp add: arc_to_ends_def)

lemma arcs_ends_G':
  assumes "head G' = snd" "tail G' = fst"
  shows "arcs_ends G' = arcs G'"
  using arcs_ends_def arc_to_ends_G' assms by(auto simp add: arcs_ends_def arc_to_ends_G')

lemma if_edge_then_cycle_length_geq_2:
  assumes "(u, v) \<in> set (vwalk_arcs C)"
  shows "length C \<ge> 2"
proof(rule ccontr)
  assume "\<not> 2 \<le> length C"
  then have length_C: "length C = 1 \<or> length C = 0"
    by linarith
  then have "vwalk_arcs C = []"
    using vwalk_arcs_from_length_1
    by auto
  then show False
    using assms
    by simp
qed

lemma sublist_for_edges:
  assumes "(u, v) \<in> set (vwalk_arcs C)"
  shows "sublist [u, v] C"
  using assms
proof(induction C)
  case Nil
  then show ?case
    by auto
next
  case (Cons a C)
  then have length_C: "length C \<ge> 1"
    using if_edge_then_cycle_length_geq_2
    by fastforce
  then show ?case
  proof(cases "u = a \<and> v = hd C")
    case True
    then have "[]@[u,v] @ (tl C) = (a#C)"
      by (metis Cons.prems append_Cons append_self_conv2 list.collapse list.distinct(1)
          list.set_cases vwalk_arcs.simps(2))
    then show ?thesis
      using sublist_def by metis
  next
    case False
    then have "(u,v) \<in> set (vwalk_arcs C)"
      using Cons
      by (metis prod.inject set_ConsD vwalk_arcs.simps(1) vwalk_arcs.simps(2) vwalk_arcs_Cons)
    then have "sublist [u, v] C"
      using Cons
      by auto
    then show ?thesis
      by (simp add: sublist_cons)
  qed
qed

lemma in_sublist_impl_in_list:
  assumes "sublist a b" "x \<in> set a"
  shows "x \<in> set b"
  using assms by (metis append_Cons append_assoc in_set_conv_decomp sublist_def)

lemma empty_arcs_impl_no_cycle:
  assumes "arcs G = {}"
  shows  "\<not>(\<exists>p. pre_digraph.cycle G p)"
proof(rule ccontr)
  assume "\<not>\<not>(\<exists>p. pre_digraph.cycle G p)"
  then obtain p where 1: "pre_digraph.cycle G p"
    by auto
  then have 0: "p \<noteq> []"
    using pre_digraph.cycle_def
    by fastforce
  then have "\<exists>u. pre_digraph.awalk G u p u"
    using 1 pre_digraph.cycle_def
    by metis
  then obtain u where 2: "pre_digraph.awalk G u p u"
    by auto
  then have "set p \<subseteq> arcs G"
    using pre_digraph.awalk_def
    by fast
  then have "p = []"
    using assms
    by simp
  then show False
    using 0
    by simp
qed

lemma pre_digraph_cas_edge:
  assumes  "head G = snd" "tail G = fst"
  shows "pre_digraph.cas G v [(v, u), (u, v)] v"
  using assms  by(simp add: pre_digraph.cas.simps)

lemma edge_cycle:
  assumes "(u, v) \<in> arcs G" "(v, u) \<in> arcs G" "u \<noteq> v" "tail G = fst" "head G = snd" "wf_digraph G"
  shows "pre_digraph.cycle G [(v, u), (u, v)]"
  using assms pre_digraph_cas_edge
  unfolding pre_digraph.cycle_def pre_digraph.awalk_def wf_digraph_def pre_digraph.awalk_verts_def
  by fastforce

lemma arcs_subset_eq_verts_times_verts:
  assumes "head G = snd" "tail G = fst" "wf_digraph G"
  shows "arcs G \<subseteq> (verts G) \<times> (verts G)"
  using assms unfolding wf_digraph_def by auto

lemma not_wf_digraph_not_arcs_empty:
  assumes "\<not> wf_digraph G"
  shows "arcs G \<noteq> {}"
  using assms unfolding wf_digraph_def by auto

lemma distinct_awalk_verts_vwalk_arcs:
  assumes "head G = snd" "tail G = fst" "distinct (tl p)" "length p \<ge> 2"
  shows "distinct (tl (pre_digraph.awalk_verts G u (vwalk_arcs p)))"
  using assms at_least_two_nodes_vwalk_arcs_awalk_verts
  by (metis leD le_antisym less_one nat_neq_iff num.distinct(1) one_eq_numeral_iff
      one_le_numeral zero_less_numeral)

lemma awalk_empty_list:
  assumes "u \<in> verts G"
  shows "pre_digraph.awalk G u [] u"
  using assms unfolding pre_digraph.awalk_def by(auto simp add: pre_digraph.cas.simps)

lemma cas_vwalk_length_at_least_2:
  assumes "vwalk p G" "head G = snd" "tail G = fst" "length p \<ge> 2"
  shows "pre_digraph.cas G (hd p) (vwalk_arcs p) (last p)"
  using assms by(induction p)(auto simp add:  pre_digraph.cas.simps Suc_leI)

lemma awalk_vwalk_length_at_least_2:
  assumes "vwalk p G" "head G = snd" "tail G = fst" "length p \<ge> 2"
  shows "pre_digraph.awalk G (hd p) (vwalk_arcs p) (last p)"
  using assms
  unfolding pre_digraph.awalk_def vwalk_def
  by(auto simp add: pre_digraph.cas.simps arcs_ends_G' cas_vwalk_length_at_least_2 assms)

lemma last_pre_digraph_cas:
  assumes "pre_digraph.cas G u (p) v" "p\<noteq> []" "head G = snd" "tail G = fst"
  shows "snd (last p) = v"
  using assms by(induction p arbitrary: u)(auto simp add: pre_digraph.cas.simps)

lemma hd_pre_digraph_cas:
  assumes "pre_digraph.cas G u (p) v" "p\<noteq> []" "head G = snd" "tail G = fst"
  shows "fst (hd p) = u"
  using assms by(induction p arbitrary: u)(auto simp add: pre_digraph.cas.simps)

lemma hd_first_edge:
  assumes "length c \<ge> 2"
  shows "fst (hd (vwalk_arcs c)) = hd c"
  using assms by (metis Suc_1 Suc_le_lessD hd_vwalk_arcs_last_p length_C_vwalk_arcs_not_empty)

lemma tail_last_edge:
  assumes "length c \<ge> 2"
  shows "snd (last (vwalk_arcs c))= last c"
  using assms by (metis Suc_1 last_vwalk_arcs_last_p not_less_eq_eq vwalk_arcs_empty_length_p)

lemma hd_last_cycle:
  assumes "length c \<ge> 2" "pre_digraph.cycle G (vwalk_arcs c)" "head G = snd" "tail G = fst"
  shows "hd c = last c"
  using assms hd_first_edge hd_pre_digraph_cas last_pre_digraph_cas tail_last_edge
  unfolding pre_digraph.cycle_def pre_digraph.awalk_def by fastforce

end