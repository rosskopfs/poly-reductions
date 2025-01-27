theory VC_To_FAS
  imports
    Reductions
    FAS_Definition
    IS_To_VC
    Set_Auxiliaries
begin

(* helper lemmas *)

lemma distinct_append1:
  assumes "y \<notin> set xs" "distinct xs"
  shows "distinct (xs@[y])"
  using assms by simp

lemma hd_distinct_not_in_tl:
  assumes "distinct xs"
  shows "hd xs \<notin> set (tl xs)"
  using assms by (cases xs) auto


lemma vimage_a_doubleton_to_pair:
  shows  "(\<lambda>(u, v). {u, v}) -` {{x,y}} = {(x,y), (y,x)}"
  unfolding vimage_def
  by (cases "x = y") auto

lemma finite_vimage_a_doubleton_to_pair:
  "finite ((\<lambda>(u, v). {u, v}) -` {s})"
  using  vimage_a_doubleton_to_pair[THEN arg_cong, where ?f = finite]
         not_finite_existsD
  unfolding vimage_def
  by fast

lemma fin_f_doubleton_ss:
  assumes "finite E"
  shows "finite {f u v| u v. {u, v} \<in> E}"
  using finite_finite_vimage_IntI[where ?A = UNIV]
        finite_vimage_a_doubleton_to_pair assms
        [[simproc add: finite_Collect]]
  by auto

(* graphs *)

lemma (in wf_digraph) awalk_verts_appendI:
  assumes "awalk u (p1 @ p2) v"
          "w = last (awalk_verts u p1)"
  shows "awalk_verts u (p1 @ p2) = awalk_verts u p1 @ tl (awalk_verts w p2)"
  using awalk_verts_append assms
  by blast

(** this is the same definition as cycle but specifies the start vertex **)
definition (in pre_digraph) cycle_start   where
  "cycle_start p x \<equiv> awalk x p x  \<and> distinct (tl (awalk_verts x p)) \<and> p \<noteq> []"

lemma (in wf_digraph) rotate1_cycle_start:
  assumes  "cycle_start (e#es) x"
  shows    "cycle_start (es@[e]) (head G e)"
proof -
  let ?y = "head G e"
  have *: "awalk ?y (es @ [e]) ?y"  using assms unfolding cycle_start_def
    by (intro awalk_appendI[where ?v = "tail G e"] arc_implies_awalk)
       (auto simp add: awalk_Cons_iff)
  moreover then have **: "awalk_verts ?y (es @ [e]) = awalk_verts ?y es @ tl (awalk_verts x [e])"
    using assms by (intro awalk_verts_appendI)
                   (auto simp add: cycle_start_def awalk_Cons_iff)
  moreover have "distinct (tl (awalk_verts ?y (es @ [e])))"
  proof -
    have "distinct (awalk_verts ?y es)" using assms unfolding cycle_start_def by simp
    moreover then have "?y \<notin> set (tl (awalk_verts ?y es))"
      using * hd_distinct_not_in_tl by fastforce
    moreover have ***: "tl (awalk_verts ?y (es @ [e])) = tl (awalk_verts ?y es) @ [?y]"
      by (simp add: "**")
    ultimately show ?thesis
      using distinct_tl unfolding *** by auto
  qed
  then show ?thesis unfolding cycle_start_def
    using calculation by fastforce
qed


(** define the reduction **)

definition H where
  "H E \<equiv> \<lparr> verts = (\<Union>E) \<times> {False, True},
           arcs = {((u, False), (u, True)) |u. u \<in> \<Union> E }
                \<union> {((u, True), (v, False)) |u v. {u,v} \<in> E},
           tail = fst, head = snd \<rparr>"

definition MALFORMED_GRAPH where
    "MALFORMED_GRAPH  =  \<lparr> verts = {},
                           arcs = {((undefined, False),(undefined, False))},
                           tail = fst, head = fst \<rparr>"
lemma isMALFORMED_GRAPH:
     "\<not> wf_digraph MALFORMED_GRAPH"
  by (simp add: MALFORMED_GRAPH_def wf_digraph_def)

definition vc_to_fas where
  "vc_to_fas \<equiv> \<lambda>(E,K). (if K \<le> card (\<Union>E) \<and> (\<forall>e \<in> E. card e = 2)
                        then H E else MALFORMED_GRAPH, K)"


(** properties of H and its cycles **)

lemma wf_H: "wf_digraph (H E)"
  unfolding wf_digraph_def H_def
  using insert_commute by auto

(*
   given a cycle starting at (u,b),
   gives a cycle (e'#es')  starting with the next node
*)
lemma cycle_start_at_next:
  assumes "pre_digraph.cycle_start (H E) (e#es) (u,b)"
  shows   "\<exists>v e' es'. e = ((u,b),(v,\<not> b))
         \<and> (\<not> b \<longrightarrow> (u = v))
         \<and> set (e#es) = set (e'#es')
         \<and> pre_digraph.cycle_start (H E) (e'#es') (v, \<not> b)"
proof -
  have e_edge: "e \<in> arcs (H E)"
    by (meson assms pre_digraph.cycle_start_def wf_digraph.awalk_Cons_iff wf_H)
  have "tail (H E) e = (u,b)"
    using assms pre_digraph.cas_simp pre_digraph.awalk_def
    unfolding pre_digraph.cycle_start_def by fastforce
  then obtain v b2 where e_content: "e = ((u,b),(v,b2))" "head (H E) e = (v, b2)"
    using assms unfolding pre_digraph.cycle_start_def pre_digraph.awalk_def H_def
    using prod.collapse select_convs by force
  moreover then have "b2 = (\<not> b)" using e_edge unfolding H_def
    by (cases b) auto
  moreover then have "pre_digraph.cycle_start (H E) (es @ [e]) (v,\<not> b)"
    using wf_digraph.rotate1_cycle_start[OF wf_H] e_content assms
    unfolding pre_digraph.cycle_start_def
    by fastforce
  moreover have "\<not> b \<Longrightarrow> u = v"
    using e_content e_edge unfolding H_def  by force
  moreover obtain e' es' where e'_def: "e'#es' = es@[e]"
    by (cases "es@[e]") auto
  ultimately show ?thesis
    by (intro exI[of _ v] exI[of _ e'] exI[of _ es'] conjI)
       (meson list.set_intros | simp)+
qed


lemma cycle_strcture:
  assumes "pre_digraph.cycle (H E) p"
  shows   "\<exists>u v. ((u, True),(v,False)) \<in> set p
                \<and> ((u, False),(u, True)) \<in> set p
                \<and> ((v, False), (v, True)) \<in> set p"
proof -
  obtain u' b' e' es' where  c_start': "pre_digraph.cycle_start (H E) (e'#es') (u',b')"
                                   and "set p = set (e' # es')"
    using assms unfolding pre_digraph.cycle_def pre_digraph.cycle_start_def by (cases p) auto
  then obtain u e es where c_start: "pre_digraph.cycle_start (H E) (e#es) (u,False)"
                                and "set p = set (e # es)"
    using cycle_start_at_next[OF c_start'] by (cases b') auto
  then show ?thesis using cycle_start_at_next list.set_intros by smt
qed

(** correctness proof **)

lemma vc_to_fas_soundness:
  assumes "(E, k) \<in> vertex_cover"
  shows "(vc_to_fas (E, k)) \<in> feedback_arc_set"
proof -
  obtain V_C where finE: "finite E" and card2: "(\<forall>e\<in>E. card e = 2)"
    and "V_C \<subseteq> \<Union> E" and "k \<le> card (\<Union> E)"
    and "card V_C \<le> k"  and "is_vertex_cover E V_C"
    using assms by fastforce
  define S where "S \<equiv> { ((u, False), (u, True)) |u. u \<in> V_C }"
  have "(H E, k) \<in> feedback_arc_set"
  proof (intro feedback_arc_set_cert[of S])

    show "S \<subseteq> arcs (H E)"
      using \<open>V_C \<subseteq> \<Union> E\<close>
      unfolding H_def S_def by fastforce

    have "finite (\<Union> E)"
      using finE card2 card.infinite
      by (intro finite_Union) fastforce+
    then show "fin_digraph (H E)"
      using finE wf_H unfolding H_def
      by (intro wf_digraph.fin_digraphI) (auto simp add: Union_eq fin_f_doubleton_ss)

    have "card S = card V_C"
      unfolding S_def
      by (intro card_Collect_mem) (simp add: inj_on_def)

    then show "card S \<le> k"
      using \<open>card V_C \<le> k\<close>  by argo

    show "\<forall> p. pre_digraph.cycle (H E) p \<longrightarrow> (\<exists> e \<in> S. e \<in> set p)"
    proof (intro allI impI)
      fix p assume p_cycle: "pre_digraph.cycle (H E) p"
      then obtain u v  where uv_def:
        "((u, True), (v, False)) \<in> set p"
        "((u, False), (u, True)) \<in> set p"
        "((v, False), (v, True)) \<in> set p"
        using cycle_strcture by blast
      then have "((u, True), (v, False)) \<in> arcs (H E)"
        by (meson p_cycle pre_digraph.awalk_def pre_digraph.cycle_def subsetD)
      then have "{u, v} \<in> E" unfolding H_def by simp
      then have  "(u \<in>  V_C) \<or> (v \<in> V_C)"
        using \<open>is_vertex_cover E V_C\<close> is_vertex_cover_def
        by fastforce
      then show "(\<exists>e\<in>S. e \<in> set p)" using S_def uv_def by blast
    qed
  qed
  then show ?thesis
    unfolding  vc_to_fas_def
    by (simp add: \<open>k \<le> card (\<Union> E)\<close> card2)
qed


lemma vc_to_fas_completeness:
  assumes "(vc_to_fas (E, k)) \<in> feedback_arc_set"
  shows "(E, k) \<in> vertex_cover"
proof (cases "k \<le> card (\<Union>E) \<and> (\<forall>e \<in> E. card e = 2)")
  case True
  obtain S where S_def: "S \<subseteq> arcs (H E)" "card S \<le> k" "fin_digraph (H E)"
    "\<forall> p. pre_digraph.cycle (H E) p \<longrightarrow> (\<exists> e \<in> S. e \<in> set p)"
    using assms True
    unfolding feedback_arc_set_def vc_to_fas_def by auto

  define V where V_def: "V \<equiv>  (fst \<circ> fst) ` S"

  have V_def2: "V = {u. ((u, False), (u, True)) \<in> S }
                  \<union> {u |u v. ((u, True), (v, False)) \<in> S}"
  proof -
    have *: "S = {((u, False), (u, True)) |u.   ((u, False), (u, True)) \<in> S}
               \<union> {((u, True), (v, False)) |u v. ((u, True), (v, False)) \<in> S}"
      using \<open>S \<subseteq> arcs (H E)\<close> unfolding H_def by auto
    show ?thesis unfolding V_def
      by (subst *, subst image_Un) force
  qed

  have "finite E"
    using  fin_digraph.finite_verts[OF \<open>fin_digraph (H E)\<close>]
           finite_UnionD finite_cartesian_productD1
    unfolding H_def by auto
  then have "ugraph E"
    by (simp add: True ugraph_def)

  moreover have "V \<subseteq> \<Union> E"
    using \<open>S \<subseteq> arcs (H E)\<close> V_def2 unfolding H_def by auto
  moreover have "k \<le> card (\<Union> E)" using True by auto
  moreover have "card V \<le> k" unfolding V_def
    using card_image_le \<open>card S \<le> k\<close>  dual_order.trans
      finite_subset[OF \<open>S \<subseteq> arcs (H E)\<close> fin_digraph.finite_arcs[OF \<open>fin_digraph (H E)\<close>]]
    by fast
  moreover have "is_vertex_cover E V"
  proof (unfold is_vertex_cover_def, intro ballI)
    fix e assume e_def: "e \<in> E"
    then obtain u v where uv_def: "e = {u, v}"
      using \<open>ugraph E\<close> unfolding ugraph_def  by (meson card_2_iff)
    then show "\<exists> v \<in> V. v \<in> e"
    proof -
      let ?cycle = "if u = v then [((u, False), (u, True)), ((u, True), (u, False))]
                             else [((u, False), (u, True)), ((u, True), (v, False)),
                                   ((v, False), (v, True)), ((v, True), (u, False))]"
      have "pre_digraph.cycle_start (H E) ?cycle (u,False)"
        unfolding pre_digraph.cycle_start_def pre_digraph.awalk_def H_def
        using uv_def e_def
        by (auto simp add: insert_commute pre_digraph.cas.simps pre_digraph.awalk_verts.simps)
      then have "(\<exists> e \<in> S. e \<in> set ?cycle)"
        unfolding pre_digraph.cycle_start_def
        using S_def pre_digraph.cycle_def by blast
      then show ?thesis using V_def2 uv_def
        by (cases "u = v") (simp,auto)
    qed
  qed
  ultimately show ?thesis unfolding vertex_cover_def by blast
next
  case False
  have "(MALFORMED_GRAPH,k) \<notin> feedback_arc_set"
    unfolding feedback_arc_set_def
    using fin_digraph_def isMALFORMED_GRAPH by fastforce
  then show ?thesis using assms False
    unfolding vc_to_fas_def by auto
qed

theorem is_reduction_vc_to_fas: "is_reduction vc_to_fas vertex_cover feedback_arc_set"
  unfolding is_reduction_def
  using vc_to_fas_soundness vc_to_fas_completeness
  by fast

end
