subsection \<open>Vertex Cover to Set Cover\<close>
theory VC_To_SC
  imports
    IS_To_VC
    SC_Definition
begin

definition
  "vc_sc \<equiv> \<lambda>(E, k).
    if ugraph E \<and> k \<le> card (\<Union> E) then ({{e. e \<in> E \<and> v \<in> e} | v. v \<in> \<Union>E}, k)
    else ({{undefined}}, 0)"

theorem is_reduction_vc_sc:
  "is_reduction vc_sc vertex_cover set_cover"
  unfolding is_reduction_def vc_sc_def vertex_cover_def set_cover_def
    vertex_cover_pred_def set_cover_pred_def
  apply clarsimp
  apply safe
  subgoal for E k V
    apply (rule bexI[where x = "{{e \<in> E. v \<in> e} |v. v \<in> V}", rotated])
    subgoal
      by fastforce
    apply (intro conjI)
    subgoal
      apply safe
      subgoal for e _ v
        by auto
      subgoal for e _ v e'
        unfolding is_vertex_cover_def by simp (metis mem_Collect_eq)
      done
    subgoal
      unfolding setcompr_eq_image
      by (rule order.trans, rule card_image_le) (auto dest: ugraph_vertex_set_finite finite_subset)
    done
  subgoal premises prems for E k S
  proof -
    define vv where "vv \<equiv> \<lambda>X. SOME v. X = {e \<in> E. v \<in> e}"
    let ?S = "vv ` S"
    have *: "{e \<in> E. v \<in> e} = {e \<in> E. vv {e \<in> E. v \<in> e} \<in> e}" for v
      unfolding vv_def by (rule someI) auto
    then have "vv {e \<in> E. v \<in> e} \<in> \<Union>E" if "{e \<in> E. v \<in> e} \<noteq> {}" for v
      using that by auto
    then have 1: "vv X \<in> \<Union>E" if "X \<in> S" for X
      using \<open>S \<subseteq> _\<close> that by blast
    from \<open>ugraph _\<close> have "finite E"
      unfolding ugraph_def by auto
    moreover have "S \<subseteq> Pow E"
      by (rule order.trans, rule prems) auto
    ultimately have "finite S"
      using \<open>finite E\<close> finite_subset by auto
    have "is_vertex_cover E ?S"
      unfolding is_vertex_cover_def
    proof safe
      fix e :: "'a set" assume "e \<in> E"
      from \<open>e \<in> E\<close> \<open>ugraph E\<close> have "card e = 2"
        unfolding ugraph_def by auto
      then obtain v where "v \<in> e"
        by force
      with \<open>\<Union> S = _\<close> \<open>e \<in> E\<close> have "e \<in> \<Union> S"
        by auto
      with \<open>S \<subseteq> {_ | _. _}\<close> obtain v where "{e \<in> E. v \<in> e} \<in> S" "v \<in> e"
        by auto
      with *[of v] \<open>e \<in> E\<close> show "\<exists>v\<in>vv ` S. v \<in> e"
        by auto
    qed
    have "?S \<subseteq> \<Union> E"
      by (auto dest: 1)
    moreover have "card ?S \<le> k"
      using \<open>card S \<le> _\<close> \<open>finite S\<close> by (auto intro: card_image_le order.trans)
    moreover have "is_vertex_cover E ?S"
      using prems
      unfolding is_vertex_cover_def
      apply auto
      subgoal premises prems for e
      proof -
        from \<open>e \<in> E\<close> \<open>ugraph E\<close> have "card e = 2"
          unfolding ugraph_def by auto
        then obtain v where "v \<in> e"
          by force
        with \<open>\<Union> S = _\<close> \<open>e \<in> E\<close> have "e \<in> \<Union> S"
          by auto
        with \<open>S \<subseteq> {_ | _. _}\<close> obtain v where "{e \<in> E. v \<in> e} \<in> S" "v \<in> e"
          by auto
        with *[of v] \<open>e \<in> E\<close> show ?thesis
          by auto
      qed
      done
    ultimately show ?thesis
      by auto
  qed
  by (simp add: finite_subset)+

end
