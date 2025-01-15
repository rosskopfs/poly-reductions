section \<open>\<open>Independent Set\<close> To \<open>Set Cover\<close>\<close>

theory IS_To_SC
  imports "../Reductions" IS_Definition
begin

subsection \<open>Preliminaries\<close>

definition
  "is_vertex_cover E V \<equiv> \<forall> e \<in> E. \<exists> v \<in> V. v \<in> e"

definition
  "vertex_cover \<equiv>
  {(E, k). \<exists>V. ugraph E \<and> V \<subseteq> \<Union> E \<and> k \<le> card (\<Union> E) \<and> card V \<le> k \<and> is_vertex_cover E V}"

definition
  (* "set_cover \<equiv> {(T, k). \<exists> S \<subseteq> T. \<Union> S = \<Union> T \<and> card S \<le> k \<and> finite T \<and> finite (\<Union> T)}" *)
  "set_cover \<equiv> {(T, k). \<exists> S \<subseteq> T. \<Union> S = \<Union> T \<and> card S \<le> k}"

definition
  "is_vc \<equiv> \<lambda>(E, k). if k > card (\<Union> E) then (E, k) else (E, card (\<Union> E) - k)"

definition
  "vc_sc \<equiv> \<lambda>(E, k).
    if ugraph E \<and> k \<le> card (\<Union> E) then ({{e. e \<in> E \<and> v \<in> e} | v. v \<in> \<Union>E}, k)
    else ({{undefined}}, 0)"

lemma is_independent_set_is_vertex_cover:
  "is_independent_set E V \<longleftrightarrow> is_vertex_cover E ((\<Union>E) - V)" if "ugraph E"
  using that unfolding is_independent_set_def is_vertex_cover_def
proof safe
  fix e
  assume A: "ugraph E" "\<forall>u\<in>V. \<forall>v\<in>V. {u, v} \<notin> E" "e \<in> E"
  then obtain u v where "e = {u, v}"
    unfolding ugraph_def by (metis card_eq_SucD numeral_2_eq_2)
  with A(2,3) consider "u \<notin> V" "v \<notin> V" | "u \<in> V" "v \<in> \<Union> E - V" | "v \<in> V" "u \<in> \<Union> E - V"
    by auto
  then show "\<exists>v\<in>\<Union> E - V. v \<in> e"
    using \<open>e \<in> E\<close> unfolding \<open>e = _\<close> by cases auto
next
  fix u v
  assume "\<forall>e\<in>E. \<exists>v\<in>\<Union> E - V. v \<in> e" "u \<in> V" "v \<in> V" "{u, v} \<in> E"
  then show False
    by force
qed

lemma ugraph_vertex_set_finite:
  assumes "ugraph E"
  shows "finite (\<Union>E)"
  using assms by (auto 4 3 intro: card_ge_0_finite simp: ugraph_def)


subsection \<open>Independent Set to Set Cover\<close>
theorem is_reduction_is_vc:
  "is_reduction is_vc independent_set vertex_cover"
  unfolding is_reduction_def is_vc_def independent_set_def vertex_cover_def
proof (simp add: is_independent_set_is_vertex_cover , safe)
  show False if "card (\<Union> E) < k" "ugraph E" "k \<le> card V" "V \<subseteq> \<Union> E" for E k and V :: "'a set"
    using that by (auto 4 4 intro: card_ge_0_finite simp: ugraph_def dest: card_mono[rotated])
next
  show "\<exists>V. V \<subseteq> \<Union> E \<and> card V \<le> card (\<Union> E) - k \<and> is_vertex_cover E V"
    if "ugraph E" "V \<subseteq> \<Union> E" "k \<le> card V" "is_independent_set E V" for E k and V :: "'a set"
    using that
    by (subst (asm) is_independent_set_is_vertex_cover, (simp; fail))
      (intro exI conjI,
        auto simp: card_Diff_subset[OF finite_subset] dest: ugraph_vertex_set_finite)
next
  fix E :: "'a set set" and k :: nat and V :: "'a set"
  assume A: "\<not> card (\<Union>E) < k" "ugraph E" "V \<subseteq> \<Union> E" "card V \<le> card (\<Union>E) - k" "is_vertex_cover E V"
  then have "\<Union> E - (\<Union> E - V) = V"
    by auto
  with A show "\<exists>V. V \<subseteq> \<Union> E \<and> k \<le> card V \<and> is_independent_set E V"
    by (auto simp: is_independent_set_is_vertex_cover card_Diff_subset[OF finite_subset]
        dest: ugraph_vertex_set_finite intro!: exI[where x = "\<Union> E - V"])
qed


subsection \<open>Vertex Cover to Set Cover\<close>
theorem is_reduction_vc_sc:
  "is_reduction vc_sc vertex_cover set_cover"
  unfolding is_reduction_def vc_sc_def vertex_cover_def set_cover_def
  apply clarsimp
  apply safe
  subgoal for E k V
    apply (rule exI[where x = "{{e \<in> E. v \<in> e} |v. v \<in> V}"])
    apply (intro conjI)
    subgoal
      by fastforce
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