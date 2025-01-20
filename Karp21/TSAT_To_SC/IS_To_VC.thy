section \<open>\<open>Independent Set\<close> To \<open>Vertex Cover\<close>\<close>
theory IS_To_VC
  imports "../Reductions" VC_Definition
begin

definition "is_vc \<equiv> \<lambda>(E, k). if k > card (\<Union> E) then (E, k) else (E, card (\<Union> E) - k)"

lemma is_independent_set_iff_is_vertex_coverI:
  assumes "ugraph E"
  shows "is_independent_set E V \<longleftrightarrow> is_vertex_cover E ((\<Union>E) - V)"
proof (intro iffI is_independent_setI is_vertex_coverI)
  fix e assume A: "is_independent_set E V" "e \<in> E"
  with assms obtain u v where "e = {u, v}" by (elim ugraphE) (meson card_2_iff)
  with A consider "u \<notin> V" "v \<notin> V" | "u \<in> V" "v \<in> \<Union> E - V" | "v \<in> V" "u \<in> \<Union> E - V" by auto
  then show "\<exists>v\<in>\<Union> E - V. v \<in> e" using \<open>e \<in> E\<close> \<open>e = _\<close> by cases auto
qed force

lemma ugraph_vertex_set_finite:
  assumes "ugraph E"
  shows "finite (\<Union>E)"
  using assms by (fastforce intro: card_ge_0_finite)

theorem is_reduction_is_vc:
  "is_reduction is_vc independent_set vertex_cover"
  unfolding is_reduction_def is_vc_def independent_set_def vertex_cover_def
    independent_set_pred_def vertex_cover_pred_def
proof (simp add: is_independent_set_iff_is_vertex_coverI, safe)
  show False if "card (\<Union> E) < k" "ugraph E" "k \<le> card V" "V \<subseteq> \<Union> E" for E k and V :: "'a set"
    using that by (auto 4 4 intro: card_ge_0_finite simp: ugraph_def dest: card_mono[rotated])
next
  have "\<exists>V. V \<subseteq> \<Union> E \<and> card V \<le> card (\<Union> E) - k \<and> is_vertex_cover E V"
    if "ugraph E" "V \<subseteq> \<Union> E" "k \<le> card V" "is_independent_set E V" for E k and V :: "'a set"
    using that
    by (subst (asm) is_independent_set_iff_is_vertex_coverI, (simp; fail))
      (intro exI conjI,
        auto simp: card_Diff_subset[OF finite_subset] dest: ugraph_vertex_set_finite)
  then show "\<exists>V \<in> Pow (\<Union>E). card V \<le> card (\<Union> E) - k \<and> is_vertex_cover E V"
    if "ugraph E" "V \<subseteq> \<Union> E" "k \<le> card V" "is_independent_set E V" for E k and V :: "'a set"
    using that by blast
next
  fix E :: "'a set set" and k :: nat and V :: "'a set"
  assume A: "\<not> card (\<Union>E) < k" "ugraph E" "V \<subseteq> \<Union> E" "card V \<le> card (\<Union>E) - k" "is_vertex_cover E V"
  then have "\<Union> E - (\<Union> E - V) = V"
    by auto
  with A have "\<exists>V. V \<subseteq> \<Union> E \<and> k \<le> card V \<and> is_independent_set E V"
    by (auto simp: is_independent_set_iff_is_vertex_coverI card_Diff_subset[OF finite_subset]
        dest: ugraph_vertex_set_finite intro!: exI[where x = "\<Union> E - V"])
  then show "\<exists>V \<in> Pow (\<Union>E). k \<le> card V \<and> is_independent_set E V" by auto
qed

end
