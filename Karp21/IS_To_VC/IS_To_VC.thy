theory IS_To_VC
  imports "../Reductions" "Poly_Reductions_Lib.SAT_Definition" "../THREE_SAT_To_IS/IS_Definition"
begin

subsection \<open>Problem Definition\<close>

definition
  "is_vertex_cover E V \<equiv> \<forall> e \<in> E. \<exists> v \<in> V. v \<in> e"

definition
  "vertex_cover \<equiv>
  {(E, k). \<exists>V. ugraph E \<and> V \<subseteq> \<Union> E \<and> k \<le> card (\<Union> E) \<and> card V \<le> k \<and> is_vertex_cover E V}"


section "The reduction"

definition
  "is_vc \<equiv> \<lambda>(E, k). if k > card (\<Union> E) then (E, k) else (E, card (\<Union> E) - k)"

section "Proof"

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
  using assms 
  by (auto 4 3 intro: card_ge_0_finite simp: ugraph_def)

section "Proof"

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


end