\<^marker>\<open>contributor "Nico Lintner"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
theory VC_Definition
  imports IS_Definition
begin

subsection \<open>Definition of Vertex Cover\<close>

definition
  "is_vertex_cover E V \<equiv> \<forall>e \<in> E. \<exists>v \<in> V. v \<in> e"

lemma is_vertex_coverI [intro]:
  assumes "\<And>e. e \<in> E \<Longrightarrow> \<exists>v \<in> V. v \<in> e"
  shows "is_vertex_cover E V"
  using assms unfolding is_vertex_cover_def by auto

lemma is_vertex_coverE [elim]:
  assumes "is_vertex_cover E V"
  obtains "\<And>e. e \<in> E \<Longrightarrow> \<exists>v \<in> V. v \<in> e"
  using assms unfolding is_vertex_cover_def by auto

definition "vertex_cover_pred E k \<equiv>
  ugraph E \<and> k \<le> card (\<Union>E) \<and> (\<exists>V \<in> Pow (\<Union>E). card V \<le> k \<and> is_vertex_cover E V)"

lemma vertex_cover_predI [intro]:
  assumes "ugraph E"
  and "k \<le> card (\<Union>E)"
  and "V \<subseteq> \<Union>E"
  and "card V \<le> k"
  and "is_vertex_cover E V"
  shows "vertex_cover_pred E k"
  using assms unfolding vertex_cover_pred_def by auto

lemma vertex_cover_predE [elim]:
  assumes "vertex_cover_pred E k"
  obtains V where "ugraph E" "k \<le> card (\<Union>E)" "V \<subseteq> \<Union>E" "card V \<le> k" "is_vertex_cover E V"
  using assms unfolding vertex_cover_pred_def by auto

definition "vertex_cover \<equiv> {(E, k). vertex_cover_pred E k}"

lemma vertex_cover_eq_Collect_vertex_cover_pred [simp]:
  "vertex_cover = {(E, k). vertex_cover_pred E k}"
  unfolding vertex_cover_def by simp

end
