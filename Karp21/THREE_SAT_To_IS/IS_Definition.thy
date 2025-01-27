theory IS_Definition
  imports Main
begin

subsection "Independent Set definitions"

type_synonym 'a ugraph = "'a set set"

definition "ugraph E \<equiv> finite E \<and> (\<forall>e \<in> E. card e = 2)" \<comment> \<open>Allow self-loops?\<close>

lemma ugraphI [intro]:
  assumes "finite E"
  and "\<And>e. e \<in> E \<Longrightarrow> card e = 2"
  shows "ugraph E"
  using assms unfolding ugraph_def by simp

lemma ugraphE [elim]:
  assumes "ugraph E"
  obtains "finite E" "\<And>e. e \<in> E \<Longrightarrow> card e = 2"
  using assms unfolding ugraph_def by simp

lemma ugraph_vertex_set_finite:
  assumes "ugraph E"
  shows "finite (\<Union>E)"
  using assms by (fastforce intro: card_ge_0_finite)

definition
  "is_independent_set E V \<equiv> \<forall>u \<in> V. \<forall>v \<in> V. {u, v} \<notin> E"

lemma is_independent_setI [intro]:
  assumes "\<And>u v. u \<in> V \<Longrightarrow> v \<in> V \<Longrightarrow> {u, v} \<notin> E"
  shows "is_independent_set E V"
  using assms unfolding is_independent_set_def by simp

lemma is_independent_setE [elim]:
  assumes "is_independent_set E V"
  obtains "\<And>u v. u \<in> V \<Longrightarrow> v \<in> V \<Longrightarrow> {u, v} \<notin> E"
  using assms unfolding is_independent_set_def by simp

definition "independent_set_pred E k \<equiv>
  ugraph E \<and> (\<exists>V \<in> Pow (\<Union>E). card V \<ge> k \<and> is_independent_set E V)"

lemma independent_set_predI [intro]:
  assumes "ugraph E"
  and "V \<subseteq> \<Union>E"
  and "card V \<ge> k"
  and "is_independent_set E V"
  shows "independent_set_pred E k"
  using assms unfolding independent_set_pred_def by auto

lemma independent_set_predE [elim]:
  assumes "independent_set_pred E k"
  obtains V where "ugraph E" "V \<subseteq> \<Union>E" "card V \<ge> k" "is_independent_set E V"
  using assms unfolding independent_set_pred_def by auto

definition "independent_set \<equiv> {(E, k). independent_set_pred E k}"

lemma independent_set_eq_Collect_independent_set_pred [simp]:
  "independent_set = {(E, k). independent_set_pred E k}"
  unfolding independent_set_def by simp

end
