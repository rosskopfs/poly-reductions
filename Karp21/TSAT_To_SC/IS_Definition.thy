theory IS_Definition
  imports Main
begin

subsection "Independent Set definitions"

type_synonym 'a ugraph = "'a set set"

definition
  "ugraph E \<equiv> finite E \<and> (\<forall>e \<in> E. card e = 2)" \<comment> \<open>Allow self-loops?\<close>

definition
  "is_independent_set E V \<equiv> \<forall>u \<in> V. \<forall>v \<in> V. {u, v} \<notin> E"

definition
  "independent_set \<equiv> {(E, k). \<exists>V. ugraph E \<and> V \<subseteq> \<Union> E \<and> card V \<ge> k \<and> is_independent_set E V}"

definition
  "independent_set_pred \<equiv> \<lambda>(E, k). ugraph E \<and> (\<exists>V \<in> Pow (\<Union> E). card V \<ge> k \<and> is_independent_set E V)"

lemma independent_set_unfold_pred: "independent_set = {E. independent_set_pred E}"
  unfolding independent_set_def independent_set_pred_def by blast

end
