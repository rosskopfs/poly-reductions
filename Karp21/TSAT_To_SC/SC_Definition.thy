\<^marker>\<open>contributor "Nico Lintner"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
theory SC_Definition
  imports IS_Definition
begin

subsection \<open>Definition of Vertex Cover\<close>

definition "set_cover_pred T k \<equiv> \<exists>S \<in> Pow T. \<Union>S = \<Union>T \<and> card S \<le> k"

lemma set_cover_predI [intro]:
  assumes "S \<subseteq> T"
  and "\<Union>S = \<Union>T"
  and "card S \<le> k"
  shows "set_cover_pred T k"
  using assms unfolding set_cover_pred_def by auto

lemma set_cover_predE [elim]:
  assumes "set_cover_pred T k"
  obtains S where "S \<subseteq> T" "\<Union>S = \<Union>T" "card S \<le> k"
  using assms unfolding set_cover_pred_def by auto

definition "set_cover \<equiv> {(T, k). set_cover_pred T k}"

lemma set_cover_eq_Collect_set_cover_pred [simp]: "set_cover = {(T, k). set_cover_pred T k}"
  unfolding set_cover_def by simp

end
