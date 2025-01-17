theory VC_SC_Definition
  imports IS_Definition
begin

definition
  "is_vertex_cover E V \<equiv> \<forall> e \<in> E. \<exists> v \<in> V. v \<in> e"

definition
  "vertex_cover \<equiv>
  {(E, k). \<exists>V. ugraph E \<and> V \<subseteq> \<Union> E \<and> k \<le> card (\<Union> E) \<and> card V \<le> k \<and> is_vertex_cover E V}"

definition
  "vertex_cover_pred ≡ λ(E, k). ugraph E ∧ k ≤ card (⋃ E) ∧ (∃V ∈ Pow (⋃ E). card V ≤ k ∧ is_vertex_cover E V)"

lemma vertex_cover_unfold_pred: "vertex_cover = {E. vertex_cover_pred E}"
  unfolding vertex_cover_def vertex_cover_pred_def by blast

definition
  "set_cover \<equiv> {(T, k). \<exists> S \<subseteq> T. \<Union> S = \<Union> T \<and> card S \<le> k}"

definition
  "set_cover_pred ≡ \<lambda>(T, k). ∃S ∈ Pow T. ⋃ S = ⋃ T ∧ card S ≤ k"

lemma set_cover_unfold_pred: "set_cover = {T. set_cover_pred T}"
  unfolding set_cover_def set_cover_pred_def by blast

end
