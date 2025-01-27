theory X3C_Definition
  imports XC_Definition
begin

definition "three_exact_cover \<equiv> {(X, S). (X, S) \<in> exact_cover \<and> (\<forall>C \<in> S. card C = 3)}"

lemma three_exact_coverI:
  assumes "(X, S) \<in> exact_cover"
  and "\<forall>C \<in> S. card C = 3"
  shows "(X,S) \<in> three_exact_cover"
  unfolding three_exact_cover_def using assms by blast

end