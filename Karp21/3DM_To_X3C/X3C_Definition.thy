theory X3C_Definition
  imports "HOL-Library.Disjoint_Sets"
begin

definition "three_exact_cover \<equiv> 
    {(X, S). finite X  \<and> \<Union>S \<subseteq> X \<and> (\<forall>C \<in> S. card C = 3) \<and> 
     (\<exists>S' \<subseteq> S. \<Union>S' = X \<and> disjoint S')}"

lemma three_exact_cover_cert:
  assumes "S' \<subseteq> S"
          "\<Union>S' = X "
          "disjoint S'"
          "finite X"
          "\<Union>S \<subseteq> X"
          "\<forall>C \<in> S. card C = 3"
  shows "(X,S) \<in> three_exact_cover"
  unfolding three_exact_cover_def 
  using assms by blast

end