theory Discriminated_Union
  imports "HOL-Library.Disjoint_Sets" 
          Automatic_Refinement.Misc (* for img_fst [intro] which proves fst_discr_Un *)
begin           

abbreviation discriminated_Union (\<open>\<Uplus>\<close>)
  where "\<Uplus>S \<equiv> {(x,s)|s x. s \<in> S \<and> x \<in> s}"

lemma card_discriminated_Union:
  assumes fin_s: "\<And>s. s \<in> S \<Longrightarrow> finite s" 
  shows "card (\<Uplus>S) = sum card S"
proof -    
  have dis: "disjoint {{(x,s) | x. x \<in> s} |s. s \<in> S}"
    unfolding disjoint_def by auto
  have  "card {(x,s) |s x. s \<in> S \<and> x \<in> s} =
         card ( \<Union>  {{(x,s) | x. x \<in> s} |s. s \<in> S})"
    by (intro arg_cong[where ?f = "card"]) auto
  also have "... = sum card ((\<lambda>s. {(x,s) | x. x \<in> s})  ` S)"
    using fin_s card_Union_disjoint[OF dis]
    by (auto simp add: Setcompr_eq_image)
  also have "... = sum card S"
  proof - 
    have inj: "inj_on (\<lambda>s. {(v,s) | v. v \<in> s}) S" 
      unfolding inj_on_def by blast
    show ?thesis       
      by (subst sum.reindex[OF inj], intro sum.cong)
         (auto simp add: Setcompr_eq_image card_image inj_on_def)
  qed
  finally show ?thesis .
qed


lemma fst_discr_Un:
   "fst ` \<Uplus>S = \<Union>S" 
  by auto (* img_fst [intro] *)

lemma finite_Union_if_finite_discriminated_Union:
  assumes "finite(\<Uplus>S)"
  shows "finite (\<Union>S)"
  using finite_imageI[OF assms, of fst] fst_discr_Un[symmetric]
  by (subst fst_discr_Un[symmetric])

lemma finite_discriminated_Union:
  assumes "finite (\<Union>S)"
  shows "finite (\<Uplus>S)"
proof -
  have fin_s: "\<And>s. s \<in> S \<Longrightarrow> finite s"
    using assms  by (meson Union_upper finite_subset)
  then have "card {(x, s) | s x. s \<in> S \<and> x \<in> s}  \<ge> card (\<Union>S)"
    by (simp add: card_Union_le_sum_card card_discriminated_Union)
  then show ?thesis 
    using assms not_finite_existsD order_antisym_conv by fastforce
qed


end