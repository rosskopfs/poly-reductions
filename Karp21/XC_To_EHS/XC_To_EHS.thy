theory XC_To_EHS
  imports
    XC_Definition
    Reductions
begin

definition "exact_hitting_set \<equiv> {S. \<exists>W. finite W \<and> (\<forall>s \<in> S. card (W \<inter> s) = 1)}"

definition "xc_to_ehs \<equiv> \<lambda>(X, S). (if finite X \<and> \<Union>S \<subseteq> X then {{s. u \<in> s \<and> s \<in> S} | u. u \<in> X} else {{}})"

definition "size_ehs \<equiv> card"

lemma xc_to_ehs_sound:
assumes  "(X, S) \<in> exact_cover"
shows "xc_to_ehs (X, S) \<in> exact_hitting_set"
proof (cases "finite X \<and> \<Union>S \<subseteq> X")
  case True
  from assms obtain S' where S'_def: "S' \<subseteq> S" " \<Union> S' = X" "disjoint S'"
    unfolding exact_cover_def
    by blast
  with assms have prems: "finite X" "\<Union>S = X" "finite S'"
    unfolding exact_cover_def
    using finite_subset[of S' S] finite_UnionD
    by auto
  obtain U where U_def: "U = xc_to_ehs (X, S)"
    by blast
  moreover hence "finite U"
    unfolding xc_to_ehs_def
    using prems
    by simp
  moreover have "\<forall>s \<in> U. card (S' \<inter> s) = 1"
  proof
    fix s
    assume "s \<in> U"
    with U_def True obtain u where u_def: "s = {s. u \<in> s \<and> s \<in> S}" "u \<in> X"
      unfolding xc_to_ehs_def
      by auto
    then obtain x where x_def: "x \<in> S'" "u \<in> x"
      using S'_def
      by blast
    hence "\<forall>y \<in> S'. x \<noteq> y \<longrightarrow> u \<notin> y"
      using S'_def(3)
      unfolding disjoint_def
      by blast
    hence "\<forall>y \<in> S'. x \<noteq> y \<longrightarrow> y \<notin> s"
      using u_def(1)
      by simp
    moreover from u_def x_def S'_def(1) have "x \<in> s"
      by blast
    ultimately have "S' \<inter> s = {x}"
      using x_def(1)
      by blast
    then show "card (S' \<inter> s) = 1"
      by force
  qed
  ultimately show ?thesis
    unfolding exact_hitting_set_def
    using prems(3)
    by blast
next
  case False
  with assms have "False"
    unfolding exact_cover_def
    by force
  then show ?thesis
    by blast
qed

lemma xc_to_ehs_complete_aux:
assumes "W \<subseteq> S" "finite W" "finite X" "\<Union> S \<subseteq> X"
 "(\<forall>s \<in> {{s. u \<in> s \<and> s \<in> S} | u. u \<in> X}. card (W \<inter> s) = 1)"
shows "(X, S) \<in> exact_cover"
proof -
   have "card (A \<inter> B) = 1 \<longrightarrow> A \<inter> B \<noteq> {}" for A B
     by fastforce
   with assms(5) have
     "\<forall>s \<in> {{s. u \<in> s \<and> s \<in> S} | u. u \<in> X}. W \<inter> s \<noteq> {}"
     by auto
   hence "\<forall>u \<in> X. u \<in> \<Union> W"
     by auto
   with assms(1, 4) have "\<Union>W = X"
     by blast
   moreover have "disjoint W"
     proof (rule disjointI)
       fix a b
       assume prems: "a \<in> W" "b \<in> W" "a \<noteq> b"
       show "a \<inter> b = {}"
       proof (rule ccontr)
         assume "a \<inter> b \<noteq> {}"
         then obtain x where x_def: "x \<in> a" "x \<in> b"
           by blast
         with prems(1) assms(1, 4) have "x \<in> X"
           by blast
         obtain s where s_def: "s = {s. x \<in> s \<and> s \<in> S}"
           by blast
         with prems(1-2) assms(1) x_def have "{a, b} \<subseteq> W \<inter> s"
           by blast
         hence "card (W \<inter> s) \<ge> 2"
           using card_mono[of "W \<inter> s" "{a, b}"] assms(2) prems(3)
           by force

         from s_def \<open>x \<in> X\<close> have "s \<in> {{s. u \<in> s \<and> s \<in> S} | u. u \<in> X}"
           by blast
         with assms(5) have "card (W \<inter> s) = 1"
           by blast
         with \<open>card (W \<inter> s) \<ge> 2\<close> show "False"
           by auto
       qed
     qed
   ultimately show ?thesis
     unfolding exact_cover_def
     using assms(1, 3-4)
     by blast
qed

lemma xc_to_ehs_complete:
assumes "xc_to_ehs (X, S) \<in> exact_hitting_set"
shows "(X, S) \<in> exact_cover"
proof (cases "finite X \<and> \<Union> S \<subseteq> X")
  case True
  from assms True obtain W where W_def: "finite W"
  "(\<forall>s \<in> {{s. u \<in> s \<and> s \<in> S} | u. u \<in> X}. card (W \<inter> s) = 1)"
    unfolding xc_to_ehs_def exact_hitting_set_def
    by auto
  moreover have "\<forall>s \<in> {{s. u \<in> s \<and> s \<in> S} | u. u \<in> X}. {s. s \<in> W \<and> s \<in> S} \<inter> s = W \<inter> s"
    by blast
  ultimately have "\<forall>s \<in> {{s. u \<in> s \<and> s \<in> S} | u. u \<in> X}. card ({s. s \<in> W \<and> s \<in> S} \<inter> s) = 1"
    by auto
  moreover from W_def have "finite {s. s \<in> W \<and> s \<in> S}" "{s. s \<in> W \<and> s \<in> S} \<subseteq> S"
    by auto
  ultimately show ?thesis
    using xc_to_ehs_complete_aux[of "{s \<in> W. s \<in> S}" S X] True
    by presburger
next
  case False
  with assms have "False"
    unfolding xc_to_ehs_def exact_hitting_set_def
    by auto
  then show ?thesis
    by blast
qed

theorem is_reduction_xc_to_ehs: "is_reduction xc_to_ehs exact_cover exact_hitting_set"
  using xc_to_ehs_sound xc_to_ehs_complete by (intro is_reductionI) auto

end