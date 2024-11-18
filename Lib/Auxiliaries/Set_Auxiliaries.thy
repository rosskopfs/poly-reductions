theory Set_Auxiliaries
  imports Main Graph_Theory.Stuff
begin

section\<open>Set auxiliaries\<close>

lemmas [trans] = finite_subset

(** thesis Ala **)
lemma card_Collect_mem:
  assumes  "inj_on f P"
  shows    "card {f x|x. x \<in> P} = card P"
  by (simp add: assms card_image setcompr_eq_image)

lemma finite_Collect_mem:
  assumes  "inj_on f P" 
  shows    "finite {f x|x. x \<in> P} = finite P"
  using assms  [[simproc add: finite_Collect]]
  by (auto simp add: finite_image_iff)
(** **)

lemma card_greater_1_contains_two_elements:
  assumes "card S > 1"
  shows "\<exists>u v. v \<in> S \<and> u \<in> S \<and> u \<noteq> v"
  by (metis One_nat_def assms card_eq_0_iff card_le_Suc0_iff_eq le_eq_less_or_eq
        less_one not_less_iff_gr_or_eq)

lemma contains_two_card_greater_1:
  assumes "v \<in> S" "u \<in> S" "u \<noteq> v" "finite S"
  shows "1 < card S"
  using assms  by simp (meson card_le_Suc0_iff_eq not_le_imp_less)

lemma e_in_E_e_explicit:
  assumes "card e = 2"
  shows "\<exists>u v. e = {u ,v} \<and> u \<noteq> v"
proof -
  from assms have "finite e"
    using card.infinite by force
  then obtain xs where "distinct xs" "set xs = e" "length xs = card e"
    by (metis assms distinct_card finite_distinct_list)
  with assms show ?thesis
    by (metis card_eq_SucD numeral_2_eq_2 singleton_iff)
qed

lemma card_dep_on_other_set:
  assumes "finite T"
  shows "card {{u. f u j}|j. j \<in> T} \<le> card T"
  using assms by (simp add: Setcompr_eq_image card_image_le)

lemma finite_union_if_all_subset_fin:
  assumes "\<forall>S' \<in> S. finite S'" "finite S"
  shows "finite (\<Union> S)"
  using assms by auto

(* XXX Move to library;  Groups_Big.card_Union_le_sum_card *)
lemma card_UN_le_sum_cards:
  assumes "finite S"
  shows "card (\<Union> S) \<le> (\<Sum>S' \<in> S. card S')"
proof (cases "\<forall>S' \<in> S. finite S'")
  case True
  with assms show ?thesis
    by induction (auto intro: card_Un_le order.trans)
next
  case False
  then have "infinite (\<Union> S)"
    by (meson Sup_upper finite_subset)
  then show ?thesis
    by simp
qed

lemma card_union_if_all_subsets_card_i:
  assumes "\<forall>S' \<in> S. card S' \<le> i" "finite S"
  shows "card (\<Union> S) \<le> i * card S"
  using assms sum_bounded_above[of S card i]
  by (intro card_Union_le_sum_card[THEN le_trans]) 
     (simp add: mult.commute)
 

lemma card_forall_for_elements:
  assumes "\<forall>j \<in> T. card {u. f u j} \<le> 1" "S = {{u. f u j}| j. j \<in> T}"
  shows "\<forall>S' \<in> S. card S' \<le> 1"
proof
  fix S' assume "S' \<in> S"
  then have "\<exists>j \<in> T. S' = {u. f u j}"
    using assms by blast
  then show "card S' \<le> 1"
    using assms by blast
qed

lemma card_union_if_all_subsets_card_1:
  assumes "\<forall>S' \<in> S. card S' \<le> 1" "finite S"
  shows "card (\<Union> S) \<le> card S"
  using assms card_union_if_all_subsets_card_i by fastforce

lemma card_leq_1_set_explicit:
  assumes "card S \<le> 1" "finite S"
  shows "(\<exists>x. S = {x}) \<or> S = {}"
  using assms card_0_eq card_1_singletonE le_eq_less_or_eq by auto

lemma two_elem_card_le:
  "card {a, b} \<le> 2"
  by (simp add: card_insert_le_m1)

lemma finite_ordered_pairs:
  assumes "finite E"
  shows "finite {(u, v). {u, v} \<in> E}" (is "finite ?S")
proof -
  let ?E = "{{u, v} | u v. {u, v} \<in> E}"
  have "?E \<subseteq> E"
    by auto
  also have "finite E"
    by (rule assms)
  finally have "finite ?E" .
  have "?S \<subseteq> (\<Union>?E) \<times> (\<Union>?E)"
    by auto
  also from \<open>finite ?E\<close> have "finite \<dots>"
    by auto
  finally show ?thesis .
qed

lemma card_ordered_pairs:
  assumes "finite E"
  shows "card {(u, v). {u, v} \<in> E} \<le> 2 * card E" (is "card ?S \<le> _")
  using assms
proof induction
  case empty
  then show ?case
    by simp
next
  case (insert x E)
  let ?E = "insert x E"
  let ?S = "{(u, v). {u, v} \<in> E}" and ?T = "{(u, v). {u, v} \<in> ?E}"
  from \<open>finite E\<close> have "finite ?S"
    by (rule finite_ordered_pairs)
  consider (same) "?T = ?S" | (new) a b where "x = {a, b}"
    by auto
  then show ?case
  proof cases
    case same
    with insert show ?thesis
      by simp
  next
    case new
    then have "?T \<subseteq> {(a, b), (b, a)} \<union> ?S"
      by fast
    with \<open>finite ?S\<close> have "card ?T \<le> card \<dots>"
      by (intro card_mono) auto
    also have "\<dots> \<le> 2 + card ?S"
      by (intro order.trans[OF card_Un_le], simp add: two_elem_card_le)
    also from insert have "\<dots> \<le> 2 * card (insert x E)"
      by simp
    finally show ?thesis .
  qed
qed

end