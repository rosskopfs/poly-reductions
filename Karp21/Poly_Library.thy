theory Poly_Library
  imports
    NREST.Refine_Foreach
    "HOL-Library.Discrete_Functions"
    Undirected_Graph_Theory.Undirected_Graphs_Root
begin

definition "mop_set_finite S = (REST [ finite S \<mapsto> 1 ])"

definition "mop_set_card S = REST [card S \<mapsto> 1]"
definition "mop_set_empty_set = REST [ {} \<mapsto> 1]"
definition "mop_set_insert S s = REST [insert s S \<mapsto> 1]"
definition "mop_get_vertices E = REST [ (\<Union> E)  \<mapsto> 2 * card E ]"

definition "mop_list_up_to xs \<equiv> REST [ {..<length xs} \<mapsto> length xs ]"
definition "mop_list_up_to_n (n :: nat) \<equiv> REST [ {..<n} \<mapsto> n ]"
definition "mop_list_length xs \<equiv> REST [ length xs \<mapsto> 1 ]"
definition "mop_list_map xs f ft \<equiv> REST [ map f xs \<mapsto> foldl (+) 0 (map ft xs)]"

definition "mop_set_times A B \<equiv> REST [ A \<times> B \<mapsto> card A * card B ]"
definition "mop_set_union A B \<equiv> REST [ A \<union> B \<mapsto> card A + card B ]"

definition "mop_all_edges V \<equiv> REST [ all_edges V \<mapsto> card V * card V]"
definition "mop_set_for_all S p pt \<equiv> REST [ \<forall>s \<in> S. p s \<mapsto> sum pt S ]"

definition "mop_set_diff A B \<equiv> REST [ A - B \<mapsto> card A ]"
definition "mop_set_Union A \<equiv> REST [ \<Union> A \<mapsto> sum card A + card A ]"
definition "mop_set_eq A B \<equiv> REST [ A = B \<mapsto> min (card A) (card B) ]"

definition "mop_leq (l :: nat) r \<equiv> REST [ (l \<le> r) \<mapsto> 1 ]"
definition "mop_plus (l :: nat) r \<equiv> REST [ l + r \<mapsto> 1 ]"

definition "nrest_image f (ft :: 'b \<Rightarrow> nat) A = REST [ f ` A \<mapsto> enat (sum ft A) ]"
definition "nrest_filter_image f (ft :: 'b \<Rightarrow> nat) P (Pt :: 'b \<Rightarrow> nat) A =
    REST [ f ` {a \<in> A. P a} \<mapsto> enat (sum (\<lambda>a. Pt a + (if P a then ft a else 0)) A) ]"

lemma nrest_image_bound:
assumes "\<And>a. a \<in> A \<Longrightarrow> ft a \<le> c"
shows "sum ft A \<le> card A * c"
by (metis assms of_nat_id sum_bounded_above)

lemma nrest_filter_image_bound:
  assumes "\<And>a. a \<in> A \<Longrightarrow> ft a \<le> c" and "\<And>a. a \<in> A \<Longrightarrow> Pt a \<le> c'"
  shows "sum (\<lambda>a. ft a + Pt a) A \<le> card A * (c + c')"
  by (auto simp add: add_mono_thms_linordered_semiring(1) assms nrest_image_bound)

lemma choose_2_upperbound: "n choose 2 \<le> n * n"
by (metis binomial_le_pow linorder_le_less_linear order_trans power2_eq_square zero_le zero_less_binomial_iff)

lemma card_all_edges_upper:
assumes "finite V"
shows "card (all_edges V) \<le> card V * card V"
by (simp add: assms card_all_edges choose_2_upperbound)

definition "nat_encoded_size k = floor_log k + 1"

lemma nat_encoded_size_leq_self:
  assumes "1 \<le> k"
  shows "nat_encoded_size k \<le> k"
using assms
unfolding nat_encoded_size_def
apply (induction k)
apply simp
by (smt (verit, del_insts) One_nat_def Suc_1 add_Suc_right floor_log_Suc_zero floor_log_le_iff
  floor_log_twice le_Suc_eq nat_arith.rule0 not_less_eq_eq)


end
