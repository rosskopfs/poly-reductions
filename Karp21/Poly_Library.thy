theory Poly_Library
  imports
    NREST.Refine_Foreach
    "HOL-Library.Discrete_Functions"
    Undirected_Graph_Theory.Undirected_Graphs_Root
begin

definition "mop_set_card S  = REST [card S \<mapsto> 1]"
definition "mop_set_empty_set = REST [ {} \<mapsto> 1]"
definition "mop_set_insert S s = REST [insert s S \<mapsto> 1]"
definition "mop_get_vertices E = REST [ (\<Union> E)  \<mapsto> 2 * card E ]"

definition "mop_list_up_to xs ≡ REST [ {..<length xs} ↦ length xs ]"
definition "mop_list_up_to_n (n :: nat) ≡ REST [ {..<n} ↦ n ]"
definition "mop_list_length xs ≡ REST [ length xs ↦ 1 ]"
definition "mop_list_map xs f ft ≡ REST [ map f xs ↦ foldl (+) 0 (map ft xs)]"

definition "mop_set_times A B ≡ REST [ A × B ↦ card A * card B ]"
definition "mop_set_union A B ≡ REST [ A \<union> B ↦ card A + card B ]"

(* can't use times since edges is a 'a set set rather than ('a × 'a) set *)
definition "mop_all_edges V ≡ REST [ all_edges V ↦ card V * card V]"
definition "mop_for_all_set S p pt ≡ REST [ ∀s ∈ S. p s ↦ sum pt S ]"

definition "mop_set_diff A B ≡ REST [ A - B ↦ card A ]"
definition "mop_set_Union A ≡ REST [ ⋃ A ↦ sum card A ]"
definition "mop_set_eq A B ≡ REST [ A = B ↦ min (card A) (card B) ]"

definition "mop_leq (l :: nat) r ≡ REST [ (l ≤ r) ↦ 1 ]"
definition "mop_plus (l :: nat) r ≡ REST [ l + r ↦ 1 ]"

definition "nrest_image f ft A = REST [ f ` A \<mapsto> sum ft A ]"
definition "nrest_filter_image f ft P Pt A =
    REST [ f ` {a ∈ A. P a} \<mapsto> sum (λa. Pt a + (if P a then ft a else 0)) A ]"

lemma nrest_image_bound:
assumes "⋀a. a ∈ A ⟹ ft a ≤ c"
shows "sum ft A ≤ card A * c"
by (metis assms of_nat_id sum_bounded_above)

lemma nrest_filter_image_bound:
assumes "⋀a. a ∈ A ⟹ ft a ≤ c" and "⋀a. a ∈ A ⟹ Pt a ≤ c'"
shows "sum (λa. ft a + Pt a) A ≤ card A * (c + c')"
by (metis assms of_nat_id nrest_image_bound)

lemma choose_2_upperbound: "n choose 2 ≤ n * n"
by (metis binomial_le_pow linorder_le_less_linear order_trans power2_eq_square zero_le zero_less_binomial_iff)

lemma card_all_edges_upper:
assumes "finite V"
shows "card (all_edges V) ≤ card V * card V"
by (simp add: assms card_all_edges choose_2_upperbound)

definition "nat_encoded_size k = floor_log k + 1"

lemma nat_encoded_size_leq_self:
  assumes "2 ≤ k"
  shows "nat_encoded_size k ≤ k"
using assms
unfolding nat_encoded_size_def
apply (induction k)
apply simp
by (smt (verit, del_insts) One_nat_def Suc_1 add_Suc_right floor_log_Suc_zero floor_log_le_iff
  floor_log_twice le_Suc_eq nat_arith.rule0 not_less_eq_eq)


end
