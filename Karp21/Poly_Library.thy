theory Poly_Library
  imports
    NREST.Refine_Foreach
    "HOL-Library.Discrete_Functions"
begin

definition "mop_set_card S  = REST [card S \<mapsto> 1]"
definition "mop_set_empty_set = REST [ {} \<mapsto> 1]"

definition "mop_set_insert S s = REST [insert s S \<mapsto> 1]"
definition "mop_get_vertices E = REST [ (\<Union> E)  \<mapsto> 2 * card E + 1]"

(* TODO: helper lemmas? *)
definition "nat_encoded_size k = floor_log k + 1"

definition "nrest_image f ft A = REST [ f ` A \<mapsto> sum ft A ]"

(* TODO: lemmas *)
definition "nrest_filter_image f ft P Pt A = REST [ f ` {a ∈ A. P a} \<mapsto> sum (λa. Pt a + (if P a then ft a else 0)) A ]"

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

end
