theory PART_To_MAXCUT_Poly
  imports
    PART_To_MAXCUT
    Polynomial_Reductions
    Poly_Library
begin

definition "mop_sum_list xs ≡ REST [ sum_list xs ↦ length xs ]"
definition "part_to_max_cut_poly ≡ λas. do {
  n ← mop_list_length as;
  V ← mop_list_up_to_n n;
  E ← mop_all_edges V;
  list_sum ← mop_sum_list as;
  RETURNT ((V, E), w as, (list_sum^2 + 3) div 4)
}"

definition "size_part \<equiv> length"
definition "size_max_cut ≡ λ((V, E), _, _). card V + sum card E"

definition "part_to_max_cut_space n ≡ n + 2 * n * n"
definition "part_to_max_cut_time n ≡ 1 + n + n * n + n"

lemma sum_card_all_edges:
assumes "finite E"
shows "sum card (all_edges E) ≤ 2 * card E * card E"
proof -
  have "⋀ e. e ∈ (all_edges E) ⟹ card e = 2"
    using all_edges_def by blast
  then have "sum card (all_edges E) = 2 * card (all_edges E)" by auto
  also have "... ≤ 2 * (card E * card E)"
    by (simp add: assms card_all_edges_upper)
  finally show ?thesis by linarith
qed

lemma part_to_max_cut_size:
  "size_max_cut (part_to_max_cut as) ≤ part_to_max_cut_space (size_part as)"
unfolding size_max_cut_def size_part_def part_to_max_cut_def part_to_max_cut_space_def
using sum_card_all_edges by force

lemma part_to_max_cut_refines:
  "part_to_max_cut_poly as
  ≤ SPEC (λy. y = part_to_max_cut as) (λ_. part_to_max_cut_time (size_part as))"
unfolding SPEC_def part_to_max_cut_def size_part_def part_to_max_cut_time_def
  part_to_max_cut_poly_def mop_list_up_to_n_def mop_list_length_def
  mop_all_edges_def mop_sum_list_def
apply(rule T_specifies_I)
apply(vcg' \<open>-\<close> rules: T_SPEC)
by (simp add: one_enat_def)

theorem part_to_max_cut_ispolyred:
  "ispolyred part_to_max_cut_poly part_alter max_cut size_part size_max_cut"
unfolding ispolyred_def
apply(rule exI[where x=part_to_max_cut])
apply(rule exI[where x=part_to_max_cut_time])
apply(rule exI[where x=part_to_max_cut_space])
apply safe
  subgoal using part_to_max_cut_refines by blast
  subgoal using part_to_max_cut_size by blast
  subgoal unfolding poly_def part_to_max_cut_time_def
    apply(rule exI[where x=2]) by auto
  subgoal unfolding poly_def part_to_max_cut_space_def
    apply(rule exI[where x=2]) by auto
  subgoal using is_reduction_part_to_maxcut .
done

end

