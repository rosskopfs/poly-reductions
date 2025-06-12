theory X3C_To_ST_Poly
  imports
    Polynomial_Reductions
    Poly_Library
    X3C_To_ST
begin

term "nrest_image (λu. {{c u, a v} | v. v ∈ u}) (λ_. 3) S"

(* TODO: *)
definition "X3C_to_steiner_tree_poly ≡ λ((X :: 'a set), S). do {
  b ← mop_set_for_all S (λs. card s = 3) (λ_. 1);
  if b then do {
    as ← nrest_image a (λ_. 1) X;
    cs ← nrest_image c (λ_. 1) S;

    v ← mop_set_union as {ROOT};
    all_v ← mop_set_union v cs;

    pairs ← nrest_image (λs. {ROOT, c s}) (λ_. 1) S;
    tmp ← nrest_image (λu. {{c u, a v} | v. v ∈ u}) (λu. card u) S;
    pairs' ← mop_set_Union tmp;

    all_pairs ← mop_set_union pairs pairs';

    union ← mop_set_union {ROOT} as;

    RETURNT (
      all_v,
      all_pairs,
      (λe. 1),
      union,
      4 * card X div 3
    )
  } else RETURNT NOT_STEINER_TREE_EXAMPLE
}"

definition "size_X3C ≡ λ(X, S). card X + sum card S"
definition "size_ST ≡ λ(V, E, _, S, K). card V + sum card E + card S + nat_encoded_size K"

definition "x3c_to_st_space n ≡ (n + 1) + n + n + 1"
definition "x3c_to_st_time n ≡ 0"

lemma x3c_to_size: "size_ST (X3C_to_steiner_tree C) ≤ x3c_to_st_space (size_X3C C)"
apply (cases C)
apply (simp add: size_ST_def X3C_to_steiner_tree_def x3c_to_st_space_def size_X3C_def)
apply (intro impI conjI)
subgoal for a b
apply (simp add: nat_encoded_size_def)
sorry

apply (simp add: NOT_STEINER_TREE_EXAMPLE_def nat_encoded_size_def)
done

end
