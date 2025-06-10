theory X3C_To_ST_Poly
  imports
    Polynomial_Reductions
    Poly_Library
    X3C_To_ST
begin

term "nrest_image (λu. {{c u, a v} | v. v ∈ u}) (λ_. 3) S"

(* TODO: *)
definition "X3C_to_steiner_tree_poly ≡ λ((X :: 'a set), S). do {
  b ← mop_for_all_set S (λs. card s = 3) (λ_. 1);
  if b then do {
    as ← nrest_image a (λ_. 1) X;
    cs ← nrest_image c (λ_. 1) S;

    v ← mop_set_union as {ROOT};
    all_v ← mop_set_union v cs;

    pairs ← nrest_image (λs. {ROOT, c s}) (λ_. 1) S;
    tmp ← nrest_image (λu. {{c u, a v} | v. v ∈ u}) (λ_. 3) S;
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

end
