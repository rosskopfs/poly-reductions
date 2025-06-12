theory XC_To_THREE_DM_Poly
  imports Main
    XC_To_THREE_DM
    Poly_Library
    Polynomial_Reductions
begin

definition "mop_set_union_eq_set A B ≡ REST [ ⋃ A = B ↦ card A * card B]"
definition "mop_set_discriminated_Union S time ≡ REST [ ⨄ S ↦ sum time S ]"

(* what would be the run-time of a Union for some S? *)
definition "xc_to_three_dm_poly ≡ \<lambda>(X, S). do {
  b ← mop_set_union_eq_set S X;
  if b then do {
    T ← mop_set_discriminated_Union S (λ_. card X);

    let α = {};
    let U1 = {};
    let U2 = {};

    RETURNT ({}, T)
  } else RETURNT MALFORMED
}"

end
