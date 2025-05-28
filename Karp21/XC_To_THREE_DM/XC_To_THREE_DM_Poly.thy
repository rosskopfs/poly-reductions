theory XC_To_THREE_DM_Poly
  imports Main
    XC_To_THREE_DM
    Poly_Library
    Polynomial_Reductions
begin

(* what would be the run-time of a Union for some S? *)
definition "xc_to_three_dm_poly ≡ \<lambda>(X, S). do {
  b ← mop_set_eq (⋃ S) X;
  if b then do {

    RETURNT {}
  } else RETURNT {}
}"

end
