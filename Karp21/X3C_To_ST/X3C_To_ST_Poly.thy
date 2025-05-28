theory X3C_To_ST_Poly
  imports
    Polynomial_Reductions
    Poly_Library
    X3C_To_ST
begin

definition "X3C_to_st_poly ≡ λ(X, S). do {
  b ← mop_for_all_set S (λs. card s = 3) (λ_. 1);
  if b then do {
    as ← nrest_image a (λ_. 1) S;
    cs ← nrest_image c (λ_. 1) X;
    v ← mop_set_union as {ROOT};
    all_v ← mop_set_union v cs;

    pairs ← nrest_image (λs. {ROOT, c s}) (λ_. 1) S;

    RETURNT {}
  } else RETURNT {}
}"

end
