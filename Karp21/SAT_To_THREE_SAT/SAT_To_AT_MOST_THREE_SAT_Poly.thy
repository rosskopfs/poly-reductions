
theory SAT_To_AT_MOST_THREE_SAT_Poly
  imports
    SAT_To_AT_MOST_THREE_SAT
    Poly_Library
    Polynomial_Reductions
begin

definition "mop_sat_to_at_most_three_sat_aux xs i ≡ REST [ sat_to_at_most_three_sat_aux xs i ↦ 0 ]"

end
