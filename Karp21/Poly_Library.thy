theory Poly_Library
  imports
    NREST.Refine_Foreach
    "HOL-Library.Discrete_Functions"
begin

definition "mop_set_empty_set = REST [ {} \<mapsto> 1]"

(* TODO: helper lemmas? *)
definition "encode_size k = floor_log k + 1"

end
