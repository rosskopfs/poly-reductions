theory TSAT_To_SC
  imports TSAT_To_IS IS_To_SC
begin

theorem sat_sc:
  "is_reduction (vc_sc o is_vc o sat_is) three_cnf_sat set_cover"
  by (rule is_reduction_trans is_reduction_sat_is is_reduction_is_vc is_reduction_vc_sc)+

end