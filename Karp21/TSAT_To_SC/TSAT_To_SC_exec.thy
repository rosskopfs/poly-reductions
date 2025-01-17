theory TSAT_To_SC_exec
  imports TSAT_To_IS_exec IS_To_SC_exec
begin

theorem sat_sc:
  "is_reduction (vc_sc_exec o is_vc_exec o sat_is_exec) three_cnf_sat_exec set_cover_exec"
  by (rule is_reduction_trans is_reduction_sat_is_exec is_reduction_is_vc_exec is_reduction_vc_sc_exec)+

end
