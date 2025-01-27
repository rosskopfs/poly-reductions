section \<open>\<open>3CNF-SAT\<close> To \<open>Set Cover\<close>\<close>
theory THREE_SAT_To_SC
  imports THREE_SAT_To_IS IS_To_VC VC_To_SC
begin

theorem sat_sc: "is_reduction (vc_sc o is_vc o sat_is) three_sat set_cover"
  by (rule is_reduction_trans is_reduction_sat_is is_reduction_is_vc is_reduction_vc_sc)+

end