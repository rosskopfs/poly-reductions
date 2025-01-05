section \<open>\<open>3CNF-SAT\<close> To \<open>Set Cover\<close>\<close>

theory Three_Sat_To_Set_Cover
  imports "../Reductions" "Poly_Reductions_Lib.SAT_Definition"
          "../THREE_SAT_To_IS/THREE_SAT_To_IS" "../IS_To_VC/IS_To_VC"
          "../VC_To_SC/VC_To_SC"
begin

theorem sat_sc:
  "is_reduction (vc_sc o is_vc o sat_is) three_cnf_sat set_cover"
  by (rule is_reduction_trans is_reduction_sat_is is_reduction_is_vc is_reduction_vc_sc)+

end