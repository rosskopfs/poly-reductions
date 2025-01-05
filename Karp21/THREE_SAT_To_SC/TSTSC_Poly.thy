subsection\<open>The reduction from \<open>3CNF-SAT\<close> To \<open>Set Cover\<close> is polynomial\<close>
theory TSTSC_Poly
  imports Polynomial_Reductions Three_Sat_To_Set_Cover
          "../THREE_SAT_To_IS/THREE_SAT_To_IS_poly"
          "../IS_To_VC/IS_To_VC_poly"
          "../VC_To_SC/VC_To_SC_poly"   
          
begin

subsubsection \<open>Combination\<close>

theorem is_to_sc_ispolyred: 
  "ispolyred (\<lambda>a. (is_to_vc a) \<bind> vc_to_sc) independent_set set_cover size_IS size_SC"
  by(rule sat_to_is_ispolyred is_to_vc_ispolyred vc_to_sc_ispolyred  
      ispolyred_trans[OF is_to_vc_ispolyred vc_to_sc_ispolyred])

theorem sat_to_sc_ispolyred: 
  "ispolyred (\<lambda>a. (sat_to_is a \<bind> is_to_vc) \<bind> vc_to_sc) three_cnf_sat set_cover size_SAT size_SC"
  by (rule ispolyred_trans [OF ispolyred_trans
        [OF sat_to_is_ispolyred is_to_vc_ispolyred] vc_to_sc_ispolyred])

end