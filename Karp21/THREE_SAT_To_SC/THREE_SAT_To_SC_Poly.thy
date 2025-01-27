subsection\<open>The reduction from \<open>3CNF-SAT\<close> To \<open>Set Cover\<close> is polynomial\<close>
theory THREE_SAT_To_SC_Poly
  imports
    Polynomial_Reductions
    IS_To_VC_Poly
    VC_To_SC_Poly
begin

subsubsection \<open>Combination\<close>

theorem is_to_sc_ispolyred:
  "ispolyred (\<lambda>a. (is_to_vc a) \<bind> vc_to_sc) independent_set set_cover size_IS size_SC"
  by(rule sat_to_is_ispolyred is_to_vc_ispolyred vc_to_sc_ispolyred
      ispolyred_trans[OF is_to_vc_ispolyred vc_to_sc_ispolyred])

theorem sat_to_sc_ispolyred:
  "ispolyred (\<lambda>a. (sat_to_is a \<bind> is_to_vc) \<bind> vc_to_sc) three_sat set_cover size_SAT size_SC"
  by (rule ispolyred_trans[OF
    ispolyred_trans[OF sat_to_is_ispolyred is_to_vc_ispolyred] vc_to_sc_ispolyred])

end
