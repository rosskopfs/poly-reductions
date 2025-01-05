theory All_Reductions_Poly
  imports
    "3DM_To_X3C/Three_DM_To_X3C_Poly"
    "CNF_SAT_To_Clique/CSTC_Poly"
    "HC_To_UHC/HC_To_UHC_Poly"
    "SAT_To_XC/SAT_To_XC_poly"
    "CNF_SAT_To_TC/TST3C_Poly"
    "TC_To_ChrN/TC_To_ChrN_Poly"
    "VC_Set_To_VC_List/VCSTVCL_Poly"
    "VC_To_FNS/VCTFNS_Poly"
    "VC_To_HC/VCHC_Poly"
    "XC_To_EHS/XC_To_EHS_poly"
    "XC_To_SS/XC_To_SS_poly"
    "SS_To_JS/SS_List_To_Job_Seq_Poly"
    "XC_To_SS/SS_To_SS_List_poly"
begin

section \<open>Overview of reductions\<close>           

text \<open>
  \<^item> SAT 
    \<^item> 3-SAT
      \<^item> 3-Colorability @{thm sat_to_is_ispolyred}
        \<^item> Chromatic Number @{thm threeColToChrNum_ispolyred}
          \<^item> Clique Cover (missing)
    \<^item> Exact Cover @{thm sat_to_xc_ispolyred}
      \<^item> Subset Sum @{thm xc_to_ss_ispolyred}
        \<^item> Job Sequencing @{thm ss_list_to_job_seq_is_polyred}
        \<^item> Partition @{thm ss_list_to_part_is_polyred}
           \<^item> Max Cut (missing)
        \<^item> Zero-One Integer Programming @{thm ss_int_list_to_zero_one_int_prog_is_polyred}
        \<^item> Knapsack @{thm ss_to_ks_is_polyred}   
      \<^item> Three-Dimensional Matching (missing)
        \<^item> Exact Cover by 3-Sets @{thm tdm_to_x3c_is_polyred}
          \<^item> Steiner Tree (missing)
      \<^item> Exact Hitting Set @{thm xc_to_ehs_is_polyred}
  \<^item> Independent Set @{thm sat_to_is_ispolyred}
    \<^item> Vertex Cover @{thm is_to_vc_ispolyred}
      \<^item> Hamiltonian Cycle @{thm vc_to_hc_ispolyred}
        \<^item> Undirected Hamiltonian Cycle @{thm hc_to_uhc_ispolyred}
      \<^item> Set Cover @{thm vc_to_sc_ispolyred}
      \<^item> Feedback Arc Set (missing)
      \<^item> Feedback Node Set @{thm vc_to_fns_ispolyred}
  \<^item> Clique @{thm cnf_sat_to_clique_ispolyred}
    \<^item> Set Packing (missing)
\<close>

section \<open>Full list (includes variations of the same problem)\<close>
text \<open>
  \<^item> SAT
    \<^item> 3-SAT
      \<^item> 3-Colorability @{thm sat_to_is_ispolyred}
        \<^item> Chromatic Number @{thm threeColToChrNum_ispolyred}
          \<^item> Clique Cover (missing)
    \<^item> Exact Cover @{thm sat_to_xc_ispolyred}
      \<^item> Subset Sum @{thm xc_to_ss_ispolyred}
        \<^item> Subset Sum (List) @{thm ss_indeces_to_ss_list_is_polyred}
           \<^item> Job Sequencing @{thm ss_list_to_job_seq_is_polyred}
           \<^item> Partition @{thm ss_list_to_part_is_polyred}
              \<^item> Max Cut (missing)
           \<^item> Subset Sum (Int List) @{thm ss_lift_to_int_is_polyred}
             \<^item> Zero-One Integer Programming @{thm ss_int_list_to_zero_one_int_prog_is_polyred}
        \<^item> Knapsack @{thm ss_to_ks_is_polyred}
      \<^item> Three-Dimensional Matching (missing)
        \<^item> Three-Dimensional Matching (Alt1) (missing)
        \<^item> Three-Dimensional Matching (Alt2) (missing)
        \<^item> Exact Cover by 3-Sets @{thm tdm_to_x3c_is_polyred}
          \<^item> Steiner Tree (missing)
      \<^item> Exact Hitting Set @{thm xc_to_ehs_is_polyred}
  \<^item> Independent Set @{thm sat_to_is_ispolyred}
    \<^item> Vertex Cover @{thm is_to_vc_ispolyred}
      \<^item> Vertex Cover (List) @{thm vcs_to_vcl_ispolyred}
        \<^item> Hamiltonian Cycle @{thm vc_to_hc_ispolyred}
          \<^item> Undirected Hamiltonian Cycle @{thm hc_to_uhc_ispolyred}
      \<^item> Set Cover @{thm vc_to_sc_ispolyred}
      \<^item> Feedback Arc Set (missing)
      \<^item> Feedback Node Set @{thm vc_to_fns_ispolyred}
  \<^item> Clique @{thm cnf_sat_to_clique_ispolyred}
    \<^item> Set Packing (missing)
\<close>

end