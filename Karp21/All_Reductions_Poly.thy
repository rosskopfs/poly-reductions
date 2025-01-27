theory All_Reductions_Poly
  imports
    HC_To_UHC_Poly
    IS_To_VC_Poly
    SAT_To_CLIQUE_Poly
    SAT_To_XC_Poly
    SS_List_To_JS_Poly
    SS_To_KS_Poly
    SS_To_SS_List_Poly
    SS_To_PART_Poly
    SS_To_ZERO_ONE_Poly
    THREE_COL_To_CHRN_Poly
    THREE_DM_To_X3C_Poly
    THREE_SAT_To_IS_Poly
    THREE_SAT_To_SC_Poly
    THREE_SAT_To_THREE_COL_Poly
    VC_Set_To_VC_List_Poly
    VC_To_FNS_Poly
    VC_To_HC_Poly
    VC_To_SC_Poly
    XC_To_EHS_Poly
    XC_To_SS_Poly
begin

section \<open>Overview of polynomial Reductions\<close>

text \<open>
  \<^item> SAT
    \<^item> 3-SAT (missing)
      \<^item> 3-Colorability @{thm sat_to_is_ispolyred}
        \<^item> Chromatic Number @{thm three_col_to_chrn_ispolyred}
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

end