theory All_Reductions
  imports
    AT_MOST_THREE_SAT_To_THREE_SAT
    CHRN_To_CC
    CLIQUE_To_SP
    HC_To_UHC
    IS_To_VC_List
    IS_To_VC
    PART_To_MAXCUT
    SAT_To_CLIQUE
    SAT_To_AT_MOST_THREE_SAT
    SAT_To_XC
    SS_To_JS
    SS_To_KS
    SS_To_SS_List
    SS_To_PART
    SS_To_ZERO_ONE
    THREE_COL_To_CHRN
    THREE_DM_To_X3C
    THREE_SAT_To_IS_List
    THREE_SAT_To_IS
    THREE_SAT_To_SC
    THREE_SAT_To_THREE_COL
    VC_Set_To_VC_List
    VC_To_FAS
    VC_To_FNS
    VC_To_HC
    VC_To_SC
    X3C_To_ST
    XC_To_EHS
    XC_To_SS
    XC_To_ST
    XC_To_THREE_DM
begin

section \<open>Overview of Reductions\<close>

text \<open>
  \<^item> SAT
    \<^item> AM3-SAT @{thm is_reduction_sat_to_at_most_three_sat}
      \<^item> 3-SAT @{thm is_reduction_at_most_three_sat_to_three_sat}
        \<^item> 3-Colorability @{thm is_reduction_sat_three_col}
         \<^item> Chromatic Number @{thm is_reduction_three_col_chrn}
          \<^item> Clique Cover  @{thm is_reduction_chrn_to_cc}
    \<^item> Exact Cover @{thm is_reduction_sat_xc}
      \<^item> Subset Sum @{thm is_reduction_xc_to_ss}
        \<^item> Job Sequencing @{thm is_reduction_ss_list_to_job_seq}{
        \<^item> Partition @{thm is_reduction_ss_list_to_part}
           \<^item> Max Cut @{thm is_reduction_part_to_maxcut}
        \<^item> Zero-One Integer Programming @{thm is_reduction_ss_int_list_to_zero_one_int_prog}
        \<^item> Knapsack @{thm is_reduction_ss_to_ks}
      \<^item> Three-Dimensional Matching @{thm is_reduction_xc_to_three_dm}
        \<^item> Exact Cover by 3-Sets @{thm is_reduction_three_dm_to_x3c}
          \<^item> Steiner Tree @{thm is_reduction_X3C_to_steiner_tree}
      \<^item> Exact Hitting Set @{thm is_reduction_xc_to_ehs}
  \<^item> Independent Set @{thm is_reduction_sat_is}
    \<^item> Vertex Cover @{thm is_reduction_is_vc}
      \<^item> Hamiltonian Cycle @{thm is_reduction_vc_to_hc}
        \<^item> Undirected Hamiltonian Cycle @{thm is_reduction_hc_uhc}
      \<^item> Set Cover @{thm is_reduction_vc_sc}
      \<^item> Feedback Arc Set @{thm is_reduction_vc_to_fas}
      \<^item> Feedback Node Set @{thm is_reduction_vc_to_fns}
  \<^item> Clique @{thm is_reduction_sat_to_clique}
    \<^item> Set Packing @{thm is_reduction_clique_to_set_packing}
\<close>

end
