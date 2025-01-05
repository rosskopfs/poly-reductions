theory All_Reductions
  imports
    "3DM_To_X3C/Three_DM_To_X3C"
    "CNF_SAT_To_Clique/CNF_SAT_To_Clique"
    "HC_To_UHC/HC_To_UHC"
    "SAT_To_XC/SAT_To_XC"
    "CNF_SAT_To_TC/TS_To_TC"
    "TC_To_ChrN/TC_To_ChrN"
    "VC_Set_To_VC_List/VC_Set_To_VC_List"
    "VC_To_FAS/VC_To_FAS"
    "VC_To_FNS/VC_To_FNS"
    "VC_To_HC/VC_To_HC"
    "X3C_To_ST/X3C_To_ST"
    "XC_To_3DM/Exact_Cover_To_3D_Matching"
    "XC_To_EHS/XC_To_EHS"
    "XC_To_SS/XC_To_SS"
    "SS_To_JS/SS_To_JS_aux"
    "XC_To_3DM/Three_DM_Definition"
    "THREE_SAT_To_SC/Three_Sat_To_Set_Cover"
    "XC_To_SS/SS_To_SS_List"
    "ChrN_To_CC/ChrN_To_CC"
    "Clique_To_SP/Clique_To_SP"
    "SAT_To_3SAT/SAT_To_AT_MOST_3SAT"
    "SAT_To_3SAT/AT_MOST_3SAT_To_3SAT"
    "PART_To_MAXCUT/PART_To_MAXCUT"
    "SS_To_PART/SS_To_PART"
    "SS_To_ZERO_ONE/SS_To_ZERO_ONE"
    "SS_To_KS/SS_To_KS"
begin

section \<open>Overview of reductions\<close>

text \<open>
  \<^item> SAT 
    \<^item> 3-SAT @{thm is_reduction_sat_to_at_most_3sat}
      \<^item> 3-SAT @{thm is_reduction_at_most_3sat_to_3sat}
        \<^item> 3-Colorability @{thm is_reduction_sat_tc} 
         \<^item> Chromatic Number @{thm is_reduction_threeC_chrN} 
          \<^item> Clique Cover  @{thm is_reduction_chrn_to_cc} 
    \<^item> Exact Cover @{thm is_reduction_sat_xc} 
      \<^item> Subset Sum @{thm is_reduction_xc_to_ss}    
        \<^item> Job Sequencing @{thm is_reduction_ss_list_to_job_seq}{
        \<^item> Partition @{thm is_reduction_ss_list_to_part}
           \<^item> Max Cut @{thm is_reduction_part_to_maxcut}
        \<^item> Zero-One Integer Programming @{thm is_reduction_ss_int_list_to_zero_one_int_prog}
        \<^item> Knapsack @{thm is_reduction_ss_to_ks}
      \<^item> Three-Dimensional Matching @{thm is_reduction_xc_to_3dm}
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
  \<^item> Clique @{thm is_reduction_cnf_sat_to_clique}
    \<^item> Set Packing @{thm is_reduction_clique_to_set_packing}
\<close>

text \<open> * Karp's knapsack corresponds to the modern Subset Sum.
       * Independent Set is not one of Karps' 21 \<close>
   

section \<open>Full list (includes variations of the same problem)\<close>
text \<open>
  \<^item> SAT
    \<^item> 3-SAT @{thm is_reduction_sat_to_at_most_3sat}
      \<^item> 3-SAT @{thm is_reduction_at_most_3sat_to_3sat}
       \<^item> 3-Colorability @{thm is_reduction_sat_tc}
        \<^item> Chromatic Number @{thm is_reduction_threeC_chrN}
          \<^item> Clique Cover  @{thm is_reduction_chrn_to_cc}    
    \<^item> Exact Cover @{thm is_reduction_sat_xc}
      \<^item> Subset Sum @{thm is_reduction_xc_to_ss}
        \<^item> Subset Sum (List) @{thm is_reduction_ss_indeces_to_ss_list}
           \<^item> Job Sequencing @{thm is_reduction_ss_list_to_job_seq}
           \<^item> Partition @{thm is_reduction_ss_list_to_part}
              \<^item> Max Cut @{thm is_reduction_part_to_maxcut}
           \<^item> Subset Sum (Int List) @{thm is_reduction_ss_lift_to_int}
             \<^item> Zero-One Integer Programming @{thm is_reduction_ss_int_list_to_zero_one_int_prog}
        \<^item> Knapsack @{thm is_reduction_ss_to_ks}
      \<^item> Three-Dimensional Matching @{thm is_reduction_xc_to_3dm}
        \<^item> Three-Dimensional Matching (Alt1) @{thm is_reduction_3dm_to_alt1}
        \<^item> Three-Dimensional Matching (Alt2) @{thm is_reduction_3dm_to_alt2}
        \<^item> Exact Cover by 3-Sets @{thm is_reduction_three_dm_to_x3c}
          \<^item> Steiner Tree @{thm is_reduction_X3C_to_steiner_tree}
      \<^item> Exact Hitting Set @{thm is_reduction_xc_to_ehs}
  \<^item> Independent Set @{thm is_reduction_sat_is}
    \<^item> Vertex Cover @{thm is_reduction_is_vc}
      \<^item> Vertex Cover (List) @{thm is_reduction_vc}
        \<^item> Hamiltonian Cycle @{thm is_reduction_vc_to_hc}
          \<^item> Undirected Hamiltonian Cycle @{thm is_reduction_hc_uhc}
      \<^item> Set Cover @{thm is_reduction_vc_sc}
      \<^item> Feedback Arc Set @{thm is_reduction_vc_to_fas}
      \<^item> Feedback Node Set @{thm is_reduction_vc_to_fns}
  \<^item> Clique @{thm is_reduction_cnf_sat_to_clique}
    \<^item> Set Packing  @{thm is_reduction_clique_to_set_packing}
\<close>

end