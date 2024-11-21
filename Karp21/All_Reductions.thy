theory All_Reductions
  imports
    "Three_DM_To_X3C"
    "CNF_SAT_To_Clique"
    "HC_To_UHC"
    "SAT_To_XC"
    "TC_To_ChrN"
    "VC_Set_To_VC_List"
    "VC_To_FAS"
    "VC_To_FNS"
    "VC_To_HC"
    "X3C_To_ST"
    "Exact_Cover_To_3D_Matching"
    "XC_To_EHS"
    "XC_To_SS"
    "XC_To_ST_Karp72"
begin

section \<open>Overview of reductions\<close>
text \<open>
  \<^item> SAT
    \<^item> Clique @{thm is_reduction_cnf_sat_to_clique}
      \<^item> Set Packing
      \<^item> Node Cover
        \<^item> Feedback Node Set
        \<^item> Feedback Arc Set
        \<^item> Directed Hamilton Circuit
          \<^item> Undirected Hamilton Circuit
        \<^item> Set Covering
    \<^item> 0-1 Integer Programming
    \<^item> 3-SAT
      \<^item> Chromatic Number
      \<^item> Exact Cover
        \<^item> 3-Dimensional Matching
        \<^item> Hitting Set
        \<^item> Steiner Tree
      \<^item> Knapsack
        \<^item> Sequencing
        \<^item> Partition
          \<^item> Max Cut
\<close>

end