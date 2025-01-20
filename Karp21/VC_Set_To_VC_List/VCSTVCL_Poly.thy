theory VCSTVCL_Poly
  imports "../TSAT_To_SC/TSTSC_Poly" VC_Set_To_VC_List
begin

subsection\<open>The reduction from \<open>VC_Set\<close> to \<open>VC_List\<close> is polynomial\<close>
subsubsection\<open>Definitions\<close>

definition "size_VC_List = (\<lambda>(E,k). length E)"
definition "vcs_to_vcl_space n  = n"

definition "mop_set_to_list_2 S = SPEC (\<lambda>xs. xs = (SOME L. (set L = S  \<and> distinct L))) (\<lambda>_. card S)"

definition "vcs_to_vcl = (\<lambda>(E,k).
  do {
    b \<leftarrow> mop_check_ugraph E;
    V  \<leftarrow> mop_get_vertices E;
    cV \<leftarrow> mop_set_card V;
    if b \<and> k \<le> cV then
      do {
        es \<leftarrow> mop_set_to_list_2 E;
        RETURNT (es, k)
      }
    else RETURNT ( [], 1 )
  } )"

definition "vcs_vcl_time n = 1+ (2 * n + 1) + 1 + n"


subsubsection\<open>Proofs\<close>

lemma vcs_to_vcl_size: "size_VC_List (vc_set_to_vc_list (E, k)) \<le> vcs_to_vcl_space (size_VC (E, k))"
  apply(simp add: size_VC_List_def vc_set_to_vc_list_def vcs_to_vcl_space_def size_VC_def
          set_to_list_def)
  by (metis (mono_tags, lifting) distinct_size eq_imp_le finite_UnionD
      finite_distinct_list tfl_some ugraph_vertex_set_finite)

lemma vcs_to_vcl_reifnes:
  "vcs_to_vcl (E, k) \<le> SPEC (\<lambda>y. y = (vc_set_to_vc_list (E, k))) (\<lambda>_. vcs_vcl_time (size_VC (E, k)))"
  unfolding SPEC_def
  unfolding vcs_to_vcl_def vc_set_to_vc_list_def
    mop_check_ugraph_def  mop_get_vertices_def mop_set_card_def
    mop_set_to_list_2_def set_to_list_def
  apply(rule T_specifies_I)
  apply(vcg' \<open>-\<close> rules: T_SPEC )
  by(auto simp: vcs_vcl_time_def size_VC_def set_set_to_list distinct_set_to_list
      one_enat_def)

theorem cnf_sat_to_clique_ispolyred:
  "ispolyred vcs_to_vcl vertex_cover vertex_cover_list size_VC size_VC_List"
  unfolding ispolyred_def
  apply(rule exI[where x=vc_set_to_vc_list])
  apply(rule exI[where x=vcs_vcl_time])
  apply(rule exI[where x=vcs_to_vcl_space])
  apply(safe)
  subgoal using vcs_to_vcl_reifnes by blast
  subgoal using vcs_to_vcl_size by blast
  subgoal unfolding poly_def vcs_vcl_time_def apply(intro exI[where x=2]) by auto
  subgoal unfolding poly_def vcs_to_vcl_space_def apply(intro exI[where x=2]) by auto
  subgoal using is_reduction_vc .
  done

end
