theory VC_To_HC
  imports  Main "../TSAT_To_SC/TSAT_To_SC" Graph_Theory.Digraph  Graph_Theory.Arc_Walk
    Graph_Theory.Vertex_Walk
    "Poly_Reductions_Lib.List_Auxiliaries" "VC_To_HC_1" "VC_To_HC_2"
    Definitions_HC
begin

subsection\<open>Main theorem\<close>

lemma vc_impl_hc: "(E,k) \<in> vertex_cover_list \<Longrightarrow> vc_hc (E,k) \<in> hc"
proof -
  assume in_vc: "(E,k)\<in> vertex_cover_list"
  then obtain Cov where "is_vertex_cover_list E Cov" "distinct Cov" "size Cov = k"
    using vertex_cover_list_def
    by (smt case_prodD mem_Collect_eq)
  then show ?thesis
    using vc_impl_hc_context in_vc
    by blast
qed

lemma hc_impl_vc: "vc_hc (E,k) \<in> hc \<Longrightarrow> (E,k) \<in> vertex_cover_list"
proof -
  assume in_hc: "vc_hc (E, k) \<in> hc"
  obtain Cycle where Cycle_def: "is_hc (vc_hc (E, k)) Cycle"
    using hc_def in_hc
    by auto
  obtain Cov where Cov_def: "Cov ={v|v e i j. (Cover j, Edge v e i) \<in> set (vwalk_arcs Cycle)}"
    by simp
  then show ?thesis
    using hc_impl_vc_context in_hc Cycle_def Cov_def
    by fastforce
qed

theorem is_reduction_vc_to_hc:
  "is_reduction vc_hc vertex_cover_list hc"
  unfolding is_reduction_def using vc_impl_hc hc_impl_vc by auto

end
