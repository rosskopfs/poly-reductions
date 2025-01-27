theory HC_To_UHC
  imports
    HC_To_UHC_1
    HC_To_UHC_2
    Reductions
begin

subsection \<open>Main theorem\<close>

lemma hc_implies_uhc:
  assumes "G \<in> hc"
  shows "hc_to_uhc G \<in> uhc"
proof -
  obtain Cycle where 1: "is_hc G Cycle"
    using assms hc_def
    by auto
  obtain Cy where 2: "Cy = (hd Cycle, 2) # to_cycle_uhc G (tl Cycle)"
    by simp
  then show ?thesis using 1 2 in_uhc assms G_leq_1_vertex_in_uhc
    by blast
qed

lemma in_uhc_implies_in_hc:
  assumes "hc_to_uhc G \<in> uhc"
  shows "G \<in> hc"
proof -
  obtain G' where 0: "G' = hc_to_uhc G"
    by auto
  obtain Cy1 where 1: "is_uhc G' Cy1"
    using assms uhc_def 0
    by auto
  obtain Cy2 where 2: "Cy2 = rev Cy1"
    by simp
  obtain C1 where 3: "C1 = to_cycle_hc Cy1"
    by auto
  obtain C2 where 4: "C2 = to_cycle_hc Cy2"
    by auto
  then show ?thesis
    using 0 1 2 3 4 in_hc assms G_leq_1_vertex_in_uhc
    by blast
qed

theorem is_reduction_hc_uhc: "is_reduction hc_to_uhc hc uhc"
  using in_uhc_implies_in_hc hc_implies_uhc by (intro is_reductionI) auto

end