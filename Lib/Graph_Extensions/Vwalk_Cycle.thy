theory Vwalk_Cycle
  imports
    List_Auxiliaries
    Graph_Auxiliaries
begin

section\<open>Vwalk_Cycle\<close>

subsection\<open>Definitions\<close>

definition vwalk_cycle where
  "vwalk_cycle G p \<equiv> distinct (tl p) \<and> vwalk p G \<and> hd p = last p \<and> length p \<ge> 2"


subsection\<open>Auxiliary proofs\<close>

lemma vwalk_cycle_rev:
  assumes "symmetric G" "vwalk_cycle G p"
  shows "vwalk_cycle G (rev p)"
  using assms unfolding vwalk_cycle_def
  by(auto simp add: distinct_tl_rev_C vwalk_rev_ex hd_rev last_rev)

lemma vwalk_cycle_not_empty:
  assumes "vwalk_cycle G p"
  shows "p \<noteq> []"
  using vwalk_cycle_def assms vwalk_def by auto

lemma vwalk_cycle_vwalk_arcs:
  assumes "vwalk_cycle G p"
  shows "vwalk_arcs p \<noteq> []"
  using assms vwalk_cycle_def vwalk_arcs_empty_length_p
  by (metis add_leD2 le_antisym nat_1_add_1 nat_le_iff_add num.distinct(1) one_eq_numeral_iff)

lemma vwalk_cycle_impl_cycle:
  assumes "head G = snd" "tail G = fst" "vwalk_cycle G p"
  shows "pre_digraph.cycle G (vwalk_arcs p)"
  using assms
  unfolding pre_digraph.cycle_def vwalk_cycle_def
  using assms vwalk_cycle_vwalk_arcs distinct_awalk_verts_vwalk_arcs awalk_vwalk_length_at_least_2
  by metis


subsubsection\<open>Cycle and Vwalk_cycle are the same\<close>

lemma cycle_implies_vwalk_cycle:
  assumes "head G = snd" "tail G = fst" "pre_digraph.cycle G (vwalk_arcs c)"
    "length c \<ge> 2" "wf_digraph G"
  shows "vwalk_cycle G c"
proof -
  have "\<forall>u. pre_digraph.awalk_verts G u (vwalk_arcs c) = c"
    using assms at_least_two_nodes_vwalk_arcs_awalk_verts
    by force
  then have 1: "distinct (tl c)"
    using assms pre_digraph.cycle_def
    by metis
  have 3: "vwalk c G"
    using assms  \<open>\<forall>u. pre_digraph.awalk_verts G u (vwalk_arcs c) = c\<close>
    by (metis wf_digraph.awalk_imp_vwalk wf_digraph.cycle_conv)
  have 4: "hd c = last c"
    using hd_last_cycle assms
    by metis
  then show ?thesis
    using 1 3 4 vwalk_cycle_def assms
    by blast
qed

end