theory VCTFNS_Poly
  imports "../TSTSC_Poly" VC_To_FNS
begin

subsection\<open>The reduction from VC to FNS is polynomial\<close>

definition "size_fns = (\<lambda>(G,k). card (verts G)+ card (arcs G))"
definition "vc_to_fns_space n  = 2*n+2*n"

definition "mop_get_verts_fns E =SPECT [ {v. v \<in> \<Union> E} \<mapsto> 2*(card E)]"
definition "mop_get_arcs_fns E =SPECT [{(u, v)| u v. {u, v} \<in> E} \<mapsto> (2*(card E))]"

definition "vc_to_fns_alg = (\<lambda>(E,k).
  do {
    b \<leftarrow> mop_check_ugraph E;
    V  \<leftarrow> mop_get_vertices E;
    cV \<leftarrow> mop_set_card V;
    if b \<and> k \<le> cV then
      do {
        v \<leftarrow> mop_get_verts_fns E;
        e \<leftarrow> mop_get_arcs_fns E;
        RETURNT (\<lparr>verts = v, arcs = e, tail = fst, head = snd\<rparr>, k+1)
      }
    else RETURNT (\<lparr>verts = {}, arcs = {}, tail = fst, head = snd \<rparr>, 0)
  } )"

definition "vc_fns_time n = 1+ (2 * n + 1) + 1 + 2 * n + 2 * n"


subsubsection\<open>Auxiliary proofs\<close>

lemma e_in_E_e_explicit:
  assumes "e \<in> E" "ugraph E"
  shows "\<exists>u v. e = {u ,v} \<and> u \<noteq> v"
  using Set_Auxiliaries.e_in_E_e_explicit assms(1) assms(2) ugraph_def by blast

lemma card_verts_ugraph:
  assumes "ugraph E"
  shows "card (\<Union> E) \<le> 2 * card E"
  by (metis assms card_union_if_all_subsets_card_i le_refl ugraph_def)

lemma card_verts:
  assumes "ugraph E"
  shows "card {v. \<exists>x\<in>E. v \<in> x} \<le> 2 * (card E)"
proof -
  have 1: "{v. \<exists>x\<in>E. v \<in> x} = \<Union> E"
    by blast
  have "card (\<Union> E) \<le> 2 * card E"
    using assms card_verts_ugraph by auto
  then show ?thesis
    using 1 by simp
qed

lemma card_arcs:
  assumes "ugraph E"
  shows "card {(u, v). {u, v} \<in> E} \<le> 2 * card E" (is "card ?S \<le> _")
  using assms unfolding ugraph_def by (simp add: card_ordered_pairs)

lemma card_G:
  assumes "ugraph E"
  shows "card {v. \<exists>x\<in>E. v \<in> x} + card {(u, v). {u, v} \<in> E} \<le> 4 * card E"
proof -
  have 1: "card {v. \<exists>x\<in>E. v \<in> x} \<le> 2 * card E"
    using card_verts assms by blast
  have 2: "card {(u, v). {u, v} \<in> E} \<le> 2 * card E"
    using card_arcs assms by blast
  then show ?thesis
    using 1 2 by auto
qed


subsubsection\<open>Main proofs\<close>

lemma vc_to_fns_size: "size_fns (vc_to_fns (E, k)) \<le> vc_to_fns_space (size_VC (E, k))"
  by (auto simp: size_fns_def vc_to_fns_space_def size_VC_def vc_to_fns_def card_G)

lemma vc_to_fns_reifnes:
  "vc_to_fns_alg (E, k) \<le> SPEC (\<lambda>y. y = (vc_to_fns (E, k))) (\<lambda>_. vc_fns_time (size_VC (E, k)))"
  unfolding SPEC_def vc_to_fns_alg_def vc_to_fns_def
    mop_check_ugraph_def  mop_get_vertices_def mop_set_card_def
    mop_get_verts_fns_def mop_get_arcs_fns_def
  apply(rule T_specifies_I)
  apply(vcg' \<open>-\<close> rules: T_SPEC )
  by(auto simp: vc_fns_time_def size_VC_def set_set_to_list distinct_set_to_list
      one_enat_def)

theorem  vc_to_fns_ispolyred: "ispolyred vc_to_fns_alg vertex_cover fns size_VC size_fns"
  unfolding ispolyred_def
  apply(rule exI[where x=vc_to_fns])
  apply(rule exI[where x=vc_fns_time])
  apply(rule exI[where x=vc_to_fns_space])
  apply(safe)
  subgoal using vc_to_fns_reifnes by blast
  subgoal using vc_to_fns_size by blast
  subgoal unfolding poly_def vc_fns_time_def apply(rule exI[where x=2]) by auto
  subgoal unfolding poly_def vc_to_fns_space_def apply(rule exI[where x=2]) by auto
  subgoal using is_reduction_vc_to_fns .
  done

end