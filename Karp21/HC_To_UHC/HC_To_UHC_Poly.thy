theory HC_To_UHC_Poly
  imports "../THREE_SAT_To_SC/TSTSC_Poly" HC_To_UHC
begin

subsection\<open>The reduction from \<open>HC\<close> to \<open>UHC\<close> is polynomial\<close>
subsubsection\<open>Definitions\<close>

definition "size_uhc = (\<lambda>G. card (verts G) + card (arcs G))"
definition "size_hc = (\<lambda>G. card (verts G))"
definition "hc_to_uhc_space n  = 3 * n+ 9 * n * n + 2"

definition "mop_check_wf_digraph Gr = SPECT [wf_digraph Gr \<mapsto> 1]"
definition "mop_check_finite Gr = SPECT [finite (verts Gr) \<mapsto> 1]"
definition "mop_check_functions Gr = SPECT [((tail Gr = fst \<and> head Gr = snd) \<or> arcs Gr = {}) \<mapsto> 3]"

definition "mop_verts_G Gr = SPECT [ {(v, (0::nat))|v. v \<in> verts Gr} \<union> {(v, 1)|v. v \<in> verts Gr}
  \<union> {(v, 2)|v. v \<in> verts Gr} \<mapsto> 3 * (card (verts Gr))]"

definition "mop_arcs_G Gr = SPECT [
            {((v, 0), (v, 1))|v. v \<in> verts Gr} \<union>{((v, 1), (v, 0))|v. v \<in> verts Gr}\<union>
          {((v, 1), (v, 2))|v. v \<in> verts Gr}\<union>{((v, 2), (v, 1))|v. v \<in> verts Gr}\<union>
          {((v, 2), (u, 0))|v u e. e \<in> arcs Gr \<and> v = tail Gr e \<and> u = head Gr e \<and> u \<noteq> v}\<union>
          {((u, 0), (v, 2))|v u e. e \<in> arcs Gr \<and> v = tail Gr e \<and> u = head Gr e \<and> u \<noteq> v}
    \<mapsto> 3 * card (verts Gr) * 3 * (card (verts Gr))]"

definition "hc_to_uhc_alg = (\<lambda>G.
  do {
    bg \<leftarrow> mop_check_wf_digraph G;
    bfu  \<leftarrow> mop_check_functions G;
    bfi \<leftarrow> mop_check_finite G;
    cVG \<leftarrow> mop_set_card (verts G);
    if bg \<and> bfu then
      do {
        if bfi then
        do {
          if cVG > 1 then
          do {
            V \<leftarrow> mop_verts_G G;
            E  \<leftarrow> mop_arcs_G G;
            RETURNT \<lparr>verts = V, arcs = E, tail = fst, head = snd\<rparr>
          }
          else RETURNT \<lparr>verts = {}, arcs = {}, tail = fst, head = snd\<rparr>
        }
        else RETURNT \<lparr>verts = {(v, 0)|v. v \<in> verts G}, arcs = {}, tail = fst, head = snd\<rparr>
      }
    else RETURNT (let x = (SOME x. x \<in> arcs G) in
      \<lparr>verts = {}, arcs = {((head G x, 0), (head G x, 1))}, tail = fst, head = snd\<rparr>)
  } )"

definition "hc_to_uhc_time n = 6 + 3*n + 3 * n * 3 * n"


subsubsection\<open>Auxiliary proofs\<close>

lemma wf_digraph_card_arcs:
  assumes "wf_digraph Gr" "(tail Gr = fst \<and> head Gr = snd) \<or> arcs Gr = {}"
    "finite (verts Gr)"
  shows "card (arcs Gr) \<le> card (verts Gr) * card (verts Gr)"
proof -
  have "arcs Gr \<subseteq> (verts Gr)\<times> (verts Gr)"
    using assms wf_digraph.head_in_verts wf_digraph.tail_in_verts by fastforce
  then show ?thesis
    using assms by (metis card_cartesian_product card_mono finite_cartesian_product_iff)
qed

lemma card_verts:
  assumes "finite (verts Gr)"
  shows "card (verts (hc_to_uhc Gr)) \<le> 3 * card (verts Gr)"
proof -
  let ?S1 = "{(v, 0::nat)|v. v \<in> verts Gr}" and ?S2 = "{(v, 1::nat)|v. v \<in> verts Gr}"
      and ?S3 = "{(v, 2::nat)|v. v \<in> verts Gr}"
  from assms have
    "card ?S1 \<le> card (verts Gr)" "card ?S2 \<le> card (verts Gr)" "card ?S3 \<le> card (verts Gr)"
    by (auto intro: card_image_le simp: setcompr_eq_image)
  then have "card ?S1 + card ?S2 + card ?S3 \<le> 3 * card (verts Gr)" (is "?lhs \<le> _")
    by auto
  also have "card (?S1 \<union> ?S2 \<union> ?S3) \<le> ?lhs"
    by (rule order.trans, rule card_Un_le) (intro order.refl add_mono card_Un_le)
  ultimately show ?thesis
    using \<open>finite (verts Gr)\<close> unfolding hc_to_uhc_def by (auto simp: Let_def)
qed

lemma card_arcs:
  assumes "finite (verts Gr)" "wf_digraph Gr" "(tail Gr = fst \<and> head Gr = snd) \<or> arcs Gr = {}"
  shows "card(arcs (hc_to_uhc Gr)) \<le> 9 * (card (verts Gr)) * (card (verts Gr))"
proof -
  have "finite (verts (hc_to_uhc Gr))"
    "tail (hc_to_uhc Gr) = fst \<and> head (hc_to_uhc Gr) = snd"
    "wf_digraph (hc_to_uhc Gr)"
    using assms by (auto simp: hc_to_uhc_def wf_digraph_def)
  then have 2: "card (arcs (hc_to_uhc Gr))
      \<le> card (verts (hc_to_uhc Gr)) * card (verts (hc_to_uhc Gr))"
    using wf_digraph_card_arcs by blast
  have "card (verts (hc_to_uhc Gr)) \<le> 3 * card (verts Gr)"
    using assms card_verts assms(1) by auto
  then have "card (arcs (hc_to_uhc Gr)) \<le> 3 * card (verts Gr)* 3 * card (verts Gr)"
    using 2 by (smt le_trans mult.assoc mult_le_mono)
  then show ?thesis
    using assms wf_digraph_card_arcs card_verts by linarith
qed

lemma aux1:
  assumes "finite (verts Gr)" "wf_digraph Gr" "(tail Gr = fst \<and> head Gr = snd) \<or> arcs Gr = {}"
  shows "card (verts (hc_to_uhc Gr))+ card(arcs (hc_to_uhc Gr))
        \<le> 3 * card (verts Gr) + 9 * card (verts Gr) * card (verts Gr)" (is "?A + ?B \<le> ?C")
proof -
  have 1: "?A \<le> 3 * card (verts Gr)"
    using card_verts assms not_wf_digraph_not_arcs_empty by auto
  have "?B \<le> 9 * card (verts Gr) * card (verts Gr)"
    using card_arcs assms not_wf_digraph_not_arcs_empty by auto
  then show ?thesis
    using 1 by simp
qed


subsubsection \<open>Main proofs\<close>

lemma vcs_to_vcl_size: "size_uhc (hc_to_uhc Gr) \<le> hc_to_uhc_space (size_hc Gr)"
proof -
  consider (inf) "infinite (verts Gr)"
    | (not_wf) "\<not> wf_digraph Gr"
    | (not_wf2) "\<not> ((tail Gr = fst \<and> head Gr = snd) \<or> arcs Gr = {})"
    | (wf) "finite (verts Gr)" "wf_digraph Gr" "(tail Gr = fst \<and> head Gr = snd) \<or> arcs Gr = {}"
    by auto
  then show ?thesis
  proof cases
    case inf
    have "infinite {(v, 0 :: nat) |v. v \<in> verts Gr}"
    proof (rule ccontr, simp)
      assume "finite {(v, 0) |v. v \<in> verts Gr}"
      moreover have "verts Gr = fst ` {(v, 0) |v. v \<in> verts Gr}"
        by auto
      ultimately show False
        by (smt inf finite_imageI)
    qed
    then show ?thesis
      by (auto simp: Let_def hc_to_uhc_def size_uhc_def hc_to_uhc_space_def)
  next
    case wf
    then show ?thesis
      using card_arcs card_verts
      by (simp add: size_uhc_def hc_to_uhc_space_def HC_To_UHC_Poly.aux1 le_SucI size_hc_def)
  qed (auto simp: Let_def hc_to_uhc_def size_uhc_def hc_to_uhc_space_def)
qed

lemma vcs_to_vcl_refines:
  "hc_to_uhc_alg Gr \<le> SPEC (\<lambda>y. y = (hc_to_uhc Gr)) (\<lambda>_. hc_to_uhc_time (size_hc Gr))"
  unfolding SPEC_def
  unfolding hc_to_uhc_alg_def hc_to_uhc_def
    mop_check_ugraph_def  mop_check_wf_digraph_def mop_check_functions_def mop_check_finite_def
    mop_arcs_G_def mop_verts_G_def mop_set_card_def
  by (rule T_specifies_I, vcg' \<open>-\<close> rules: T_SPEC )
     (auto simp: hc_to_uhc_time_def one_enat_def size_hc_def numeral_eq_enat)

theorem cnf_sat_to_clique_ispolyred: "ispolyred hc_to_uhc_alg hc uhc size_hc size_uhc"
  unfolding ispolyred_def
  apply(rule exI[where x=hc_to_uhc])
  apply(rule exI[where x=hc_to_uhc_time])
  apply(rule exI[where x=hc_to_uhc_space])
  apply(safe)
  subgoal using vcs_to_vcl_refines by blast
  subgoal using vcs_to_vcl_size by blast
  subgoal unfolding poly_def hc_to_uhc_time_def apply(rule exI[where x=2]) by auto
  subgoal unfolding poly_def hc_to_uhc_space_def apply(rule exI[where x=2]) by auto
  subgoal using is_reduction_hc_uhc .
  done

end