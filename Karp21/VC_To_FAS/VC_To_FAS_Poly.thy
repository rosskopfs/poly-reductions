theory VC_To_FAS_Poly
  imports
    Polynomial_Reductions
    Poly_Library
    VC_To_FAS
begin

definition H' where
  "H' v a \<equiv> \<lparr>
        verts = v,
        arcs = a,
        tail = fst, head = snd \<rparr>"

lemma H_eq_H':
"H E =
  H' ((\<Union>E) \<times> {False, True})
     ({((u, False), (u, True)) |u. u \<in> \<Union> E } \<union> {((u, True), (v, False)) |u v. {u,v} \<in> E})"
unfolding H_def H'_def by blast

definition "vc_to_fas_poly ≡ λ(E, K). do {
  fin ← mop_set_finite E;
  e_card ← mop_set_for_all E (λe. card e = 2) (λ_. 1);
  if fin ∧ e_card then do {
    union ← mop_set_Union E;
    card_union ← mop_set_card union;
    if K ≤ card_union then do {
      verts ← mop_set_times union ({False, True});

      cross ← mop_set_times union union;
      arcs1 ← nrest_image (λu. ((u, False), (u, True))) (λ_. 1) union;
      arcs2 ← nrest_filter_image
              (λ(u, v). ((u, True), (v, False))) (λ_. 1)
              (λ(u, v). {u, v} ∈ E) (λ_. card E) cross;

      arcs ← mop_set_union arcs1 arcs2;

      RETURNT ((H' verts arcs), K)
    } else RETURNT (MALFORMED_GRAPH, K)
  } else RETURNT (MALFORMED_GRAPH, K)
}"

term "verts (h :: ('a × bool, ('a × bool) × 'a × bool) pre_digraph)"
term "arcs (h :: ('a × bool, ('a × bool) × 'a × bool) pre_digraph)"

definition "size_VC ≡ λ(E, K). card E + nat_encoded_size K"
definition "size_FAS ≡ λ(H, K). card (verts H) + card (arcs H) + nat_encoded_size K"

definition "vc_to_fas_space n ≡ 6 * n + 4 * n * n"
definition "vc_to_fas_time n ≡
  1 + n +
  2 * n + 1 +
  4 * n +

  4 * n * n +
  2 * n +
  4 * n * n * n +
  4 * n * n * n + 2 * n"

lemma pair_image_list_inj_on: "inj_on (λ(u,v). ((u, True), (v, False))) { (u, v) . (u,v) ∈ S}"
using inj_on_def by fast

lemma inj_on_subset:
assumes "inj_on f S"
shows "inj_on f { s ∈ S. P s}"
using assms inj_on_subset by fastforce

lemma card_image_cross_to_arcs:
assumes "finite S" and "∀s ∈ S. finite s"
shows "card ((λ(u,v). ((u, True), (v, False))) ` { (u, v) ∈ (⋃ S) × (⋃ S). {u, v} ∈ S })
      ≤ card ((⋃ S) × (⋃ S))"
proof -
  have "inj_on (λ(u,v). ((u, True), (v, False))) { (u, v) ∈ (⋃ S) × (⋃ S). {u, v} ∈ S }"
    using inj_on_subset[OF pair_image_list_inj_on]
    by (simp add: inj_on_def)
  then show ?thesis
    using card_image le_eq_less_or_eq by blast
qed

lemma vc_to_fas_size: "size_FAS (vc_to_fas E) ≤ vc_to_fas_space (size_VC E)"
apply (cases E)
apply (simp add: vc_to_fas_def size_FAS_def vc_to_fas_space_def size_VC_def)
apply (intro impI conjI)
apply (simp add: VC_To_FAS.H_def)
subgoal for a b
proof -
  let ?A = "⋃ a"
  let ?arc1 = "{((u, False), (u, True)) | u. u \<in> ?A }"
  let ?arc2 = "{((u, True), (v, False)) |u v. {u,v} \<in> a}"
  let ?n = "nat_encoded_size b"

  assume assms: "finite a ∧ b ≤ card ?A ∧ (∀e∈a. card e = 2)"
  then have finite_a_inner: "∀e∈a. finite e"
    using card_ge_0_finite by force

  have "sum card a = 2 * card a" using assms by simp
  then have card_A_bound[simp]: "card ?A ≤ 2 * card a" using assms
    by (metis card_Union_le_sum_card)

  have a: "card (?A × {False, True}) ≤ 4 * card a"
    by (metis card_cartesian_product card_doubleton_eq_2_iff card_A_bound)

  have "inj_on (λu. ((u, False), (u, True))) ?A"
    by (auto simp: inj_on_def)
  moreover have "card ((λu. ((u, False), (u, True))) ` ?A) = card ?A"
    using card_image by blast
  moreover have "((λu. ((u, False), (u, True))) ` ?A) = ?arc1" by blast
  ultimately have "card ?arc1 = card ?A" by argo
  then have b: "card ?arc1 ≤ 2 * card a" using card_A_bound
    by argo

  have "?arc2 = (λ(u,v). ((u, True), (v, False))) ` {(u, v) ∈ ?A × ?A. {u, v} ∈ a}"
    by fast
  then have "card ?arc2 ≤ card (?A × ?A)"
    using card_image_cross_to_arcs finite_a_inner assms
    by fastforce
  also have "... = card ?A * card ?A" using card_cartesian_product
    by fast
  also have "... ≤ 2 * card a * card ?A" by fastforce
  also have "... ≤ 4 * card a * card a" by fastforce
  also have "... ≤ 4 * (card a + ?n) * card a" by fastforce
  also have "... ≤ 4 * (card a + ?n) * (card a + ?n)" by fastforce
  also have "... = (4 * card a + 4 * ?n) * (card a + ?n)" by fastforce

  finally have "card (?A × {False, True}) + card ?arc1 + card ?arc2
    ≤ 4 * card a + 2 * card a + (4 * card a + 4 * ?n) * (card a + ?n)"
    using a b by linarith
  also have "... = 6 * card a + ((4 * card a + 4 * ?n) * (card a + ?n))"
    by fastforce
  also have "... ≤ 5 * ?n + (6 * card a + ((4 * card a + 4 * ?n) * (card a + ?n)))"
    by fastforce
  finally show ?thesis using card_Un_le[of ?arc1 ?arc2]
    by simp
qed
by (simp add: MALFORMED_GRAPH_def nat_encoded_size_def)

lemma vc_to_fas_refines:
  "vc_to_fas_poly VC
  ≤ SPEC (λy. y = vc_to_fas VC) (λ_. vc_to_fas_time (size_VC VC))"
unfolding SPEC_def vc_to_fas_poly_def vc_to_fas_def vc_to_fas_time_def size_VC_def
  mop_set_finite_def mop_set_for_all_def mop_set_Union_def mop_set_card_def
  mop_set_times_def mop_set_union_def nrest_image_def nrest_filter_image_def
  H_def H'_def
apply (rule T_specifies_I)
apply(vcg' \<open>-\<close> rules: T_SPEC)
apply (simp_all)
subgoal for a b
sorry
subgoal for a b
sorry
apply (simp add: MALFORMED_GRAPH_def)
sorry

end
