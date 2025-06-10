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

term "mop_set_times E E"
term "nrest_image (λ(u, v). ((u, True), (v, False))) (λ_. 1) (E × E)"
term "nrest_image (λu. ((u, False), (u, True))) (λ_. 1) (⋃ E)"

find_consts "'a set => 'a list"

definition "vc_to_fas_poly ≡ λ(E, K). do {
  e_card ← mop_for_all_set E (λe. card e = 2) (λ_. 1);
  if e_card then do {
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

definition "vc_to_fas_space n ≡ 4 * n + 4 * n"
definition "vc_to_fas_time n ≡ 0"

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

  assume assms: "b ≤ card ?A ∧ (∀e∈a. card e = 2)"

  have "sum card a = 2 * card a" using assms by simp
  then have card_A_bound: "card ?A ≤ 2 * card a" using assms
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

  have c: "card ?arc2 ≤ 2 * card a" using assms
  sorry

  from a b c show ?thesis

  sorry
qed
by (simp add: MALFORMED_GRAPH_def nat_encoded_size_def)


end
