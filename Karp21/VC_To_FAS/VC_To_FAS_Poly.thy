theory VC_To_FAS_Poly
  imports
    Polynomial_Reductions
    Poly_Library
    VC_To_FAS
begin

definition H' where
  "H' v a ≡ ⦇
        verts = v,
        arcs = a,
        tail = fst, head = snd ⦈"

lemma H_eq_H':
"H E =
  H' ((⋃E) × {False, True})
     ({((u, False), (u, True)) |u. u ∈ ⋃ E } ∪ {((u, True), (v, False)) |u v. {u,v} ∈ E})"
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
definition "vc_to_fas_time n ≡ 2 + 11 * n + 12 * n * n + 4 * n * n * n"

lemma pair_image_list_inj_on: "inj_on (λ(u,v). ((u, True), (v, False))) { (u, v) . (u,v) ∈ S}"
using inj_on_def by fast

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
  let ?arc1 = "{((u, False), (u, True)) | u. u ∈ ?A }"
  let ?arc2 = "{((u, True), (v, False)) |u v. {u,v} ∈ a}"
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
apply(vcg' ‹-› rules: T_SPEC)
apply (simp_all add: of_nat_eq_enat)
subgoal for E K
apply (intro impI conjI)
apply fast
subgoal proof -
  let ?u = "⋃ E"
  let ?card = "card E"
  let ?card_u = "card (⋃ E)"
  let ?cross = "(⋃ E) × (⋃ E)"
  let ?enc_k = "nat_encoded_size K"

  assume e: "finite E ∧ (∀s∈E. card s = 2)" and k: "K ≤ ?card_u"

  from e have card_u_bound: "?card_u ≤ 2 * ?card"
    using card_union_if_all_subsets_card_i
    by fastforce

  have card_bound: "?card ≤ ?card + ?enc_k"
    unfolding nat_encoded_size_def by force

  from e have inner_finite: "∀s ∈ E. finite s"
    using card_ge_0_finite by force

  from e have finite_a_inner: "∀e∈E. finite e"
    using card_ge_0_finite by force
  hence finite_u: "finite ?u" using finite_union_if_all_subset_fin[of E] e
    by fastforce

  from card_u_bound have card_cross: "card ?cross ≤ 4 * ?card * ?card"
  using card_cartesian_product[of ?u ?u] mult_le_mono[of ?card_u "2 * ?card" ?card_u "2 * ?card"]
    by linarith

  let ?a = "1 + enat ?card + enat (?card * 2) + 1 + enat (?card_u + ?card_u) + enat (?card_u * ?card_u) + enat ?card_u"
  let ?a_nat = "1 + ?card + ?card * 2 + 1 + ?card_u + ?card_u + ?card_u * ?card_u + ?card_u"
  have a_eq_nat: "?a = ?a_nat"
    by (simp add: add.assoc one_enat_def)

  have "?a_nat ≤
        1 + ?card + ?card * 2 + 1 + 2 * ?card + 2 * ?card + 2 * ?card * 2 * ?card + 2 * ?card"
      using card_u_bound mult_le_mono by fastforce
  then have a: "?a_nat ≤ 2 + 9 * ?card + 4 * ?card * ?card"
    by simp

  let ?b = "(∑a∈ ?cross . enat ?card + (if case a of (u, v) ⇒ {u, v} ∈ E then 1 else 0))"
  let ?b_nat = "(∑a∈ ?cross . ?card + (if case a of (u, v) ⇒ {u, v} ∈ E then 1 else 0))"

  have sum_enat_nat: "⋀ A f. (∑ a ∈ A. enat (f a)) = enat (∑ a ∈ A. f a)"
    by (metis (no_types, lifting) of_nat_eq_enat of_nat_sum sum.cong)
  have "∀a. enat (card E) + (if case a of (u, v) ⇒ {u, v} ∈ E then 1 else 0) =
          enat (card E + (if case a of (u, v) ⇒ {u, v} ∈ E then 1 else 0))"
    by (simp add: one_enat_def)
  then have "?b = (∑a∈ ?cross . enat (?card + (if case a of (u, v) ⇒ {u, v} ∈ E then 1 else 0)))"
     by presburger
  also have  "... = enat ?b_nat"
    using sum_enat_nat[of "λa. ?card + (if case a of (u, v) ⇒ {u, v} ∈ E then 1 else 0)" ?cross]
    by force
  finally have b_eq_nat: "?b = ?b_nat" .

  have "?b_nat ≤ (∑a∈ ?cross . ?card + 1)"
    using sum_mono[of ?cross _ "λ_. ?card + 1"]
    by simp
  also have "... ≤ card ?cross * (?card + 1)" by fastforce
  also have "... ≤ 4 * ?card * ?card * (?card + 1)" using card_cross mult_le_mono
    by blast
  also have "... = 4 * ?card * ?card * ?card + 4 * ?card * ?card" by simp
  finally have b: "?b_nat ≤ 4 * ?card * ?card * ?card + 4 * ?card * ?card" .

  let ?c = "card ((λu. ((u, False), u, True)) ` ?u)"
  from finite_u have "?c ≤ ?card_u" using card_image_le e
    by blast
  then have c: "?c ≤ 2 * ?card" using card_u_bound
    by linarith

  let ?d = "card ((λ(u, v). ((u, True), v, False)) ` { (u,v) ∈ ?cross. {u, v} ∈ E})"
  have "?d ≤ card ?cross" using e card_image_cross_to_arcs inner_finite
    by blast
  hence d: "?d ≤ 4 * ?card * ?card" using card_cross by linarith

  have *: "?a + ?b + ?c + ?d = enat (?a_nat + ?b_nat + ?c + ?d)"
    using a_eq_nat b_eq_nat plus_enat_simps(1) by presburger
  have "?a_nat + ?b_nat + ?c + ?d ≤
    2 + 9 * ?card + 4 * ?card * ?card + 4 * ?card * ?card * ?card +
    4 * ?card * ?card + 2 * ?card + 4 * ?card * ?card"
    using a b c d by simp

  also have "... = 2 + 11 * ?card + 12 * ?card * ?card + 4 * ?card * ?card * ?card"
    by algebra
  also have "... ≤ 2 + (11 * ?card + 11 * ?enc_k) + (12 * ?card + 12 * ?enc_k) * (?card + ?enc_k) +
                    (4 * ?card + 4 * ?enc_k) * (?card + ?enc_k) * (?card + ?enc_k)"
    by (simp add: algebra_simps card_bound)
  finally have **: "?a + ?b + ?c + ?d ≤
      2 + (11 * ?card + 11 * ?enc_k) + (12 * ?card + 12 * ?enc_k) * (?card + ?enc_k) +
          (4 * ?card + 4 * ?enc_k) * (?card + ?enc_k) * (?card + ?enc_k)"
      using * by fastforce

  have "{a ∈ ?cross. case a of (u, v) ⇒ {u, v} ∈ E}
        = {(u, v). Bex E ((∈) u) ∧ Bex E ((∈) v) ∧ {u, v} ∈ E}"
    by auto
  then have "?a + ?b +
    enat (card ((λu. ((u, False), u, True)) ` ?u)
      + card ((λ(u, v). ((u, True), v, False)) ` {a ∈ ?cross. case a of (u, v) ⇒ {u, v} ∈ E}))
      = ?a + ?b + ?c + ?d"
      by simp

  then show ?thesis using * ** add_2_eq_Suc[symmetric]
    by (smt (verit, del_insts) add.assoc)
qed
done
apply (simp add: one_enat_def)
apply (intro impI conjI)
by (simp_all add: MALFORMED_GRAPH_def one_enat_def)

theorem vc_to_fas_ispolyred:
  "ispolyred vc_to_fas_poly vertex_cover feedback_arc_set size_VC size_FAS"
unfolding ispolyred_def
apply(rule exI[where x=vc_to_fas])
apply(rule exI[where x=vc_to_fas_time])
apply(rule exI[where x=vc_to_fas_space])
apply safe
  subgoal using vc_to_fas_refines by blast
  subgoal using vc_to_fas_size by blast
  subgoal unfolding poly_def vc_to_fas_time_def apply(rule exI[where x=2]) by auto
  subgoal unfolding poly_def vc_to_fas_space_def apply(rule exI[where x=3]) by auto
  subgoal using is_reduction_vc_to_fas .
done

end

