theory X3C_To_ST_Poly
  imports
    Polynomial_Reductions
    Poly_Library
    X3C_To_ST
begin

definition "X3C_to_steiner_tree_poly ≡ λ((X :: 'a set), S). do {
  b ← mop_set_for_all S (λs. card s = 3) (λ_. 1);
  if b then do {
    as ← nrest_image a (λ_. 1) X;
    cs ← nrest_image c (λ_. 1) S;

    v ← mop_set_union as {ROOT};
    all_v ← mop_set_union v cs;

    pairs ← nrest_image (λs. {ROOT, c s}) (λ_. 1) S;
    tmp ← nrest_image (λu. {{c u, a v} | v. v ∈ u}) (λu. card u) S;
    pairs' ← mop_set_Union tmp;

    all_pairs ← mop_set_union pairs pairs';

    union ← mop_set_union {ROOT} as;

    RETURNT (
      all_v,
      all_pairs,
      (λe. 1),
      union,
      4 * card X div 3
    )
  } else RETURNT NOT_STEINER_TREE_EXAMPLE
}"

\<comment> \<open>
definition "X3C_to_steiner_tree_poly ≡ λ((X :: 'a set), S). do {
  b ← mop_set_for_all S (λs. card s = 3) (λ_. 1); n
  if b then do {
    as ← nrest_image a (λ_. 1) X; n
    cs ← nrest_image c (λ_. 1) S; n

    v ← mop_set_union as {ROOT}; n + 1
    all_v ← mop_set_union v cs;  n + 1 + n

    pairs ← nrest_image (λs. {ROOT, c s}) (λ_. 1) S; n
    tmp ← nrest_image (λu. {{c u, a v} | v. v ∈ u}) (λu. card u) S; n * n
    pairs' ← mop_set_Union tmp; n * n * n?

    all_pairs ← mop_set_union pairs pairs'; n + n * n * n?

    union ← mop_set_union {ROOT} as; n

    RETURNT (
      all_v,
      all_pairs,
      (λe. 1),
      union,
      4 * card X div 3
    )
  } else RETURNT NOT_STEINER_TREE_EXAMPLE
}"
\<close>

definition "size_X3C ≡ λ(X, S). card X + card S + sum card S"
definition "size_ST ≡ λ(V, E, _, S, K). card V + sum card E + card S + nat_encoded_size K"

definition "X3C_to_steiner_tree_space n ≡ 3 + 6 * n"
definition "X3C_to_steiner_tree_time n ≡ 3 + 8 * n + 2 * n * n"

lemma inj_on_a: "inj_on a S"
by (meson inj_onI red_vertex.inject(1))

lemma inj_on_c: "inj_on c S"
by (meson inj_onI red_vertex.inject(2))

lemma inj_on_root: "inj_on (λs. {ROOT, c s}) S"
  unfolding inj_on_def by blast

lemma inj_on_f: "inj_on (λu. {{c u, a v} | v. v ∈ u}) S"
proof -
  let ?f = "(λu. {{c u, a v} | v. v ∈ u})"
  have "inj ?f" unfolding inj_def
    by (smt (z3) doubleton_eq_iff mem_Collect_eq red_vertex.inject(2)
                 red_vertex.simps(6) set_eq_iff)
  then show ?thesis
    by (metis (mono_tags, lifting) inj_def inj_onI)
qed

lemma sum_card_c_a:
  assumes "∀s∈S. card s = n"
  shows "sum card ((λu. {{c u, a v} | v. v ∈ u}) ` S) ≤ n * card S"
proof -
  let ?f = "(λu. {{c u, a v} | v. v ∈ u})"
  have card_f_inner: "∀s∈S. card (?f s) ≤ n"
  proof -
    have "∀s. s ∉ S ∨ card {{c s, a v} | v. v ∈ s} ≤ n"
      by (metis (no_types) Setcompr_eq_image assms card_image_le)
    then show ?thesis
      by blast
  qed
  then have "card (?f ` S) = card S" using card_image inj_on_f by blast
  then have sum_bound: "sum card (?f ` S) ≤ n * card S" using card_f_inner
    by (smt (verit) imageE mult.commute nrest_image_bound)
  then show ?thesis .
qed


lemma X3C_to_steiner_tree_size:
  "size_ST (X3C_to_steiner_tree C) ≤ X3C_to_steiner_tree_space (size_X3C C)"
apply (cases C)
apply (simp add: size_ST_def X3C_to_steiner_tree_def X3C_to_steiner_tree_space_def size_X3C_def)
apply (intro impI conjI)
subgoal for X S
proof -
  assume assms: "∀s∈S. card s = 3"

  have card_insert: "card (insert ROOT (a ` X)) ≤ 1 + card X"
    by (auto simp: card_image[OF inj_on_a[of X]] card_insert_le_m1)

  then have card_insert_un: "card (insert ROOT (a ` X ∪ c ` S)) ≤ 1 + card X + card S"
    using card_insert_le_m1 card_image inj_on_c
    by (smt (verit, ccfv_SIG) Un_insert_left add_le_cancel_right card_Un_le le_trans)

  have "4 * card X div 3 ≤ 1 + 4 * card X" by simp
  then have "nat_encoded_size (4 * card X div 3) ≤ 1 + 4 * card X"
    apply (cases "card X > 0")
    using nat_encoded_size_leq_self[of "4 * card X div 3"]
      apply linarith
    by (simp add: nat_encoded_size_def)

  have "{{ROOT, c s} | s. s ∈ S} = (λs. {ROOT, c s}) ` S" by blast

  have "sum card ((λs. {ROOT, c s}) ` S) ≤ 2 * card S"
  proof (cases "finite S")
    case True
    let ?f = "λs. {ROOT, c s}"
    have "∀ s ∈ S. card {ROOT, c s} = 2" by auto
    moreover have "∀ s ∈ S. finite {ROOT, c s}" by blast
    ultimately have "sum card ((λs. {ROOT, c s}) ` S) ≤ 2 * card S"
      using True card_image inj_on_root
    by (smt (verit, del_insts) imageE mult.commute nrest_image_bound two_elem_card_le)
    then show ?thesis .
  next
    case False
    then have "infinite ((λs. {ROOT, c s}) ` S)"
      using inj_on_root finite_imageD by metis
    then show ?thesis by simp
  qed

  have *: "disjoint_family_on (λs. {(c s, a v) | v. v ∈ s}) S"
    using disjoint_family_on_def mem_Collect_eq by fastforce
  then have disj: "disjoint_family_on (λs. {{c s, a v} | v. v ∈ s}) S"
    using disjoint_family_on_def by blast

  have "card (⋃ ((λs. { {c s, a v} | v. v ∈ s}) ` S)) ≤ sum card ((λs. { {c s, a v} | v. v ∈ s}) ` S)"
    using card_Union_le_sum_card by blast
  also have "... ≤ 3 * card S" using assms sum_card_c_a by blast
  moreover have "∀ s ∈ (⋃ ((λs. { {c s, a v} | v. v ∈ s}) ` S)). card s = 2" by auto
  ultimately have "sum card (⋃ ((λs. { {c s, a v} | v. v ∈ s}) ` S)) ≤ 2 * 3 * card S"
    (* sledgehammer[provers = "z3 zipperposition cvc5 vampire cvc5_proof e spass", isar_proofs = true, timeout = 100] *)

  (* finite ?I ⟹ ∀i∈?I. finite (?A i) ⟹ disjoint_family_on ?A ?I ⟹ sum ?g (⋃ (?A ` ?I)) = (∑x∈?I. sum ?g (?A x)) *)
  proof (cases "finite S")
    case True
    have *: "∀s ∈ S. (λs. { {c s, a v} | v. v ∈ s}) s = (λv. {c s, a v}) ` s" by blast
    have finite_inner: "∀s∈S. finite s" using assms
      by (metis card_ge_0_finite zero_less_numeral)

    have "∀ s ∈ S. inj_on (λv. {c s, a v}) s" unfolding inj_on_def by blast
    then have "∀ s ∈ S. card ((λv. {c s, a v}) ` s) = 3" using card_image assms by fastforce
    then have "∀ s ∈ S. finite ((λv. {c s, a v}) ` s)" using card_ge_0_finite by force
    then have **: "∀ s ∈ S. finite ((λs. { {c s, a v} | v. v ∈ s}) s)" using * by simp
    then have "sum card (⋃ ((λs. { {c s, a v} | v. v ∈ s}) ` S)) = (∑s∈S. sum card ({ {c s, a v} | v. v ∈ s}))"
      using sum.UNION_disjoint_family[OF True ** disj] by blast

    have "∀ s ∈ S. ∀ s' ∈ ({ {c s, a v} | v. v ∈ s}). card s' = 2" by auto
    have "∀ s ∈ S. sum card ({ {c s, a v} | v. v ∈ s}) = 2 * card s"
    sorry
    then have "∀ s ∈ S. sum card ({ {c s, a v} | v. v ∈ s}) = sum (λ_. 2) ({ {c s, a v} | v. v ∈ s})"
    sorry
    then show ?thesis using disj
    (* sledgehammer[provers = "z3 zipperposition cvc5 vampire cvc5_proof e spass", isar_proofs = true, timeout = 100] *)
    sorry
  next
    case False
    then show ?thesis
    sorry
  qed

  have "{{c u, a v} |u v. u ∈ S ∧ v ∈ u} = ⋃ ((λs. { {c s, a v} | v. v ∈ s}) ` S)" by blast

  then have "sum card {{c u, a v} |u v. u ∈ S ∧ v ∈ u} =
  sum card (⋃ ((λs. { {c s, a v} | v. v ∈ s}) ` S))" by argo

  then have "... ≤ sum card ((λs. { {c s, a v} | v. v ∈ s}) ` S)"
  (* sledgehammer *)
  sorry
  (* have "sum card {{c u, a v} |u v. u ∈ S ∧ v ∈ u} ≤ " *)
  (* sorry *)

  have "sum card ({{ROOT, c s} |s. s ∈ S} ∪ {{c u, a v} |u v. u ∈ S ∧ v ∈ u}) ≤
        sum card {{ROOT, c s} | s. s ∈ S} + sum card {{c u, a v} |u v. u ∈ S ∧ v ∈ u}"
    by (metis (no_types, lifting) diff_le_self finite_Un le_add1
                                  le_add_same_cancel1 sum.infinite sum_Un_nat)



  show ?thesis sorry
qed
apply (simp add: NOT_STEINER_TREE_EXAMPLE_def nat_encoded_size_def)
done

lemma X3C_to_steiner_tree_refines:
  "X3C_to_steiner_tree_poly C ≤
    SPEC (λy. y = X3C_to_steiner_tree C) (λ_. enat (X3C_to_steiner_tree_time (size_X3C C)))"
unfolding SPEC_def X3C_to_steiner_tree_poly_def
  X3C_to_steiner_tree_def nrest_image_def mop_set_for_all_def
  mop_set_Union_def mop_set_union_def X3C_to_steiner_tree_time_def
  size_X3C_def
apply(rule T_specifies_I)
apply(vcg' \<open>-\<close> rules: T_SPEC)
apply (simp_all add: zero_enat_def one_enat_def of_nat_eq_enat)
subgoal for X S
proof -
  assume assms: "∀s∈S. card s = 3"
  let ?mapped = "(λu. {{c u, a v} | v. v ∈ u}) ` S"

  have card_insert: "card (insert ROOT (a ` X)) ≤ 1 + card X"
    by (auto simp: card_image[OF inj_on_a[of X]] card_insert_le_m1)
  have finite_inner: "∀s∈S. finite s" using assms
    by (metis card_ge_0_finite zero_less_numeral)
  then have sum_bound: "sum card ?mapped ≤ 3 * card S" using assms sum_card_c_a
    by blast

  have "card (⋃u∈S. {{c u, a v} | v. v ∈ u}) = card (⋃ ?mapped)" by blast
  then have "... ≤ sum card ?mapped"
    using card_Union_le_sum_card by blast

  then show ?thesis
  apply (intro conjI, fast)
  apply (simp add: card_image inj_on_a inj_on_c inj_on_root)
  using sum_bound card_insert by linarith
qed
apply fast
done

theorem X3C_to_steiner_tree_ispolyred:
  "ispolyred X3C_to_steiner_tree_poly three_exact_cover steiner_tree size_X3C size_ST"
unfolding ispolyred_def
apply(rule exI[where x=X3C_to_steiner_tree])
apply(rule exI[where x=X3C_to_steiner_tree_time])
apply(rule exI[where x=X3C_to_steiner_tree_space])
apply safe
  subgoal using X3C_to_steiner_tree_refines by blast
  subgoal using X3C_to_steiner_tree_size by blast
  subgoal unfolding X3C_to_steiner_tree_time_def
    by (auto simp: poly_add poly_mult poly_linear)
  subgoal unfolding X3C_to_steiner_tree_space_def sorry
  subgoal using is_reduction_X3C_to_steiner_tree .
done

end
