theory X3C_To_ST_Poly
  imports
    Polynomial_Reductions
    Poly_Library
    X3C_To_ST
begin

definition "X3C_to_steiner_tree_poly \<equiv> \<lambda>((X :: 'a set), S). do {
  b \<leftarrow> mop_set_for_all S (\<lambda>s. card s = 3) (\<lambda>_. 1);
  if b then do {
    as \<leftarrow> nrest_image a (\<lambda>_. 1) X;
    cs \<leftarrow> nrest_image c (\<lambda>_. 1) S;

    v \<leftarrow> mop_set_union as {ROOT};
    all_v \<leftarrow> mop_set_union v cs;

    pairs \<leftarrow> nrest_image (\<lambda>s. {ROOT, c s}) (\<lambda>_. 1) S;
    tmp \<leftarrow> nrest_image (\<lambda>u. {{c u, a v} | v. v \<in> u}) (\<lambda>u. card u) S;
    pairs' \<leftarrow> mop_set_Union tmp;

    all_pairs \<leftarrow> mop_set_union pairs pairs';

    union \<leftarrow> mop_set_union {ROOT} as;

    RETURNT (
      all_v,
      all_pairs,
      (\<lambda>e. 1),
      union,
      4 * card X div 3
    )
  } else RETURNT NOT_STEINER_TREE_EXAMPLE
}"

definition "size_X3C \<equiv> \<lambda>(X, S). card X + card S + sum card S"
definition "size_ST \<equiv> \<lambda>(V, E, _, S, K). card V + sum card E + card S + nat_encoded_size K"

definition "X3C_to_steiner_tree_space n \<equiv> 3 + 6 * n"
definition "X3C_to_steiner_tree_time n \<equiv> 3 + 8 * n + 2 * n * n"

lemma inj_on_a: "inj_on a S"
by (meson inj_onI red_vertex.inject(1))

lemma inj_on_c: "inj_on c S"
by (meson inj_onI red_vertex.inject(2))

lemma inj_on_root: "inj_on (\<lambda>s. {ROOT, c s}) S"
  unfolding inj_on_def by blast

lemma inj_on_f: "inj_on (\<lambda>u. {{c u, a v} | v. v \<in> u}) S"
proof -
  let ?f = "(\<lambda>u. {{c u, a v} | v. v \<in> u})"
  have "inj ?f" unfolding inj_def
    by (smt (z3) doubleton_eq_iff mem_Collect_eq red_vertex.inject(2)
                 red_vertex.simps(6) set_eq_iff)
  then show ?thesis
    by (metis (mono_tags, lifting) inj_def inj_onI)
qed

lemma sum_card_c_a:
  assumes "\<And>s. s\<in>S \<Longrightarrow> card s = n"
  and "0 < n"
  shows "sum card ((\<lambda>u. {{c u, a v} | v. v \<in> u}) ` S) \<le> n * card S"
proof -
  let ?f = "(\<lambda>u. {{c u, a v} | v. v \<in> u})"
  have card_f_inner: "card (?f s) \<le> n" if prems: "s\<in>S" for s
    using assms prems unfolding Setcompr_eq_image
    by (auto intro!: card_image_le card_ge_0_finite)
  then have "card (?f ` S) = card S" using card_image inj_on_f by blast
  then have sum_bound: "sum card (?f ` S) \<le> n * card S" using card_f_inner
    by (smt (verit) imageE mult.commute nrest_image_bound)
  then show ?thesis .
qed


(* TODO: *)
lemma X3C_to_steiner_tree_size:
  "size_ST (X3C_to_steiner_tree C) \<le> X3C_to_steiner_tree_space (size_X3C C)"
apply (cases C)
apply (simp add: size_ST_def X3C_to_steiner_tree_def X3C_to_steiner_tree_space_def size_X3C_def)
apply (intro impI conjI)
subgoal for X S
proof -
  assume assms: "\<forall>s\<in>S. card s = 3"

  have card_insert: "card (insert ROOT (a ` X)) \<le> 1 + card X"
    by (auto simp: card_image[OF inj_on_a[of X]] card_insert_le_m1)

  then have card_insert_un: "card (insert ROOT (a ` X \<union> c ` S)) \<le> 1 + card X + card S"
    using card_insert_le_m1 card_image inj_on_c
    by (smt (verit, ccfv_SIG) Un_insert_left add_le_cancel_right card_Un_le le_trans)

  have "4 * card X div 3 \<le> 1 + 4 * card X" by simp
  then have "nat_encoded_size (4 * card X div 3) \<le> 1 + 4 * card X"
    apply (cases "card X > 0")
    using nat_encoded_size_leq_self[of "4 * card X div 3"]
      apply linarith
    by (simp add: nat_encoded_size_def)

  have "{{ROOT, c s} | s. s \<in> S} = (\<lambda>s. {ROOT, c s}) ` S" by blast

  have "sum card ((\<lambda>s. {ROOT, c s}) ` S) \<le> 2 * card S"
  proof (cases "finite S")
    case True
    let ?f = "\<lambda>s. {ROOT, c s}"
    have "\<forall> s \<in> S. card {ROOT, c s} = 2" by auto
    moreover have "\<forall> s \<in> S. finite {ROOT, c s}" by blast
    ultimately have "sum card ((\<lambda>s. {ROOT, c s}) ` S) \<le> 2 * card S"
      using True card_image inj_on_root
    by (smt (verit, del_insts) imageE mult.commute nrest_image_bound two_elem_card_le)
    then show ?thesis .
  next
    case False
    then have "infinite ((\<lambda>s. {ROOT, c s}) ` S)"
      using inj_on_root finite_imageD by metis
    then show ?thesis by simp
  qed

  have *: "disjoint_family_on (\<lambda>s. {(c s, a v) | v. v \<in> s}) S"
    using disjoint_family_on_def mem_Collect_eq by fastforce
  then have disj: "disjoint_family_on (\<lambda>s. {{c s, a v} | v. v \<in> s}) S"
    using disjoint_family_on_def by blast

  have "card (\<Union> ((\<lambda>s. { {c s, a v} | v. v \<in> s}) ` S)) \<le> sum card ((\<lambda>s. { {c s, a v} | v. v \<in> s}) ` S)"
    using card_Union_le_sum_card by blast
  also have "... \<le> 3 * card S" using assms sum_card_c_a by fastforce
  moreover have "\<forall> s \<in> (\<Union> ((\<lambda>s. { {c s, a v} | v. v \<in> s}) ` S)). card s = 2" by auto
  ultimately have "sum card (\<Union> ((\<lambda>s. { {c s, a v} | v. v \<in> s}) ` S)) \<le> 2 * 3 * card S" sorry

  have "{{c u, a v} |u v. u \<in> S \<and> v \<in> u} = \<Union> ((\<lambda>s. { {c s, a v} | v. v \<in> s}) ` S)" by blast

  then have "sum card {{c u, a v} |u v. u \<in> S \<and> v \<in> u} =
    sum card (\<Union> ((\<lambda>s. { {c s, a v} | v. v \<in> s}) ` S))" by argo
  have "sum card ({{ROOT, c s} |s. s \<in> S} \<union> {{c u, a v} |u v. u \<in> S \<and> v \<in> u}) \<le>
        sum card {{ROOT, c s} | s. s \<in> S} + sum card {{c u, a v} |u v. u \<in> S \<and> v \<in> u}"
    by (metis (no_types, lifting) diff_le_self finite_Un le_add1
                                  le_add_same_cancel1 sum.infinite sum_Un_nat)
  show ?thesis sorry
qed
apply (simp add: NOT_STEINER_TREE_EXAMPLE_def nat_encoded_size_def)
done

lemma X3C_to_steiner_tree_refines:
  "X3C_to_steiner_tree_poly C \<le>
    SPEC (\<lambda>y. y = X3C_to_steiner_tree C) (\<lambda>_. enat (X3C_to_steiner_tree_time (size_X3C C)))"
unfolding SPEC_def X3C_to_steiner_tree_poly_def
  X3C_to_steiner_tree_def nrest_image_def mop_set_for_all_def
  mop_set_Union_def mop_set_union_def X3C_to_steiner_tree_time_def
  size_X3C_def
apply(rule T_specifies_I)
apply(vcg' \<open>-\<close> rules: T_SPEC)
apply (simp_all add: zero_enat_def one_enat_def of_nat_eq_enat)
subgoal for X S
proof -
  assume assms: "\<forall>s\<in>S. card s = 3"
  let ?mapped = "(\<lambda>u. {{c u, a v} | v. v \<in> u}) ` S"

  have card_insert: "card (insert ROOT (a ` X)) \<le> 1 + card X"
    by (auto simp: card_image[OF inj_on_a[of X]] card_insert_le_m1)
  have finite_inner: "\<forall>s\<in>S. finite s" using assms
    by (metis card_ge_0_finite zero_less_numeral)
  then have sum_bound: "sum card ?mapped \<le> 3 * card S" using assms sum_card_c_a
    by fastforce

  have "card (\<Union>u\<in>S. {{c u, a v} | v. v \<in> u}) = card (\<Union> ?mapped)" by blast
  then have *: "... \<le> sum card ?mapped"
    using card_Union_le_sum_card by blast
  have **: "card ((\<lambda>u. {{c u, a v} |v. v \<in> u}) ` S) = card S" using card_image[OF inj_on_f] by blast

  then show ?thesis
  apply (intro conjI, fast)
  apply (simp add: card_image inj_on_a inj_on_c inj_on_root)
  using sum_bound card_insert * ** by linarith
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
  subgoal unfolding X3C_to_steiner_tree_time_def by (auto simp: poly_add poly_mult poly_linear)
  subgoal unfolding X3C_to_steiner_tree_space_def sorry
  subgoal using is_reduction_X3C_to_steiner_tree .
done

end
