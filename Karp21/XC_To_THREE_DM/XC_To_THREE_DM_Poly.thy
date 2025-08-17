theory XC_To_THREE_DM_Poly
  imports Main
    XC_To_THREE_DM
    Poly_Library
    Polynomial_Reductions
begin

definition "mop_set_discriminated_Union S \<equiv> REST [ \<Uplus> S \<mapsto> sum card S + card S ]"

(* Computable by constructing cross product of X and T and filtering out collisions/duplicates
  i.e. O(|X| * |T|)*)
definition "mop_choice_alpha X T \<equiv> REST [ (SOME f. inj_on f X \<and> f ` X \<subseteq> T) \<mapsto> card X * card T ]"

definition "xc_to_three_dm_poly \<equiv> \<lambda>(X, S). do {
  S_un \<leftarrow> mop_set_Union S;
  b \<leftarrow> mop_set_eq S_un X;
  b' \<leftarrow> mop_set_finite X;
  if b \<and> b' then do {
    T \<leftarrow> mop_set_discriminated_Union S;
    \<alpha> \<leftarrow> mop_choice_alpha X T;

    U1' \<leftarrow> nrest_image (\<lambda>s. { (\<alpha> x, (x, s), (x, s)) | x. x \<in> s}) (\<lambda>s. card s) S;
    U1 \<leftarrow> mop_set_Union U1';

    mapped \<leftarrow> nrest_image \<alpha> (\<lambda>_. 1) X;
    diff \<leftarrow> mop_set_diff T mapped;

    nxt_set \<leftarrow> nrest_image (\<lambda>s. { ((x, s), nxt (x, s)) | x. x \<in> s}) (\<lambda>s. card s) S;
    U2' \<leftarrow> mop_set_Union nxt_set;
    U2 \<leftarrow> mop_set_times diff U2';

    U \<leftarrow> mop_set_union U1 U2;

    RETURNT (U, T)
  } else RETURNT MALFORMED
}"

definition "size_XC \<equiv> \<lambda>(X, S). card X + sum card S + card S"

(* TODO *)
definition "size_DM \<equiv> \<lambda>(U, T). 0"

definition "xc_to_three_dm_time n \<equiv> 1 + 8 * n + 6 * n * n"

(* TODO *)
definition "xc_to_three_dm_space n \<equiv> 0"
lemma xc_to_three_dm_size:
  "space_DM (xc_to_three_dm P) \<le> xc_to_three_dm_space (size_XC P)"
  sorry

lemma xc_to_three_dm_refines:
  "xc_to_three_dm_poly P \<le> SPEC (\<lambda>y. y = xc_to_three_dm P) (\<lambda>_. xc_to_three_dm_time (size_XC P))"
  unfolding SPEC_def xc_to_three_dm_poly_def xc_to_three_dm_def xc_to_three_dm_time_def size_XC_def
  unfolding mop_set_Union_def mop_set_eq_def mop_set_discriminated_Union_def mop_choice_alpha_def
            nrest_image_def mop_set_diff_def mop_set_times_def mop_set_union_def mop_set_finite_def
apply (rule T_specifies_I)
apply(vcg' \<open>-\<close> rules: T_SPEC)
subgoal for X S
apply (simp add: zero_enat_def one_enat_def)
apply (rule conjI)
subgoal proof -
  assume "\<Union> S = X \<and> finite X"
  let ?T = "\<Uplus> S"
  define \<alpha> where "\<alpha> = (SOME f.  inj_on f X \<and> f ` X \<subseteq> ?T)"
  let ?U1 = "{(\<alpha> x, (x, s), x, s) |s x. s \<in> S \<and> x \<in> s}"
  let ?U1' = "(\<Union>s\<in>S. {(\<alpha> x, (x, s), x, s) | x. x \<in> s})"
  let ?U2 = "\<Union> {{((a, b), (x, s), nxt (x, s)) |s x. s \<in> S \<and> x \<in> s} | a b. (a, b) \<notin> \<alpha> ` X \<and> b \<in> S \<and> a \<in> b}"
  let ?U2' = "(?T - (\<alpha> ` X)) \<times> (\<Union>s\<in>S. {((x, s), nxt (x, s)) |x. x \<in> s})"

  have "?U1 \<union> ?U2 = ?U1' \<union> ?U2" by blast
  also have "... = ?U1' \<union> ?U2'" by blast
  finally have "(?U1' \<union> ?U2', ?T) = (?U1 \<union> ?U2, ?T)" by force
  then show ?thesis unfolding \<alpha>_def by meson
qed
subgoal proof -
  assume assm: "\<Union> S = X \<and> finite X"
  let ?T = "\<Uplus> S"
  define \<alpha> where "\<alpha> = (SOME f.  inj_on f X \<and> f ` X \<subseteq> ?T)"
  let ?nxt = "(\<lambda>s. {((x, s), nxt (x, s)) |x. x \<in> s})"
  let ?alpha = "(\<lambda>s. {(\<alpha> x, (x, s), x, s) |x. x \<in> s})"

  let ?card_x = "card X"
  let ?card_t = "card ?T"

  from assm have "finite (\<Union> S)" by blast
  then have finite_t: "finite ?T" using finite_discriminated_Union by fast

  have card_bound: "?card_t \<le> sum card S"
  proof (cases "\<forall>s\<in>S. finite s")
    case False
    then have "infinite (\<Uplus> S)"
      by (metis (mono_tags, lifting) Sup_upper finite_Union_if_finite_discriminated_Union rev_finite_subset)
    then show ?thesis by simp
  qed (simp add: card_discriminated_Union)

  from finite_t have card_diff: "card (?T - \<alpha> ` X) \<le> sum card S"
    using card_mono[OF finite_t Diff_subset[of "?T" "\<alpha> ` X"]] card_bound by linarith

  have inj_on_nxt: "inj_on ?nxt S" unfolding inj_on_def by fastforce
  have card_nxt_inner: "\<forall>s\<in>S. card (?nxt s) = card s"
  proof
    fix s
    assume "s \<in> S"
    have "inj_on (\<lambda>x. ((x, s), nxt (x, s))) s" unfolding inj_on_def by blast
    then have card: "card ((\<lambda>x. ((x, s), nxt (x, s))) ` s) = card s" using card_image by blast
    have "?nxt s = {((x, s), nxt (x, s)) | x. x \<in> s}" by meson
    moreover have "... = (\<lambda>x. ((x, s), nxt (x, s))) ` s" by blast
    ultimately show "card (?nxt s) = card s" using card by argo
  qed

  have inj_on_alpha: "inj_on ?alpha S" unfolding inj_on_def by fastforce
  have card_alpha_inner: "\<forall>s\<in>S. card (?alpha s) = card s"
  proof
    fix s
    assume "s \<in> S"
    have "inj_on (\<lambda>x. (\<alpha> x, (x, s), x, s)) s" unfolding inj_on_def by blast
    then have card: "card ((\<lambda>x. (\<alpha> x, (x, s), x, s)) ` s) = card s" using card_image by blast
    have "?alpha s = {(\<alpha> x, (x, s), x, s) |x. x \<in> s}" by meson
    moreover have "... = (\<lambda>x. (\<alpha> x, (x, s), x, s)) ` s" by blast
    ultimately show "card (?alpha s) = card s" using card by argo
  qed

  have a: "card (?alpha ` S) = card S" using card_image[OF inj_on_alpha] by fast
  have "sum card (?alpha ` S) = sum (\<lambda>s. card (?alpha s)) S" using sum.reindex[OF inj_on_alpha]
    by auto
  then have alpha: "sum card (?alpha ` S) = sum card S" using  card_alpha_inner by auto

  have n: "card (?nxt ` S) = card S" using card_image[OF inj_on_nxt] by fast
  have "sum card (?nxt ` S) = sum (\<lambda>s. card (?nxt s)) S" using sum.reindex[OF inj_on_nxt] by auto
  then have nxt: "sum card (?nxt ` S) = sum card S" using card_nxt_inner by auto

  have "?card_x * ?card_t + sum card (?alpha ` S) + card (?alpha ` S) + ?card_t +
        sum card (?nxt ` S) + card (?nxt ` S) +
        card (?T - \<alpha> ` X) * card (\<Union>s\<in>S. {((x, s), nxt (x, s)) |x. x \<in> s}) +
        card (\<Union>s\<in>S. {(\<alpha> x, (x, s), x, s) |x. x \<in> s}) +
        card ((?T - \<alpha> ` X) \<times> (\<Union>s\<in>S. {((x, s), nxt (x, s)) |x. x \<in> s})) \<le>
        ?card_x * (sum card S) + (sum card S) + card S + (sum card S) + (sum card S) + card S +
        card (?T - \<alpha> ` X) * sum card S + sum card S +
        card ((?T - \<alpha> ` X) \<times> (\<Union>s\<in>S. {((x, s), nxt (x, s)) |x. x \<in> s}))"
    using nxt alpha card_Union_le_sum_card alpha nxt a n
    by (smt (z3) card_bound add_le_mono add_mono_thms_linordered_semiring(3) mult_le_mono2)

  also have "... \<le>
      ?card_x * sum card S + sum card S + card S + sum card S + sum card S + card S +
      sum card S * sum card S + sum card S +
      card ((?T - \<alpha> ` X) \<times> (\<Union>s\<in>S. {((x, s), nxt (x, s)) |x. x \<in> s}))"
    using card_bound card_diff by simp
  also have "... \<le>
      ?card_x * sum card S + 4 * sum card S + 2 * card S + sum card S * sum card S +
      card (?T - \<alpha> ` X) * card (\<Union>s\<in>S. {((x, s), nxt (x, s)) |x. x \<in> s})"
    using card_cartesian_product[of "(?T - \<alpha> ` X)" "(\<Union>s\<in>S. {((x, s), nxt (x, s)) |x. x \<in> s})"]
    by linarith
  also have "... \<le>
      ?card_x * sum card S + 4 * sum card S + 2 * card S + sum card S * sum card S +
      sum card S * sum card S" using card_diff nxt card_Union_le_sum_card
    by (metis (lifting) add_le_cancel_left mult_le_mono)
  also have "... =
      4 * sum card S + 2 * card S + 2 * sum card S * sum card S + ?card_x * sum card S" by algebra
  also have "... \<le>
      4 * sum card S + 2 * card S + 2 * (sum card S * sum card S + 2 * ?card_x * sum card S + ?card_x * ?card_x)"
      by simp
  also have "... =
      4 * sum card S + 2 * card S + 2 * (?card_x + sum card S) * (?card_x + sum card S)" by algebra
  also have "... \<le>
      4 * sum card S + 2 * card S + 2 * (?card_x + sum card S + card S) * (?card_x + sum card S + card S)"
      by (simp add: mult_le_mono)
  also have "... \<le>
      4 * sum card S + 6 * card X + 6 * card S +
      6 * (?card_x + sum card S + card S) * (?card_x + sum card S + card S)" by linarith
  also have "... =
      4 * sum card S + 6 * card X + 6 * card S +
      (6 * ?card_x + 6 * sum card S + 6 * card S) * (?card_x + sum card S + card S)" by simp
  finally show ?thesis unfolding \<alpha>_def by presburger
qed done
by (auto simp: one_enat_def)

theorem xc_to_three_dm_ispolyred:
  "ispolyred xc_to_three_dm_poly exact_cover three_dm size_XC size_DM"
  unfolding ispolyred_def
  apply(rule exI[where x=xc_to_three_dm])
  apply(rule exI[where x=xc_to_three_dm_time])
  apply(rule exI[where x=xc_to_three_dm_space])
  apply safe
    subgoal using xc_to_three_dm_refines .
    subgoal using xc_to_three_dm_size sorry
    subgoal unfolding xc_to_three_dm_time_def
      by (intro poly_add) (auto simp: poly_linear poly_mult)
    subgoal sorry
    subgoal using is_reduction_xc_to_three_dm .
  done

end
