theory XC_To_SS
  imports
    DigitsInBase.DigitsInBase
    Subset_Sum_Definitions
    XC_Definition
begin

subsection "definition of reduction functions"

definition "map_to_nat X \<equiv> (SOME f. (if X = {} then bij_betw f X {} else bij_betw f X {1..card X}))"
definition "weight p X \<equiv> (sum (\<lambda>x. p ^ x)  X)"


lemma map_to_nat_unfold:
assumes "finite X"
shows  "(map_to_nat X) ` X = (if X = {} then {} else {1..card X}) \<and> inj_on (map_to_nat X) X"
proof -
  have "(if X = {} then bij_betw (map_to_nat X) X {} else bij_betw (map_to_nat X) X {1..card X})"
    unfolding map_to_nat_def
    apply (rule someI_ex[of "\<lambda>f. (if X = {} then bij_betw f X {} else bij_betw f X {1..card X})"])
    using bij_exist[OF assms] .
  thus ?thesis
    unfolding bij_betw_def
    by presburger
qed

lemma weight_eq_poly:
fixes X:: "nat set" and p::nat
assumes "p \<ge> 2"
shows  "weight p X = \<Sum>{p ^ x | x . x \<in> X}"
  proof -
    from assms have "inj_on (\<lambda>x. p ^ x) X"
      proof (induction p)
        case (Suc p)
        then show ?case
        proof (cases "p = 1")
          case True
          then show ?thesis
            unfolding inj_on_def
            by simp
        next
          case False
          with Suc have prem: "\<forall>x\<in>X. \<forall>y\<in>X. p ^ x = p ^ y \<longrightarrow> x = y"
            unfolding inj_on_def
            by linarith
         have "\<forall>x\<in>X. \<forall>y\<in>X. Suc p ^ x = Suc p ^ y \<longrightarrow> x = y"
            proof auto
              fix x y
              assume "x \<in> X" "y \<in> X" "Suc p ^ x = Suc p ^ y"
              with prem have "p ^ x = p ^ y \<longrightarrow> x = y" "p ^ x = p ^ y"
                using Suc(2)
                by fastforce+
              then show "x = y"
                by blast
            qed
          then show ?thesis
            unfolding inj_on_def .
        qed
      qed auto

    moreover have "{p ^ x | x . x \<in> X} = ((\<lambda>x. p ^ x) ` X)"
      by blast
    ultimately show ?thesis
      unfolding weight_def
      using sum.image_eq[of "(\<lambda>x. p ^ x)" "X"]
      by presburger
  qed



definition
"xc_to_ss XC \<equiv>
  (case XC of (X, S) \<Rightarrow>
    (if infinite X \<or> (\<not> \<Union>S \<subseteq> X) then ({}, card, 1::nat)
    else
      (let f = map_to_nat X;
           p = max 2 (card S + 1)
        in
      (S,
      (\<lambda>A.  (weight p (f ` A))),
       (weight p (f ` X)))
      )
    )
  )"

subsection "the proof of the soundness"

lemma infinite_not_in_ss:
  "\<not> is_subset_sum ({}, card , 1::nat)"
unfolding is_subset_sum_def
by force

lemma xc_to_subset_sum_sound_aux:
assumes "cover S X" "finite X" "xc_to_ss (X, S0) = (S', w, B)" "S \<subseteq> S'" "\<Union>S0 \<subseteq> X"
shows "is_subset_sum (S, w, B)"
proof -
  let ?f = "(map_to_nat X)"
  let ?p = "max 2 (card S0 + 1)"
  from assms have prems: "disjoint S" "\<Union>S = X"
    unfolding cover_def
    by blast+

  from assms have "finite (\<Union>S)"
    using prems
    by blast
  hence *:"finite S"
    using finite_UnionD
    by blast

  have "\<forall>i \<in> S. finite i"
    using \<open>finite (\<Union>S)\<close>
    by (metis Sup_upper finite_subset)
  hence **:"\<forall>i\<in>S. finite (?f ` i)"
    by blast

  have "inj_on ?f X"
    using map_to_nat_unfold[OF assms(2)]
    by blast
  with prems have "disjoint ((`) ?f ` S)"
    by (simp add: disjoint_image)
  hence ***:"\<forall>i\<in>S. \<forall>j\<in>S. i \<noteq> j \<longrightarrow> map_to_nat X ` i \<inter> map_to_nat X ` j = {}"
    unfolding disjoint_def
    by (metis Sup_upper \<open>inj_on (map_to_nat X) X\<close> disjointD image_empty
    inj_on_image_Int prems(1) prems(2))

  from * ** *** have
  "(\<Sum>x\<in>\<Union> ((`) ?f ` S). ?p ^ x) = (\<Sum>x\<in>S. \<Sum>x\<in>?f ` x. ?p ^ x)"
    using sum.UNION_disjoint[of S "(`) ?f" "(\<lambda>x. ?p ^ x)"]
    by blast
  moreover have "\<Union> ((`) ?f ` S) = ?f ` X"
    using prems
    by blast
  ultimately have "(\<Sum>x\<in>S. \<Sum>x\<in>?f` x. ?p ^ x) = (\<Sum>x\<in>?f ` X. ?p ^ x)"
    by argo
  hence "(\<Sum>x\<in>S.  (\<Sum>x\<in>?f` x. ?p ^ x)) = (\<Sum>x\<in>?f ` X.  (?p ^ x))"
    by (metis of_nat_sum)
  with assms * prems have "sum w S = B"
    unfolding xc_to_ss_def Let_def weight_def
    by auto

  then show ?thesis
    unfolding is_subset_sum_def
    by force
qed

subsubsection "the proof of the completeness"


lemma distr_aux:
fixes a::nat
assumes "a \<le> b"
shows "a * c + (b - a) * c = b * c"
using assms
by (metis add_mult_distrib le_add_diff_inverse)

lemma   sum_distr:
fixes X :: "'a set" and f :: "'a \<Rightarrow> nat"
assumes "finite S" "finite X" "\<Union>S \<subseteq> X"
shows "(\<Sum>i\<in>S. sum f i) = (\<Sum>i \<in> X. (card {A \<in> S. i \<in> A}) * f i)"
using assms proof (induction S)
  case (insert x F)
  hence "x \<subseteq> X"
    by blast
  from sum.subset_diff[OF this insert(4)] have "(\<Sum>i\<in>X. (if i \<in> x then 1 else 0) * f i)
    = (\<Sum>i\<in>X - x. (if i \<in> x then 1 else 0) * f i) + (\<Sum>i\<in>x. (if i \<in> x then 1 else 0) * f i)"
    by blast
  also have "... = (\<Sum>i\<in>x. (if i \<in> x then 1 else 0) * f i)"
    by simp
  also have "... = sum f x"
    by simp
  finally have *: "sum f x = (\<Sum>i\<in>X. (if i \<in> x then 1 else 0) * f i)"
    by presburger

  have "({A \<in> insert x F. i \<in> A} - {A \<in> F. i \<in> A}) = (if i \<in> x then {x} else {})" for i
    using insert
    by auto
  hence "card ({A \<in> insert x F. i \<in> A} - {A \<in> F. i \<in> A}) = (if i \<in> x then 1 else 0)" for i
    by simp
  moreover have "finite {A \<in> F. i \<in> A}" for i
    using insert
    by fastforce
  moreover have "{A \<in> F. i \<in> A} \<subseteq> {A \<in> insert x F. i \<in> A}" for i
    by blast
  ultimately have "card {A \<in> insert x F. i \<in> A} - card {A \<in> F. i \<in> A} = (if i \<in> x then 1 else 0)" for i
    using card_Diff_subset[of "{A \<in> F. i \<in> A}" "{A \<in> insert x F. i \<in> A}"]
    by algebra
  with * have sum_distr: "sum f x = (\<Sum>i\<in>X. (card {A \<in> insert x F. i \<in> A} - card {A \<in> F. i \<in> A}) * f i)"
    by presburger

  have "\<forall>i \<in> X. {A \<in> F. i \<in> A} \<le> {A \<in> insert x F. i \<in> A}"
    by blast
  moreover with insert have "\<forall>i \<in> X. finite {A \<in> insert x F. i \<in> A}"
    by fastforce
  ultimately have "\<forall>i \<in> X. card {A \<in> F. i \<in> A} \<le> card {A \<in> insert x F. i \<in> A}"
    using card_mono
    by meson
  then have "(\<Sum>i\<in>X. card {A \<in> insert x F. i \<in> A} * f i) =
      (\<Sum>i\<in>X. card {A \<in> F. i \<in> A} * f i)
    + (\<Sum>i\<in>X. (card {A \<in> insert x F. i \<in> A} - card {A \<in> F. i \<in> A}) * f i)"
      using sum.distrib[of "(\<lambda>i. card {A \<in> F. i \<in> A} * f i)"
             "(\<lambda>i. (card {A \<in> insert x F. i \<in> A} - card {A \<in> F. i \<in> A}) * f i)" X]
      distr_aux
      by force
  also have "... = (\<Sum>i\<in>X. card {A \<in> F. i \<in> A} * f i) + sum f x"
    using sum_distr
    by argo
  also have "... = sum (sum f) F + sum f x"
    using insert
    by auto
  also have "... = sum (sum f) (insert x F)"
    using insert
    by auto
  finally show ?case
    by argo
qed auto

lemma ss_leads_disjoint:
assumes "xc_to_ss (X, S0) = (S', w, B)" "S \<subseteq> S'" "is_subset_sum (S, w, B)"
  "finite S" "finite X" "\<Union>S0 \<subseteq> X"
shows "disjoint S"
proof -
  let ?f = "(map_to_nat X)"
  let ?p = "max 2 (card S0 + 1)"
  let ?m = "weight ?p (?f ` X)"
  let ?D = "\<lambda>x. if x \<in> ?f ` X then card {A. A \<in> S \<and> x \<in> ?f ` A} else 0"
      let ?E = "(\<lambda>x. if x \<in> ?f ` X then 1 else 0)"
  from assms have S_prop:
  "finite S" "(\<Sum>A\<in>S.  (weight ?p (?f ` A))) =  (weight ?p (?f ` X))" "\<Union>S \<subseteq> X" "S' = S0"
    unfolding xc_to_ss_def is_subset_sum_def Let_def
    using finite_subset
    by auto

  have "finite S0"
    using assms(5-6)
    by (simp add: finite_UnionD finite_subset)
  moreover from \<open>S' = S0\<close> assms(2) this have S_card: "card S \<le> card S0"
    using card_mono
    by blast

  have base: "digits_in_base ?p" "?p \<ge> 2"
    unfolding digits_in_base_def
    by auto
  have f_dom: "?f ` X = (if X = {} then {} else {1..card X})" "inj_on ?f X" "finite X"
    using map_to_nat_unfold assms
    by blast+
  from assms have "finite (?f ` X)"
    by blast
  moreover have "(\<And>n. n \<notin> (?f ` X) \<Longrightarrow> ?E n * ?p ^ n = 0)"
    by simp
  ultimately have "(\<Sum>i. ?E i * ?p ^ i) = (\<Sum>i \<in> (?f ` X). ?E i * ?p ^ i)"
    using suminf_finite
    by meson
  also have "?m = (\<Sum>i \<in> (?f ` X). ?E i * ?p ^ i)"
    unfolding weight_def
    by fastforce
  finally have sum_of_poly_E: "?m = (\<Sum>i. ?E i * ?p ^ i)"
    by simp

  have "bij_betw (map_to_nat X) A (map_to_nat X ` A)" if "A \<in> S" for A
    proof (simp add: bij_betw_def)
      from \<open>A \<in> S\<close> S_prop(3) have "A \<subseteq> X"
        by blast
      with f_dom(2) show "inj_on (map_to_nat X) A"
        unfolding inj_on_def
        by blast
    qed
  hence **: "\<forall>A \<in> S. sum (\<lambda>i. ?p ^ i) (?f ` A) = (sum (\<lambda>x. ?p ^ ?f x)) A"
    using sum.reindex_bij_betw[of ?f _ _ "\<lambda>x. ?p ^ x", symmetric] bij_betwE
    by blast
  from f_dom have ***: "bij_betw ?f X (?f` X)"
    using bij_betw_def
    by blast
  have "\<forall>A\<in>S. A \<subseteq> X"
    using S_prop(3)
    by blast
  hence ****:"\<forall>i \<in> X. {A \<in> S. i \<in> A} = {A \<in> S. ?f i \<in> ?f ` A}"
   using f_dom(2)
   unfolding inj_on_def
   by auto

  from assms have "?m = (\<Sum>i\<in>S.  (weight ?p (?f ` i)))"
    unfolding is_subset_sum_def xc_to_ss_def Let_def
    by auto
  also have "... =  (\<Sum>A\<in>S. sum (\<lambda>i. ?p ^ i) (?f ` A))"
    unfolding weight_def
    by simp
  also have "... =  (\<Sum>A\<in>S. (sum (\<lambda>i. ?p ^ ?f i)) A)"
    using **
    by simp
  also have "... =  (\<Sum>i\<in>X. card {A \<in> S. i \<in> A} * ?p ^ (?f i))"
    using sum_distr[OF S_prop(1) f_dom(3) S_prop(3), of "\<lambda>i. ?p ^ (?f i)"]
    by argo
  also have "... =  (\<Sum>x\<in>X. card {A \<in> S. ?f x \<in> ?f ` A} * ?p ^ ?f x)"
    using ****
    by simp
  also have "... =  (\<Sum>i\<in>?f ` X. card {A \<in> S. i \<in> ?f ` A} * ?p ^ i)"
    using sum.reindex_bij_betw[OF ***,of "\<lambda>i. card {A \<in> S. i \<in> ?f ` A} * ?p ^ i"]
    by argo
  also have "... =  (\<Sum>i \<in> (?f ` X). ?D i * ?p ^ i)"
    by simp
  finally have *: "?m =  (\<Sum>i \<in> (?f ` X). ?D i * ?p ^ i)"
    by simp

  from assms have "finite (?f ` X)"
    by blast
  moreover have "(\<And>n. n \<notin> (?f ` X) \<Longrightarrow> ?D n * ?p ^ n = 0)"
    by simp
  ultimately have "(\<Sum>i. ?D i * ?p ^ i) = (\<Sum>i \<in> (?f ` X). ?D i * ?p ^ i)"
    using suminf_finite
    by meson
  with * have sum_of_poly_D: "?m =  (\<Sum>i. ?D i * ?p ^ i)"
    by presburger
  show ?thesis
    proof (rule ccontr)
      assume "\<not> disjoint S"
      then obtain A B b where b_def: "A \<in> S" "B \<in> S" "b \<in> A" "b \<in> B" "A \<noteq> B"
        unfolding disjoint_def
        by blast
      hence "A \<in> {A \<in> S. b \<in> A}" "B \<in> {A \<in> S. b \<in> A}" "finite {A \<in> S. b \<in> A}"
        using S_prop(1)
        by auto
      with b_def(5) have card_ge_2: "2 \<le> card {A \<in> S. b \<in> A}"
        using card_le_Suc0_iff_eq
        by fastforce
      have *****:"b \<in> X"
        using b_def S_prop(3)
        by blast
      then have "{A \<in> S. b \<in> A} = {A \<in> S. ?f b \<in> ?f ` A}"
        using ****
        by blast
      with card_ge_2 have "card {A \<in> S. ?f b \<in> ?f ` A} \<ge> 2"
        by argo
      moreover from ***** have "?f b \<in> ?f ` X"
        by blast
      ultimately have D_ge_2: "?D (?f b) \<ge> 2"
        by presburger

      have "eventually_zero ?E"
        proof (unfold eventually_zero_char, standard)
          show "\<forall>i\<ge>card X + 1. (if i \<in> ?f ` X then 1 else 0) = 0"
            unfolding f_dom
            by force
        qed
      moreover have "(\<And>i. ?E i < ?p)"
        by fastforce
      ultimately have jth_bit_1: "?E (?f b) = ?m div ?p ^ (?f b) mod ?p"
        using digits_in_base.seq_uniqueness[OF base(1) _ sum_of_poly_E]
        by blast

      have "eventually_zero ?D"
        proof (unfold eventually_zero_char, standard)
          show "\<forall>i\<ge>card X + 1. (if i \<in> ?f ` X then card {A \<in> S. i \<in> ?f ` A} else 0) = 0"
            unfolding f_dom
            by force
        qed
      moreover have "(\<And>i. ?D i < ?p)"
        proof -
          fix i
          have "{A \<in> S. i \<in> ?f ` A} \<subseteq> S"
            by blast
          then have "card {A \<in> S. i \<in> ?f ` A} \<le> card S"
            using S_prop card_mono
            by meson
          then show "?D i < ?p"
            using S_card
            by force
        qed
      ultimately have "?D (?f b) = ?m div ?p ^ (?f b) mod ?p"
        using digits_in_base.seq_uniqueness[OF base(1) _ sum_of_poly_D]
        by blast
      with jth_bit_1 have "?D (?f b) = ?E (?f b)"
        by argo
      with D_ge_2 show "False"
        by (auto split: if_splits)
    qed
qed

lemma xc_to_subset_sum_complete_aux:
assumes "xc_to_ss (X, S0) = (S', w, B)" "S \<subseteq> S'" "is_subset_sum (S, w, B)"
  "finite S" "finite X" "\<Union>S0 \<subseteq> X"
shows "cover S X"
proof -
  let ?f = "map_to_nat X"
  let ?p = "max 2 (card S' + 1)"
  have S_prop: "finite S" "(\<Sum>A\<in>S.  (weight ?p (?f ` A))) =  (weight ?p (?f ` X))" "S0 = S'"
      using assms
      unfolding xc_to_ss_def is_subset_sum_def Let_def
      by auto
  have f_unfold:
    "?f ` X = (if X = {} then {} else {1..card X})"
    "inj_on ?f X"
      using map_to_nat_unfold assms
      by blast+

  have "?p \<ge> 2"
    by auto
  hence weight_unfold:
  "weight ?p (?f ` X) = \<Sum>{?p ^ x | x . x \<in> (?f ` X)}"
  "\<forall>A\<in>S. weight ?p (?f ` A) = \<Sum>{?p ^ x | x . x \<in> (?f ` A)}"
    using weight_eq_poly[of ?p]
    by blast+
  hence "(\<Sum>A\<in>S.  (weight ?p (?f ` A))) = \<Sum>{?p ^ x | x . x \<in> (?f ` X)}"
    using S_prop(2)
    by argo
  moreover from weight_unfold(2) have
  "(\<Sum>A\<in>S.  (weight ?p (?f ` A))) = (\<Sum>A\<in>S. \<Sum>{?p ^ x | x . x \<in> (?f ` A)})"
    by simp
  ultimately have Sum_eq: "(\<Sum>A\<in>S. \<Sum>{?p ^ x | x . x \<in> (?f ` A)}) = \<Sum>{?p ^ x | x . x \<in> (?f ` X)}"
    by presburger

  from assms have "disjoint S"
   using ss_leads_disjoint
   by blast

  moreover have "\<Union>S = X"
  proof (rule ccontr)
    assume "\<Union>S \<noteq> X"
    moreover from assms have "\<Union>S' \<subseteq> X" "finite (\<Union>S')"
      using finite_subset S_prop(3)
      by blast+
    moreover have "\<Union>S \<subseteq> \<Union>S'"
      using assms(2)
      by blast
    ultimately have prems: "\<Union>S \<subset> X" "finite (\<Union> S)"
      by (auto simp add: finite_subset)
    with S_prop have "\<forall>i \<in> S. finite i"
      by (metis Sup_upper finite_subset)
    hence *: "\<forall>i\<in>S. finite (?f ` i)"
      by blast

    with f_unfold prems have "inj_on ?f (\<Union>S)"
      unfolding inj_on_def
      by blast
    with \<open>disjoint S\<close> have "disjoint ((`) ?f ` S)"
      by (simp add: disjoint_image)
    hence **:"\<forall>i\<in>S. \<forall>j\<in>S. i \<noteq> j \<longrightarrow> map_to_nat X ` i \<inter> map_to_nat X ` j = {}"
      unfolding disjoint_def
      by (metis Sup_upper \<open>disjoint S\<close> \<open>inj_on ?f (\<Union> S)\<close> disjointD
         image_empty inj_on_image_Int)

    have strict_subset: "\<Union> ((`) ?f ` S) \<subset> ?f ` X"
      using prems(1)
      by (metis \<open>inj_on ?f X\<close> image_Union image_strict_mono)
    hence "(\<Sum>x\<in>\<Union> ((`) ?f ` S). ?p ^ x) < (\<Sum>x\<in>?f ` X. ?p ^ x)"
      proof-
        from strict_subset obtain b where b_def: "b \<in> ?f ` X - \<Union> ((`) ?f ` S)"
          by blast
        hence "b \<in> ?f ` X"
          by blast
        moreover hence "\<forall>b \<in> ?f ` X. b > 0"
          using f_unfold
          by auto
        ultimately have "0 < b ^ max 2 (card S + 1)" "\<forall>b \<in> ?f ` X. b \<ge> 0"
          by force+

        moreover have "finite (?f ` X)"
          using assms
          by blast
        thm sum_strict_mono2[of "?f ` X" "\<Union> ((`) ?f ` S)" b "(\<lambda>x. ?p ^ x)"]
        ultimately show ?thesis
          using b_def strict_subset
            sum_strict_mono2[of "?f ` X" "\<Union> ((`) ?f ` S)" b "(\<lambda>x. ?p ^ x)"]
          by fastforce
      qed
    moreover from \<open>finite S\<close> * ** have
      "(\<Sum>x\<in>\<Union> ((`) ?f ` S). ?p ^ x) = (\<Sum>x\<in>S. \<Sum>x\<in>?f ` x. ?p ^ x)"
      using sum.UNION_disjoint[of S "(`) ?f" "(\<lambda>x. ?p ^ x)"]
      by blast
    ultimately have "(\<Sum>x\<in>S. \<Sum>x\<in>?f` x. ?p ^ x) < (\<Sum>x\<in>?f ` X. ?p ^ x)"
      by argo
    with S_prop
    show "False"
      unfolding weight_def
      by (metis (no_types, lifting) Sum_eq nat_neq_iff sum.cong weight_def
      weight_unfold(1) weight_unfold(2))
  qed

  ultimately show ?thesis
    unfolding cover_def
    by blast
qed

subsection "the final theorem"


lemma xc_to_subset_sum_sound:
"(X, S) \<in> exact_cover \<Longrightarrow> (xc_to_ss (X, S)) \<in> subset_sum"
proof (cases "infinite X \<or> (\<not> \<Union>S \<subseteq> X)")
  case True
  assume "(X, S) \<in> exact_cover"
  with True show ?thesis
    unfolding exact_cover_def xc_to_ss_def
    by fastforce
next
  case False
  assume prems: "(X, S) \<in> exact_cover"
  with False obtain S' where "cover S' X" "S' \<subseteq> S"
    unfolding exact_cover_def cover_def
    by blast
  moreover from False obtain w B where unfold:
  "xc_to_ss (X, S) = (S, w, B)"
    unfolding subset_sum_def xc_to_ss_def
    by (auto simp: Let_def split: if_splits)
  ultimately have "is_subset_sum (S', w, B)"
    using xc_to_subset_sum_sound_aux False
    by blast
  moreover from prems have "finite S"
    unfolding exact_cover_def
    by (meson False finite_UnionD rev_finite_subset)
  ultimately show ?thesis
    using \<open>S' \<subseteq> S\<close> \<open>xc_to_ss (X, S) = (S, w, B)\<close>
    unfolding subset_sum_def
    by auto
qed

lemma xc_to_subset_sum_complete:
"(xc_to_ss (X, S)) \<in> subset_sum \<Longrightarrow> (X, S) \<in> exact_cover"
proof (cases "infinite X \<or> (\<not> \<Union>S \<subseteq> X)")
  case True
  assume "(xc_to_ss (X, S)) \<in> subset_sum"
  with True show ?thesis
    unfolding xc_to_ss_def subset_sum_def
    using infinite_not_in_ss
    by auto
next
  case False
  assume "(xc_to_ss (X, S)) \<in> subset_sum"
  with False obtain w B S' where unfold:
  "xc_to_ss (X, S) = (S, w, B)" "S' \<subseteq> S" "is_subset_sum (S', w, B)"
    unfolding subset_sum_def xc_to_ss_def
    by (auto simp: Let_def split: if_splits)
  moreover with False have "finite S'" "cover S' X"
    using xc_to_subset_sum_complete_aux
    by (metis finite_UnionD infinite_super)+
  ultimately show ?thesis
    using exact_coverI[of S' S] False
    by blast
qed

theorem is_reduction_xc_to_ss: "is_reduction xc_to_ss exact_cover subset_sum"
  using xc_to_subset_sum_sound xc_to_subset_sum_complete by (intro is_reductionI) auto

end
