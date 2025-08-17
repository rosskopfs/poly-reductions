theory XC_To_THREE_DM
  imports Main
    "List-Index.List_Index"
    Discriminated_Union
    THREE_DM_Definition
    XC_Definition
begin

lemma mod_SucE: " Suc a mod k = Suc b mod k \<Longrightarrow> a mod k = b mod k"
  using mod_Suc by (metis nat.inject nat.simps(3))

text \<open>Plays the role of \<pi> in karp72. It is a cyclic permutation of \<open>{(x,s)|x. \<in> s}\<close>\<close>

definition to_list where
  "to_list s = (SOME l. set l = s \<and> distinct l)"

lemma to_list_distinct:
  assumes "finite s"
  shows   "set (to_list s) = s \<and> distinct (to_list s)"
  unfolding to_list_def using finite_distinct_list[OF assms]
  by (intro someI_ex[of "\<lambda>l.  set l = s \<and> distinct l"])

definition "nxtk k  = (\<lambda>(x, s). (let l = to_list s in l!(((index l x) + k) mod (length l)), s))"

definition nxt where "nxt = nxtk 1"

lemma nxt_nxtk:
  assumes "x \<in> s" "finite s"
  shows "nxt ((nxtk k) (x,s)) = nxtk (Suc k) (x,s)"
  using assms to_list_distinct[OF \<open>finite s\<close>]  mod_Suc_eq
        mod_less_divisor[of "length (to_list s)",
        THEN index_nth_id[of "to_list s", rotated]]
  unfolding nxtk_def nxt_def Let_def
  by (cases "0 < length (to_list s)") auto

lemma nxt_el:
  assumes "x \<in> s" "finite s"
  shows "\<exists>x'. nxt (x,s) = (x',s) \<and> x' \<in> s"
  unfolding nxt_def Let_def nxtk_def
  using assms to_list_distinct[OF \<open>finite s\<close>]
        mod_less_divisor[THEN nth_mem, of "to_list s"]
  by (cases "length (to_list s) > 0") force+


lemma nxtk_induct :
  assumes f: "finite s" and el:"x \<in> s"
     and "P (nxtk 0 (x, s))"
     and "\<And>x. P (x,s) \<Longrightarrow> P (nxt (x,s))"
  shows "P (nxtk k (x,s))"
  using assms nxt_nxtk[OF el f, symmetric]
  by (induction k)  (auto simp add: nxtk_def)


lemma nxt_induct:
  assumes "finite s" "x \<in> s"
          "P (x,s)"
          "\<And>x. P (x,s) \<Longrightarrow> P (nxt (x,s))"
  shows  "\<forall>y \<in> s. P (y,s)"
proof (rule ballI)
  fix y
  assume "y \<in> s"
  let ?l = "to_list s"
  let ?st = "index ?l x"
  let ?fin = "index ?l y"
  let ?d = "(length ?l - ?st) + ?fin"
  have "(?st + ?d) mod (length ?l) = ?fin mod (length ?l)"
    using index_le_size[of ?l x] index_le_size[of ?l y] by simp
  then have "(y,s) = nxtk ?d (x,s)"
    by (simp add: \<open>y \<in> s\<close> assms(1) nxtk_def to_list_distinct)
  moreover have "P (nxtk ?d (x,s))"
    by (induction rule: nxtk_induct)
       (auto simp add: assms nxtk_def to_list_distinct)
  ultimately show "P (y, s)" by auto
qed

lemma nxt_inj_on_discriminated_Union:
  assumes "finite (\<Uplus>S)"
  shows "inj_on nxt (\<Uplus>S)"
proof (intro inj_on_diff inj_onI)
  fix x y
  assume "x \<in> (\<Uplus>S)" "y \<in> (\<Uplus>S)" "nxt x = nxt y"
  then obtain x' y' s where x'y'_def:"x = (x',s)" "y = (y',s)"
    unfolding nxt_def nxtk_def by fastforce
  then have "finite s"
    using Union_upper \<open>y \<in> (\<Uplus>S)\<close> assms finite_subset
    finite_Union_if_finite_discriminated_Union by fastforce
  let ?l = "to_list s"
  have "?l ! ((index ?l x' + 1) mod length ?l) =
        ?l ! ((index ?l y' + 1) mod length ?l) "
    using \<open>nxt x = nxt y\<close>  unfolding nxt_def nxtk_def Let_def x'y'_def
    by fastforce
  then have "(Suc (index ?l x')) mod length ?l = (Suc (index ?l y')) mod length ?l"
    using to_list_distinct[OF \<open>finite s\<close>]
    by (cases ?l) (simp add: nth_eq_iff_index_eq)+
  then have "index ?l x'  mod length ?l = index ?l y'  mod length ?l"
    by (rule mod_SucE)
  then show "x = y"
    using \<open>finite s\<close> \<open>x \<in> (\<Uplus>S)\<close> \<open>y \<in> (\<Uplus>S)\<close> to_list_distinct x'y'_def
    by fastforce
qed


definition MALFORMED where
  "MALFORMED = ({(undefined,undefined,undefined)},{})"

lemma MALFROMED_not_in_THREE_DM: "MALFORMED \<notin> three_dm"
  unfolding MALFORMED_def three_dm_def
  by blast

definition "xc_to_three_dm = (\<lambda>(X, S). if \<Union> S = X ∧ finite X then
    let
      T = \<Uplus>S;
      \<alpha> = (SOME f. inj_on f X \<and> f ` X \<subseteq> T );
      U1 = { (\<alpha> x, (x, s), (x, s)) | s x. s \<in> S \<and> x \<in> s };
      U2 = \<Union> { {(\<beta>, (x,s), nxt (x,s)) | s x. s \<in> S \<and> x \<in> s }
                | \<beta>. \<beta> \<notin> (\<alpha> ` X) \<and> \<beta> \<in> T }
    in
      (U1 \<union> U2, T) else MALFORMED
  )"

subsection \<open>Soundness\<close>

lemma xc_to_three_dm_sound:
  assumes "(X, S) \<in> exact_cover"
  shows "xc_to_three_dm (X, S) \<in> three_dm"
proof -
  from assms obtain S' where
    "finite X" "\<Union>S \<subseteq> X" "S' \<subseteq> S" "\<Union>S' = X" "pairwise disjnt S'"
    unfolding exact_cover_def by blast

  have "finite (\<Union>S)"
    using \<open>\<Union> S \<subseteq> X\<close> \<open>finite X\<close> infinite_super by blast
  then have "finite S"
    using finite_UnionD by blast
  have fin_s: "s \<in> S \<Longrightarrow> finite s" for s
    by (meson Sup_upper \<open>finite (\<Union> S)\<close> infinite_super)

  let ?T = "\<Uplus>S"
  have fin_T: "finite ?T"
     using \<open>finite (\<Union> S)\<close> finite_discriminated_Union by blast

  define \<alpha> where "\<alpha> = (SOME f.  inj_on f X \<and> f ` X \<subseteq> ?T)"
  have "card X \<le> card ?T"
  proof -
    have "card ?T = sum card S"
      using card_discriminated_Union fin_s by blast
    also have "\<dots> \<ge> sum card S'" using \<open>finite S\<close> \<open>S' \<subseteq> S\<close>
      by (intro sum_mono2) auto
    finally show ?thesis
      using \<open>\<Union> S' = X\<close> card_Union_le_sum_card le_trans by blast
  qed
  then have inj_\<alpha>: "inj_on \<alpha> X \<and> \<alpha> ` X \<subseteq> ?T"
    unfolding \<alpha>_def using \<open>finite X\<close> fin_T
    by (intro someI_ex[of "\<lambda>f. inj_on f X \<and> f ` X \<subseteq> ?T"] inj_on_iff_card_le[THEN iffD2])


  let ?U1 = "{ (\<alpha> x, (x, s), (x, s)) | s x. s \<in> S \<and> x \<in> s }"
  let ?U2 = " \<Union> { {(\<beta>, (x,s), nxt (x,s))
                | s x. s \<in> S \<and> x \<in> s }
                | \<beta>. \<beta> \<notin> (\<alpha> ` X) \<and> \<beta> \<in> ?T }"
  let ?U = "?U1 \<union> ?U2"

  define A where "A = {(x, s) | s x. s \<in> S' \<and> x \<in> s}"
  have "A \<subseteq> ?T" unfolding A_def using \<open>S' \<subseteq> S\<close> by blast
  then have "finite A" using fin_T rev_finite_subset by blast

  have "card (?T - A) = card (?T - (\<alpha> ` X))"
  proof -
    have "card (?T - A) = card ?T - card A"
      using \<open>A \<subseteq> ?T\<close> \<open>finite A\<close> card_Diff_subset by blast
    moreover have "card (?T - \<alpha> ` X) = card ?T - card (\<alpha> ` X)"
      using \<alpha>_def \<open>finite X\<close> inj_\<alpha> card_Diff_subset by auto
    moreover{
      have fin_s': "s \<in> S' \<Longrightarrow> finite s" for s
        using \<open>S' \<subseteq> S\<close> fin_s by blast
      then have "card  A = sum card S'"
        using A_def card_discriminated_Union by blast
      also have "... = card (\<Union>S')"
        using fin_s' \<open>disjoint S'\<close>
        by (intro card_Union_disjoint[symmetric]) auto
      also have "... = card (\<alpha> ` X)"
        using inj_\<alpha> card_image[symmetric] \<open>\<Union> S' = X\<close> by fast
      finally have "card A = card (\<alpha> ` X)".
    }
    ultimately show ?thesis by argo
  qed
  then obtain \<beta> where \<beta>_bij: "bij_betw \<beta> (?T - A) (?T - (\<alpha> ` X))"
    using finite_same_card_bij finite_Diff fin_T
    by meson

  define f where "f = (\<lambda>(x, (s::'a set)). \<alpha> x)"


  let ?M1 = "{ (f u, u, u) |u. u \<in> A }"
  let ?M2 = "{ (\<beta> u, u, nxt u)|u. u \<in> (?T - A)}"
  let ?M = "?M1 \<union> ?M2"

  have "(?U, ?T) \<in> three_dm"
  proof (intro three_dm_cert[of ?M])
    show "finite ?T" using fin_T.
    show  "?U \<subseteq> ?T \<times> ?T \<times> ?T"  using inj_\<alpha> \<open>\<Union>S \<subseteq> X\<close> nxt_el fin_s
      by (auto, blast, meson)
    show "?M \<subseteq> ?U"
    proof -
      have "(\<beta> u, u, nxt u) \<in> ?U2"  if "u \<in> (?T - A)" for u
      proof -
        have *:"\<beta> u  \<notin> (\<alpha> ` X) \<and> \<beta> u \<in> ?T"
          using \<beta>_bij bij_betwE that by fastforce
        moreover have "(\<beta> u, u, nxt u) \<in>  {(\<beta> u, (x, s), nxt (x, s)) |s x. s \<in> S \<and> x \<in> s}"
          using that by blast
        moreover have "{(\<beta> u, (x, s), nxt (x, s)) |s x. s \<in> S \<and> x \<in> s} \<in>
                { {(\<beta>, (x,s), nxt (x,s))
                | s x. s \<in> S \<and> x \<in> s }
                | \<beta>. \<beta> \<notin> (\<alpha> ` X) \<and> \<beta> \<in> ?T }"
          using "*" that by fastforce
        ultimately show ?thesis  using that
          by (meson UnionI)
      qed
      then have "?M2 \<subseteq> ?U2"  by blast
      moreover have "?M1 \<subseteq> ?U1" unfolding f_def A_def
        using \<open>S' \<subseteq> S\<close> by auto
      ultimately show ?thesis
        by (meson sup_mono)
    qed

    show "card ?M = card ?T"
    proof -
      have "finite ?M1" using inj_on_def \<open>finite A\<close>
        by (intro card_Un_disjoint finite_Collect_mem[THEN iffD2]) auto
      moreover have "finite ?M2" using inj_on_def fin_T
        by (intro finite_Collect_mem[THEN iffD2]) blast+
      ultimately have "card ?M = card ?M1 + card ?M2"
        by (intro card_Un_disjoint) auto
      moreover have "card ?M1 = card A"
        by (intro card_Collect_mem) (simp add: inj_on_def)
      moreover have "card ?M2 = card (?T - A)"
        by (intro card_Collect_mem) (simp add: inj_on_def)
      moreover have "card ?T = card A  + card (?T - A)"
        using card_Int_Diff[of ?T A]
        by (simp add: Int_absorb1 \<open>A \<subseteq> ?T\<close> fin_T)
      ultimately show ?thesis by argo
    qed

    show  "self_distinct_components3 ?M" using inj_on_id
    proof (intro self_distinct_components3_unionI
                 self_distinct_components3_injI)
      show "distinct_components3 ?M1 ?M2"
      proof(intro distinct_components3I)
        fix a b c a1 b1 c1
        assume in_M1: "(a, b, c) \<in> ?M1"
        assume in_M2: "(a1, b1, c1) \<in> ?M2"
        have "b \<noteq> b1" using in_M1 in_M2 by blast
        moreover {
          have "c1 = nxt b1" using in_M2 by blast
          then have "snd c1 = snd b1"
            by (simp add: case_prod_unfold nxt_def nxtk_def)
          then have "snd c1 \<noteq> snd b"
            using \<open>b \<noteq> b1\<close>  A_def in_M1 in_M2 by force
          then have "c \<noteq> c1" using in_M1 by blast
        }
        moreover {
          have "\<beta> b1 \<notin> (\<alpha> ` X)"
            using \<beta>_bij bij_betw_apply in_M2 by fastforce
          moreover have "f b \<in> (\<alpha> ` X)"
            using A_def \<open>\<Union> S' = X\<close> f_def in_M1 by auto
          ultimately have "a \<noteq> a1"  using in_M1 in_M2 by auto
        }
        ultimately show "(a = a1 \<or> b = b1 \<or> c = c1) \<Longrightarrow> (a, b, c) = (a1, b1, c1)"
          by simp
      qed
      show "inj_on f A"
      proof (intro inj_onCI)
        fix x y
        assume "x \<in> A" "y \<in> A" "f x = f y" "x \<noteq> y"
        obtain a s b s' where *:"x = (a,s)" "a \<in> s" "s \<in> S'"
                                "y = (b,s')" "b \<in> s'" "s' \<in> S'"
          using A_def \<open>x \<in> A\<close> \<open>y \<in> A\<close>  by blast
        have "a \<noteq> b" using disjoint_def \<open>disjoint S'\<close> * \<open>x \<noteq> y\<close>
          by (cases "s = s'") fast+
        moreover have "\<alpha> a = \<alpha> b" using \<open>f x = f y\<close>
          by (simp add: "*" f_def)
        ultimately show False
          by (meson "*" UnionI \<open>S' \<subseteq> S\<close> \<open>\<Union> S \<subseteq> X\<close> in_mono inj_\<alpha> inj_on_def)
      qed
      show "inj_on \<beta> (?T - A)" using \<beta>_bij bij_betw_def by blast
      show "inj_on nxt (?T - A)"
        using nxt_inj_on_discriminated_Union fin_T
        by (intro inj_on_diff)
    qed (simp_all)
  qed
  moreover have "\<Union>S = X"
    using \<open>S' \<subseteq> S\<close> \<open>\<Union> S \<subseteq> X\<close> \<open>\<Union> S' = X\<close> by blast
  moreover have "finite X" using ‹finite X› by blast
  ultimately show ?thesis unfolding xc_to_three_dm_def Let_def using \<alpha>_def
    by simp
qed

subsection \<open>Completeness\<close>

lemma xc_to_three_dm_complete:
  assumes "xc_to_three_dm (X, S) \<in> three_dm"
  shows "(X, S) \<in> exact_cover"
proof (cases "\<Union>S = X ∧ finite X")
  case True
  then have "\<Union>S = X" by simp
  let ?T = "{(x, s) | s x. s \<in> S \<and> x \<in> s}"
  define \<alpha> where "\<alpha> = (SOME f.  inj_on f X \<and> f ` X \<subseteq> ?T)"
  let ?U1 = "{ (\<alpha> x, (x, s), (x, s)) | s x. s \<in> S \<and> x \<in> s }"
  let ?U2 = " \<Union> { {(\<beta>, (x,s), nxt (x,s))
                | s x. s \<in> S \<and> x \<in> s }
                | \<beta>. \<beta> \<notin> (\<alpha> ` X) \<and> \<beta> \<in> ?T }"
  let ?U = "?U1 \<union> ?U2"

  obtain M where "M\<subseteq>?U" "card M = card ?T"  "self_distinct_components3 M"
    "finite ?T" "?U \<subseteq> ?T \<times> ?T \<times> ?T"
    using assms True unfolding three_dm_def xc_to_three_dm_def Let_def \<alpha>_def
    by auto
  define f where "f = (\<lambda>(x, (s::'a set)). \<alpha> x)"
  define S' where "S' = {s |s x. (\<alpha> x, (x, s), (x, s)) \<in> (?U1 \<inter> M)}"


  show "(X, S) \<in> exact_cover"
  proof (intro exact_coverI[of S'])
    show "S' \<subseteq> S"  unfolding S'_def by blast
    show "\<Union>S \<subseteq> X"  by (simp add: True)
    show "finite X"
      using finite_Union_if_finite_discriminated_Union
            \<open>finite ?T\<close> \<open>\<Union>S = X\<close> by blast

    have "card X \<le> card ?T"
    proof -
      have "finite s"  if "s \<in> S" for s
        by (meson Sup_le_iff \<open>\<Union> S \<subseteq> X\<close> \<open>finite X\<close> finite_subset that)
      then have "card ?T = sum card S"
        using card_discriminated_Union by blast
      then show ?thesis
        using \<open>\<Union>S = X\<close> card_Union_le_sum_card le_trans by auto
    qed
    then have inj_\<alpha>: "inj_on \<alpha> X \<and> \<alpha> ` X \<subseteq> ?T"
      unfolding \<alpha>_def using \<open>finite X\<close> \<open>finite ?T\<close>
      by (intro someI_ex[of "\<lambda>f. inj_on f X \<and> f ` X \<subseteq> ?T"]
          inj_on_iff_card_le[THEN iffD2])

    have "M \<subseteq> ?T \<times> ?T \<times> ?T"
      using \<open>M \<subseteq> ?U\<close> \<open>?U \<subseteq> ?T \<times> ?T \<times> ?T\<close>
      by order
    have M_decomp: "M = (?U1 \<inter> M) \<union> (?U2 \<inter> M)" using \<open>M \<subseteq>?U\<close>
      by auto

    have "X \<subseteq>  \<Union>S'"
    proof
      fix x assume "x \<in> X"
      then obtain s where "x \<in> s" and "s \<in> S"
        using \<open>\<Union>S = X\<close> by fast
      then have "\<alpha> x \<in> ?T"  using \<open>x \<in> X\<close> inj_\<alpha> by blast
      moreover have "fst ` M = ?T"
        using \<open>card M = card ?T\<close> \<open>self_distinct_components3 M\<close>
              \<open>finite ?T\<close> \<open>M \<subseteq> ?T \<times> ?T \<times> ?T\<close>
        by (intro fstM_T)
      ultimately have  "\<alpha> x \<in> fst ` M" by blast
      moreover have "\<alpha> x \<notin> fst ` (?U2 \<inter> M)"
        using image_iff \<open>x \<in> X\<close> by fastforce
      moreover have  "fst ` M  = fst ` (?U1 \<inter> M) \<union>  fst ` (?U2 \<inter> M)"
        by (metis M_decomp image_Un)
      ultimately have "\<alpha> x \<in> fst ` (?U1 \<inter> M)"  by simp
      then obtain el where "el \<in> (?U1 \<inter> M)" and "fst el = \<alpha> x" and "el \<in> ?U1"
        by fastforce
      then obtain s' where "el = (\<alpha> x, (x,s'), (x,s'))"
        by (auto, meson UnionI \<open>\<Union> S \<subseteq> X\<close> \<open>x \<in> X\<close> in_mono inj_\<alpha> inj_on_def)
      moreover then have "s' \<in> S'"
        using S'_def \<open>el \<in> ?U1 \<inter> M\<close> by blast
      ultimately show "x \<in> \<Union>S'"
        using \<open>el \<in> ?U1\<close> by blast
    qed
    moreover{

      have next_in: "(f (nxt (y,s)), nxt (y, s), nxt (y, s)) \<in> (?U1 \<inter> M)"
        if  "y \<in> s" "(f (y,s), (y, s), (y, s)) \<in> (?U1 \<inter> M)" for y s
      proof (cases  "nxt (y,s) \<noteq> (y,s)")
        case True
        have in_T: "(y,s) \<in> ?T" using that by auto
        have "(\<beta>, (y,s), nxt (y,s)) \<notin> (?U2 \<inter> M)" for \<beta>
          using that True \<open>self_distinct_components3 M\<close>
          unfolding distinct_components3_def
          by fastforce
        then have "nxt (y,s) \<notin> (t3_thrd ` (?U2 \<inter> M))"
          using inj_onD[OF nxt_inj_on_discriminated_Union[OF \<open>finite ?T\<close>] _ in_T]
          by (auto, blast)
        moreover have "nxt (y,s) \<in> (t3_thrd ` M)"
        proof -
          have "nxt (y,s) \<in> ?T"
            using Union_upper \<open>\<Union> S = X\<close> \<open>finite X\<close> finite_subset in_T nxt_el
            by fastforce
          moreover have "t3_thrd ` M = ?T"
            using \<open>card M = card ?T\<close> \<open>self_distinct_components3 M\<close>
              \<open>finite ?T\<close> \<open>M \<subseteq> ?T \<times> ?T \<times> ?T\<close>
            by (intro thrdM_T)
          ultimately show ?thesis by blast
        qed
        ultimately have "nxt (y,s) \<in> (t3_thrd ` (?U1 \<inter> M))"
          using image_Un[of t3_thrd "?U1 \<inter> M" "?U2 \<inter> M"] M_decomp
          by auto
        then show ?thesis unfolding f_def by force
      qed (use that in force)

      then have one_in_all_in: "\<forall>x \<in> s. (f (x,s), (x, s), (x, s)) \<in> (?U1 \<inter> M)"
        if  "y \<in> s" "(f (y,s), (y, s), (y, s)) \<in> (?U1 \<inter> M)" for y s
        using Union_upper \<open>\<Union> S = X\<close> \<open>finite X\<close> finite_subset that
        by (intro nxt_induct[of s y]) fastforce+

      have "disjoint S'"
      proof (intro Disjoint_Sets.disjointI, rule ccontr)
        fix a b
        assume "a \<in> S'" and "b \<in> S'" and "a \<noteq> b" and "a \<inter> b \<noteq> {}"
        obtain w1 w2 where witnesses: "w1 \<in> a" "(f (w1,a), (w1, a), (w1, a)) \<in> M"
          "w2 \<in> b" "(f (w2,b), (w2, b), (w2, b)) \<in> M"
          using \<open>a \<in> S'\<close> \<open>b \<in> S'\<close> f_def S'_def  by fast

        obtain x where "x \<in> a \<inter> b"  using \<open>a \<inter> b \<noteq> {}\<close> by blast
        have "(f (x,a), (x, a), (x, a)) \<in> M" and "(f (x,b), (x, b), (x, b)) \<in> M"
          using witnesses one_in_all_in \<open>S' \<subseteq> S\<close> \<open>a \<in> S'\<close>  \<open>b \<in> S'\<close> \<open>x \<in> a \<inter> b\<close>  f_def
          by auto
        moreover have "f (x,a) = f (x,b)" using f_def by simp
        ultimately show False
          using \<open>self_distinct_components3 M\<close> \<open>a \<noteq> b\<close> unfolding distinct_components3_def
          by fast
      qed

    }
    ultimately show "cover S' X"
      using \<open>S' \<subseteq> S\<close> \<open>\<Union> S = X\<close> cover_def
      by fastforce
  qed
  next
  case False
  then have "xc_to_three_dm (X, S) = MALFORMED" unfolding xc_to_three_dm_def by auto
  then show ?thesis using assms MALFROMED_not_in_THREE_DM by auto
qed

subsection "Theorem"

theorem is_reduction_xc_to_three_dm: "is_reduction xc_to_three_dm exact_cover three_dm"
  using xc_to_three_dm_sound xc_to_three_dm_complete
  by (intro is_reductionI) auto

end
