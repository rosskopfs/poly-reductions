\<^marker>\<open>creator "Manuel Eberl"\<close>
theory Polynomial_Growth_Functions
  imports Landau_Symbols.Landau_More
begin

subsection \<open>Auxiliary stuff\<close>

lemma natfun_bigoE:
  fixes f :: "nat \<Rightarrow> _"
  assumes bigo: "f \<in> O(g)" and nz: "\<And>n. n \<ge> n0 \<Longrightarrow> g n \<noteq> 0"
  obtains c where "c > 0" "\<And>n. n \<ge> n0 \<Longrightarrow> norm (f n) \<le> c * norm (g n)"
proof -
  from bigo obtain c where c: "c > 0" "eventually (\<lambda>n. norm (f n) \<le> c * norm (g n)) at_top"
    by (auto elim: landau_o.bigE)
  then obtain n0' where n0': "\<And>n. n \<ge> n0' \<Longrightarrow> norm (f n) \<le> c * norm (g n)"
    by (auto simp: eventually_at_top_linorder)
  define c' where "c' = Max ((\<lambda>n. norm (f n) / norm (g n)) ` (insert n0 {n0..<n0'}))"
  have "norm (f n) \<le> max 1 (max c c') * norm (g n)" if "n \<ge> n0" for n
  proof (cases "n \<ge> n0'")
    case False
    with that have "norm (f n) / norm (g n) \<le> c'"
      unfolding c'_def by (intro Max.coboundedI) auto
    also have "\<dots> \<le> max 1 (max c c')" by simp
    finally show ?thesis using nz[of n] that by (simp add: field_simps)
  next
    case True
    hence "norm (f n) \<le> c * norm (g n)" by (rule n0')
    also have "\<dots> \<le> max 1 (max c c') * norm (g n)"
      by (intro mult_right_mono) auto
    finally show ?thesis .
  qed
  with that[of "max 1 (max c c')"] show ?thesis by auto
qed

lemma natfun_bigo_poly_iff:
  fixes f :: "nat \<Rightarrow> real"
  shows "f \<in> O(\<lambda>n. n ^ k) \<longleftrightarrow> (\<exists>c. \<forall>n>0. \<bar>f n\<bar> \<le> c * real n ^ k)"
proof
  assume "\<exists>c. \<forall>n>0. \<bar>f n\<bar> \<le> c * real n ^ k"
  then obtain c where c: "\<forall>n>0. \<bar>f n\<bar> \<le> c * real n ^ k"
    by auto
  have "eventually (\<lambda>n. \<bar>f n\<bar> \<le> c * real n ^ k) at_top"
    using eventually_gt_at_top[of 0] by eventually_elim (use c in auto)
  thus "f \<in> O(\<lambda>n. n ^ k)"
    by (intro bigoI[of _ c]) (auto intro!: always_eventually)
next
  assume 1: "f \<in> O(\<lambda>n. n ^ k)"
  have 2: "real n ^ k \<noteq> 0" if "n \<ge> 1" for n :: nat using that by auto
  from natfun_bigoE[OF 1 2, of 1] obtain c where "\<forall>n\<ge>1. \<bar>f n\<bar> \<le> c * real n ^ k"
    by simp metis?
  thus "\<exists>c. \<forall>n>0. \<bar>f n\<bar> \<le> c * real n ^ k"
    by (auto simp: Suc_le_eq)
qed


subsection \<open>Polynomial-growth functions\<close>

definition poly :: "(nat \<Rightarrow> nat) \<Rightarrow> bool"
  where "poly f \<longleftrightarrow> (\<exists>k. (\<lambda>n. real (f n)) \<in> O(\<lambda>n. real n ^ k))"

lemma poly_iff_ex_smallo: "poly f \<longleftrightarrow> (\<exists>k. (\<lambda>n. real (f n)) \<in> o(\<lambda>n. real n ^ k))"
  unfolding poly_def
proof safe
  fix k assume "f \<in> O(\<lambda>n. n ^ k)"
  also have "(\<lambda>n. real n ^ k) \<in> o(\<lambda>n. real n ^ (k + 1))"
    by force
  finally have "f \<in> o(\<lambda>n. n ^ (k + 1))" .
  thus "\<exists>k. f \<in> o(\<lambda>n. n ^ k)" ..
qed (auto intro: landau_o.small_imp_big)

lemma poly_const [simp, intro]: "poly (\<lambda>_. c)"
  by (auto simp: poly_def intro!: exI[of _ 0])

lemma poly_cmult [intro]: "poly f \<Longrightarrow> poly (\<lambda>x. c * f x)"
  by (auto simp: poly_def)

lemma poly_add [intro]:
  assumes "poly f" "poly g"
  shows "poly (\<lambda>x. f x + g x)"
proof -
  from assms obtain k l where kl: "f \<in> O(\<lambda>n. n ^ k)" "g \<in> O(\<lambda>n. n ^ l)"
    by (auto simp: poly_def)
  have "f \<in> O(\<lambda>n. n ^ max k l)" "g \<in> O(\<lambda>n. n ^ max k l)"
    by (rule kl[THEN landau_o.big.trans], force)+
  from sum_in_bigo(1)[OF this] show ?thesis
    by (auto simp: poly_def)
qed

lemma poly_diff [intro]:
  assumes "poly f" "poly g"
  shows "poly (\<lambda>x. f x - g x)"
proof -
  from assms obtain k l where kl: "f \<in> O(\<lambda>n. n ^ k)" "g \<in> O(\<lambda>n. n ^ l)"
    by (auto simp: poly_def)
  have "(\<lambda>x. real (f x - g x)) \<in> O(\<lambda>x. real (f x) - real (g x))"
    by (intro landau_o.big_mono) (auto intro!: always_eventually)
  also have "f \<in> O(\<lambda>n. n ^ max k l)" "g \<in> O(\<lambda>n. n ^ max k l)"
    by (rule kl[THEN landau_o.big.trans], force)+
  from sum_in_bigo(2)[OF this] have "(\<lambda>x. real (f x) - real (g x)) \<in> O(\<lambda>x. real x ^ max k l)" .
  finally show ?thesis
    by (auto simp: poly_def)
qed

lemma poly_mult [intro]:
  assumes "poly f" "poly g"
  shows "poly (\<lambda>x. f x * g x)"
proof -
  from assms obtain k l where kl: "f \<in> O(\<lambda>n. n ^ k)" "g \<in> O(\<lambda>n. n ^ l)"
    by (auto simp: poly_def)
  from landau_o.big.mult[OF this] have "(\<lambda>n. f n * g n) \<in> O(\<lambda>n. n ^ (k + l))"
    by (simp add: power_add)
  thus ?thesis by (auto simp: poly_def)
qed

definition make_mono :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "make_mono f n = Max (f ` {..n})"

lemma le_make_mono [intro]: "f n \<le> make_mono f n"
  by (auto simp: make_mono_def)

lemma mono_make_mono [intro]: "mono (make_mono f)"
  by (auto simp: make_mono_def incseq_def)

lemma poly_make_mono_iff: "poly (make_mono f) \<longleftrightarrow> poly f"
proof safe
  fix f
  assume *: "poly (make_mono f)"
  have "f \<in> O(make_mono f)"
    by (rule landau_o.big_mono) (auto intro!: always_eventually)
  also from * obtain k where "make_mono f \<in> O(\<lambda>n. n ^ k)"
    by (auto simp: poly_def)
  finally show "poly f"
    by (auto simp: poly_def)
next
  assume "poly f"
  then obtain k where "f \<in> O(\<lambda>n. n ^ k)"
    by (auto simp: poly_def)
  then obtain c' :: real where c': "\<And>n. n > 0 \<Longrightarrow> f n \<le> c' * n ^ k"
    by (subst (asm) natfun_bigo_poly_iff) auto
  define c where "c = max c' 1"
  have "c > 0" by (simp add: c_def)
  have c: "f n \<le> c * n ^ k" if "n > 0" for n
  proof -
    have "f n \<le> c' * n ^ k"
      using c'[of n] that by simp
    also have "\<dots> \<le> c * n ^ k"
      by (intro mult_right_mono) (auto simp: c_def)
    finally show ?thesis by simp
  qed

  have "eventually (\<lambda>n. real (make_mono f n) \<le> real (f 0) + c * real n ^ k) at_top"
    using eventually_gt_at_top[of 0]
  proof eventually_elim
    case (elim n)
    have "real (make_mono f n) = real (Max (f ` {..n}))"
      by (auto simp: make_mono_def)
    also have "{..n} = insert 0 {0<..n}"
      using elim by auto
    also have "Max (f ` \<dots>) = max (f 0) (Max (f ` {0<..n}))"
      using elim by (simp add: Max_insert)
    also have "real \<dots> = max (real (f 0)) (real (Max (f ` {0<..n})))"
      by simp
    also have "real (Max (f ` {0<..n})) = Max ((real \<circ> f) ` {0<..n})"
      using elim by (subst mono_Max_commute) (auto simp: image_image incseq_def)
    also have "\<dots> \<le> c * real n ^ k"
      unfolding o_def
    proof (intro Max.boundedI; safe?)
      fix i assume i: "i \<in> {0<..n}"
      from i have "real (f i) \<le> c * real i ^ k"
        by (intro c) auto
      also have "\<dots> \<le> c * real n ^ k"
        using i \<open>c > 0\<close> by (auto intro!: mult_left_mono power_mono)
      finally show "real (f i) \<le> c * real n ^ k" .
    qed (use elim in auto)
    hence "max (real (f 0)) (Max ((real \<circ> f) ` {0<..n})) \<le> max (real (f 0)) (c * real n ^ k)"
      by (intro max.mono) auto
    also have "\<dots> \<le> real (f 0) + c * real n ^ k"
      using \<open>c > 0\<close> by simp
    finally show ?case .
  qed
  hence "make_mono f \<in> O(\<lambda>n. real (f 0) + c * real n ^ k)"
    using \<open>c > 0\<close> by (intro bigoI[of _ 1]) auto
  also have "(\<lambda>n. real (f 0) + c * real n ^ k) \<in> O(\<lambda>n. real n ^ k)"
    using \<open>c > 0\<close> by (intro sum_in_bigo) auto
  finally show "poly (make_mono f)"
    by (auto simp: poly_def)
qed

lemma poly_compose [intro]:
  assumes "poly f" "poly g"
  shows "poly (f \<circ> g)"
proof -
  from assms have "poly (make_mono f)"
    by (simp add: poly_make_mono_iff)
  then obtain k c where k: "\<And>n. n > 0 \<Longrightarrow> make_mono f n \<le> c * real n ^ k"
    by (auto simp: poly_def natfun_bigo_poly_iff)
  from assms obtain l where l: "g \<in> o(\<lambda>n. n ^ l)"
    by (auto simp: poly_iff_ex_smallo)

  have "eventually (\<lambda>n. g n \<le> n ^ l) at_top"
    using landau_o.smallD[OF l, of 1] by auto
  hence "eventually (\<lambda>n. real (f (g n)) \<le> c * real n ^ (k * l)) at_top"
    using eventually_gt_at_top[of 0]
  proof eventually_elim
    case (elim n)
    have "real (f (g n)) \<le> real (make_mono f (g n))"
      by auto
    also from elim(1) have "make_mono f (g n) \<le> make_mono f (n ^ l)"
      by (rule monoD[OF mono_make_mono])
    also have "\<dots> \<le> c * (n ^ l) ^ k"
      using k[of "n ^ l"] \<open>n > 0\<close> by simp
    also have "\<dots> = c * real n ^ (k * l)"
      by (subst mult.commute) (simp add: power_mult)
    finally show ?case by simp
  qed
  hence "f \<circ> g \<in> O(\<lambda>n. n ^ (k * l))"
    by (intro bigoI[of _ c]) auto
  thus ?thesis by (auto simp: poly_def)
qed

lemma poly_linear: "poly (\<lambda>a. a)"
  unfolding poly_def by force

end