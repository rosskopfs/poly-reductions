theory Triangle_Extensions
  imports
    Landau_Auxiliaries
begin

text \<open>Stuff about triangle numbers, in particular triangular root \<close>

lemma triangle_Sum: "triangle n = (\<Sum>x\<in>{1..n}. x)"
  by (induction n) (auto simp add: triangle_def)

(* Proofs in here are ugly, look at again, I also do quite a lot by just doing it on reals and transfering back *)

(* Stuff for moving to the reals *)
lemma sqrt_power2_iff_eq: "x \<ge> 0 \<Longrightarrow> y\<ge>0\<Longrightarrow> sqrt x = y \<longleftrightarrow> x = y^2" by auto

lemma triangle_invert_real: "n\<ge>0 \<Longrightarrow> (sqrt (8*(n*(n+1) / 2)+1) - 1) / 2 = n"
proof-
  have s: "(8*(n*(n+1) / 2)+1) = (2 * n + 1)^2" if "n\<ge>0"
    using that by (auto simp add: power2_eq_square distrib_left mult.commute)
  have "sqrt (8*(n*(n+1) / 2)+1) = 2*n + 1" if "n\<ge>0"
    using that by (simp add: s sqrt_power2_iff_eq) algebra
  then show ?thesis if "n\<ge>0"
    using that by auto
qed

lemma sqrt_Discrete_sqrt: "nat (floor (sqrt n)) = floor_sqrt n"
  apply (rule antisym)
  apply (rule le_floor_sqrtI)
  apply (smt (verit, ccfv_threshold) of_int_floor_le of_nat_0_le_iff of_nat_le_of_nat_power_cancel_iff
      of_nat_nat real_less_lsqrt real_sqrt_ge_0_iff zero_le_floor)
  apply (rule floor_sqrt_leI)
  by (simp add: le_nat_floor real_le_rsqrt)

lemma divide2_div2: "nat (floor (n/2)) = n div 2"
  by linarith
lemma divide2_div2': "nat (floor (n/2)) = nat (floor (n::real)) div 2"
  by linarith

lemma triangular_part_real: "nat (floor (((sqrt (8*n + 1)) -1) /2)) = (floor_sqrt (8*n + 1) -1) div 2"
  apply (simp add: divide2_div2' nat_diff_distrib')
  by (metis add.commute of_nat_Suc of_nat_mult of_nat_numeral sqrt_Discrete_sqrt)

lemma triangle_invert_real_typ: "(sqrt (8*(n*(n+1) / 2)+1) - 1) / 2 = (n::nat)"
  using triangle_invert_real by simp

lemma triangle_invert_real_typ': "nat (floor ((sqrt (8*(n*(n+1) / 2)+1) - 1) / 2)) = (n::nat)"
  using triangle_invert_real by simp

text \<open>Triangular root\<close>

definition "tsqrt n \<equiv> (floor_sqrt (8*n + 1) - 1) div 2"

lemma tsqrt_0[simp]: "tsqrt 0 = 0"
  by code_simp
lemma tsqrt_1[simp]: "tsqrt 1 = 1"
  by code_simp
lemma tsqrt_2[simp]: "tsqrt 2 = 1"
  by code_simp

lemma tsqrt_correct[simp]: "tsqrt (triangle n) = n"
proof(unfold triangle_def tsqrt_def)
  have s: "real (n * Suc n div 2) = real n * (real n + 1) / 2"
    by (smt (verit, del_insts) Multiseries_Expansion.intyness_1 add.commute double_gauss_sum gauss_sum
        id_apply nat_1_add_1 nonzero_mult_div_cancel_left of_nat_Suc of_nat_eq_id of_nat_mult plus_1_eq_Suc)
  show "(floor_sqrt (8 * (n * Suc n div 2) + 1) - 1) div 2 = n"
    apply (subst triangular_part_real[symmetric]) apply (subst s)
    using triangle_invert_real_typ' by simp
qed

lemma mono_tsqrt: "mono tsqrt"
  unfolding tsqrt_def by (intro monoI) (auto simp: diff_le_mono div_le_mono mono_floor_sqrt')

lemma mono_tsqrt': "x\<le>y \<Longrightarrow> tsqrt x \<le> tsqrt y"
  using mono_tsqrt by (drule monoD)

text \<open>Alternative triangular root definition, based on how \<^const>\<open>floor_sqrt\<close> is defined
  Copied lemmas/proofs as well and modified them for some free properties.

  General way of this construction might be a student project?
\<close>

definition "tsqrt_alt n \<equiv> Max {m. triangle m \<le> n}"

lemma tsqrt_alt_aux:
  fixes n :: nat
  shows "finite {m. triangle m \<le> n}" and "{m. triangle m \<le> n} \<noteq> {}"
proof -
  { fix m
    assume "triangle m \<le> n"
    then have "m \<le> n"
      by (cases m) (simp_all)
  } note ** = this
  then have "{m. triangle m \<le> n} \<subseteq> {m. m \<le> n}" by auto
  then show "finite {m. triangle m \<le> n}" by (rule finite_subset) rule
  have "triangle 0 \<le> n" by simp
  then show *: "{m. triangle m \<le> n} \<noteq> {}" by blast
qed

lemma tsqrt_alt_unique:
  assumes "triangle m \<le> n" "n < triangle (Suc m)"
  shows   "tsqrt_alt n = m"
proof -
  have "m' \<le> m" if "triangle m' \<le> n" for m'
  proof -
    note that
    also note assms(2)
    finally have "m' < Suc m" (* Apparently I already have some connection to tsqrt here *)
      by (metis le_neq_implies_less less_or_eq_imp_le mono_tsqrt' nat_neq_iff tsqrt_correct)
    thus "m' \<le> m" by simp
  qed
  with \<open>triangle m \<le> n\<close> tsqrt_alt_aux[of n] show ?thesis unfolding tsqrt_alt_def
    by (intro antisym Max.boundedI Max.coboundedI) simp_all
qed


lemma triangle_nat_le_imp_le:
  fixes m n :: nat
  assumes "triangle m \<le> n"
  shows "m \<le> n"
proof (cases m)
  case 0
  then show ?thesis
    by simp
next
  case (Suc nat)
  then show ?thesis
    using assms by auto
qed

(* Real proof *)
lemma triangle_nat_le_eq_le: "triangle m \<le> triangle n \<longleftrightarrow> m \<le> n"
  for m n :: nat
  by (metis linorder_le_cases mono_tsqrt' tsqrt_correct verit_la_disequality)

(* basically linear search, delete this code equation once you have a better one *)
lemma tsqrt_alt_code_1 [code]: "tsqrt_alt n = Max (Set.filter (\<lambda>m. triangle m \<le> n) {0..n})"
proof -
  from triangle_nat_le_imp_le [of _ n] have "{m. m \<le> n \<and> triangle m \<le> n} = {m. triangle m \<le> n}" by auto
  then show ?thesis by (simp add: tsqrt_alt_def Set.filter_def)
qed

lemma tsqrt_alt_inverse_triangle [simp]: "tsqrt_alt (triangle n) = n"
proof -
  have "{m. m \<le> n} \<noteq> {}" by auto
  then have "Max {m. m \<le> n} \<le> n" by auto
  then show ?thesis
    by (auto simp add: tsqrt_alt_def triangle_nat_le_eq_le intro: antisym)
qed

lemma tsqrt_alt_zero [simp]: "tsqrt_alt 0 = 0"
  using tsqrt_alt_inverse_triangle [of 0] by simp

lemma tsqrt_alt_one [simp]: "tsqrt_alt 1 = 1"
  using tsqrt_alt_inverse_triangle [of 1] by simp

lemma mono_tsqrt_alt: "mono tsqrt_alt"
proof
  fix m n :: nat
  have *: "0 * 0 \<le> m" by simp
  assume "m \<le> n"
  then show "tsqrt_alt m \<le> tsqrt_alt n"
    apply (auto intro!: Max_mono \<open>0 * 0 \<le> m\<close> finite_less_ub simp add: tsqrt_alt_def triangle_nat_le_imp_le)
    apply (metis triangle_0 zero_le)
    done
qed

lemma mono_tsqrt_alt_': "m \<le> n \<Longrightarrow> tsqrt_alt m \<le> tsqrt_alt n"
  using mono_tsqrt_alt unfolding mono_def by auto

lemma tsqrt_alt_greater_zero_iff [simp]: "tsqrt_alt n > 0 \<longleftrightarrow> n > 0"
proof -
  have *: "0 < Max {m. triangle m \<le> n} \<longleftrightarrow> (\<exists>a\<in>{m. triangle m \<le> n}. 0 < a)"
    by (rule Max_gr_iff) (fact tsqrt_alt_aux)+
  show ?thesis
  proof
    assume "0 < tsqrt_alt n"
    then have "0 < Max {m. triangle m \<le> n}" by (simp add: tsqrt_alt_def)
    with * show "0 < n" by (auto dest: triangle_nat_le_imp_le)
  next
    assume "0 < n"
    then have "triangle 1 \<le> n \<and> 0 < (1::nat)" by simp
    then have "\<exists>q. triangle q \<le> n \<and> 0 < q" ..
    with * have "0 < Max {m. triangle m \<le> n}" by blast
    then show "0 < tsqrt_alt n" by (simp add: tsqrt_alt_def)
  qed
qed

(* No idea what this proof does, find out sometime :) *)
lemma tsqrt_alt_triangle_le [simp]: "triangle (tsqrt_alt n) \<le> n" (* FIXME tune proof *)
proof (cases "n > 0")
  case False then show ?thesis by simp
next
  case True then have "tsqrt_alt n > 0" by simp
  then have "mono (times (Max {m. triangle m \<le> n}))" by (auto intro: mono_times_nat simp add: tsqrt_alt_def)
  then have *: "Max {m. triangle m \<le> n} * Max {m. triangle m \<le> n} = Max (times (Max {m. triangle m \<le> n}) ` {m. triangle m \<le> n})"
    using tsqrt_alt_aux [of n] by (rule mono_Max_commute)
  have "\<And>a. a * a \<le> n \<Longrightarrow> Max {m. m * m \<le> n} * a \<le> n"
  proof -
    fix q
    assume "q * q \<le> n"
    show "Max {m. m * m \<le> n} * q \<le> n"
    proof (cases "q > 0")
      case False then show ?thesis by simp
    next
      case True then have "mono (times q)" by (rule mono_times_nat)
      then have "q * Max {m. m * m \<le> n} = Max (times q ` {m. m * m \<le> n})"
        using floor_sqrt_aux [of n] by (auto simp add: power2_eq_square intro: mono_Max_commute)
      then have "Max {m. m * m \<le> n} * q = Max (times q ` {m. m * m \<le> n})" by (simp add: ac_simps)
      moreover have "finite ((*) q ` {m. m * m \<le> n})"
        by (metis (mono_tags) finite_imageI finite_less_ub le_square)
      moreover have "\<exists>x. x * x \<le> n"
        by (metis \<open>q * q \<le> n\<close>)
      ultimately show ?thesis
        by simp (metis \<open>q * q \<le> n\<close> le_cases mult_le_mono1 mult_le_mono2 order_trans)
    qed
  qed
  then have "Max ((*) (Max {m. m * m \<le> n}) ` {m. m * m \<le> n}) \<le> n"
    apply (subst Max_le_iff)
      apply (metis (mono_tags) finite_imageI finite_less_ub le_square)
     apply auto
    apply (metis le0 mult_0_right)
    done
  with * show ?thesis
    using tsqrt_alt_aux Max_in by (auto simp add: tsqrt_alt_def)
qed

lemma tsqrt_alt_le: "tsqrt_alt n \<le> n"
  using tsqrt_alt_aux [of n] by (auto simp add: tsqrt_alt_def intro: triangle_nat_le_imp_le)

lemma Suc_tsqrt_alt_triangle_gt: "n < triangle (Suc (tsqrt_alt n))"
  using Max_ge[OF tsqrt_alt_aux(1), of "tsqrt_alt n + 1" n]
  by (cases "n < triangle (Suc (tsqrt_alt n))") (simp_all add: tsqrt_alt_def)

lemma le_tsqrt_alt_iff: "x \<le> tsqrt_alt y \<longleftrightarrow> triangle x \<le> y"
proof -
  have "x \<le> tsqrt_alt y \<longleftrightarrow> (\<exists>z. triangle z \<le> y \<and> x \<le> z)"
    using Max_ge_iff[OF tsqrt_alt_aux, of x y] by (simp add: tsqrt_alt_def)
  also have "\<dots> \<longleftrightarrow> triangle x \<le> y"
  proof safe
    fix z assume "x \<le> z" "triangle z \<le> y"
    thus "triangle x \<le> y" by (intro le_trans[of "triangle x" "triangle z" y]) (simp_all add: triangle_nat_le_eq_le)
  qed auto
  finally show ?thesis .
qed

lemma le_tsqrt_altI: "triangle x \<le> y \<Longrightarrow> x \<le> tsqrt_alt y"
  by (simp add: le_tsqrt_alt_iff)

lemma tsqrt_alt_le_iff: "tsqrt_alt y \<le> x \<longleftrightarrow> (\<forall>z. triangle z \<le> y \<longrightarrow> z \<le> x)"
  using Max.bounded_iff[OF tsqrt_alt_aux] by (simp add: tsqrt_alt_def)

lemma sqrt_leI:
  "(\<And>z. triangle z \<le> y \<Longrightarrow> z \<le> x) \<Longrightarrow> tsqrt_alt y \<le> x"
  by simp

lemma triangle_less_imp_less: "triangle x < triangle y \<Longrightarrow> 0 \<le> y \<Longrightarrow> x < y"
  by (simp add: less_le_not_le triangle_nat_le_eq_le)
lemma tsqrt_alt_Suc:
  "tsqrt_alt (Suc n) = (if \<exists>m. Suc n = triangle m then Suc (tsqrt_alt n) else tsqrt_alt n)"
proof cases
  assume "\<exists> m. Suc n = triangle m"
  then obtain m where m_def: "Suc n = triangle m" by blast
  then have lhs: "tsqrt_alt (Suc n) = m" by simp
  from m_def tsqrt_alt_triangle_le[of n]
    have "triangle (tsqrt_alt n) < triangle m" by linarith
  with triangle_less_imp_less have lt_m: "tsqrt_alt n < m" by blast
  from m_def Suc_tsqrt_alt_triangle_gt[of "n"]
    have "triangle m \<le> triangle (Suc(tsqrt_alt n))"
      by linarith
  with triangle_nat_le_eq_le have "m \<le> Suc (tsqrt_alt n)" by blast
  with lt_m have "m = Suc (tsqrt_alt n)" by simp
  with lhs m_def show ?thesis by metis
next
  assume asm: "\<not> (\<exists> m. Suc n = triangle m)"
  hence "Suc n \<noteq> triangle (tsqrt_alt (Suc n))" by simp
  with tsqrt_alt_triangle_le[of "Suc n"]
    have "tsqrt_alt (Suc n) \<le> tsqrt_alt n" by (intro le_tsqrt_altI) linarith
  moreover have "tsqrt_alt (Suc n) \<ge> tsqrt_alt n"
    by (intro monoD[OF mono_tsqrt_alt]) simp_all
  ultimately show ?thesis using asm by simp
qed

(* Continue with direct definition, once again by moving to reals*)

lemma triangle_tsqrt_le_real:
  "nat (floor (((sqrt (8 * n + 1) - 1) / 2) * ((1 + ((sqrt (8 * n + 1) - 1) / 2)) / 2))) \<le> n"
  by (auto simp add: triangle_def field_simps)

lemma tsqrt_real: "tsqrt n = nat (floor (((sqrt (8 * n + 1) - 1) / 2)))"
  apply (simp add: tsqrt_def field_simps)
  by (metis One_nat_def add.commute divide2_div2' mult.commute plus_1_eq_Suc triangular_part_real)

lemma triangle_tsqrt_real_pre:
  "triangle (tsqrt n) = nat (floor ((nat (floor (((sqrt (8 * n + 1) - 1) / 2))) * nat (floor (1 + ((sqrt (8 * n + 1) - 1) / 2)))) / 2))"
  unfolding triangle_def tsqrt_real divide2_div2
  apply (simp add: field_simps)
  by (smt (verit, best) Suc_eq_plus1 add_mult_distrib2 floor_diff_of_int int_nat_eq
      nat_int_comparison(1) nat_mult_1_right of_int_1 of_nat_1 of_nat_add plus_1_eq_Suc real_average_minus_first)

lemma triangle_tsqrt_le_real_bound: "nat (floor ((nat (floor (((sqrt (8 * n + 1) - 1) / 2))) * nat (floor (1 + ((sqrt (8 * n + 1) - 1) / 2)))) / 2))
  \<le> nat (floor (((sqrt (8 * n + 1) - 1) / 2) * ((1 + ((sqrt (8 * n + 1) - 1) / 2)) / 2)))"
  by (metis div_le_mono divide2_div2' le_mult_nat_floor times_divide_eq_right triangle_invert_real_typ triangle_invert_real_typ')

lemma triangle_tsqrt_le: "triangle (tsqrt n) \<le> n"
  unfolding triangle_tsqrt_real_pre
  using triangle_tsqrt_le_real triangle_tsqrt_le_real_bound
  by (meson le_trans)

lemma tsqrt_unique:
  assumes "triangle m \<le> n" "n < triangle (Suc m)"
  shows "tsqrt n = m"
  using assms triangle_tsqrt_le tsqrt_correct
  by (metis le_SucE le_antisym mono_tsqrt' nat_less_le)

lemma tsqrt_tsqrt: "tsqrt_alt n = tsqrt n"
  by (metis Suc_tsqrt_alt_triangle_gt tsqrt_unique tsqrt_alt_triangle_le)

lemma tsqrt_Suc:
  "tsqrt (Suc n) = (if \<exists>m. Suc n = triangle m then Suc (tsqrt n) else tsqrt n)"
  using tsqrt_alt_Suc tsqrt_tsqrt by force

end