
subsection \<open>Timing\<close>

theory Primitives_IMP_Minus_Time
  imports Primitives_IMP_Minus "Poly_Reductions_Lib.Landau_Auxiliaries" "Poly_Reductions_Lib.Polynomial_Growth_Functions"
    "HOL-Library.Rewrite"
begin

text \<open>In this file we show that the runtime of the programs in Primitives_IMP_Minus is polynomial
  in the input size\<close>

subsubsection \<open>Multiplication\<close>

(* Accumulator in one step, not sure if necessary *)
lemma mul_imp_time_acc': "mul_imp_time t s = mul_imp_time 0 s + t"
  by (induction t) (use mul_imp_time_acc in auto)
(* Experiment, this should stop endless unfolding problems *)
corollary mul_imp_time_acc'': "NO_MATCH 0 t \<Longrightarrow> mul_imp_time t s = mul_imp_time 0 s + t"
  using mul_imp_time_acc'.

(* Experiments with simp rules, delete: *)
lemma no_match_simp: "NO_MATCH p v \<Longrightarrow> P \<Longrightarrow> P"
  by simp
lemmas mul_imp_time_simp = no_match_simp[OF _ mul_imp_time.simps, where p="mul_imp_time t (mul_state_upd s)" for s t]

(* Proving was getting ugly, so drop the accumulator *)
fun mul_imp_time' :: "nat \<Rightarrow> nat" where
  "mul_imp_time' 0 = 2"
| "mul_imp_time' n = mul_imp_time' (n div 2) + 10"

(* Equivalence of simpler version  *)
lemma mul_imp_time_mul_imp_time': "mul_imp_time t s = mul_imp_time' (mul_b s) + t"
proof (induction "mul_b s" arbitrary: s t rule: mul_imp_time'.induct)
  case 1
  then show ?case
    by (subst mul_imp_time.simps) auto
next
  case 2
  show ?case
    by (subst mul_imp_time.simps) (auto simp add: 2(1) 2(2)[symmetric] mul_state_upd_def mul_imp_time_acc)
qed

(* Extract non recursive version *)
lemma mul_imp_time'_non_rec: "mul_imp_time' b = (if b = 0 then 0 else 10 * (1 + floor_log b)) + 2"
proof (induction b rule: mul_imp_time'.induct)
  case 1
  then show ?case
    by simp
next
  case (2 b)
  then show ?case
  proof(cases b)
    case 0
    then show ?thesis
      using 2 by auto
  next
    case (Suc n)
    then show ?thesis
      using 2 by (auto simp add: log_rec)
  qed
qed

(* Move back to mul_imp_time *)
lemma mul_imp_time_non_rec: "mul_imp_time t s = (if mul_b s = 0 then 0 else 10 * (1 + floor_log (mul_b s))) + 2 + t"
proof-
  have "mul_imp_time t s = mul_imp_time' (mul_b s) + t"
    by (simp add: mul_imp_time_mul_imp_time')
  also have "\<dots> = (if (mul_b s) = 0 then 0 else 10 * (1 + floor_log (mul_b s))) + 2 + t"
    by (simp add: mul_imp_time'_non_rec)
  finally show ?thesis
    by simp
qed

(* Hide details maybe?*)
lemma mul_imp_time_non_rec_bound: "mul_imp_time t s \<le> 10 * floor_log (mul_b s) + 12 + t"
  using mul_imp_time_non_rec by auto

subsubsection \<open>Squaring\<close>

definition square_imp_time' :: "nat \<Rightarrow> nat" where
  "square_imp_time' a = 8 + mul_imp_time' a"

lemma square_imp_time_square_imp_time': "square_imp_time t s = square_imp_time' (square_x s) + t"
  by (subst square_imp_time.simps) (simp add: square_imp_time'_def mul_imp_time_mul_imp_time')

lemma square_imp_time'_non_rec: "square_imp_time' a = (if a = 0 then 0 else 10 * (1 + floor_log a)) + 10"
  by (simp del: mul_imp_time'.simps add: mul_imp_time'_non_rec square_imp_time'_def)

lemma square_imp_time'_non_rec_bound: "square_imp_time' a \<le> 20 + 10 * (floor_log a)"
proof-
  have "22 + 10 * floor_log (Suc a) \<le> 22 + 10 * Suc (floor_log a)"
    using dlog_Suc_bound by (meson add_left_mono mult_le_mono2)
  thus ?thesis
    by (subst square_imp_time'_non_rec) simp
qed

(* This allows bounding *)
lemma mono_mul_imp_time'_pre: "m \<le> n \<Longrightarrow> mul_imp_time' m \<le> mul_imp_time' n"
  by (auto simp add: floor_log_le_iff mul_imp_time'_non_rec)
corollary mono_mul_imp_time': "mono mul_imp_time'"
  using mono_mul_imp_time'_pre ..

lemma mono_square_imp_time'_pre: "m \<le> n \<Longrightarrow> square_imp_time' m \<le> square_imp_time' n"
  by (auto simp add: mono_mul_imp_time'_pre square_imp_time'_def)
corollary mono_square_imp_time': "mono square_imp_time'"
  using mono_square_imp_time'_pre ..


subsubsection \<open>Triangle\<close>

(* Probably useless accumulator laws *)
lemma triangle_imp_time_acc': "triangle_imp_time t s = triangle_imp_time 0 s + t"
  by (induction t) (use triangle_imp_time_acc in auto)
(* This should prevent endless unfolding *)
lemma triangle_imp_time_acc'': "NO_MATCH 0 t \<Longrightarrow> triangle_imp_time t s = triangle_imp_time 0 s + t"
  using triangle_imp_time_acc' .

definition triangle_imp_time' :: "nat \<Rightarrow> nat" where
  "triangle_imp_time' a = 10 + mul_imp_time' (a+1)"

lemma triangle_imp_time_triangle_imp_time': "triangle_imp_time t s = triangle_imp_time' (triangle_a s) + t"
  by (subst triangle_imp_time.simps) (simp add: triangle_imp_time'_def mul_imp_time_mul_imp_time')

(* Problem: Suc a in argument *)
lemma triangle_imp_time'_non_rec: "triangle_imp_time' a = 22 + 10 * floor_log (Suc a)"
  by (simp del: mul_imp_time'.simps add: mul_imp_time'_non_rec triangle_imp_time'_def)

lemma triangle_imp_time'_non_rec_bound: "triangle_imp_time' a \<le> 32 + 10 * (floor_log a)"
proof-
  have "22 + 10 * floor_log (Suc a) \<le> 22 + 10 * Suc (floor_log a)"
    using dlog_Suc_bound by (meson add_left_mono mult_le_mono2)
  thus ?thesis
    by (subst triangle_imp_time'_non_rec) simp
qed

subsubsection \<open>Encoding pairs\<close>

definition prod_encode_imp_time' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "prod_encode_imp_time' a b = 8 + triangle_imp_time' (a+b)"

lemma prod_encode_imp_time_prod_encode_imp_time': "prod_encode_imp_time t s
  = prod_encode_imp_time' (prod_encode_a s) (prod_encode_b s) + t"
  by (subst prod_encode_imp_time.simps) (simp add: prod_encode_imp_time'_def triangle_imp_time_triangle_imp_time')

lemma dlog_add_bound': "a+b > 0 \<Longrightarrow> floor_log (a+b) \<le> floor_log a + floor_log b + 1"
  apply (induction "a+b" arbitrary: a b rule: log_induct)
   apply auto
  using log_Suc_zero apply auto[1]
  by (metis floor_log_le_iff add_Suc_right add_Suc_shift add_cancel_right_left add_le_mono1
      log_twice mult_2 nat_add_left_cancel_le nat_le_linear trans_le_add1 trans_le_add2)

lemma dlog_add_bound: "floor_log (a+b) \<le> Suc (floor_log a + floor_log b)"
  by (metis Suc_eq_plus1 dlog_add_bound' le_SucI le_add2 not_gr0 trans_less_add2)

(* The question is whether I bound this in each step or at the end *)
lemma prod_encode_imp_time'_non_rec: "prod_encode_imp_time' a b = 30 + 10 * floor_log (Suc (a + b))"
  by (auto simp add: prod_encode_imp_time'_def triangle_imp_time'_non_rec)

(* Bound every step, should scale better in the long run *)
lemma prod_encode_imp_time'_non_rec_bound:
  "prod_encode_imp_time' a b \<le> 50 + 10 * floor_log a + 10 * floor_log b"
proof-
  have "prod_encode_imp_time' a b = 8 + triangle_imp_time' (a+b)"
    unfolding prod_encode_imp_time'_def ..
  also have "\<dots> \<le> 40 + 10 * (floor_log (a+b))"
    using triangle_imp_time'_non_rec_bound by simp
  also have "\<dots> \<le> 40 + 10 * Suc (floor_log a + floor_log b)"
    using dlog_add_bound by (meson add_left_mono mult_le_mono2)
  also have "\<dots> = 50 + 10 * floor_log a + 10 * floor_log b"
    by simp
  finally show ?thesis .
qed
subsubsection \<open>Square root\<close>

function dsqrt'_imp_time' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "dsqrt'_imp_time' y L R = (if Suc L < R
    then let M = (L+R) div 2 in 23 + square_imp_time' M + (if M*M \<le> y then dsqrt'_imp_time' y M R else dsqrt'_imp_time' y L M)
    else 7)"
  by auto
termination by (relation "Wellfounded.measure (\<lambda>(y,L,R). R - L)") auto

declare dsqrt'_imp_time'.simps[simp del]

lemma dsqrt'_imp_time_dsqrt'_imp_time':
  "dsqrt'_imp_time t s = dsqrt'_imp_time' (dsqrt'_state_y s) (dsqrt'_state_L s) (dsqrt'_state_R s) + t"
proof (induction "dsqrt'_state_y s" "dsqrt'_state_L s" "dsqrt'_state_R s" arbitrary: s t rule: dsqrt'_imp_time'.induct)
  case 1
  then show ?case
    apply (subst dsqrt'_imp_time.simps)
    apply (subst dsqrt'_imp_time'.simps)
    by (auto simp add: "1" dsqrt'_imp_state_upd_def dsqrt'_imp_time_acc square_imp_time_square_imp_time'
      power2_eq_square square_imp_correct Let_def)
qed

lemma middle_alternative: "Suc L < R \<Longrightarrow> (L + R) div 2 = (R - L) div 2 + L"
  by (induction L arbitrary: R) auto

lemma "1 + (L::real) < R \<Longrightarrow> R - ((R - L) div 2 + L) = (R - L) div 2"
  by (smt (z3) field_sum_of_halves)

(* Basically: Add a ceiling function. *)
lemma distance: "Suc L < R \<Longrightarrow> R - ((R - L) div 2 + L) = (R - L) div 2 + (if even (L+R) then 0 else 1)"
  apply (induction L arbitrary: R)
   apply (auto simp add: algebra_simps)[]
  using left_add_twice apply presburger
  apply auto
     apply (smt (verit, best) Suc_diff_1 Suc_less_eq add.right_neutral diff_diff_left even_Suc odd_pos plus_1_eq_Suc)
    apply (smt (verit, ccfv_SIG) Nat.add_0_right Suc_lessE diff_Suc_Suc even_Suc)
   apply (smt (verit, del_insts) One_nat_def Suc_diff_Suc Suc_lessD add.commute add_Suc_right
      even_diff_nat odd_Suc_div_two odd_add odd_one plus_1_eq_Suc)
  by (smt (verit, best) One_nat_def Suc_eq_plus1 Suc_less_eq diff_diff_left even_Suc odd_Suc_minus_one plus_1_eq_Suc)


(* Quick'n'dirty version of the textbook proof, first for powers of two then general *)
lemma dsqrt'_imp_time'_log_bound_2pow: "L < R
  \<Longrightarrow> \<exists>k. R-L = 2^k
  \<Longrightarrow> dsqrt'_imp_time' y L R \<le> (23 + square_imp_time' R) * (floor_log (R - L)) + 7"
proof(induction  y L R rule: dsqrt'_imp_time'.induct)
  case (1 y L R)
  then show ?case
  proof(cases "Suc L < R")
    case rec: True

    from rec have "(R - L) > 1"
      by simp
    hence size: "(R - L) div 2 > 0"
      by simp

    from "1.prems"(2) \<open>1 < R - L\<close> have "even (L+R)"
      by (metis One_nat_def add.commute even_diff_nat even_numeral even_power less_nat_zero_code
          nat_diff_split nat_neq_iff nat_power_eq_Suc_0_iff)
    hence "even (R - L)"
      by simp
    with \<open>even (L + R)\<close> "1.prems"(2) have pow: "\<exists>k . R - (L + R) div 2 = 2^k"
      by (smt (verit, del_insts) Suc_leI  cancel_comm_monoid_add_class.diff_cancel distance
          even_power le_add_diff_inverse local.rec log_exp log_exp2_le middle_alternative
          power_Suc0_right power_diff_power_eq size zero_neq_numeral)
    from \<open>even (L + R)\<close> distance rec have d: "R - (L + R) div 2 = (R - L) div 2"
      using middle_alternative by simp
    from \<open>even (L + R)\<close> distance rec have d': "(L + R) div 2 - L = (R - L) div 2"
      using middle_alternative by simp

    have mid_bound: "(L + R) div 2 < R"
      by (metis d size zero_less_diff)

    show ?thesis
    proof(cases "((L + R) div 2)^2 \<le> y")
      case True
      hence s: "dsqrt'_imp_time' y L R \<le> 23 + square_imp_time' R + (dsqrt'_imp_time' y ((L + R) div 2) R)"
        using mid_bound mono_square_imp_time'_pre by (subst dsqrt'_imp_time'.simps) (simp add: rec power2_eq_square Let_def)

      have I: "(dsqrt'_imp_time' y ((L + R) div 2) R) \<le> (23 + square_imp_time' R) * floor_log (R - ((L + R) div 2)) + 7"
        apply (subst "1.IH"(1))
        using "1.prems" rec True pow
        by (auto simp add: power2_eq_square)

      have "dsqrt'_imp_time' y L R \<le> 23 + square_imp_time' R + (dsqrt'_imp_time' y ((L + R) div 2) R)"
        using s .
      also have "\<dots> \<le> (23 + square_imp_time' R) * Suc (floor_log (R - ((L + R) div 2))) + 7"
        using I by auto

      finally show ?thesis
        apply (subst log_rec)
        using div_greater_zero_iff size apply blast
        by (simp add: d)
    next
      case False
      hence s: "dsqrt'_imp_time' y L R \<le> 23 + square_imp_time' R + (dsqrt'_imp_time' y L ((L + R) div 2))"
        using mid_bound mono_square_imp_time'_pre by (subst dsqrt'_imp_time'.simps) (simp add: rec power2_eq_square Let_def)

      have I: "(dsqrt'_imp_time' y L ((L + R) div 2)) \<le> (23 + square_imp_time' ((L + R) div 2)) * floor_log (((L + R) div 2) - L) + 7"
        apply (subst "1.IH"(2))
        using "1.prems" rec False pow
        by (auto simp add: power2_eq_square d d')
      hence I': "(dsqrt'_imp_time' y L ((L + R) div 2)) \<le> (23 + square_imp_time' R) * floor_log (((L + R) div 2) - L) + 7"
        using mid_bound mono_square_imp_time'_pre
        by (smt (verit, best) add.left_commute add_le_mono less_or_eq_imp_le mult_le_mono1 nat_add_left_cancel_le)
      have "dsqrt'_imp_time' y L R \<le> 23 + square_imp_time' R + (dsqrt'_imp_time' y L ((L + R) div 2))"
        using s .
      also have "\<dots> \<le> (23 + square_imp_time' R) * Suc (floor_log (((L + R) div 2)- L)) + 7"
        using I' by auto

      finally show ?thesis
        apply (subst log_rec)
        using div_greater_zero_iff size apply blast
        by (simp add: d d')
    qed
  next
    case False
    then show ?thesis
      using "1.prems" False
      by (metis add_leD2 dsqrt'_imp_time'.simps le_refl)
  qed
qed

(* The extra size from uneven splits is only dangerous near powers of two*)
lemma log_changes_2pow: "(\<And>k .Suc n \<noteq> 2^k) \<Longrightarrow> floor_log (Suc n) = floor_log n"
  by (metis Suc_lessD bot_nat_0.not_eq_extremum le_SucE log_Suc_zero log_eqI log_exp2_gt log_exp2_le log_zero zero_less_Suc)

(* The bigger half is a power of two, so problem should not cascade *)
lemma "k>1 \<Longrightarrow> Suc n = 2^k \<Longrightarrow> n = 2^(k-1) + 2^(k-1) - 1"
  apply (induction n) apply auto
  using log_Suc_zero apply auto[1]
  by (metis One_nat_def diff_add_inverse le_add_diff_inverse mult_2 nat_less_le plus_1_eq_Suc power_Suc)

lemma log_split_near_2pow: "Suc n = 2^k \<Longrightarrow> floor_log (Suc (2 * n)) = (floor_log (Suc n))"
  by (simp add: log_eqI)

lemma dsqrt'_imp_time'_log: "L < R \<Longrightarrow> dsqrt'_imp_time' y L R \<le> (23 + square_imp_time' R) * (Suc (floor_log (R - L))) + 7"
proof(induction "R-L" arbitrary: y L R rule: less_induct)
  case less
  then show ?case
  proof(cases "Suc L < R")
    case rec: True

    have mid_bound: "(L + R) div 2 < R"
      using local.rec by linarith

    then show ?thesis
    proof(cases "((L + R) div 2)^2 \<le> y")
      case True
      hence s: "dsqrt'_imp_time' y L R \<le> 23 + square_imp_time' R + (dsqrt'_imp_time' y ((L + R) div 2) R)"
        using mid_bound mono_square_imp_time'_pre by (subst dsqrt'_imp_time'.simps) (simp add: rec power2_eq_square Let_def)

      have I: "dsqrt'_imp_time' y ((L + R) div 2) R \<le> (23 + square_imp_time' R) * Suc (floor_log (R - ((L + R) div 2))) + 7"
        apply (rule less)
        using local.rec by linarith+

      consider (even_split) "(R - ((L + R) div 2)) = (R - L) div 2"
        | (odd_split) "(R - ((L + R) div 2)) = Suc ((R - L) div 2)"
        by linarith
      then show ?thesis
      proof cases
        (* No problem here *)
        case even_split
        from rec have "floor_log (R - L) > 0"
          by (subst log_rec) simp_all
        with even_split show ?thesis
          using I s by auto
      next
        case odd_split
        (* For an odd split we need an interval of length \<ge>3 *)
        with rec have odd: "odd (R - L)"
          using distance middle_alternative by fastforce
        with rec have size: "R - L > 2"
          by (auto simp add: less_diff_conv intro!: Suc_lessI)

        have recomb: "R - L = Suc (2 * ((R - L) div 2))"
          by (metis Suc_eq_plus1 odd odd_two_times_div_two_succ)

        consider (power) k where "Suc ((R - L) div 2) = 2^k"
          | (unproblematic) "\<And>k. Suc ((R - L) div 2) \<noteq> 2^k"
          by blast
        then show ?thesis
        proof cases
          case power
          have "floor_log (Suc ((R - L) div 2)) = k"
            by (simp add: power)
          hence question: "floor_log (R - L) = k"
            apply (subst recomb)
            apply (subst log_split_near_2pow)
            using power apply assumption
            by simp

          have "dsqrt'_imp_time' y L R \<le> 23 + square_imp_time' R + (dsqrt'_imp_time' y ((L + R) div 2) R)"
            using s .
          also have "\<dots> \<le> 23 + square_imp_time' R + ((23 + square_imp_time' R) * Suc (floor_log (R - ((L + R) div 2))) + 7)"
            using I by auto
          also have "\<dots> \<le> (23 + square_imp_time' R) * Suc (Suc (floor_log (R - ((L + R) div 2)))) + 7"
            by simp

          have "23 + square_imp_time' R + (dsqrt'_imp_time' y ((L + R) div 2) R) \<le> (23 + square_imp_time' R) * Suc (floor_log (R - L)) + 7"
            by (simp add:  question) (metis \<open>floor_log (Suc ((R - L) div 2)) = k\<close> add.commute
                dsqrt'_imp_time'_log_bound_2pow mid_bound odd_split power)
          (* Basically works because we have an exact version for the 2^k case *)
          show ?thesis
            using \<open>23 + square_imp_time' R + dsqrt'_imp_time' y ((L + R) div 2) R \<le> (23 + square_imp_time' R) * Suc (floor_log (R - L)) + 7\<close> order.trans s by blast

        next
          case unproblematic
          hence "Suc ((R - L) div 2) \<noteq> 2^k" for k
            by (simp add: odd_split)
          hence irrel: "floor_log (Suc ((R - L) div 2)) = floor_log ((R - L) div 2)"
            by (rule log_changes_2pow)
          show ?thesis
            using I odd_split size s irrel by (subst log_rec) auto
        qed
      qed
    next
      case False

      hence s: "dsqrt'_imp_time' y L R \<le> 23 + square_imp_time' R + (dsqrt'_imp_time' y L ((L + R) div 2))"
        using mid_bound mono_square_imp_time'_pre by (subst dsqrt'_imp_time'.simps) (simp add: rec power2_eq_square Let_def)

      have I: "(dsqrt'_imp_time' y L ((L + R) div 2)) \<le> (23 + square_imp_time' R) * Suc (floor_log (((L + R) div 2) - L)) + 7"
        by (smt (verit, best) False One_nat_def diff_add_inverse2 diff_is_0_eq div_2_gt_zero div_greater_zero_iff div_less
            dsqrt'_imp_time'.elims le_diff_conv le_trans less.hyps linorder_not_le local.rec mid_bound
            middle_alternative mult.commute mult_le_mono2 plus_1_eq_Suc power2_eq_square s)

      have split: "(((L + R) div 2) - L) = (R - L) div 2"
        by (simp add: local.rec middle_alternative)
      from rec have "floor_log (R - L) > 0"
        by (subst log_rec) simp_all
      with split show ?thesis
        using I s by auto
    qed
  next
    case False
    with less.prems have "Suc L = R"
      by simp
    then show ?thesis
      apply (subst dsqrt'_imp_time'.simps)
      using False by auto
  qed
qed

lemma dsqrt'_imp_time'_non_rec_bound:
  assumes "L < R" shows "dsqrt'_imp_time' y L R \<le> 60 + (63 * floor_log R + 10 * (floor_log R)^2)"
proof-
  have "dsqrt'_imp_time' y L R \<le> (23 + 20 + 10 * Suc (floor_log R)) * Suc (floor_log (R - L)) + 7"
    apply (rule le_trans[OF dsqrt'_imp_time'_log[OF assms, of y]])
    apply (rule add_le_mono1)
    apply (rule mult_le_mono1)
    using square_imp_time'_non_rec_bound[of R] by simp
  also have "\<dots> = (43 + 10 * Suc (floor_log R)) * Suc (floor_log (R - L)) + 7"
    by simp
  also have "\<dots> \<le> (43 + 10 * Suc (floor_log R)) * Suc (floor_log R) + 7"
    by (simp add: floor_log_le_iff)
  finally show ?thesis
    by (auto simp add: power2_eq_square algebra_simps)
qed

lemma "dsqrt'_state_L s < dsqrt'_state_R s \<Longrightarrow> dsqrt'_imp_time t s \<le> t +
  60 + (63 * floor_log (dsqrt'_state_R s) + 10 * (floor_log (dsqrt'_state_R s))^2)"
  by (simp add: dsqrt'_imp_time'_non_rec_bound dsqrt'_imp_time_dsqrt'_imp_time')

fun dsqrt_imp_time' :: "nat \<Rightarrow> nat" where
  "dsqrt_imp_time' y = 8 + dsqrt'_imp_time' y 0 (Suc y)"

lemma dsqrt_imp_time_dsqrt_imp_time': "dsqrt_imp_time t s = t + dsqrt_imp_time' (dsqrt_state_y s)"
  by (subst dsqrt_imp_time.simps) (auto simp add: dsqrt_imp_time_acc_2 dsqrt'_imp_time_dsqrt'_imp_time')

lemma dsqrt_imp_time'_non_rec_bound: "dsqrt_imp_time' y \<le> 141 + (83 * floor_log y + 10 * (floor_log y)\<^sup>2)"
proof-
  have "dsqrt_imp_time' y \<le> 68 + (63 * floor_log (Suc y) + 10 * (floor_log (Suc y))^2)"
    by (auto simp add: dsqrt'_imp_time'_non_rec_bound)
  also have "\<dots> \<le> 131 + (63 * floor_log y + 10 * (floor_log (Suc y))^2)"
    by simp (metis dlog_Suc_bound le_refl mult_Suc_right mult_le_mono)
  also have "\<dots> \<le> 131 + (63 * floor_log y + 10 * (Suc (floor_log y))^2)"
    by (simp add: dlog_Suc_bound)
  also have "\<dots> = 131 + (63 * floor_log y + 10 * (1 + 2 * floor_log y + (floor_log y)^2))"
    by (smt (verit, del_insts) Suc_eq_plus1_left add.assoc add.commute mult.assoc mult_1 power2_sum power_one)
  also have "\<dots> \<le> 141 + (83 * floor_log y + 10 * (floor_log y)^2)"
    by simp
  finally show ?thesis .
qed

text \<open>Triangular root\<close>

fun tsqrt_imp_time' :: "nat \<Rightarrow> nat" where
  "tsqrt_imp_time' y = 16 + mul_imp_time' 8 + dsqrt_imp_time' (8*y+1)"

lemma tsqrt_imp_time_tsqrt_imp_time': "tsqrt_imp_time t s = t + tsqrt_imp_time' (tsqrt_state_y s)"
  by (subst tsqrt_imp_time.simps) (auto simp add: tsqrt_imp_time_acc_2 dsqrt_imp_time_dsqrt_imp_time'
      mul_imp_time_mul_imp_time' mul_imp_correct Let_def mult.commute)

lemma tsqrt_imp_time'_non_rec_bound: "tsqrt_imp_time' y \<le> 691 + (163 * floor_log y + 10 * (floor_log y)\<^sup>2)"
proof-
  have "tsqrt_imp_time' y = 58 + dsqrt_imp_time' (8*y+1)"
    by code_simp
  also have "\<dots> \<le> 58 + (141 + (83 * floor_log (8*y+1) + 10 * (floor_log (8*y+1))\<^sup>2))"
    using dsqrt_imp_time'_non_rec_bound by auto
  also have "\<dots> \<le> 282 + (83 * floor_log (8*y) + 10 * (floor_log (8*y+1))\<^sup>2)"
    by simp (metis dlog_Suc_bound le_refl mult_Suc_right mult_le_mono)
  also have "\<dots> \<le> 282 + (83 * (3 + floor_log y) + 10 * (floor_log (8*y+1))\<^sup>2)"
  proof- (* \<le> because of y=0 case*)
    have s: "8*y = (2*(2*(2*y)))" by simp
    have "floor_log (8*y) = 3 + floor_log y" if "y>0"
      apply (subst s)
      using that apply (subst log_twice, simp)+
      by presburger
    thus ?thesis
      by force
  qed
  also have "\<dots> = 531 + (83 * floor_log y + 10 * (floor_log (8*y+1))\<^sup>2)"
    by simp
  also have "\<dots> \<le> 531 + (83 * floor_log y + 10 * (1 + floor_log (8*y))\<^sup>2)"
    by (simp add: dlog_Suc_bound)
  also have "\<dots> \<le> 531 + (83 * floor_log y + 10 * (4 + floor_log y)\<^sup>2)"
  proof-
    have s: "8*y = (2*(2*(2*y)))" by simp
    have "floor_log (8*y) = 3 + floor_log y" if "y>0"
      apply (subst s)
      using that apply (subst log_twice, simp)+
      by presburger
    thus ?thesis
      by force
  qed
  also have "\<dots> = 531 + (83 * floor_log y + 10 * (floor_log y)^2 + 80 * floor_log y + 160)"
    by (auto simp add: power2_eq_square algebra_simps)
  also have "\<dots> = 691 + (163 * floor_log y + 10 * (floor_log y)^2)"
    by simp
  finally show ?thesis .
qed


fun fst'_imp_time' :: "nat \<Rightarrow> nat" where
  "fst'_imp_time' p = 10 + tsqrt_imp_time' p + triangle_imp_time' (tsqrt p)"

lemma fst'_imp_time_fst'_imp_time': "fst'_imp_time t s = t + fst'_imp_time' (fst'_state_p s)"
  by (subst fst'_imp_time.simps) (auto simp add: fst'_imp_time_acc_2 tsqrt_imp_time_tsqrt_imp_time'
      triangle_imp_time_triangle_imp_time' tsqrt_imp_correct Let_def mult.commute)

(* MOVE *)
lemma tsqrt_le: "tsqrt p \<le> p"
  using triangle_nat_le_imp_le triangle_tsqrt_le by blast

lemma fst'_imp_time'_non_rec_bound: "fst'_imp_time' p \<le> 733 + 173 * floor_log p + 10 * (floor_log p)\<^sup>2"
proof-
  have "fst'_imp_time' p = 10 + tsqrt_imp_time' p + triangle_imp_time' (tsqrt p)"
    by simp
  also have "\<dots> \<le> 10 + 691 + (163 * floor_log p + 10 * (floor_log p)\<^sup>2) + triangle_imp_time' (tsqrt p)"
    using tsqrt_imp_time'_non_rec_bound by simp
  also have "\<dots> \<le> 10 + 691 + (163 * floor_log p + 10 * (floor_log p)\<^sup>2) + 32 + 10 * (floor_log (tsqrt p))"
    using triangle_imp_time'_non_rec_bound by simp
  also have "\<dots> \<le> 10 + 691 + (163 * floor_log p + 10 * (floor_log p)\<^sup>2) + 32 + 10 * (floor_log p)"
    using tsqrt_le by (simp add: floor_log_le_iff)
  also have "\<dots> \<le> 733 + 173 * floor_log p + 10 * (floor_log p)\<^sup>2"
    by simp
  finally show ?thesis .
qed

fun snd'_imp_time' :: "nat \<Rightarrow> nat" where
  "snd'_imp_time' p = 8 + tsqrt_imp_time' p + fst'_imp_time' p"

lemma snd'_imp_time_snd'_imp_time': "snd'_imp_time t s = t + snd'_imp_time' (snd'_state_p s)"
  by (subst snd'_imp_time.simps) (auto simp add: snd'_imp_time_acc_2 tsqrt_imp_time_tsqrt_imp_time'
      fst'_imp_time_fst'_imp_time' Let_def)

lemma snd'_imp_time'_non_rec_bound: "snd'_imp_time' p \<le> 1432 + 336 * floor_log p + 20 * (floor_log p)\<^sup>2"
proof-
  have "snd'_imp_time' p = 8 + tsqrt_imp_time' p + fst'_imp_time' p"
    by simp
  also have "\<dots> \<le> 8 + 691 + (163 * floor_log p + 10 * (floor_log p)\<^sup>2) + fst'_imp_time' p"
    using tsqrt_imp_time'_non_rec_bound by (metis (no_types, lifting) add_mono eq_imp_le group_cancel.add1)
  also have "\<dots> \<le> 8 + 691 + (163 * floor_log p + 10 * (floor_log p)\<^sup>2) + 733 + 173 * floor_log p + 10 * (floor_log p)\<^sup>2"
    using fst'_imp_time'_non_rec_bound by (metis (mono_tags, lifting) add.assoc nat_add_left_cancel_le)
  also have "\<dots> \<le> 1432 + 336 * floor_log p + 20 * (floor_log p)\<^sup>2"
    by auto
  finally show ?thesis .
qed


fun prod_decode_imp_time' :: "nat \<Rightarrow> nat" where
  "prod_decode_imp_time' p = 8 + fst'_imp_time' p + snd'_imp_time' p"

lemma prod_decode_imp_time_prod_decode_imp_time': "prod_decode_imp_time t s = t + prod_decode_imp_time' (prod_decode_state_p s)"
  by (subst prod_decode_imp_time.simps) (auto simp add: prod_decode_imp_time_acc_2 tsqrt_imp_time_tsqrt_imp_time'
      fst'_imp_time_fst'_imp_time' snd'_imp_time_snd'_imp_time' Let_def)

lemma prod_decode'_imp_time'_non_rec_bound: "prod_decode_imp_time' p \<le> 2173 + 509 * floor_log p + 30 * (floor_log p)\<^sup>2"
proof-
  have "prod_decode_imp_time' p = 8 + fst'_imp_time' p + snd'_imp_time' p"
    by simp
  also have "\<dots> \<le> 8 + 733 + 173 * floor_log p + 10 * (floor_log p)\<^sup>2 + snd'_imp_time' p"
    using fst'_imp_time'_non_rec_bound by (metis (no_types, lifting) add_mono eq_imp_le group_cancel.add1)
  also have "\<dots> \<le> 8 + 733 + 173 * floor_log p + 10 * (floor_log p)\<^sup>2 + 1432 + 336 * floor_log p + 20 * (floor_log p)\<^sup>2"
    using snd'_imp_time'_non_rec_bound by (metis (no_types, lifting) add_mono eq_imp_le group_cancel.add1)
  also have "\<dots> \<le> 2173 + 509 * floor_log p + 30 * (floor_log p)\<^sup>2"
    by auto
  finally show ?thesis .
qed

fun hd_imp_time' :: "nat \<Rightarrow> nat" where
  "hd_imp_time' l = 8 + prod_decode_imp_time' (l-1)"

lemma hd_imp_time_hd_imp_time': "hd_imp_time t s = t + hd_imp_time' (hd_xs s)"
  by (subst hd_imp_time.simps) (auto simp add: hd_imp_time_acc prod_decode_imp_time_prod_decode_imp_time'
      Let_def)

lemma hd_imp_time'_non_rec_bound: "hd_imp_time' l \<le> 2181 + 509 * floor_log l + 30 * (floor_log l)\<^sup>2"
proof-
  have "hd_imp_time' l \<le> 8 + 2173 + 509 * floor_log (l-1) + 30 * (floor_log (l-1))\<^sup>2"
    using prod_decode'_imp_time'_non_rec_bound by simp
  also have "\<dots> \<le> 2181 + 509 * floor_log (l-1) + 30 * (floor_log (l-1))\<^sup>2"
    by simp
  also have "\<dots> \<le> 2181 + 509 * floor_log l + 30 * (floor_log (l-1))\<^sup>2"
    by (simp add: floor_log_le_iff)
  also have "\<dots> \<le> 2181 + 509 * floor_log l + 30 * (floor_log l)\<^sup>2"
    by (simp add: floor_log_le_iff)
  finally show ?thesis .
qed


fun tl_imp_time' :: "nat \<Rightarrow> nat" where
  "tl_imp_time' l = 8 + prod_decode_imp_time' (l-1)"

lemma tl_imp_time_tl_imp_time': "tl_imp_time t s = t + tl_imp_time' (tl_xs s)"
  by (subst tl_imp_time.simps) (auto simp add: tl_imp_time_acc prod_decode_imp_time_prod_decode_imp_time'
      Let_def)

lemma tl_imp_time'_non_rec_bound: "tl_imp_time' l \<le> 2181 + 509 * floor_log l + 30 * (floor_log l)\<^sup>2"
proof-
  have "tl_imp_time' l \<le> 8 + 2173 + 509 * floor_log (l-1) + 30 * (floor_log (l-1))\<^sup>2"
    using prod_decode'_imp_time'_non_rec_bound by simp
  also have "\<dots> \<le> 2181 + 509 * floor_log (l-1) + 30 * (floor_log (l-1))\<^sup>2"
    by simp
  also have "\<dots> \<le> 2181 + 509 * floor_log l + 30 * (floor_log (l-1))\<^sup>2"
    by (simp add: floor_log_le_iff)
  also have "\<dots> \<le> 2181 + 509 * floor_log l + 30 * (floor_log l)\<^sup>2"
    by (simp add: floor_log_le_iff)
  finally show ?thesis .
qed

(*
function length_imp_time:: "nat \<Rightarrow> length_state\<Rightarrow> nat" where
  "length_imp_time t s =
  (if length_xs s \<noteq> 0 then \<comment> \<open>While xs \<noteq> 0\<close>
    (
      let
        t = t + 1;
        tl_xs' = (length_xs s);
        t = t+2;
        tl_ret' = 0;
        t = t+2;
        tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
        tl_state_ret = tl_imp tl_state;
        t = t + tl_imp_time 0 tl_state;
        length_xs' = tl_ret tl_state_ret;
        t = t + 2;
        length_ret' = length_ret s + 1;
        t = t + 2;
        next_iteration = length_imp_time t (length_state_upd s)
      in
        next_iteration
    )
  else
    (
      let
        t = t + 2;
        ret = t
      in
        ret
    )
  )*)

fun length_imp_time' :: "nat \<Rightarrow> nat" where
  "length_imp_time' 0 = 2"
| "length_imp_time' xs = 9 + tl_imp_time' xs + length_imp_time' (tl_nat xs)"


lemma length_imp_time_acc_3: "NO_MATCH 0 x \<Longrightarrow> (length_imp_time x s) = x + (length_imp_time 0 s)"
  using length_imp_time_acc_2.

lemma length_imp_time_length_imp_time': "length_imp_time t s = t + length_imp_time' (length_xs s)"
proof (induction "length_xs s" arbitrary: s t rule: length_imp_time'.induct)
  case 1
  then show ?case
    by (subst length_imp_time.simps) auto
next
  case 2
  hence s: "length_imp_time' (length_xs s)
    = 9 + tl_imp_time' (length_xs s) + length_imp_time' (tl_nat (length_xs s))"
  by (metis length_imp_time'.simps(2))
  show ?case
    apply (subst length_imp_time.simps)
    using 2(2)
    apply (simp add: s 2(1) Let_def length_imp_time_acc_3 tl_imp_time_tl_imp_time' length_state_upd_def tl_imp_correct)
    done
qed


lemma a: "6 < (n::nat) \<Longrightarrow> 1 + n * 8 \<le> (1 + n)\<^sup>2"
  apply (induction n)
  apply (auto simp add: field_simps power2_eq_square)
  by (metis add_less_mono1 eval_nat_numeral(3) mult_Suc_right nat_le_linear nat_mult_less_cancel_disj not_less_iff_gr_or_eq order_le_less_trans)

lemma a': "6 < (n::real) \<Longrightarrow> 1 + n * 8 \<le> (1 + n)\<^sup>2"
  by (auto simp add: field_simps power2_eq_square)

lemma b': assumes "6 < n" shows "(sqrt (8 * n + 1) - 1) / 2 \<le> n / 2"
proof-
  have "sqrt (8 * n + 1) \<le> 1 + n"
    apply (rule real_le_lsqrt)
    using assms by (auto simp add: a' mult.commute add.commute)
  hence "(sqrt (8 * n + 1) - 1) \<le> n" by simp
  thus ?thesis by simp
qed


lemma b: assumes "6 < n" shows "(floor_sqrt (8 * n + 1) - 1) div 2 \<le> n div 2"
proof-
  have 1: "(floor_sqrt (8 * n + 1) - 1) div 2 \<le> nat (floor ((sqrt (8 * n + 1) - 1) / 2))"
    using tsqrt_def tsqrt_real by presburger
  have assms': "6 < real n"
    using assms by simp
  show ?thesis
    apply (rule le_trans)
    using 1 apply simp
    using b'[OF assms']
    by (metis add.commute divide2_div2 floor_mono nat_mono)
qed

(* This should mean it shrinks fast enough.
  Condition is annoying, as it might result in me having to do the first few cases explicitly
  There is a reason why Landau symbols where invented...
*)
lemma tsqrt_div2_bound: "n > 6 \<Longrightarrow> tsqrt n \<le> n div 2"
  unfolding tsqrt_def using b .

lemma snd'_nat_div2_bound: "n > 6 \<Longrightarrow> snd'_nat n \<le> n div 2"
  unfolding snd'_nat_def using tsqrt_div2_bound by force
lemma snd_nat_div2_bound: "n > 6 \<Longrightarrow> snd_nat n \<le> n div 2"
  using snd'_nat_div2_bound snd_nat_snd'_nat by presburger

(* This proof shows that I migh need monotonicity lemmas for my operartions.. *)
lemma tl_nat_div2_bound: "n > 6 \<Longrightarrow> tl_nat n \<le> n div 2"
  unfolding tl_nat_def using snd_nat_div2_bound
  by (metis diff_le_self le_trans mono_tsqrt' snd'_nat_def snd_nat_snd'_nat tsqrt_div2_bound)

lemma triangle_imp_time'_mono_pre: "m \<le> n \<Longrightarrow> triangle_imp_time' m \<le> triangle_imp_time' n"
  using mono_mul_imp_time'_pre by (simp add: triangle_imp_time'_def)

(*
  It is easier now to bound before solving the recursion, problem is that I would need to prove
  something like monotonicity for tl_imp_time' which requires a bunch of monotonicity
*)
fun length_imp_time'' :: "nat \<Rightarrow> nat" where
  "length_imp_time'' 0 = 2"
| "length_imp_time'' xs = 9 + (2181 + 509 * floor_log xs + 30 * (floor_log xs)\<^sup>2) + length_imp_time'' (tl_nat xs)"

lemma length_imp_time'_length_imp_time'': "length_imp_time' xs \<le> length_imp_time'' xs"
  apply (induction xs rule: length_imp_time''.induct)
   apply simp
  using tl_imp_time'_non_rec_bound
  by (metis add.commute add_le_mono add_le_mono1 length_imp_time''.simps(2) length_imp_time'.simps(2))


lemma length_imp_time''_non_rec_bound': "length_imp_time'' xs
  \<le> 2 + Suc (floor_log xs) * (9 + (2181 + 509 * floor_log xs + 30 * (floor_log xs)\<^sup>2))"
proof (induction xs rule: length_imp_time''.induct)
  case 1
  then show ?case by simp
next
  case (2 v)
  show ?case
  proof(cases "Suc v>6")
    case True
    hence "tl_nat (Suc v) \<le> Suc v div 2"
      using tl_nat_div2_bound by blast
    hence "floor_log (tl_nat (Suc v)) \<le> floor_log (Suc v div 2)"
      by (rule log_le_iff)
    with "2.IH" have "length_imp_time'' (tl_nat (Suc v)) \<le> 2 + Suc (floor_log (Suc v div 2)) *
      (9 + (2181 + 509 * floor_log (tl_nat (Suc v)) + 30 * (floor_log (tl_nat (Suc v)))\<^sup>2))"
      by (smt (verit, best) Suc_le_mono Suc_mult_le_cancel1 add_le_cancel_left add_le_mono1 le_trans less_Suc_eq_le less_numeral_extra(3)
          mult_le_mono not_less_less_Suc_eq numeral_2_eq_2)
    also have "\<dots> \<le> 2 + Suc (floor_log (Suc v div 2)) *
      (9 + (2181 + 509 * floor_log (Suc v div 2) + 30 * (floor_log (Suc v div 2))\<^sup>2))"
      by (metis \<open>floor_log (tl_nat (Suc v)) \<le> floor_log (Suc v div 2)\<close> add_left_mono
          add_mono_thms_linordered_semiring(1) nat_mult_le_cancel_disj power2_nat_le_eq_le)
    also have "\<dots> \<le> 2 + (floor_log (Suc v)) *
      (9 + (2181 + 509 * floor_log (Suc v div 2) + 30 * (floor_log (Suc v div 2))\<^sup>2))"
      by (metis floor_log.simps True gr_implies_not0 le_eq_less_or_eq less_Suc_eq numeral_2_eq_2 zero_neq_numeral)
    finally show ?thesis
      apply (subst length_imp_time''.simps) apply (auto simp add: algebra_simps simp del: tl_imp_time'.simps)
      by (smt (verit, ccfv_SIG) Suc_le_mono diff_le_self le_trans mult_le_mono2 nat_add_left_cancel_le power2_nat_le_eq_le)
  next
    case False
    from this consider "v = 0" | "v = 1" | "v = 2" | "v = 3" | "v = 4" | "v = 5" by fastforce
    then show ?thesis apply (cases)
      apply (auto simp add: tl_nat_def snd_nat_snd'_nat snd'_nat_def tsqrt_def fst'_nat_def)
           apply (all code_simp)
      done
  qed
qed

corollary length_imp_time'_non_rec_bound': "length_imp_time' xs
  \<le> 2192 + 2699 * floor_log xs + 539 * (floor_log xs)\<^sup>2 + 30 * (floor_log xs)^3"
  apply (rule le_trans[OF length_imp_time'_length_imp_time'' ])
  using length_imp_time''_non_rec_bound' by (auto simp add: field_simps power2_eq_square power3_eq_cube)

fun cons_imp_time' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "cons_imp_time' h t = 8 + prod_encode_imp_time' h t"

lemma cons_imp_time_cons_imp_time': "cons_imp_time t s = t + cons_imp_time' (cons_h s) (cons_t s)"
  by (auto simp add: cons_imp_time.simps prod_encode_imp_time_prod_encode_imp_time')

lemma cons_imp_time'_non_rec_bound: "cons_imp_time' h t \<le> 58 + 10 * floor_log h + 10 * floor_log t"
  using prod_encode_imp_time'_non_rec_bound by (simp add: add.assoc)

fun append_imp_time' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "append_imp_time' _ 0 = 2"
| "append_imp_time' acc xs = 19 + hd_imp_time' xs + cons_imp_time' (hd_nat xs) acc + tl_imp_time' xs
    + append_imp_time' (cons (hd_nat xs) acc) (tl_nat xs)"

lemma O_square_subset_nat: "O((f::nat \<Rightarrow> nat)) \<subseteq> O(\<lambda>n . (f n)^2)"
  apply (rule landau_o.big_subsetI)
  apply (rule landau_o.big_mono)
  apply (rule eventuallyI)
  apply (auto simp add: power2_nat_le_imp_le)
  done


corollary "(\<exists>k . (\<lambda>n. real (f n)) \<in> O(\<lambda>n. real n ^ k)) \<longleftrightarrow> (\<exists>k . (\<lambda>n. real (f n)) \<in> o(\<lambda>n. real n ^ k))"
  using poly_def poly_iff_ex_smallo by presburger

(* The definition seperates the polynomial bit from the bit_length part, I did it combined so far. *)
lemma natfun_bigo_poly_log_iff:
  fixes f :: "nat \<Rightarrow> real"
  shows "f \<in> O(\<lambda>n. floor_log n ^ k) \<longleftrightarrow> (\<exists>c. \<forall>n>1. \<bar>f n\<bar> \<le> c * real (floor_log n ^ k))"
proof
  assume "\<exists>c. \<forall>n>1. \<bar>f n\<bar> \<le> c * real (floor_log n ^ k)"
  then obtain c where c: "\<forall>n>1. \<bar>f n\<bar> \<le> c * real (floor_log n ^ k)"
    by auto
  have "eventually (\<lambda>n. \<bar>f n\<bar> \<le> c * real (floor_log n ^ k)) at_top"
    using eventually_gt_at_top[of 1] by eventually_elim (use c in auto)
  thus "f \<in> O(\<lambda>n. floor_log n ^ k)"
    by (intro bigoI[of _ c]) (auto intro!: always_eventually)
next
  assume 1: "f \<in> O(\<lambda>n. floor_log n ^ k)"
  have 2: "real (floor_log n ^ k) \<noteq> 0" if "n \<ge> 2" for n :: nat using that
    by (metis bot_nat_0.not_eq_extremum log_rec of_nat_0_eq_iff power_not_zero zero_less_Suc)
  from natfun_bigoE[OF 1 2, of 2] obtain c where "\<forall>n\<ge>2. \<bar>f n\<bar> \<le> c * real (floor_log n ^ k)"
    by simp metis?
  thus "\<exists>c. \<forall>n>1. \<bar>f n\<bar> \<le> c * real (floor_log n ^ k)"
    apply (auto simp: Suc_le_eq)
    by (metis Suc_leI numeral_2_eq_2)
qed

term poly


definition poly_log :: "(nat \<Rightarrow> nat) \<Rightarrow> bool"
  where "poly_log f \<longleftrightarrow> (\<exists>k. (\<lambda>n. real (f n)) \<in> O(\<lambda>n. real (floor_log n ^ k)))"

lemma poly_log_iff_ex_smallo: "poly_log f \<longleftrightarrow> (\<exists>k. (\<lambda>n. real (f n)) \<in> o(\<lambda>n. real (floor_log n ^ k)))"
  unfolding poly_log_def
proof safe
  fix k assume "f \<in> O(\<lambda>n. real (floor_log n ^ k))"
  also have "(\<lambda>n. real (floor_log n ^ k)) \<in> o(\<lambda>n. real (floor_log n ^ (k + 1)))"
    by real_asymp
  finally have "f \<in> o(\<lambda>n. (floor_log n ^ (k + 1)))" .
  thus "\<exists>k. f \<in> o(\<lambda>n. floor_log n ^ k)" ..
qed (auto intro: landau_o.small_imp_big)

lemma poly_log_const [simp, intro]: "poly_log (\<lambda>_. c)"
  by (auto simp: poly_log_def intro!: exI[of _ 0])

lemma poly_log_cmult [intro]: "poly_log f \<Longrightarrow> poly_log (\<lambda>x. c * f x)"
  by (auto simp: poly_log_def)

thm real_asymp_nat_reify
thm real_asymp_reify_simps

lemma test: "(\<lambda>x. real (floor_log x) ^ k) \<in> O(\<lambda>x. real (floor_log x) ^ max k l)"
  apply (rule landau_o.big_mono[of])
  apply (rule eventually_at_top_linorderI[of 2])
  apply simp_all
  apply (rule power_increasing)
  apply simp_all
  by (metis One_nat_def Suc_leI log_rec real_of_nat_ge_one_iff zero_less_Suc)

lemma "norm (real c) = real c"
  by simp

lemma power_weaken_heavy: "a \<le> b \<Longrightarrow> n > 0 \<Longrightarrow> a \<le> (b::nat)^(n::nat)"
  by (metis One_nat_def Suc_leI bot_nat_0.extremum_uniqueI not_less_eq_eq order.trans power_increasing power_one_right zero_le_power)

lemma const_in_poly_log_internal': "(\<lambda>_. real c) \<in> O(\<lambda>n . real (floor_log n ^ (Suc k)))"
  apply (rule landau_o.big_mono[])
  apply (rule eventually_at_top_linorderI[of "2^c"])
  by (metis (mono_tags, opaque_lifting) floor_log_le_iff One_nat_def Suc_leI bot_nat_0.not_eq_extremum
      le_trans log_exp nat.simps(3) nle_le norm_of_nat of_nat_le_iff power_increasing power_one_right)

corollary const_in_poly_log_internal: "(\<lambda>_. real c) \<in> O(\<lambda>n . real (floor_log n ^ k))"
  apply (cases k)
   apply simp
  using const_in_poly_log_internal' by simp

lemma poly_log_add [intro]:
  assumes "poly_log f" "poly_log g"
  shows   "poly_log (\<lambda>x. f x + g x)"
proof -
  from assms obtain k l where kl: "f \<in> O(\<lambda>n. floor_log n ^ k)" "g \<in> O(\<lambda>n. floor_log n ^ l)"
    by (auto simp: poly_log_def)
  have "f \<in> O(\<lambda>n. floor_log n ^ max k l)" "g \<in> O(\<lambda>n. floor_log n ^ max k l)"
     apply (rule kl[THEN landau_o.big.trans], simp add: test)+
    by (metis max.commute test)
  from sum_in_bigo(1)[OF this] show ?thesis
    by (auto simp: poly_log_def)
qed

lemma poly_log_diff [intro]:
  assumes "poly_log f" "poly_log g"
  shows   "poly_log (\<lambda>x. f x - g x)"
proof -
  from assms obtain k l where kl: "f \<in> O(\<lambda>n. floor_log n ^ k)" "g \<in> O(\<lambda>n. floor_log n ^ l)"
    by (auto simp: poly_log_def)
  have "(\<lambda>x. real (f x - g x)) \<in> O(\<lambda>x. real (f x) - real (g x))"
    by (intro landau_o.big_mono) (auto intro!: always_eventually)
  also have "f \<in> O(\<lambda>n. floor_log n ^ max k l)" "g \<in> O(\<lambda>n. floor_log n ^ max k l)"
     apply (rule kl[THEN landau_o.big.trans], simp add: test)+
    by (metis max.commute test)
  from sum_in_bigo(2)[OF this] have "(\<lambda>x. real (f x) - real (g x)) \<in> O(\<lambda>x. real (floor_log x ^ max k l))" .
  finally show ?thesis
    by (auto simp: poly_log_def)
qed

lemma poly_log_mult [intro]:
  assumes "poly_log f" "poly_log g"
  shows   "poly_log (\<lambda>x. f x * g x)"
proof -
  from assms obtain k l where kl: "f \<in> O(\<lambda>n. floor_log n ^ k)" "g \<in> O(\<lambda>n. floor_log n ^ l)"
    by (auto simp: poly_log_def)
  from landau_o.big.mult[OF this] have "(\<lambda>n. f n * g n) \<in> O(\<lambda>n. floor_log n ^ (k + l))"
    by (simp add: power_add)
  thus ?thesis by (auto simp: poly_log_def)
qed

value "{..(n::nat)}"


lemma poly_log_make_mono_iff: "poly_log (make_mono f) \<longleftrightarrow> poly_log f"
proof safe
  fix f
  assume *: "poly_log (make_mono f)"
  have "f \<in> O(make_mono f)"
    by (rule landau_o.big_mono) (auto intro!: always_eventually)
  also from * obtain k where "make_mono f \<in> O(\<lambda>n. floor_log n ^ k)"
    by (auto simp: poly_log_def)
  finally show "poly_log f"
    by (auto simp: poly_log_def)
next
  assume "poly_log f"
  then obtain k where "f \<in> O(\<lambda>n. floor_log n ^ k)"
    by (auto simp: poly_log_def)
  then obtain c' :: real where c': "\<And>n. n > 1 \<Longrightarrow> f n \<le> c' * floor_log n ^ k"
    by (subst (asm) natfun_bigo_poly_log_iff) auto
  define c where "c = max c' 1"
  have "c > 0" by (simp add: c_def)
  have c: "f n \<le> c * floor_log n ^ k" if "n > 1" for n
  proof -
    have "f n \<le> c' * floor_log n ^ k"
      using c'[of n] that by blast
    also have "\<dots> \<le> c * floor_log n ^ k"
      by (intro mult_right_mono) (auto simp: c_def)
    finally show ?thesis by simp
  qed

  have "eventually (\<lambda>n. real (make_mono f n) \<le> real (f 0) + real (f 1) + c * real (floor_log n ^ k)) at_top"
    using eventually_gt_at_top[of 1]
  proof eventually_elim
    case (elim n)
    have "real (make_mono f n) = real (Max (f ` {..n}))"
      by (auto simp: make_mono_def)
    also have "{..n} = insert 0 {0<..n}"
      using elim by auto
    also have "\<dots> = insert 0 (insert 1 {1<..n})"
      using elim by auto
    also have "Max (f ` \<dots>) = max (f 0) (max (f 1) (Max (f ` {1<..n})))"
      using elim by (simp add: Max_insert)
    also have "real \<dots> = max (real (f 0)) (max (real (f 1)) (real (Max (f ` {1<..n}))))"
      by simp
    also have "real (Max (f ` {1<..n})) = Max ((real \<circ> f) ` {1<..n})"
      using elim by (subst mono_Max_commute) (auto simp: image_image incseq_def)
    also have "\<dots> \<le> c * real (floor_log n ^ k)"
      unfolding o_def
    proof (intro Max.boundedI; safe?)
      fix i assume i: "i \<in> {1<..n}"
      from i have "real (f i) \<le> c * real (floor_log i ^ k)"
        by (intro c) auto
      also have "\<dots> \<le> c * real (floor_log n ^ k)"
        using i \<open>c > 0\<close> by (auto intro!: mult_left_mono power_mono simp add: floor_log_le_iff)
      finally show "real (f i) \<le> c * real (floor_log n ^ k)" .
    qed (use elim in auto)
    hence "max (real (f 0)) (max (real (f 1)) (Max ((real \<circ> f) ` {1<..n}))) \<le> max (real (f 0)) (max (real (f 1)) (c * real (floor_log n ^ k)))"
      by (intro max.mono) auto
    also have "\<dots> \<le> real (f 0) + real (f 1) +  c * real (floor_log n ^ k)"
      using \<open>c > 0\<close> by simp
    finally show ?case .
  qed
  hence "make_mono f \<in> O(\<lambda>n. real (f 0) + real (f 1) + c * real (floor_log n ^ k))"
    using \<open>c > 0\<close> by (intro bigoI[of _ 1]) auto
  also have "(\<lambda>n. real (f 0) + real (f 1) + c * real (floor_log n ^ k)) \<in> O(\<lambda>n. real (floor_log n ^ k))"
    using \<open>c > 0\<close> apply (intro sum_in_bigo) apply (intro const_in_poly_log_internal)+ apply auto done
  finally show "poly_log (make_mono f)"
    by (auto simp: poly_log_def)
qed

lemma "n>0 \<Longrightarrow> (n::nat)^k \<le> n^(Suc k)"
  by simp

lemma "(\<lambda>_. 1) \<in> O(floor_log)"
  by real_asymp

find_theorems name: Landau name: trans
lemma step: "(\<lambda>_. 1) \<in> O(g) \<Longrightarrow> f \<in> O(\<lambda>n . g n ^ k) \<Longrightarrow> f \<in> O(\<lambda>n . g n ^ Suc k)"
  apply simp
  apply (rule Landau_Symbols.landau_o.big_mult_1')
  by simp_all
lemma step': "(\<lambda>_. 1) \<in> O(g) \<Longrightarrow> f \<in> o(\<lambda>n . g n ^ k) \<Longrightarrow> f \<in> o(\<lambda>n . g n ^ Suc k)"
  apply simp
  apply (rule Landau_Symbols.landau_o.small_mult_1')
  by simp_all

lemma step'_nat: "(\<lambda>_. 1) \<in> O(g) \<Longrightarrow> (f::nat \<Rightarrow> nat) \<in> o(\<lambda>n . (g::nat \<Rightarrow> nat) n ^ k) \<Longrightarrow> f \<in> o(\<lambda>n . g n ^ Suc k)"
  using step' by auto


lemma poly_log_compose [intro]:
  assumes "poly_log f" "poly_log g"
  shows   "poly_log (f \<circ> g)"
proof -
  from assms have "poly_log (make_mono f)"
    by (simp add: poly_log_make_mono_iff)
  then obtain k c where k: "\<And>n. n > 1 \<Longrightarrow> make_mono f n \<le> c * real (floor_log n ^ k)"
    apply (auto simp: poly_log_def natfun_bigo_poly_log_iff) (* ? *)
    by (smt (verit, del_insts) One_nat_def \<open>poly_log (make_mono f)\<close> natfun_bigo_poly_log_iff norm_of_nat of_nat_power poly_log_def)
  have "c \<ge> 0"
  proof-
    have "floor_log n ^ k \<ge> 0" for n by simp
    hence 1: "real (floor_log n ^ k) \<ge> 0" for n by simp
    have 2: "make_mono f n \<ge> 0" for n by simp
    show ?thesis
      using k[of 2] 1[of 2] 2[of 2] apply (auto simp add: field_simps)
      by (metis (mono_tags, opaque_lifting) Multiseries_Expansion.intyness_1 landau_o.R_trans log_exp mult.right_neutral nle_le of_nat_0_le_iff one_le_power power_le_one_iff power_one_right)
  qed

  from assms obtain l where l: "g \<in> o(\<lambda>n. floor_log n ^ l)"
    by (auto simp: poly_log_iff_ex_smallo)
  hence "g \<in> o(\<lambda>n. floor_log n ^ Suc l)"
    apply (intro step'_nat)
      apply real_asymp
    using l by simp
  from this obtain l where l: "g \<in> o(\<lambda>n. floor_log n ^ l)" "l > 0"
    by blast
  have "eventually (\<lambda>n. g n \<le> floor_log n ^ l) at_top"
    using landau_o.smallD[OF l(1), of 1] by auto
  hence "eventually (\<lambda>n. real (f (g n)) \<le> c * real (floor_log n ^ (k * l))) at_top"
    using eventually_gt_at_top[of 4]
  proof eventually_elim
    case (elim n)
    have "real (f (g n)) \<le> real (make_mono f (g n))"
      by auto
    also from elim(1) have "make_mono f (g n) \<le> make_mono f (floor_log n ^ l)"
      by (rule monoD[OF mono_make_mono])
    also have "\<dots> \<le> c * (floor_log (floor_log n ^ l)) ^ k"
    proof-
      have "floor_log n \<ge> floor_log 4"
        apply (rule log_le_iff)
        using \<open>n>4\<close> by simp
      hence "floor_log n > 1"
        by code_simp auto
      hence "1 < floor_log n ^ l"
        using \<open>n>4\<close> l(2) apply code_simp apply auto
        using less_trans_Suc power_gt_expt by presburger
      hence "real (make_mono f (floor_log n ^ l)) \<le> c * real (floor_log (floor_log n ^ l) ^ k)"
        using k[of "floor_log n ^ l"] by simp
      thus ?thesis
        by simp
    qed
    also have "\<dots> \<le> c * (floor_log n ^ l) ^ k"
    proof-
      have "(floor_log (floor_log n ^ l) ^ k) \<le> ((floor_log n ^ l) ^ k)"
        by (metis floor_log_le_iff le_neq_implies_less lessI less_or_eq_imp_le log_exp
            nat_power_eq_Suc_0_iff numeral_2_eq_2 power_gt_expt power_mono_iff zero_order(1))
      thus ?thesis
        by (meson \<open>0 \<le> c\<close> mult_left_mono of_nat_le_iff)
    qed
    also have "\<dots> = c * real (floor_log n ^ (k * l))"
      by (subst mult.commute) (simp add: power_mult)
    finally show ?case by simp
  qed
  hence "f \<circ> g \<in> O(\<lambda>n. floor_log n ^ (k * l))"
    by (intro bigoI[of _ c]) auto
  thus ?thesis by (auto simp: poly_log_def)
qed

lemma poly_log_dlog: "poly_log floor_log"
  unfolding poly_log_def
  apply (rule exI[of _ 1])
  by simp

lemma "(\<lambda>n . (floor_log::nat \<Rightarrow> nat) n + (floor_log n)^2) \<in> O(\<lambda>n . (floor_log n)^2)"
  by real_asymp

lemma append_imp_time_append_imp_time':
  "append_imp_time t s = t + append_imp_time' (append_state.append_acc s) (append_xs s)"
proof(induction "append_state.append_acc s" "append_xs s" arbitrary: t s rule: append_imp_time'.induct)
  case 1
  then show ?case
    by (simp add: append_imp_time.simps)
next
  case (2 v)
  hence s: "append_imp_time' (append_state.append_acc s) (append_xs s) =
     19 + hd_imp_time' (append_xs s) + cons_imp_time' (hd_nat (append_xs s)) (append_state.append_acc s) + tl_imp_time' (append_xs s)
    + append_imp_time' (cons (hd_nat (append_xs s)) (append_state.append_acc s)) (tl_nat (append_xs s))"
    by (metis append_imp_time'.simps(2))
  show ?case
    apply (subst append_imp_time.simps)
    apply (subst  append_imp_time_acc_2)
    using 2(2)
    by (simp add: s 2(1) Let_def append_imp_time_acc hd_imp_time_hd_imp_time' tl_imp_time_tl_imp_time'
        cons_imp_time_cons_imp_time' hd_imp_correct tl_imp_correct cons_imp_correct append_state_upd_def
        del: hd_imp_time'.simps tl_imp_time'.simps cons_imp_time'.simps)
qed

lemma hd_nat_le: "hd_nat n \<le> n"
  unfolding hd_nat_def fst_nat_fst'_nat fst'_nat_def by auto

definition "append_imp_time'_iter_bound acc xs \<equiv> 60 * (floor_log xs)\<^sup>2 + 1028 * floor_log xs + 10 * floor_log acc + 4439"

fun append_imp_time'' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "append_imp_time'' _ 0 = 2"
| "append_imp_time'' acc xs = append_imp_time'_iter_bound acc xs + append_imp_time'' (cons (hd_nat xs) acc) (tl_nat xs)"

(* Extra Suc to account for rounding down :( *)
lemma log_mult: "floor_log (n * m) \<le> Suc (floor_log n + floor_log m)"
  by (auto simp add: log_altdef algebra_simps log_mult floor_add)
thm log_twice


lemma cons_bound:
  "floor_log (cons h t) \<le> Suc (Suc (Suc (Suc (Suc (Suc (3 * floor_log h + 2 * floor_log t))))))"
proof-
  have "floor_log (Suc ((h + t) * Suc (h + t) div 2 + h))
    \<le> Suc (Suc (floor_log ((h + t) * Suc (h + t) div 2) + floor_log h))"
    using dlog_add_bound dlog_Suc_bound by (meson Suc_le_mono le_trans)
  also have "\<dots> \<le> Suc (Suc (floor_log ((h + t) * Suc (h + t)) + floor_log h))" (* Bounds are getting more and more loose lol*)
    by (subst log_half) auto
  also have "\<dots> \<le> Suc (Suc (Suc (floor_log (h + t) + floor_log (Suc (h + t)) + floor_log h)))"
    using log_mult by (metis (no_types, opaque_lifting) Suc_plus add.commute nat_add_left_cancel_le)
  also have "\<dots> \<le> Suc (Suc (Suc (Suc (2 * floor_log (h + t) + floor_log h))))"
    using dlog_Suc_bound by force
  also have "\<dots> \<le> Suc (Suc (Suc (Suc (2 * Suc (floor_log h + floor_log t) + floor_log h))))"
    using dlog_add_bound by (meson Suc_le_mono add_mono_thms_linordered_semiring(3) mult_le_mono2)
  also have "\<dots> \<le> Suc (Suc (Suc (Suc (Suc (Suc (3 * floor_log h + 2 * floor_log t))))))"
    by simp
  finally show ?thesis
    by (auto simp add: cons_def prod_encode_def triangle_def)
qed



lemma "cons prod_encode xs (cons (y#ys))"

lemma
  "floor_log (Primitives.append_acc acc xs) \<le> 3 * Suc (floor_log acc + floor_log xs)"
proof(induction acc xs rule: Primitives.append_acc.induct)
  case (1 acc)
  then show ?case
    by simp
next
  case (2 acc xs)
  then show ?case sorry
qed

lemma add_0_eq_nat: "x = 0+(x::nat)"
  by simp

lemma "append_imp_time'_iter_bound (cons x acc) xs \<le> 10 + (append_imp_time'_iter_bound acc (cons x xs))"
  unfolding append_imp_time'_iter_bound_def
proof-


qed
  apply (subst (3) add.commute)
  apply (rule add_mono)
  apply simp
  apply (rule add_mono)

  apply simp
  apply (auto simp add: cons_def prod_encode_def triangle_def field_simps power2_eq_square)



lemma append_imp_time'_append_imp_time'': "append_imp_time' acc xs \<le> append_imp_time'' acc xs"
proof (induction acc xs rule: append_imp_time''.induct)
  case (1 uu)
  then show ?case by simp
next
  (* Why do I just now remember my rewrite? Try it here *)
  case (2 acc v)
  have s: "append_imp_time'_iter_bound acc xs = 19 + (2181 + 509 * floor_log xs + 30 * (floor_log xs)\<^sup>2)
    + (58 + 10 * floor_log xs + 10 * floor_log acc)
    + (2181 + 509 * floor_log xs + 30 * (floor_log xs)\<^sup>2)" for acc xs
    by (auto simp add: append_imp_time'_iter_bound_def)
  show ?case
    apply (simp only: s append_imp_time'.simps append_imp_time''.simps)
    apply (rule add_le_mono)
    apply (rule add_le_mono)
    apply (rule add_le_mono)
       apply (rule add_le_mono)
    apply simp
    using hd_imp_time'_non_rec_bound apply blast
    using cons_imp_time'_non_rec_bound hd_nat_le apply auto[] apply (meson floor_log_le_iff add_le_mono1 add_left_mono le_refl le_trans mult_le_mono)
    using tl_imp_time'_non_rec_bound apply blast
    using "2.IH" apply auto
    done
qed

lemma append_imp_time'_append_imp_time'': "append_imp_time'' acc xs \<le> "
proof (induction acc xs rule: append_imp_time''.induct)
  case (1 uu)
  then show ?case by simp
next
  (* Why do I just now remember my rewrite? Try it here *)
  case (2 acc v)
  have s: "append_imp_time'_iter_bound acc xs = 19 + (2181 + 509 * floor_log xs + 30 * (floor_log xs)\<^sup>2)
    + (58 + 10 * floor_log xs + 10 * floor_log acc)
    + (2181 + 509 * floor_log xs + 30 * (floor_log xs)\<^sup>2)" for acc xs
    by (auto simp add: append_imp_time'_iter_bound_def)
  show ?case
    apply (simp only: s append_imp_time'.simps append_imp_time''.simps)
    apply (rule add_le_mono)
    apply (rule add_le_mono)
    apply (rule add_le_mono)
       apply (rule add_le_mono)
    apply simp
    using hd_imp_time'_non_rec_bound apply blast
    using cons_imp_time'_non_rec_bound hd_nat_le apply auto[] apply (meson floor_log_le_iff add_le_mono1 add_left_mono le_refl le_trans mult_le_mono)
    using tl_imp_time'_non_rec_bound apply blast
    using "2.IH" apply auto
    done
qed


(* Solving recursion will be a bit ugly, as acc grows... *)

(* List stuff skipped as prod_encode_aux missing :( *)


subsubsection \<open>Logical and\<close>

fun AND_neq_zero_imp_time' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "AND_neq_zero_imp_time' a b = 1 + (if a \<noteq> 0 then 3 else 2)"

lemma AND_neq_zero_imp_time_AND_neq_zero_imp_time':
  "AND_neq_zero_imp_time t s = AND_neq_zero_imp_time' (AND_neq_zero_a s) (AND_neq_zero_b s) + t"
  by (auto simp add: AND_neq_zero_imp_time.simps)

subsubsection \<open>Logical or\<close>

fun OR_neq_zero_imp_time' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "OR_neq_zero_imp_time' a b = 1 + (if a \<noteq> 0 then 2 else 3)"

lemma OR_neq_zero_imp_time_OR_neq_zero_imp_time':
  "OR_neq_zero_imp_time t s = OR_neq_zero_imp_time' (OR_neq_zero_a s) (OR_neq_zero_b s) + t"
  by (auto simp add: OR_neq_zero_imp_time.simps)


end