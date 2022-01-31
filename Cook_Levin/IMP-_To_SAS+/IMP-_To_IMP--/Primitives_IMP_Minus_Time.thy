
subsection \<open>Timing\<close>

theory Primitives_IMP_Minus_Time
  imports Primitives_IMP_Minus "Poly_Reductions_Lib.Landau_Auxiliaries"
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
lemma mul_imp_time'_non_rec: "mul_imp_time' b = (if b = 0 then 0 else 10 * (1 + Discrete.log b)) + 2"
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
lemma mul_imp_time_non_rec: "mul_imp_time t s = (if mul_b s = 0 then 0 else 10 * (1 + Discrete.log (mul_b s))) + 2 + t"
proof-
  have "mul_imp_time t s = mul_imp_time' (mul_b s) + t"
    by (simp add: mul_imp_time_mul_imp_time')
  also have "\<dots> = (if (mul_b s) = 0 then 0 else 10 * (1 + Discrete.log (mul_b s))) + 2 + t"
    by (simp add: mul_imp_time'_non_rec)
  finally show ?thesis
    by simp
qed

(* Hide details maybe?*)
lemma mul_imp_time_non_rec_bound: "mul_imp_time t s \<le> 10 * Discrete.log (mul_b s) + 12 + t"
  using mul_imp_time_non_rec by auto

subsubsection \<open>Squaring\<close>

definition square_imp_time' :: "nat \<Rightarrow> nat" where
  "square_imp_time' a = 8 + mul_imp_time' a"

lemma square_imp_time_square_imp_time': "square_imp_time t s = square_imp_time' (square_x s) + t"
  by (subst square_imp_time.simps) (simp add: square_imp_time'_def mul_imp_time_mul_imp_time')

lemma square_imp_time'_non_rec: "square_imp_time' a = (if a = 0 then 0 else 10 * (1 + Discrete.log a)) + 10"
  by (simp del: mul_imp_time'.simps add: mul_imp_time'_non_rec square_imp_time'_def)

lemma square_imp_time'_non_rec_bound: "square_imp_time' a \<le> 20 + 10 * (Discrete.log a)"
proof-
  have "22 + 10 * Discrete.log (Suc a) \<le> 22 + 10 * Suc (Discrete.log a)"
    using dlog_Suc_bound by (meson add_left_mono mult_le_mono2)
  thus ?thesis 
    by (subst square_imp_time'_non_rec) simp 
qed

(* This allows bounding *)
lemma mono_mul_imp_time'_pre: "m \<le> n \<Longrightarrow> mul_imp_time' m \<le> mul_imp_time' n"
  by (auto simp add: Discrete.log_le_iff mul_imp_time'_non_rec)
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
lemma triangle_imp_time'_non_rec: "triangle_imp_time' a = 22 + 10 * Discrete.log (Suc a)"
  by (simp del: mul_imp_time'.simps add: mul_imp_time'_non_rec triangle_imp_time'_def)

lemma triangle_imp_time'_non_rec_bound: "triangle_imp_time' a \<le> 32 + 10 * (Discrete.log a)"
proof-
  have "22 + 10 * Discrete.log (Suc a) \<le> 22 + 10 * Suc (Discrete.log a)"
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

lemma dlog_add_bound': "a+b > 0 \<Longrightarrow> Discrete.log (a+b) \<le> Discrete.log a + Discrete.log b + 1"
  apply (induction "a+b" arbitrary: a b rule: log_induct)
   apply auto
  using log_Suc_zero apply auto[1]
  by (metis Discrete.log_le_iff add_Suc_right add_Suc_shift add_cancel_right_left add_le_mono1 
      log_twice mult_2 nat_add_left_cancel_le nat_le_linear trans_le_add1 trans_le_add2)

lemma dlog_add_bound: "Discrete.log (a+b) \<le> Suc (Discrete.log a + Discrete.log b)"
  by (metis Suc_eq_plus1 dlog_add_bound' le_SucI le_add2 not_gr0 trans_less_add2)

(* The question is whether I bound this in each step or at the end *)
lemma prod_encode_imp_time'_non_rec: "prod_encode_imp_time' a b = 30 + 10 * Discrete.log (Suc (a + b))"
  by (auto simp add: prod_encode_imp_time'_def triangle_imp_time'_non_rec)

(* Bound every step, should scale better in the long run *)
lemma prod_encode_imp_time'_non_rec_bound: 
  "prod_encode_imp_time' a b \<le> 50 + 10 * Discrete.log a + 10 * Discrete.log b"
proof-
  have "prod_encode_imp_time' a b = 8 + triangle_imp_time' (a+b)"
    unfolding prod_encode_imp_time'_def ..
  also have "\<dots> \<le> 40 + 10 * (Discrete.log (a+b))"
    using triangle_imp_time'_non_rec_bound by simp
  also have "\<dots> \<le> 40 + 10 * Suc (Discrete.log a + Discrete.log b)"
    using dlog_add_bound by (meson add_left_mono mult_le_mono2)
  also have "\<dots> = 50 + 10 * Discrete.log a + 10 * Discrete.log b"
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
  \<Longrightarrow> dsqrt'_imp_time' y L R \<le> (23 + square_imp_time' R) * (Discrete.log (R - L)) + 7"
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

      have I: "(dsqrt'_imp_time' y ((L + R) div 2) R) \<le> (23 + square_imp_time' R) * Discrete.log (R - ((L + R) div 2)) + 7"
        apply (subst "1.IH"(1))
        using "1.prems" rec True pow 
        by (auto simp add: power2_eq_square)

      have "dsqrt'_imp_time' y L R \<le> 23 + square_imp_time' R + (dsqrt'_imp_time' y ((L + R) div 2) R)"
        using s .
      also have "\<dots> \<le> (23 + square_imp_time' R) * Suc (Discrete.log (R - ((L + R) div 2))) + 7"
        using I by auto

      finally show ?thesis
        apply (subst log_rec)
        using div_greater_zero_iff size apply blast
        by (simp add: d)
    next
      case False
      hence s: "dsqrt'_imp_time' y L R \<le> 23 + square_imp_time' R + (dsqrt'_imp_time' y L ((L + R) div 2))"
        using mid_bound mono_square_imp_time'_pre by (subst dsqrt'_imp_time'.simps) (simp add: rec power2_eq_square Let_def)

      have I: "(dsqrt'_imp_time' y L ((L + R) div 2)) \<le> (23 + square_imp_time' ((L + R) div 2)) * Discrete.log (((L + R) div 2) - L) + 7"
        apply (subst "1.IH"(2))
        using "1.prems" rec False pow 
        by (auto simp add: power2_eq_square d d')
      hence I': "(dsqrt'_imp_time' y L ((L + R) div 2)) \<le> (23 + square_imp_time' R) * Discrete.log (((L + R) div 2) - L) + 7"
        using mid_bound mono_square_imp_time'_pre 
        by (smt (verit, best) add.left_commute add_le_mono less_or_eq_imp_le mult_le_mono1 nat_add_left_cancel_le)
      have "dsqrt'_imp_time' y L R \<le> 23 + square_imp_time' R + (dsqrt'_imp_time' y L ((L + R) div 2))"
        using s .
      also have "\<dots> \<le> (23 + square_imp_time' R) * Suc (Discrete.log (((L + R) div 2)- L)) + 7"
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
lemma log_changes_2pow: "(\<And>k .Suc n \<noteq> 2^k) \<Longrightarrow> Discrete.log (Suc n) = Discrete.log n"
  by (metis Suc_lessD bot_nat_0.not_eq_extremum le_SucE log_Suc_zero log_eqI log_exp2_gt log_exp2_le log_zero zero_less_Suc)

(* The bigger half is a power of two, so problem should not cascade *)
lemma "k>1 \<Longrightarrow> Suc n = 2^k \<Longrightarrow> n = 2^(k-1) + 2^(k-1) - 1"
  apply (induction n) apply auto
  using log_Suc_zero apply auto[1]
  by (metis One_nat_def diff_add_inverse le_add_diff_inverse mult_2 nat_less_le plus_1_eq_Suc power_Suc)

lemma log_split_near_2pow: "Suc n = 2^k \<Longrightarrow> Discrete.log (Suc (2 * n)) = (Discrete.log (Suc n))"
  by (simp add: log_eqI)

lemma dsqrt'_imp_time'_log: "L < R \<Longrightarrow> dsqrt'_imp_time' y L R \<le> (23 + square_imp_time' R) * (Suc (Discrete.log (R - L))) + 7"
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

      have I: "dsqrt'_imp_time' y ((L + R) div 2) R \<le> (23 + square_imp_time' R) * Suc (Discrete.log (R - ((L + R) div 2))) + 7"
        apply (rule less)
        using local.rec by linarith+

      consider (even_split) "(R - ((L + R) div 2)) = (R - L) div 2" 
        | (odd_split) "(R - ((L + R) div 2)) = Suc ((R - L) div 2)"
        by linarith
      then show ?thesis
      proof cases
        (* No problem here *)
        case even_split
        from rec have "Discrete.log (R - L) > 0"
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
          have "Discrete.log (Suc ((R - L) div 2)) = k"
            by (simp add: power)
          hence question: "Discrete.log (R - L) = k"
            apply (subst recomb)
            apply (subst log_split_near_2pow)
            using power apply assumption
            by simp

          have "dsqrt'_imp_time' y L R \<le> 23 + square_imp_time' R + (dsqrt'_imp_time' y ((L + R) div 2) R)" 
            using s .
          also have "\<dots> \<le> 23 + square_imp_time' R + ((23 + square_imp_time' R) * Suc (Discrete.log (R - ((L + R) div 2))) + 7)"
            using I by auto
          also have "\<dots> \<le> (23 + square_imp_time' R) * Suc (Suc (Discrete.log (R - ((L + R) div 2)))) + 7" 
            by simp

          have "23 + square_imp_time' R + (dsqrt'_imp_time' y ((L + R) div 2) R) \<le> (23 + square_imp_time' R) * Suc (Discrete.log (R - L)) + 7"
            by (simp add:  question) (metis \<open>Discrete.log (Suc ((R - L) div 2)) = k\<close> add.commute 
                dsqrt'_imp_time'_log_bound_2pow mid_bound odd_split power)
          (* Basically works because we have an exact version for the 2^k case *)
          show ?thesis 
            using \<open>23 + square_imp_time' R + dsqrt'_imp_time' y ((L + R) div 2) R \<le> (23 + square_imp_time' R) * Suc (Discrete.log (R - L)) + 7\<close> order.trans s by blast

        next
          case unproblematic
          hence "Suc ((R - L) div 2) \<noteq> 2^k" for k
            by (simp add: odd_split)
          hence irrel: "Discrete.log (Suc ((R - L) div 2)) = Discrete.log ((R - L) div 2)"
            by (rule log_changes_2pow)
          show ?thesis
            using I odd_split size s irrel by (subst log_rec) auto
        qed
      qed
    next
      case False

      hence s: "dsqrt'_imp_time' y L R \<le> 23 + square_imp_time' R + (dsqrt'_imp_time' y L ((L + R) div 2))"
        using mid_bound mono_square_imp_time'_pre by (subst dsqrt'_imp_time'.simps) (simp add: rec power2_eq_square Let_def)

      have I: "(dsqrt'_imp_time' y L ((L + R) div 2)) \<le> (23 + square_imp_time' R) * Suc (Discrete.log (((L + R) div 2) - L)) + 7"
        by (smt (verit, best) False One_nat_def diff_add_inverse2 diff_is_0_eq div_2_gt_zero div_greater_zero_iff div_less 
            dsqrt'_imp_time'.elims le_diff_conv le_trans less.hyps linorder_not_le local.rec mid_bound
            middle_alternative mult.commute mult_le_mono2 plus_1_eq_Suc power2_eq_square s)
        
      have split: "(((L + R) div 2) - L) = (R - L) div 2"
        by (simp add: local.rec middle_alternative)
      from rec have "Discrete.log (R - L) > 0"
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
  assumes "L < R" shows "dsqrt'_imp_time' y L R \<le> 60 + (63 * Discrete.log R + 10 * (Discrete.log R)^2)"
proof-
  have "dsqrt'_imp_time' y L R \<le> (23 + 20 + 10 * Suc (Discrete.log R)) * Suc (Discrete.log (R - L)) + 7"
    apply (rule le_trans[OF dsqrt'_imp_time'_log[OF assms, of y]]) 
    apply (rule add_le_mono1)
    apply (rule mult_le_mono1)
    using square_imp_time'_non_rec_bound[of R] by simp
  also have "\<dots> = (43 + 10 * Suc (Discrete.log R)) * Suc (Discrete.log (R - L)) + 7"
    by simp
  also have "\<dots> \<le> (43 + 10 * Suc (Discrete.log R)) * Suc (Discrete.log R) + 7"
    by (simp add: Discrete.log_le_iff)
  finally show ?thesis
    by (auto simp add: power2_eq_square algebra_simps)
qed

lemma "dsqrt'_state_L s < dsqrt'_state_R s \<Longrightarrow> dsqrt'_imp_time t s \<le> t + 
  60 + (63 * Discrete.log (dsqrt'_state_R s) + 10 * (Discrete.log (dsqrt'_state_R s))^2)"
  by (simp add: dsqrt'_imp_time'_non_rec_bound dsqrt'_imp_time_dsqrt'_imp_time')

fun dsqrt_imp_time' :: "nat \<Rightarrow> nat" where
  "dsqrt_imp_time' y = 8 + dsqrt'_imp_time' y 0 (Suc y)"

lemma dsqrt_imp_time_dsqrt_imp_time': "dsqrt_imp_time t s = t + dsqrt_imp_time' (dsqrt_state_y s)"
  by (subst dsqrt_imp_time.simps) (auto simp add: dsqrt_imp_time_acc_2 dsqrt'_imp_time_dsqrt'_imp_time')

lemma dsqrt_imp_time'_non_rec_bound: "dsqrt_imp_time' y \<le> 141 + (83 * Discrete.log y + 10 * (Discrete.log y)\<^sup>2)"
proof-
  have "dsqrt_imp_time' y \<le> 68 + (63 * Discrete.log (Suc y) + 10 * (Discrete.log (Suc y))^2)"
    by (auto simp add: dsqrt'_imp_time'_non_rec_bound)
  also have "\<dots> \<le> 131 + (63 * Discrete.log y + 10 * (Discrete.log (Suc y))^2)"
    by simp (metis dlog_Suc_bound le_refl mult_Suc_right mult_le_mono)
  also have "\<dots> \<le> 131 + (63 * Discrete.log y + 10 * (Suc (Discrete.log y))^2)"
    by (simp add: dlog_Suc_bound)
  also have "\<dots> = 131 + (63 * Discrete.log y + 10 * (1 + 2 * Discrete.log y + (Discrete.log y)^2))"
    by (smt (verit, del_insts) Suc_eq_plus1_left add.assoc add.commute mult.assoc mult_1 power2_sum power_one)
  also have "\<dots> \<le> 141 + (83 * Discrete.log y + 10 * (Discrete.log y)^2)"
    by simp
  finally show ?thesis .
qed

text \<open>Triangular root\<close>

fun tsqrt_imp_time' :: "nat \<Rightarrow> nat" where
  "tsqrt_imp_time' y = 16 + mul_imp_time' 8 + dsqrt_imp_time' (8*y+1)"

lemma tsqrt_imp_time_tsqrt_imp_time': "tsqrt_imp_time t s = t + tsqrt_imp_time' (tsqrt_state_y s)"
  by (subst tsqrt_imp_time.simps) (auto simp add: tsqrt_imp_time_acc_2 dsqrt_imp_time_dsqrt_imp_time' 
      mul_imp_time_mul_imp_time' mul_imp_correct Let_def mult.commute)

lemma tsqrt_imp_time'_non_rec_bound: "tsqrt_imp_time' y \<le> 691 + (163 * Discrete.log y + 10 * (Discrete.log y)\<^sup>2)"
proof-
  have "tsqrt_imp_time' y = 58 + dsqrt_imp_time' (8*y+1)"
    by code_simp
  also have "\<dots> \<le> 58 + (141 + (83 * Discrete.log (8*y+1) + 10 * (Discrete.log (8*y+1))\<^sup>2))"
    using dsqrt_imp_time'_non_rec_bound by auto
  also have "\<dots> \<le> 282 + (83 * Discrete.log (8*y) + 10 * (Discrete.log (8*y+1))\<^sup>2)"
    by simp (metis dlog_Suc_bound le_refl mult_Suc_right mult_le_mono)
  also have "\<dots> \<le> 282 + (83 * (3 + Discrete.log y) + 10 * (Discrete.log (8*y+1))\<^sup>2)"
  proof- (* \<le> because of y=0 case*)
    have s: "8*y = (2*(2*(2*y)))" by simp
    have "Discrete.log (8*y) = 3 + Discrete.log y" if "y>0"
      apply (subst s)
      using that apply (subst log_twice, simp)+
      by presburger
    thus ?thesis
      by force
  qed
  also have "\<dots> = 531 + (83 * Discrete.log y + 10 * (Discrete.log (8*y+1))\<^sup>2)"
    by simp
  also have "\<dots> \<le> 531 + (83 * Discrete.log y + 10 * (1 + Discrete.log (8*y))\<^sup>2)"
    by (simp add: dlog_Suc_bound)
  also have "\<dots> \<le> 531 + (83 * Discrete.log y + 10 * (4 + Discrete.log y)\<^sup>2)"
  proof-
    have s: "8*y = (2*(2*(2*y)))" by simp
    have "Discrete.log (8*y) = 3 + Discrete.log y" if "y>0"
      apply (subst s)
      using that apply (subst log_twice, simp)+
      by presburger
    thus ?thesis
      by force
  qed
  also have "\<dots> = 531 + (83 * Discrete.log y + 10 * (Discrete.log y)^2 + 80 * Discrete.log y + 160)"
    by (auto simp add: power2_eq_square algebra_simps)
  also have "\<dots> = 691 + (163 * Discrete.log y + 10 * (Discrete.log y)^2)"
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

lemma fst'_imp_time'_non_rec_bound: "fst'_imp_time' p \<le> 733 + 173 * Discrete.log p + 10 * (Discrete.log p)\<^sup>2"
proof-
  have "fst'_imp_time' p = 10 + tsqrt_imp_time' p + triangle_imp_time' (tsqrt p)"
    by simp
  also have "\<dots> \<le> 10 + 691 + (163 * Discrete.log p + 10 * (Discrete.log p)\<^sup>2) + triangle_imp_time' (tsqrt p)"
    using tsqrt_imp_time'_non_rec_bound by simp
  also have "\<dots> \<le> 10 + 691 + (163 * Discrete.log p + 10 * (Discrete.log p)\<^sup>2) + 32 + 10 * (Discrete.log (tsqrt p))"
    using triangle_imp_time'_non_rec_bound by simp
  also have "\<dots> \<le> 10 + 691 + (163 * Discrete.log p + 10 * (Discrete.log p)\<^sup>2) + 32 + 10 * (Discrete.log p)"
    using tsqrt_le by (simp add: Discrete.log_le_iff)
  also have "\<dots> \<le> 733 + 173 * Discrete.log p + 10 * (Discrete.log p)\<^sup>2"
    by simp
  finally show ?thesis .
qed

fun snd'_imp_time' :: "nat \<Rightarrow> nat" where
  "snd'_imp_time' p = 8 + tsqrt_imp_time' p + fst'_imp_time' p"

lemma snd'_imp_time_snd'_imp_time': "snd'_imp_time t s = t + snd'_imp_time' (snd'_state_p s)"
  by (subst snd'_imp_time.simps) (auto simp add: snd'_imp_time_acc_2 tsqrt_imp_time_tsqrt_imp_time' 
      fst'_imp_time_fst'_imp_time' Let_def)

lemma snd'_imp_time'_non_rec_bound: "snd'_imp_time' p \<le> 1432 + 336 * Discrete.log p + 20 * (Discrete.log p)\<^sup>2"
proof-
  have "snd'_imp_time' p = 8 + tsqrt_imp_time' p + fst'_imp_time' p"
    by simp
  also have "\<dots> \<le> 8 + 691 + (163 * Discrete.log p + 10 * (Discrete.log p)\<^sup>2) + fst'_imp_time' p"
    using tsqrt_imp_time'_non_rec_bound by (metis (no_types, lifting) add_mono eq_imp_le group_cancel.add1)
  also have "\<dots> \<le> 8 + 691 + (163 * Discrete.log p + 10 * (Discrete.log p)\<^sup>2) + 733 + 173 * Discrete.log p + 10 * (Discrete.log p)\<^sup>2"
    using fst'_imp_time'_non_rec_bound by (metis (mono_tags, lifting) add.assoc nat_add_left_cancel_le) 
  also have "\<dots> \<le> 1432 + 336 * Discrete.log p + 20 * (Discrete.log p)\<^sup>2"
    by auto
  finally show ?thesis .
qed


fun prod_decode_imp_time' :: "nat \<Rightarrow> nat" where
  "prod_decode_imp_time' p = 8 + fst'_imp_time' p + snd'_imp_time' p"

lemma prod_decode_imp_time_prod_decode_imp_time': "prod_decode_imp_time t s = t + prod_decode_imp_time' (prod_decode_state_p s)"
  by (subst prod_decode_imp_time.simps) (auto simp add: prod_decode_imp_time_acc_2 tsqrt_imp_time_tsqrt_imp_time' 
      fst'_imp_time_fst'_imp_time' snd'_imp_time_snd'_imp_time' Let_def)

lemma prod_decode'_imp_time'_non_rec_bound: "prod_decode_imp_time' p \<le> 2173 + 509 * Discrete.log p + 30 * (Discrete.log p)\<^sup>2"
proof-
  have "prod_decode_imp_time' p = 8 + fst'_imp_time' p + snd'_imp_time' p"
    by simp
  also have "\<dots> \<le> 8 + 733 + 173 * Discrete.log p + 10 * (Discrete.log p)\<^sup>2 + snd'_imp_time' p"
    using fst'_imp_time'_non_rec_bound by (metis (no_types, lifting) add_mono eq_imp_le group_cancel.add1)
  also have "\<dots> \<le> 8 + 733 + 173 * Discrete.log p + 10 * (Discrete.log p)\<^sup>2 + 1432 + 336 * Discrete.log p + 20 * (Discrete.log p)\<^sup>2"
    using snd'_imp_time'_non_rec_bound by (metis (no_types, lifting) add_mono eq_imp_le group_cancel.add1)
  also have "\<dots> \<le> 2173 + 509 * Discrete.log p + 30 * (Discrete.log p)\<^sup>2" 
    by auto
  finally show ?thesis .
qed  

fun hd_imp_time' :: "nat \<Rightarrow> nat" where
  "hd_imp_time' l = 8 + prod_decode_imp_time' (l-1)"

lemma hd_imp_time_hd_imp_time': "hd_imp_time t s = t + hd_imp_time' (hd_xs s)"
  by (subst hd_imp_time.simps) (auto simp add: hd_imp_time_acc prod_decode_imp_time_prod_decode_imp_time'
      Let_def)

lemma hd_imp_time'_non_rec_bound: "hd_imp_time' l \<le> 2181 + 509 * Discrete.log l + 30 * (Discrete.log l)\<^sup>2"
proof-
  have "hd_imp_time' l \<le> 8 + 2173 + 509 * Discrete.log (l-1) + 30 * (Discrete.log (l-1))\<^sup>2" 
    using prod_decode'_imp_time'_non_rec_bound by simp
  also have "\<dots> \<le> 2181 + 509 * Discrete.log (l-1) + 30 * (Discrete.log (l-1))\<^sup>2" 
    by simp
  also have "\<dots> \<le> 2181 + 509 * Discrete.log l + 30 * (Discrete.log (l-1))\<^sup>2" 
    by (simp add: Discrete.log_le_iff)
  also have "\<dots> \<le> 2181 + 509 * Discrete.log l + 30 * (Discrete.log l)\<^sup>2" 
    by (simp add: Discrete.log_le_iff)
  finally show ?thesis .
qed


fun tl_imp_time' :: "nat \<Rightarrow> nat" where
  "tl_imp_time' l = 8 + prod_decode_imp_time' (l-1)"

lemma tl_imp_time_tl_imp_time': "tl_imp_time t s = t + tl_imp_time' (tl_xs s)"
  by (subst tl_imp_time.simps) (auto simp add: tl_imp_time_acc prod_decode_imp_time_prod_decode_imp_time'
      Let_def)

lemma tl_imp_time'_non_rec_bound: "tl_imp_time' l \<le> 2181 + 509 * Discrete.log l + 30 * (Discrete.log l)\<^sup>2"
proof-
  have "tl_imp_time' l \<le> 8 + 2173 + 509 * Discrete.log (l-1) + 30 * (Discrete.log (l-1))\<^sup>2" 
    using prod_decode'_imp_time'_non_rec_bound by simp
  also have "\<dots> \<le> 2181 + 509 * Discrete.log (l-1) + 30 * (Discrete.log (l-1))\<^sup>2" 
    by simp
  also have "\<dots> \<le> 2181 + 509 * Discrete.log l + 30 * (Discrete.log (l-1))\<^sup>2" 
    by (simp add: Discrete.log_le_iff)
  also have "\<dots> \<le> 2181 + 509 * Discrete.log l + 30 * (Discrete.log l)\<^sup>2" 
    by (simp add: Discrete.log_le_iff)
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


lemma b: assumes "6 < n" shows "(Discrete.sqrt (8 * n + 1) - 1) div 2 \<le> n div 2"
proof-
  have 1: "(Discrete.sqrt (8 * n + 1) - 1) div 2 \<le> nat (floor ((sqrt (8 * n + 1) - 1) / 2))"
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
| "length_imp_time'' xs = 9 + (2181 + 509 * Discrete.log xs + 30 * (Discrete.log xs)\<^sup>2) + length_imp_time'' (tl_nat xs)"

lemma length_imp_time'_length_imp_time'': "length_imp_time' xs \<le> length_imp_time'' xs"
  apply (induction xs rule: length_imp_time''.induct)
   apply simp
  using tl_imp_time'_non_rec_bound
  by (metis add.commute add_le_mono add_le_mono1 length_imp_time''.simps(2) length_imp_time'.simps(2))


lemma length_imp_time''_non_rec_bound': "length_imp_time'' xs 
  \<le> 2 + Suc (Discrete.log xs) * (9 + (2181 + 509 * Discrete.log xs + 30 * (Discrete.log xs)\<^sup>2))"
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
    hence "Discrete.log (tl_nat (Suc v)) \<le> Discrete.log (Suc v div 2)"
      by (rule log_le_iff)
    with "2.IH" have "length_imp_time'' (tl_nat (Suc v)) \<le> 2 + Suc (Discrete.log (Suc v div 2)) *
      (9 + (2181 + 509 * Discrete.log (tl_nat (Suc v)) + 30 * (Discrete.log (tl_nat (Suc v)))\<^sup>2))"
      by (smt (verit, best) Suc_le_mono Suc_mult_le_cancel1 add_le_cancel_left add_le_mono1 le_trans less_Suc_eq_le less_numeral_extra(3) 
          mult_le_mono not_less_less_Suc_eq numeral_2_eq_2)
    also have "\<dots> \<le> 2 + Suc (Discrete.log (Suc v div 2)) *
      (9 + (2181 + 509 * Discrete.log (Suc v div 2) + 30 * (Discrete.log (Suc v div 2))\<^sup>2))"
      by (metis \<open>Discrete.log (tl_nat (Suc v)) \<le> Discrete.log (Suc v div 2)\<close> add_left_mono 
          add_mono_thms_linordered_semiring(1) nat_mult_le_cancel_disj power2_nat_le_eq_le)
    also have "\<dots> \<le> 2 + (Discrete.log (Suc v)) *
      (9 + (2181 + 509 * Discrete.log (Suc v div 2) + 30 * (Discrete.log (Suc v div 2))\<^sup>2))"
      by (metis Discrete.log.simps True gr_implies_not0 le_eq_less_or_eq less_Suc_eq numeral_2_eq_2 zero_neq_numeral)
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
  \<le> 2192 + 2699 * Discrete.log xs + 539 * (Discrete.log xs)\<^sup>2 + 30 * (Discrete.log xs)^3"
  apply (rule le_trans[OF length_imp_time'_length_imp_time'' ])
  using length_imp_time''_non_rec_bound' by (auto simp add: field_simps power2_eq_square power3_eq_cube)

fun cons_imp_time' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "cons_imp_time' h t = 8 + prod_encode_imp_time' h t"

lemma cons_imp_time_cons_imp_time': "cons_imp_time t s = t + cons_imp_time' (cons_h s) (cons_t s)"
  by (auto simp add: cons_imp_time.simps prod_encode_imp_time_prod_encode_imp_time')

lemma cons_imp_time'_non_rec_bound: "cons_imp_time' h t \<le> 58 + 10 * Discrete.log h + 10 * Discrete.log t"
  using prod_encode_imp_time'_non_rec_bound by (simp add: add.assoc)

fun append_imp_time' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "append_imp_time' _ 0 = 2"
| "append_imp_time' acc xs = 19 + hd_imp_time' xs + cons_imp_time' (hd_nat xs) acc + tl_imp_time' xs
    + append_imp_time' (cons (hd_nat xs) acc) (tl_nat xs)"

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

definition "append_imp_time'_iter_bound acc xs \<equiv> 60 * (Discrete.log xs)\<^sup>2 + 1028 * Discrete.log xs + 10 * Discrete.log acc + 4439"

fun append_imp_time'' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "append_imp_time'' _ 0 = 2"
| "append_imp_time'' acc xs = append_imp_time'_iter_bound acc xs + append_imp_time'' (cons (hd_nat xs) acc) (tl_nat xs)"


lemma append_imp_time'_append_imp_time'': "append_imp_time' acc xs \<le> append_imp_time'' acc xs"
proof (induction acc xs rule: append_imp_time''.induct)
  case (1 uu)
  then show ?case by simp
next
  (* Why do I just now remember my rewrite? Try it here *)
  case (2 acc v)
  have s: "append_imp_time'_iter_bound acc xs = 19 + (2181 + 509 * Discrete.log xs + 30 * (Discrete.log xs)\<^sup>2)
    + (58 + 10 * Discrete.log xs + 10 * Discrete.log acc)
    + (2181 + 509 * Discrete.log xs + 30 * (Discrete.log xs)\<^sup>2)" for acc xs
    by (auto simp add: append_imp_time'_iter_bound_def)
  show ?case 
    apply (simp only: s append_imp_time'.simps append_imp_time''.simps)
    apply (rule add_le_mono)
    apply (rule add_le_mono)
    apply (rule add_le_mono)
       apply (rule add_le_mono)
    apply simp
    using hd_imp_time'_non_rec_bound apply blast
    using cons_imp_time'_non_rec_bound hd_nat_le apply auto[] apply (meson Discrete.log_le_iff add_le_mono1 add_left_mono le_refl le_trans mult_le_mono)
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