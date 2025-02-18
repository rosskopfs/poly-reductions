\<^marker>\<open>creator Florian Keßler\<close>

section "Binary Arithmetic"

theory Binary_Arithmetic 
  imports "IMP-.IMP_Minus_Base" "HOL-Library.Discrete_Functions"

begin

text \<open> In this theory, we introduce functions to access bits out of nats, and Lemmas that relate
        the bits in the result of addition and subtraction to the bits of the original numbers. \<close>

fun nth_bit_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nth_bit_nat x 0 = x mod 2" |
  "nth_bit_nat x (Suc n) = nth_bit_nat (x div 2) n"

fun nth_bit_tail:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nth_bit_tail x 0 = x mod 2" |
  "nth_bit_tail x (Suc n) = nth_bit_tail (x div 2) n"

lemma subtail_nth_bit: "nth_bit_tail x n = nth_bit_nat x n"
  by(induct x n rule: nth_bit_tail.induct) simp+

lemma nth_bit_nat_is_right_shift: "nth_bit_nat x n = (x div 2 ^ n) mod 2"
  apply(induction n arbitrary: x)
  by(auto simp:  div_mult2_eq)

definition nth_bit:: "nat \<Rightarrow> nat \<Rightarrow> bit" where
"nth_bit x n = nat_to_bit (nth_bit_nat x n)"

fun nth_bit_of_num:: "num \<Rightarrow> nat \<Rightarrow> bit" where
"nth_bit_of_num Num.One 0 = One" |
"nth_bit_of_num Num.One (Suc n) = Zero" |
"nth_bit_of_num (Num.Bit0 x) 0 = Zero" |
"nth_bit_of_num (Num.Bit1 x) 0 = One" |
"nth_bit_of_num (Num.Bit0 x) (Suc n) = nth_bit_of_num x n" |
"nth_bit_of_num (Num.Bit1 x) (Suc n) = nth_bit_of_num x n"

lemma nth_bit_nat_of_zero[simp]: "nth_bit_nat 0 n = 0"
  by (induction n) auto

lemma nth_bit_of_zero[simp]: "nth_bit 0 n = Zero"
  by (induction n) (auto simp: nth_bit_def)

lemma nth_bit_of_one[simp]: "nth_bit (Suc 0) n = (if n = 0 then One else Zero)"
  apply(cases n)
  by(auto simp: nth_bit_def nat_to_bit_eq_Zero_iff)

lemma one_plus_2n_is_odd[simp]: "Suc (n + n) mod 2 = 1" by presburger

lemma nth_bit_of_nat_of_num: "nth_bit (nat_of_num x) n = nth_bit_of_num x n"
proof(induction n arbitrary: x)
  case 0
  then show ?case by (cases x) (auto simp: nth_bit_def nat_to_bit_eq_One_iff)
next
  case (Suc n)
  then show ?case using Suc by (cases x) (auto simp: nth_bit_def)
qed

lemma nth_bit_is_nth_bit_of_num: "nth_bit x n = (if x = 0 then Zero
  else nth_bit_of_num (num_of_nat x) n)"
proof (cases "x = 0")
  case False
  hence "nth_bit x n = nth_bit (nat_of_num (num_of_nat x)) n" using num_of_nat_inverse by auto
  thus ?thesis using False by(simp add: nth_bit_of_nat_of_num)
qed auto

lemma le_2_to_the_n_then_nth_bit_zero: "x < 2 ^ n \<Longrightarrow> nth_bit x n = Zero"
  by(auto simp: nth_bit_def nat_to_bit_eq_Zero_iff nth_bit_nat_is_right_shift)

lemma nth_bit_add_out_of_range: "(a :: nat) < 2 ^ n \<Longrightarrow> j < n \<Longrightarrow> nth_bit (2 ^ n + a) j = nth_bit a j"
proof-
  assume "a < 2 ^ n" "j < n"
  have "(2 ^ n + a) div 2 ^ j mod 2 = ((2 ^ n) div 2 ^ j + a div 2 ^ j) mod 2"
    using div_plus_div_distrib_dvd_left[OF le_imp_power_dvd[OF less_imp_le_nat[OF \<open>j < n\<close>]]]
    by metis
  also have "... = (2 ^ (n - j) + a div 2 ^ j) mod 2" using \<open>j < n\<close>
    using power_diff[OF _ less_imp_le_nat[OF \<open>j < n\<close>], where ?a=2]
    by (metis nat.simps numeral_2_eq_2)
  also have  "... = a div 2 ^ j mod 2" using \<open>j < n\<close>
    by (metis (no_types, lifting) Suc_leI add.commute add.right_neutral even_iff_mod_2_eq_zero
        le_imp_power_dvd mod_add_left_eq power_Suc0_right zero_less_diff)
  finally show ?thesis
    apply(cases "nth_bit a j")
    by(auto simp: nth_bit_def nat_to_bit_cases nth_bit_nat_is_right_shift)
qed

fun nth_carry:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bit" where
"nth_carry 0 a b = (if (nth_bit a 0 = One \<and> nth_bit b 0 = One) then One else Zero)" |
"nth_carry (Suc n) a b = (if (nth_bit a (Suc n) = One \<and> nth_bit b (Suc n) = One)
  \<or> ((nth_bit a (Suc n) = One \<or> nth_bit b (Suc n) = One) \<and> nth_carry n a b = One)
  then One else Zero)"

lemma a_mod_n_plus_b_mod_n_geq_a_plus_b_mod_n: "(a :: nat) mod n + b mod n \<ge> (a + b) mod n"
  by (metis mod_add_eq mod_less_eq_dividend)

lemma a_mod_2_to_the_n_decomposition: "(a :: nat) mod (2 * 2 ^ n)
  = a div 2 ^ n mod 2 * 2 ^ n +  a mod 2 ^ n"
  by (metis mod_mult2_eq mult.commute)

lemma a_mod_plus_b_mod_div_le_2: "((a :: nat) mod 2 ^ n + b mod 2 ^ n) div 2 ^ n < 2"
proof-
  have "a mod 2 ^ n < 2 ^ n" "b mod 2 ^ n < 2 ^ n" by auto
  hence "(a mod 2 ^ n + b mod 2 ^ n) < 2 * 2 ^ n" by linarith
  thus ?thesis using less_mult_imp_div_less by simp
qed

lemma a_mod_plus_b_mod: "((a :: nat) mod (2 * 2 ^ n) + b mod (2 * 2 ^ n)) div (2 * 2 ^ n) mod 2
  = (a div 2 ^ n mod 2 + b div 2 ^ n mod 2 +
      (a mod (2 ^ n) + b mod (2 ^ n)) div (2 ^ n) mod 2) div 2"
proof -
  have "(a mod (2 * 2 ^ n) + b mod (2 * 2 ^ n)) div (2 * 2 ^ n) mod 2
    = (a div 2 ^ n mod 2 * 2 ^ n + b div 2 ^ n mod 2 * 2 ^ n
      + a mod 2 ^ n + b mod 2 ^ n) div (2 * 2 ^ n) mod 2"
    using a_mod_2_to_the_n_decomposition by presburger
  also have "... = ((a div 2 ^ n mod 2 * 2 ^ n + b div 2 ^ n mod 2 * 2 ^ n
      + a mod 2 ^ n + b mod 2 ^ n) div 2 ^ n) div 2 mod 2"
    by (metis (mono_tags, lifting) div_mult2_eq mult.commute)
  also have "... = ((a div 2 ^ n mod 2 * 2 ^ n) div 2 ^ n  + (b div 2 ^ n mod 2 * 2 ^ n) div 2 ^ n
      + (a mod 2 ^ n + b mod 2 ^ n) div 2 ^ n) div 2 mod 2" by (simp add: add.assoc)
  also have "... = (a div 2 ^ n mod 2  + b div 2 ^ n mod 2
      + (a mod 2 ^ n + b mod 2 ^ n) div 2 ^ n) div 2 mod 2" by simp
  also have "... = (a div 2 ^ n mod 2  + b div 2 ^ n mod 2
      + (a mod 2 ^ n + b mod 2 ^ n) div 2 ^ n mod 2) div 2 mod 2"
    using a_mod_plus_b_mod_div_le_2 by simp
  finally show ?thesis by simp
qed

lemma nth_carry_mod: "nth_carry n a b =
  nth_bit ((a mod 2 ^ Suc n) + (b mod 2 ^ Suc n)) (Suc n)"
proof(induction n)
  case 0
  then show ?case by(auto simp: nth_bit_def nat_to_bit_cases nth_bit_nat_is_right_shift)
next
  case (Suc n)
  then show ?case
    apply(cases "nth_carry n a b")
      by(auto simp: nth_bit_def nat_to_bit_cases nth_bit_nat_is_right_shift
          a_mod_plus_b_mod[where ?n="Suc n", simplified] algebra_simps split: if_splits)
qed

lemma first_bit_of_add: "nth_bit (a + b) 0
  = (if nth_bit a 0 = One then if nth_bit b 0 = One then Zero else One
     else if nth_bit b 0 = One then One else Zero)"
  apply(auto simp: nth_bit_def nat_to_bit_eq_One_iff nat_to_bit_eq_Zero_iff)
  by presburger

lemma nth_bit_of_add: "nth_bit (a + b) (Suc n) = (let u = nth_bit a (Suc n);
  v = nth_bit b (Suc n); w = nth_carry n a b in
  (if u = One then
    if v = One then
     if w = One then One else Zero
    else
     if w = One then Zero else One
   else
    if v = One then
     if w = One then Zero else One
    else
     if w = One then One else Zero))"
  apply(auto simp: Let_def nth_bit_def nth_bit_nat_is_right_shift nat_to_bit_cases nth_carry_mod)
  by (metis div_add1_eq even_add even_iff_mod_2_eq_zero not_mod2_eq_Suc_0_eq_0)+

lemma no_overflow_condition: "a + b < 2 ^ n \<Longrightarrow> nth_carry (n - 1) a b = Zero"
  apply(cases n)
  by(auto simp: nth_carry_mod nth_bit_def nth_bit_nat_is_right_shift nat_to_bit_cases)

lemma has_bit_one_then_greater_zero: "nth_bit a j = One \<Longrightarrow> 0 < a"
  apply(auto simp: nth_bit_def nth_bit_nat_is_right_shift nat_to_bit_cases)
  by (metis One_nat_def div_less dvd_0_right even_mod_2_iff gr_zeroI less_2_cases_iff
      odd_one zero_less_power)

lemma greater_zero_then_has_bit_one: "x > 0 \<Longrightarrow> x < 2 ^ n \<Longrightarrow> \<exists>b \<in> {0..<n}. nth_bit x b = One"
proof(rule ccontr)
  assume "x > 0" "x < 2 ^ n" "\<not> (\<exists>b\<in>{0..<n}. nth_bit x b = One)"
  hence "(\<forall>b. nth_bit x b = Zero) \<or> (\<exists>b \<ge> n. nth_bit x b = One)" by auto
  thus False
  proof(elim disjE)
    assume "\<forall>b. nth_bit x b = Zero"
    hence "nth_bit x (floor_log x) = Zero" by auto
    moreover have "x div 2 ^ floor_log x = 1"
      using floor_log_exp2_gt floor_log_exp2_le[OF \<open>x > 0\<close>]
      by (metis Euclidean_Rings.div_eq_0_iff One_nat_def leD less_2_cases_iff
          less_mult_imp_div_less power_not_zero zero_neq_numeral)
    ultimately show False by(auto simp: nth_bit_def nth_bit_nat_is_right_shift nat_to_bit_cases)
  next
    assume "\<exists>b \<ge> n. nth_bit x b = One"
    then obtain b where "b \<ge> n \<and> nth_bit x b = One" by blast
    thus False using \<open>x < 2 ^ n\<close>
      apply(auto simp: nth_bit_def nth_bit_nat_is_right_shift nat_to_bit_cases)
      by (metis div_greater_zero_iff gr0I leD le_less_trans less_2_cases_iff less_Suc0
          mod_less_eq_dividend nat_power_less_imp_less)
  qed
qed

fun nth_carry_sub:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bit" where
"nth_carry_sub 0 a b = (if (nth_bit a 0 = Zero \<and> nth_bit b 0 = One) then One else Zero)" |
"nth_carry_sub (Suc n) a b =
  (if (nth_bit a (Suc n) = Zero \<and> ( nth_bit b (Suc n) = One \<or> nth_carry_sub n a b = One))
    \<or> (nth_bit a (Suc n) = One \<and> (nth_bit b (Suc n)) = One \<and> nth_carry_sub n a b = One) then One
  else Zero)"

lemma a_mod_less_b_mod_iff: "(a :: nat) mod (2 * 2 ^ n) < b mod (2 * 2 ^ n)
  \<longleftrightarrow> ((a div 2 ^ n mod 2 < b div 2 ^ n mod 2)
        \<or> (a div 2 ^ n mod 2 = b div 2 ^ n mod 2 \<and> a mod 2 ^ n < b mod 2 ^ n))"
  apply(auto simp: algebra_simps a_mod_2_to_the_n_decomposition)
    apply (smt add.right_neutral add_self_div_2 le_less_trans le_simps(1) less_Suc0 mod_less_divisor
      mult_0_right mult_numeral_1_right not_add_less2 not_mod_2_eq_0_eq_1 numeral_2_eq_2
      numeral_Bit0_div_2 plus_1_eq_Suc pos2 zero_less_power)
   apply (metis (no_types, lifting) One_nat_def add.right_neutral add_lessD1 add_less_cancel_right
      less_Suc0 mult_0_right not_mod_2_eq_0_eq_1)
  by (smt add.commute add.right_neutral add_self_div_2 mod_less_divisor mult_0_right
      mult_numeral_1_right not_add_less2 not_mod_2_eq_0_eq_1 numeral_2_eq_2
      numeral_Bit0_div_2 plus_1_eq_Suc trans_less_add2 zero_less_power)

lemma nth_carry_sub_mod: "nth_carry_sub n a b =
 (if (a mod 2 ^ Suc n) < (b mod 2 ^ Suc n) then One else Zero)"
proof(induction n)
  case 0
  then show ?case by(auto simp: nth_bit_def nat_to_bit_cases nth_bit_nat_is_right_shift)
next
  case (Suc n)
  then show ?case
    apply(cases "nth_carry_sub n a b")
    by(auto simp: nth_bit_def nat_to_bit_cases nth_bit_nat_is_right_shift
        a_mod_less_b_mod_iff[where ?n="Suc n", simplified] algebra_simps split: if_splits)
qed

lemma first_bit_of_sub_n_no_underflow: "a \<ge> b \<Longrightarrow> nth_bit (a - b) 0 = (if nth_bit a 0 = One then
  (if nth_bit b 0 = One then Zero else One)
  else (if nth_bit b 0 = One then One else Zero))"
  apply(auto simp: nth_bit_def nat_to_bit_eq_One_iff nat_to_bit_eq_Zero_iff)
  by presburger+

lemma a_times_n_minus_one_div_n: "n > 0 \<Longrightarrow> ((a :: nat) * n - 1) div n = a - 1"
proof(induction a)
  case (Suc a)
  then show ?case using Suc
  proof(cases a)
    case (Suc nat)
    hence "((Suc a) * n - 1) div n = (n + (a * n - 1)) div n"
      using Suc.prems by auto
    also have "... = 1 + (a * n - 1) div n" using Suc by (simp add: Suc.prems)
    finally show ?thesis using Suc  using Suc.IH Suc.prems by auto
  qed auto
qed auto

lemma a_times_n_minus_n_minus_one_div_n: "n > 1 \<Longrightarrow> ((a :: nat) * n - (n - 1)) div n = a - 1"
proof(induction a)
  case (Suc a)
  then show ?case using Suc
  proof(cases a)
    case (Suc nat)
    hence "((Suc a) * n - (n - 1)) div n = (n + (a * n - (n - 1))) div n"
      using Suc.prems by auto
    also have "... = 1 + (a * n - (n - 1)) div n" using Suc.prems Euclidean_Rings.le_div_geq by auto
    finally show ?thesis using Suc  using Suc.IH Suc.prems by auto
  qed auto
qed auto

lemma a_plus_b_minus_c_mod:
  assumes "n > 1"
  shows "((a :: nat) * n + b mod n - c mod n) div n
    = a - (if b mod n < c mod n then 1 else 0)"
proof(cases "b mod n < c mod n")
  case True
  hence "(a * n + b mod n - c mod n) div n \<le> (a * n - 1) div n" by(auto intro: div_le_mono)
  hence "(a * n + b mod n - c mod n) div n \<le> a - 1" using \<open>n > 1\<close> a_times_n_minus_one_div_n by simp
  have "(a * n + b mod n - c mod n) div n \<ge> (a * n + b mod n - (n - 1)) div n"
    apply(rule div_le_mono)
    apply(rule diff_le_mono2)
    using  mod_less_divisor[where ?n=n] \<open>n > 1\<close>
    by (metis One_nat_def Suc_pred le_less_trans less_Suc_eq_le zero_le_one)
  moreover have "(a * n + b mod n - (n - 1)) div n \<ge> (a * n - (n - 1)) div n"
    using div_le_mono by simp
  ultimately have "(a * n + b mod n - c mod n) div n \<ge> a - 1"
    using a_times_n_minus_n_minus_one_div_n[OF \<open>n > 1\<close>] by simp
  show ?thesis using \<open>(a * n + b mod n - c mod n) div n \<le> a - 1\<close>
    \<open>(a * n + b mod n - c mod n) div n \<ge> a - 1\<close> using True le_antisym by presburger
next
  case False
  hence "(a * n + b mod n - c mod n) div n = (a * n + (b mod n - c mod n)) div n" by simp
  hence "(a * n + b mod n - c mod n) div n = a + (b mod n - c mod n) div n" using \<open>n > 1\<close> by auto
  thus ?thesis using \<open>\<not> b mod n < c mod n\<close>
    by (metis (mono_tags, lifting) Euclidean_Rings.div_eq_0_iff add_cancel_left_right diff_zero
        less_imp_diff_less mod_less_divisor neq0_conv)
qed

lemma a_minus_b_shift_right: "(a - b) div 2 ^ Suc n = (a :: nat) div 2 ^ Suc n - b div 2 ^ Suc n
  - (if a mod 2 ^ Suc n < b mod 2 ^ Suc n then 1 else 0)"
proof -
  have "1 < (2 :: nat) ^ Suc n"
    using one_less_numeral_iff power_gt1 semiring_norm(76) by blast
   have *: "(a - b) div (2 ^ Suc n) = (((a div (2 * 2 ^ n)) * 2 * 2 ^ n + a mod (2 * 2 ^ n))
        - ((b div (2 * 2 ^ n)) * 2 * 2 ^ n + b mod (2 * 2 ^ n))) div (2 * 2 ^ n)"
     by (simp add: div_mult_mod_eq mult.assoc)
   show ?thesis
   proof(cases "(a div (2 * 2 ^ n)) * 2 * 2 ^ n \<ge> (b div (2 * 2 ^ n)) * 2 * 2 ^ n")
     case True
     hence "(a - b) div (2 ^ Suc n)
        = (((a div (2 * 2 ^ n)) - (b div (2 * 2 ^ n))) * (2 * 2 ^ n)
          + a mod (2 * 2 ^ n) - b mod (2 * 2 ^ n))  div (2 * 2 ^ n)"
       using "*" by(auto simp: algebra_simps)
     then show ?thesis
       using a_plus_b_minus_c_mod[OF \<open>1 < (2 :: nat) ^ Suc n\<close>, where
           ?a="(a div (2 * 2 ^ n)) - (b div (2 * 2 ^ n))" and ?b=a and ?c=b, simplified]
       by(auto)
  next
    case False
    hence "a < b"
      by (metis div_le_mono le_neq_implies_less mult_le_mono1 nat_le_linear)
    thus ?thesis using False by auto
  qed
qed

lemma a_minus_b_mod2: "(a :: nat) \<ge> b \<Longrightarrow> (a - b) mod 2 = (if a mod 2 = 0 then
  (if b mod 2 = 0 then 0 else 1)
 else
  (if b mod 2 = 0 then 1 else 0))"
  by presburger

lemma a_le_b_but_a_mod_greater_b_mod_then: "a \<ge> b \<Longrightarrow> a mod n < b mod n
  \<Longrightarrow> a div n \<ge> Suc (b div n)"
proof(rule ccontr)
  assume"a \<ge> b" "a mod n < b mod n" "\<not> (a div n \<ge> Suc (b div n))"
  hence "a = a div n * n + a mod n" by auto
  hence "a < a div n * n + b mod n" using \<open>a mod n < b mod n\<close> by linarith
  moreover have "a div n * n \<le> b div n * n" using \<open>\<not> (a div n \<ge> Suc (b div n))\<close> by simp
  ultimately have "a < b div n * n + b mod n" by linarith
  also have "... = b" by simp
  finally show False using \<open>a \<ge> b\<close> by simp
qed

lemma nth_bit_of_sub_n_no_underflow: "a \<ge> b \<Longrightarrow>
  nth_bit (a - b) (Suc n) = (let an = nth_bit a (Suc n); bn = nth_bit b (Suc n);
  c = nth_carry_sub n a b in
  (if an = One then
    (if bn = One then
      (if c = One then One else Zero)
     else
      (if c = One then Zero else One))
  else
    (if bn = One then
      (if c = One then Zero else One)
     else
      (if c = One then One else Zero))))"
  apply(auto simp: Let_def nth_bit_def nth_bit_nat_is_right_shift nat_to_bit_cases
      a_minus_b_shift_right[simplified] nth_carry_sub_mod a_minus_b_mod2[OF div_le_mono]
      a_minus_b_mod2[OF a_le_b_but_a_mod_greater_b_mod_then] split: if_splits)
  by (metis dvd_imp_mod_0 even_Suc)+


lemma nth_bit_of_sub_n_underflow: "a < b \<Longrightarrow>
  nth_bit (a - b) (Suc n) = Zero"
  by simp

lemma nth_carry_sub_underflow: "a < b \<Longrightarrow> a < 2 ^ n \<Longrightarrow> b < 2 ^ n
  \<Longrightarrow> nth_carry_sub (n - 1) (2^n + a) b = One"
  apply(cases n)
  by(auto simp: nth_carry_sub_mod)

lemma nth_carry_sub_no_underflow: "a \<ge> b \<Longrightarrow> a < 2 ^ n \<Longrightarrow> b < 2 ^ n
  \<Longrightarrow> nth_carry_sub (n - 1) a b = Zero"
  by (smt bit_neq_zero_iff le_add_diff_inverse no_overflow_condition nth_bit_of_add
      nth_bit_of_sub_n_no_underflow)

lemma div2_is_right_shift: "nth_bit (x div 2) n = nth_bit x (Suc n)"
  by(auto simp: nth_bit_def)

fun bit_list_to_nat:: "bit list \<Rightarrow> nat" where
"bit_list_to_nat [] = 0" |
"bit_list_to_nat (x # xs) = (case x of Zero \<Rightarrow> 2 * bit_list_to_nat xs |
  One \<Rightarrow> 1 + 2 * bit_list_to_nat xs)"

lemma bit_list_to_nat_right_shift: "(bit_list_to_nat l) div 2 ^ n
  = (bit_list_to_nat (drop n l))"
proof(induction l arbitrary: n)
  case (Cons a l)
  then show ?case
     apply(cases n)
     apply(auto split: bit.splits)
    by (simp add: div_mult2_eq)
qed simp

lemma bit_list_to_nat_mod2: "bit_list_to_nat l mod 2 = (if l = [] then 0 else
  (if hd l = Zero then 0 else 1))"
  apply(cases l)
  by auto

lemma nth_bit_of_bit_list_to_nat[simp]: "nth_bit (bit_list_to_nat l) k
  = (if k < length l then l ! k else Zero)"
    apply(cases "nat_to_bit (2 * bit_list_to_nat l div 2 ^ k mod 2)")
  by(auto simp: nth_bit_def nth_bit_nat_is_right_shift nat_to_bit_cases
        bit_list_to_nat_right_shift bit_list_to_nat_mod2 hd_drop_conv_nth
        split: bit.splits if_splits)

lemma nth_bit_to_nat_greater_zero_then_has_bit_greater_zero:
  assumes "bit_list_to_nat l > 0"
  shows "\<exists>i < length l. l ! i = One"
  using assms
proof(induction l)
  case (Cons a l)
  then show ?case
  proof(cases a)
    case Zero
    hence "bit_list_to_nat l > 0" using Cons by simp
    show ?thesis using Cons.IH[OF \<open>bit_list_to_nat l > 0\<close>] by auto
  qed auto
qed auto

lemma bit_list_to_nat_geq_two_to_the_k_then: "bit_list_to_nat l \<ge> 2 ^ k
  \<Longrightarrow> (\<exists>i. k \<le> i \<and> i < length l \<and> l ! i = One)"
proof-
  assume "bit_list_to_nat l \<ge> 2 ^ k"
  hence "(bit_list_to_nat l) div 2 ^ k \<ge> 1" by (simp add: Suc_leI div_greater_zero_iff)
  hence "bit_list_to_nat (drop k l) \<ge> 1" using bit_list_to_nat_right_shift by simp
  then obtain i where "i < length (drop k l) \<and> (drop k l) ! i = One"
    using nth_bit_to_nat_greater_zero_then_has_bit_greater_zero by force
  hence "k \<le> (k + i) \<and> k + i < length l \<and> l ! (k + i) = One" by auto
  thus ?thesis by blast
qed

lemma not_One_then_has_bit_one_at_higher_position: "x \<noteq> Num.One
  \<Longrightarrow> (\<exists>i > 0. nth_bit_of_num x i = One)"
proof(induction x)
  case One
  then show ?case by auto
next
  case (Bit0 x)
  then show ?case by (cases x) auto
next
  case (Bit1 x)
  then show ?case by (cases x) auto
qed


lemma num_unequal_then_has_unequal_bit: "x \<noteq> y
  \<Longrightarrow> (\<exists>i. nth_bit_of_num x i \<noteq> nth_bit_of_num y i)"
proof(induction x arbitrary: y)
  case One
  hence "y \<noteq> Num.One" by simp
  then obtain i where "i > 0 \<and> nth_bit_of_num y i = One"
    using not_One_then_has_bit_one_at_higher_position by auto
  moreover hence "nth_bit_of_num Num.One i = Zero" using gr0_implies_Suc nth_bit_of_num.simps by blast
  ultimately show ?case by (metis bit.simps)
next
  case (Bit0 x)
  then show ?case
  proof(cases y)
    case One
    then obtain i where "i > 0 \<and> nth_bit_of_num (Num.Bit0 x) i = One"
      using not_One_then_has_bit_one_at_higher_position by auto
    moreover hence "nth_bit_of_num Num.One i = Zero" using gr0_implies_Suc nth_bit_of_num.simps by blast
    ultimately show ?thesis using One by (metis bit.simps)
  next
    case (Bit0 x2)
    hence "x \<noteq> x2" using \<open>num.Bit0 x \<noteq> y\<close> by simp
    then obtain i where "nth_bit_of_num x i \<noteq> nth_bit_of_num x2 i" using Bit0.IH[OF \<open>x \<noteq> x2\<close>] by blast
    hence "nth_bit_of_num (num.Bit0 x) (Suc i) \<noteq> nth_bit_of_num (num.Bit0 x2) (Suc i)" by simp
    then show ?thesis using \<open>y = num.Bit0 x2\<close> by blast
  next
    case (Bit1 x3)
    then show ?thesis by (metis bit.simps nth_bit_of_num.simps nth_bit_of_num.simps)
  qed
next
  case (Bit1 x)
  then show ?case
  proof(cases y)
    case One
    then obtain i where "i > 0 \<and> nth_bit_of_num (Num.Bit1 x) i = One"
      using not_One_then_has_bit_one_at_higher_position by auto
    moreover hence "nth_bit_of_num Num.One i = Zero" using gr0_implies_Suc nth_bit_of_num.simps by blast
    ultimately show ?thesis using One by (metis bit.simps)
  next
    case (Bit0 x2)
    then show ?thesis by (metis bit.simps nth_bit_of_num.simps nth_bit_of_num.simps)
  next
    case (Bit1 x3)
    hence "x \<noteq> x3" using \<open>num.Bit1 x \<noteq> y\<close> by simp
    then obtain i where "nth_bit_of_num x i \<noteq> nth_bit_of_num x3 i" using Bit1.IH[OF \<open>x \<noteq> x3\<close>] by blast
    hence "nth_bit_of_num (num.Bit1 x) (Suc i) \<noteq> nth_bit_of_num (num.Bit1 x3) (Suc i)" by simp
    then show ?thesis using \<open>y = num.Bit1 x3\<close> by blast
  qed
qed

lemma all_bits_equal_then_equal: "x < 2 ^ n \<Longrightarrow> y < 2 ^ n \<Longrightarrow> (\<And>i. i < n \<Longrightarrow> nth_bit x i = nth_bit y i) \<Longrightarrow> x = y"
proof(rule ccontr, goal_cases)
  case 1
  hence "i > n \<longrightarrow> x div 2 ^ i = 0" "i > n \<longrightarrow> y div 2 ^ i = 0" for i
    by (meson div_greater_zero_iff gr0I le_less_trans nat_power_less_imp_less order.asym pos2)+
  hence all_bits_equal: "nth_bit x i = nth_bit y i" for i
    apply(cases "i < n")
    using 1
     apply(simp_all add: nth_bit_def nth_bit_nat_is_right_shift)
    by (metis \<open>x < 2 ^ n\<close> \<open>y < 2 ^ n\<close> div_less linorder_neqE_nat)
  assume "x \<noteq> y"
  have "x \<noteq> 0" apply - apply(rule ccontr)
    using \<open>x \<noteq> y\<close> all_bits_equal greater_zero_then_has_bit_one[OF _ \<open>y < 2 ^ n\<close>] by auto
  have "y \<noteq> 0" apply - apply(rule ccontr)
    using \<open>x \<noteq> y\<close> all_bits_equal greater_zero_then_has_bit_one[OF _ \<open>x < 2 ^ n\<close>] by auto
  have "num_of_nat x \<noteq> num_of_nat y"
  proof (rule ccontr)
    assume "\<not>(num_of_nat x \<noteq> num_of_nat y)"
    hence "nat_of_num (num_of_nat x) = nat_of_num (num_of_nat y)" by simp
    hence "x = y" using \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close> num_of_nat_inverse by auto
    thus False using \<open>x \<noteq> y\<close> by blast
  qed
  then obtain i where "nth_bit_of_num (num_of_nat x) i \<noteq> nth_bit_of_num (num_of_nat y) i"
    using num_unequal_then_has_unequal_bit by auto
  hence "nth_bit x i \<noteq> nth_bit y i" using \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close>
    by(auto simp: nth_bit_is_nth_bit_of_num)
  thus False using all_bits_equal by blast
qed

lemma bit_list_to_nat_less_2_to_the_length: "bit_list_to_nat l < 2 ^ length l"
  apply(rule ccontr)
  using bit_list_to_nat_geq_two_to_the_k_then using not_less by blast

lemma bit_list_to_nat_eq_nat_iff: "bit_list_to_nat l = y \<longleftrightarrow> (y < 2 ^ length l \<and>
  (\<forall>i < length l. l ! i = nth_bit y i))"
proof
  assume "bit_list_to_nat l = y"
  hence "y = bit_list_to_nat l" by simp
  hence "y div 2 ^ length l = 0" by(simp add: \<open>y = bit_list_to_nat l\<close> bit_list_to_nat_right_shift)
  hence "y < 2 ^ length l" by (simp add: Euclidean_Rings.div_eq_0_iff)
  thus "y < 2 ^ length l \<and> (\<forall>i < length l. l ! i = nth_bit y i)"
    by(simp add: \<open>y = bit_list_to_nat l\<close>)
next
  assume "y < 2 ^ length l \<and> (\<forall>i < length l. l ! i = nth_bit y i)"
  thus "bit_list_to_nat l = y"
    apply - apply(rule all_bits_equal_then_equal[where ?n="length l"])
    using bit_list_to_nat_less_2_to_the_length by auto
qed

definition bit_length where "bit_length x \<equiv>  floor_log x + 1"

lemma bit_length_monotonic: "x \<le> y \<Longrightarrow> bit_length x \<le> bit_length y"
  by(auto simp: bit_length_def floor_log_le_iff)

lemma mod_2_of_zero_is_zero_intro: "x = (0 :: nat) \<Longrightarrow> x mod 2 = 0" by auto

lemma bit_geq_bit_length_is_Zero: "i \<ge> bit_length x \<Longrightarrow> nth_bit x i = Zero"
  apply(auto simp: nth_bit_def nat_to_bit_cases nth_bit_nat_is_right_shift bit_length_def)
  apply(rule mod_2_of_zero_is_zero_intro)
  by (metis div_less floor_log_le_iff floor_log_power linorder_not_le not_less_eq_eq)

end