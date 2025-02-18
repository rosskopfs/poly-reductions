\<^marker>\<open>creator Florian Keßler\<close>
\<^marker>\<open>contributors Mohammad Abdulaziz, Bilel Ghorbel\<close>

section "IMP to IMP-"

theory IMP_To_IMP_Minus
  imports Binary_Operations "IMP.Big_StepT" "IMP.Max_Constant"
begin

text \<open> We give a reduction from IMP to IMP-. The reduction works by bit blasting each register
       of IMP into several registers in IMP- each holding a single bit. Arithmetic operations
       and assignment in IMP are replaced by the binary operations defined in the Binary Operations
       theory. For WHILE and IF, we replace the condition of a single register's content being
       non-zero by checking whether any of the bits in the translated state is non-zero. \<close>

definition var_bit_list:: "nat \<Rightarrow> vname \<Rightarrow> vname list" where
"var_bit_list n v = map (\<lambda>i. var_bit_to_var (v, i)) [0..<n]"

lemma exists_non_zero_in_var_bit_list_iff:
  assumes "finite (range s)" "Max (range s) < 2 ^ n"
  shows "(\<exists>b\<in>set (var_bit_list n v). IMP_State_To_IMP_Minus s n b \<noteq> Some Zero)
      \<longleftrightarrow> s v > 0"
  using assms
  by(auto simp: var_bit_list_def IMP_State_To_IMP_Minus_def
      IMP_State_To_IMP_Minus_with_operands_a_b_def has_bit_one_then_greater_zero
      greater_zero_then_has_bit_one)

fun IMP_To_IMP_Minus:: "IMP_com \<Rightarrow> nat \<Rightarrow> IMP_Minus_com" where
"IMP_To_IMP_Minus Com.SKIP n = SKIP" |
"IMP_To_IMP_Minus (Com.Assign v aexp) n = assignment_to_binary n v aexp" |
"IMP_To_IMP_Minus (Com.Seq c1 c2) n =
  (IMP_To_IMP_Minus c1 n ;; IMP_To_IMP_Minus c2 n )" |
"IMP_To_IMP_Minus (Com.If v c1 c2) n = (IF (var_bit_list n v)\<noteq>0 THEN
  IMP_To_IMP_Minus c1 n ELSE IMP_To_IMP_Minus c2 n)" |
"IMP_To_IMP_Minus (Com.While v c) n = (WHILE (var_bit_list n v)\<noteq>0 DO
  IMP_To_IMP_Minus c n)"

lemma finite_range_stays_finite: "(c1, s1) \<Rightarrow>\<^bsup>t\<^esup> s2 \<Longrightarrow> finite (range s1)
  \<Longrightarrow> finite (range s2)"
  apply(induction c1 s1 t s2 rule: big_step_t_induct)
  apply auto
  by (metis Un_infinite image_Un sup_top_right)

lemma Max_insert_le_when:
  "\<lbrakk>finite (range (s :: vname \<Rightarrow> nat)); y < r;  Max (range s) < r\<rbrakk> \<Longrightarrow> Max (range (s(x := y))) < r"
proof(goal_cases)
  case 1
  hence "finite (s ` {xa. xa \<noteq> x})"
    using finite_nat_set_iff_bounded
    by auto
  moreover have "s ` {xa. xa \<noteq> x} \<noteq> {}"
    using 1
    by auto
  moreover have "max y (Max (s ` {xa. xa \<noteq> x})) < r"
    using 1
    apply(subst max_less_iff_conj)
    apply(subst Max_less_iff)
    using finite_nat_set_iff_bounded
    by auto
  ultimately show ?case
    by simp
qed

\<^marker>\<open>title "thm:spaceConsume"\<close>
lemma IMP_space_growth:
  "\<lbrakk>(c1, s1) \<Rightarrow>\<^bsup>t\<^esup> s2; finite (range s1);
    max (Max (range s1)) (Max_Constant.max_constant c1) < 2 ^ k\<rbrakk> \<Longrightarrow>
    (finite (range s2) \<and> Max (range s2) < (2 :: nat) ^ (k + t))"
proof(induction c1 s1 t s2 arbitrary: k rule: big_step_t_induct)
  case (Skip s)
  thus ?case
  by (smt add_lessD1 le_less_trans le_simps max_def mult_2 mult_Suc_right not_le plus_1_eq_Suc
      power.simps power.simps power_add)
next
  case (Assign x a s)
  hence "AExp.aval a s < 2 * 2 ^ k"
    by (auto intro!: aval_le_when)
  hence "Max (range (s(x := aval a s))) < 2 ^ (k + Suc (Suc 0))"
    using Assign
    by (fastforce simp: eval_nat_numeral intro!: trans_less_add2 Max_insert_le_when)
  thus ?case using Assign
    using finite_range_stays_finite
    by blast
next
  case (Seq c1 s1 x s2 c2 y s3 z)
  hence "finite (range s2)"
    using finite_range_stays_finite
    by blast
  hence "s2 a < 2 ^ (k + x)" for a
    using Seq \<open>finite (range s1)\<close> \<open>finite (range s2)\<close>
    by auto
  have "max_constant c2  < 2 ^ k"
    using Seq
    by simp
  hence "max_constant c2 < (2 :: nat) ^ (k + x)"
    using bigstep_progress Seq
    by (auto simp: eval_nat_numeral intro: le_less_trans less_imp_le_nat  n_less_n_mult_m)
  hence "s3 a < (2 :: nat) ^ (k + x + y)" for a using Seq \<open>finite (range s2)\<close>
    by fastforce
  moreover have "finite (range s3)"
    using Seq.hyps(2) \<open>finite (range s2)\<close> finite_range_stays_finite
    by blast
  ultimately show ?case using Seq
    by (auto simp: add.assoc eval_nat_numeral)
next
  case (WhileTrue s1 b c x s2 y s3 z)
  hence "finite (range s2)" using finite_range_stays_finite by blast
  hence "s2 a < 2 ^ (k + x)" for a
    using WhileTrue \<open>finite (range s1)\<close> \<open>finite (range s2)\<close>
    by auto
  have "max_constant (WHILE b\<noteq>0 DO c)  < 2 ^ k"
    using WhileTrue
    by simp
  hence "max_constant (WHILE b\<noteq>0 DO c) < (2 :: nat) ^ (k + x)"
    by (metis One_nat_def WhileTrue.hyps(2) bigstep_progress le_less_trans lessI
        less_add_same_cancel1 less_imp_le_nat numeral_2_eq_2 power_strict_increasing_iff)
  hence "\<forall>a. s3 a < (2 :: nat) ^ (k + x + y)"
    using WhileTrue \<open>finite (range s2)\<close>
    by fastforce
  moreover have "finite (range s3)"
    using WhileTrue.hyps(3) \<open>finite (range s2)\<close> finite_range_stays_finite
    by blast
  ultimately show ?case using WhileTrue
    by (auto simp: group_cancel.add1 mult_2 trans_less_add2)
qed (auto simp: numeral_2_eq_2 trans_less_add1)

lemma power_of_two_minus: "2 ^ a * c < 2 ^ b \<Longrightarrow> c < (2 :: nat) ^ (b - a)"
proof(induction a arbitrary: c)
  case (Suc a)
  hence "2 * c < 2 ^ (b - a)" by auto
  thus ?case
    by (metis One_nat_def Suc_diff_Suc bot_nat_0.not_eq_extremum less_Suc0
              nat_mult_less_cancel_disj numeral_2_eq_2 power_0 power_Suc zero_less_diff zero_less_power)
qed auto

lemma power_of_two_increase_exponent_le: "(2 :: nat) ^ (a + b) * c < r \<Longrightarrow> 2 ^ a * c < r"
  by(auto intro: dual_order.strict_trans2)

lemma move_exponent_to_rhs: "c < (2 :: nat) ^ (a - b) \<Longrightarrow> 2 ^ b * c < 2 ^ a"
  by (smt One_nat_def diff_mult_distrib2 gr_zeroI less_Suc0
      linordered_semidom_class.add_diff_inverse mult_eq_0_iff order.asym power.simps(1)
      power_add power_eq_0_iff zero_less_diff zero_neq_numeral)

subsection \<open>Correctness\<close>

text \<open>First direction of the correctness statement. We show that when an IMP program run from a
      state where all values are bounded terminates in some state, then the translated IMP- program
      started on the translated initial state will terminate in the translated final state, after
      a number of steps that is polynomially bigger than the number of steps the IMP program run
      for. The constants appearing in the polynomial bound have no significance.  \<close>

\<^marker>\<open>title "lem:bitblastProgram"\<close>
lemma IMP_To_IMP_Minus:
  assumes
    "(c1 :: IMP_com, s1) \<Rightarrow>\<^bsup>t\<^esup> s2"
    "finite (range s1)"
    "n > t"
    "((2 :: nat) ^ t) * (max (Max (range s1)) (max_constant c1)) < 2 ^ n"
  shows
    "t_small_step_fun (100 * n * (t - 1) + 50)
      (IMP_To_IMP_Minus c1 n, IMP_State_To_IMP_Minus s1 n)
     = (SKIP, IMP_State_To_IMP_Minus s2 n)"
  using assms
proof(induction c1 s1 t s2 rule: big_step_t_induct)
  case (Assign x a s)
  moreover hence "s v < (2 :: nat) ^ n" for v
    using Max_range_le_then_element_le[where ?s=s and ?x="2^n" and ?y=v] by fastforce
  ultimately show ?case
    apply(subst t_small_step_fun_increase_time[where ?t="50 * (n + 1)"])
    by (auto simp: aval_le_when IMP_State_To_IMP_Minus_def fun_eq_iff
             intro!: assignment_to_binary_correct[simplified]
             split!: option.splits)
next
  case (Seq c1 s1 x s2 c2 y s3 z)
  hence "(2 :: nat) ^ x \<le> 2 ^ z" by simp
  hence "((2 :: nat) ^ x) * max (Max (range s1)) (max_constant (c1 ;; c2)) < 2 ^ n"
    using Seq(8)
    by (meson leD leI less_le_trans mult_less_cancel2)
  hence "2 ^ x * max (Max (range s1)) (max_constant c1) < 2 ^ n"
    by (simp add: nat_mult_max_right)
  have "max (Max (range s1)) (max_constant (c1)) < 2 ^ (n - z)"
    using power_of_two_minus Seq.prems(3)
    by fastforce
  have "Max (range s2) < 2 ^ (n - y)"
    using
      IMP_space_growth[OF \<open>(c1, s1) \<Rightarrow>\<^bsup> x \<^esup> s2\<close> \<open>finite (range s1)\<close>
                                \<open>max (Max (range s1)) (max_constant (c1)) < 2 ^ (n - z)\<close>]
      \<open>z = x + y\<close> \<open>n > z \<close>
    by auto
  hence "2 ^ y * Max (range s2) < 2 ^ n"
    using move_exponent_to_rhs
    by blast
 moreover have "2 ^ y * max_constant c2 < 2 ^ n"
    using \<open>z = x + y\<close> \<open>2 ^ z * max (Max (range s1)) (max_constant (c1;; c2)) < 2 ^ n\<close>
          power_of_two_increase_exponent_le[where ?b=x]
    by(auto simp: add.commute nat_mult_max_right)
  ultimately have "2 ^ y * max (Max (range s2)) (max_constant c2) < 2 ^ n"
    by simp
  moreover have "finite (range s2)" using finite_range_stays_finite Seq
    by simp
  ultimately show ?case using Seq \<open>2 ^ x * max (Max (range s1)) (max_constant c1) < 2 ^ n\<close>
    apply (subst IMP_To_IMP_Minus.simps)
    apply(rule seq_terminates_when[where ?t1.0="100 * n * (x - Suc 0) + 50" and
          ?t2.0="100 * n * (y - Suc 0) + 50"])
      apply (drule bigstep_progress[where p = x] bigstep_progress[where p = y])+
      apply(cases x)
       apply simp_all
    apply(cases y)
    by (auto simp: algebra_simps)
next
  case (IfTrue s b c1 x t y c2)
  hence "(2 ^ y) * Max (range s) < 2 ^ n"
    by (meson le_less_trans max.cobounded1 move_exponent_to_rhs power_of_two_minus)
  hence "Max (range s) < 2 ^ n" by(auto intro: le_less_trans[OF _ \<open>2 ^ y * Max (range s) < 2 ^ n\<close>])
  thus ?case apply(simp only: t_small_step_fun_terminate_iff)
    using IfTrue apply(simp add: t_small_step_fun_small_step_fun exists_non_zero_in_var_bit_list_iff)
    apply(rule t_small_step_fun_increase_time[where ?t="100 * n * (x - 1) + 50"])
     apply(cases x)
      using bigstep_progress IfTrue.IH bigstep_progress
    by(fastforce simp: nat_mult_max_right)+
next
  case (IfFalse s b c2 x t y c1)
  hence "(2 ^ y) * Max (range s) < 2 ^ n"
    by (meson le_less_trans max.cobounded1 move_exponent_to_rhs power_of_two_minus)
  hence "Max (range s) < 2 ^ n" by(auto intro: le_less_trans[OF _ \<open>2 ^ y * Max (range s) < 2 ^ n\<close>])
  then show ?case
    apply(subst t_small_step_fun_terminate_iff)
    using IfFalse
    using t_small_step_fun_small_step_fun exists_non_zero_in_var_bit_list_iff
    apply simp
    apply(rule t_small_step_fun_increase_time[where ?t="100 * n * (x - 1) + 50"])
     apply(cases x)
    using bigstep_progress IfFalse.IH bigstep_progress
    by(fastforce simp: nat_mult_max_right)+
next
  case (WhileFalse s b c)
  hence "(2 ^ Suc (Suc 0)) * Max (range s) < 2 ^ n"
    by (meson le_less_trans max.cobounded1 move_exponent_to_rhs power_of_two_minus)
  hence "Max (range s) < 2 ^ n"
    by(auto intro: le_less_trans[OF _ \<open>(2 ^ Suc (Suc 0)) * Max (range s) < 2 ^ n\<close>])
  then show ?case using WhileFalse
    by(simp add: t_small_step_fun_terminate_iff exists_non_zero_in_var_bit_list_iff)
next
  case (WhileTrue s1 b c x s2 y s3 z)
  hence "(2 ^ z) * Max (range s1) < 2 ^ n"
    by (meson le_less_trans max.cobounded1 move_exponent_to_rhs power_of_two_minus)
  hence "Max (range s1) < 2 ^ n" by(auto intro: le_less_trans[OF _ \<open>2 ^ z * Max (range s1) < 2 ^ n\<close>])
  have "(2 :: nat) ^ x \<le> 2 ^ z" using WhileTrue by simp
  hence "((2 :: nat) ^ x) * max (Max (range s1)) (max_constant (WHILE b\<noteq>0 DO c)) < 2 ^ n"
    using \<open>2 ^ z * max (Max (range s1)) (max_constant (WHILE b\<noteq>0 DO c)) < 2 ^ n\<close>
    by (meson leD leI less_le_trans mult_less_cancel2)
  hence "2 ^ x * max (Max (range s1)) (max_constant c) < 2 ^ n" by (simp add: nat_mult_max_right)
  have "max (Max (range s1)) (max_constant c) < 2 ^ (n - z)"
    using power_of_two_minus WhileTrue by (metis Max_Constant.max_constant.simps)
  have "Max (range s2) < 2 ^ (n - (y + 1))"
    using IMP_space_growth[OF \<open>(c, s1) \<Rightarrow>\<^bsup> x \<^esup> s2\<close> \<open>finite (range s1)\<close>
        \<open>max (Max (range s1)) (max_constant c) < 2 ^ (n - z)\<close>] \<open>1 + x + y = z\<close> \<open>n > z \<close> by auto
  hence "2 ^ (y + 1) * Max (range s2) < 2 ^ n" using move_exponent_to_rhs by blast
  moreover have "2 ^ (y + 1) * max_constant  (WHILE b\<noteq>0 DO c) < 2 ^ n"
    using \<open>1 + x + y = z\<close> \<open>2 ^ z * max (Max (range s1)) (max_constant (WHILE b\<noteq>0 DO c)) < 2 ^ n\<close>
      power_of_two_increase_exponent_le[where ?a="1 + y" and ?b=x]
    by(auto simp: add.commute nat_mult_max_right)
  ultimately have "2 ^ (y + 1) * max (Max (range s2)) (max_constant (WHILE b\<noteq>0 DO c)) < 2 ^ n"
    by simp
  moreover have "finite (range s2)" using finite_range_stays_finite WhileTrue by simp
  ultimately show ?case using Seq \<open>2 ^ x * max (Max (range s1)) (max_constant c) < 2 ^ n\<close>
    apply(simp only: t_small_step_fun_terminate_iff)
    using \<open>s1 b \<noteq> 0\<close> \<open>finite (range s1)\<close> \<open>Max (range s1) < 2 ^ n\<close>
    apply(simp add: exists_non_zero_in_var_bit_list_iff)
    apply(rule seq_terminates_when[where ?t1.0="100 * n * (x - Suc 0) + 50" and
          ?t2.0="100 * n * (y - Suc 0) + 50"])
      using WhileTrue
    using bigstep_progress by(auto simp: algebra_simps)
qed auto

text \<open>The other direction. Observe that we assume that the IMP program terminates after a limited
      number of steps, that is, we don't show that termination of the IMP program follows from
      termination of the translated IMP- program \<close>

lemma IMP_Minus_To_IMP_aux:
  assumes "(c :: IMP_com, s1) \<Rightarrow>\<^bsup>t'\<^esup> s2"
    "t' \<le> t"
    "finite (range s1)"
    "n > t"
    "((2 :: nat) ^ t) * (max (Max (range s1)) (max_constant c)) < 2 ^ n"
    "t_small_step_fun t''
      (IMP_To_IMP_Minus c n, IMP_State_To_IMP_Minus s1 n)
     = (SKIP, s2')"
  shows
    "s2' = IMP_State_To_IMP_Minus s2 n"
proof -
  have "t_small_step_fun (100 * n * (t' - 1) + 50)
      (IMP_To_IMP_Minus c n, IMP_State_To_IMP_Minus s1 n)
     = (SKIP, IMP_State_To_IMP_Minus s2 n)"
    using assms by(fastforce intro: IMP_To_IMP_Minus dual_order.strict_trans2)
  thus ?thesis by(metis Pair_inject assms less_imp_le_nat not_less t_small_step_fun_increase_time)
qed

subsection \<open>Variables\<close>

text \<open>We give a few lemmas that specify what variables appear in translated IMP- programs. \<close>

lemma IMP_To_IMP_Minus_variables:
  "n > 0 \<Longrightarrow> set (enumerate_variables (IMP_To_IMP_Minus c n)) \<subseteq>
    { var_bit_to_var (w, i) | w i. i < n \<and> w \<in> set (Max_Constant.all_variables c) }
    \<union> { operand_bit_to_var (op, i) | op i. i < n \<and> (op = CHR ''a'' \<or> op = CHR ''b'') }
    \<union> { ''carry'' }"
proof(induction c)
  case SKIP
  then show ?case by(auto simp: enumerate_variables_def)
next
  case (Assign v a)
  thus ?case using assignment_to_binary_variables[where ?n=n and ?v=v and ?a=a] by auto
next
  case (Seq c1 c2)
  then show ?case by(auto simp: set_enumerate_variables_seq)
next
  case (If x1 c1 c2)
  then show ?case by(auto simp: set_enumerate_variables_if var_bit_list_def)
next
  case (While x1 c)
  then show ?case by(auto simp: set_enumerate_variables_while var_bit_list_def)
qed

lemma card_of_set_comprehension_of_set_list: "card { f x |x. x \<in> set l} \<le> length (remdups l)"
proof(induction l)
  case (Cons a l)
  have "{ f x |x. x \<in> set (a # l)} = { f a } \<union> { f x |x. x \<in> set l}" by auto
  thus ?case using Cons apply auto
     apply (metis (mono_tags, lifting) card.infinite card_insert_if finite_insert mem_Collect_eq)
    by (metis (no_types, lifting) Suc_le_mono card.infinite card_insert_disjoint finite_insert
        insert_absorb le_SucI)
qed auto

lemma card_union_le: "card U \<le> a \<Longrightarrow> card W \<le> b \<Longrightarrow> card (U \<union> W) \<le> (a + b)"
  using card_Un_le[where ?A=U and ?B=W] by simp

lemma card_union_le_intro: "card U \<le> a \<Longrightarrow> card W \<le> b \<Longrightarrow> c \<ge> a + b \<Longrightarrow> card (U \<union> W) \<le> c"
  using card_Un_le[where ?A=U and ?B=W] by simp

lemma IMP_To_IMP_Minus_variables_length:
  assumes "n > 0"
  shows "length (enumerate_variables (IMP_To_IMP_Minus c n)) \<le>
    (n + 1) * (Max_Constant.num_variables c) + 2 * n + 1"
proof -
  have "finite { var_bit_to_var (w, i) | w i. i < n \<and> w \<in> set (Max_Constant.all_variables c) }
    \<and> card { var_bit_to_var (w, i) | w i. i < n \<and> w \<in> set (Max_Constant.all_variables c) }
    \<le> n * (Max_Constant.num_variables c)"
  proof(induction n)
    case (Suc n)
    have "{var_bit_to_var (w, i) |w i. i < Suc n \<and> w \<in> set (Max_Constant.all_variables c)}
      = {var_bit_to_var (w, i) |w i. i < n \<and> w \<in> set (Max_Constant.all_variables c)}
        \<union> { var_bit_to_var (w, n) |w. w \<in> set (Max_Constant.all_variables c) }"
      by auto
    moreover have "card {var_bit_to_var (w, n) |w. w \<in> set (Max_Constant.all_variables c)}
      \<le> num_variables c"
      using card_of_set_comprehension_of_set_list num_variables_def by fastforce
    ultimately show ?case using Suc by (simp add: card_union_le sup_commute)
  qed auto
  moreover have "card {CHR ''?'' # CHR ''$'' # w |w. w \<in> set (Max_Constant.all_variables c)}
    \<le> num_variables c" using card_of_set_comprehension_of_set_list num_variables_def by fastforce
  moreover have "finite {operand_bit_to_var (op, i) |op i. i < n \<and> (op = CHR ''a'' \<or> op = CHR ''b'')}
    \<and> card { operand_bit_to_var (op, i) |op i. i < n \<and> (op = CHR ''a'' \<or> op = CHR ''b'') } \<le> 2 * n"
  proof (induction n)
    case (Suc n)
    have "{operand_bit_to_var (op, i) |op i. i < Suc n \<and> (op = CHR ''a'' \<or> op = CHR ''b'')}
      = { operand_bit_to_var (op, i) |op i. i < n \<and> (op = CHR ''a'' \<or> op = CHR ''b'') }
        \<union> { operand_bit_to_var (CHR ''a'', n), operand_bit_to_var (CHR ''b'', n)}" by auto
    thus ?case using Suc by(auto intro!: card_insert_le_m1)
  qed auto
  ultimately have
    f: "finite ({ var_bit_to_var (w, i) | w i. i < n \<and> w \<in> set (Max_Constant.all_variables c) }
    \<union> { operand_bit_to_var (op, i) | op i. i < n \<and> (op = CHR ''a'' \<or> op = CHR ''b'') }
    \<union> { ''carry'' })" and
    "card ({ var_bit_to_var (w, i) | w i. i < n \<and> w \<in> set (Max_Constant.all_variables c) }
    \<union> { operand_bit_to_var (op, i) | op i. i < n \<and> (op = CHR ''a'' \<or> op = CHR ''b'') }
    \<union> { ''carry'' }) \<le> (n + 1) * (num_variables c) + 2 * n + 1"
    by(auto simp: card_union_le intro!: card_insert_le_m1 card_union_le_intro)
  hence "card (set (enumerate_variables (IMP_To_IMP_Minus c n)))
    \<le> (n + 1) * (num_variables c) + 2 * n + 1"
    using card_mono[OF f IMP_To_IMP_Minus_variables[OF \<open>n > 0\<close>]] by simp
  thus ?thesis by(simp add:  distinct_card[OF enumerate_variables_distinct])
qed

lemma var_bit_in_IMP_Minus_variables_then_bit_less_n: "n > 0 \<Longrightarrow> var_bit_to_var (a, b)
           \<in> set (enumerate_variables (IMP_To_IMP_Minus c n)) \<Longrightarrow> b < n"
  apply(frule set_mp[OF IMP_To_IMP_Minus_variables])
  by auto

lemma var_bit_in_IMP_Minus_variables: "v \<in> set (Max_Constant.all_variables c)
  \<Longrightarrow> i < n \<Longrightarrow> var_bit_to_var (v, i) \<in>  set (enumerate_variables (IMP_To_IMP_Minus c n))"
  apply(induction c)
  by(auto simp: assignment_to_binary_def binary_adder_def set_enumerate_variables_seq
      copy_atom_to_operand_variables adder_def com_list_to_seq_variables full_adder_variables
      binary_subtractor_def subtract_handle_underflow_variables set_enumerate_variables_if
      var_bit_list_def set_enumerate_variables_while split: aexp.splits atomExp.splits)

end