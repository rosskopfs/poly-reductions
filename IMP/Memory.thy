\<^marker>\<open>creator Florian Kessler\<close>

theory Memory
  imports Big_Step_Small_Step_Equivalence "HOL-Library.Discrete_Functions" Max_Constant
begin

text \<open> We give a definition for the amount of memory that an IMP program uses during its
       execution, and show that there is a bound that is linear in the number of steps the
       execution takes. \<close>

definition bit_length where "bit_length x \<equiv>  floor_log x + 1"

lemma bit_length_monotonic: "x \<le> y \<Longrightarrow> bit_length x \<le> bit_length y"
  by(auto simp: bit_length_def floor_log_le_iff)

lemma bit_length_of_power_of_two: "y > 0 \<Longrightarrow> bit_length (2 ^ x * y) = x + bit_length y"
  apply(induction x)
  by(auto simp: bit_length_def mult.assoc)

text \<open> The amount of memory a single state uses. Note that we only consider registers that
       can be accessed by the program, hence the additional parameter 'c' in this definition. \<close>

definition state_memory :: "com \<Rightarrow> state \<Rightarrow> nat" where
"state_memory c s = fold (+) (map (\<lambda> r. bit_length (s r)) (remdups (all_variables c))) 0"

text \<open> We define something to be a memory bound for a program and an initial state, if it
       bounds every state that is reachable. \<close>

definition is_memory_bound :: "com \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> bool" where
"is_memory_bound c s n \<equiv> (\<forall> t c' s'. (c, s) \<rightarrow>\<^bsup>t\<^esup> (c', s') \<longrightarrow> state_memory c' s' \<le> n)"

lemma x_leq_fold_max_l_x: "(x :: nat) \<le> fold max l x"
proof(induction l arbitrary: x)
  case (Cons a l)
  then show ?case by (auto intro: le_trans[where ?j = "max a x"])
qed auto

lemma fold_max_l_x_le_l_y: "(x :: nat) \<le> y \<Longrightarrow> fold max l x \<le> fold max l y"
  by (induction l arbitrary: x y) auto

lemma sum_of_list_leq_length_times_max: "length l * fold max l (0 :: nat) \<le> k \<Longrightarrow> fold (+) l 0 \<le> k"
proof(induction l arbitrary: k)
  case (Cons a l)
  let ?k = "length l * fold max l (0 :: nat)"
  have "fold (+) (a # l) 0 = a + fold (+) l 0" by (simp add: fold_plus_sum_list_rev)
  also have "... \<le> a + ?k" using Cons.IH[where ?k="?k"] by simp
  also have "... \<le> fold max l a + ?k"
    using x_leq_fold_max_l_x by simp
  also have "... \<le> fold max l a + length l * fold max l a"
    using fold_max_l_x_le_l_y by simp
  finally show ?case using Cons by auto
qed auto

lemma max_bit_length_bit_length: "max (bit_length x) (bit_length y) = bit_length (max x y)"
  by (simp add: bit_length_def floor_log_mono max_of_mono)

lemma fold_max_map_bit_length: "l \<noteq> []
  \<Longrightarrow> fold max (map (\<lambda>x. bit_length (f x)) l) (bit_length a) = bit_length (fold max (map f l) a)"
proof(induction l arbitrary: a)
  case (Cons a l)
  then show ?case by (cases l) (auto simp: max_bit_length_bit_length)
qed auto

lemma fold_max_map_bit_length':
  assumes "l \<noteq> []"
  shows "fold max (map (\<lambda>x. bit_length (f x)) l) 0 = bit_length (fold max (map f l) 0)"
  using assms proof(induction l)
  case (Cons a l)
  then show ?case
    apply(auto simp: max_bit_length_bit_length)
    apply(cases l)
     apply simp
    apply(rule fold_max_map_bit_length )
    by simp
qed auto

lemma remdups_non_empty_iff[simp]: "remdups l \<noteq> [] \<longleftrightarrow> l \<noteq> []"
  by (induction l) auto

lemma fold_max_map_le_Max_range:
  "finite (range (f :: _ \<Rightarrow> nat)) \<Longrightarrow> fold max (map f l) x \<le> max x (Max (range f))"
  apply(induction l arbitrary: x)
   apply auto
  by (smt Max.in_idem max.assoc max.commute rangeI)

lemma fold_max_map_le_Max_range':
  "finite (range (f :: _ \<Rightarrow> nat)) \<Longrightarrow> fold max (map f l) 0 \<le> Max (range f)"
  using fold_max_map_le_Max_range
  by (metis max_0L)

lemma Max_register_bounds_state_memory: "finite (range s)
  \<Longrightarrow> state_memory c s \<le> num_variables c * bit_length (Max (range s))"
  by(auto simp: num_variables_def fold_max_map_bit_length' state_memory_def
          intro!: bit_length_monotonic fold_max_map_le_Max_range' sum_of_list_leq_length_times_max)

lemma finite_range_stays_finite_step: "(c1, s1) \<rightarrow> (c2, s2) \<Longrightarrow> finite (range s1)
  \<Longrightarrow> finite (range s2)"
proof(induction c1 s1 c2 s2 rule: small_step_induct)
  case (Assign x a s)
  then show ?case
    by (auto intro: finite_subset[where ?B = "range s"])
qed auto

lemma finite_range_stays_finite: "(c1, s1) \<rightarrow>\<^bsup>t\<^esup> (c2, s2) \<Longrightarrow> finite (range s1)
  \<Longrightarrow> finite (range s2)"
  apply(induction t arbitrary: c1 s1)
   using finite_range_stays_finite_step by auto

lemma Max_insert_le_when: "finite (range (s :: vname \<Rightarrow> nat)) \<Longrightarrow> y \<le> r \<Longrightarrow>  Max (range s) \<le> r
  \<Longrightarrow> Max (range (s(x := y))) \<le> r"
  apply auto
  apply(subst Max_insert)
    apply(metis Un_infinite image_Un sup_top_right)
   apply(auto)
  apply(subst Max_le_iff)
    apply(metis Un_infinite image_Un sup_top_right)
  by auto

lemma le_then_sub_le: "(a :: nat) \<le> b \<Longrightarrow> a - c \<le> b" by simp

lemma one_step_Max_increase: "(c1, s1) \<rightarrow> (c2, s2) \<Longrightarrow> finite (range s1)
  \<Longrightarrow> Max (range s2) \<le> 2 * (max (Max (range s1)) (max_constant c1))"
proof (induction c1 s1 c2 s2 rule: small_step_induct)
  case (Assign x a s)
  then show ?case
  proof (cases a)
    case (A x1)
    then show ?thesis
      using \<open>finite (range s)\<close>
      by (cases x1; fastforce simp: numeral_2_eq_2 trans_le_add1 intro: Max_insert_le_when)
  next
    case (Plus x1 x2)
    then show ?thesis
      using \<open>finite (range s)\<close>
      apply(cases x1; cases x2; auto simp only: intro!: Max_insert_le_when)
      by(auto simp add: numeral_2_eq_2 max.coboundedI1 intro!: add_le_mono)
  next
    case (Sub x1 x2)
    then show ?thesis
      using \<open>finite (range s)\<close>
      apply(cases x1; cases x2; auto simp only: intro!: Max_insert_le_when)
      by(auto simp: numeral_2_eq_2 max.coboundedI1
              intro!: le_then_sub_le trans_le_add1)
  qed
next
  case (Seq2 c\<^sub>1 s c\<^sub>1' s' c\<^sub>2)
  then show ?case by simp
qed (linarith)+

lemma Max_increase: "(c1, s1) \<rightarrow>\<^bsup>t\<^esup> (c2, s2) \<Longrightarrow> finite (range s1)
  \<Longrightarrow> Max (range s2) \<le> (2 ^ t) * (max (Max (range s1)) (max_constant c1))"
proof (induction t arbitrary: c1 s1)
  case (Suc t)
  obtain c1' s1' where "(c1, s1) \<rightarrow> (c1', s1')" "(c1', s1') \<rightarrow>\<^bsup>t\<^esup> (c2, s2)"
    using \<open>(c1, s1) \<rightarrow>\<^bsup>Suc t\<^esup> (c2, s2)\<close>
    by auto
  have "Max (range s2) \<le> (2 ^ t) * (max (Max (range s1')) (max_constant c1'))"
    using Suc.IH \<open>finite (range s1)\<close>
      \<open>(c1', s1') \<rightarrow>\<^bsup>t\<^esup> (c2, s2)\<close> \<open>(c1, s1) \<rightarrow> (c1', s1')\<close>
      finite_range_stays_finite_step
    by presburger
  also have "... \<le> (2 ^ t) *
    (max (2 * (max (Max (range s1)) (max_constant c1))) (max_constant c1'))"
    using one_step_Max_increase[OF \<open>(c1, s1) \<rightarrow> (c1', s1')\<close> \<open>finite (range s1)\<close>]
    by simp
  also have "... \<le> (2 ^ Suc t) *
      (max (max (Max (range s1)) (max_constant c1))) (max_constant c1')"
    by simp
  also have "... \<le> (2 ^ Suc t) * max (Max (range s1)) (max_constant c1)"
    using max_constant_not_increasing_step[OF \<open>(c1, s1) \<rightarrow> (c1', s1')\<close>]
    by simp
  finally show ?case by simp
qed auto

text \<open> We show that there always is a linear bound for the memory consumption. \<close>

lemma linear_bound: "(c1, s1) \<Rightarrow>\<^bsup>t\<^esup> s2 \<Longrightarrow> finite (range s1)
  \<Longrightarrow> is_memory_bound c1 s1 ((num_variables c1)
      * (t + bit_length (max 1 (max (Max (range s1)) (max_constant c1)))))"
proof -
  let ?b = "(num_variables c1)
      * (t + bit_length (max 1 (max (Max (range s1)) (max_constant c1))))"

  assume "(c1, s1) \<Rightarrow>\<^bsup>t\<^esup> s2" "finite (range s1)"

  have "(c1, s1) \<rightarrow>\<^bsup>t'\<^esup> (c', s') \<Longrightarrow> state_memory c' s' \<le> ?b" for t' c' s'
  proof -
    assume "(c1, s1) \<rightarrow>\<^bsup>t'\<^esup> (c', s')"

    hence "finite (range s')"
      using \<open>finite (range s1)\<close> finite_range_stays_finite
      by auto

    have "Max (range s') \<le> (2 ^ t') * (max (Max (range s1)) (max_constant c1))"
      using Max_increase \<open>(c1, s1) \<rightarrow>\<^bsup>t'\<^esup> (c', s')\<close> \<open>finite (range s1)\<close>
      by auto
    also have "... \<le> (2 ^ t) * (max (Max (range s1)) (max_constant c1))"
      using small_step_cant_run_longer_than_big_step
        \<open>(c1, s1) \<Rightarrow>\<^bsup>t\<^esup> s2\<close> \<open>(c1, s1) \<rightarrow>\<^bsup>t'\<^esup> (c', s')\<close>
      by simp

    finally have "state_memory c' s' \<le> num_variables c'
          * bit_length ((2 ^ t) * (max (Max (range s1)) (max_constant c1)))"
      using Max_register_bounds_state_memory[OF \<open>finite (range s')\<close>]
      by (meson bit_length_monotonic dual_order.trans mult_le_cancel1)
    also have "... \<le>  num_variables c'
          * bit_length ((2 ^ t) * (max 1 (max (Max (range s1)) (max_constant c1))))"
      using bit_length_monotonic
      by simp

    finally show "state_memory c' s' \<le> ?b"
      using num_variables_not_increasing[OF \<open>(c1, s1) \<rightarrow>\<^bsup>t'\<^esup> (c', s')\<close>] order_trans
      by(fastforce simp: bit_length_of_power_of_two)
  qed

  thus ?thesis by(auto simp: is_memory_bound_def)
qed

end
