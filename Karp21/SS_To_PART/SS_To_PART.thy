theory SS_To_PART
  imports "../XC_To_SS/XC_To_SS_aux"  "../Reductions"
begin

subsection "number_partition"

definition "part \<equiv> {as::nat list. \<exists>xs. (\<forall>i < length xs. xs!i \<in> {0, 1}) \<and> length as = length xs 
  \<and> 2 * (\<Sum>i < length as. as ! i * xs ! i) =( \<Sum>i < length as. as ! i)}"

definition "part_alter \<equiv> {as::nat list. \<exists>xs. (\<forall>i < length xs. xs!i \<in> {0, 1}) \<and> length as = length xs 
  \<and> (\<Sum>i < length as. as ! i * xs ! i) =(\<Sum>i < length as. as ! i * (1 - xs ! i))}"

definition ss_list_to_part :: "nat list * nat \<Rightarrow> nat list" where
"ss_list_to_part \<equiv> \<lambda>(as, s). (if s \<le> (\<Sum> i < length as. as ! i) then ((\<Sum>i < length as. as ! i) + 1 - s) # (s + 1) # as else [1])"

definition "size_part \<equiv> length"

subsection "the two definitions of number partition are equivalent"

lemma sum_binary_part: 
assumes  "(\<forall>i < length xs. xs!i = (0::nat) \<or> xs!i = 1)" "length as = length xs" 
shows  "(\<Sum>i < length as. as ! i * xs ! i) + (\<Sum>i < length as. as ! i * (1 - xs ! i)) = (\<Sum>i < length as. as ! i)"
proof -
  have "(\<Sum>i < length as. as ! i * xs ! i) + (\<Sum>i < length as. as ! i * (1 - xs ! i)) 
    = (\<Sum>i < length as. as ! i * xs ! i + as ! i * (1 - xs ! i))"
    by (simp add: sum.distrib)
  also have "... = (\<Sum>i < length as. as ! i * (xs ! i + 1 - xs ! i))"
    proof -
      from assms have "\<forall>i < length as. as ! i * xs ! i + as ! i * (1 - xs ! i) 
          = as ! i * (xs ! i + 1 - xs ! i)"
        by fastforce
      then show ?thesis 
        by auto
    qed 
  finally show ?thesis
    by auto
qed 

lemma part_subseteq_part_alter:
"as \<in> part \<Longrightarrow> as \<in> part_alter"
proof -
  assume "as \<in> part"
  then obtain xs where xs_def: "(\<forall>i < length xs. xs!i \<in> {0, 1})" "length as = length xs "
    "2 * (\<Sum>i < length as. as ! i * xs ! i) = (\<Sum>i < length as. as ! i)"
    unfolding part_def 
    by blast 
  then have "(\<Sum>i < length as. as ! i * xs ! i) + (\<Sum>i < length as. as ! i * (1 - xs ! i))
   = (\<Sum>i < length as. as ! i)"
   using sum_binary_part 
   by blast 
  with xs_def show "as \<in> part_alter"
    unfolding part_alter_def
    by auto
qed

lemma part_alter_subseteq_part:
"as \<in> part_alter \<Longrightarrow> as \<in> part"
proof -
  assume "as \<in> part_alter"
  then obtain xs where xs_def: "(\<forall>i < length xs. xs!i \<in> {0, 1})" "length as = length xs "
    "(\<Sum>i<length as. as ! i * xs ! i) = (\<Sum>i<length as. as ! i * (1 - xs ! i))"
    unfolding part_alter_def
    by blast 
  moreover then have "(\<Sum>i<length as. as ! i * xs ! i) + (\<Sum>i<length as. as ! i * (1 - xs ! i)) 
    = (\<Sum>i < length as. as ! i)"
    using sum_binary_part
    by blast 
  ultimately have "2 * (\<Sum>i < length as. as ! i * xs ! i) = (\<Sum>i < length as. as ! i)"
    by linarith
  with xs_def show "as \<in> part"
    unfolding part_def 
    by blast 
qed

theorem part_eq_part_alter:
"part = part_alter"
using part_alter_subseteq_part part_subseteq_part_alter 
  by blast



subsection "the reduction from subset sum to number partition is correct"

lemma ss_list_to_part_sound:
assumes "(as, s) \<in> subset_sum_list"
shows "ss_list_to_part (as, s) \<in> part"
proof (cases "s \<le> (\<Sum> i < length as. as ! i)")
  case True 
  from assms obtain xs where xs_def:
  "(\<forall>i<length xs. xs ! i \<in> {0, 1})" 
  "(\<Sum>i<length as. as ! i * xs ! i) = s" 
  "length xs = length as"
    unfolding subset_sum_list_def
    by blast 
  
  obtain bs ys where by_def:
  "bs = ((\<Sum>i < length as. as ! i) + 1 - s) # (s + 1) # as"
  "ys = 1 # 0 # xs"
    by blast

  have *: "length bs = length ys"
    using xs_def(3) by_def
    by force 
  from xs_def(1) have "set xs \<subseteq> {0, 1}"
    by (induction xs) fastforce+
  hence "set (1 # 0 # xs) = {0, 1}"
    by auto
  hence **: "\<forall>i < length ys. ys ! i \<in> {0, 1}"
    using nth_mem by_def
    by metis

  have "(\<Sum>i < length bs. bs ! i * ys ! i) = (\<Sum>i <length xs + 2. bs ! i * ys ! i)"
    using by_def(2) *
    by auto
  also have "... = (bs ! 0 * ys ! 0) + (\<Sum>i < length xs + 1. bs ! (i+1) * ys ! (i+1))"
    using sum.lessThan_Suc_shift
    by auto 
  also have "... = (bs ! 0 * ys ! 0) + (bs ! 1 * ys ! 1) + (\<Sum>i < length xs. bs ! (i+2) * ys ! (i+2))"
    using sum.lessThan_Suc_shift
    by auto 
  also have "... = (\<Sum>i < length as. as ! i) + 1"
    using by_def xs_def(2-3) True
    by auto
  finally have ***:"(\<Sum>i < length bs. bs ! i * ys ! i) = (\<Sum>i < length as. as ! i) + 1"
    by blast 

  have "(\<Sum>i < length bs. bs ! i) = (\<Sum>i < length xs + 2. bs ! i)"
    using * by_def(2)
    by force 
  also have "... = bs ! 0 + (\<Sum>i < length xs + 1. bs ! (i+1))"
    using sum.lessThan_Suc_shift
    by auto
  also have "... = bs ! 0 + bs ! 1 + (\<Sum>i < length xs. bs ! (i+2))"
    using sum.lessThan_Suc_shift
    by auto
  also have "... = (\<Sum>i < length as. as ! i) + 1 + 1 + (\<Sum>i < length as. as ! i)"
    using xs_def by_def True
    by auto
  finally have "(\<Sum>i < length bs. bs ! i) = 2 * ((\<Sum>i < length as. as ! i) + 1)"
    by presburger

  with *** have "2 * (\<Sum>i < length bs. bs ! i * ys ! i) = (\<Sum>i < length bs. bs ! i)"
    by argo

   with * ** have "bs \<in> part"
    unfolding part_def 
    by blast   
  with True show ?thesis
    unfolding ss_list_to_part_def 
    using by_def
    by fastforce
next 
  case False 
  from assms obtain xs where xs_def:
  "(\<forall>i<length xs. xs ! i \<in> {0, 1})" 
  "(\<Sum>i<length as. as ! i * xs ! i) = s" 
  "length xs = length as"
    unfolding subset_sum_list_def
    by blast 
  hence "\<And>i. i < length as \<Longrightarrow> as ! i * xs ! i \<le> as ! i"
    by auto
  hence "(\<Sum>i<length as. as ! i * xs ! i) \<le> (\<Sum>i<length as. as ! i)"
    using sum_mono[of "{..<length as}" "\<lambda>i. as ! i * xs ! i" "\<lambda>i. as ! i"]
    by blast
  with xs_def have s_up: "s \<le> (\<Sum>i<length as. as ! i)"
    by blast
  with False show ?thesis
    unfolding part_def ss_list_to_part_def 
    by argo
qed 

lemma ss_list_to_part_complete:
assumes "ss_list_to_part (as, s) \<in> part"
shows "(as, s) \<in> subset_sum_list"
proof (cases "s \<le> (\<Sum> i < length as. as ! i)")
  case True 
  obtain bs where bs_def: "bs = ss_list_to_part (as, s)"
    by blast 
  with assms obtain ys where ys_def: 
  "(\<forall>i < length ys. ys!i = 0 \<or> ys!i = 1 )" "length bs = length ys"
  "2 * (\<Sum>i < length bs. bs ! i * ys ! i) = (\<Sum>i < length bs. bs ! i)"
    unfolding part_def
    by blast
  from True this(2) bs_def have "length ys = length as + 2"
    unfolding ss_list_to_part_def
    by force
  with ys_def(1) have "\<And>i. i < length as \<Longrightarrow> ys ! (i + 2) \<in> {0, 1}"
    unfolding ss_list_to_part_def 
    by simp
  hence i_up: "\<And>i. i \<in> {..<length as} \<Longrightarrow> as ! i * ys ! (i + 2) \<le> as ! i"
    by force 

  from True have "(\<Sum>i < length bs. bs ! i * ys ! i) = (\<Sum>i <length as + 2. bs ! i * ys ! i)"
    using bs_def 
    unfolding ss_list_to_part_def
    by auto
  also have "... = (bs ! 0 * ys ! 0) + (\<Sum>i < length as + 1. bs ! (i+1) * ys ! (i+1))"
    using sum.lessThan_Suc_shift
    by auto 
  also have "... = (bs ! 0 * ys ! 0) + (bs ! 1 * ys ! 1) + (\<Sum>i < length as. bs ! (i+2) * ys ! (i+2))"
    using sum.lessThan_Suc_shift
    by auto
  finally have *: "(\<Sum>i < length bs. bs ! i * ys ! i) 
    = (bs ! 0 * ys ! 0) + (bs ! 1 * ys ! 1) + (\<Sum>i < length as. bs ! (i+2) * ys ! (i+2))"
    by blast

  from True have "(\<Sum>i < length bs. bs ! i) = (\<Sum>i < length as + 2. bs ! i)"
    using bs_def
    unfolding ss_list_to_part_def
    by force 
  also have "... = bs ! 0 + (\<Sum>i < length as + 1. bs ! (i+1))"
    using sum.lessThan_Suc_shift
    by auto
  also have "... = bs ! 0 + bs ! 1 + (\<Sum>i < length as. bs ! (i+2))"
    using sum.lessThan_Suc_shift
    by auto
  also have "... = (\<Sum>i < length as. as ! i) + 1 + 1 + (\<Sum>i < length as. as ! i)"
    using bs_def True
    unfolding ss_list_to_part_def
    by fastforce 
  finally have "(\<Sum>i < length bs. bs ! i) = 2 * ((\<Sum>i < length as. as ! i) + 1)"
    by presburger
  hence **: "(\<Sum>i < length bs. bs ! i * ys ! i) = ((\<Sum>i < length as. as ! i) + 1)"
    using ys_def(3)
    by algebra
  
  from True have ***: "bs ! 0 = (\<Sum>i < length as. as ! i) + 1 - s" "bs ! 1 = (s + 1)"
    using bs_def 
    unfolding ss_list_to_part_def 
    by auto

  from True ys_def(2) have "length ys > 1"
    using bs_def
    unfolding ss_list_to_part_def
    by force 
  with ys_def(1) have "ys ! 0 \<in> {0, 1}" "ys ! 1 \<in> {0, 1}"
    by fastforce+
  then consider 
  "ys ! 0 = 1 \<and> ys ! 1 = 1" | "ys ! 0 = 1 \<and> ys ! 1 = 0" |
  "ys ! 0 = 0 \<and> ys ! 1 = 1" | "ys ! 0 = 0 \<and> ys ! 1 = 0"
    by blast 
  then have "(ys ! 0 = 1 \<and> ys ! 1 = 0) \<or> (ys ! 0 = 0 \<and> ys ! 1 = 1)"
  proof (cases)
    case 1
    with * *** have "(\<Sum>i < length bs. bs ! i * ys ! i) 
    = ((\<Sum>i < length as. as ! i) + 1 - s) + (s + 1) + (\<Sum>i < length as. bs ! (i+2) * ys ! (i+2))"
      by algebra
    also have "... = (\<Sum>i < length as. as ! i) + 2 + (\<Sum>i < length as. as ! i * ys ! (i+2))"
      using bs_def True
      unfolding ss_list_to_part_def
      by simp
    finally have "(\<Sum>i < length bs. bs ! i * ys ! i) 
      = (\<Sum>i < length as. as ! i) + 2 + (\<Sum>i < length as. as ! i * ys ! (i+2))"
      by blast 
    with ** have "False"
      by linarith
    then show ?thesis
      by blast
  next
    case 4
    with * *** have "(\<Sum>i < length bs. bs ! i * ys ! i) = (\<Sum>i < length as. bs ! (i+2) * ys ! (i+2))"
      by algebra
    also have "... = (\<Sum>i < length as. as ! i * ys ! (i+2))"
      using bs_def True
      unfolding ss_list_to_part_def 
      by simp
    also have "... \<le> (\<Sum>i < length as. as ! i)"
      using sum_mono i_up
      by meson
    finally have "(\<Sum>i < length bs. bs ! i * ys ! i) \<le> (\<Sum>i < length as. as ! i)"
      by blast
    with ** have "False"
      by presburger
    then show ?thesis
      by blast
  qed simp+
  then consider "ys ! 0 = 1 \<and> ys ! 1 = 0" | "ys ! 0 = 0 \<and> ys ! 1 = 1 "
    by blast
  then show ?thesis
  proof (cases)
    obtain xs where xs_def: "xs = tl (tl ys)"
      by blast
    case 1
    with xs_def have prems: "\<forall>i < length xs. xs!i \<in> {0, 1}" "length xs = length as"
      using \<open>length ys = length as + 2\<close> \<open>\<And>i. i < length as \<Longrightarrow> ys ! (i + 2) \<in> {0, 1}\<close>
      by (auto, metis Misc.nth_tl Zero_not_Suc diff_Suc_1 length_0_conv length_tl)
    from 1 * *** have "(\<Sum>i < length bs. bs ! i * ys ! i) 
    = ((\<Sum>i < length as. as ! i) + 1 - s)  + (\<Sum>i < length as. bs ! (i+2) * ys ! (i+2))"
      by algebra
    with True ** have "(\<Sum>i < length as. bs ! (i+2) * ys ! (i+2)) = s"
      by linarith
    hence "(\<Sum>i < length as. as ! i * ys ! (i+2)) = s"
      using bs_def True
      unfolding ss_list_to_part_def
      by simp
    moreover have "\<forall>i < length as. xs ! i = ys ! (i + 2)"
      using xs_def \<open>length ys = length as + 2\<close> 
      by (simp add: List.nth_tl)
    ultimately have "(\<Sum>i < length as. as ! i * xs ! i) = s"
      by simp
    with prems show ?thesis
      unfolding subset_sum_list_def
      by blast
  next
    obtain zs where zs_def: "zs = map (\<lambda>x. 1 - x) ys"
      by blast
    obtain xs where xs_def: "xs = tl (tl zs)"
      by blast
    case 2
    from zs_def have "length zs = length as + 2" 
    "\<And>i. i < length as \<Longrightarrow> zs ! (i + 2) \<in> {0, 1}"
      using \<open>length ys = length as + 2\<close> \<open>\<And>i. i < length as \<Longrightarrow> ys ! (i + 2) \<in> {0, 1}\<close>
      by auto
    with xs_def have prems: "\<forall>i < length xs. xs!i \<in> {0, 1}" "length xs = length as"
      by (auto, metis Misc.nth_tl Zero_not_Suc diff_Suc_1 length_0_conv length_tl)
    have "(\<Sum>i < length bs. bs ! i * ys ! i) 
      + (\<Sum>i < length bs. bs ! i * (1 - ys ! i)) = (\<Sum>i < length bs. bs ! i)"
      using ys_def(1, 2) sum_binary_part
      by auto
    with ys_def(3) have flip_eq: "(\<Sum>i < length bs. bs ! i * ys ! i) = (\<Sum>i < length bs. bs ! i * (1 - ys ! i))"
        by linarith

    from True have "(\<Sum>i < length bs. bs ! i * (1 - ys ! i)) = (\<Sum>i <length as + 2. bs ! i * (1 - ys ! i))"
      using bs_def 
      unfolding ss_list_to_part_def
      by auto
    also have "... = (bs ! 0 * (1 - ys ! 0)) + (\<Sum>i < length as + 1. bs ! (i+1) * (1 - ys ! (i + 1)))"
      using sum.lessThan_Suc_shift 
      by auto 
    also have "... = (bs ! 0 * (1 - ys ! 0)) + (bs ! 1 * (1 - ys ! 1)) + (\<Sum>i < length as. bs ! (i+2) * (1 - ys ! (i + 2)))"
      using sum.lessThan_Suc_shift
      by auto
    also have "... = (\<Sum>i < length as. as ! i) + 1 - s + (\<Sum>i < length as. bs ! (i+2) * (1 - ys ! (i + 2)))"
      using *** 2
      by presburger
    finally have "(\<Sum>i < length bs. bs ! i * (1 - ys ! i)) 
      = (\<Sum>i < length as. as ! i) + 1 - s + (\<Sum>i < length as. bs ! (i+2) * (1 - ys ! (i + 2)))"
      by blast 
    with True ** flip_eq have "(\<Sum>i < length as. bs ! (i+2) * (1 - ys ! (i + 2))) = s"
      by linarith
    with True bs_def have "(\<Sum>i < length as. as ! i * (1 - ys ! (i + 2))) = s"
      unfolding ss_list_to_part_def 
      by force
    moreover have "\<forall>i < length as. 1 - ys ! (i+2) = zs ! (i+2)"
      using zs_def ys_def(1-2) True bs_def
      unfolding ss_list_to_part_def
      by auto
    moreover have "\<forall>i < length as. xs ! i = zs ! (i + 2)"
      using xs_def \<open>length zs = length as + 2\<close> 
      by (simp add: List.nth_tl)
    ultimately have "(\<Sum>i < length as. as ! i * xs ! i) = s"
      by simp
    with prems show ?thesis
      unfolding subset_sum_list_def 
      by blast
  qed
next 
  case False 
  with assms show ?thesis
    unfolding ss_list_to_part_def part_def
    by simp
qed 


theorem is_reduction_ss_list_to_part:
"is_reduction ss_list_to_part subset_sum_list part"
  unfolding is_reduction_def 
  using ss_list_to_part_sound ss_list_to_part_complete
  by fast

end