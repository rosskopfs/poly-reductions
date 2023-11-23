theory weighted_problems_aux
  imports "../XC_To_SS/XC_To_SS_aux"
begin

section "A few NP-hard combinatorics problems"

subsection "type lifting"

definition "subset_sum_int_list \<equiv> {(as,s). (\<exists>xs::int list. 
    (\<forall>i<length xs. xs!i \<in> {0,1}) \<and> (\<Sum>i<length as. as!i * xs!i) = s \<and> length xs = length as)}"

definition "ss_lift_to_int \<equiv> (\<lambda>(as, s). ((map int as), int s))"

definition "size_ss_int_list \<equiv> \<lambda>(as, s). length as + 1"

subsection "number_partition"

definition "part \<equiv> {as::nat list. \<exists>xs. (\<forall>i < length xs. xs!i \<in> {0, 1}) \<and> length as = length xs 
  \<and> 2 * (\<Sum>i < length as. as ! i * xs ! i) =( \<Sum>i < length as. as ! i)}"

definition "part_alter \<equiv> {as::nat list. \<exists>xs. (\<forall>i < length xs. xs!i \<in> {0, 1}) \<and> length as = length xs 
  \<and> (\<Sum>i < length as. as ! i * xs ! i) =(\<Sum>i < length as. as ! i * (1 - xs ! i))}"

definition ss_list_to_part :: "nat list * nat \<Rightarrow> nat list" where
"ss_list_to_part \<equiv> \<lambda>(as, s). (if s \<le> (\<Sum> i < length as. as ! i) then ((\<Sum>i < length as. as ! i) + 1 - s) # (s + 1) # as else [1])"

definition "size_part \<equiv> length"

subsection "knapsack"

definition "knapsack \<equiv> {(S, w, b, W, B). finite S \<and> (\<exists>S' \<subseteq> S. sum w S' \<le> W \<and> sum b S' \<ge> B)}"

definition "ss_to_ks \<equiv> (\<lambda>(S, w, B). (S, w, w, B, B))"

definition "size_ks \<equiv> \<lambda>(S, w, b, W, B). card S"

subsection "zero-one integer programming"

definition "zero_one_int_prog \<equiv> {(X, cs, B). \<forall>(as, s)\<in>X. 
  \<exists>xs. (\<forall>i<length xs. xs ! i \<in> {0, 1}) 
  \<and> (\<Sum>i<length as. as ! i * xs ! i) \<le> s \<and> length xs = length as 
  \<and> (\<Sum>i<length cs. cs ! i * xs ! i) \<ge> B \<and> length xs = length cs}"
(*The definition from the intracbility book by Garey and Harrison*)

definition "ss_int_list_to_zero_one_int_prog \<equiv> \<lambda>(as, s). ({(as, s)}, as, s)"

definition "size_zero_one_int_prog \<equiv> \<lambda>(X, cs, B). (length cs + 1) * card X"

subsection "a type lifting from natural numbers to integers for subset sum"

lemma subset_sum_nat_to_int_sound:
assumes "(as, s) \<in> subset_sum_list"
shows "(map int as, int s) \<in> subset_sum_int_list"
proof -
  from assms obtain xs where 
  "(\<forall>i<length xs. xs!i \<in> {0,1}) \<and> (\<Sum>i<length as. as!i * xs!i) = s \<and> length xs = length as"
    unfolding subset_sum_list_def
    by blast 
  hence "(\<forall>i<length (map int xs).(map int xs)! i \<in> {0,1}) 
    \<and> (\<Sum>i<length (map int as). (map int as)! i * (map int xs) ! i) = int s 
    \<and> length (map int xs) = length (map int as)"
    by force
  then show ?thesis
    unfolding subset_sum_int_list_def
    by blast
qed 

lemma subset_sum_nat_to_int_complete:
assumes "(map int as, int s) \<in> subset_sum_int_list"
shows "(as, s) \<in> subset_sum_list"
proof -
  from assms obtain xs where xs_def:
  "(\<forall>i<length xs. xs ! i \<in> {0,1})"
    "(\<Sum>i<length (map int as). (map int as)! i * xs ! i) = int s"
    "length xs = length (map int as)"
    unfolding subset_sum_int_list_def
    by fast 
  from this(1) have "\<exists>ys. map int ys = xs"
    proof (induction xs)
      case (Cons a xs)
      then obtain ys where "map int ys = xs"
        by fastforce 
      moreover from Cons(2) have "a = 1 \<or> a = 0"
        by auto
      ultimately have "map int ((if a = 1 then 1 :: nat else 0 )# ys) = a # xs"
        by fastforce
      then show ?case
        by metis
    qed simp
  then obtain ys where "map int ys = xs"
    by blast
  with xs_def have "(\<forall>i<length ys. ys! i \<in> {0,1}) 
    \<and> (\<Sum>i<length as. as! i * ys ! i) = s 
    \<and> length ys = length as"
    by (auto, smt (verit) of_nat_eq_iff of_nat_mult of_nat_sum sum.cong)
  then show ?thesis 
    unfolding subset_sum_list_def
    by blast
qed 

lemma is_reduction_ss_lift_to_int:
"is_reduction ss_lift_to_int subset_sum_list subset_sum_int_list"
  unfolding is_reduction_def ss_lift_to_int_def
  using subset_sum_nat_to_int_sound subset_sum_nat_to_int_complete
  by auto

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


end 