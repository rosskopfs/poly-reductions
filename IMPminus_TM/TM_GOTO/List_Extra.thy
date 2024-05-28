theory List_Extra
  imports Main "IMPminus_TM-Def.Global_Defs"
begin

lemma length_concat_same_length:
  "\<forall>xs \<in> set xss. length xs = len \<Longrightarrow> length (concat xss) = len * length xss"
proof -
  assume "\<forall>xs \<in> set xss. length xs = len"
  then have "map length xss = replicate (length xss) len"
    using map_replicate_const [where ?k = len and ?lst = xss]
    by (metis map_eq_conv)
  moreover
  have "sum_list (replicate (length xss) len) = (length xss) * len"
    by (simp add: sum_list_replicate)
  ultimately
  show "length (concat xss) = len * length xss"
    by (simp add: length_concat)
qed

lemma drop_concat_same_length:
  "\<forall>xs \<in> set xss. length xs = len \<Longrightarrow> drop (len * n) (concat xss) = concat (drop n xss)"
proof (induction xss arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons xs xss)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis by auto
  next
    case (Suc m)
    with \<open>\<forall>xs\<in>set (xs # xss). length xs = len\<close>
    have "drop (len * (Suc m)) (concat (xs # xss)) = drop (len * m) (concat xss)"
      by auto
    moreover
    have "concat (drop (Suc m) (xs # xss)) = concat (drop m xss)"
      by simp
    moreover
    from Cons have "drop (len * m) (concat xss) = concat (drop m xss)"
      by auto
    ultimately
    show ?thesis
      using \<open>n = Suc m\<close> by presburger
  qed
qed

lemma take_concat_same_length:
  "\<forall>xs \<in> set xss. length xs = len \<Longrightarrow> take (len * n) (concat xss) = concat (take n xss)"
proof (induction xss arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons xs xss)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis by auto
  next
    case (Suc m)
    with \<open>\<forall>xs\<in>set (xs # xss). length xs = len\<close>
    have "take (len * (Suc m)) (concat (xs # xss)) = xs @ take (len * m) (concat xss)"
      by auto
    moreover
    have "concat (take (Suc m) (xs # xss)) = xs @ concat (take m xss)"
      by simp
    moreover
    from Cons have "take (len * m) (concat xss) = concat (take m xss)"
      by auto
    ultimately
    show ?thesis
      using \<open>n = Suc m\<close> by presburger
  qed
qed

lemma concat_take_1_is_hd: "xss \<noteq> [] \<Longrightarrow> concat (take 1 xss) = hd xss"
  by (induction xss) auto

lemma mem_set_product_lists_replicate':
  "set ys \<subseteq> set xs \<Longrightarrow> ys \<in> set (product_lists (replicate (length ys) xs))"
  by (induction ys) auto

lemma mem_set_product_lists_replicate[intro]:
  "\<forall>i < len. ys ! i \<in> set xs \<Longrightarrow> len = length ys \<Longrightarrow>
   ys \<in> set (product_lists (replicate len xs))"
  using mem_set_product_lists_replicate'
  by (metis in_set_conv_nth subset_code(1))

lemma inth_concat_same_length [simp]:
  assumes same_length: "\<forall>xs \<in> set xss. length xs = len"
      and "0 < i \<and> i \<le> len"
      and "n < length xss"
    shows "concat xss !! (n * len + i) = (xss ! n) !! i"
  using assms
proof -
  from \<open>n < length xss\<close> same_length have "drop (n * len) (concat xss) = concat (drop n xss)"
    using drop_concat_same_length
    by (metis mult.commute)
  also have "take len ... = concat (take 1 (drop n xss))"
    using same_length take_concat_same_length
    by (metis in_set_dropD nat_mult_1_right)
  also have "... = hd (drop n xss)"
    using concat_take_1_is_hd \<open>n < length xss\<close>
    by (metis Cons_nth_drop_Suc neq_Nil_conv)
  also have "... = xss ! n"
    using \<open>n < length xss\<close> hd_drop_conv_nth by blast
  finally have "take len (drop (n * len) (concat xss)) = xss ! n"
    by blast

  from \<open>0 < i \<and> i \<le> len\<close> have "0 < n * len + i" by blast
  moreover
  from same_length have "length (concat xss) = length xss * len"
    using length_concat_same_length
    by (metis mult.commute)
  with \<open>n < length xss\<close> have "(n + 1) * len \<le> length (concat xss)"
    by (metis Suc_eq_plus1 less_eq_Suc_le mult_le_mono1)
  with \<open>0 < i \<and> i \<le> len\<close> have "n * len + i \<le> length (concat xss)"
    by fastforce
  ultimately
  have "concat xss !! (n * len + i) = concat xss ! (n * len + (i - 1))"
    using inth_nth [where ?i = "n * len + i" and ?xs = "concat xss"]
    using assms(2) by force

  also have "... = (drop (n * len) (concat xss)) ! (i - 1)"
    using \<open>n * len + i \<le> length (concat xss)\<close> by auto
  also have "... = (take len (drop (n * len) (concat xss))) ! (i - 1)"
    by (metis antisym_conv2 assms(2) diff_less nth_take order.strict_trans zero_less_one)
  with \<open>take len (drop (n * len) (concat xss)) = xss ! n\<close>
       \<open>concat xss !! (n * len + i) = concat xss ! (n * len + (i - 1))\<close>
  have "concat xss !! (n * len + i) = (xss ! n) ! (i - 1)"
    using calculation by presburger
  then show ?thesis
    using inth_nth
    by (metis assms(2) assms(3) nth_mem same_length)
qed


lemma nth_concat_same_length [simp]:
  assumes same_length: "\<forall>xs \<in> set xss. length xs = len"
      and "i < len"
      and "n < length xss"
    shows "concat xss ! (n * len + i) = (xss ! n) ! i"
  using assms
proof -
  from \<open>n < length xss\<close> same_length have "drop (n * len) (concat xss) = concat (drop n xss)"
    using drop_concat_same_length
    by (metis mult.commute)
  also have "take len ... = concat (take 1 (drop n xss))"
    using same_length take_concat_same_length
    by (metis in_set_dropD nat_mult_1_right)
  also have "... = hd (drop n xss)"
    using concat_take_1_is_hd \<open>n < length xss\<close>
    by (metis Cons_nth_drop_Suc neq_Nil_conv)
  also have "... = xss ! n"
    using \<open>n < length xss\<close> hd_drop_conv_nth by blast
  finally have "take len (drop (n * len) (concat xss)) = xss ! n"
    by blast
  moreover
  from same_length have "length (concat xss) = length xss * len"
    using length_concat_same_length
    by (metis mult.commute)
  with \<open>n < length xss\<close> have "n * len < length (concat xss)"
    using \<open>i < len\<close> by auto
  then have "concat xss ! (n * len + i) = drop (n * len) (concat xss) ! i"
    using nth_drop [where ?n = "n * len" and ?xs = "concat xss" and ?i = i]
    by simp
(*Q:
Vacuous calculation result: take len (drop (n * len) (concat xss)) = xss ! n
derived as projection (1) from:
    take len (drop (n * len) (concat xss)) = xss ! n
    concat xss ! (n * len + i) = drop (n * len) (concat xss) ! i
  also have "... = take len (drop (n * len) (concat xss)) ! i"
    using \<open>i < len\<close> by auto
*)
  then have "concat xss ! (n * len + i) = take len (drop (n * len) (concat xss)) ! i"
    using \<open>i < len\<close> by auto
  ultimately
  show ?thesis by argo
qed

lemma nth_last [simp]:
  "xs \<noteq> [] \<Longrightarrow> xs ! (length xs - 1) = last xs"
  by (induction xs) auto

end