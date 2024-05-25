theory List_Extra
  imports Main
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

end