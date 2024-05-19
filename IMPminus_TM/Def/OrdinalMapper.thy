theory OrdinalMapper
  imports Main
begin

fun map_to_nat :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "map_to_nat [] a = undefined" |
  "map_to_nat (x#xs) a = (if x = a then length xs else map_to_nat xs a)"

value "map_to_nat [0, 1, 2, 3, 4, 5] (5::nat)"
value "length [(0::nat), 1, 2, 3, 4, 5]"

lemma map_to_nat_bounded_above: "a \<in> set xs \<Longrightarrow> map_to_nat xs a < length xs"
  by (induction xs) auto

lemma map_to_nat_cons_index: "a \<in> set xs \<Longrightarrow> x \<noteq> a \<Longrightarrow> (x # rev xs) ! Suc (map_to_nat xs a) = a"
  apply (induction xs)
  apply auto
  apply (metis length_rev nth_append_length)
  apply (metis length_rev nth_append_length)
  subgoal for x xs 
    using nth_append[where ?xs = "rev xs" and ?ys = "[x]" and ?n = "map_to_nat xs a"]
    using map_to_nat_bounded_above
    by fastforce
  done

lemma map_to_nat_index: "a \<in> set xs \<Longrightarrow> (rev xs) ! (map_to_nat xs a) = a"
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then show ?case
    apply (auto)
    apply (metis length_rev nth_append_length)
    apply (metis length_rev nth_append_length)
    using map_to_nat_cons_index [of a xs x]
    by (metis butlast_snoc length_rev map_to_nat_bounded_above nth_butlast)
qed

lemma map_to_nat_injective:
  assumes "distinct xs"
      and "a \<in> set xs"
      and "b \<in> set xs"
    shows "map_to_nat xs a = map_to_nat xs b \<Longrightarrow> a = b"
  using assms
  apply (induction xs)
  apply simp
  by (metis map_to_nat_index)

lemma map_to_nat_surjective:
  assumes "distinct xs"
      and "i < length xs"
    shows "\<exists>x \<in> set xs. map_to_nat xs x = i"
proof -
  let ?x = "xs ! (length xs - i - 1)"
  from \<open>i < length xs\<close> have "?x \<in> set xs"
    by simp
  from \<open>i < length xs\<close> have "rev xs ! i = ?x"
    by (simp add: rev_nth)
  also have "?x = rev xs ! map_to_nat xs ?x"
    using map_to_nat_index \<open>?x \<in> set xs\<close> by metis
  finally have "rev xs ! i = rev xs ! map_to_nat xs ?x"
    by blast
  then have "map_to_nat xs ?x = i"
    using assms \<open>?x \<in> set xs\<close>
    by (metis distinct_rev length_rev map_to_nat_bounded_above nth_eq_iff_index_eq)
  with \<open>?x \<in> set xs\<close> show ?thesis by blast
qed

corollary map_to_nat_bijective:
  assumes "distinct xs"
  shows "map_to_nat xs ` (set xs) = {..< length xs}"
proof (standard; standard)
  fix i assume "i \<in> map_to_nat xs ` set xs"
  then obtain x where "x \<in> set xs" and "i = map_to_nat xs x" by blast
  then have "i < length xs"
    using map_to_nat_bounded_above by fast
  then show "i \<in> {..< length xs}" by blast
next
  fix i assume "i \<in> {..< length xs}"
  then have "i < length xs" by blast
  with assms obtain x where "x \<in> set xs" and "i = map_to_nat xs x"
    using map_to_nat_surjective by blast
  then show "i \<in> map_to_nat xs ` set xs"
    by blast
qed

lemma map_to_nat_image_card:
  "distinct xs \<Longrightarrow> card (map_to_nat xs ` (set xs)) = length xs"
  using map_to_nat_bijective by fastforce

end