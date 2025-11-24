theory Fresh
  imports "HOL-Library.Log_Nat" "HOL-Library.Char_ord" Eq_On
begin


lemma nat_induct1: assumes "P 0" "P 1" "\<And>n. P n \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> P (Suc n)" shows "P n"
  using assms nat.induct by auto


fun string_of_nat :: "nat \<Rightarrow> string" where
  "string_of_nat n = (
    if n < 10 then [char_of (n + of_char CHR ''0'')]
    else string_of_nat (n div 10) @ string_of_nat (n mod 10))"

lemma string_of_nat_simps[simp]:
  shows "n < 10 \<Longrightarrow> string_of_nat n = [char_of (n + of_char CHR ''0'')]"
  and "\<not> n < 10 \<Longrightarrow> string_of_nat n = string_of_nat (n div 10) @ string_of_nat (n mod 10)"
  by auto
declare string_of_nat.simps[simp del]

lemma string_of_nat_induct:
  assumes "\<And>n. n < 10 \<Longrightarrow> P n"
  assumes "\<And>n. \<not> n < 10 \<Longrightarrow> P (n div 10) \<Longrightarrow> P (n mod 10) \<Longrightarrow> P n"
  shows "P (n :: nat)"
proof (cases rule: string_of_nat.induct[of P n])
  case (1 n)
  then show ?case apply (cases "n < 10") using 1 assms by blast+
qed

lemma inj_string_of_nat_lt10[simp]:
  shows "inj_on string_of_nat {n. n < 10}"
  unfolding inj_on_def by simp


definition "is_digit x \<longleftrightarrow> CHR ''0'' \<le> x \<and> x \<le> CHR ''9''"

lemma string_of_nat_is_digits: assumes "x \<in> set (string_of_nat n)" shows "is_digit x"
  using assms apply (induction arbitrary: x rule: string_of_nat_induct)
  unfolding is_digit_def less_eq_char_def by auto


definition "digits n \<equiv> max 1 (floorlog 10 n)"

lemma digits_ge10_div10: assumes "\<not> n < 10" shows "digits (n div 10) + 1 = digits n"
  unfolding digits_def floorlog_def using assms apply simp
  using floor_log_div[where x = n and b = 10] Suc_nat_eq_nat_zadd1 by auto

lemma string_of_nat_len[simp]: "length (string_of_nat n) = digits n"
proof (induction n rule: string_of_nat_induct)
  case (1 n) then show ?case unfolding floorlog_def digits_def by simp
next
  case (2 n) with digits_ge10_div10 show ?case by fastforce
qed

lemma digits_ge10_gt1[simp]: assumes "\<not> n < 10" shows "digits n > 1"
  unfolding digits_def floorlog_def using assms by simp

lemma one_digit_iff[iff]: "digits n = 1 \<longleftrightarrow> n < 10"
  unfolding digits_def floorlog_def by simp

lemma digits_non0[simp]: "digits n \<noteq> 0" unfolding digits_def floorlog_def by simp

lemma digits_mod10[simp]: shows "digits (n mod 10) = 1"
  using one_digit_iff unfolding digits_def by simp


lemma inj_append1: "inj (\<lambda>xs. xs @ ys)" unfolding inj_def by blast
lemma inj_append2: "inj (\<lambda>ys. xs @ ys)" unfolding inj_def by blast

lemma inj_partition:
  fixes f I A
  assumes "\<And>i. i \<in> I ` A \<Longrightarrow> inj_on f {x. I x = i}"
  assumes "\<And>x y. I x \<noteq> I y \<Longrightarrow> f x \<noteq> f y"
  shows "inj_on f A"
proof (rule inj_onI)
  fix x y
  assume *: "x \<in> A" "f x = f y"
  show "x = y"
  proof (cases "I x = I y")
    case True
    with assms(1) \<open>x \<in> A\<close> have "inj_on f {y. I y = I x}" by blast
    then show "x = y" apply (rule inj_onD) using True \<open>f x = f y\<close> by simp_all
  next
    case False
    then show "x = y" using assms(2) \<open>f x = f y\<close> by simp
  qed
qed

lemma inj_prod: fixes A B assumes "inj_on f A" "inj_on g B"
  shows "inj_on (\<lambda>(x, y). (f x, g y)) (A \<times> B)" using assms by (simp add: inj_on_def)

lemma inj_on_append_fix_len2: "inj_on (\<lambda>(xs, ys). xs @ ys) {(xs, ys). length ys = l}"
  apply (rule inj_onCI) apply simp by (smt (verit) append_eq_append_conv case_prodE old.prod.case)


lemma inj_string_of_nat: "inj string_of_nat"
proof (rule inj_partition[where I = digits])
  fix x y
  assume "digits x \<noteq> digits y"
  then show "string_of_nat x \<noteq> string_of_nat y" using string_of_nat_len by metis
next
  fix i
  assume *: "i \<in> range digits" then have "i > 0" using digits_non0 by blast
  show "inj_on string_of_nat {x. digits x = i}"
  proof (induction i rule: nat_induct1)
    case 2
    then have "{x. digits x = 1} = {x. x < 10}" using one_digit_iff by fastforce
    then show ?case using inj_string_of_nat_lt10 by presburger
  next
    case (3 n)
    then have "Suc n \<noteq> 1" by simp
    then have x10: "\<not> x < 10" if "digits x = Suc n" for x using that one_digit_iff by metis

    let ?part = "{x. digits x = Suc n}"

    let ?divmod = "\<lambda>(n :: nat). (n div 10, n mod 10)"
    have inj_divmod: "inj_on ?divmod ?part" by (rule inj_onCI) (metis div_mod_decomp prod.inject)

    let ?str = "\<lambda>(d, m). (string_of_nat d, string_of_nat m)"
    have sub: "?divmod ` ?part \<subseteq> ({x. digits x = n} \<times> {x. x < 10})"
    proof
      fix x
      assume "x \<in> (\<lambda>n. (n div 10, n mod 10)) ` {x. digits x = Suc n}"
      then obtain y where "x = (y div 10, y mod 10)" and "digits y = Suc n" by blast
      then moreover have "digits (y div 10) = n" "y mod 10 < 10" using x10 digits_ge10_div10 by fastforce simp
      ultimately show "x \<in> {x. digits x = n} \<times> {x. x < 10}" by simp
    qed
    have inj_str: "inj_on ?str (?divmod ` ?part)"
      apply (rule inj_on_subset[OF inj_prod sub])
      using 3 apply simp
      using inj_string_of_nat_lt10 by blast

    let ?app = "\<lambda>(d, m). d @ m"
    have inj_app: "inj_on ?app (?str ` ?divmod ` ?part)"
      using inj_on_subset[where f = ?app and A = "{(xs, ys). length ys = 1}" and B = "?str ` ?divmod ` ?part", OF inj_on_append_fix_len2] by fastforce

    have "string_of_nat = (?app o ?str o ?divmod) on ?part" apply (rule eq_onI) using x10 by simp
    moreover have "inj_on (?app o ?str o ?divmod) ?part"
      by (rule comp_inj_on[OF _ comp_inj_on, OF inj_divmod, OF inj_str, OF inj_app])
    ultimately show "inj_on string_of_nat ?part" unfolding eq_on_def using inj_on_cong by fast
  qed simp
qed

(* alternative to fresh producing easier-to-understand variable names *)
definition "fresh stale name =
  hd (filter (\<lambda>n. n \<notin> set stale) [name @ ''.'' @ string_of_nat i . i \<leftarrow> [0 ..< Suc (length stale)]])"

value "fresh [''x.0'', ''x.3'',''x.1''] ''x''"
value "fresh [''x.0'', ''x.1'',''x.2''] ''x''"
value "fresh [''x'', ''y''] ''z''"

lemma set_filter_diff[simp]: "set (filter (\<lambda>x. x \<notin> Y) xs) = set xs - Y" by auto

lemma diff_not_empty_card: assumes "card X > card Y" "finite Y" shows "X - Y \<noteq> {}"
  using assms card_mono linorder_not_less by auto

lemma inj_fresh1: "inj (\<lambda>i. name @ ''.'' @ string_of_nat i)"
proof-
  have "inj ((\<lambda>s. (name @ ''.'') @ s) o string_of_nat)"
    using inj_append2 inj_string_of_nat inj_compose by blast
  then show "inj (\<lambda>i. name @ ''.'' @ string_of_nat i)"
    unfolding comp_def using append.assoc by simp
qed

lemma
  shows fresh_in: "fresh stale name \<in> set [name @ ''.'' @ string_of_nat i . i \<leftarrow> [0 ..< Suc (length stale)]]"
  and fresh_not_in_stale: "fresh stale name \<notin> set stale"
proof-
  let ?f = "\<lambda>i. name @ ''.'' @ string_of_nat i"
  have "card (set (map ?f [0 ..< Suc (length stale)])) = card (?f ` set [0 ..< Suc (length stale)])"
    by (simp only: List.set_map)
  also have "... = card (set [0 ..< Suc (length stale)])"
    using inj_on_subset inj_fresh1 by (blast intro: card_image)
  also have "... = Suc (length stale)" by simp
  finally have "card (set (map ?f [0 ..< Suc (length stale)])) > card (set stale)"
    using List.card_length[where xs = stale] by linarith
  then have "set [name @ ''.'' @ string_of_nat i . i \<leftarrow> [0 ..< Suc (length stale)]] - set stale \<noteq> {}"
    using diff_not_empty_card by blast
  then have "fresh stale name \<in> set [name @ ''.'' @ string_of_nat i . i \<leftarrow> [0 ..< Suc (length stale)]] - set stale"
    unfolding fresh_def using hd_in_set set_filter_diff empty_set by metis
  then show
    "fresh stale name \<in> set [name @ ''.'' @ string_of_nat i . i \<leftarrow> [0 ..< Suc (length stale)]]"
    "fresh stale name \<notin> set stale"
    by blast+
qed

abbreviation "dropWhileEnd P xs \<equiv> rev (dropWhile P (rev xs))"
value "dropWhileEnd is_digit (fresh [] ''x'')"
lemma dropWhileEnd_rev: "dropWhileEnd P (rev xs) = rev (dropWhile P xs)" by simp

lemma dropwhile_pref: assumes "\<forall>x \<in> set xs. P x" "\<not> P y" shows "dropWhile P (xs @ y # ys) = y # ys"
  using assms by (induction xs) auto

lemma dropwhile_end_suff: assumes "\<forall>x \<in> set xs. P x" "\<not> P y" shows "dropWhileEnd P (ys @ y # xs) = ys @ [y]"
  using dropwhile_pref[where P = P and y = y and xs = "rev xs"] assms by simp

lemma fresh_the_name: "butlast (dropWhileEnd is_digit (fresh stale name)) = name"
proof-
  let ?v = "fresh stale name"
  have "?v \<in> set [name @ ''.'' @ string_of_nat i . i \<leftarrow> [0 ..< Suc (length stale)]]"
    using fresh_in .
  then obtain i where "?v = name @ ''.'' @ string_of_nat i" using ex_map_conv by meson
  moreover have "dropWhileEnd is_digit (name @ CHR ''.'' # string_of_nat i) = name @ ''.''"
    apply (rule dropwhile_end_suff)
    using dropwhile_end_suff string_of_nat_is_digits is_digit_def by simp_all
  ultimately show "butlast (dropWhileEnd is_digit ?v) = name" by simp
qed

lemma inj_fresh: "inj (fresh stale)" unfolding inj_def using fresh_the_name by metis

end
