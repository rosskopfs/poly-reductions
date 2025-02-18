\<^marker>\<open>creator Bilel Ghorbel, Florian Kessler\<close>

section "IMP- An even more reduced imperative language"

theory IMP_Minus_Com
  imports
    Main
    "HOL-Library.Char_ord"
    "HOL-Library.List_Lexorder"
begin

paragraph "Summary"
text\<open>Syntax definition for IMP-. Based on the syntax definition of IMP. Compared to IMP,
  we get rid of arithmetic expressions. Instead, we can only assign bit values to registers.
  For the IF and WHILE conditions, we add the possibility to specify a list of registers, such that
  the condition is considered True if at least one of the registers is non-zero. \<close>

datatype bit = Zero | One

fun nat_to_bit:: "nat \<Rightarrow> bit" where
  "nat_to_bit 0 = Zero" |
  "nat_to_bit _ = One"

lemma bit_neq_zero_iff[simp]: "x \<noteq> Zero \<longleftrightarrow> x = One" by (cases x) auto
lemma bit_neq_one_iff[simp]: "x \<noteq> One \<longleftrightarrow> x = Zero" by (cases x) auto

lemma nat_to_bit_eq_One_iff: "nat_to_bit x = One \<longleftrightarrow> x > 0"
  by (cases x) auto

lemma nat_to_bit_eq_One_iff': "One = nat_to_bit x \<longleftrightarrow> x > 0"
  by (cases x) auto

lemma nat_to_bit_eq_Zero_iff: "nat_to_bit x = Zero \<longleftrightarrow> x = 0"
  by (cases x) auto

lemma nat_to_bit_eq_Zero_iff': "Zero = nat_to_bit x \<longleftrightarrow> x = 0"
  by (cases x) auto

lemmas nat_to_bit_cases = nat_to_bit_eq_One_iff nat_to_bit_eq_One_iff' nat_to_bit_eq_Zero_iff
  nat_to_bit_eq_Zero_iff'

type_synonym vname = string

datatype
  com = SKIP
  | Assign vname bit
  | Seq com com
  | If "(vname list)" com com
  | While "(vname list)" com

open_bundle com_syntax
begin
notation Assign ("_ ::= _" [1000, 61] 61) and
  Seq ("_;;/ _"  [60, 61] 60) and
  If ("(IF _/\<noteq>0 THEN _/ ELSE _)"  [0, 0, 61] 61) and
  While ("(WHILE _/\<noteq>0 DO _)"  [0, 61] 61)
end

instantiation bit :: order_bot
begin

fun less_eq_bit :: "bit \<Rightarrow> bit \<Rightarrow> bool" where
  "less_eq_bit Zero _ \<longleftrightarrow> True"
| "less_eq_bit _ Zero \<longleftrightarrow> False"
| "less_eq_bit One One \<longleftrightarrow> True"


definition less_bit :: "bit \<Rightarrow> bit \<Rightarrow> bool" where
  "less_bit c1 c2 = (c1 \<le> c2 \<and> \<not> c2 \<le> c1)"

definition bot_bit :: "bit" where
  "bot_bit = Zero"

instance
proof(standard, goal_cases)
  case 1 show ?case by (simp add: less_bit_def)
next
  case (2 x) show ?case by(cases x; simp)
next
  case 3 thus ?case
    by(force elim: less_eq_bit.elims)
next
  case 4 thus ?case by(force elim: less_eq_bit.elims)
next
  case 5 show ?case
    unfolding bot_bit_def by simp
qed
end

instantiation com :: order_bot
begin

fun less_eq_com :: "com \<Rightarrow> com \<Rightarrow> bool" where
  "less_eq_com (Assign v1 b1) (Assign v2 b2) \<longleftrightarrow> v1 \<le> v2 \<and> b1 \<le> b2"
| "less_eq_com (Seq c1 c2) (Seq c3 c4) \<longleftrightarrow> less_eq_com c1 c3 \<and> less_eq_com c2 c4"
| "less_eq_com (If v1 c1 c2) (If v2 c3 c4) \<longleftrightarrow> v1 \<le> v2 \<and> less_eq_com c1 c3 \<and> less_eq_com c2 c4"
| "less_eq_com (While v1 c1) (While v2 c2) \<longleftrightarrow> v1 \<le> v2 \<and> less_eq_com c1 c2"
| "less_eq_com SKIP _ \<longleftrightarrow> True"
| "less_eq_com _ SKIP \<longleftrightarrow> False"
| "less_eq_com (Assign _ _) _ \<longleftrightarrow> True"
| "less_eq_com _ (Assign _ _) \<longleftrightarrow> False"
| "less_eq_com (Seq _ _) _ \<longleftrightarrow> True"
| "less_eq_com _ (Seq _ _) \<longleftrightarrow> False"
| "less_eq_com (If _ _ _) _ \<longleftrightarrow> True"
| "less_eq_com _ (If _ _ _) \<longleftrightarrow> False"

definition less_com :: "com \<Rightarrow> com \<Rightarrow> bool" where
  "less_com c1 c2 = (c1 \<le> c2 \<and> \<not> c2 \<le> c1)"

definition bot_com :: "com" where
  "bot_com = SKIP"

instance
proof(standard, goal_cases)
  case 1 show ?case by (simp add: less_com_def)
next
  case (2 x) show ?case by(induction x; simp)
next
  case (3 x y z) thus ?case
    by(induction x z arbitrary: y rule: less_eq_com.induct; auto; force elim: less_eq_com.elims)
next
  case (4 x y) thus ?case
    by(induction x y rule: less_eq_com.induct; force elim: less_eq_com.elims)
next
  case 5 show ?case
    unfolding bot_com_def by simp
qed
end

end