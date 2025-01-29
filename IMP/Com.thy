\<^marker>\<open>creator Bilel Ghorbel, Florian Kessler\<close>
section "IMP- A reduced imperative language"
theory Com
  imports
    Main
    AExp
    "HOL-Library.Char_ord"
    "HOL-Library.List_Lexorder"
    "HOL-Library.Product_Lexorder"
begin

paragraph "Summary"
text\<open>Syntax definition for IMP-. Based on the syntax definition of IMP\<close>

datatype com = SKIP
  | Assign vname aexp
  | Seq    com  com
  | If     vname com com
  | While  vname com

open_bundle com_syntax
begin
notation Assign ("_ ::= _" [1000, 61] 61)
and Seq ("_;;/ _"  [60, 61] 60)
and If ("(IF _/\<noteq>0 THEN _/ ELSE _)"  [0, 0, 61] 61)
and While ("(WHILE _/\<noteq>0 DO _)"  [0, 61] 61)
end

instantiation com :: order_bot
begin

fun less_eq_com :: "com \<Rightarrow> com \<Rightarrow> bool" where
  "less_eq_com (Assign v1 e1) (Assign v2 e2) \<longleftrightarrow> v1 \<le> v2 \<and> e1 \<le> e2"
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