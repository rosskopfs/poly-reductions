\<^marker>\<open>creator Bilel Ghorbel, Florian Kessler\<close>
section "IMP A reduced imperative language"
theory Com
  imports AExp
begin

paragraph "Summary"
text\<open>Syntax definition for IMP. Based on the syntax definition of IMP\<close>

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


section "Instances"

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

instantiation com :: vars
begin
fun vars_com :: "com \<Rightarrow> vname list" where
"vars SKIP = []" |
"vars (x::=e) = x#vars e" |
"vars (c1;;c2) = vars c1 @ vars c2" |
"vars (IF b\<noteq>0 THEN c1 ELSE c2) = b # vars c1 @ vars c2" |
"vars (WHILE b\<noteq>0 DO c) = b#vars c"
instance ..
end

instantiation com :: subst
begin
fun subst_com :: "(vname \<Rightarrow> vname) \<Rightarrow> com \<Rightarrow> com" where
"subst m SKIP = SKIP" |
"subst m (x::=e) = (m x) ::= subst m e" |
"subst m (c\<^sub>1;;c\<^sub>2) = subst m c\<^sub>1;; subst m c\<^sub>2" |
"subst m (IF b\<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2) = IF m b\<noteq>0 THEN subst m c\<^sub>1 ELSE subst m c\<^sub>2" |
"subst m (WHILE b\<noteq>0 DO c) = WHILE m b\<noteq>0 DO subst m c"
instance
proof (standard, goal_cases)
  case (1 m c)
  then show ?case by (induction c) auto
qed
end

instantiation com :: max_const
begin
fun max_const_com :: "com \<Rightarrow> nat" where
"max_const SKIP = 0" |
"max_const (_ ::= e) = max_const e" |
"max_const (c1;;c2) = max (max_const c1) (max_const c2)" |
"max_const (IF _\<noteq>0 THEN c1 ELSE c2) = max (max_const c1) (max_const c2)" |
"max_const (WHILE _\<noteq>0 DO c) = max_const c"
instance ..
end


section "More Definitions and Facts"

lemma subset_then_length_remdups_le: "set as \<subseteq> set bs
  \<Longrightarrow> length (remdups (as @ cs)) \<le> length (remdups (bs @ cs))"
  apply(induction cs)
   apply (auto simp: card_mono length_remdups_card_conv)
  by (metis (no_types, lifting) List.finite_set Un_insert_right card_mono dual_order.trans
      finite.insertI finite_Un sup.boundedI sup.cobounded1 sup.cobounded2)

definition num_vars:: "com \<Rightarrow> nat" where
"num_vars c = length (remdups (vars c))"

fun lvars :: "com \<Rightarrow> vname set" where
"lvars SKIP = {}" |
"lvars (x::=e) = {x}" |
"lvars (c1;;c2) = lvars c1 \<union> lvars c2" |
"lvars (IF b\<noteq>0 THEN c1 ELSE c2) = lvars c1 \<union> lvars c2" |
"lvars (WHILE b\<noteq>0 DO c) = lvars c"


end