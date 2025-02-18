\<^marker>\<open>creator Bilel Ghorbel, Florian Kessler\<close>
\<^marker>\<open>creator Fabian Huch\<close>
theory AExp
  imports
    IMP_Base Eq_On
    "HOL-Library.Char_ord" "HOL-Library.List_Lexorder" "HOL-Library.Product_Lexorder"
begin

section "Arithmetic Expressions"

text \<open>We define non-nested arithmetic expressions on natural numbers.
The defined operations are addition and modified subtraction. Based on the AExp theory of IMP.\<close>

subsection "Atomic expressions:"

datatype atomExp = N val | V vname

fun atomVal :: "atomExp \<Rightarrow> state \<Rightarrow> val" where
  "atomVal (V var) s = s var"|
  "atomVal (N number) _ = number"

subsection "Arithmetic operators and general form of expressions: "

datatype aexp = A atomExp | Plus atomExp atomExp | Sub atomExp atomExp

open_bundle aexp_syntax
begin
notation Plus ("_ \<oplus> _" [60,60] 60)
and Sub ("_ \<ominus> _" [60,60] 60)
end

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (A atomExp) s = atomVal atomExp s"        |
  "aval (a \<oplus> b) s = atomVal a s  + atomVal b s" |
  "aval (a \<ominus> b) s = atomVal a s - atomVal b s"


section "Instances"

subsection "Atomic expressions"

instantiation atomExp :: order_bot
begin
fun less_eq_atomExp :: "atomExp \<Rightarrow> atomExp \<Rightarrow> bool" where
  "less_eq_atomExp (N n1) (N n2) \<longleftrightarrow> n1 \<le> n2"
| "less_eq_atomExp (V v1) (V v2) \<longleftrightarrow> v1 \<le> v2"
| "less_eq_atomExp (N _) _ \<longleftrightarrow> True"
| "less_eq_atomExp (V _) _ \<longleftrightarrow> False"
definition less_atomExp :: "atomExp \<Rightarrow> atomExp \<Rightarrow> bool" where "less_atomExp c1 c2 = (c1 \<le> c2 \<and> \<not> c2 \<le> c1)"
definition bot_atomExp :: "atomExp" where "bot_atomExp = N 0"
instance
proof(standard, goal_cases)
  case 1 show ?case by (simp add: less_atomExp_def)
next
  case 2 show ?case using less_eq_atomExp.simps by (fast elim: less_eq_atomExp.elims)
next
  case 3 thus ?case by (fastforce elim: less_eq_atomExp.elims)
next
  case 4 thus ?case by (fastforce elim: less_eq_atomExp.elims)
next
  case 5 show ?case unfolding bot_atomExp_def using less_eq_atomExp.elims(3) by blast
qed
end

instantiation atomExp :: vars
begin
fun vars_atomExp :: "atomExp \<Rightarrow> vname list" where
"vars_atomExp (V var) = [var]" |
"vars_atomExp (N _) = []"
instance ..
end

instantiation atomExp :: subst
begin
fun subst_atomExp :: "(vname \<Rightarrow> vname) \<Rightarrow> atomExp \<Rightarrow> atomExp" where
"subst m (V var) = V (m var)" |
"subst m (N n) = N n"
instance
proof (standard, goal_cases)
  case (1 m c)
  then show ?case by (induction c) auto
qed
end

instantiation atomExp :: max_const
begin
fun max_const_atomExp :: "atomExp \<Rightarrow> nat" where
"max_const (V _) = 0" |
"max_const (N n) = n"
instance ..
end



subsection "Arithmetic expressions"

instantiation aexp :: order_bot
begin
fun less_eq_aexp :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" where
  "less_eq_aexp (A a1) (A a2) \<longleftrightarrow> a1 \<le> a2"
| "less_eq_aexp (Plus a1 a2) (Plus b1 b2) \<longleftrightarrow> (a1, a2) \<le> (b1, b2)"
| "less_eq_aexp (Sub a1 a2) (Sub b1 b2) \<longleftrightarrow> (a1, a2) \<le> (b1, b2)"
| "less_eq_aexp (A _) _ \<longleftrightarrow> True"
| "less_eq_aexp _ (A _) \<longleftrightarrow> False"
| "less_eq_aexp (Plus _ _) _ \<longleftrightarrow> True"
| "less_eq_aexp _ (Plus _ _) \<longleftrightarrow> False"
definition less_aexp :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" where "less_aexp c1 c2 = (c1 \<le> c2 \<and> \<not> c2 \<le> c1)"
definition bot_aexp :: "aexp" where "bot_aexp = A bot"
instance
proof(standard, goal_cases)
  case 1 show ?case by (simp add: less_aexp_def)
next
  case (2 x) show ?case by(cases x; simp)
next
  case (3 x y z) thus ?case by (cases x; cases y; cases z) auto
next
  case (4 x y) thus ?case by (cases x; cases y) auto
next
  case 5 show ?case unfolding bot_aexp_def using bot_atomExp_def less_eq_aexp.elims(3) by fastforce
qed
end

instantiation aexp :: vars
begin
fun vars_aexp :: "aexp \<Rightarrow> vname list" where
"vars (A e) = vars e" |
"vars (Plus e\<^sub>1 e\<^sub>2) = vars e\<^sub>1 @ vars e\<^sub>2" |
"vars (Sub e\<^sub>1 e\<^sub>2) = vars e\<^sub>1 @ vars e\<^sub>2"
instance ..
end

instantiation aexp :: subst
begin
fun subst_aexp :: "(vname \<Rightarrow> vname) \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst m (A e) = A (subst m e)" |
"subst m (Plus e\<^sub>1 e\<^sub>2) = Plus (subst m e\<^sub>1) (subst m e\<^sub>2)" |
"subst m (Sub e\<^sub>1 e\<^sub>2) = Sub (subst m e\<^sub>1) (subst m e\<^sub>2)"
instance
proof (standard, goal_cases)
  case (1 m c)
  then show ?case by (induction c) auto
qed
end

instantiation aexp :: max_const
begin
fun max_const_aexp :: "aexp \<Rightarrow> nat" where
"max_const (A e) = max_const e" |
"max_const (Plus e\<^sub>1 e\<^sub>2) = max (max_const e\<^sub>1) (max_const e\<^sub>2)" |
"max_const (Sub e\<^sub>1 e\<^sub>2) = max (max_const e\<^sub>1) (max_const e\<^sub>2)"
instance ..
end



section "Facts"

lemma atomVal_eq_if_eq_on_vars[simp]:
  "s\<^sub>1 = s\<^sub>2 on set (vars a) \<Longrightarrow> atomVal a s\<^sub>1 = atomVal a s\<^sub>2"
  by (induction a) auto

lemma aval_eq_if_eq_on_vars [simp]:
  "s\<^sub>1 = s\<^sub>2 on set (vars a) \<Longrightarrow> aval a s\<^sub>1 = aval a s\<^sub>2"
  apply (induction a)
  apply auto
  using atomVal_eq_if_eq_on_vars eq_on_subset
  apply (metis sup.cobounded1 sup.cobounded2)+
  done

lemma atomVal_subst[simp]: "inj_on m (set (vars a)) \<Longrightarrow> atomVal (subst m a) s = (atomVal a (s o m))"
  by (induction a) auto

lemma aval_subst[simp]: "inj_on m (set (vars a)) \<Longrightarrow> aval (subst m a) s = aval a (s o m)"
  by (induction a) (auto simp add: inj_on_Un)


lemma Max_range_le_then_element_le: "finite (range s) \<Longrightarrow> 2 * Max (range s) < (x :: nat) \<Longrightarrow> 2 * (s y) < x"
proof -
  assume "2 * Max (range s) < (x :: nat)"
  moreover have "s y \<in> range s" by simp
  moreover assume "finite (range s)"
  moreover hence "s y \<le> Max (range s)" by simp
  ultimately show ?thesis by linarith
qed

lemma aval_le_when:
  assumes "finite (range s)" "2 * max (Max (range s)) (max_const a) < x"
  shows "aval a s < x"
using assms proof(cases a)
  case (A x1)
  thus ?thesis using assms
  proof(cases x1)
    case (V x2)
    thus ?thesis using assms A Max_range_le_then_element_le[where ?s=s and ?x = x and ?y=x2] by simp
  qed simp
next
  case (Plus x21 x22)
  hence "2 * max (AExp.atomVal x21 s) (AExp.atomVal x22 s) < x"
    apply(cases x21; cases x22)
    using assms
    by (auto simp add: Max_range_le_then_element_le nat_mult_max_right)
  thus ?thesis using Plus by auto
next
  case (Sub x31 x32)
  then show ?thesis
    apply(cases x31 ; cases x32)
    using assms apply(auto simp add: Max_range_le_then_element_le nat_mult_max_right)
    using Max_range_le_then_element_le
    by (metis gr_implies_not0 lessI less_imp_diff_less less_imp_le_nat less_le_trans
        linorder_neqE_nat n_less_m_mult_n numeral_2_eq_2)+
qed


end