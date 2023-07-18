\<^marker>\<open>creator Bilel Ghorbel, Florian Kessler\<close>
section "Arithmetic Expressions"

text \<open>
We define non-nested arithmetic expressions on natural numbers.
The defined operations are addition and modified subtraction. Based on the AExp theory of IMP.
\<close>

theory AExp
  imports
    Main
    "HOL-Library.Char_ord"
    "HOL-Library.List_Lexorder"
    "HOL-Library.Product_Lexorder"
begin

type_synonym vname = string
type_synonym val = nat
type_synonym state = "vname \<Rightarrow> val"

text "Defining atomic expressions:"
datatype atomExp = N val | V vname

fun atomVal :: "atomExp \<Rightarrow> state \<Rightarrow> val" where
  "atomVal (V var) s = s var"|
  "atomVal (N number) _ = number"

text "Defining arithmetic operators and general form of expressions: "

datatype aexp =  A atomExp            |
  Plus atomExp atomExp |
  Sub atomExp atomExp  |
  Parity atomExp       |
  RightShift atomExp

bundle aexp_syntax
begin
notation Plus            ("_ \<oplus> _" [60,60] 60) and
  Sub             ("_ \<ominus> _" [60,60] 60) and
  Parity          ("_ \<doteq>1" [60] 60)   and
  RightShift      ("_\<then>" [60] 60)

end
bundle no_aexp_syntax
begin
notation Plus            ("_ \<oplus> _" [60,60] 60) and
  Sub             ("_ \<ominus> _" [60,60] 60) and
  Parity          ("_ \<doteq>1" [60] 60)    and
  RightShift      ("_\<then>" [60] 60)
end
unbundle aexp_syntax

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (A atomExp) s = atomVal atomExp s"        |
  "aval (a \<oplus> b) s = atomVal a s  + atomVal b s" |
  "aval (a \<ominus> b) s = atomVal a s - atomVal b s"  |
  "aval (a \<doteq>1) s = atomVal a s  mod 2"        |
  "aval (a \<then>) s = atomVal a s div 2"

text "evaluation examples:"
value "aval (V ''x'' \<oplus> N 5)  (\<lambda>x. if x = ''x'' then 7 else 0)"
value "aval (V ''x'' \<ominus> N 5)  ((\<lambda>x. 0) (''x'':= 7))"

text "Syntactic sugar to write states:"
definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

bundle state_syntax
begin
notation null_state ("<>")
end

bundle no_state_syntax
begin
no_notation null_state ("<>")
end

lemma "<a := 1, b := 2> = (<> (a := 1)) (b := (2::int))"
  by (rule refl)

value "aval (V ''x'' \<ominus> N 5) <''x'' := 7>"
value "aval (V ''x'' \<ominus> N 10) <''x'' := 7>"


instantiation atomExp :: order_bot
begin

fun less_eq_atomExp :: "atomExp \<Rightarrow> atomExp \<Rightarrow> bool" where
  "less_eq_atomExp (N n1) (N n2) \<longleftrightarrow> n1 \<le> n2"
| "less_eq_atomExp (V v1) (V v2) \<longleftrightarrow> v1 \<le> v2"
| "less_eq_atomExp (N _) _ \<longleftrightarrow> True"
| "less_eq_atomExp (V _) _ \<longleftrightarrow> False"

definition less_atomExp :: "atomExp \<Rightarrow> atomExp \<Rightarrow> bool" where
  "less_atomExp c1 c2 = (c1 \<le> c2 \<and> \<not> c2 \<le> c1)"

definition bot_atomExp :: "atomExp" where
  "bot_atomExp = N 0"

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

instantiation aexp :: order_bot
begin

fun less_eq_aexp :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" where
  "less_eq_aexp (A a1) (A a2) \<longleftrightarrow> a1 \<le> a2"
| "less_eq_aexp (Plus a1 a2) (Plus b1 b2) \<longleftrightarrow> (a1, a2) \<le> (b1, b2)"
| "less_eq_aexp (Sub a1 a2) (Sub b1 b2) \<longleftrightarrow> (a1, a2) \<le> (b1, b2)"
| "less_eq_aexp (Parity p1) (Parity p2) \<longleftrightarrow> p1 \<le> p2"
| "less_eq_aexp (RightShift sh1) (RightShift sh2) \<longleftrightarrow> sh1 \<le> sh2"
| "less_eq_aexp (A _) _ \<longleftrightarrow> True"
| "less_eq_aexp _ (A _) \<longleftrightarrow> False"
| "less_eq_aexp (Plus _ _) _ \<longleftrightarrow> True"
| "less_eq_aexp _ (Plus _ _) \<longleftrightarrow> False"
| "less_eq_aexp (Sub _ _) _ \<longleftrightarrow> True"
| "less_eq_aexp _ (Sub _ _) \<longleftrightarrow> False"
| "less_eq_aexp (Parity _) _ \<longleftrightarrow> True"
| "less_eq_aexp _ (Parity _) \<longleftrightarrow> False"

definition less_aexp :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" where
  "less_aexp c1 c2 = (c1 \<le> c2 \<and> \<not> c2 \<le> c1)"

definition bot_aexp :: "aexp" where
  "bot_aexp = A bot"

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
  case 5 show ?case
    unfolding bot_aexp_def using bot_atomExp_def less_eq_aexp.elims(3) by fastforce
qed
end

end