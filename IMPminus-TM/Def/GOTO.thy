theory GOTO
  imports Main "HOL-IMP.Star" (*"HOL-IMP.Compiler"*)
begin

(* what does this mean? *)
declare [[coercion_enabled]] 
declare [[coercion "int :: nat \<Rightarrow> int"]]

fun inth :: "'a list \<Rightarrow> int \<Rightarrow> 'a" (infixl "!!" 100) where
  "(x # xs) !! i = (if i = 0 then x else xs !! (i - 1))"

lemma inth_append [simp]:
  "0 \<le> i \<Longrightarrow>
  (xs @ ys) !! i = (if i < size xs then xs !! i else ys !! (i - size xs))"
by (induction xs arbitrary: i) (auto simp: algebra_simps)

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"
type_synonym label = nat
type_synonym pc = nat

datatype operi = N val | V vname

datatype instr = 
  HALT |
  ASSIGN vname operi (\<open>_ ::= _\<close>) |
  ADD vname operi (\<open>_ += _\<close>) |
  SUB vname operi (\<open>_ -= _\<close>) |
  JMP label (\<open>GOTO _\<close>) |
  CONDJMP vname operi label (\<open>IF _ = _ THEN GOTO _\<close>)

type_synonym GOTO_prog = "instr list"
type_synonym config = "pc \<times> state"

definition is_halt :: "config \<Rightarrow> bool" where
  "is_halt c \<longleftrightarrow> (fst c) = 0"

fun iexec :: "instr \<Rightarrow> config \<Rightarrow> config" where
  "iexec instr (p, s) = (
    case instr of
      HALT \<Rightarrow> (p, s) |
      x ::= t \<Rightarrow> (p + 1, case t of N c \<Rightarrow> s(x := c) | V y \<Rightarrow> s(x := s y)) |
      x += t \<Rightarrow> (p + 1, case t of N c \<Rightarrow> s(x := s x + c) | V y \<Rightarrow> s(x := s x + s y)) | 
      x -= t \<Rightarrow> (p + 1, case t of N c \<Rightarrow> s(x := s x - c) | V y \<Rightarrow> s(x := s x - s y)) | 
      GOTO i \<Rightarrow> (i, s) | 
      IF x = t THEN GOTO i \<Rightarrow> (case t of 
        N c \<Rightarrow> if s x = c then (i, s) else (p, s) | 
        V y \<Rightarrow> if s x = s y then (i, s) else (p, s))
  )"

definition exec1 :: "GOTO_prog \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" ("(_/ \<turnstile> (_ \<rightarrow>/ _))" [59,0,59] 60) where
  "P \<turnstile> c \<rightarrow> c' = (\<exists>p s. c = (p, s) \<and> c' = iexec (P !! (p - 1)) c \<and> 0 < p \<and> p \<le> size P)"

lemma exec1I [intro, code_pred_intro]:
  "c' = iexec (P !! (p - 1)) (p, s) \<Longrightarrow> 0 < p \<Longrightarrow> p \<le> size P \<Longrightarrow> P \<turnstile> (p, s) \<rightarrow> c'"
  by (simp add: exec1_def of_nat_diff)

abbreviation 
  exec :: "GOTO_prog \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" ("(_/ \<turnstile> (_ \<rightarrow>*/ _))" 50)
where
  "exec P \<equiv> star (exec1 P)"

lemmas exec_induct = star.induct [of "exec1 P", split_format(complete)]

code_pred exec1 using exec1I exec1_def by auto

(*
values
  "{(p, map t [''x'',''y'']) | p t. (
    [''x'' ::= N 3, ''z'' ::= V ''x'', HALT] \<turnstile>
    (1, (\<lambda>x. 0)(''x'' := 3)) \<rightarrow>* (p, t))}"

  Warning: do not terminate. Why?
*)
end