theory GOTO
  imports Global_Defs "HOL-IMP.Star"
begin

datatype operi = N val | V vname

datatype instr = 
  HALT |
  ASSIGN vname operi (\<open>_ ::= _\<close>) |
  ADD vname operi (\<open>_ += _\<close>) |
  SUB vname operi (\<open>_ -= _\<close>) |
  RSH vname (\<open>_ \<bind>1\<close>) |
  MOD vname (\<open>_ %=2\<close>) |
  JMP label (\<open>GOTO _\<close>) |
  CONDJMP vname operi label (\<open>IF _ = _ THEN GOTO _\<close>)

type_synonym GOTO_prog = "instr list"
type_synonym config = "pc \<times> state"

definition is_halt :: "config \<Rightarrow> bool" where
  "is_halt c \<longleftrightarrow> (fst c) = 0"

fun iexec :: "instr \<Rightarrow> config \<Rightarrow> config" where
  "iexec instr (p, s) = (
    case instr of
      HALT \<Rightarrow> (0, s) |
      x ::= t \<Rightarrow> (p + 1, case t of N c \<Rightarrow> s(x := c) | V y \<Rightarrow> s(x := s y)) |
      x += t \<Rightarrow> (p + 1, case t of N c \<Rightarrow> s(x := s x + c) | V y \<Rightarrow> s(x := s x + s y)) | 
      x -= t \<Rightarrow> (p + 1, case t of N c \<Rightarrow> s(x := s x - c) | V y \<Rightarrow> s(x := s x - s y)) | 
      x \<bind>1 \<Rightarrow> (p + 1, s(x := s x div 2)) |
      x %=2 \<Rightarrow> (p + 1, s(x := s x mod 2)) |
      GOTO i \<Rightarrow> (i, s) | 
      IF x = t THEN GOTO i \<Rightarrow> (case t of 
        N c \<Rightarrow> if s x = c then (i, s) else (p, s) | 
        V y \<Rightarrow> if s x = s y then (i, s) else (p, s))
  )"

definition exec1 :: "GOTO_prog \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" ("(_/ \<turnstile> (_ \<rightarrow>/ _))" [59,0,59] 60) where
  "P \<turnstile> c \<rightarrow> c' = (\<exists>p s. c = (p, s) \<and> c' = iexec (P !! p) c \<and> 0 < p \<and> p \<le> size P)"

lemma exec1I [intro, code_pred_intro]:
  "c' = iexec (P !! p) (p, s) \<Longrightarrow> 0 < p \<Longrightarrow> p \<le> size P \<Longrightarrow> P \<turnstile> (p, s) \<rightarrow> c'"
  by (simp add: exec1_def of_nat_diff)

abbreviation 
  exec :: "GOTO_prog \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" ("(_/ \<turnstile> (_ \<rightarrow>*/ _))" 50)
where
  "exec P \<equiv> star (exec1 P)"

lemmas exec_induct = star.induct [of "exec1 P", split_format(complete)]

code_pred exec1 using exec1I exec1_def by auto

text \<open>A small example for z = x + y\<close>
values
  "{(p, map t [''x'', ''y'', ''z'']) | p t. (
    [''x'' ::= N 3, ''y'' ::= N 4, ''z'' ::= V ''x'', ''z'' += V ''y'', HALT] \<turnstile>
    (1, (\<lambda>x. 0)) \<rightarrow>* (p, t))}"

end