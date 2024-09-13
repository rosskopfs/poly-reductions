theory GOTO
  imports Global_Defs "HOL-IMP.Star"
begin

datatype operi = N val | V vname

datatype instr = 
  HALT |
  ASSIGN vname operi (\<open>_ ;;= _\<close> [0] 100) |
  ADD vname operi (\<open>_ += _\<close>  [0] 100) |
  SUB vname operi (\<open>_ -= _\<close>  [0] 100) |
  RSH vname (\<open>_ \<bind>1\<close>  [0] 100) |
  MOD vname (\<open>_ %=2\<close>  [0] 100) |
  JMP label (\<open>GOTO _\<close>  [0] 100) |
  CONDJMP vname label (\<open>IF _\<noteq>0 THEN GOTO _\<close> [0] 100)

type_synonym GOTO_Prog = "instr list"
type_synonym config = "pc \<times> state"

definition is_halt :: "config \<Rightarrow> bool" where
  "is_halt c \<longleftrightarrow> (fst c) = 0"

fun iexec :: "instr \<Rightarrow> config \<Rightarrow> config" where
  "iexec instr (p, s) = (
    case instr of
      HALT \<Rightarrow> (0, s) |
      x ;;= t \<Rightarrow> (p + 1, case t of N c \<Rightarrow> s(x := c) | V y \<Rightarrow> s(x := s y)) |
      x += t \<Rightarrow> (p + 1, case t of N c \<Rightarrow> s(x := s x + c) | V y \<Rightarrow> s(x := s x + s y)) | 
      x -= t \<Rightarrow> (p + 1, case t of N c \<Rightarrow> s(x := s x - c) | V y \<Rightarrow> s(x := s x - s y)) | 
      x \<bind>1 \<Rightarrow> (p + 1, s(x := s x div 2)) |
      x %=2 \<Rightarrow> (p + 1, s(x := s x mod 2)) |
      GOTO i \<Rightarrow> (i, s) | 
      IF x\<noteq>0 THEN GOTO i \<Rightarrow> (if s x \<noteq> 0 then (i, s) else (p + 1, s))
  )"

definition exec1 :: "GOTO_Prog \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" ("(_/ \<turnstile> (_ \<rightarrow>/ _))" [59,0,59] 60) where
  "P \<turnstile> c \<rightarrow> c' = (\<exists>p s. c = (p, s) \<and> c' = iexec (P !! p) c \<and> 0 < p \<and> p \<le> size P)"

lemma exec1I [intro, code_pred_intro]:
  "c' = iexec (P !! p) (p, s) \<Longrightarrow> 0 < p \<Longrightarrow> p \<le> size P \<Longrightarrow> P \<turnstile> (p, s) \<rightarrow> c'"
  by (simp add: exec1_def of_nat_diff)

abbreviation 
  exec :: "GOTO_Prog \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" ("(_/ \<turnstile> (_ \<rightarrow>*/ _))" 50)
where
  "exec P \<equiv> star (exec1 P)"

lemmas exec_induct = star.induct [of "exec1 P", split_format(complete)]

code_pred exec1 using exec1I exec1_def by auto

inductive exec_t :: "GOTO_Prog \<Rightarrow> pc \<times> state \<Rightarrow> nat \<Rightarrow> pc \<times> state \<Rightarrow> bool" ("_ \<turnstile> _ \<rightarrow>\<^bsup> _ \<^esup> _" 55) where
step0:  "P \<turnstile> (0, s) \<rightarrow>\<^bsup> 0 \<^esup> (0, s)" | 
step1:  "P \<turnstile> (pc\<^sub>1, s\<^sub>1) \<rightarrow> (pc\<^sub>2, s\<^sub>2) \<Longrightarrow> pc\<^sub>2 \<noteq> 0 \<Longrightarrow> P \<turnstile> (pc\<^sub>2, s\<^sub>2) \<rightarrow>\<^bsup> x \<^esup> (pc\<^sub>3, s\<^sub>3) \<Longrightarrow> P \<turnstile> (pc\<^sub>1, s\<^sub>1) \<rightarrow>\<^bsup> 1 + x \<^esup> (pc\<^sub>3, s\<^sub>3)"

thm exec_t.induct
lemmas exec_t_induct = exec_t.induct[split_format(complete)]

text \<open>A small example for z = x + y\<close>
values
  "{(p, map t [''x'', ''y'', ''z'']) | p t. (
    [''x'' ;;= N 3, ''y'' ;;= N 4, ''z'' ;;= V ''x'', ''z'' += V ''y'', HALT] \<turnstile>
    (1, (\<lambda>x. 0)) \<rightarrow>* (p, t))}"

end