theory GOTO
  imports Main Global_Defs "HOL-IMP.Star"
begin

text \<open>The automatic transform from index of list to index of GOTO prog is done here\<close>
fun inth :: "'a list \<Rightarrow> nat \<Rightarrow> 'a" (infixl "!!" 100) where
  "(x # xs) !! i = (if i = 1 then x else xs !! (i - 1))"

text \<open>The only additional lemma we need about this function is indexing over append:\<close>
lemma inth_append [simp]:
  "0 < i \<Longrightarrow> i \<le> length xs + length ys \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow>
  (xs @ ys) !! i = (if i \<le> size xs then xs !! i else ys !! (i - size xs))" 
  apply (induction xs arbitrary: i) apply (auto simp: algebra_simps)
  apply (metis Suc_le_mono Suc_pred diff_is_0_eq list.size(3) neq0_conv trans_le_add1)
  by (smt (verit, ccfv_threshold) Suc_pred append_Nil diff_Suc_Suc diff_is_0_eq le0 list.size(3) neq0_conv)

type_synonym label = nat
type_synonym pc = nat

datatype operi = N val | V vname

datatype instr = 
  HALT |
  ASSIGN vname operi (\<open>_ ::= _\<close>) |
  ADD vname operi (\<open>_ += _\<close>) |
  SUB vname operi (\<open>_ -= _\<close>) |
  RSH vname (\<open>_ \<bind>1\<close>) |
  MOD vname (\<open>_ %=2\<close>) |
  JMP label (\<open>GOTO _\<close>) |
  CONDJMP vname label (\<open>IF _\<noteq>0 THEN GOTO _\<close>)

type_synonym GOTO_Prog = "instr list"
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

text \<open>A small example for z = x + y\<close>
values
  "{(p, map t [''x'', ''y'', ''z'']) | p t. (
    [''x'' ::= N 3, ''y'' ::= N 4, ''z'' ::= V ''x'', ''z'' += V ''y'', HALT] \<turnstile>
    (1, (\<lambda>x. 0)) \<rightarrow>* (p, t))}"

end