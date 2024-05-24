text \<open>A GOTO-like language that works on list.
Used as intermediate of multitape TM and GOTO program.
Generally, one list here imitates one tape from the TM.\<close>

theory GOTO_on_List
  imports "IMPminus_TM-Def.Global_Defs" "HOL-IMP.Star"
begin

(*TODO: rewrite all documentations using LaTeX syntax *)
text \<open>The value of variables in GOTO_on_List programs are lists.
The length of the lists in a GOTO_on_List program, reduced from a multitape-TM, can be one of the following:
1. length = 1, with the current state of the TM as the only element.
  Luckly our TM uses type nat for both states and tape characters, so this unification is possible.
2. length = k, where k is the number of tapes in the TM.
  Storing the positions of heads on each tape, and the characters at those positions on each tape
3. length = maximum length of a tape in the TM during execution.
  Storing the content of tapes. Depending on the implementation of the reducing algorithm from IMP- to TM,
  this length should be bounded to \<O>(t), where t is the runtime of the original IMP- program.\<close>

datatype var\<^sub>l =
  ST      | \<comment> \<open>State\<close>
  TP nat  | \<comment> \<open>Tape\<close>
  HP nat  | \<comment> \<open>Head positions\<close>
  TMP nat   \<comment> \<open>Other variables, e.g. storing chars at head positions on each tape\<close>

datatype GOTO\<^sub>l_operi =
  L "val list" |
  V\<^sub>l var\<^sub>l |
  ReadChs "nat list"
\<comment> \<open>ReadChs: get the list of characters where the heads currently point at on each tape
    E.g. Index [0, 1, 2], under the following state:
    <Tape 0 = [0,1], Tape 1 = [10,11], Tape 2 = [20,21],
     HP 0 = [0], HP 1 = [0], HP 2 = [1]>
    Result would be [0,10,21].\<close>
\<comment> \<open>This example can be found at the end of this file\<close>


datatype GOTO\<^sub>l_instr =
  NOP\<^sub>l |
  HALT\<^sub>l |
  Assign var\<^sub>l GOTO\<^sub>l_operi (\<open>_ ::=\<^sub>l _\<close> [60]60)|
  TapeModify nat val |
  MoveLeft nat |
  MoveRight nat |
  Jmp label (\<open>GOTO\<^sub>l _\<close>) |
  CondJmp var\<^sub>l GOTO\<^sub>l_operi label (\<open>IF _ = _ THEN GOTO\<^sub>l _\<close> [59, 0, 59] 60) |
  CondJmp2 var\<^sub>l GOTO\<^sub>l_operi var\<^sub>l GOTO\<^sub>l_operi label (\<open>IF _ = _ AND _ = _ THEN GOTO\<^sub>l _\<close> [59, 59, 0, 59] 60)


subsection \<open>Semantics of GOTO_on_List programs\<close>
text \<open>This part draws largely on "HOL-IMP.Compiler"\<close>

type_synonym GOTO\<^sub>l_prog = "GOTO\<^sub>l_instr list"
type_synonym state\<^sub>l = "var\<^sub>l \<Rightarrow> val list"
type_synonym config\<^sub>l = "pc \<times> state\<^sub>l"

fun eval_GOTO\<^sub>l_operi :: "state\<^sub>l \<Rightarrow> GOTO\<^sub>l_operi \<Rightarrow> val list" where
  "eval_GOTO\<^sub>l_operi s (L l) = l" |
  "eval_GOTO\<^sub>l_operi s (V\<^sub>l x) = s x" |
  "eval_GOTO\<^sub>l_operi s (ReadChs tps) = map (\<lambda>n. (s (TP n)) ! (hd (s (HP n)))) tps"

fun iexec\<^sub>l :: "GOTO\<^sub>l_instr \<Rightarrow> config\<^sub>l \<Rightarrow> config\<^sub>l" where
  "iexec\<^sub>l NOP\<^sub>l (pc, s) = (Suc pc, s)" |
  "iexec\<^sub>l HALT\<^sub>l (pc, s) = (0, s)" |
  "iexec\<^sub>l (x ::=\<^sub>l l) (pc, s) = (Suc pc, s(x := eval_GOTO\<^sub>l_operi s l))" |
  "iexec\<^sub>l (TapeModify n v) (pc, s) = (Suc pc, s(TP n := (s (TP n))[hd (s (HP n)) := v]))" |
  "iexec\<^sub>l (MoveLeft n) (pc, s) = (Suc pc, s(HP n := [hd (s (HP n)) - 1]))" |
  "iexec\<^sub>l (MoveRight n) (pc, s) = (Suc pc, s(HP n := [Suc (hd (s (HP n)))]))" |
  "iexec\<^sub>l (GOTO\<^sub>l label) (pc, s) = (label, s)" |
  "iexec\<^sub>l (IF x = l THEN GOTO\<^sub>l label) (pc, s) =
    (if (s x = eval_GOTO\<^sub>l_operi s l) then label else Suc pc, s)" |
  "iexec\<^sub>l (IF x = l\<^sub>1 AND y = l\<^sub>2 THEN GOTO\<^sub>l label) (pc, s) =
    (if s x = eval_GOTO\<^sub>l_operi s l\<^sub>1 \<and> s y = eval_GOTO\<^sub>l_operi s l\<^sub>2 then label else Suc pc, s)"

definition exec1\<^sub>l :: "GOTO\<^sub>l_prog \<Rightarrow> config\<^sub>l \<Rightarrow> config\<^sub>l \<Rightarrow> bool" ("(_/ \<turnstile>\<^sub>l (_ \<rightarrow>/ _))" [59,0,59] 60) where
  "P \<turnstile>\<^sub>l cfg \<rightarrow> cfg' \<longleftrightarrow> (\<exists>pc s. cfg = (pc, s) \<and> cfg' = iexec\<^sub>l (P !! pc) cfg \<and>
                         P \<noteq> [] \<and> 0 < pc \<and> pc \<le> length P)"

text \<open>Note that pc = 0 is when the program halts; programs are indexed with "!!", indices start from 1\<close>
lemma exec1\<^sub>l_I [intro, code_pred_intro]:
  "c' = iexec\<^sub>l (P !! pc) (pc, s) \<Longrightarrow> P \<noteq> [] \<Longrightarrow> 0 < pc \<Longrightarrow> pc \<le> length P \<Longrightarrow>
   P \<turnstile>\<^sub>l (pc, s) \<rightarrow> c'"
  by (simp add: exec1\<^sub>l_def of_nat_diff)

lemma exec1\<^sub>l_pc_range [intro]:
  "P \<turnstile>\<^sub>l (pc, s) \<rightarrow> c' \<Longrightarrow> 0 < pc \<and> pc \<le> length P"
  unfolding exec1\<^sub>l_def by blast

lemma exec1\<^sub>l_iexec\<^sub>l [intro]:
  "P \<turnstile>\<^sub>l (pc, s) \<rightarrow> c' \<Longrightarrow> iexec\<^sub>l (P !! pc) (pc, s) = c'"
  unfolding exec1\<^sub>l_def by blast

abbreviation
  exec\<^sub>l :: "GOTO\<^sub>l_prog \<Rightarrow> config\<^sub>l \<Rightarrow> config\<^sub>l \<Rightarrow> bool" ("(_/ \<turnstile>\<^sub>l (_ \<rightarrow>*/ _))" [60] 50)
where
  "exec\<^sub>l P \<equiv> star (exec1\<^sub>l P)"

lemmas exec\<^sub>l_induct = star.induct[of "exec1\<^sub>l P", split_format(complete)]

code_pred exec1\<^sub>l using exec1\<^sub>l_I exec1\<^sub>l_def by auto

abbreviation 
  exec\<^sub>l_t :: "GOTO\<^sub>l_prog \<Rightarrow> config\<^sub>l \<Rightarrow> nat \<Rightarrow> config\<^sub>l \<Rightarrow> bool" ("(_/ \<turnstile>\<^sub>l (_ \<rightarrow>\<^bsub>_\<^esub>/ _))" [60] 50)
where
  "exec\<^sub>l_t P cfg t cfg' \<equiv> ((exec1\<^sub>l P) ^^ t) cfg cfg'"

lemma exec\<^sub>l_t_add[intro]:
  assumes "P \<turnstile>\<^sub>l (pc, s) \<rightarrow>\<^bsub>t\<^sub>1\<^esub> (pc', s')"
      and "P \<turnstile>\<^sub>l (pc', s') \<rightarrow>\<^bsub>t\<^sub>2\<^esub> (pc'', s'')"
    shows "P \<turnstile>\<^sub>l (pc, s) \<rightarrow>\<^bsub>t\<^sub>1 + t\<^sub>2\<^esub> (pc'', s'')"
  using assms
  apply (induction t\<^sub>2)
  apply auto
  by (metis relcomppI relpowp_add)

definition pc_start :: "nat" where "pc_start = 1"
definition pc_halt :: "nat" where "pc_halt = 0"

lemma pc_start_eq_1[simp]: "pc_start = 1"
  unfolding pc_start_def by simp
lemma pc_halt_eq_0[simp]: "pc_halt = 0"
  unfolding pc_halt_def by simp

text \<open>An example of list modification\<close>
values
  "{(pc, map t [HP 0, TP 0]) | pc t. (
    [TP 0 ::=\<^sub>l L [0, 1, 2], HP 0 ::=\<^sub>l L [2],
     TapeModify 0 100,
     MoveLeft 0,
     TapeModify 0 100,
     HALT\<^sub>l] \<turnstile>\<^sub>l
    (1, (\<lambda>x. [])) \<rightarrow>* (pc, t))}"

text \<open>An example of ReadChs\<close>
values
  "{(pc, map t [TP 0, TP 1, TP 2, HP 0, HP 1, HP 2, TMP 0]) | pc t. (
    [TP 0 ::=\<^sub>l L [0, 1], TP 1 ::=\<^sub>l L [10, 11], TP 2 ::=\<^sub>l L [20, 21],
     HP 0 ::=\<^sub>l L [0],    HP 1 ::=\<^sub>l L [0],      HP 2 ::=\<^sub>l L [1],
     TMP 0 ::=\<^sub>l ReadChs [0, 1, 2], HALT\<^sub>l] \<turnstile>\<^sub>l
    (1, (\<lambda>x. [])) \<rightarrow>* (pc, t))}"


subsection \<open>Verification infrastructure\<close>

text \<open>The program is executed deterministically\<close>
lemma iexec\<^sub>l_determ [intro]:
  "iexec\<^sub>l ins s = s\<^sub>1 \<Longrightarrow> iexec\<^sub>l ins s = s\<^sub>2 \<Longrightarrow> s\<^sub>1 = s\<^sub>2"
  by (cases ins) auto

lemma exec1\<^sub>l_determ [intro]:
  "P \<turnstile>\<^sub>l cfg \<rightarrow> cfg' \<Longrightarrow> P \<turnstile>\<^sub>l cfg \<rightarrow> cfg'' \<Longrightarrow> cfg' = cfg''"
  unfolding exec1\<^sub>l_def
  by blast

lemma exec\<^sub>l_t_determ [intro]:
  "P \<turnstile>\<^sub>l cfg \<rightarrow>\<^bsub>t\<^esub> cfg' \<Longrightarrow> P \<turnstile>\<^sub>l cfg \<rightarrow>\<^bsub>t\<^esub> cfg'' \<Longrightarrow> cfg' = cfg''"
proof (induction t arbitrary: cfg)
  case 0
  then show ?case by auto
next
  case (Suc t)
  from Suc obtain cfg\<^sub>1 where cfg\<^sub>1: "P \<turnstile>\<^sub>l cfg \<rightarrow> cfg\<^sub>1" "P \<turnstile>\<^sub>l cfg\<^sub>1 \<rightarrow>\<^bsub>t\<^esub> cfg'"
    by (metis relpowp_Suc_D2)
  from Suc obtain cfg\<^sub>2 where cfg\<^sub>2: "P \<turnstile>\<^sub>l cfg \<rightarrow> cfg\<^sub>2" "P \<turnstile>\<^sub>l cfg\<^sub>2 \<rightarrow>\<^bsub>t\<^esub> cfg''"
    by (metis relpowp_Suc_D2)
  from \<open>P \<turnstile>\<^sub>l cfg \<rightarrow> cfg\<^sub>1\<close> \<open>P \<turnstile>\<^sub>l cfg \<rightarrow> cfg\<^sub>2\<close> have "cfg\<^sub>1 = cfg\<^sub>2" by fast
  with Suc.IH \<open>P \<turnstile>\<^sub>l cfg\<^sub>1 \<rightarrow>\<^bsub>t\<^esub> cfg'\<close> \<open>P \<turnstile>\<^sub>l cfg\<^sub>2 \<rightarrow>\<^bsub>t\<^esub> cfg''\<close>
  show ?case by blast
qed

text \<open>The verification of GOTO on List programs depends on very specific properties of the program,
below are some lemmas about the behaviour of the program with certain properties.\<close>

text \<open>First, a large part of the transformed program does not contain modification to any variable.
This is a very useful information for verification.\<close>

fun no_modification :: "GOTO\<^sub>l_instr \<Rightarrow> bool" where
  "no_modification (_ ::=\<^sub>l _) \<longleftrightarrow> False" |
  "no_modification (TapeModify _ _) \<longleftrightarrow> False" |
  "no_modification (MoveLeft _) \<longleftrightarrow> False" |
  "no_modification (MoveRight _) \<longleftrightarrow> False" |
  "no_modification _ \<longleftrightarrow> True"

lemma iexec\<^sub>l_no_modification[intro]:
  assumes "no_modification ins"
    shows "\<exists>pc'. iexec\<^sub>l ins (pc, s) = (pc', s)"
  using assms
  by (cases ins) auto

text \<open>If a block of program contains no jump command, or only conditional jumps
with conditions unsatisfied under the given state, the block is then executed sequentially.
With this information, the runtime can be determined directly.\<close>

fun no_jump :: "state\<^sub>l \<Rightarrow> GOTO\<^sub>l_instr \<Rightarrow> bool" where
  "no_jump s HALT\<^sub>l \<longleftrightarrow> False" | \<comment>\<open>HALT \<equiv> GOTO 0\<close>
  "no_jump s (GOTO\<^sub>l _) \<longleftrightarrow> False" |
  "no_jump s (IF x = l THEN GOTO\<^sub>l _) \<longleftrightarrow> s x \<noteq> eval_GOTO\<^sub>l_operi s l" |
  "no_jump s (IF x = l\<^sub>1 AND y = l\<^sub>2 THEN GOTO\<^sub>l _) \<longleftrightarrow>
   s x \<noteq> eval_GOTO\<^sub>l_operi s l\<^sub>1 \<or> s y \<noteq> eval_GOTO\<^sub>l_operi s l\<^sub>2" |
  "no_jump _ _ \<longleftrightarrow> True"

lemma iexec\<^sub>l_no_jump[intro]:
  assumes "no_jump s ins"
    shows "\<exists>s'. iexec\<^sub>l ins (pc, s) = (Suc pc, s')"
  using assms
  by (cases ins) auto

fun strict_no_jump :: "GOTO\<^sub>l_instr \<Rightarrow> bool" where
  "strict_no_jump HALT\<^sub>l \<longleftrightarrow> False" | \<comment>\<open>HALT \<equiv> GOTO 0\<close>
  "strict_no_jump (GOTO\<^sub>l _) \<longleftrightarrow> False" |
  "strict_no_jump (IF x = l THEN GOTO\<^sub>l _) \<longleftrightarrow> False" |
  "strict_no_jump (IF x = l\<^sub>1 AND y = l\<^sub>2 THEN GOTO\<^sub>l _) \<longleftrightarrow> False" |
  "strict_no_jump _ \<longleftrightarrow> True"

lemma strict_no_jump_no_jump[intro]:
  "strict_no_jump ins \<Longrightarrow> \<forall>s. no_jump s ins"
  by (cases ins) auto

lemma iexec\<^sub>l_strict_no_jump[intro]:
  assumes "strict_no_jump ins"
    shows "\<exists>s'. iexec\<^sub>l ins (pc, s) = (Suc pc, s')"
  using assms
  by (cases ins) auto

lemma execute_prog_strict_no_jump:
  assumes block_P_a_len: "0 < a \<and> a + len \<le> length P \<and> P \<noteq> []" \<comment>\<open>Please note that indices start from 1 instead of 0\<close>
      and block_strict_no_jump: "\<forall>i. a \<le> i \<and> i < a + len \<longrightarrow> strict_no_jump (P !! i)"
    shows "\<exists>s'. P \<turnstile>\<^sub>l (a, s) \<rightarrow>\<^bsub>len\<^esub> (a + len, s')"
  using assms
proof (induction len)
  case 0
  then show ?case by simp
next
  case (Suc len)
  then obtain s' where "P \<turnstile>\<^sub>l (a, s) \<rightarrow>\<^bsub>len\<^esub> (a + len, s')" by auto
  moreover
  from Suc.prems have "strict_no_jump (P !! (a + len))" by simp
  then obtain s'' where "iexec\<^sub>l (P !! (a + len)) (a + len, s') = (a + Suc len, s'')" by force
  then have "P \<turnstile>\<^sub>l (a + len, s') \<rightarrow> (a + Suc len, s'')" using Suc by auto
  ultimately
  show ?case by auto
qed

lemma execute_prog_strict_no_jump_mid_state:
  assumes block_P_a_len: "0 < a \<and> a + Suc len \<le> length P \<and> P \<noteq> []" \<comment>\<open>Please note that indices start from 1 instead of 0\<close>
      and block_strict_no_jump: "\<forall>i. a \<le> i \<and> i < a + Suc len \<longrightarrow> strict_no_jump (P !! i)"
      and final_state: "P \<turnstile>\<^sub>l (a, s) \<rightarrow>\<^bsub>Suc len\<^esub> (a + Suc len, t)"
    shows "\<exists>t'. (P \<turnstile>\<^sub>l (a, s) \<rightarrow>\<^bsub>len\<^esub> (a + len, t')) \<and> (P \<turnstile>\<^sub>l (a + len, t') \<rightarrow> (a + Suc len, t))"
proof -
  from block_P_a_len block_strict_no_jump
  obtain t' where t': "P \<turnstile>\<^sub>l (a, s) \<rightarrow>\<^bsub>len\<^esub> (a + len, t')"
    using execute_prog_strict_no_jump by fastforce
  from block_strict_no_jump have "strict_no_jump (P !! (a + len))" by auto
  with t' have "P \<turnstile>\<^sub>l (a + len, t') \<rightarrow> (a + Suc len, t)"
    by (metis exec\<^sub>l_t_determ final_state relpowp_Suc_E)
  with t' show ?thesis by blast
qed

text \<open>In the best situation, a block of program runs sequentially and the state remains the same.
This is luckily the case for the entrance block in the transformed program.\<close>
lemma iexec\<^sub>l_no_jump_and_no_modification[intro]:
  assumes "no_jump s ins" 
      and "no_modification ins"
    shows "iexec\<^sub>l ins (pc, s) = (Suc pc, s)"
  using assms
  by (cases ins) auto

lemma execute_prog_no_jump_and_no_modification:
  "0 < a \<and> a + len \<le> length P \<Longrightarrow> P \<noteq> [] \<Longrightarrow> \<comment>\<open>Please note that indices start from 1 instead of 0\<close>
   \<forall>i. a \<le> i \<and> i < a + len \<longrightarrow> no_jump s (P !! i) \<and> no_modification (P !! i) \<Longrightarrow>
   P \<turnstile>\<^sub>l (a, s) \<rightarrow>\<^bsub>len\<^esub> (a + len, s)"
proof (induction len)
  case 0
  then show ?case by auto
next
  case (Suc len)
  then have "P \<turnstile>\<^sub>l (a, s) \<rightarrow>\<^bsub>len\<^esub> (a + len, s)" by force
  moreover
  from Suc.prems have "no_jump s (P !! (a + len))" "no_modification (P !! (a + len))" by simp+
  then have "iexec\<^sub>l (P !! (a + len)) (a + len, s) = (a + Suc len, s)" by auto
  then have "P \<turnstile>\<^sub>l (a + len, s) \<rightarrow> (a + Suc len, s)" using Suc by auto
  ultimately
  show ?case by auto
qed

text \<open>Another informative situation is when the program runs sequentially, and some variable
is modified at most once. In this case the value of variable can be inferred statically
from the commands in the program block.\<close>

fun no_write :: "var\<^sub>l \<Rightarrow> GOTO\<^sub>l_instr \<Rightarrow> bool" where
  \<comment>\<open>ST, the state of the Turing Machine\<close>
  "no_write ST (x ::=\<^sub>l l) \<longleftrightarrow> x \<noteq> ST" |
  "no_write ST _ \<longleftrightarrow> True" |
  \<comment>\<open>TP n, the n-th tape of the Turing Machine\<close>
  "no_write (TP n) (x ::=\<^sub>l l) \<longleftrightarrow> x \<noteq> TP n" |
  "no_write (TP n) (TapeModify m v) \<longleftrightarrow> n \<noteq> m" |
  "no_write (TP n) _ \<longleftrightarrow> True" |
  \<comment>\<open>HP n, head position of the n-th tape of the Turing Machine\<close>
  "no_write (HP n) (x ::=\<^sub>l l) \<longleftrightarrow> x \<noteq> HP n" |
  "no_write (HP n) (MoveLeft m) \<longleftrightarrow> m \<noteq> n" |
  "no_write (HP n) (MoveRight m) \<longleftrightarrow> m \<noteq> n" |
  "no_write (HP n) _ \<longleftrightarrow> True" |
  \<comment>\<open>TMP n, other variables used in the program\<close>
  "no_write (TMP n) (x ::=\<^sub>l l) \<longleftrightarrow> x \<noteq> TMP n" |
  "no_write (TMP n) _ \<longleftrightarrow> True"

lemma iexec\<^sub>l_no_write[intro]:
  assumes "no_write x ins"
      and "iexec\<^sub>l ins (pc, s) = (pc', s')"
    shows "s' x = s x"
  using assms
  by (cases ins; cases x) auto

lemma execute_no_write_and_strict_no_jump:
  assumes block_P_a_len: "0 < a \<and> a + len \<le> length P \<and> P \<noteq> []" \<comment>\<open>Please note that indices start from 1 instead of 0\<close>
      and block_strict_no_jump_and_no_write:
          "\<forall>i. a \<le> i \<and> i < a + len \<longrightarrow> strict_no_jump (P !! i) \<and> no_write x (P !! i)"
      and final_state: "P \<turnstile>\<^sub>l (a, s) \<rightarrow>\<^bsub>len\<^esub> (a + len, s')"
    shows "s' x = s x"
  using assms
proof (induction len arbitrary: s')
  case 0
  then show ?case by auto
next
  case (Suc len)
  then have IH_cond: "0 < a \<and> a + len \<le> length P" "P \<noteq> []"
    "\<forall>i. a \<le> i \<and> i < a + len \<longrightarrow> strict_no_jump (P !! i) \<and> no_write x (P !! i)"
    by simp+
  with execute_prog_strict_no_jump obtain s_mid where s_mid: "P \<turnstile>\<^sub>l (a, s) \<rightarrow>\<^bsub>len\<^esub> (a + len, s_mid)"
    by blast
  with Suc.IH IH_cond have "s_mid x = s x" by blast
  moreover
  from Suc have prop_cur_ins: "strict_no_jump (P !! (a + len)) \<and> no_write x (P !! (a + len))" by auto
  then obtain s'' where s'': "P \<turnstile>\<^sub>l (a + len, s_mid) \<rightarrow> (a + Suc len, s'')"
    by (metis Suc.prems(3) exec\<^sub>l_t_determ relpowp_Suc_E s_mid)
  with prop_cur_ins have "s'' x = s_mid x" by blast
  moreover
  from s_mid s'' have "P \<turnstile>\<^sub>l (a, s) \<rightarrow>\<^bsub>Suc len\<^esub> (a + Suc len, s'')"
    by auto
  with \<open>P \<turnstile>\<^sub>l (a, s) \<rightarrow>\<^bsub>Suc len\<^esub> (a + Suc len, s')\<close> have "s' = s''" 
    using exec\<^sub>l_t_determ [where ?t = "Suc len"] by blast
  ultimately
  show ?case by simp
qed

fun vars_read_in_operi :: "GOTO\<^sub>l_operi \<Rightarrow> var\<^sub>l set" where
  "vars_read_in_operi (L l) = {}" |
  "vars_read_in_operi (V\<^sub>l y) = {y}" |
  "vars_read_in_operi (ReadChs tps) = (TP ` (set tps)) \<union> (HP ` (set tps))"

fun vars_read :: "GOTO\<^sub>l_instr \<Rightarrow> var\<^sub>l set" where
  "vars_read (x ::=\<^sub>l l) = vars_read_in_operi l" |
  "vars_read (TapeModify n v) = {TP n, HP n}" |
  "vars_read (MoveLeft n) = {HP n}" |
  "vars_read (MoveRight n) = {HP n}" |
  "vars_read (IF x = l THEN GOTO\<^sub>l label) = vars_read_in_operi l \<union> {x}" |
  "vars_read (IF x = l\<^sub>1 AND y = l\<^sub>2 THEN GOTO\<^sub>l label) =
     vars_read_in_operi l\<^sub>1 \<union> {x} \<union> vars_read_in_operi l\<^sub>2 \<union> {y}" |
  "vars_read _ = {}"

lemma iexec\<^sub>l_with_all_dependent_var_same:
  assumes "\<forall>y \<in> vars_read ins. s y = s' y"
      and "s x = s' x"
      and "iexec\<^sub>l ins (pc, s) = (pc', t)"
      and "iexec\<^sub>l ins (pc, s') = (pc', t')"
    shows "t x = t' x"
  using assms
  apply (cases ins)
  apply auto
  subgoal for operi
    by (cases operi) auto
  done

lemma execute_with_var_modified_at_most_once:
  assumes block_P_a_len: "0 < a \<and> a + len \<le> length P \<and> P \<noteq> []" \<comment>\<open>Please note that indices start from 1 instead of 0\<close>
        \<comment>\<open>ins_modify: the only possible point where x is modified\<close>
      and ins_modify: "a \<le> j \<and> j < a + len \<and> (P !! j) = ins_modify"
      and block_strict_no_jump: "\<forall>i. a \<le> i \<and> i < a + len \<longrightarrow> strict_no_jump (P !! i)"
      and other_cmd_no_write_x: "\<forall>i. a \<le> i \<and> i < a + len \<and> i \<noteq> j \<longrightarrow> no_write x (P !! i)"
      and dependent_vars_no_modify_before_ins:
          "\<forall>y \<in> vars_read ins_modify. \<forall>i. a \<le> i \<and> i < j \<longrightarrow> no_write y (P !! i)"
      and config_at_end: "P \<turnstile>\<^sub>l (a, s) \<rightarrow>\<^bsub>len\<^esub> (a + len, t)"
      and value_x: "\<forall>s'. iexec\<^sub>l ins_modify (j, s) = (Suc j, s') \<longrightarrow> s' x = v"
    shows "t x = v"
proof -
  from block_P_a_len ins_modify block_strict_no_jump
  obtain s_before_j where s_before_j: "P \<turnstile>\<^sub>l (a, s) \<rightarrow>\<^bsub>j - a\<^esub> (j, s_before_j)"
    using execute_prog_strict_no_jump [where ?len = "j - a" and ?P = P and ?a = a and ?s = s]
    by auto
  with block_P_a_len ins_modify block_strict_no_jump dependent_vars_no_modify_before_ins
  have "\<forall>y \<in> vars_read ins_modify. s y = s_before_j y"
    using execute_no_write_and_strict_no_jump
    by (smt (verit, ccfv_SIG) le_add_diff_inverse less_or_eq_imp_le trans_less_add1)
  moreover
  from block_P_a_len ins_modify block_strict_no_jump other_cmd_no_write_x s_before_j
  have "s x = s_before_j x"
    using execute_no_write_and_strict_no_jump
    by (smt (verit, ccfv_threshold) le_add_diff_inverse le_add_diff_inverse2 nat_less_le trans_less_add2)
  moreover
  from block_strict_no_jump ins_modify have "strict_no_jump ins_modify" by blast
  then obtain s_after_j where s_after_j: "iexec\<^sub>l ins_modify (j, s_before_j) = (Suc j, s_after_j)" by force
  moreover
  from block_strict_no_jump ins_modify have "strict_no_jump ins_modify" by blast
  then obtain s_after_j' where s_after_j': "iexec\<^sub>l ins_modify (j, s) = (Suc j, s_after_j')" by force
  ultimately
  have "s_after_j x = s_after_j' x"
    using iexec\<^sub>l_with_all_dependent_var_same [where ?pc = j and ?pc' = "Suc j" and ?ins = ins_modify
                                                and ?s = s and ?s' = s_before_j and ?t = s_after_j'
                                                and ?t' = s_after_j and ?x = x]
    by presburger
  with s_after_j' value_x have "s_after_j x = v" by blast

  from s_after_j block_P_a_len ins_modify have "P \<turnstile>\<^sub>l (j, s_before_j) \<rightarrow> (Suc j, s_after_j)"
    by (simp add: exec1\<^sub>l_I)
  with s_before_j ins_modify have s_to_s_after_j: "P \<turnstile>\<^sub>l (a, s) \<rightarrow>\<^bsub>Suc j - a\<^esub> (Suc j, s_after_j)"
    using Suc_diff_le by auto
    
  from block_P_a_len ins_modify block_strict_no_jump
  obtain t' where t': "P \<turnstile>\<^sub>l (Suc j, s_after_j) \<rightarrow>\<^bsub>a + len - Suc j\<^esub> (a + len, t')"
    using execute_prog_strict_no_jump [where ?len = "a + len - Suc j" and ?P = P and ?a = "Suc j" and ?s = s_after_j]
    by auto
  with s_to_s_after_j have "P \<turnstile>\<^sub>l (a, s) \<rightarrow>\<^bsub>len\<^esub> (a + len, t')"
    using exec\<^sub>l_t_add ins_modify le_imp_less_Suc by fastforce
  with config_at_end have "t = t'"
    using exec\<^sub>l_t_determ by blast

  from t' block_P_a_len ins_modify block_strict_no_jump other_cmd_no_write_x
  have "s_after_j x = t' x"
    using execute_no_write_and_strict_no_jump [where ?a = "Suc j" and ?len = "a + len - Suc j"
                                                 and ?P = P and ?x = x and ?s = s_after_j and ?s' = t']
    by force

  from \<open>s_after_j x = t' x\<close> \<open>t = t'\<close> \<open>s_after_j x = v\<close>
  show ?thesis by simp
qed

end