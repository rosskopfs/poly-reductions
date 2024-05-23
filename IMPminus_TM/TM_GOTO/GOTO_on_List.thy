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
    (if (s x = eval_GOTO\<^sub>l_operi s l) then label else pc, s)" |
  "iexec\<^sub>l (IF x = l1 AND y = l2 THEN GOTO\<^sub>l label) (pc, s) =
    (if s x = eval_GOTO\<^sub>l_operi s l1 \<and> s y = eval_GOTO\<^sub>l_operi s l2 then label else pc, s)"

definition exec1\<^sub>l :: "GOTO\<^sub>l_prog \<Rightarrow> config\<^sub>l \<Rightarrow> config\<^sub>l \<Rightarrow> bool" ("(_/ \<turnstile>\<^sub>l (_ \<rightarrow>/ _))" [59,0,59] 60) where
  "P \<turnstile>\<^sub>l cfg \<rightarrow> cfg' \<longleftrightarrow> (\<exists>pc s. cfg = (pc, s) \<and> cfg' = iexec\<^sub>l (P !! pc) cfg \<and>
                         P \<noteq> [] \<and> 0 < pc \<and> pc \<le> size P)"

text \<open>Note that pc = 0 is when the program halts\<close>
lemma exec1\<^sub>l_I [intro, code_pred_intro]:
  "c' = iexec\<^sub>l (P !! pc) (pc, s) \<Longrightarrow> P \<noteq> [] \<Longrightarrow> 0 < pc \<Longrightarrow> pc \<le> size P \<Longrightarrow> P \<turnstile>\<^sub>l (pc, s) \<rightarrow> c'"
  by (simp add: exec1\<^sub>l_def of_nat_diff)

lemma exec1\<^sub>l_pc_range [intro]:
  "P \<turnstile>\<^sub>l (pc, s) \<rightarrow> c' \<Longrightarrow> 0 < pc \<and> pc \<le> length P"
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
text \<open>This part draws largely on "HOL-IMP.Compiler"\<close>

fun ins_no_jump :: "state\<^sub>l \<Rightarrow> GOTO\<^sub>l_instr \<Rightarrow> bool" where
  "ins_no_jump s ins \<longleftrightarrow> (
    (\<nexists>n. ins = GOTO\<^sub>l n) \<and>
    (\<exists>x l n. ins = IF x = l THEN GOTO\<^sub>l n \<longrightarrow> s x \<noteq> eval_GOTO\<^sub>l_operi s l) \<and>
    (\<exists>x y l\<^sub>1 l\<^sub>2 n. (ins = IF x = l\<^sub>1 AND y = l\<^sub>1 THEN GOTO\<^sub>l n) \<longrightarrow>
         (s x \<noteq> eval_GOTO\<^sub>l_operi s l\<^sub>1 \<or> s y \<noteq> eval_GOTO\<^sub>l_operi s l\<^sub>2)))"

lemma iexec\<^sub>l_seq_independent_from_pc[simp]:
  assumes "ins_no_jump s ins"
    shows "iexec\<^sub>l ins (pc, s) = (pc', s') \<Longrightarrow> \<forall>pc''. iexec\<^sub>l ins (pc, s) = (pc', s')"
  using assms
  by (auto split: GOTO\<^sub>l_instr.split)

lemma exec1\<^sub>l_appendR:
  assumes "ins_no_jump s (P!!pc)"
    shows "P \<turnstile>\<^sub>l (pc, s) \<rightarrow> c' \<Longrightarrow> P @ P' \<turnstile>\<^sub>l (pc, s) \<rightarrow> c'"
  by (auto simp: exec1\<^sub>l_def)

lemma exec_appendR:
  assumes "\<forall>ins \<in> set P. ins_no_jump s ins"
    shows "P \<turnstile>\<^sub>l (pc, s) \<rightarrow>* c'' \<Longrightarrow> P @ P' \<turnstile>\<^sub>l (pc, s) \<rightarrow>* c''"
proof (induction "(pc, s)" c'' rule: star.induct)
  case refl
  then show ?case by blast
next
  case (step c' c'')
  with exec1\<^sub>l_pc_range have "0 < pc \<and> pc \<le> length P" by blast
  then have "P !! pc \<in> set P" by blast
  with assms have "ins_no_jump s (P !! pc)" by blast
  with step exec1\<^sub>l_appendR have "P @ P' \<turnstile>\<^sub>l (pc, s) \<rightarrow> c'" by blast
  with step show ?case  sorry
qed

end