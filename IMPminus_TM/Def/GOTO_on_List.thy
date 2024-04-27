text \<open>A GOTO-like language that works on list.
Used as intermediate of multitape TM and GOTO program.
Generally, one list here imitates one tape from the TM.\<close>

theory GOTO_on_List
  imports Global_Defs "HOL-IMP.Star"
begin

datatype GOTO\<^sub>l_operi =
  L "val list" |
  V\<^sub>l vname |
  Index "vname list" vname
\<comment> \<open>Index: Indexing each variable (which stores a list)
    with the indices stored in the variable as the second parameter.
    E.g. Index [''v0'', ''v1'', ''v2''] ''ps'', under the following state:
    <''v0''=[0,1], ''v1''=[10,11], ''v2''=[20,21], ''ps''=[0,0,1]>
    Result would be [0,10,21].
    In the context of the corresponding multitape-TM:
    variables in the list stores content of tapes;
    the second variable stores head positions of each tapes\<close>
\<comment> \<open>This example can be found at the end of this file\<close>


datatype GOTO\<^sub>l_instr =
  HALT\<^sub>l |
  Assign vname GOTO\<^sub>l_operi (\<open>_ ::=\<^sub>l _\<close>)|
  Modify vname nat val (\<open>_\<^bsub>_\<^esub> ::= _\<close>) |
  Jmp label (\<open>GOTO\<^sub>l _\<close>) |
  CondJmp vname GOTO\<^sub>l_operi label (\<open>IF _ = _ THEN GOTO\<^sub>l _\<close>)

type_synonym GOTO\<^sub>l_prog = "GOTO\<^sub>l_instr list"
type_synonym state\<^sub>l = "vname \<Rightarrow> val list"
type_synonym config\<^sub>l = "pc \<times> state\<^sub>l"

fun eval_GOTO\<^sub>l_operi :: "state\<^sub>l \<Rightarrow> GOTO\<^sub>l_operi \<Rightarrow> val list" where
  "eval_GOTO\<^sub>l_operi s (L l) = l" |
  "eval_GOTO\<^sub>l_operi s (V\<^sub>l x) = s x" |
  "eval_GOTO\<^sub>l_operi s (Index vs l) = map (\<lambda>v_i. (s (fst v_i)) ! (snd v_i)) (zip vs (s l))"

definition is_halt\<^sub>l :: "config\<^sub>l \<Rightarrow> bool" where
  "is_halt\<^sub>l c \<longleftrightarrow> fst c = 0"

fun iexec\<^sub>l :: "GOTO\<^sub>l_instr \<Rightarrow> config\<^sub>l \<Rightarrow> config\<^sub>l" where
  "iexec\<^sub>l HALT\<^sub>l         (pc, s) = (0, s)" |
  "iexec\<^sub>l (x ::=\<^sub>l l)    (pc, s) = (Suc pc, s(x := eval_GOTO\<^sub>l_operi s l))" |
  "iexec\<^sub>l (x\<^bsub>i\<^esub> ::= v)  (pc, s) = (Suc pc, s(x := (s x)[i := v]))" |
  "iexec\<^sub>l (GOTO\<^sub>l label) (pc, s) = (label, s)" |
  "iexec\<^sub>l (IF x = l THEN GOTO\<^sub>l label) (pc, s) =
    (if (s x = eval_GOTO\<^sub>l_operi s l) then label else pc, s)"

definition exec1\<^sub>l :: "GOTO\<^sub>l_prog \<Rightarrow> config\<^sub>l \<Rightarrow> config\<^sub>l \<Rightarrow> bool" ("(_/ \<turnstile>\<^sub>l (_ \<rightarrow>/ _))" [59,0,59] 60) where
  "P \<turnstile>\<^sub>l cfg \<rightarrow> cfg' = (\<exists>pc s. cfg = (pc, s) \<and> cfg' = iexec\<^sub>l (P !! pc) cfg \<and> 0 < pc \<and> pc \<le> size P)"

lemma exec1\<^sub>l_I [intro, code_pred_intro]:
  "c' = iexec\<^sub>l (P !! pc) (pc, s) \<Longrightarrow> 0 < pc \<Longrightarrow> pc \<le> size P \<Longrightarrow> P \<turnstile>\<^sub>l (pc, s) \<rightarrow> c'"
  by (simp add: exec1\<^sub>l_def of_nat_diff)

abbreviation 
  exec\<^sub>l :: "GOTO\<^sub>l_prog \<Rightarrow> config\<^sub>l \<Rightarrow> config\<^sub>l \<Rightarrow> bool" ("(_/ \<turnstile> (_ \<rightarrow>*/ _))" 50)
where
  "exec\<^sub>l P \<equiv> star (exec1\<^sub>l P)"

lemmas exec\<^sub>l_induct = star.induct [of "exec1\<^sub>l P", split_format(complete)]

code_pred exec1\<^sub>l using exec1\<^sub>l_I exec1\<^sub>l_def by auto

text \<open>An example of list modification\<close>
values
  "{(pc, map t [''x'']) | pc t. (
    [''x'' ::=\<^sub>l (L [0, 1, 2]), ''x''\<^bsub>2\<^esub> ::= 100, HALT\<^sub>l] \<turnstile>
    (1, (\<lambda>x. [])) \<rightarrow>* (pc, t))}"

text \<open>An example illustrating the semantical meaning of "Index"\<close>
values
  "{(pc, map t [''x'', ''y'', ''z'', ''ps'', ''res'']) | pc t. (
    [''x'' ::=\<^sub>l (L [0, 1]), ''y'' ::=\<^sub>l (L [10, 11]), ''z'' ::=\<^sub>l (L [20, 21]),
     ''ps'' ::=\<^sub>l (L [0, 0, 1]),
     ''res'' ::=\<^sub>l (Index [''x'', ''y'', ''z''] ''ps''), HALT\<^sub>l] \<turnstile>
    (1, (\<lambda>x. [])) \<rightarrow>* (pc, t))}"

end