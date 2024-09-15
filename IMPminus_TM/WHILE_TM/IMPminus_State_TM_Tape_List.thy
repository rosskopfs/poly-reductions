theory IMPminus_State_TM_Tape_List
  imports IMP_Minus.Com Cook_Levin.Basics Cook_Levin.Arithmetic "List-Index.List_Index" 
begin

subsection \<open>Collect all variables in an IMP_Minus program\<close>

subsubsection \<open>Get variable set of an IMP_Minus program\<close>
fun var_set_of_atomExp :: "atomExp \<Rightarrow> vname set" where
  "var_set_of_atomExp (N _) = {}" |
  "var_set_of_atomExp (V x) = {x}"

fun atomExp_set_of_aexp :: "aexp \<Rightarrow> atomExp set" where
  "atomExp_set_of_aexp (A a) = {a}" |
  "atomExp_set_of_aexp (a\<^sub>1 \<oplus> a\<^sub>2) = {a\<^sub>1, a\<^sub>2}" |
  "atomExp_set_of_aexp (a\<^sub>1 \<ominus> a\<^sub>2) = {a\<^sub>1, a\<^sub>2}" |
  "atomExp_set_of_aexp (a \<doteq>1) = {a}" |
  "atomExp_set_of_aexp (a\<then>) = {a}"
                                      
fun var_set_of_aexp :: "aexp \<Rightarrow> vname set" where
  "var_set_of_aexp a = \<Union> (var_set_of_atomExp ` atomExp_set_of_aexp a)"

fun var_set :: "com \<Rightarrow> vname set" where
  "var_set SKIP = {}" |
  "var_set (x ::= a) = {x} \<union> var_set_of_aexp a" |
  "var_set (c\<^sub>1;; c\<^sub>2) = var_set c\<^sub>1 \<union> var_set c\<^sub>2" |
  "var_set (IF x\<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2) = {x} \<union> var_set c\<^sub>1 \<union> var_set c\<^sub>2" |
  "var_set (WHILE x\<noteq>0 DO c) = {x} \<union> var_set c"

subsubsection \<open>Get variable list of an IMP_Minus program\<close>
fun vars_of_atomExp :: "atomExp \<Rightarrow> vname list" where
  "vars_of_atomExp (N _) = []" |
  "vars_of_atomExp (V x) = [x]"

fun vars_of_aexp :: "aexp \<Rightarrow> vname list" where
  "vars_of_aexp (A a) = vars_of_atomExp a" |
  "vars_of_aexp (a\<^sub>1 \<oplus> a\<^sub>2) = vars_of_atomExp a\<^sub>1 @ vars_of_atomExp a\<^sub>2" |
  "vars_of_aexp (a\<^sub>1 \<ominus> a\<^sub>2) = vars_of_atomExp a\<^sub>1 @ vars_of_atomExp a\<^sub>2" |
  "vars_of_aexp (a \<doteq>1) = vars_of_atomExp a" |
  "vars_of_aexp (a\<then>) = vars_of_atomExp a"

fun vars_aux :: "com \<Rightarrow> vname list" where
  "vars_aux SKIP = []" |
  "vars_aux (x ::= a) = x # vars_of_aexp a" |
  "vars_aux (c\<^sub>1;; c\<^sub>2) = vars_aux c\<^sub>1 @ vars_aux c\<^sub>2" |
  "vars_aux (IF x\<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2) = x # vars_aux c\<^sub>1 @ vars_aux c\<^sub>2" |
  "vars_aux (WHILE x\<noteq>0 DO c) = x # vars_aux c"

fun vars :: "com \<Rightarrow> vname list" where
  "vars prog = remdups (vars_aux prog)"

subsubsection \<open>Equivalence of the two collectors of variables\<close>
lemma vars_of_atomExp_set [simp]:
  "set (vars_of_atomExp a) = var_set_of_atomExp a"
  by (cases a) auto

lemma vars_of_aexp_set [simp]:
  "set (vars_of_aexp a) = var_set_of_aexp a"
  by (cases a) auto

lemma vars_aux_set [simp]:
  "set (vars_aux prog) = var_set prog"
  by (induction prog) auto

subsection \<open>Translation between variables and tape numbers\<close>

fun var_to_tape_number :: "com \<Rightarrow> (vname \<Rightarrow> tapeidx)" where
  "var_to_tape_number prog x = index (vars prog) x + 3" \<comment>\<open>The first 3 tapes are for special usages\<close>

fun tape_number_to_var :: "com \<Rightarrow> nat \<Rightarrow> vname" where
  "tape_number_to_var prog n = (vars prog) ! (n - 3)"

lemma var_tape_number_var [simp]:
  assumes "x \<in> var_set prog"
    shows "tape_number_to_var prog (var_to_tape_number prog x) = x"
  using assms by simp

lemma tape_number_var_tape_number [simp]:
  assumes "n \<ge> 3"
      and "n < length (vars prog) + 3"
    shows "var_to_tape_number prog (tape_number_to_var prog n) = n"
  using assms
  by (simp add: index_nth_id)

subsection \<open>Translation between IMP- state and TM tape list\<close>
text \<open>Natural numbers are represented by the reverse order of their binary form.
An example: 10 in decimal equals 1010 in binary, so the tape content would be:
(start symbol) 0 1 0 1 (blank symbols)\<close>

fun IMPminus_state_to_TM_tape_list :: "com \<Rightarrow> AExp.state \<Rightarrow> tape list" where
  "IMPminus_state_to_TM_tape_list prog s =
   (\<lfloor>0\<rfloor>\<^sub>N, 1) # \<comment>\<open>read only tape, unused\<close>
   (\<lfloor>0\<rfloor>\<^sub>N, 1) # \<comment>\<open>1. operand\<close>
   (\<lfloor>0\<rfloor>\<^sub>N, 1) # \<comment>\<open>2. operand\<close>
   map (\<lambda>x. (\<lfloor>(s x)\<rfloor>\<^sub>N, 1)) (vars prog) @ \<comment>\<open>tapes for each variable\<close>
   [(\<lfloor>0\<rfloor>\<^sub>N, 1)]" \<comment>\<open>last tape for carry, see Memorizing.thy in afp entry Cook_Levin\<close>
                                     
subsection \<open>Equivalence checking of IMP- state and TM tape list\<close>
fun tape_content_to_num :: "tape \<Rightarrow> nat" where
  "tape_content_to_num tp = (THE n. \<lfloor>n\<rfloor>\<^sub>N = fst tp)"

fun initial_tape :: "tape list  \<Rightarrow> bool"
where  
" initial_tape tps \<longleftrightarrow> (tps!0=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and>  (tps!1=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and> (tps!2=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and> ( tps!(length tps-1)= \<lceil>\<triangleright>\<rceil>)"

fun proper_tape ::"tape list \<Rightarrow>bool "
  where
"proper_tape tps \<longleftrightarrow> length tps\<ge>4 \<and> (\<forall>i<(length tps). clean_tape (tps!i))"

fun variable_tape_list_equiv_IMPminus_state :: "vname \<Rightarrow>(vname\<Rightarrow>nat) \<Rightarrow> tape list \<Rightarrow> AExp.state \<Rightarrow> bool" (\<open>_-_ \<turnstile> _ \<sim> _\<close> 55)
where  
  "v-idd \<turnstile> tps \<sim> s \<longleftrightarrow>((tps ! idd v) =(\<lfloor>s v\<rfloor>\<^sub>N, 1))"

fun tape_list_equiv_IMPminus_state_on_a_set :: "(vname set) \<Rightarrow>(vname\<Rightarrow>nat) \<Rightarrow> tape list \<Rightarrow> AExp.state \<Rightarrow> bool" (\<open>_ @ _ \<turnstile> _ \<sim> _\<close> 55)
where  
  "S @ idd \<turnstile> tps \<sim> s \<longleftrightarrow>(\<forall>v\<in>S. idd v\<ge>3 \<and> idd v+1 < length tps\<and> v-idd \<turnstile> tps \<sim> s) \<and> inj_on idd S "

lemma equiv_monoton:" S2\<subseteq>S \<longrightarrow> S@idd \<turnstile> tps \<sim> s \<longrightarrow>  S2@idd \<turnstile> tps \<sim> s"
  apply auto using inj_on_subset by blast

lemma var_prog_finite :"finite (var_set prog)"
  by (metis List.finite_set vars_aux_set)

(*
lemma tape_list_equiv_IMPminus_state_for_Seq:
  assumes "(prog1;;prog2) @ idd \<turnstile> tps \<sim> s" 
  shows"prog1 @idd \<turnstile> tps \<sim> s " 
proof -
  have "idd ` var_set prog1 \<subseteq> idd ` var_set (prog1;;prog2)"  by (simp add: image_mono)
  then show "prog1 (idd) \<turnstile> tps \<sim> s " using assms by auto
qed
*)
end