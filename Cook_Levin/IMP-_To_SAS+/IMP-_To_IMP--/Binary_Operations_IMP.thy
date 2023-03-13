theory Binary_Operations_IMP
  imports
    Primitives_IMP_Minus
    Binary_Arithmetic_IMP
    IMP_Minus_To_IMP_Minus_Minus_State_Translations_IMP
    Binary_Operations_Nat
    IMP_Minus.Com
    Utilities
begin

unbundle IMP_Minus_Minus_Com.no_com_syntax


subsection copy_var_to_operand

subsubsection copy_var_to_operand_aux1

record copy_var_to_operand_aux1_state=
copy_var_to_operand_aux1_op::nat
copy_var_to_operand_aux1_diff::nat
copy_var_to_operand_aux1_ret::nat

abbreviation "copy_var_to_operand_aux1_prefix \<equiv> ''copy_var_to_operand_aux1_op.''"
abbreviation "copy_var_to_operand_aux1_op_str \<equiv> ''op''"
abbreviation "copy_var_to_operand_aux1_diff_str \<equiv> ''diff''"
abbreviation "copy_var_to_operand_aux1_ret_str \<equiv> ''ret''"

definition "copy_var_to_operand_aux1_imp_state_upd s \<equiv> 
 (let
   prod_encode_a' = copy_var_to_operand_aux1_op s;
   prod_encode_b' = copy_var_to_operand_aux1_diff s;
   prod_encode_ret' = 0;
   prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                       prod_encode_b = prod_encode_b',
                       prod_encode_ret = prod_encode_ret'\<rparr>;
   prod_encode_ret_state = prod_encode_imp prod_encode_state;
   var_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
   var_bit_to_var_tail_ret' = 0;
   var_bit_to_var_tail_state = \<lparr>var_bit_to_var_tail_n = var_bit_to_var_tail_n',
                               var_bit_to_var_tail_ret = var_bit_to_var_tail_ret'\<rparr>;
   var_bit_to_var_tail_ret_state = var_bit_to_var_tail_imp var_bit_to_var_tail_state;

   cons_h' = var_bit_to_var_tail_ret var_bit_to_var_tail_ret_state;
   cons_t' = 0;
   cons_ret' = 0;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;

   copy_var_to_operand_aux1_ret' = cons_ret cons_ret_state;
   ret = \<lparr>copy_var_to_operand_aux1_op = copy_var_to_operand_aux1_op s,
         copy_var_to_operand_aux1_diff = copy_var_to_operand_aux1_diff s,
         copy_var_to_operand_aux1_ret = copy_var_to_operand_aux1_ret'\<rparr>
  in
   ret)"

function copy_var_to_operand_aux1_imp 
 :: "copy_var_to_operand_aux1_state \<Rightarrow> copy_var_to_operand_aux1_state" where 
"copy_var_to_operand_aux1_imp s = 
  (let
     ret = copy_var_to_operand_aux1_imp_state_upd s
   in
    ret)" by simp+
termination 
  by (relation "measure copy_var_to_operand_aux1_op", simp)

declare copy_var_to_operand_aux1_imp.simps[simp del]

lemma copy_var_to_operand_aux1_imp_correct[let_function_correctness]:
  "copy_var_to_operand_aux1_ret (copy_var_to_operand_aux1_imp s)
    = ((var_bit_to_var_tail (prod_encode (
        (copy_var_to_operand_aux1_op s), (copy_var_to_operand_aux1_diff s)))) ## 0)"
apply (subst copy_var_to_operand_aux1_imp.simps copy_var_to_operand_aux1_imp_state_upd_def)+
apply (auto simp add: Let_def var_bit_to_var_tail_imp_correct 
  cons_imp_correct prod_encode_imp_correct)
done 

definition "copy_var_to_operand_aux1_imp_state_upd_time t s \<equiv> 
 (let
   prod_encode_a' = copy_var_to_operand_aux1_op s;
   t = t + 2;
   prod_encode_b' = copy_var_to_operand_aux1_diff s;
   t = t + 2;
   prod_encode_ret' = 0;
   t = t + 2;
   prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                       prod_encode_b = prod_encode_b',
                       prod_encode_ret = prod_encode_ret'\<rparr>;
   prod_encode_ret_state = prod_encode_imp prod_encode_state;
   t = t + prod_encode_imp_time 0 prod_encode_state;

   var_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
   t = t + 2;
   var_bit_to_var_tail_ret' = 0;
   t = t + 2;
   var_bit_to_var_tail_state = \<lparr>var_bit_to_var_tail_n = var_bit_to_var_tail_n',
                               var_bit_to_var_tail_ret = var_bit_to_var_tail_ret'\<rparr>;
   var_bit_to_var_tail_ret_state = var_bit_to_var_tail_imp var_bit_to_var_tail_state;
   t = t + var_bit_to_var_tail_imp_time 0 var_bit_to_var_tail_state;

   cons_h' = var_bit_to_var_tail_ret var_bit_to_var_tail_ret_state;
   t = t + 2;
   cons_t' = 0;
   t = t + 2;
   cons_ret' = 0;
   t = t + 2;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

   copy_var_to_operand_aux1_ret' = cons_ret cons_ret_state;
   t = t + 2;
   ret = \<lparr>copy_var_to_operand_aux1_op = copy_var_to_operand_aux1_op s,
         copy_var_to_operand_aux1_diff = copy_var_to_operand_aux1_diff s,
         copy_var_to_operand_aux1_ret = copy_var_to_operand_aux1_ret'\<rparr>
  in
   t)"

function copy_var_to_operand_aux1_imp_time 
 :: "nat \<Rightarrow> copy_var_to_operand_aux1_state \<Rightarrow> nat" where 
"copy_var_to_operand_aux1_imp_time t s = 
  (let
     ret = copy_var_to_operand_aux1_imp_state_upd s;
     t = t + copy_var_to_operand_aux1_imp_state_upd_time 0 s
   in
    t)" by auto
termination 
  by (relation "measure (copy_var_to_operand_aux1_op \<circ> snd)", simp)

definition "copy_var_to_operand_aux1_IMP_Minus \<equiv> 
  (prod_encode_prefix @ prod_encode_a_str) ::= A (V copy_var_to_operand_aux1_op_str);;
  (prod_encode_prefix @ prod_encode_b_str) ::= A (V copy_var_to_operand_aux1_diff_str);;
  (prod_encode_prefix @ prod_encode_ret_str) ::= A (N 0);;
  invoke_subprogram prod_encode_prefix prod_encode_IMP_Minus;;
  
  (var_bit_to_var_tail_prefix @ var_bit_to_var_tail_n_str) ::= A (V (prod_encode_prefix @ prod_encode_ret_str));;
  (var_bit_to_var_tail_prefix @ var_bit_to_var_tail_ret_str) ::= A (N 0);;
  invoke_subprogram var_bit_to_var_tail_prefix var_bit_to_var_tail_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (var_bit_to_var_tail_prefix @ var_bit_to_var_tail_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  copy_var_to_operand_aux1_ret_str ::= A (V (cons_prefix @ cons_ret_str))"

abbreviation "copy_var_to_operand_aux1_IMP_vars \<equiv> 
  {copy_var_to_operand_aux1_op_str, copy_var_to_operand_aux1_diff_str, copy_var_to_operand_aux1_ret_str}"

definition "copy_var_to_operand_aux1_imp_to_HOL_state p s \<equiv> 
  \<lparr>copy_var_to_operand_aux1_op = s (add_prefix p copy_var_to_operand_aux1_op_str),
  copy_var_to_operand_aux1_diff = s (add_prefix p copy_var_to_operand_aux1_diff_str),
  copy_var_to_operand_aux1_ret = s (add_prefix p copy_var_to_operand_aux1_ret_str)\<rparr>"

lemmas copy_var_to_operand_aux1_state_translators =
  copy_var_to_operand_aux1_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  var_bit_to_var_tail_imp_to_HOL_state_def 
  prod_encode_imp_to_HOL_state_def

lemma copy_var_to_operand_aux1_IMP_Minus_correct_function:
  "(invoke_subprogram p copy_var_to_operand_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_var_to_operand_aux1_ret_str)
      = copy_var_to_operand_aux1_ret (copy_var_to_operand_aux1_imp (copy_var_to_operand_aux1_imp_to_HOL_state p s))"
  apply (simp only: copy_var_to_operand_aux1_imp.simps copy_var_to_operand_aux1_imp_state_upd_def)
  apply (simp only: copy_var_to_operand_aux1_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule prod_encode_IMP_Minus_correct[where vars=copy_var_to_operand_aux1_IMP_vars])
  subgoal premises p using p(12) by fastforce
  apply (erule var_bit_to_var_tail_IMP_Minus_correct[where vars=copy_var_to_operand_aux1_IMP_vars])
  subgoal premises p using p(14) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux1_IMP_vars])
  subgoal premises p using p(16) by fastforce
  apply (force simp add: copy_var_to_operand_aux1_state_translators Let_def)
  done 

lemma copy_var_to_operand_aux1_IMP_Minus_correct_time:
  "(invoke_subprogram p copy_var_to_operand_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = copy_var_to_operand_aux1_imp_time 0 (copy_var_to_operand_aux1_imp_to_HOL_state p s)"
  apply (simp only: copy_var_to_operand_aux1_imp_time.simps copy_var_to_operand_aux1_imp_state_upd_time_def)
  apply (simp only: copy_var_to_operand_aux1_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule prod_encode_IMP_Minus_correct[where vars=copy_var_to_operand_aux1_IMP_vars])
  subgoal premises p using p(23) by fastforce
  apply (erule var_bit_to_var_tail_IMP_Minus_correct[where vars=copy_var_to_operand_aux1_IMP_vars])
  subgoal premises p using p(25) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux1_IMP_vars])
  subgoal premises p using p(27) by fastforce
  apply (force simp add: copy_var_to_operand_aux1_state_translators Let_def)
  done 

lemma copy_var_to_operand_aux1_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_var_to_operand_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
     \<lbrakk>t = (copy_var_to_operand_aux1_imp_time 0 (copy_var_to_operand_aux1_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) copy_var_to_operand_aux1_ret_str) =
        copy_var_to_operand_aux1_ret
          (copy_var_to_operand_aux1_imp (copy_var_to_operand_aux1_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_var_to_operand_aux1_IMP_Minus_correct_function 
      copy_var_to_operand_aux1_IMP_Minus_correct_time
       set_mono_prefix
  by (smt (verit, ccfv_SIG) com_add_prefix_valid_subset com_only_vars)

subsubsection copy_var_to_operand_aux2

record copy_var_to_operand_aux2_state=
copy_var_to_operand_aux2_op::nat
copy_var_to_operand_aux2_diff::nat
copy_var_to_operand_aux2_ret::nat

abbreviation "copy_var_to_operand_aux2_prefix \<equiv> ''copy_var_to_operand_aux2_op.''"
abbreviation "copy_var_to_operand_aux2_op_str \<equiv> ''op''"
abbreviation "copy_var_to_operand_aux2_diff_str \<equiv> ''diff''"
abbreviation "copy_var_to_operand_aux2_ret_str \<equiv> ''ret''"

definition "copy_var_to_operand_aux2_imp_state_upd s \<equiv> 
 (let
   prod_encode_a' = copy_var_to_operand_aux2_op s;
   prod_encode_b' = copy_var_to_operand_aux2_diff s;
   prod_encode_ret' = 0;
   prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                       prod_encode_b = prod_encode_b',
                       prod_encode_ret = prod_encode_ret'\<rparr>;
   prod_encode_ret_state = prod_encode_imp prod_encode_state;
   operand_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
   operand_bit_to_var_tail_ret' = 0;
   operand_bit_to_var_tail_state = \<lparr>operand_bit_to_var_tail_n = operand_bit_to_var_tail_n',
                               operand_bit_to_var_tail_ret = operand_bit_to_var_tail_ret'\<rparr>;
   operand_bit_to_var_tail_ret_state = operand_bit_to_var_tail_imp operand_bit_to_var_tail_state;

   cons_h' = 1;
   cons_t' = 0;
   cons_ret' = 0;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;

   cons_h' = operand_bit_to_var_tail_ret operand_bit_to_var_tail_ret_state;
   cons_t' = cons_ret cons_ret_state;
   cons_ret' = 0;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;

   cons_h' = 1;
   cons_t' = cons_ret cons_ret_state;
   cons_ret' = 0;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;

   copy_var_to_operand_aux2_ret' = cons_ret cons_ret_state;
   ret = \<lparr>copy_var_to_operand_aux2_op = copy_var_to_operand_aux2_op s,
         copy_var_to_operand_aux2_diff = copy_var_to_operand_aux2_diff s,
         copy_var_to_operand_aux2_ret = copy_var_to_operand_aux2_ret'\<rparr>
  in
   ret)"

function copy_var_to_operand_aux2_imp 
 :: "copy_var_to_operand_aux2_state \<Rightarrow> copy_var_to_operand_aux2_state" where 
"copy_var_to_operand_aux2_imp s = 
  (let
     ret = copy_var_to_operand_aux2_imp_state_upd s
   in
    ret)" by simp+
termination 
  by (relation "measure copy_var_to_operand_aux2_op", simp)

declare copy_var_to_operand_aux2_imp.simps[simp del]

lemma copy_var_to_operand_aux2_imp_correct[let_function_correctness]:
  "copy_var_to_operand_aux2_ret (copy_var_to_operand_aux2_imp s)
    = (1 ## (operand_bit_to_var_tail (prod_encode (
        (copy_var_to_operand_aux2_op s), (copy_var_to_operand_aux2_diff s)))) ## 1 ## 0)"
apply (subst copy_var_to_operand_aux2_imp.simps copy_var_to_operand_aux2_imp_state_upd_def)+
apply (auto simp add: Let_def operand_bit_to_var_tail_imp_correct 
  cons_imp_correct prod_encode_imp_correct)
done 

definition "copy_var_to_operand_aux2_imp_state_upd_time t s \<equiv> 
 (let
   prod_encode_a' = copy_var_to_operand_aux2_op s;
   t = t + 2;
   prod_encode_b' = copy_var_to_operand_aux2_diff s;
   t = t + 2;
   prod_encode_ret' = 0;
   t = t + 2;
   prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                       prod_encode_b = prod_encode_b',
                       prod_encode_ret = prod_encode_ret'\<rparr>;
   prod_encode_ret_state = prod_encode_imp prod_encode_state;
   t = t + prod_encode_imp_time 0 prod_encode_state;

   operand_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
   t = t + 2;
   operand_bit_to_var_tail_ret' = 0;
   t = t + 2;
   operand_bit_to_var_tail_state = \<lparr>operand_bit_to_var_tail_n = operand_bit_to_var_tail_n',
                               operand_bit_to_var_tail_ret = operand_bit_to_var_tail_ret'\<rparr>;
   operand_bit_to_var_tail_ret_state = operand_bit_to_var_tail_imp operand_bit_to_var_tail_state;
   t = t + operand_bit_to_var_tail_imp_time 0 operand_bit_to_var_tail_state;

   cons_h' = 1;
   t = t + 2;
   cons_t' = 0;
   t = t + 2;
   cons_ret' = 0;
   t = t + 2;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

   cons_h' = operand_bit_to_var_tail_ret operand_bit_to_var_tail_ret_state;
   t = t + 2;
   cons_t' = cons_ret cons_ret_state;
   t = t + 2;
   cons_ret' = 0;
   t = t + 2;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

   cons_h' = 1;
   t = t + 2;
   cons_t' = cons_ret cons_ret_state;
   t = t + 2;
   cons_ret' = 0;
   t = t + 2;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

   copy_var_to_operand_aux2_ret' = cons_ret cons_ret_state;
   t = t + 2;
   ret = \<lparr>copy_var_to_operand_aux2_op = copy_var_to_operand_aux2_op s,
         copy_var_to_operand_aux2_diff = copy_var_to_operand_aux2_diff s,
         copy_var_to_operand_aux2_ret = copy_var_to_operand_aux2_ret'\<rparr>
  in
   t)"

function copy_var_to_operand_aux2_imp_time 
 :: "nat \<Rightarrow> copy_var_to_operand_aux2_state \<Rightarrow> nat" where 
"copy_var_to_operand_aux2_imp_time t s = 
  (let
     ret = copy_var_to_operand_aux2_imp_state_upd s;
     t = t + copy_var_to_operand_aux2_imp_state_upd_time 0 s
   in
    t)" by auto
termination 
  by (relation "measure (copy_var_to_operand_aux2_op \<circ> snd)", simp)

definition "copy_var_to_operand_aux2_IMP_Minus \<equiv> 
  (prod_encode_prefix @ prod_encode_a_str) ::= A (V copy_var_to_operand_aux2_op_str);;
  (prod_encode_prefix @ prod_encode_b_str) ::= A (V copy_var_to_operand_aux2_diff_str);;
  (prod_encode_prefix @ prod_encode_ret_str) ::= A (N 0);;
  invoke_subprogram prod_encode_prefix prod_encode_IMP_Minus;;
  
  (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_n_str) ::= A (V (prod_encode_prefix @ prod_encode_ret_str));;
  (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str) ::= A (N 0);;
  invoke_subprogram operand_bit_to_var_tail_prefix operand_bit_to_var_tail_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (N 1);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (N 1);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  copy_var_to_operand_aux2_ret_str ::= A (V (cons_prefix @ cons_ret_str))"

abbreviation "copy_var_to_operand_aux2_IMP_vars \<equiv> 
  {copy_var_to_operand_aux2_op_str, copy_var_to_operand_aux2_diff_str, copy_var_to_operand_aux2_ret_str}"

definition "copy_var_to_operand_aux2_imp_to_HOL_state p s \<equiv> 
  \<lparr>copy_var_to_operand_aux2_op = s (add_prefix p copy_var_to_operand_aux2_op_str),
  copy_var_to_operand_aux2_diff = s (add_prefix p copy_var_to_operand_aux2_diff_str),
  copy_var_to_operand_aux2_ret = s (add_prefix p copy_var_to_operand_aux2_ret_str)\<rparr>"

lemmas copy_var_to_operand_aux2_state_translators =
  copy_var_to_operand_aux2_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  operand_bit_to_var_tail_imp_to_HOL_state_def 
  prod_encode_imp_to_HOL_state_def

lemma copy_var_to_operand_aux2_IMP_Minus_correct_function:
  "(invoke_subprogram p copy_var_to_operand_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_var_to_operand_aux2_ret_str)
      = copy_var_to_operand_aux2_ret (copy_var_to_operand_aux2_imp (copy_var_to_operand_aux2_imp_to_HOL_state p s))"
  apply (simp only: copy_var_to_operand_aux2_imp.simps copy_var_to_operand_aux2_imp_state_upd_def)
  apply (simp only: copy_var_to_operand_aux2_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule prod_encode_IMP_Minus_correct[where vars=copy_var_to_operand_aux2_IMP_vars])
  subgoal premises p using p(20) by fastforce
  apply (erule operand_bit_to_var_tail_IMP_Minus_correct[where vars=copy_var_to_operand_aux2_IMP_vars])
  subgoal premises p using p(22) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux2_IMP_vars])
  subgoal premises p using p(24) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux2_IMP_vars])
  subgoal premises p using p(26) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars="copy_var_to_operand_aux2_IMP_vars 
    \<union> {operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str}"])
  subgoal premises p using p(28) by fastforce
  apply (force simp: copy_var_to_operand_aux2_state_translators Let_def) 
  done 

lemma copy_var_to_operand_aux2_IMP_Minus_correct_time:
  "(invoke_subprogram p copy_var_to_operand_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = copy_var_to_operand_aux2_imp_time 0 (copy_var_to_operand_aux2_imp_to_HOL_state p s)"
  apply (simp only: copy_var_to_operand_aux2_imp_time.simps copy_var_to_operand_aux2_imp_state_upd_time_def)
  apply (simp only: copy_var_to_operand_aux2_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule prod_encode_IMP_Minus_correct[where vars=copy_var_to_operand_aux2_IMP_vars])
  subgoal premises p using p(39) by fastforce
  apply (erule operand_bit_to_var_tail_IMP_Minus_correct[where vars=copy_var_to_operand_aux2_IMP_vars])
  subgoal premises p using p(41) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux2_IMP_vars])
  subgoal premises p using p(43) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux2_IMP_vars])
  subgoal premises p using p(45) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars="copy_var_to_operand_aux2_IMP_vars 
    \<union> {operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str}"])
  subgoal premises p using p(47) by fastforce
  apply (force simp: copy_var_to_operand_aux2_state_translators Let_def) 
  done 

lemma copy_var_to_operand_aux2_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_var_to_operand_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
     \<lbrakk>t = (copy_var_to_operand_aux2_imp_time 0 (copy_var_to_operand_aux2_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) copy_var_to_operand_aux2_ret_str) =
        copy_var_to_operand_aux2_ret
          (copy_var_to_operand_aux2_imp (copy_var_to_operand_aux2_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_var_to_operand_aux2_IMP_Minus_correct_function 
      copy_var_to_operand_aux2_IMP_Minus_correct_time
       set_mono_prefix
  by (smt (verit, ccfv_SIG) com_add_prefix_valid_subset com_only_vars)

subsubsection copy_var_to_operand_aux3

record copy_var_to_operand_aux3_state=
copy_var_to_operand_aux3_op::nat
copy_var_to_operand_aux3_diff::nat
copy_var_to_operand_aux3_ret::nat

abbreviation "copy_var_to_operand_aux3_prefix \<equiv> ''copy_var_to_operand_aux3_op.''"
abbreviation "copy_var_to_operand_aux3_op_str \<equiv> ''op''"
abbreviation "copy_var_to_operand_aux3_diff_str \<equiv> ''diff''"
abbreviation "copy_var_to_operand_aux3_ret_str \<equiv> ''ret''"

definition "copy_var_to_operand_aux3_imp_state_upd s \<equiv> 
 (let
   prod_encode_a' = copy_var_to_operand_aux3_op s;
   prod_encode_b' = copy_var_to_operand_aux3_diff s;
   prod_encode_ret' = 0;
   prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                       prod_encode_b = prod_encode_b',
                       prod_encode_ret = prod_encode_ret'\<rparr>;
   prod_encode_ret_state = prod_encode_imp prod_encode_state;
   operand_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
   operand_bit_to_var_tail_ret' = 0;
   operand_bit_to_var_tail_state = \<lparr>operand_bit_to_var_tail_n = operand_bit_to_var_tail_n',
                               operand_bit_to_var_tail_ret = operand_bit_to_var_tail_ret'\<rparr>;
   operand_bit_to_var_tail_ret_state = operand_bit_to_var_tail_imp operand_bit_to_var_tail_state;

   cons_h' = 0;
   cons_t' = 0;
   cons_ret' = 0;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;

   cons_h' = operand_bit_to_var_tail_ret operand_bit_to_var_tail_ret_state;
   cons_t' = cons_ret cons_ret_state;
   cons_ret' = 0;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;

   cons_h' = 1;
   cons_t' = cons_ret cons_ret_state;
   cons_ret' = 0;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;

   copy_var_to_operand_aux3_ret' = cons_ret cons_ret_state;
   ret = \<lparr>copy_var_to_operand_aux3_op = copy_var_to_operand_aux3_op s,
         copy_var_to_operand_aux3_diff = copy_var_to_operand_aux3_diff s,
         copy_var_to_operand_aux3_ret = copy_var_to_operand_aux3_ret'\<rparr>
  in
   ret)"

function copy_var_to_operand_aux3_imp 
 :: "copy_var_to_operand_aux3_state \<Rightarrow> copy_var_to_operand_aux3_state" where 
"copy_var_to_operand_aux3_imp s = 
  (let
     ret = copy_var_to_operand_aux3_imp_state_upd s
   in
    ret)" by simp+
termination 
  by (relation "measure copy_var_to_operand_aux3_op", simp)

declare copy_var_to_operand_aux3_imp.simps[simp del]

lemma copy_var_to_operand_aux3_imp_correct[let_function_correctness]:
  "copy_var_to_operand_aux3_ret (copy_var_to_operand_aux3_imp s)
    = (1 ## (operand_bit_to_var_tail (prod_encode (
        (copy_var_to_operand_aux3_op s), (copy_var_to_operand_aux3_diff s)))) ## 0 ## 0)"
apply (subst copy_var_to_operand_aux3_imp.simps copy_var_to_operand_aux3_imp_state_upd_def)+
apply (auto simp add: Let_def operand_bit_to_var_tail_imp_correct 
  cons_imp_correct prod_encode_imp_correct)
done 

definition "copy_var_to_operand_aux3_imp_state_upd_time t s \<equiv> 
 (let
   prod_encode_a' = copy_var_to_operand_aux3_op s;
   t = t + 2;
   prod_encode_b' = copy_var_to_operand_aux3_diff s;
   t = t + 2;
   prod_encode_ret' = 0;
   t = t + 2;
   prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                       prod_encode_b = prod_encode_b',
                       prod_encode_ret = prod_encode_ret'\<rparr>;
   prod_encode_ret_state = prod_encode_imp prod_encode_state;
   t = t + prod_encode_imp_time 0 prod_encode_state;

   operand_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
   t = t + 2;
   operand_bit_to_var_tail_ret' = 0;
   t = t + 2;
   operand_bit_to_var_tail_state = \<lparr>operand_bit_to_var_tail_n = operand_bit_to_var_tail_n',
                               operand_bit_to_var_tail_ret = operand_bit_to_var_tail_ret'\<rparr>;
   operand_bit_to_var_tail_ret_state = operand_bit_to_var_tail_imp operand_bit_to_var_tail_state;
   t = t + operand_bit_to_var_tail_imp_time 0 operand_bit_to_var_tail_state;

   cons_h' = 0;
   t = t + 2;
   cons_t' = 0;
   t = t + 2;
   cons_ret' = 0;
   t = t + 2;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

   cons_h' = operand_bit_to_var_tail_ret operand_bit_to_var_tail_ret_state;
   t = t + 2;
   cons_t' = cons_ret cons_ret_state;
   t = t + 2;
   cons_ret' = 0;
   t = t + 2;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

   cons_h' = 1;
   t = t + 2;
   cons_t' = cons_ret cons_ret_state;
   t = t + 2;
   cons_ret' = 0;
   t = t + 2;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

   copy_var_to_operand_aux3_ret' = cons_ret cons_ret_state;
   t = t + 2;
   ret = \<lparr>copy_var_to_operand_aux3_op = copy_var_to_operand_aux3_op s,
         copy_var_to_operand_aux3_diff = copy_var_to_operand_aux3_diff s,
         copy_var_to_operand_aux3_ret = copy_var_to_operand_aux3_ret'\<rparr>
  in
   t)"

function copy_var_to_operand_aux3_imp_time 
 :: "nat \<Rightarrow> copy_var_to_operand_aux3_state \<Rightarrow> nat" where 
"copy_var_to_operand_aux3_imp_time t s = 
  (let
     ret = copy_var_to_operand_aux3_imp_state_upd s;
     t = t + copy_var_to_operand_aux3_imp_state_upd_time 0 s
   in
    t)" by auto
termination 
  by (relation "measure (copy_var_to_operand_aux3_op \<circ> snd)", simp)

definition "copy_var_to_operand_aux3_IMP_Minus \<equiv> 
  (prod_encode_prefix @ prod_encode_a_str) ::= A (V copy_var_to_operand_aux3_op_str);;
  (prod_encode_prefix @ prod_encode_b_str) ::= A (V copy_var_to_operand_aux3_diff_str);;
  (prod_encode_prefix @ prod_encode_ret_str) ::= A (N 0);;
  invoke_subprogram prod_encode_prefix prod_encode_IMP_Minus;;
  
  (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_n_str) ::= A (V (prod_encode_prefix @ prod_encode_ret_str));;
  (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str) ::= A (N 0);;
  invoke_subprogram operand_bit_to_var_tail_prefix operand_bit_to_var_tail_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (N 0);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (N 1);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  copy_var_to_operand_aux3_ret_str ::= A (V (cons_prefix @ cons_ret_str))"

abbreviation "copy_var_to_operand_aux3_IMP_vars \<equiv> 
  {copy_var_to_operand_aux3_op_str, copy_var_to_operand_aux3_diff_str, copy_var_to_operand_aux3_ret_str}"

definition "copy_var_to_operand_aux3_imp_to_HOL_state p s \<equiv> 
  \<lparr>copy_var_to_operand_aux3_op = s (add_prefix p copy_var_to_operand_aux3_op_str),
  copy_var_to_operand_aux3_diff = s (add_prefix p copy_var_to_operand_aux3_diff_str),
  copy_var_to_operand_aux3_ret = s (add_prefix p copy_var_to_operand_aux3_ret_str)\<rparr>"

lemmas copy_var_to_operand_aux3_state_translators =
  copy_var_to_operand_aux3_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  operand_bit_to_var_tail_imp_to_HOL_state_def 
  prod_encode_imp_to_HOL_state_def

lemma copy_var_to_operand_aux3_IMP_Minus_correct_function:
  "(invoke_subprogram p copy_var_to_operand_aux3_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_var_to_operand_aux3_ret_str)
      = copy_var_to_operand_aux3_ret (copy_var_to_operand_aux3_imp (copy_var_to_operand_aux3_imp_to_HOL_state p s))"
  apply (simp only: copy_var_to_operand_aux3_imp.simps copy_var_to_operand_aux3_imp_state_upd_def)
  apply (simp only: copy_var_to_operand_aux3_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule prod_encode_IMP_Minus_correct[where vars=copy_var_to_operand_aux3_IMP_vars])
  subgoal premises p using p(20) by fastforce
  apply (erule operand_bit_to_var_tail_IMP_Minus_correct[where vars=copy_var_to_operand_aux3_IMP_vars])
  subgoal premises p using p(22) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux3_IMP_vars])
  subgoal premises p using p(24) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux3_IMP_vars])
  subgoal premises p using p(26) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars="copy_var_to_operand_aux3_IMP_vars 
    \<union> {operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str}"])
  subgoal premises p using p(28) by fastforce
  apply (force simp: copy_var_to_operand_aux3_state_translators Let_def) 
  done 

lemma copy_var_to_operand_aux3_IMP_Minus_correct_time:
  "(invoke_subprogram p copy_var_to_operand_aux3_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = copy_var_to_operand_aux3_imp_time 0 (copy_var_to_operand_aux3_imp_to_HOL_state p s)"
  apply (simp only: copy_var_to_operand_aux3_imp_time.simps copy_var_to_operand_aux3_imp_state_upd_time_def)
  apply (simp only: copy_var_to_operand_aux3_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule prod_encode_IMP_Minus_correct[where vars=copy_var_to_operand_aux3_IMP_vars])
  subgoal premises p using p(39) by fastforce
  apply (erule operand_bit_to_var_tail_IMP_Minus_correct[where vars=copy_var_to_operand_aux3_IMP_vars])
  subgoal premises p using p(41) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux3_IMP_vars])
  subgoal premises p using p(43) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux3_IMP_vars])
  subgoal premises p using p(45) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars="copy_var_to_operand_aux3_IMP_vars 
    \<union> {operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str}"])
  subgoal premises p using p(47) by fastforce
  apply (force simp: copy_var_to_operand_aux3_state_translators Let_def) 
  done 

lemma copy_var_to_operand_aux3_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_var_to_operand_aux3_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
     \<lbrakk>t = (copy_var_to_operand_aux3_imp_time 0 (copy_var_to_operand_aux3_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) copy_var_to_operand_aux3_ret_str) =
        copy_var_to_operand_aux3_ret
          (copy_var_to_operand_aux3_imp (copy_var_to_operand_aux3_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_var_to_operand_aux3_IMP_Minus_correct_function 
      copy_var_to_operand_aux3_IMP_Minus_correct_time
       set_mono_prefix
  by (smt (verit, ccfv_SIG) com_add_prefix_valid_subset com_only_vars)

subsubsection copy_var_to_operand_aux4

record copy_var_to_operand_aux4_state=
  copy_var_to_operand_aux4_diff::nat
  copy_var_to_operand_aux4_i::nat
  copy_var_to_operand_aux4_op::nat
  copy_var_to_operand_aux4_v::nat 
  copy_var_to_operand_aux4_ret::nat

abbreviation "copy_var_to_operand_aux4_prefix \<equiv> ''copy_var_to_operand_aux4_prefix.''"
abbreviation "copy_var_to_operand_aux4_diff_str \<equiv> ''diff''"
abbreviation "copy_var_to_operand_aux4_i_str \<equiv> ''i''"
abbreviation "copy_var_to_operand_aux4_op_str \<equiv> ''op''"
abbreviation "copy_var_to_operand_aux4_v_str \<equiv> ''v''"
abbreviation "copy_var_to_operand_aux4_ret_str \<equiv> ''ret''"

definition "copy_var_to_operand_aux4_state_upd s \<equiv> 
 (let
   copy_var_to_operand_aux3_op' = copy_var_to_operand_aux4_op s;
   copy_var_to_operand_aux3_diff' = copy_var_to_operand_aux4_i s - copy_var_to_operand_aux4_diff s;
   copy_var_to_operand_aux3_ret' = 0;
   copy_var_to_operand_aux3_state = \<lparr>copy_var_to_operand_aux3_op = copy_var_to_operand_aux3_op',
                                    copy_var_to_operand_aux3_diff = copy_var_to_operand_aux3_diff',
                                    copy_var_to_operand_aux3_ret = copy_var_to_operand_aux3_ret'\<rparr>;
   copy_var_to_operand_aux3_ret_state = copy_var_to_operand_aux3_imp copy_var_to_operand_aux3_state;

   cons_h' = copy_var_to_operand_aux3_ret copy_var_to_operand_aux3_ret_state;
   cons_t' = 0;
   cons_ret' = 0;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;

   copy_var_to_operand_aux2_op' = copy_var_to_operand_aux4_op s;
   copy_var_to_operand_aux2_diff' = copy_var_to_operand_aux4_i s - copy_var_to_operand_aux4_diff s;
   copy_var_to_operand_aux2_ret' = 0;
   copy_var_to_operand_aux2_state = \<lparr>copy_var_to_operand_aux2_op = copy_var_to_operand_aux2_op',
                                    copy_var_to_operand_aux2_diff = copy_var_to_operand_aux2_diff',
                                    copy_var_to_operand_aux2_ret = copy_var_to_operand_aux2_ret'\<rparr>;
   copy_var_to_operand_aux2_ret_state = copy_var_to_operand_aux2_imp copy_var_to_operand_aux2_state;

   cons_h' = copy_var_to_operand_aux2_ret copy_var_to_operand_aux2_ret_state;
   cons_t' = cons_ret cons_ret_state;
   cons_ret' = 0;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;

   copy_var_to_operand_aux1_op' = copy_var_to_operand_aux4_v s;
   copy_var_to_operand_aux1_diff' = copy_var_to_operand_aux4_i s - copy_var_to_operand_aux4_diff s;
   copy_var_to_operand_aux1_ret' = 0;
   copy_var_to_operand_aux1_state = \<lparr>copy_var_to_operand_aux1_op = copy_var_to_operand_aux1_op',
                                    copy_var_to_operand_aux1_diff = copy_var_to_operand_aux1_diff',
                                    copy_var_to_operand_aux1_ret = copy_var_to_operand_aux1_ret'\<rparr>;
  copy_var_to_operand_aux1_ret_state = copy_var_to_operand_aux1_imp copy_var_to_operand_aux1_state;

 cons_h' = copy_var_to_operand_aux1_ret copy_var_to_operand_aux1_ret_state;
 cons_t' = cons_ret cons_ret_state; 
 cons_ret' = 0;
 cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
 cons_ret_state = cons_imp cons_state;

 cons_h' = 3;
 cons_t' = cons_ret cons_ret_state; 
 cons_ret' = 0;
 cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
 cons_ret_state = cons_imp cons_state;

 copy_var_to_operand_aux4_ret' = cons_ret cons_ret_state;
 ret = \<lparr>copy_var_to_operand_aux4_diff = copy_var_to_operand_aux4_diff s,
       copy_var_to_operand_aux4_i = copy_var_to_operand_aux4_i s,
       copy_var_to_operand_aux4_op = copy_var_to_operand_aux4_op s,
       copy_var_to_operand_aux4_v = copy_var_to_operand_aux4_v s,
       copy_var_to_operand_aux4_ret = copy_var_to_operand_aux4_ret'\<rparr>
 in
  ret)"

function copy_var_to_operand_aux4_imp 
  :: "copy_var_to_operand_aux4_state \<Rightarrow> copy_var_to_operand_aux4_state" where
"copy_var_to_operand_aux4_imp s = 
  (let
    ret = copy_var_to_operand_aux4_state_upd s
   in
    ret)" by simp+
termination 
 by (relation "measure copy_var_to_operand_aux4_diff", simp)

declare copy_var_to_operand_aux4_imp.simps[simp del]

lemma copy_var_to_operand_aux4_imp_correct:
  "copy_var_to_operand_aux4_ret (copy_var_to_operand_aux4_imp s) = 
    (3 ## ((var_bit_to_var_tail (prod_encode ((copy_var_to_operand_aux4_v s), 
      (copy_var_to_operand_aux4_i s) - (copy_var_to_operand_aux4_diff s)))) ## 0)
    ## (1 ## (operand_bit_to_var_tail (prod_encode ((copy_var_to_operand_aux4_op s), 
       (copy_var_to_operand_aux4_i s) - (copy_var_to_operand_aux4_diff s)))) ## 1 ## 0)
    ## (1 ## (operand_bit_to_var_tail (prod_encode ((copy_var_to_operand_aux4_op s), 
      (copy_var_to_operand_aux4_i s) - (copy_var_to_operand_aux4_diff s)))) ## 0 ## 0)
    ## 0)"
  apply (simp only: copy_var_to_operand_aux4_imp.simps copy_var_to_operand_aux4_state_upd_def)
  apply (auto simp add: cons_imp_correct Let_def 
    copy_var_to_operand_aux1_imp_correct copy_var_to_operand_aux3_imp_correct
    copy_var_to_operand_aux2_imp_correct)
  done 

definition "copy_var_to_operand_aux4_state_upd_time t s \<equiv> 
 (let
   copy_var_to_operand_aux3_op' = copy_var_to_operand_aux4_op s;
   t = t + 2;
   copy_var_to_operand_aux3_diff' = copy_var_to_operand_aux4_i s - copy_var_to_operand_aux4_diff s;
   t = t + 2;
   copy_var_to_operand_aux3_ret' = 0;
   t = t + 2;
   copy_var_to_operand_aux3_state = \<lparr>copy_var_to_operand_aux3_op = copy_var_to_operand_aux3_op',
                                    copy_var_to_operand_aux3_diff = copy_var_to_operand_aux3_diff',
                                    copy_var_to_operand_aux3_ret = copy_var_to_operand_aux3_ret'\<rparr>;
   copy_var_to_operand_aux3_ret_state = copy_var_to_operand_aux3_imp copy_var_to_operand_aux3_state;
   t = t + copy_var_to_operand_aux3_imp_time 0 copy_var_to_operand_aux3_state;

   cons_h' = copy_var_to_operand_aux3_ret copy_var_to_operand_aux3_ret_state;
   t = t + 2;
   cons_t' = 0;
   t = t + 2;
   cons_ret' = 0;
   t = t + 2;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

   copy_var_to_operand_aux2_op' = copy_var_to_operand_aux4_op s;
   t = t + 2;
   copy_var_to_operand_aux2_diff' = copy_var_to_operand_aux4_i s - copy_var_to_operand_aux4_diff s;
   t = t + 2;
   copy_var_to_operand_aux2_ret' = 0;
   t = t + 2;
   copy_var_to_operand_aux2_state = \<lparr>copy_var_to_operand_aux2_op = copy_var_to_operand_aux2_op',
                                    copy_var_to_operand_aux2_diff = copy_var_to_operand_aux2_diff',
                                    copy_var_to_operand_aux2_ret = copy_var_to_operand_aux2_ret'\<rparr>;
   copy_var_to_operand_aux2_ret_state = copy_var_to_operand_aux2_imp copy_var_to_operand_aux2_state;
   t = t + copy_var_to_operand_aux2_imp_time 0 copy_var_to_operand_aux2_state;

   cons_h' = copy_var_to_operand_aux2_ret copy_var_to_operand_aux2_ret_state;
   t = t + 2;
   cons_t' = cons_ret cons_ret_state;
   t = t + 2;
   cons_ret' = 0;
   t = t + 2;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

   copy_var_to_operand_aux1_op' = copy_var_to_operand_aux4_v s;
   t = t + 2;
   copy_var_to_operand_aux1_diff' = copy_var_to_operand_aux4_i s - copy_var_to_operand_aux4_diff s;
   t = t + 2;
   copy_var_to_operand_aux1_ret' = 0;
   t = t + 2;
   copy_var_to_operand_aux1_state = \<lparr>copy_var_to_operand_aux1_op = copy_var_to_operand_aux1_op',
                                    copy_var_to_operand_aux1_diff = copy_var_to_operand_aux1_diff',
                                    copy_var_to_operand_aux1_ret = copy_var_to_operand_aux1_ret'\<rparr>;
  copy_var_to_operand_aux1_ret_state = copy_var_to_operand_aux1_imp copy_var_to_operand_aux1_state;
   t = t + copy_var_to_operand_aux1_imp_time 0 copy_var_to_operand_aux1_state;

 cons_h' = copy_var_to_operand_aux1_ret copy_var_to_operand_aux1_ret_state;
   t = t + 2;
 cons_t' = cons_ret cons_ret_state; 
   t = t + 2;
 cons_ret' = 0;
   t = t + 2;
 cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
 cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

 cons_h' = 3;
   t = t + 2;
 cons_t' = cons_ret cons_ret_state; 
   t = t + 2;
 cons_ret' = 0;
   t = t + 2;
 cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
 cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

 copy_var_to_operand_aux4_ret' = cons_ret cons_ret_state;
   t = t + 2;
 ret = \<lparr>copy_var_to_operand_aux4_diff = copy_var_to_operand_aux4_diff s,
       copy_var_to_operand_aux4_i = copy_var_to_operand_aux4_i s,
       copy_var_to_operand_aux4_op = copy_var_to_operand_aux4_op s,
       copy_var_to_operand_aux4_v = copy_var_to_operand_aux4_v s,
       copy_var_to_operand_aux4_ret = copy_var_to_operand_aux4_ret'\<rparr>
 in
  t)"


function copy_var_to_operand_aux4_imp_time 
  :: "nat \<Rightarrow> copy_var_to_operand_aux4_state \<Rightarrow> nat" where
"copy_var_to_operand_aux4_imp_time t s = 
  (let
    ret = copy_var_to_operand_aux4_state_upd s;
    t = t + copy_var_to_operand_aux4_state_upd_time 0 s
   in
    t)" by auto
termination 
 by (relation "measure (copy_var_to_operand_aux4_diff \<circ> snd)", simp)

declare copy_var_to_operand_aux4_imp_time.simps[simp del]

definition "copy_var_to_operand_aux4_IMP_Minus \<equiv> 
  (copy_var_to_operand_aux3_prefix @ copy_var_to_operand_aux3_op_str)
    ::= A (V copy_var_to_operand_aux4_op_str);;
  (copy_var_to_operand_aux3_prefix @ copy_var_to_operand_aux3_diff_str)
    ::= Sub (V copy_var_to_operand_aux4_i_str) ((V copy_var_to_operand_aux4_diff_str));;
  (copy_var_to_operand_aux3_prefix @ copy_var_to_operand_aux3_ret_str)
    ::= A (N 0);;
  invoke_subprogram copy_var_to_operand_aux3_prefix copy_var_to_operand_aux3_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (copy_var_to_operand_aux3_prefix @ copy_var_to_operand_aux3_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (copy_var_to_operand_aux2_prefix @ copy_var_to_operand_aux2_op_str)
    ::= A (V copy_var_to_operand_aux4_op_str);;
  (copy_var_to_operand_aux2_prefix @ copy_var_to_operand_aux2_diff_str)
    ::= Sub (V copy_var_to_operand_aux4_i_str) ((V copy_var_to_operand_aux4_diff_str));;
  (copy_var_to_operand_aux2_prefix @ copy_var_to_operand_aux2_ret_str)
    ::= A (N 0);;
  invoke_subprogram copy_var_to_operand_aux2_prefix copy_var_to_operand_aux2_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (copy_var_to_operand_aux2_prefix @ copy_var_to_operand_aux2_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (copy_var_to_operand_aux1_prefix @ copy_var_to_operand_aux1_op_str)
    ::= A (V copy_var_to_operand_aux4_v_str);;
  (copy_var_to_operand_aux1_prefix @ copy_var_to_operand_aux1_diff_str)
    ::= Sub (V copy_var_to_operand_aux4_i_str) ((V copy_var_to_operand_aux4_diff_str));;
  (copy_var_to_operand_aux1_prefix @ copy_var_to_operand_aux1_ret_str)
    ::= A (N 0);;
  invoke_subprogram copy_var_to_operand_aux1_prefix copy_var_to_operand_aux1_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (copy_var_to_operand_aux1_prefix @ copy_var_to_operand_aux1_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (N 3);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  copy_var_to_operand_aux4_ret_str ::= A (V (cons_prefix @ cons_ret_str))"

abbreviation "copy_var_to_operand_aux4_IMP_vars \<equiv> 
 {copy_var_to_operand_aux4_diff_str, copy_var_to_operand_aux4_i_str,
 copy_var_to_operand_aux4_op_str, copy_var_to_operand_aux4_v_str}"

definition "copy_var_to_operand_aux4_imp_to_HOL_state p s = 
  \<lparr>copy_var_to_operand_aux4_diff = s (add_prefix p copy_var_to_operand_aux4_diff_str),
  copy_var_to_operand_aux4_i = s (add_prefix p copy_var_to_operand_aux4_i_str),
  copy_var_to_operand_aux4_op = s (add_prefix p copy_var_to_operand_aux4_op_str),
  copy_var_to_operand_aux4_v = s (add_prefix p copy_var_to_operand_aux4_v_str),
  copy_var_to_operand_aux4_ret = s (add_prefix p copy_var_to_operand_aux4_ret_str)\<rparr>"

lemmas copy_var_to_operand_aux4_state_translators = 
  copy_var_to_operand_aux4_imp_to_HOL_state_def
  copy_var_to_operand_aux3_imp_to_HOL_state_def
  copy_var_to_operand_aux2_imp_to_HOL_state_def 
  copy_var_to_operand_aux1_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
    
lemma copy_var_to_operand_aux4_IMP_Minus_correct_function:
 "(invoke_subprogram p copy_var_to_operand_aux4_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_var_to_operand_aux4_ret_str)
      = copy_var_to_operand_aux4_ret (copy_var_to_operand_aux4_imp (copy_var_to_operand_aux4_imp_to_HOL_state p s))" 
  apply (simp only: copy_var_to_operand_aux4_imp.simps copy_var_to_operand_aux4_state_upd_def)
  apply (simp only: copy_var_to_operand_aux4_IMP_Minus_def prefix_simps)  
  apply (erule Seq_E)+
  apply (erule copy_var_to_operand_aux3_IMP_Minus_correct[where vars=copy_var_to_operand_aux4_IMP_vars])
  subgoal premises p using p(29) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux4_IMP_vars])
  subgoal premises p using p(31) by fastforce
  apply (erule copy_var_to_operand_aux2_IMP_Minus_correct[where vars="copy_var_to_operand_aux4_IMP_vars \<union> {(cons_prefix @ cons_ret_str)}"])
  subgoal premises p using p(33) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux4_IMP_vars])
  subgoal premises p using p(35) by fastforce
  apply (erule copy_var_to_operand_aux1_IMP_Minus_correct[where vars="copy_var_to_operand_aux4_IMP_vars \<union> {(cons_prefix @ cons_ret_str)}"])
  subgoal premises p using p(37) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux4_IMP_vars])
  subgoal premises p using p(39) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux4_IMP_vars])
  subgoal premises p using p(41) by fastforce
  apply (force simp: copy_var_to_operand_aux4_state_translators Let_def)
  done

lemma copy_var_to_operand_aux4_IMP_Minus_correct_time:
 "(invoke_subprogram p copy_var_to_operand_aux4_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = copy_var_to_operand_aux4_imp_time 0 (copy_var_to_operand_aux4_imp_to_HOL_state p s)" 
  apply (simp only: copy_var_to_operand_aux4_imp_time.simps copy_var_to_operand_aux4_state_upd_time_def)
  apply (simp only: copy_var_to_operand_aux4_IMP_Minus_def prefix_simps)  
  apply (erule Seq_tE)+
  apply (erule copy_var_to_operand_aux3_IMP_Minus_correct[where vars=copy_var_to_operand_aux4_IMP_vars])
  subgoal premises p using p(57) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux4_IMP_vars])
  subgoal premises p using p(59) by fastforce
  apply (erule copy_var_to_operand_aux2_IMP_Minus_correct[where vars="copy_var_to_operand_aux4_IMP_vars \<union> {(cons_prefix @ cons_ret_str)}"])
  subgoal premises p using p(61) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux4_IMP_vars])
  subgoal premises p using p(63) by fastforce
  apply (erule copy_var_to_operand_aux1_IMP_Minus_correct[where vars="copy_var_to_operand_aux4_IMP_vars \<union> {(cons_prefix @ cons_ret_str)}"])
  subgoal premises p using p(65) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux4_IMP_vars])
  subgoal premises p using p(67) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux4_IMP_vars])
  subgoal premises p using p(69) by fastforce
  apply (force simp: copy_var_to_operand_aux4_state_translators Let_def)
  done

lemma copy_var_to_operand_aux4_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_var_to_operand_aux4_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
     \<lbrakk>t = (copy_var_to_operand_aux4_imp_time 0 (copy_var_to_operand_aux4_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) copy_var_to_operand_aux4_ret_str) =
        copy_var_to_operand_aux4_ret
          (copy_var_to_operand_aux4_imp (copy_var_to_operand_aux4_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_var_to_operand_aux4_IMP_Minus_correct_function 
      copy_var_to_operand_aux4_IMP_Minus_correct_time
       set_mono_prefix
  by (smt (verit, ccfv_SIG) com_add_prefix_valid_subset com_only_vars)

subsubsection copy_var_to_operand_aux5

record copy_var_to_operand_aux5_state = 
  copy_var_to_operand_aux5_acc::nat
  copy_var_to_operand_aux5_diff::nat
  copy_var_to_operand_aux5_i::nat
  copy_var_to_operand_aux5_op::nat
  copy_var_to_operand_aux5_v::nat 
  copy_var_to_operand_aux5_ret::nat

abbreviation "copy_var_to_operand_aux5_prefix \<equiv> ''copy_var_to_operand_aux5.''"
abbreviation "copy_var_to_operand_aux5_acc_str \<equiv> ''acc''"
abbreviation "copy_var_to_operand_aux5_diff_str \<equiv> ''diff''"
abbreviation "copy_var_to_operand_aux5_i_str \<equiv> ''i''"
abbreviation "copy_var_to_operand_aux5_op_str \<equiv> ''op''"
abbreviation "copy_var_to_operand_aux5_v_str \<equiv> ''v''"
abbreviation "copy_var_to_operand_aux5_ret_str \<equiv> ''ret''"

definition "copy_var_to_operand_aux5_state_upd s \<equiv>
  (let
   cons_h' = copy_var_to_operand_aux5_acc s;
   cons_t' = 0;
   cons_ret' = 0;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;

   copy_var_to_operand_aux4_diff' = copy_var_to_operand_aux5_diff s;
   copy_var_to_operand_aux4_i' = copy_var_to_operand_aux5_i s;
   copy_var_to_operand_aux4_op' = copy_var_to_operand_aux5_op s;
   copy_var_to_operand_aux4_v' = copy_var_to_operand_aux5_v s;
   copy_var_to_operand_aux4_ret' = 0;
   copy_var_to_operand_aux4_state = 
    \<lparr>copy_var_to_operand_aux4_diff = copy_var_to_operand_aux4_diff',
    copy_var_to_operand_aux4_i = copy_var_to_operand_aux4_i',
    copy_var_to_operand_aux4_op = copy_var_to_operand_aux4_op',
    copy_var_to_operand_aux4_v = copy_var_to_operand_aux4_v',
    copy_var_to_operand_aux4_ret = copy_var_to_operand_aux4_ret'\<rparr>;
  copy_var_to_operand_aux4_ret_state = copy_var_to_operand_aux4_imp copy_var_to_operand_aux4_state;

  cons_h' = copy_var_to_operand_aux4_ret copy_var_to_operand_aux4_ret_state;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = 2;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  copy_var_to_operand_aux5_ret' = cons_ret cons_ret_state;
  ret = \<lparr>copy_var_to_operand_aux5_acc = copy_var_to_operand_aux5_acc s,
        copy_var_to_operand_aux5_diff = copy_var_to_operand_aux5_diff s,
        copy_var_to_operand_aux5_i = copy_var_to_operand_aux5_i s,
        copy_var_to_operand_aux5_op = copy_var_to_operand_aux5_op s,
        copy_var_to_operand_aux5_v = copy_var_to_operand_aux5_v s,
        copy_var_to_operand_aux5_ret = copy_var_to_operand_aux5_ret'\<rparr>
  in
   ret)"

function copy_var_to_operand_aux5_imp :: 
  "copy_var_to_operand_aux5_state \<Rightarrow> copy_var_to_operand_aux5_state" where
"copy_var_to_operand_aux5_imp s = 
  (let
   ret =copy_var_to_operand_aux5_state_upd s
  in
   ret)" by simp+
  termination 
   by (relation "measure copy_var_to_operand_aux5_diff", simp)

declare copy_var_to_operand_aux5_imp.simps[simp del]

fun copy_var_to_operand_aux5 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"copy_var_to_operand_aux5 acc diff i op v = 
  (2 ## 
      (3 ## ((var_bit_to_var_tail (prod_encode (v, i - diff))) ## 0)
          ## (1 ## (operand_bit_to_var_tail (prod_encode (op, i - diff))) ## 1 ## 0)
          ## (1 ## (operand_bit_to_var_tail (prod_encode (op, i - diff))) ## 0 ## 0)
          ## 0)
        ## acc
        ## 0)"

lemma copy_var_to_operand_aux5_imp_correct:
  "copy_var_to_operand_aux5_ret (copy_var_to_operand_aux5_imp s) = 
    copy_var_to_operand_aux5 (copy_var_to_operand_aux5_acc s) (copy_var_to_operand_aux5_diff s)
     (copy_var_to_operand_aux5_i s) (copy_var_to_operand_aux5_op s) (copy_var_to_operand_aux5_v s)"
apply (subst copy_var_to_operand_aux5_imp.simps copy_var_to_operand_aux5_state_upd_def)+
apply (auto simp add: copy_var_to_operand_aux4_imp_correct cons_imp_correct Let_def)
done 

definition "copy_var_to_operand_aux5_state_upd_time t s \<equiv>
  (let
   cons_h' = copy_var_to_operand_aux5_acc s;
   t = t + 2;
   cons_t' = 0;
   t = t + 2;
   cons_ret' = 0;
   t = t + 2;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

   copy_var_to_operand_aux4_diff' = copy_var_to_operand_aux5_diff s;
   t = t + 2;
   copy_var_to_operand_aux4_i' = copy_var_to_operand_aux5_i s;
   t = t + 2;
   copy_var_to_operand_aux4_op' = copy_var_to_operand_aux5_op s;
   t = t + 2;
   copy_var_to_operand_aux4_v' = copy_var_to_operand_aux5_v s;
   t = t + 2;
   copy_var_to_operand_aux4_ret' = 0;
   t = t + 2;
   copy_var_to_operand_aux4_state = 
    \<lparr>copy_var_to_operand_aux4_diff = copy_var_to_operand_aux4_diff',
    copy_var_to_operand_aux4_i = copy_var_to_operand_aux4_i',
    copy_var_to_operand_aux4_op = copy_var_to_operand_aux4_op',
    copy_var_to_operand_aux4_v = copy_var_to_operand_aux4_v',
    copy_var_to_operand_aux4_ret = copy_var_to_operand_aux4_ret'\<rparr>;
  copy_var_to_operand_aux4_ret_state = copy_var_to_operand_aux4_imp copy_var_to_operand_aux4_state;
   t = t + copy_var_to_operand_aux4_imp_time 0 copy_var_to_operand_aux4_state;

  cons_h' = copy_var_to_operand_aux4_ret copy_var_to_operand_aux4_ret_state;
   t = t + 2;
  cons_t' = cons_ret cons_ret_state;
   t = t + 2;
  cons_ret' = 0;
   t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

  cons_h' = 2;
   t = t + 2;
  cons_t' = cons_ret cons_ret_state;
   t = t + 2;
  cons_ret' = 0;
   t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

  copy_var_to_operand_aux5_ret' = cons_ret cons_ret_state;
   t = t + 2;
  ret = \<lparr>copy_var_to_operand_aux5_acc = copy_var_to_operand_aux5_acc s,
        copy_var_to_operand_aux5_diff = copy_var_to_operand_aux5_diff s,
        copy_var_to_operand_aux5_i = copy_var_to_operand_aux5_i s,
        copy_var_to_operand_aux5_op = copy_var_to_operand_aux5_op s,
        copy_var_to_operand_aux5_v = copy_var_to_operand_aux5_v s,
        copy_var_to_operand_aux5_ret = copy_var_to_operand_aux5_ret'\<rparr>
  in
   t)"

function copy_var_to_operand_aux5_imp_time :: 
  "nat \<Rightarrow> copy_var_to_operand_aux5_state \<Rightarrow> nat" where
"copy_var_to_operand_aux5_imp_time t s = 
  (let
   ret =copy_var_to_operand_aux5_state_upd s;
   t = t + copy_var_to_operand_aux5_state_upd_time 0 s
  in
   t)" by auto
  termination 
   by (relation "measure (copy_var_to_operand_aux5_diff \<circ> snd)", simp)

declare copy_var_to_operand_aux5_imp_time.simps[simp del]

definition "copy_var_to_operand_aux5_IMP_Minus \<equiv>
  (cons_prefix @ cons_h_str) ::= A (V copy_var_to_operand_aux5_acc_str);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (copy_var_to_operand_aux4_prefix @ copy_var_to_operand_aux4_diff_str) 
    ::= A (V (copy_var_to_operand_aux5_diff_str));;
  (copy_var_to_operand_aux4_prefix @ copy_var_to_operand_aux4_i_str) 
    ::= A (V copy_var_to_operand_aux5_i_str);;
  (copy_var_to_operand_aux4_prefix @ copy_var_to_operand_aux4_op_str) 
    ::= A (V copy_var_to_operand_aux5_op_str);;
  (copy_var_to_operand_aux4_prefix @ copy_var_to_operand_aux4_v_str) 
    ::= A (V copy_var_to_operand_aux5_v_str);;
  (copy_var_to_operand_aux4_prefix @ copy_var_to_operand_aux4_ret_str) 
    ::= A (N 0);;
  invoke_subprogram copy_var_to_operand_aux4_prefix copy_var_to_operand_aux4_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (copy_var_to_operand_aux4_prefix @ copy_var_to_operand_aux4_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (N 2);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  copy_var_to_operand_aux5_ret_str ::= A (V (cons_prefix @ cons_ret_str))
"

abbreviation "copy_var_to_operand_aux5_IMP_vars\<equiv>
  {copy_var_to_operand_aux5_acc_str, copy_var_to_operand_aux5_diff_str,
  copy_var_to_operand_aux5_i_str, copy_var_to_operand_aux5_op_str,
  copy_var_to_operand_aux5_v_str, copy_var_to_operand_aux5_ret_str}"


definition "copy_var_to_operand_aux5_imp_to_HOL_state p s =
  \<lparr>copy_var_to_operand_aux5_acc = (s (add_prefix p copy_var_to_operand_aux5_acc_str)),
  copy_var_to_operand_aux5_diff = (s (add_prefix p copy_var_to_operand_aux5_diff_str)),
  copy_var_to_operand_aux5_i = (s (add_prefix p copy_var_to_operand_aux5_i_str)),
  copy_var_to_operand_aux5_op = (s (add_prefix p copy_var_to_operand_aux5_op_str)),
  copy_var_to_operand_aux5_v = (s (add_prefix p copy_var_to_operand_aux5_v_str)),
  copy_var_to_operand_aux5_ret = (s (add_prefix p copy_var_to_operand_aux5_ret_str))\<rparr>"

lemmas copy_var_to_operand_aux5_state_translators =
  copy_var_to_operand_aux5_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  copy_var_to_operand_aux4_imp_to_HOL_state_def

lemma copy_var_to_operand_aux5_IMP_Minus_correct_function:
  "(invoke_subprogram p copy_var_to_operand_aux5_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_var_to_operand_aux5_ret_str)
      = copy_var_to_operand_aux5_ret
          (copy_var_to_operand_aux5_imp (copy_var_to_operand_aux5_imp_to_HOL_state p s))"
  apply (simp only: copy_var_to_operand_aux5_imp.simps copy_var_to_operand_aux5_state_upd_def)
  apply (simp only: copy_var_to_operand_aux5_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux5_IMP_vars])
  subgoal premises p using p(19) by fastforce
  apply (erule copy_var_to_operand_aux4_IMP_Minus_correct[where 
         vars="copy_var_to_operand_aux5_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
  subgoal premises p using p(21) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux5_IMP_vars])
  subgoal premises p using p(23) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux5_IMP_vars])
  subgoal premises p using p(25) by fastforce
  apply (force simp: Let_def copy_var_to_operand_aux5_state_translators)
  done 

lemma copy_var_to_operand_aux5_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ copy_var_to_operand_aux5_pref) copy_var_to_operand_aux5_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix copy_var_to_operand_aux5_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemma copy_var_to_operand_aux5_IMP_Minus_correct_time:
  "(invoke_subprogram p copy_var_to_operand_aux5_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = copy_var_to_operand_aux5_imp_time 0 (copy_var_to_operand_aux5_imp_to_HOL_state p s)"
  apply (simp only: copy_var_to_operand_aux5_imp_time.simps copy_var_to_operand_aux5_state_upd_time_def)
  apply (simp only: copy_var_to_operand_aux5_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux5_IMP_vars])
  subgoal premises p using p(37) by fastforce
  apply (erule copy_var_to_operand_aux4_IMP_Minus_correct[where 
         vars="copy_var_to_operand_aux5_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
  subgoal premises p using p(39) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux5_IMP_vars])
  subgoal premises p using p(41) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux5_IMP_vars])
  subgoal premises p using p(43) by fastforce
  apply (force simp: Let_def copy_var_to_operand_aux5_state_translators)
  done 

lemma copy_var_to_operand_aux5_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_var_to_operand_aux5_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (copy_var_to_operand_aux5_imp_time 0 (copy_var_to_operand_aux5_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) copy_var_to_operand_aux5_ret_str) =
          copy_var_to_operand_aux5_ret (copy_var_to_operand_aux5_imp
                                        (copy_var_to_operand_aux5_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_var_to_operand_aux5_IMP_Minus_correct_function
  by (auto simp: copy_var_to_operand_aux5_IMP_Minus_correct_time)
    (meson copy_var_to_operand_aux5_IMP_Minus_correct_effects set_mono_prefix)

subsubsection copy_var_to_operand_acc

record copy_var_to_operand_acc_state =
  copy_var_to_operand_acc_acc::nat
  copy_var_to_operand_acc_diff::nat
  copy_var_to_operand_acc_i::nat
  copy_var_to_operand_acc_op::nat
  copy_var_to_operand_acc_v::nat 
  copy_var_to_operand_acc_ret::nat

abbreviation "copy_var_to_operand_acc_prefix \<equiv> ''copy_var_to_operand_acc.''"
abbreviation "copy_var_to_operand_acc_acc_str \<equiv> ''acc''"
abbreviation "copy_var_to_operand_acc_diff_str \<equiv> ''diff''"
abbreviation "copy_var_to_operand_acc_i_str \<equiv> ''i''"
abbreviation "copy_var_to_operand_acc_op_str \<equiv> ''op''"
abbreviation "copy_var_to_operand_acc_v_str \<equiv> ''v''"
abbreviation "copy_var_to_operand_acc_ret_str \<equiv> ''ret''"

definition "copy_var_to_operand_acc_state_upd s \<equiv>
  (let 
   copy_var_to_operand_aux5_acc' = copy_var_to_operand_acc_acc s;
   copy_var_to_operand_aux5_diff' = copy_var_to_operand_acc_diff s;
   copy_var_to_operand_aux5_i' = copy_var_to_operand_acc_i s;
   copy_var_to_operand_aux5_op' = copy_var_to_operand_acc_op s;
   copy_var_to_operand_aux5_v' = copy_var_to_operand_acc_v s;
   copy_var_to_operand_aux5_ret' = 0;
   copy_var_to_operand_aux5_state = 
    \<lparr>copy_var_to_operand_aux5_acc = copy_var_to_operand_aux5_acc',
    copy_var_to_operand_aux5_diff = copy_var_to_operand_aux5_diff',
    copy_var_to_operand_aux5_i = copy_var_to_operand_aux5_i',
    copy_var_to_operand_aux5_op = copy_var_to_operand_aux5_op',
    copy_var_to_operand_aux5_v = copy_var_to_operand_aux5_v',
    copy_var_to_operand_aux5_ret = copy_var_to_operand_aux5_ret'\<rparr>;
  copy_var_to_operand_aux5_ret_state = copy_var_to_operand_aux5_imp copy_var_to_operand_aux5_state;

  copy_var_to_operand_acc_acc' = copy_var_to_operand_aux5_ret copy_var_to_operand_aux5_ret_state;
  copy_var_to_operand_acc_diff' = copy_var_to_operand_acc_diff s - 1;
  ret = \<lparr>copy_var_to_operand_acc_acc = copy_var_to_operand_acc_acc',
        copy_var_to_operand_acc_diff = copy_var_to_operand_acc_diff',
        copy_var_to_operand_acc_i = copy_var_to_operand_acc_i s,
        copy_var_to_operand_acc_op = copy_var_to_operand_acc_op s,
        copy_var_to_operand_acc_v = copy_var_to_operand_acc_v s,
        copy_var_to_operand_acc_ret = copy_var_to_operand_acc_ret s\<rparr>
  in
   ret)"


definition "copy_var_to_operand_acc_imp_compute_loop_condition s \<equiv> 
 (let
  condition = copy_var_to_operand_acc_diff s
 in 
  condition)"

definition "copy_var_to_operand_acc_imp_after_loop s \<equiv> 
 (let 
  copy_var_to_operand_acc_ret' = copy_var_to_operand_acc_acc s;
  ret = \<lparr>copy_var_to_operand_acc_acc = copy_var_to_operand_acc_acc s,
        copy_var_to_operand_acc_diff = copy_var_to_operand_acc_diff s,
        copy_var_to_operand_acc_i = copy_var_to_operand_acc_i s,
        copy_var_to_operand_acc_op = copy_var_to_operand_acc_op s,
        copy_var_to_operand_acc_v = copy_var_to_operand_acc_v s,
        copy_var_to_operand_acc_ret = copy_var_to_operand_acc_ret'\<rparr>
 in
  ret)"

lemmas copy_var_to_operand_acc_imp_subprogram_simps = 
  copy_var_to_operand_acc_state_upd_def
  copy_var_to_operand_acc_imp_compute_loop_condition_def
  copy_var_to_operand_acc_imp_after_loop_def

function copy_var_to_operand_acc_imp::
  "copy_var_to_operand_acc_state \<Rightarrow> copy_var_to_operand_acc_state" where
  "copy_var_to_operand_acc_imp s =
  (if copy_var_to_operand_acc_imp_compute_loop_condition s \<noteq> 0
   then
    let next_iteration = copy_var_to_operand_acc_imp (copy_var_to_operand_acc_state_upd s)
    in next_iteration
   else
    let ret = copy_var_to_operand_acc_imp_after_loop s
    in ret
  )"
  by simp+
termination
  apply (relation "measure copy_var_to_operand_acc_diff")
  apply (simp add: copy_var_to_operand_acc_imp_subprogram_simps)+
  done

declare copy_var_to_operand_acc_imp.simps [simp del]

lemma copy_var_to_operand_acc_imp_correct:
  "copy_var_to_operand_acc_ret (copy_var_to_operand_acc_imp s) =
    copy_var_to_operand_acc (copy_var_to_operand_acc_acc s) 
    (copy_var_to_operand_acc_diff s) (copy_var_to_operand_acc_i s)
    (copy_var_to_operand_acc_op s) (copy_var_to_operand_acc_v s)"
  apply (induction s rule: copy_var_to_operand_acc_imp.induct)
  apply (subst copy_var_to_operand_acc_imp.simps)
  apply (subst copy_var_to_operand_acc.simps)
  apply (auto simp del: copy_var_to_operand_acc.simps simp add: 
  copy_var_to_operand_acc_imp_subprogram_simps Let_def
  copy_var_to_operand_aux5_imp_correct)
  done            


definition "copy_var_to_operand_acc_state_upd_time t s \<equiv>
  (let
   copy_var_to_operand_aux5_acc' = copy_var_to_operand_acc_acc s;
   t = t + 2;
   copy_var_to_operand_aux5_diff' = copy_var_to_operand_acc_diff s;
   t = t + 2;
   copy_var_to_operand_aux5_i' = copy_var_to_operand_acc_i s;
   t = t + 2;
   copy_var_to_operand_aux5_op' = copy_var_to_operand_acc_op s;
   t = t + 2;
   copy_var_to_operand_aux5_v' = copy_var_to_operand_acc_v s;
   t = t + 2;
   copy_var_to_operand_aux5_ret' = 0;
   t = t + 2;
   copy_var_to_operand_aux5_state = 
    \<lparr>copy_var_to_operand_aux5_acc = copy_var_to_operand_aux5_acc',
    copy_var_to_operand_aux5_diff = copy_var_to_operand_aux5_diff',
    copy_var_to_operand_aux5_i = copy_var_to_operand_aux5_i',
    copy_var_to_operand_aux5_op = copy_var_to_operand_aux5_op',
    copy_var_to_operand_aux5_v = copy_var_to_operand_aux5_v',
    copy_var_to_operand_aux5_ret = copy_var_to_operand_aux5_ret'\<rparr>;
  copy_var_to_operand_aux5_ret_state = copy_var_to_operand_aux5_imp copy_var_to_operand_aux5_state;
   t = t + copy_var_to_operand_aux5_imp_time 0 copy_var_to_operand_aux5_state;

  copy_var_to_operand_acc_acc' = copy_var_to_operand_aux5_ret copy_var_to_operand_aux5_ret_state;
  t = t + 2;
  copy_var_to_operand_acc_diff' = copy_var_to_operand_acc_diff s - 1;
    t = t + 2;
  ret = \<lparr>copy_var_to_operand_acc_acc = copy_var_to_operand_acc_acc',
        copy_var_to_operand_acc_diff = copy_var_to_operand_acc_diff',
        copy_var_to_operand_acc_i = copy_var_to_operand_acc_i s,
        copy_var_to_operand_acc_op = copy_var_to_operand_acc_op s,
        copy_var_to_operand_acc_v = copy_var_to_operand_acc_v s,
        copy_var_to_operand_acc_ret = copy_var_to_operand_acc_ret s\<rparr>
  in
   t)"

definition "copy_var_to_operand_acc_imp_compute_loop_condition_time t s \<equiv>
  let
  condition = copy_var_to_operand_acc_diff s;
  t = t + 2
  in
    t
"

definition "copy_var_to_operand_acc_imp_after_loop_time t s \<equiv>
  (let
    copy_var_to_operand_acc_ret' = copy_var_to_operand_acc_acc s;
    t = t + 2;
    ret = \<lparr>copy_var_to_operand_acc_acc = copy_var_to_operand_acc_acc s,
        copy_var_to_operand_acc_diff = copy_var_to_operand_acc_diff s,
        copy_var_to_operand_acc_i = copy_var_to_operand_acc_i s,
        copy_var_to_operand_acc_op = copy_var_to_operand_acc_op s,
        copy_var_to_operand_acc_v = copy_var_to_operand_acc_v s,
        copy_var_to_operand_acc_ret = copy_var_to_operand_acc_ret'\<rparr>
  in
    t)
"

lemmas copy_var_to_operand_acc_imp_subprogram_time_simps = 
  copy_var_to_operand_acc_state_upd_time_def
  copy_var_to_operand_acc_imp_compute_loop_condition_time_def
  copy_var_to_operand_acc_imp_after_loop_time_def
  copy_var_to_operand_acc_imp_subprogram_simps

function copy_var_to_operand_acc_imp_time::
  "nat \<Rightarrow> copy_var_to_operand_acc_state \<Rightarrow> nat" where
  "copy_var_to_operand_acc_imp_time t s =
  copy_var_to_operand_acc_imp_compute_loop_condition_time 0 s +
  (if copy_var_to_operand_acc_imp_compute_loop_condition s \<noteq> 0
    then
      (let
        t = t + 1;
        next_iteration =
          copy_var_to_operand_acc_imp_time (t + copy_var_to_operand_acc_state_upd_time 0 s)
                         (copy_var_to_operand_acc_state_upd s)
       in next_iteration)
    else
      (let
        t = t + 2;
        ret = t + copy_var_to_operand_acc_imp_after_loop_time 0 s
       in ret)
  )"
  by auto
termination
  apply (relation "measure (copy_var_to_operand_acc_diff \<circ> snd)")
  by (simp add: copy_var_to_operand_acc_imp_subprogram_time_simps)+

declare copy_var_to_operand_acc_imp_time.simps [simp del]            

lemma copy_var_to_operand_acc_imp_time_acc:
  "(copy_var_to_operand_acc_imp_time (Suc t) s) = Suc (copy_var_to_operand_acc_imp_time t s)"
  by (induction t s rule: copy_var_to_operand_acc_imp_time.induct)
    ((subst (1 2) copy_var_to_operand_acc_imp_time.simps);
      (simp add: copy_var_to_operand_acc_state_upd_def))            

lemma copy_var_to_operand_acc_imp_time_acc_2_aux:
  "(copy_var_to_operand_acc_imp_time t s) = t + (copy_var_to_operand_acc_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: copy_var_to_operand_acc_imp_time_acc)+            

lemma copy_var_to_operand_acc_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (copy_var_to_operand_acc_imp_time t s) = t + (copy_var_to_operand_acc_imp_time 0 s)"
  by (rule copy_var_to_operand_acc_imp_time_acc_2_aux)            

lemma copy_var_to_operand_acc_imp_time_acc_3:
  "(copy_var_to_operand_acc_imp_time (a + b) s) = a + (copy_var_to_operand_acc_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: copy_var_to_operand_acc_imp_time_acc)+            

abbreviation "copy_var_to_operand_acc_while_cond \<equiv> ''condition''"

definition "copy_var_to_operand_acc_IMP_init_while_cond \<equiv>
  copy_var_to_operand_acc_while_cond ::= A (V copy_var_to_operand_acc_diff_str)
"

definition "copy_var_to_operand_acc_IMP_loop_body \<equiv>
  (copy_var_to_operand_aux5_prefix @ copy_var_to_operand_aux5_acc_str) 
    ::= A (V (copy_var_to_operand_acc_acc_str));;
  (copy_var_to_operand_aux5_prefix @ copy_var_to_operand_aux5_diff_str) 
    ::= A (V (copy_var_to_operand_acc_diff_str));;
  (copy_var_to_operand_aux5_prefix @ copy_var_to_operand_aux5_i_str) 
    ::= A (V copy_var_to_operand_acc_i_str);;
  (copy_var_to_operand_aux5_prefix @ copy_var_to_operand_aux5_op_str) 
    ::= A (V copy_var_to_operand_acc_op_str);;
  (copy_var_to_operand_aux5_prefix @ copy_var_to_operand_aux5_v_str) 
    ::= A (V copy_var_to_operand_acc_v_str);;
  (copy_var_to_operand_aux5_prefix @ copy_var_to_operand_aux5_ret_str) 
    ::= A (N 0);;
  invoke_subprogram copy_var_to_operand_aux5_prefix copy_var_to_operand_aux5_IMP_Minus;;

  copy_var_to_operand_acc_acc_str ::= A (V (copy_var_to_operand_aux5_prefix @ copy_var_to_operand_aux5_ret_str) );;
  copy_var_to_operand_acc_diff_str ::= Sub (V copy_var_to_operand_acc_diff_str) (N 1)
"

definition "copy_var_to_operand_acc_IMP_after_loop \<equiv>
  copy_var_to_operand_acc_ret_str ::= A (V copy_var_to_operand_acc_acc_str)
"

definition copy_var_to_operand_acc_IMP_Minus where
  "copy_var_to_operand_acc_IMP_Minus \<equiv>
  copy_var_to_operand_acc_IMP_init_while_cond;;
  WHILE copy_var_to_operand_acc_while_cond \<noteq>0 DO (
    copy_var_to_operand_acc_IMP_loop_body;;
    copy_var_to_operand_acc_IMP_init_while_cond
  );;
  copy_var_to_operand_acc_IMP_after_loop"

abbreviation "copy_var_to_operand_acc_IMP_vars\<equiv>
  {copy_var_to_operand_acc_acc_str, copy_var_to_operand_acc_diff_str,
  copy_var_to_operand_acc_i_str, copy_var_to_operand_acc_op_str,
  copy_var_to_operand_acc_v_str, copy_var_to_operand_acc_ret_str,
  copy_var_to_operand_acc_while_cond}"

lemmas copy_var_to_operand_acc_IMP_subprogram_simps =
  copy_var_to_operand_acc_IMP_init_while_cond_def
  copy_var_to_operand_acc_IMP_loop_body_def
  copy_var_to_operand_acc_IMP_after_loop_def

definition "copy_var_to_operand_acc_imp_to_HOL_state p s =
  \<lparr>copy_var_to_operand_acc_acc = (s (add_prefix p copy_var_to_operand_acc_acc_str)),
  copy_var_to_operand_acc_diff = (s (add_prefix p copy_var_to_operand_acc_diff_str)),
  copy_var_to_operand_acc_i = (s (add_prefix p copy_var_to_operand_acc_i_str)),
  copy_var_to_operand_acc_op = (s (add_prefix p copy_var_to_operand_acc_op_str)),
  copy_var_to_operand_acc_v = (s (add_prefix p copy_var_to_operand_acc_v_str)),
  copy_var_to_operand_acc_ret = (s (add_prefix p copy_var_to_operand_acc_ret_str))\<rparr>"

lemmas copy_var_to_operand_acc_state_translators =
  copy_var_to_operand_acc_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  copy_var_to_operand_aux5_imp_to_HOL_state_def

lemmas copy_var_to_operand_acc_complete_simps =
  copy_var_to_operand_acc_IMP_subprogram_simps
  copy_var_to_operand_acc_imp_subprogram_simps
  copy_var_to_operand_acc_state_translators

lemma copy_var_to_operand_acc_IMP_Minus_correct_function:
  "(invoke_subprogram p copy_var_to_operand_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_var_to_operand_acc_ret_str)
      = copy_var_to_operand_acc_ret
          (copy_var_to_operand_acc_imp (copy_var_to_operand_acc_imp_to_HOL_state p s))"
  apply(induction "copy_var_to_operand_acc_imp_to_HOL_state p s" arbitrary: s s' t
    rule: copy_var_to_operand_acc_imp.induct)
  apply(subst copy_var_to_operand_acc_imp.simps)
  apply(simp only: copy_var_to_operand_acc_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule While_tE)

  subgoal
    apply(simp only: copy_var_to_operand_acc_IMP_subprogram_simps prefix_simps)
    by(fastforce simp: copy_var_to_operand_acc_IMP_subprogram_simps
        copy_var_to_operand_acc_imp_subprogram_simps
        copy_var_to_operand_acc_state_translators)

  apply(erule Seq_E)+
  apply(dest_com_gen)

  subgoal
      apply(simp only: copy_var_to_operand_acc_IMP_init_while_cond_def prefix_simps)
      by(fastforce simp add: copy_var_to_operand_acc_complete_simps)

  subgoal
      apply(subst (asm) copy_var_to_operand_acc_IMP_init_while_cond_def)
      apply(simp only: copy_var_to_operand_acc_IMP_loop_body_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule copy_var_to_operand_aux5_IMP_Minus_correct[where vars = copy_var_to_operand_acc_IMP_vars])
      subgoal premises p using p(14) by fastforce
      by (force simp: copy_var_to_operand_acc_imp_subprogram_simps
          copy_var_to_operand_acc_state_translators Let_def)

  subgoal
      apply(simp only: copy_var_to_operand_acc_IMP_init_while_cond_def prefix_simps
          copy_var_to_operand_acc_IMP_loop_body_def)
      apply(erule Seq_E)+
      apply(erule copy_var_to_operand_aux5_IMP_Minus_correct[where vars = copy_var_to_operand_acc_IMP_vars])
      subgoal premises p using p(14) by fastforce
      by (force simp: copy_var_to_operand_acc_imp_subprogram_simps
          copy_var_to_operand_acc_state_translators Let_def)
  done        

lemma copy_var_to_operand_acc_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ copy_var_to_operand_acc_pref) copy_var_to_operand_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix copy_var_to_operand_acc_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemmas copy_var_to_operand_acc_complete_time_simps =
  copy_var_to_operand_acc_imp_subprogram_time_simps
  copy_var_to_operand_acc_imp_time_acc_2
  copy_var_to_operand_acc_imp_time_acc_3
  copy_var_to_operand_acc_state_translators

lemma copy_var_to_operand_acc_IMP_Minus_correct_time:
  "(invoke_subprogram p copy_var_to_operand_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = copy_var_to_operand_acc_imp_time 0 (copy_var_to_operand_acc_imp_to_HOL_state p s)"
  apply(induction "copy_var_to_operand_acc_imp_to_HOL_state p s" arbitrary: s s' t
      rule: copy_var_to_operand_acc_imp.induct)
  apply(subst copy_var_to_operand_acc_imp_time.simps)
  apply(simp only: copy_var_to_operand_acc_IMP_Minus_def prefix_simps)

  apply(erule Seq_tE)+
  apply(erule While_tE_time)

  subgoal
    apply(simp only: copy_var_to_operand_acc_IMP_subprogram_simps prefix_simps)
    by (force simp: copy_var_to_operand_acc_IMP_subprogram_simps
        copy_var_to_operand_acc_imp_subprogram_time_simps copy_var_to_operand_acc_state_translators)

  apply(erule Seq_tE)+
  apply(simp add: add.assoc)
  apply(dest_com_gen_time)

  subgoal
    apply(simp only: copy_var_to_operand_acc_IMP_init_while_cond_def prefix_simps)
    by(fastforce simp add: copy_var_to_operand_acc_complete_simps)

  subgoal
    apply(subst (asm) copy_var_to_operand_acc_IMP_init_while_cond_def)
    apply(simp only: copy_var_to_operand_acc_IMP_loop_body_def prefix_simps)
    apply(erule Seq_tE)+
    apply(erule copy_var_to_operand_aux5_IMP_Minus_correct[where vars = copy_var_to_operand_acc_IMP_vars])
    subgoal premises p using p(25) by fastforce
    by (force simp: copy_var_to_operand_acc_imp_subprogram_simps
          copy_var_to_operand_acc_state_translators Let_def)

  subgoal
    apply(simp only: prefix_simps copy_var_to_operand_acc_IMP_init_while_cond_def
        copy_var_to_operand_acc_IMP_loop_body_def)
    apply(erule Seq_tE)+
    apply(erule copy_var_to_operand_aux5_IMP_Minus_correct[where vars = copy_var_to_operand_acc_IMP_vars])
    subgoal premises p using p(25) by fastforce
    apply (force simp: copy_var_to_operand_acc_complete_time_simps Let_def)
    done      
  done        

lemma copy_var_to_operand_acc_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_var_to_operand_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (copy_var_to_operand_acc_imp_time 0 (copy_var_to_operand_acc_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) copy_var_to_operand_acc_ret_str) =
          copy_var_to_operand_acc_ret (copy_var_to_operand_acc_imp
                                        (copy_var_to_operand_acc_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_var_to_operand_acc_IMP_Minus_correct_function
  by (auto simp: copy_var_to_operand_acc_IMP_Minus_correct_time)
    (meson copy_var_to_operand_acc_IMP_Minus_correct_effects set_mono_prefix) 

subsubsection copy_var_to_operand_tail 

record copy_var_to_operand_tail_state =
  copy_var_to_operand_tail_i::nat
  copy_var_to_operand_tail_op::nat 
  copy_var_to_operand_tail_v::nat
  copy_var_to_operand_tail_ret::nat

abbreviation "copy_var_to_operand_tail_prefix \<equiv> ''copy_var_to_operand_tail.''"
abbreviation "copy_var_to_operand_tail_i_str \<equiv> ''i''"
abbreviation "copy_var_to_operand_tail_op_str \<equiv> ''op''"
abbreviation "copy_var_to_operand_tail_v_str \<equiv> ''v''"
abbreviation "copy_var_to_operand_tail_ret_str \<equiv> ''ret''"

definition "copy_var_to_operand_tail_state_upd s \<equiv> 
(let
  cons_h' = 0;
  cons_t' = 0;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  copy_var_to_operand_acc_acc' = cons_ret cons_ret_state;
  copy_var_to_operand_acc_diff' = copy_var_to_operand_tail_i s;
  copy_var_to_operand_acc_i' = copy_var_to_operand_tail_i s;
  copy_var_to_operand_acc_op' = copy_var_to_operand_tail_op s;
  copy_var_to_operand_acc_v' = copy_var_to_operand_tail_v s;
  copy_var_to_operand_acc_ret' = 0;
  copy_var_to_operand_acc_state = 
    \<lparr>copy_var_to_operand_acc_acc = copy_var_to_operand_acc_acc',
    copy_var_to_operand_acc_diff = copy_var_to_operand_acc_diff',
    copy_var_to_operand_acc_i = copy_var_to_operand_acc_i',
    copy_var_to_operand_acc_op = copy_var_to_operand_acc_op',
    copy_var_to_operand_acc_v = copy_var_to_operand_acc_v',
    copy_var_to_operand_acc_ret = copy_var_to_operand_acc_ret'\<rparr>;
  copy_var_to_operand_acc_ret_state = copy_var_to_operand_acc_imp copy_var_to_operand_acc_state;

  copy_var_to_operand_tail_ret' = copy_var_to_operand_acc_ret copy_var_to_operand_acc_ret_state;
  ret = 
    \<lparr>copy_var_to_operand_tail_i = copy_var_to_operand_tail_i s,
    copy_var_to_operand_tail_op = copy_var_to_operand_tail_op s,
    copy_var_to_operand_tail_v = copy_var_to_operand_tail_v s,
    copy_var_to_operand_tail_ret = copy_var_to_operand_tail_ret'\<rparr>
  in 
   ret)"

function copy_var_to_operand_tail_imp 
 :: "copy_var_to_operand_tail_state \<Rightarrow> copy_var_to_operand_tail_state" where 
"copy_var_to_operand_tail_imp s = 
 (let
   ret = copy_var_to_operand_tail_state_upd s
  in
   ret)" by simp+
  termination by (relation "measure copy_var_to_operand_tail_i", simp)

declare copy_var_to_operand_tail_imp.simps[simp del]

lemma copy_var_to_operand_tail_imp_correct:
  "copy_var_to_operand_tail_ret (copy_var_to_operand_tail_imp s) =
    copy_var_to_operand_tail (copy_var_to_operand_tail_i s) 
     (copy_var_to_operand_tail_op s) (copy_var_to_operand_tail_v s)"
apply (simp only: copy_var_to_operand_tail_imp.simps copy_var_to_operand_tail_state_upd_def)
apply (simp add: copy_var_to_operand_acc_imp_correct cons_imp_correct 
      Let_def copy_var_to_operand_tail_def)
done 

definition "copy_var_to_operand_tail_state_upd_time t s \<equiv> 
(let
  cons_h' = 0;
  t = t + 2;
  cons_t' = 0;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  copy_var_to_operand_acc_acc' = cons_ret cons_ret_state;
  t = t + 2;
  t = t + 2;
  copy_var_to_operand_acc_diff' = copy_var_to_operand_tail_i s;
  copy_var_to_operand_acc_i' = copy_var_to_operand_tail_i s;
  t = t + 2;
  copy_var_to_operand_acc_op' = copy_var_to_operand_tail_op s;
  t = t + 2;
  copy_var_to_operand_acc_v' = copy_var_to_operand_tail_v s;
  t = t + 2;
  copy_var_to_operand_acc_ret' = 0;
  t = t + 2;
  copy_var_to_operand_acc_state = 
    \<lparr>copy_var_to_operand_acc_acc = copy_var_to_operand_acc_acc',
    copy_var_to_operand_acc_diff = copy_var_to_operand_acc_diff',
    copy_var_to_operand_acc_i = copy_var_to_operand_acc_i',
    copy_var_to_operand_acc_op = copy_var_to_operand_acc_op',
    copy_var_to_operand_acc_v = copy_var_to_operand_acc_v',
    copy_var_to_operand_acc_ret = copy_var_to_operand_acc_ret'\<rparr>;
  copy_var_to_operand_acc_ret_state = copy_var_to_operand_acc_imp copy_var_to_operand_acc_state;
  t = t + copy_var_to_operand_acc_imp_time 0 copy_var_to_operand_acc_state;

  copy_var_to_operand_tail_ret' = copy_var_to_operand_acc_ret copy_var_to_operand_acc_ret_state;
  t = t + 2;
  ret = 
    \<lparr>copy_var_to_operand_tail_i = copy_var_to_operand_tail_i s,
    copy_var_to_operand_tail_op = copy_var_to_operand_tail_op s,
    copy_var_to_operand_tail_v = copy_var_to_operand_tail_v s,
    copy_var_to_operand_tail_ret = copy_var_to_operand_tail_ret'\<rparr>
  in 
   t)"

function copy_var_to_operand_tail_imp_time 
 :: "nat \<Rightarrow> copy_var_to_operand_tail_state \<Rightarrow> nat" where 
"copy_var_to_operand_tail_imp_time t s = 
 (let
   ret = copy_var_to_operand_tail_state_upd s;
   t = t + copy_var_to_operand_tail_state_upd_time 0 s
  in
   t)" by auto
  termination by (relation "measure (copy_var_to_operand_tail_i \<circ> snd)", simp)

declare copy_var_to_operand_tail_imp_time.simps[simp del]

abbreviation "copy_var_to_operand_tail_IMP_vars \<equiv> 
  {copy_var_to_operand_tail_i_str, copy_var_to_operand_tail_op_str, 
  copy_var_to_operand_tail_v_str, copy_var_to_operand_tail_ret_str}"

definition "copy_var_to_operand_tail_imp_to_HOL_state p s \<equiv>
  \<lparr>copy_var_to_operand_tail_i = s (add_prefix p copy_var_to_operand_tail_i_str),
  copy_var_to_operand_tail_op = s (add_prefix p copy_var_to_operand_tail_op_str),
  copy_var_to_operand_tail_v = s (add_prefix p copy_var_to_operand_tail_v_str),
  copy_var_to_operand_tail_ret = s (add_prefix p copy_var_to_operand_tail_ret_str)\<rparr>"

definition "copy_var_to_operand_tail_IMP_Minus \<equiv> 
  (cons_prefix @ cons_h_str) ::= A (N 0);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (copy_var_to_operand_acc_prefix @ copy_var_to_operand_acc_acc_str)
    ::= A (V (cons_prefix @ cons_ret_str));;
  (copy_var_to_operand_acc_prefix @ copy_var_to_operand_acc_diff_str)
    ::= A (V copy_var_to_operand_tail_i_str);;
  (copy_var_to_operand_acc_prefix @ copy_var_to_operand_acc_i_str)
    ::= A (V copy_var_to_operand_tail_i_str);;
  (copy_var_to_operand_acc_prefix @ copy_var_to_operand_acc_op_str)
    ::= A (V copy_var_to_operand_tail_op_str);;
  (copy_var_to_operand_acc_prefix @ copy_var_to_operand_acc_v_str)
    ::= A (V copy_var_to_operand_tail_v_str);;
  (copy_var_to_operand_acc_prefix @ copy_var_to_operand_acc_ret_str)
    ::= A (N 0);;
  invoke_subprogram  copy_var_to_operand_acc_prefix  copy_var_to_operand_acc_IMP_Minus;;
  
  copy_var_to_operand_tail_ret_str 
    ::= A (V (copy_var_to_operand_acc_prefix @ copy_var_to_operand_acc_ret_str))
    
  "

lemmas copy_var_to_operand_tail_state_translators=
  copy_var_to_operand_tail_imp_to_HOL_state_def
  copy_var_to_operand_acc_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def

lemma copy_var_to_operand_tail_IMP_Minus_correct_function:
  "(invoke_subprogram p copy_var_to_operand_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_var_to_operand_tail_ret_str)
      = copy_var_to_operand_tail_ret
          (copy_var_to_operand_tail_imp (copy_var_to_operand_tail_imp_to_HOL_state p s))"
apply (simp only: copy_var_to_operand_tail_imp.simps copy_var_to_operand_tail_state_upd_def)
apply (simp only: copy_var_to_operand_tail_IMP_Minus_def prefix_simps)
apply (erule Seq_E)+
apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_tail_IMP_vars])
subgoal premises p using p(12) by fastforce
apply (erule copy_var_to_operand_acc_IMP_Minus_correct[where vars=copy_var_to_operand_tail_IMP_vars])
subgoal premises p using p(14) by fastforce
apply (force simp add: copy_var_to_operand_tail_state_translators Let_def)
done 

lemma copy_var_to_operand_tail_IMP_Minus_correct_time:
  "(invoke_subprogram p copy_var_to_operand_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (copy_var_to_operand_tail_imp_time 0 (copy_var_to_operand_tail_imp_to_HOL_state p s))"
apply (simp only: copy_var_to_operand_tail_imp_time.simps copy_var_to_operand_tail_state_upd_time_def)
apply (simp only: copy_var_to_operand_tail_IMP_Minus_def prefix_simps)
apply (erule Seq_tE)+
apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_tail_IMP_vars])
subgoal premises p using p(23) by fastforce
apply (erule copy_var_to_operand_acc_IMP_Minus_correct[where vars=copy_var_to_operand_tail_IMP_vars])
subgoal premises p using p(25) by fastforce
apply (force simp add: copy_var_to_operand_tail_state_translators Let_def)
done 

lemma copy_var_to_operand_tail_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ copy_var_to_operand_tail_pref) copy_var_to_operand_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix copy_var_to_operand_tail_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma copy_var_to_operand_tail_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_var_to_operand_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (copy_var_to_operand_tail_imp_time 0 (copy_var_to_operand_tail_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) copy_var_to_operand_tail_ret_str) =
          copy_var_to_operand_tail_ret (copy_var_to_operand_tail_imp
                                        (copy_var_to_operand_tail_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_var_to_operand_tail_IMP_Minus_correct_function
  by (auto simp: copy_var_to_operand_tail_IMP_Minus_correct_time)
    (meson copy_var_to_operand_tail_IMP_Minus_correct_effects set_mono_prefix) 

subsection copy_const_to_operand

subsubsection copy_const_to_operand_aux1

record copy_const_to_operand_aux1_state =
  copy_const_to_operand_aux1_x::nat
  copy_const_to_operand_aux1_diff::nat
  copy_const_to_operand_aux1_op::nat
  copy_const_to_operand_aux1_ret::nat

abbreviation "copy_const_to_operand_aux1_prefix \<equiv> ''copy_const_to_operand_aux1.''"
abbreviation "copy_const_to_operand_aux1_x_str \<equiv> ''x''"
abbreviation "copy_const_to_operand_aux1_diff_str \<equiv> ''diff''"
abbreviation "copy_const_to_operand_aux1_op_str \<equiv> ''op''"
abbreviation "copy_const_to_operand_aux1_ret_str \<equiv> ''ret''"

definition "copy_const_to_operand_aux1_imp s \<equiv> 
(let
  nth_bit_tail_acc' = copy_const_to_operand_aux1_x s;
  nth_bit_tail_n' = copy_const_to_operand_aux1_diff s;
  nth_bit_tail_ret' = 0;
  nth_bit_tail_state = \<lparr>nth_bit_tail_acc = nth_bit_tail_acc',
                        nth_bit_tail_n = nth_bit_tail_n',
                        nth_bit_tail_ret = nth_bit_tail_ret'\<rparr>;
  nth_bit_tail_ret_state = nth_bit_tail_imp nth_bit_tail_state;

  cons_h' = nth_bit_tail_ret nth_bit_tail_ret_state;
  cons_t' = 0;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  prod_encode_a' = copy_const_to_operand_aux1_op s;
  prod_encode_b' = copy_const_to_operand_aux1_diff s;
  prod_encode_ret' = 0;
  prod_encode_state = \<lparr>prod_encode_a = prod_encode_a', 
                       prod_encode_b = prod_encode_b',
                       prod_encode_ret = prod_encode_ret'\<rparr>;
  prod_encode_ret_state = prod_encode_imp prod_encode_state;

  operand_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
  operand_bit_to_var_tail_ret' = 0;
  operand_bit_to_var_tail_state = 
    \<lparr>operand_bit_to_var_tail_n = operand_bit_to_var_tail_n',
    operand_bit_to_var_tail_ret = operand_bit_to_var_tail_ret'\<rparr>;
  operand_bit_to_var_tail_ret_state 
    = operand_bit_to_var_tail_imp operand_bit_to_var_tail_state;

  cons_h' = operand_bit_to_var_tail_ret operand_bit_to_var_tail_ret_state;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp  cons_state;

  cons_h' = 1;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp  cons_state;

  copy_const_to_operand_aux1_ret' = cons_ret cons_ret_state;
  ret = \<lparr>copy_const_to_operand_aux1_x = copy_const_to_operand_aux1_x s,
        copy_const_to_operand_aux1_diff = copy_const_to_operand_aux1_diff s,
        copy_const_to_operand_aux1_op = copy_const_to_operand_aux1_op s,
        copy_const_to_operand_aux1_ret = copy_const_to_operand_aux1_ret'\<rparr>
in
 ret)"

lemma copy_const_to_operand_aux1_imp_correct:
  "copy_const_to_operand_aux1_ret (copy_const_to_operand_aux1_imp s) 
  = (1 ## (operand_bit_to_var_tail (prod_encode 
    (copy_const_to_operand_aux1_op s,copy_const_to_operand_aux1_diff s))) 
## (nth_bit_tail (copy_const_to_operand_aux1_x s) (copy_const_to_operand_aux1_diff s)) 
## 0)"
apply (simp only: copy_const_to_operand_aux1_imp_def)
apply (simp add: Let_def cons_imp_correct nth_bit_tail_imp_correct
   operand_bit_to_var_tail_imp_correct prod_encode_imp_correct nth_bit_tail'_correct)
done 

definition "copy_const_to_operand_aux1_imp_time t s \<equiv> 
(let
  nth_bit_tail_acc' = copy_const_to_operand_aux1_x s;
  t = t + 2;
  nth_bit_tail_n' = copy_const_to_operand_aux1_diff s;
  t = t + 2;
  nth_bit_tail_ret' = 0;
  t = t + 2;
  nth_bit_tail_state = \<lparr>nth_bit_tail_acc = nth_bit_tail_acc',
                        nth_bit_tail_n = nth_bit_tail_n',
                        nth_bit_tail_ret = nth_bit_tail_ret'\<rparr>;
  nth_bit_tail_ret_state = nth_bit_tail_imp nth_bit_tail_state;
  t = t + nth_bit_tail_imp_time 0 nth_bit_tail_state;

  cons_h' = nth_bit_tail_ret nth_bit_tail_ret_state;
  t = t + 2;
  cons_t' = 0;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  prod_encode_a' = copy_const_to_operand_aux1_op s;
  t = t + 2;
  prod_encode_b' = copy_const_to_operand_aux1_diff s;
  t = t + 2;
  prod_encode_ret' = 0;
  t = t + 2;
  prod_encode_state = \<lparr>prod_encode_a = prod_encode_a', 
                       prod_encode_b = prod_encode_b',
                       prod_encode_ret = prod_encode_ret'\<rparr>;
  prod_encode_ret_state = prod_encode_imp prod_encode_state;
  t = t + prod_encode_imp_time 0 prod_encode_state;

  operand_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
  t = t + 2;
  operand_bit_to_var_tail_ret' = 0;
  t = t + 2;
  operand_bit_to_var_tail_state = 
    \<lparr>operand_bit_to_var_tail_n = operand_bit_to_var_tail_n',
    operand_bit_to_var_tail_ret = operand_bit_to_var_tail_ret'\<rparr>;
  operand_bit_to_var_tail_ret_state 
    = operand_bit_to_var_tail_imp operand_bit_to_var_tail_state;
  t = t + operand_bit_to_var_tail_imp_time 0 operand_bit_to_var_tail_state;

  cons_h' = operand_bit_to_var_tail_ret operand_bit_to_var_tail_ret_state;
  t = t + 2;
  cons_t' = cons_ret cons_ret_state;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp  cons_state;
  t = t + cons_imp_time 0 cons_state;

  cons_h' = 1;
  t = t + 2;
  cons_t' = cons_ret cons_ret_state;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp  cons_state;
  t = t + cons_imp_time 0 cons_state;

  copy_const_to_operand_aux1_ret' = cons_ret cons_ret_state;
  t = t + 2;
  ret = \<lparr>copy_const_to_operand_aux1_x = copy_const_to_operand_aux1_x s,
        copy_const_to_operand_aux1_diff = copy_const_to_operand_aux1_diff s,
        copy_const_to_operand_aux1_op = copy_const_to_operand_aux1_op s,
        copy_const_to_operand_aux1_ret = copy_const_to_operand_aux1_ret'\<rparr>
in
 t)"

abbreviation "copy_const_to_operand_aux1_IMP_vars \<equiv>
  {copy_const_to_operand_aux1_op_str, copy_const_to_operand_aux1_diff_str,
  copy_const_to_operand_aux1_x_str, copy_const_to_operand_aux1_ret_str}"

definition "copy_const_to_operand_aux1_imp_to_HOL_state p s\<equiv> 
  \<lparr>copy_const_to_operand_aux1_x = s (add_prefix p copy_const_to_operand_aux1_x_str),
  copy_const_to_operand_aux1_diff = s (add_prefix p copy_const_to_operand_aux1_diff_str),
  copy_const_to_operand_aux1_op = s (add_prefix p copy_const_to_operand_aux1_op_str),
  copy_const_to_operand_aux1_ret = s (add_prefix p copy_const_to_operand_aux1_ret_str)\<rparr>"

lemmas copy_const_to_operand_aux1_state_translators=
copy_const_to_operand_aux1_imp_to_HOL_state_def
cons_imp_to_HOL_state_def
prod_encode_imp_to_HOL_state_def
operand_bit_to_var_tail_imp_to_HOL_state_def
nth_bit_tail_imp_to_HOL_state_def

definition "copy_const_to_operand_aux1_IMP_Minus \<equiv> 
   (nth_bit_tail_prefix @ nth_bit_tail_acc_str) 
     ::= A (V copy_const_to_operand_aux1_x_str);;
   (nth_bit_tail_prefix @ nth_bit_tail_n_str) 
     ::= A (V copy_const_to_operand_aux1_diff_str);;
   (nth_bit_tail_prefix @ nth_bit_tail_ret_str) 
     ::= A (N 0);;
   invoke_subprogram nth_bit_tail_prefix nth_bit_tail_IMP_Minus;;

   (cons_prefix @ cons_h_str) ::= A (V (nth_bit_tail_prefix @ nth_bit_tail_ret_str));;
   (cons_prefix @ cons_t_str) ::= A (N 0);;
   (cons_prefix @ cons_ret_str) ::= A (N 0);;
   invoke_subprogram cons_prefix cons_IMP_Minus;;

   (prod_encode_prefix @ prod_encode_a_str) ::= A (V copy_const_to_operand_aux1_op_str);;
   (prod_encode_prefix @ prod_encode_b_str) ::= A (V copy_const_to_operand_aux1_diff_str);;
   (prod_encode_prefix @ prod_encode_ret_str) ::= A (N 0);;
   invoke_subprogram prod_encode_prefix prod_encode_IMP_Minus;;

   (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_n_str)
     ::= A (V (prod_encode_prefix @ prod_encode_ret_str));;
   (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str)
     ::= A (N 0);;
    invoke_subprogram operand_bit_to_var_tail_prefix operand_bit_to_var_tail_IMP_Minus;;

   (cons_prefix @ cons_h_str) 
     ::= A (V (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str));;
   (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
   (cons_prefix @ cons_ret_str) ::= A (N 0);;
   invoke_subprogram cons_prefix cons_IMP_Minus;;

   (cons_prefix @ cons_h_str) ::= A (N 1);;
   (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
   (cons_prefix @ cons_ret_str) ::= A (N 0);;
   invoke_subprogram cons_prefix cons_IMP_Minus;;

   copy_const_to_operand_aux1_ret_str ::= A (V (cons_prefix @ cons_ret_str))
  "

lemma copy_const_to_operand_aux1_IMP_Minus_correct_function:
  "(invoke_subprogram p copy_const_to_operand_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_const_to_operand_aux1_ret_str)
      = copy_const_to_operand_aux1_ret
          (copy_const_to_operand_aux1_imp (copy_const_to_operand_aux1_imp_to_HOL_state p s))"
  apply (simp only: copy_const_to_operand_aux1_imp_def)
  apply (simp only: copy_const_to_operand_aux1_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule nth_bit_tail_IMP_Minus_correct[where vars=copy_const_to_operand_aux1_IMP_vars])
  subgoal premises p using p(24) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_const_to_operand_aux1_IMP_vars])
  subgoal premises p using p(26) by fastforce
  apply (erule prod_encode_IMP_Minus_correct[where vars="copy_const_to_operand_aux1_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
  subgoal premises p using p(28) by fastforce
  apply (erule operand_bit_to_var_tail_IMP_Minus_correct[where vars="copy_const_to_operand_aux1_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
  subgoal premises p using p(30) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_const_to_operand_aux1_IMP_vars])
  subgoal premises p using p(32) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_const_to_operand_aux1_IMP_vars])
  subgoal premises p using p(34) by fastforce
  apply (force simp: Let_def copy_const_to_operand_aux1_state_translators)
  done 

lemma copy_const_to_operand_aux1_IMP_Minus_correct_time:
  "(invoke_subprogram p copy_const_to_operand_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
    t =  (copy_const_to_operand_aux1_imp_time 0 (copy_const_to_operand_aux1_imp_to_HOL_state p s))"
  apply (simp only: copy_const_to_operand_aux1_imp_time_def)
  apply (simp only: copy_const_to_operand_aux1_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule nth_bit_tail_IMP_Minus_correct[where vars=copy_const_to_operand_aux1_IMP_vars])
  subgoal premises p using p(47) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_const_to_operand_aux1_IMP_vars])
  subgoal premises p using p(49) by fastforce
  apply (erule prod_encode_IMP_Minus_correct[where vars="copy_const_to_operand_aux1_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
  subgoal premises p using p(51) by fastforce
  apply (erule operand_bit_to_var_tail_IMP_Minus_correct[where vars="copy_const_to_operand_aux1_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
  subgoal premises p using p(53) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_const_to_operand_aux1_IMP_vars])
  subgoal premises p using p(55) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_const_to_operand_aux1_IMP_vars])
  subgoal premises p using p(57) by fastforce
  apply (force simp: Let_def copy_const_to_operand_aux1_state_translators)
  done 

lemma copy_const_to_operand_aux1_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ copy_const_to_operand_aux1_pref) copy_const_to_operand_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix copy_const_to_operand_aux1_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma copy_const_to_operand_aux1_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_const_to_operand_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (copy_const_to_operand_aux1_imp_time 0 (copy_const_to_operand_aux1_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) copy_const_to_operand_aux1_ret_str) =
          copy_const_to_operand_aux1_ret (copy_const_to_operand_aux1_imp
                                        (copy_const_to_operand_aux1_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_const_to_operand_aux1_IMP_Minus_correct_function
  by (auto simp: copy_const_to_operand_aux1_IMP_Minus_correct_time)
    (meson copy_const_to_operand_aux1_IMP_Minus_correct_effects set_mono_prefix) 


subsubsection copy_const_to_operand_acc

record copy_const_to_operand_acc_state = 
  copy_const_to_operand_acc_acc::nat
  copy_const_to_operand_acc_diff::nat 
  copy_const_to_operand_acc_i::nat
  copy_const_to_operand_acc_op::nat
  copy_const_to_operand_acc_x::nat
  copy_const_to_operand_acc_ret::nat

abbreviation "copy_const_to_operand_acc_prefix \<equiv> ''copy_const_to_operand_acc.''"
abbreviation "copy_const_to_operand_acc_acc_str \<equiv> ''acc''"
abbreviation "copy_const_to_operand_acc_diff_str \<equiv> ''diff''"
abbreviation "copy_const_to_operand_acc_i_str \<equiv> ''i''"
abbreviation "copy_const_to_operand_acc_op_str \<equiv> ''op''"
abbreviation "copy_const_to_operand_acc_x_str \<equiv> ''x''"
abbreviation "copy_const_to_operand_acc_ret_str \<equiv> ''ret''"

definition "copy_const_to_operand_acc_state_upd s \<equiv> 
 (let
  cons_h' = copy_const_to_operand_acc_acc s;
  cons_t' = 0;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  copy_const_to_operand_aux1_x' = copy_const_to_operand_acc_x s;
  copy_const_to_operand_aux1_diff' = copy_const_to_operand_acc_i s - copy_const_to_operand_acc_diff s;
  copy_const_to_operand_aux1_op'= copy_const_to_operand_acc_op s;
  copy_const_to_operand_aux1_ret' = 0;
  copy_const_to_operand_aux1_state = 
    \<lparr>copy_const_to_operand_aux1_x = copy_const_to_operand_aux1_x',
    copy_const_to_operand_aux1_diff = copy_const_to_operand_aux1_diff',
    copy_const_to_operand_aux1_op = copy_const_to_operand_aux1_op',
    copy_const_to_operand_aux1_ret = copy_const_to_operand_aux1_ret'\<rparr>;
  copy_const_to_operand_aux1_ret_state = copy_const_to_operand_aux1_imp copy_const_to_operand_aux1_state;

  cons_h' = copy_const_to_operand_aux1_ret copy_const_to_operand_aux1_ret_state;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = 2;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  copy_const_to_operand_acc_acc' = cons_ret cons_ret_state;
  copy_const_to_operand_acc_diff' = copy_const_to_operand_acc_diff s - 1;
  ret = 
   \<lparr>copy_const_to_operand_acc_acc = copy_const_to_operand_acc_acc',
   copy_const_to_operand_acc_diff = copy_const_to_operand_acc_diff',
   copy_const_to_operand_acc_i = copy_const_to_operand_acc_i s,
   copy_const_to_operand_acc_op = copy_const_to_operand_acc_op s,
   copy_const_to_operand_acc_x = copy_const_to_operand_acc_x s,
   copy_const_to_operand_acc_ret = copy_const_to_operand_acc_ret s\<rparr>
 in
  ret)"

definition "copy_const_to_operand_acc_imp_compute_loop_condition s \<equiv> 
  (let 
    cond = copy_const_to_operand_acc_diff s
   in 
    cond)"

definition "copy_const_to_operand_acc_imp_after_loop s \<equiv> 
(let
  copy_const_to_operand_acc_ret' = copy_const_to_operand_acc_acc s;
  ret = 
   \<lparr>copy_const_to_operand_acc_acc = copy_const_to_operand_acc_acc s,
   copy_const_to_operand_acc_diff = copy_const_to_operand_acc_diff s,
   copy_const_to_operand_acc_i = copy_const_to_operand_acc_i s,
   copy_const_to_operand_acc_op = copy_const_to_operand_acc_op s,
   copy_const_to_operand_acc_x = copy_const_to_operand_acc_x s,
   copy_const_to_operand_acc_ret = copy_const_to_operand_acc_ret'\<rparr>
in 
   ret)"

lemmas copy_const_to_operand_acc_imp_subprogram_simps = 
  copy_const_to_operand_acc_state_upd_def
  copy_const_to_operand_acc_imp_compute_loop_condition_def
  copy_const_to_operand_acc_imp_after_loop_def

function copy_const_to_operand_acc_imp::
  "copy_const_to_operand_acc_state \<Rightarrow> copy_const_to_operand_acc_state" where
  "copy_const_to_operand_acc_imp s =
  (if copy_const_to_operand_acc_imp_compute_loop_condition s \<noteq> 0
   then
    let next_iteration = copy_const_to_operand_acc_imp (copy_const_to_operand_acc_state_upd s)
    in next_iteration
   else
    let ret = copy_const_to_operand_acc_imp_after_loop s
    in ret
  )"
  by simp+
termination
  apply (relation "measure copy_const_to_operand_acc_diff")
  apply (simp add: copy_const_to_operand_acc_imp_subprogram_simps
    cons_imp_correct copy_const_to_operand_aux1_imp_correct Let_def)+
  done

declare copy_const_to_operand_acc_imp.simps [simp del]

lemma copy_const_to_operand_acc_imp_correct:
  "copy_const_to_operand_acc_ret (copy_const_to_operand_acc_imp s) =
    copy_const_to_operand_acc (copy_const_to_operand_acc_acc s) (copy_const_to_operand_acc_diff s)
    (copy_const_to_operand_acc_i s) (copy_const_to_operand_acc_op s) (copy_const_to_operand_acc_x s)"
  apply (induction s rule: copy_const_to_operand_acc_imp.induct)
  apply (subst copy_const_to_operand_acc_imp.simps)
  apply (subst copy_const_to_operand_acc.simps)
  apply (auto simp del: copy_const_to_operand_acc.simps 
  simp add: copy_const_to_operand_acc_imp_subprogram_simps Let_def
  cons_imp_correct copy_const_to_operand_aux1_imp_correct)
  done  

definition "copy_const_to_operand_acc_state_upd_time t s \<equiv> 
 (let
  cons_h' = copy_const_to_operand_acc_acc s;
  t = t + 2;
  cons_t' = 0;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  copy_const_to_operand_aux1_x' = copy_const_to_operand_acc_x s;
  t = t + 2;
  copy_const_to_operand_aux1_diff' = copy_const_to_operand_acc_i s - copy_const_to_operand_acc_diff s;
  t = t + 2;
  copy_const_to_operand_aux1_op'= copy_const_to_operand_acc_op s;
  t = t + 2;
  copy_const_to_operand_aux1_ret' = 0;
  t = t + 2;
  copy_const_to_operand_aux1_state = 
    \<lparr>copy_const_to_operand_aux1_x = copy_const_to_operand_aux1_x',
    copy_const_to_operand_aux1_diff = copy_const_to_operand_aux1_diff',
    copy_const_to_operand_aux1_op = copy_const_to_operand_aux1_op',
    copy_const_to_operand_aux1_ret = copy_const_to_operand_aux1_ret'\<rparr>;
  copy_const_to_operand_aux1_ret_state = copy_const_to_operand_aux1_imp copy_const_to_operand_aux1_state;
  t = t + copy_const_to_operand_aux1_imp_time 0 copy_const_to_operand_aux1_state;

  cons_h' = copy_const_to_operand_aux1_ret copy_const_to_operand_aux1_ret_state;
  t = t + 2;
  cons_t' = cons_ret cons_ret_state;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  cons_h' = 2;
  t = t + 2;
  cons_t' = cons_ret cons_ret_state;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  copy_const_to_operand_acc_acc' = cons_ret cons_ret_state;
  t = t + 2;
  copy_const_to_operand_acc_diff' = copy_const_to_operand_acc_diff s - 1;
  t = t + 2;
  ret = 
   \<lparr>copy_const_to_operand_acc_acc = copy_const_to_operand_acc_acc',
   copy_const_to_operand_acc_diff = copy_const_to_operand_acc_diff',
   copy_const_to_operand_acc_i = copy_const_to_operand_acc_i s,
   copy_const_to_operand_acc_op = copy_const_to_operand_acc_op s,
   copy_const_to_operand_acc_x = copy_const_to_operand_acc_x s,
   copy_const_to_operand_acc_ret = copy_const_to_operand_acc_ret s\<rparr>
 in
  t)"

definition "copy_const_to_operand_acc_imp_compute_loop_condition_time t s \<equiv> 
  (let 
    cond = copy_const_to_operand_acc_diff s;
    t = t + 2
   in 
    t)"

definition "copy_const_to_operand_acc_imp_after_loop_time t s \<equiv> 
(let
  copy_const_to_operand_acc_ret' = copy_const_to_operand_acc_acc s;
  t = t + 2;
  ret = 
   \<lparr>copy_const_to_operand_acc_acc = copy_const_to_operand_acc_acc s,
   copy_const_to_operand_acc_diff = copy_const_to_operand_acc_diff s,
   copy_const_to_operand_acc_i = copy_const_to_operand_acc_i s,
   copy_const_to_operand_acc_op = copy_const_to_operand_acc_op s,
   copy_const_to_operand_acc_x = copy_const_to_operand_acc_x s,
   copy_const_to_operand_acc_ret = copy_const_to_operand_acc_ret'\<rparr>
in 
   t)"

lemmas copy_const_to_operand_acc_imp_subprogram_time_simps = 
  copy_const_to_operand_acc_state_upd_time_def
  copy_const_to_operand_acc_imp_compute_loop_condition_time_def
  copy_const_to_operand_acc_imp_after_loop_time_def
  copy_const_to_operand_acc_imp_subprogram_simps

function copy_const_to_operand_acc_imp_time::
  "nat \<Rightarrow> copy_const_to_operand_acc_state \<Rightarrow> nat" where
  "copy_const_to_operand_acc_imp_time t s =
  copy_const_to_operand_acc_imp_compute_loop_condition_time 0 s +
  (if copy_const_to_operand_acc_imp_compute_loop_condition s \<noteq> 0
    then
      (let
        t = t + 1;
        next_iteration =
          copy_const_to_operand_acc_imp_time (t + copy_const_to_operand_acc_state_upd_time 0 s)
                         (copy_const_to_operand_acc_state_upd s)
       in next_iteration)
    else
      (let
        t = t + 2;
        ret = t + copy_const_to_operand_acc_imp_after_loop_time 0 s
       in ret)
  )"
  by auto
termination
  apply (relation "measure (copy_const_to_operand_acc_diff \<circ> snd)")
  by (simp add: copy_const_to_operand_acc_imp_subprogram_time_simps 
  copy_const_to_operand_aux1_imp_correct cons_imp_correct Let_def)+


declare copy_const_to_operand_acc_imp_time.simps [simp del]            

lemma copy_const_to_operand_acc_imp_time_acc:
  "(copy_const_to_operand_acc_imp_time (Suc t) s) = Suc (copy_const_to_operand_acc_imp_time t s)"
  by (induction t s rule: copy_const_to_operand_acc_imp_time.induct)
    ((subst (1 2) copy_const_to_operand_acc_imp_time.simps);
      (simp add: copy_const_to_operand_acc_state_upd_def))            

lemma copy_const_to_operand_acc_imp_time_acc_2_aux:
  "(copy_const_to_operand_acc_imp_time t s) = t + (copy_const_to_operand_acc_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: copy_const_to_operand_acc_imp_time_acc)+            

lemma copy_const_to_operand_acc_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (copy_const_to_operand_acc_imp_time t s) = t + (copy_const_to_operand_acc_imp_time 0 s)"
  by (rule copy_const_to_operand_acc_imp_time_acc_2_aux)            

lemma copy_const_to_operand_acc_imp_time_acc_3:
  "(copy_const_to_operand_acc_imp_time (a + b) s) = a + (copy_const_to_operand_acc_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: copy_const_to_operand_acc_imp_time_acc)+            

abbreviation "copy_const_to_operand_acc_while_cond \<equiv> ''condition''"

definition "copy_const_to_operand_acc_IMP_init_while_cond \<equiv>
  copy_const_to_operand_acc_while_cond ::= A (V copy_const_to_operand_acc_diff_str)
"

definition "copy_const_to_operand_acc_IMP_loop_body \<equiv> 
(cons_prefix @ cons_h_str) ::= A (V copy_const_to_operand_acc_acc_str);;
(cons_prefix @ cons_t_str) ::= A (N 0);;
(cons_prefix @ cons_ret_str) ::= A (N 0);;
invoke_subprogram cons_prefix cons_IMP_Minus;;

(copy_const_to_operand_aux1_prefix @ copy_const_to_operand_aux1_x_str)
  ::= A (V copy_const_to_operand_acc_x_str);;
(copy_const_to_operand_aux1_prefix @ copy_const_to_operand_aux1_diff_str)
  ::= Sub (V copy_const_to_operand_acc_i_str) (V copy_const_to_operand_acc_diff_str);;
(copy_const_to_operand_aux1_prefix @ copy_const_to_operand_aux1_op_str)
  ::= A (V copy_const_to_operand_acc_op_str);;
  (copy_const_to_operand_aux1_prefix @ copy_const_to_operand_aux1_ret_str)
  ::= A (N 0);;
invoke_subprogram copy_const_to_operand_aux1_prefix copy_const_to_operand_aux1_IMP_Minus;;
 
(cons_prefix @ cons_h_str) 
  ::= A (V (copy_const_to_operand_aux1_prefix @ copy_const_to_operand_aux1_ret_str));;
(cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
(cons_prefix @ cons_ret_str) ::= A (N 0);;
invoke_subprogram cons_prefix cons_IMP_Minus;;

(cons_prefix @ cons_h_str) ::= A (N 2);;
(cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
(cons_prefix @ cons_ret_str) ::= A (N 0);;
invoke_subprogram cons_prefix cons_IMP_Minus;;

copy_const_to_operand_acc_acc_str ::= A (V (cons_prefix @ cons_ret_str));;
copy_const_to_operand_acc_diff_str ::= Sub (V copy_const_to_operand_acc_diff_str) (N 1)"

definition "copy_const_to_operand_acc_IMP_after_loop \<equiv>
copy_const_to_operand_acc_ret_str ::= A (V copy_const_to_operand_acc_acc_str)
"

definition copy_const_to_operand_acc_IMP_Minus where
  "copy_const_to_operand_acc_IMP_Minus \<equiv>
  copy_const_to_operand_acc_IMP_init_while_cond;;
  WHILE copy_const_to_operand_acc_while_cond \<noteq>0 DO (
    copy_const_to_operand_acc_IMP_loop_body;;
    copy_const_to_operand_acc_IMP_init_while_cond
  );;
  copy_const_to_operand_acc_IMP_after_loop"

abbreviation "copy_const_to_operand_acc_IMP_vars\<equiv>
  {copy_const_to_operand_acc_ret_str, copy_const_to_operand_acc_acc_str,
  copy_const_to_operand_acc_i_str, copy_const_to_operand_acc_diff_str,
  copy_const_to_operand_acc_op_str, copy_const_to_operand_acc_x_str,
  copy_const_to_operand_acc_while_cond}"

lemmas copy_const_to_operand_acc_IMP_subprogram_simps =
  copy_const_to_operand_acc_IMP_init_while_cond_def
  copy_const_to_operand_acc_IMP_loop_body_def
  copy_const_to_operand_acc_IMP_after_loop_def

definition "copy_const_to_operand_acc_imp_to_HOL_state p s =
  \<lparr>copy_const_to_operand_acc_acc = (s (add_prefix p copy_const_to_operand_acc_acc_str)),
   copy_const_to_operand_acc_diff = (s (add_prefix p copy_const_to_operand_acc_diff_str)),
   copy_const_to_operand_acc_i = (s (add_prefix p copy_const_to_operand_acc_i_str)),
   copy_const_to_operand_acc_op = (s (add_prefix p copy_const_to_operand_acc_op_str)),
   copy_const_to_operand_acc_x = (s (add_prefix p copy_const_to_operand_acc_x_str)),
   copy_const_to_operand_acc_ret = (s (add_prefix p copy_const_to_operand_acc_ret_str))\<rparr>"

lemmas copy_const_to_operand_acc_state_translators =
  copy_const_to_operand_acc_imp_to_HOL_state_def
  copy_const_to_operand_aux1_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def

lemmas copy_const_to_operand_acc_complete_simps =
  copy_const_to_operand_acc_IMP_subprogram_simps
  copy_const_to_operand_acc_imp_subprogram_simps
  copy_const_to_operand_acc_state_translators

lemma copy_const_to_operand_acc_IMP_Minus_correct_function:
  "(invoke_subprogram p copy_const_to_operand_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_const_to_operand_acc_ret_str)
      = copy_const_to_operand_acc_ret
          (copy_const_to_operand_acc_imp (copy_const_to_operand_acc_imp_to_HOL_state p s))"
  apply(induction "copy_const_to_operand_acc_imp_to_HOL_state p s" arbitrary: s s' t
    rule: copy_const_to_operand_acc_imp.induct)
  apply(subst copy_const_to_operand_acc_imp.simps)
  apply(simp only: copy_const_to_operand_acc_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule While_tE)

  subgoal
    apply(simp only: copy_const_to_operand_acc_IMP_subprogram_simps prefix_simps)
    by(fastforce simp: copy_const_to_operand_acc_IMP_subprogram_simps
        copy_const_to_operand_acc_imp_subprogram_simps
        copy_const_to_operand_acc_state_translators)

  apply(erule Seq_E)+
  apply(dest_com_gen)

  subgoal
      apply(simp only: copy_const_to_operand_acc_IMP_init_while_cond_def prefix_simps)
      by(fastforce simp add: copy_const_to_operand_acc_complete_simps)

  subgoal
      apply(subst (asm) copy_const_to_operand_acc_IMP_init_while_cond_def)
      apply(simp only: copy_const_to_operand_acc_IMP_loop_body_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
      subgoal premises p using p(24) by fastforce
      apply(erule copy_const_to_operand_aux1_IMP_Minus_correct[where 
        vars = "copy_const_to_operand_acc_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
      subgoal premises p using p(26) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
      subgoal premises p using p(28) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
      subgoal premises p using p(30) by fastforce
      by (force simp: copy_const_to_operand_acc_imp_subprogram_simps
          copy_const_to_operand_acc_state_translators Let_def)

  subgoal
      apply(simp only: copy_const_to_operand_acc_IMP_init_while_cond_def prefix_simps
          copy_const_to_operand_acc_IMP_loop_body_def)
      apply(erule Seq_E)+
      apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
      subgoal premises p using p(24) by fastforce
      apply(erule copy_const_to_operand_aux1_IMP_Minus_correct[where 
        vars = "copy_const_to_operand_acc_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
      subgoal premises p using p(26) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
      subgoal premises p using p(28) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
      subgoal premises p using p(30) by fastforce
      by (force simp: copy_const_to_operand_acc_imp_subprogram_simps
          copy_const_to_operand_acc_state_translators Let_def)
  done        

lemma copy_const_to_operand_acc_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ copy_const_to_operand_acc_pref) copy_const_to_operand_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix copy_const_to_operand_acc_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemmas copy_const_to_operand_acc_complete_time_simps =
  copy_const_to_operand_acc_imp_subprogram_time_simps
  copy_const_to_operand_acc_imp_time_acc_2
  copy_const_to_operand_acc_imp_time_acc_3
  copy_const_to_operand_acc_state_translators

lemma copy_const_to_operand_acc_IMP_Minus_correct_time:
  "(invoke_subprogram p copy_const_to_operand_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = copy_const_to_operand_acc_imp_time 0 (copy_const_to_operand_acc_imp_to_HOL_state p s)"
  apply(induction "copy_const_to_operand_acc_imp_to_HOL_state p s" arbitrary: s s' t
      rule: copy_const_to_operand_acc_imp.induct)
  apply(subst copy_const_to_operand_acc_imp_time.simps)
  apply(simp only: copy_const_to_operand_acc_IMP_Minus_def prefix_simps)

  apply(erule Seq_tE)+
  apply(erule While_tE_time)

  subgoal
    apply(simp only: copy_const_to_operand_acc_IMP_subprogram_simps prefix_simps)
    by (force simp: copy_const_to_operand_acc_IMP_subprogram_simps
        copy_const_to_operand_acc_imp_subprogram_time_simps copy_const_to_operand_acc_state_translators)

  apply(erule Seq_tE)+
  apply(simp add: add.assoc)
  apply(dest_com_gen_time)

  subgoal
    apply(simp only: copy_const_to_operand_acc_IMP_init_while_cond_def prefix_simps)
    by(fastforce simp add: copy_const_to_operand_acc_complete_simps)

  subgoal
    apply(subst (asm) copy_const_to_operand_acc_IMP_init_while_cond_def)
    apply(simp only: copy_const_to_operand_acc_IMP_loop_body_def prefix_simps)
    apply(erule Seq_E)+
    apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
    subgoal premises p using p(27) by fastforce
    apply(erule copy_const_to_operand_aux1_IMP_Minus_correct[where 
      vars = "copy_const_to_operand_acc_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
    subgoal premises p using p(29) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
    subgoal premises p using p(31) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
    subgoal premises p using p(33) by fastforce
    by (force simp: copy_const_to_operand_acc_imp_subprogram_simps
        copy_const_to_operand_acc_state_translators Let_def)
  
  subgoal
    apply(simp only: prefix_simps copy_const_to_operand_acc_IMP_init_while_cond_def
        copy_const_to_operand_acc_IMP_loop_body_def)
    apply(erule Seq_tE)+
    apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
    subgoal premises p using p(45) by fastforce
    apply(erule copy_const_to_operand_aux1_IMP_Minus_correct[where 
      vars = "copy_const_to_operand_acc_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
    subgoal premises p using p(47) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
    subgoal premises p using p(49) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
    subgoal premises p using p(51) by fastforce
    by(force simp: copy_const_to_operand_acc_complete_time_simps Let_def)
 done      

lemma copy_const_to_operand_acc_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_const_to_operand_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (copy_const_to_operand_acc_imp_time 0 (copy_const_to_operand_acc_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) copy_const_to_operand_acc_ret_str) =
          copy_const_to_operand_acc_ret (copy_const_to_operand_acc_imp
                                        (copy_const_to_operand_acc_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_const_to_operand_acc_IMP_Minus_correct_function
  by (auto simp: copy_const_to_operand_acc_IMP_Minus_correct_time)
    (meson copy_const_to_operand_acc_IMP_Minus_correct_effects set_mono_prefix)

subsubsection copy_const_to_operand_tail

record copy_const_to_operand_tail_state = 
  copy_const_to_operand_tail_i::nat
  copy_const_to_operand_tail_op::nat
  copy_const_to_operand_tail_x::nat
  copy_const_to_operand_tail_ret::nat

abbreviation "copy_const_to_operand_tail_prefix \<equiv> ''copy_const_to_operand_tail.''"
abbreviation "copy_const_to_operand_tail_i_str \<equiv> ''i''"
abbreviation "copy_const_to_operand_tail_op_str \<equiv> ''op''"
abbreviation "copy_const_to_operand_tail_x_str \<equiv> ''x''"
abbreviation "copy_const_to_operand_tail_ret_str \<equiv> ''ret''"

function copy_const_to_operand_tail_imp 
  :: "copy_const_to_operand_tail_state \<Rightarrow> copy_const_to_operand_tail_state" where 
"copy_const_to_operand_tail_imp s = 
  (let
    cons_h' = 0;
    cons_t' = 0;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    copy_const_to_operand_acc_acc' = cons_ret cons_ret_state;
    copy_const_to_operand_acc_diff' = copy_const_to_operand_tail_i s;
    copy_const_to_operand_acc_i' = copy_const_to_operand_tail_i s;
    copy_const_to_operand_acc_op' = copy_const_to_operand_tail_op s;
    copy_const_to_operand_acc_x' = copy_const_to_operand_tail_x s;
    copy_const_to_operand_acc_ret' = 0;
    copy_const_to_operand_acc_state = 
      \<lparr>copy_const_to_operand_acc_acc = copy_const_to_operand_acc_acc',
      copy_const_to_operand_acc_diff = copy_const_to_operand_acc_diff',
      copy_const_to_operand_acc_i = copy_const_to_operand_acc_i',
      copy_const_to_operand_acc_op = copy_const_to_operand_acc_op',
      copy_const_to_operand_acc_x = copy_const_to_operand_acc_x',
      copy_const_to_operand_acc_ret = copy_const_to_operand_acc_ret'\<rparr>;
    copy_const_to_operand_acc_ret_state
      = copy_const_to_operand_acc_imp copy_const_to_operand_acc_state;
    copy_const_to_operand_tail_ret' = 
      copy_const_to_operand_acc_ret copy_const_to_operand_acc_ret_state;
    ret =
      \<lparr>copy_const_to_operand_tail_i = copy_const_to_operand_tail_i s,
      copy_const_to_operand_tail_op = copy_const_to_operand_tail_op s,
      copy_const_to_operand_tail_x = copy_const_to_operand_tail_x s,
      copy_const_to_operand_tail_ret = copy_const_to_operand_tail_ret'\<rparr>
  in 
   ret)" by simp+
  termination 
  by (relation "measure copy_const_to_operand_tail_i", simp)

declare copy_const_to_operand_tail_imp.simps[simp del]

lemma copy_const_to_operand_tail_imp_correct:
  "copy_const_to_operand_tail_ret (copy_const_to_operand_tail_imp s)
    = copy_const_to_operand_tail (copy_const_to_operand_tail_i s) 
      (copy_const_to_operand_tail_op s) (copy_const_to_operand_tail_x s)"
apply (simp only: copy_const_to_operand_tail_imp.simps)
apply (auto simp add: copy_const_to_operand_acc_imp_correct cons_imp_correct Let_def
  copy_const_to_operand_tail_def)
done 

function copy_const_to_operand_tail_imp_time 
  :: "nat \<Rightarrow> copy_const_to_operand_tail_state \<Rightarrow> nat" where 
"copy_const_to_operand_tail_imp_time t s = 
  (let
    cons_h' = 0;
    t = t + 2;
    cons_t' = 0;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    copy_const_to_operand_acc_acc' = cons_ret cons_ret_state;
    t = t + 2;
    copy_const_to_operand_acc_diff' = copy_const_to_operand_tail_i s;
    t = t + 2;
    copy_const_to_operand_acc_i' = copy_const_to_operand_tail_i s;
    t = t + 2;
    copy_const_to_operand_acc_op' = copy_const_to_operand_tail_op s;
    t = t + 2;
    copy_const_to_operand_acc_x' = copy_const_to_operand_tail_x s;
    t = t + 2;
    copy_const_to_operand_acc_ret' = 0;
    t = t + 2;
    copy_const_to_operand_acc_state = 
      \<lparr>copy_const_to_operand_acc_acc = copy_const_to_operand_acc_acc',
      copy_const_to_operand_acc_diff = copy_const_to_operand_acc_diff',
      copy_const_to_operand_acc_i = copy_const_to_operand_acc_i',
      copy_const_to_operand_acc_op = copy_const_to_operand_acc_op',
      copy_const_to_operand_acc_x = copy_const_to_operand_acc_x',
      copy_const_to_operand_acc_ret = copy_const_to_operand_acc_ret'\<rparr>;
    copy_const_to_operand_acc_ret_state
      = copy_const_to_operand_acc_imp copy_const_to_operand_acc_state;
    t = t + copy_const_to_operand_acc_imp_time 0 copy_const_to_operand_acc_state;

    copy_const_to_operand_tail_ret' = 
      copy_const_to_operand_acc_ret copy_const_to_operand_acc_ret_state;
    t = t + 2;
    ret =
      \<lparr>copy_const_to_operand_tail_i = copy_const_to_operand_tail_i s,
      copy_const_to_operand_tail_op = copy_const_to_operand_tail_op s,
      copy_const_to_operand_tail_x = copy_const_to_operand_tail_x s,
      copy_const_to_operand_tail_ret = copy_const_to_operand_tail_ret'\<rparr>
  in 
   t)" by auto
  termination 
  by (relation "measure (copy_const_to_operand_tail_i \<circ> snd)", simp)

abbreviation "copy_const_to_operand_tail_IMP_vars \<equiv> 
  {copy_const_to_operand_tail_i_str, copy_const_to_operand_tail_op_str,
  copy_const_to_operand_tail_x_str, copy_const_to_operand_tail_ret_str}"

definition "copy_const_to_operand_tail_imp_to_HOL_state p s \<equiv> 
   \<lparr>copy_const_to_operand_tail_i = s (add_prefix p copy_const_to_operand_tail_i_str),
    copy_const_to_operand_tail_op = s (add_prefix p copy_const_to_operand_tail_op_str),
    copy_const_to_operand_tail_x = s (add_prefix p copy_const_to_operand_tail_x_str),
    copy_const_to_operand_tail_ret = s (add_prefix p copy_const_to_operand_tail_ret_str)\<rparr>"

lemmas copy_const_to_operand_tail_state_translators=
  copy_const_to_operand_tail_imp_to_HOL_state_def
  copy_const_to_operand_acc_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def

definition "copy_const_to_operand_tail_IMP_Minus \<equiv> 
  (cons_prefix @ cons_h_str) ::= A (N 0);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (copy_const_to_operand_acc_prefix @ copy_const_to_operand_acc_acc_str)
    ::= A (V (cons_prefix @ cons_ret_str));;
  (copy_const_to_operand_acc_prefix @ copy_const_to_operand_acc_diff_str)
    ::= A (V copy_const_to_operand_tail_i_str);;
  (copy_const_to_operand_acc_prefix @ copy_const_to_operand_acc_i_str)
    ::= A (V copy_const_to_operand_tail_i_str);;
  (copy_const_to_operand_acc_prefix @ copy_const_to_operand_acc_op_str)
    ::= A (V copy_const_to_operand_tail_op_str);;
  (copy_const_to_operand_acc_prefix @ copy_const_to_operand_acc_x_str)
    ::= A (V copy_const_to_operand_tail_x_str);;
  (copy_const_to_operand_acc_prefix @ copy_const_to_operand_acc_ret_str)
    ::= A (N 0);;
  invoke_subprogram copy_const_to_operand_acc_prefix copy_const_to_operand_acc_IMP_Minus;;
  copy_const_to_operand_tail_ret_str 
    ::= A (V (copy_const_to_operand_acc_prefix @ copy_const_to_operand_acc_ret_str))"

lemma copy_const_to_operand_tail_IMP_Minus_correct_function:
  "(invoke_subprogram p copy_const_to_operand_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_const_to_operand_tail_ret_str)
      = copy_const_to_operand_tail_ret
          (copy_const_to_operand_tail_imp (copy_const_to_operand_tail_imp_to_HOL_state p s))"
  apply (simp only: copy_const_to_operand_tail_imp.simps)
  apply (simp only: copy_const_to_operand_tail_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule cons_IMP_Minus_correct[where vars = copy_const_to_operand_tail_IMP_vars])
  subgoal premises p using p(12) by fastforce
  apply (erule copy_const_to_operand_acc_IMP_Minus_correct[where vars = copy_const_to_operand_tail_IMP_vars])
  subgoal premises p using p(14) by fastforce
  apply (force simp: copy_const_to_operand_tail_state_translators Let_def)
  done 

lemma copy_const_to_operand_tail_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ copy_const_to_operand_acc_pref) copy_const_to_operand_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix copy_const_to_operand_acc_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemma copy_const_to_operand_tail_IMP_Minus_correct_time:
  "(invoke_subprogram p copy_const_to_operand_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = copy_const_to_operand_tail_imp_time 0 (copy_const_to_operand_tail_imp_to_HOL_state p s)"
  apply (simp only: copy_const_to_operand_tail_imp_time.simps)
  apply (simp only: copy_const_to_operand_tail_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule cons_IMP_Minus_correct[where vars = copy_const_to_operand_tail_IMP_vars])
  subgoal premises p using p(23) by fastforce
  apply (erule copy_const_to_operand_acc_IMP_Minus_correct[where vars = copy_const_to_operand_tail_IMP_vars])
  subgoal premises p using p(25) by fastforce
  apply (force simp: copy_const_to_operand_tail_state_translators Let_def)
  done 

lemma copy_const_to_operand_tail_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_const_to_operand_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (copy_const_to_operand_tail_imp_time 0 (copy_const_to_operand_tail_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) copy_const_to_operand_tail_ret_str) =
          copy_const_to_operand_tail_ret (copy_const_to_operand_tail_imp
                                        (copy_const_to_operand_tail_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_const_to_operand_tail_IMP_Minus_correct_function 
      copy_const_to_operand_tail_IMP_Minus_correct_time
       set_mono_prefix
  by (smt (verit, ccfv_SIG) com_add_prefix_valid_subset com_only_vars)

subsection copy_atom_to_operand_nat

record copy_atom_to_operand_nat_state = 
  copy_atom_to_operand_nat_n::nat
  copy_atom_to_operand_nat_op::nat
  copy_atom_to_operand_nat_a::nat
  copy_atom_to_operand_nat_ret::nat

abbreviation "copy_atom_to_operand_nat_prefix \<equiv> ''copy_atom_to_operand_nat.''"
abbreviation "copy_atom_to_operand_nat_n_str \<equiv> ''n''"
abbreviation "copy_atom_to_operand_nat_op_str \<equiv> ''op''"
abbreviation "copy_atom_to_operand_nat_a_str \<equiv> ''a''"
abbreviation "copy_atom_to_operand_nat_ret_str \<equiv> ''ret''"
abbreviation "copy_atom_to_operand_nat_cond \<equiv> ''cond''"

function copy_atom_to_operand_nat_imp 
  :: "copy_atom_to_operand_nat_state \<Rightarrow> copy_atom_to_operand_nat_state"
where 
"copy_atom_to_operand_nat_imp s = 
(let
  fst'_state_p' = copy_atom_to_operand_nat_a s;
  fst'_state = \<lparr>fst'_state_p = fst'_state_p'\<rparr>;
  fst'_ret_state = fst'_imp fst'_state;
  cond = fst'_state_p fst'_ret_state
in
  (if cond \<noteq> 0 
  then (let
         snd'_state_p' = copy_atom_to_operand_nat_a s;
         snd'_state = \<lparr>snd'_state_p = snd'_state_p'\<rparr>;
         snd'_ret_state = snd'_imp snd'_state;
         
         copy_const_to_operand_tail_i' = copy_atom_to_operand_nat_n s;
         copy_const_to_operand_tail_op' = copy_atom_to_operand_nat_op s;
         copy_const_to_operand_tail_x' = snd'_state_p snd'_ret_state;
         copy_const_to_operand_tail_ret' = 0;
         copy_const_to_operand_tail_state 
           = \<lparr>copy_const_to_operand_tail_i = copy_const_to_operand_tail_i',
             copy_const_to_operand_tail_op = copy_const_to_operand_tail_op',
             copy_const_to_operand_tail_x = copy_const_to_operand_tail_x',
             copy_const_to_operand_tail_ret = copy_const_to_operand_tail_ret'\<rparr>;
         copy_const_to_operand_tail_ret_state = 
            copy_const_to_operand_tail_imp copy_const_to_operand_tail_state;
         copy_atom_to_operand_nat_ret' 
            = copy_const_to_operand_tail_ret copy_const_to_operand_tail_ret_state;
         ret =
           \<lparr>copy_atom_to_operand_nat_n = copy_atom_to_operand_nat_n s,
            copy_atom_to_operand_nat_op = copy_atom_to_operand_nat_op s,
            copy_atom_to_operand_nat_a = copy_atom_to_operand_nat_a s,
            copy_atom_to_operand_nat_ret = copy_atom_to_operand_nat_ret'\<rparr>
        in
         ret)
  else (let
         snd'_state_p' = copy_atom_to_operand_nat_a s;
         snd'_state = \<lparr>snd'_state_p = snd'_state_p'\<rparr>;
         snd'_ret_state = snd'_imp snd'_state;
         
         copy_var_to_operand_tail_i' = copy_atom_to_operand_nat_n s;
         copy_var_to_operand_tail_op' = copy_atom_to_operand_nat_op s;
         copy_var_to_operand_tail_v' = snd'_state_p snd'_ret_state;
         copy_var_to_operand_tail_ret' = 0;
         copy_var_to_operand_tail_state 
           = \<lparr>copy_var_to_operand_tail_i = copy_var_to_operand_tail_i',
             copy_var_to_operand_tail_op = copy_var_to_operand_tail_op',
             copy_var_to_operand_tail_v = copy_var_to_operand_tail_v',
             copy_var_to_operand_tail_ret = copy_var_to_operand_tail_ret'\<rparr>;
         copy_var_to_operand_tail_ret_state = 
            copy_var_to_operand_tail_imp copy_var_to_operand_tail_state;
         copy_atom_to_operand_nat_ret' 
            = copy_var_to_operand_tail_ret copy_var_to_operand_tail_ret_state;
         ret =
           \<lparr>copy_atom_to_operand_nat_n = copy_atom_to_operand_nat_n s,
            copy_atom_to_operand_nat_op = copy_atom_to_operand_nat_op s,
            copy_atom_to_operand_nat_a = copy_atom_to_operand_nat_a s,
            copy_atom_to_operand_nat_ret = copy_atom_to_operand_nat_ret'\<rparr>
        in
         ret)
  ))" by simp+
termination by (relation "measure copy_atom_to_operand_nat_n", simp)

declare copy_atom_to_operand_nat_imp.simps[simp del]

lemma copy_atom_to_operand_nat_imp_correct[let_function_correctness]:
  "copy_atom_to_operand_nat_ret (copy_atom_to_operand_nat_imp s) = 
    copy_atom_to_operand_nat (copy_atom_to_operand_nat_n s)
      (copy_atom_to_operand_nat_op s) (copy_atom_to_operand_nat_a s)"
apply (simp only: copy_atom_to_operand_nat_imp.simps)
apply (simp add: copy_var_to_operand_tail_imp_correct
copy_const_to_operand_tail_imp_correct fst'_imp_correct snd'_imp_correct Let_def)
by (simp add: fst_nat_fst'_nat snd_nat_snd'_nat copy_atom_to_operand_nat_def
subtail_copy_const_to_operand subtail_copy_var_to_operand)

function copy_atom_to_operand_nat_imp_time 
  :: "nat \<Rightarrow> copy_atom_to_operand_nat_state \<Rightarrow> nat"
where 
"copy_atom_to_operand_nat_imp_time t s = 
(let
  fst'_state_p' = copy_atom_to_operand_nat_a s;
  t = t + 2;
  fst'_state = \<lparr>fst'_state_p = fst'_state_p'\<rparr>;
  fst'_ret_state = fst'_imp fst'_state;
  t = t + fst'_imp_time 0 fst'_state;
  cond = fst'_state_p fst'_ret_state;
  t = t + 2
in
  (if cond \<noteq> 0 
  then (let
         t = t + 1;
         snd'_state_p' = copy_atom_to_operand_nat_a s;
         t = t + 2;
         snd'_state = \<lparr>snd'_state_p = snd'_state_p'\<rparr>;
         snd'_ret_state = snd'_imp snd'_state;
         t = t + snd'_imp_time 0 snd'_state;
         
         copy_const_to_operand_tail_i' = copy_atom_to_operand_nat_n s;
         t = t + 2;
         copy_const_to_operand_tail_op' = copy_atom_to_operand_nat_op s;
         t = t + 2;
         copy_const_to_operand_tail_x' = snd'_state_p snd'_ret_state;
         t = t + 2;
         copy_const_to_operand_tail_ret' = 0;
         t = t + 2;
         copy_const_to_operand_tail_state 
           = \<lparr>copy_const_to_operand_tail_i = copy_const_to_operand_tail_i',
             copy_const_to_operand_tail_op = copy_const_to_operand_tail_op',
             copy_const_to_operand_tail_x = copy_const_to_operand_tail_x',
             copy_const_to_operand_tail_ret = copy_const_to_operand_tail_ret'\<rparr>;
         copy_const_to_operand_tail_ret_state = 
            copy_const_to_operand_tail_imp copy_const_to_operand_tail_state;
         t = t + copy_const_to_operand_tail_imp_time 0 copy_const_to_operand_tail_state;
         copy_atom_to_operand_nat_ret' 
            = copy_const_to_operand_tail_ret copy_const_to_operand_tail_ret_state;
         t = t + 2;
         ret =
           \<lparr>copy_atom_to_operand_nat_n = copy_atom_to_operand_nat_n s,
            copy_atom_to_operand_nat_op = copy_atom_to_operand_nat_op s,
            copy_atom_to_operand_nat_a = copy_atom_to_operand_nat_a s,
            copy_atom_to_operand_nat_ret = copy_atom_to_operand_nat_ret'\<rparr>
        in
         t)
  else (let
         t = t + 1;
         snd'_state_p' = copy_atom_to_operand_nat_a s;
         t = t + 2;
         snd'_state = \<lparr>snd'_state_p = snd'_state_p'\<rparr>;
         snd'_ret_state = snd'_imp snd'_state;
         t = t + snd'_imp_time 0 snd'_state;
         
         copy_var_to_operand_tail_i' = copy_atom_to_operand_nat_n s;
         t = t + 2;
         copy_var_to_operand_tail_op' = copy_atom_to_operand_nat_op s;
         t = t + 2;
         copy_var_to_operand_tail_v' = snd'_state_p snd'_ret_state;
         t = t + 2;
         copy_var_to_operand_tail_ret' = 0;
         t = t + 2;
         copy_var_to_operand_tail_state 
           = \<lparr>copy_var_to_operand_tail_i = copy_var_to_operand_tail_i',
             copy_var_to_operand_tail_op = copy_var_to_operand_tail_op',
             copy_var_to_operand_tail_v = copy_var_to_operand_tail_v',
             copy_var_to_operand_tail_ret = copy_var_to_operand_tail_ret'\<rparr>;
         copy_var_to_operand_tail_ret_state = 
            copy_var_to_operand_tail_imp copy_var_to_operand_tail_state;
         t = t + copy_var_to_operand_tail_imp_time 0 copy_var_to_operand_tail_state;
         copy_atom_to_operand_nat_ret' 
            = copy_var_to_operand_tail_ret copy_var_to_operand_tail_ret_state;
         t = t + 2;
         ret =
           \<lparr>copy_atom_to_operand_nat_n = copy_atom_to_operand_nat_n s,
            copy_atom_to_operand_nat_op = copy_atom_to_operand_nat_op s,
            copy_atom_to_operand_nat_a = copy_atom_to_operand_nat_a s,
            copy_atom_to_operand_nat_ret = copy_atom_to_operand_nat_ret'\<rparr>
        in
         t)
  ))" by auto
termination by (relation "measure (copy_atom_to_operand_nat_n \<circ> snd)", simp)

declare copy_atom_to_operand_nat_imp_time.simps[simp del]

abbreviation "copy_atom_to_operand_nat_IMP_vars \<equiv> 
 {copy_atom_to_operand_nat_ret_str, copy_atom_to_operand_nat_n_str,
 copy_atom_to_operand_nat_op_str, copy_atom_to_operand_nat_a_str,
 copy_atom_to_operand_nat_cond}"

definition "copy_atom_to_operand_nat_imp_to_HOL_state p s\<equiv> 
\<lparr>copy_atom_to_operand_nat_n = s (add_prefix p copy_atom_to_operand_nat_n_str),
copy_atom_to_operand_nat_op = s (add_prefix p copy_atom_to_operand_nat_op_str),
copy_atom_to_operand_nat_a = s (add_prefix p copy_atom_to_operand_nat_a_str),
copy_atom_to_operand_nat_ret = s (add_prefix p copy_atom_to_operand_nat_ret_str)\<rparr>"

lemmas copy_atom_to_operand_nat_state_translators=
  copy_atom_to_operand_nat_imp_to_HOL_state_def
  copy_var_to_operand_tail_imp_to_HOL_state_def
  copy_const_to_operand_tail_imp_to_HOL_state_def
  fst'_imp_to_HOL_state_def snd'_imp_to_HOL_state_def

definition "copy_atom_to_operand_nat_IMP_Minus \<equiv> 
  (fst'_prefix @ fst'_p_str) ::= A (V copy_atom_to_operand_nat_a_str);;
  invoke_subprogram fst'_prefix fst'_IMP_Minus;;
  copy_atom_to_operand_nat_cond ::= A (V (fst'_prefix @ fst'_p_str));;
  IF copy_atom_to_operand_nat_cond\<noteq>0 
  THEN 
    (
    (snd'_prefix @ snd'_p_str) ::= A (V copy_atom_to_operand_nat_a_str);;
    invoke_subprogram snd'_prefix snd'_IMP_Minus;;

    (copy_const_to_operand_tail_prefix @ copy_const_to_operand_tail_i_str)
      ::= A (V copy_atom_to_operand_nat_n_str);;
    (copy_const_to_operand_tail_prefix @ copy_const_to_operand_tail_op_str)
      ::= A (V copy_atom_to_operand_nat_op_str);;
    (copy_const_to_operand_tail_prefix @ copy_const_to_operand_tail_x_str)
      ::= A (V (snd'_prefix @ snd'_p_str));;
    (copy_const_to_operand_tail_prefix @ copy_const_to_operand_tail_ret_str)
      ::= A (N 0);;
    invoke_subprogram copy_const_to_operand_tail_prefix copy_const_to_operand_tail_IMP_Minus;;

    (copy_atom_to_operand_nat_ret_str) ::=
      A (V (copy_const_to_operand_tail_prefix @ copy_const_to_operand_tail_ret_str))
    )
  ELSE 
    (
    (snd'_prefix @ snd'_p_str) ::= A (V copy_atom_to_operand_nat_a_str);;
    invoke_subprogram snd'_prefix snd'_IMP_Minus;;

    (copy_var_to_operand_tail_prefix @ copy_var_to_operand_tail_i_str)
      ::= A (V copy_atom_to_operand_nat_n_str);;
    (copy_var_to_operand_tail_prefix @ copy_var_to_operand_tail_op_str)
      ::= A (V copy_atom_to_operand_nat_op_str);;
    (copy_var_to_operand_tail_prefix @ copy_var_to_operand_tail_v_str)
      ::= A (V (snd'_prefix @ snd'_p_str));;
    (copy_var_to_operand_tail_prefix @ copy_var_to_operand_tail_ret_str)
      ::= A (N 0);;
    invoke_subprogram copy_var_to_operand_tail_prefix copy_var_to_operand_tail_IMP_Minus;;

    (copy_atom_to_operand_nat_ret_str) ::=
      A (V (copy_var_to_operand_tail_prefix @ copy_var_to_operand_tail_ret_str))
    )
  "

lemma copy_atom_to_operand_nat_IMP_Minus_correct_function:
  "(invoke_subprogram p copy_atom_to_operand_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_atom_to_operand_nat_ret_str)
      = copy_atom_to_operand_nat_ret
          (copy_atom_to_operand_nat_imp (copy_atom_to_operand_nat_imp_to_HOL_state p s))"
  apply (simp only: copy_atom_to_operand_nat_imp.simps)
  apply (simp only: copy_atom_to_operand_nat_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule fst'_IMP_Minus_correct[where vars = copy_atom_to_operand_nat_IMP_vars])
  subgoal premises p using p(4) by fastforce
  apply (erule If_E)
    subgoal 
      apply (erule Seq_E)+
      apply (erule snd'_IMP_Minus_correct[where vars = copy_atom_to_operand_nat_IMP_vars])
      subgoal premises p using p (14) by fastforce
      apply (erule copy_const_to_operand_tail_IMP_Minus_correct[where vars = copy_atom_to_operand_nat_IMP_vars])
      subgoal premises p using p (16) by fastforce
      apply (force simp: copy_atom_to_operand_nat_state_translators Let_def)
    done 

    subgoal 
      apply (erule Seq_E)+
      apply (erule snd'_IMP_Minus_correct[where vars = copy_atom_to_operand_nat_IMP_vars])
      subgoal premises p using p (14) by fastforce
      apply (erule copy_var_to_operand_tail_IMP_Minus_correct[where vars = copy_atom_to_operand_nat_IMP_vars])
      subgoal premises p using p (16) by fastforce
      apply (force simp: copy_atom_to_operand_nat_state_translators Let_def)
    done 
  done 

lemma copy_atom_to_operand_nat_IMP_Minus_correct_time:
  "(invoke_subprogram p copy_atom_to_operand_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
    t = (copy_atom_to_operand_nat_imp_time 0 (copy_atom_to_operand_nat_imp_to_HOL_state p s))"
  apply (simp only: copy_atom_to_operand_nat_imp_time.simps)
  apply (simp only: copy_atom_to_operand_nat_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule fst'_IMP_Minus_correct[where vars = copy_atom_to_operand_nat_IMP_vars])
  subgoal premises p using p(7) by fastforce
  apply (erule If_tE)
    subgoal 
      apply (erule Seq_tE)+
      apply (erule snd'_IMP_Minus_correct[where vars = copy_atom_to_operand_nat_IMP_vars])
      subgoal premises p using p (25) by fastforce
      apply (erule copy_const_to_operand_tail_IMP_Minus_correct[where vars = copy_atom_to_operand_nat_IMP_vars])
      subgoal premises p using p (27) by fastforce
      apply (force simp: copy_atom_to_operand_nat_state_translators Let_def)
    done 

    subgoal 
      apply (erule Seq_tE)+
      apply (erule snd'_IMP_Minus_correct[where vars = copy_atom_to_operand_nat_IMP_vars])
      subgoal premises p using p (25) by fastforce
      apply (erule copy_var_to_operand_tail_IMP_Minus_correct[where vars = copy_atom_to_operand_nat_IMP_vars])
      subgoal premises p using p (27) by fastforce
      apply (force simp: copy_atom_to_operand_nat_state_translators Let_def)
    done 
  done 

lemma copy_atom_to_operand_nat_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_atom_to_operand_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (copy_atom_to_operand_nat_imp_time 0 (copy_atom_to_operand_nat_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) copy_atom_to_operand_nat_ret_str) =
          copy_atom_to_operand_nat_ret (copy_atom_to_operand_nat_imp
                                        (copy_atom_to_operand_nat_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_atom_to_operand_nat_IMP_Minus_correct_function 
      copy_atom_to_operand_nat_IMP_Minus_correct_time
       set_mono_prefix
  by (smt (verit, ccfv_SIG) com_add_prefix_valid_subset com_only_vars)

end 