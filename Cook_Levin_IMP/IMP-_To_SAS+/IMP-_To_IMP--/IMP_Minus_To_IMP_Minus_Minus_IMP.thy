\<^marker>\<open>creator Alexander Taepper\<close>

theory IMP_Minus_To_IMP_Minus_Minus_IMP
  imports
    Primitives_IMP_Minus
    Binary_Arithmetic_IMP
    IMP_Minus_To_IMP_Minus_Minus_State_Translations_IMP
    IMP_Minus_To_IMP_Minus_Minus_nat
    IMP_Minus.Com
begin


unbundle IMP_Minus_Minus_Com.no_com_syntax

subsection \<open>Useful Definitions and Lemmas\<close>

subsection "add_result_to_stack"

subsubsection "add_result_to_stack_aux"

record add_result_to_stack_aux_state =
  add_result_to_stack_aux_c::nat 
  add_result_to_stack_aux_h::nat
  add_result_to_stack_aux_con::nat
  add_result_to_stack_aux_t::nat
  add_result_to_stack_aux_s::nat
  add_result_to_stack_aux_ret::nat

abbreviation "add_result_to_stack_aux_prefix \<equiv> ''add_result_to_stack_aux.''"
abbreviation "add_result_to_stack_aux_c_str \<equiv> ''c''"
abbreviation "add_result_to_stack_aux_h_str \<equiv> ''h''"
abbreviation "add_result_to_stack_aux_con_str \<equiv> ''con''"
abbreviation "add_result_to_stack_aux_t_str \<equiv> ''t''"
abbreviation "add_result_to_stack_aux_s_str \<equiv> ''s''"
abbreviation "add_result_to_stack_aux_ret_str \<equiv> ''ret''"

definition "add_result_to_stack_aux_imp_to_HOL_state p s \<equiv> 
  \<lparr>add_result_to_stack_aux_c = s (add_prefix p add_result_to_stack_aux_c_str),
  add_result_to_stack_aux_h = s (add_prefix p add_result_to_stack_aux_h_str),
  add_result_to_stack_aux_con = s (add_prefix p add_result_to_stack_aux_con_str),
  add_result_to_stack_aux_t = s (add_prefix p add_result_to_stack_aux_t_str),
  add_result_to_stack_aux_s = s (add_prefix p add_result_to_stack_aux_s_str),
  add_result_to_stack_aux_ret = s (add_prefix p add_result_to_stack_aux_ret_str)\<rparr>"

abbreviation "add_result_to_stack_aux_IMP_vars \<equiv> 
  {add_result_to_stack_aux_c_str, add_result_to_stack_aux_h_str, 
  add_result_to_stack_aux_con_str, add_result_to_stack_aux_t_str, 
  add_result_to_stack_aux_s_str, add_result_to_stack_aux_ret_str}"

lemmas add_result_to_stack_aux_state_translators = 
  add_result_to_stack_aux_imp_to_HOL_state_def
  nth_nat_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def

paragraph "con_eq_three"

definition "add_result_to_stack_aux_con_eq_three_imp s = 
  (let 
    cons_h' = add_result_to_stack_aux_c s;
    cons_t' = 0;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    nth_nat_n' = 3;
    nth_nat_x' = add_result_to_stack_aux_h s;
    nth_nat_ret' = 0;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    nth_nat_n' = 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    nth_nat_ret' = 0;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    nth_nat_n' = 1;
    nth_nat_x' = add_result_to_stack_aux_h s;
    nth_nat_ret' = 0;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    cons_h' = 4;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    cons_h' = cons_ret cons_ret_state;
    cons_t' = add_result_to_stack_aux_t s;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    add_result_to_stack_aux_ret' = cons_ret cons_ret_state;
    ret = \<lparr>add_result_to_stack_aux_c = add_result_to_stack_aux_c s,
          add_result_to_stack_aux_h = add_result_to_stack_aux_h s,
          add_result_to_stack_aux_con = add_result_to_stack_aux_con s,
          add_result_to_stack_aux_t = add_result_to_stack_aux_t s,
          add_result_to_stack_aux_s = add_result_to_stack_aux_s s,
          add_result_to_stack_aux_ret = add_result_to_stack_aux_ret'\<rparr>
  in 
   ret)"

lemma add_result_to_stack_aux_con_eq_three_imp_correct[let_function_correctness]:
  "add_result_to_stack_aux_ret (add_result_to_stack_aux_con_eq_three_imp s) = 
    ((4## (nth_nat (Suc 0) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc 0)) (add_result_to_stack_aux_h s)) 
      ## (nth_nat (Suc (Suc (Suc 0))) (add_result_to_stack_aux_h s)) 
      ## (add_result_to_stack_aux_c s) ## 0) ## (add_result_to_stack_aux_t s))"
  apply (subst add_result_to_stack_aux_con_eq_three_imp_def)
  apply (auto simp add: cons_imp_correct nth_nat_imp_correct eval_nat_numeral Let_def)
  done 

definition "add_result_to_stack_aux_con_eq_three_imp_time t s = 
  (let 
    cons_h' = add_result_to_stack_aux_c s;
    t = t + 2;
    cons_t' = 0;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    nth_nat_n' = 3;
    t = t + 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    t = t + 2;
    nth_nat_ret' = 0;
    t = t + 2;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;
    t = t + nth_nat_imp_time 0 nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    nth_nat_n' = 2;
    t = t + 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    t = t + 2;
    nth_nat_ret' = 0;
    t = t + 2;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;
    t = t + nth_nat_imp_time 0 nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    nth_nat_n' = 1;
    t = t + 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    t = t + 2;
    nth_nat_ret' = 0;
    t = t + 2;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;
    t = t + nth_nat_imp_time 0 nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    cons_h' = 4;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    cons_h' = cons_ret cons_ret_state;
    t = t + 2;
    cons_t' = add_result_to_stack_aux_t s;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    add_result_to_stack_aux_ret' = cons_ret cons_ret_state;
    t = t + 2;
    ret = \<lparr>add_result_to_stack_aux_c = add_result_to_stack_aux_c s,
          add_result_to_stack_aux_h = add_result_to_stack_aux_h s,
          add_result_to_stack_aux_con = add_result_to_stack_aux_con s,
          add_result_to_stack_aux_t = add_result_to_stack_aux_t s,
          add_result_to_stack_aux_s = add_result_to_stack_aux_s s,
          add_result_to_stack_aux_ret = add_result_to_stack_aux_ret'\<rparr>
  in 
   t)"

definition "add_result_to_stack_aux_con_eq_three_IMP_Minus \<equiv> 
  (cons_prefix @ cons_h_str) ::= A (V add_result_to_stack_aux_c_str);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
    
  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 3);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V add_result_to_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 2);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V add_result_to_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 1);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V add_result_to_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (N 4);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V add_result_to_stack_aux_t_str);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  add_result_to_stack_aux_ret_str ::= A (V (cons_prefix @ cons_ret_str))"

lemma add_result_to_stack_aux_con_eq_three_IMP_Minus_correct_function:
  "(invoke_subprogram p add_result_to_stack_aux_con_eq_three_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p add_result_to_stack_aux_ret_str)
      = add_result_to_stack_aux_ret
          (add_result_to_stack_aux_con_eq_three_imp (add_result_to_stack_aux_imp_to_HOL_state p s))"
apply (subst add_result_to_stack_aux_con_eq_three_imp_def)
apply (simp only: add_result_to_stack_aux_con_eq_three_IMP_Minus_def prefix_simps)
apply (erule Seq_E)+
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(37) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(39) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(41) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(43) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(45) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(47) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(49) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(51) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(53) by fastforce 
apply (fastforce simp : add_result_to_stack_aux_state_translators Let_def)
done 

lemma add_result_to_stack_aux_con_eq_three_IMP_Minus_correct_time :
  "(invoke_subprogram p add_result_to_stack_aux_con_eq_three_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = add_result_to_stack_aux_con_eq_three_imp_time 0 (add_result_to_stack_aux_imp_to_HOL_state p s)"
apply (subst add_result_to_stack_aux_con_eq_three_imp_time_def)
apply (simp only: add_result_to_stack_aux_con_eq_three_IMP_Minus_def prefix_simps)
apply (erule Seq_tE)+
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(73) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(75) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(77) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(79) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(81) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(83) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(85) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(87) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(89) by fastforce 
apply (fastforce simp : add_result_to_stack_aux_state_translators Let_def)
done 


paragraph "con_eq_four"

definition "add_result_to_stack_aux_con_eq_four_imp s = 
  (let 
    cons_h' = add_result_to_stack_aux_c s;
    cons_t' = 0;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    nth_nat_n' = 4;
    nth_nat_x' = add_result_to_stack_aux_h s;
    nth_nat_ret' = 0;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    nth_nat_n' = 3;
    nth_nat_x' = add_result_to_stack_aux_h s;
    nth_nat_ret' = 0;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    nth_nat_n' = 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    nth_nat_ret' = 0;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    nth_nat_n' = 1;
    nth_nat_x' = add_result_to_stack_aux_h s;
    nth_nat_ret' = 0;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    cons_h' = 5;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    cons_h' = cons_ret cons_ret_state;
    cons_t' = add_result_to_stack_aux_t s;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    add_result_to_stack_aux_ret' = cons_ret cons_ret_state;
    ret = \<lparr>add_result_to_stack_aux_c = add_result_to_stack_aux_c s,
          add_result_to_stack_aux_h = add_result_to_stack_aux_h s,
          add_result_to_stack_aux_con = add_result_to_stack_aux_con s,
          add_result_to_stack_aux_t = add_result_to_stack_aux_t s,
          add_result_to_stack_aux_s = add_result_to_stack_aux_s s,
          add_result_to_stack_aux_ret = add_result_to_stack_aux_ret'\<rparr>
  in 
   ret)"

lemma add_result_to_stack_aux_con_eq_four_imp_correct[let_function_correctness]:
  "add_result_to_stack_aux_ret (add_result_to_stack_aux_con_eq_four_imp s) = 
    ((5## (nth_nat (Suc 0) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc 0)) (add_result_to_stack_aux_h s)) 
      ## (nth_nat (Suc (Suc (Suc 0))) (add_result_to_stack_aux_h s)) 
      ## (nth_nat (Suc (Suc (Suc (Suc 0)))) (add_result_to_stack_aux_h s)) 
      ## (add_result_to_stack_aux_c s) ## 0) ## (add_result_to_stack_aux_t s))"
  apply (subst add_result_to_stack_aux_con_eq_four_imp_def)
  apply (auto simp add: cons_imp_correct nth_nat_imp_correct eval_nat_numeral Let_def)
  done 

definition "add_result_to_stack_aux_con_eq_four_imp_time t s = 
  (let 
    cons_h' = add_result_to_stack_aux_c s;
    t = t + 2;
    cons_t' = 0;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    nth_nat_n' = 4;
    t = t + 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    t = t + 2;
    nth_nat_ret' = 0;
    t = t + 2;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;
    t = t + nth_nat_imp_time 0 nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    nth_nat_n' = 3;
    t = t + 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    t = t + 2;
    nth_nat_ret' = 0;
    t = t + 2;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;
    t = t + nth_nat_imp_time 0 nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    nth_nat_n' = 2;
    t = t + 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    t = t + 2;
    nth_nat_ret' = 0;
    t = t + 2;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;
    t = t + nth_nat_imp_time 0 nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    nth_nat_n' = 1;
    t = t + 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    t = t + 2;
    nth_nat_ret' = 0;
    t = t + 2;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;
    t = t + nth_nat_imp_time 0 nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    cons_h' = 5;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    cons_h' = cons_ret cons_ret_state;
    t = t + 2;
    cons_t' = add_result_to_stack_aux_t s;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    add_result_to_stack_aux_ret' = cons_ret cons_ret_state;
    t = t + 2;
    ret = \<lparr>add_result_to_stack_aux_c = add_result_to_stack_aux_c s,
          add_result_to_stack_aux_h = add_result_to_stack_aux_h s,
          add_result_to_stack_aux_con = add_result_to_stack_aux_con s,
          add_result_to_stack_aux_t = add_result_to_stack_aux_t s,
          add_result_to_stack_aux_s = add_result_to_stack_aux_s s,
          add_result_to_stack_aux_ret = add_result_to_stack_aux_ret'\<rparr>
  in 
   t)"

definition "add_result_to_stack_aux_con_eq_four_IMP_Minus \<equiv> 
  (cons_prefix @ cons_h_str) ::= A (V add_result_to_stack_aux_c_str);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 4);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V add_result_to_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
    
  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 3);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V add_result_to_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 2);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V add_result_to_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 1);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V add_result_to_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (N 5);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V add_result_to_stack_aux_t_str);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  add_result_to_stack_aux_ret_str ::= A (V (cons_prefix @ cons_ret_str))"

lemma add_result_to_stack_aux_con_eq_four_IMP_Minus_correct_function:
  "(invoke_subprogram p add_result_to_stack_aux_con_eq_four_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p add_result_to_stack_aux_ret_str)
      = add_result_to_stack_aux_ret
          (add_result_to_stack_aux_con_eq_four_imp (add_result_to_stack_aux_imp_to_HOL_state p s))"
apply (subst add_result_to_stack_aux_con_eq_four_imp_def)
apply (simp only: add_result_to_stack_aux_con_eq_four_IMP_Minus_def prefix_simps)
apply (erule Seq_E)+
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(45) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(47) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(49) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(51) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(53) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(55) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(57) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(59) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(61) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(63) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(65) by fastforce 
apply (fastforce simp : add_result_to_stack_aux_state_translators Let_def)
done 

lemma add_result_to_stack_aux_con_eq_four_IMP_Minus_correct_time :
  "(invoke_subprogram p add_result_to_stack_aux_con_eq_four_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = add_result_to_stack_aux_con_eq_four_imp_time 0 (add_result_to_stack_aux_imp_to_HOL_state p s)"
apply (subst add_result_to_stack_aux_con_eq_four_imp_time_def)
apply (simp only: add_result_to_stack_aux_con_eq_four_IMP_Minus_def prefix_simps)
apply (erule Seq_tE)+
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(89) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(91) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(93) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(95) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(97) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(99) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(101) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(103) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(105) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(107) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(109) by fastforce 
apply (fastforce simp : add_result_to_stack_aux_state_translators Let_def)
done 

paragraph "con_eq_six"

definition "add_result_to_stack_aux_con_eq_six_imp s = 
  (let 
    cons_h' = add_result_to_stack_aux_c s;
    cons_t' = 0;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    nth_nat_n' = 4;
    nth_nat_x' = add_result_to_stack_aux_h s;
    nth_nat_ret' = 0;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    nth_nat_n' = 3;
    nth_nat_x' = add_result_to_stack_aux_h s;
    nth_nat_ret' = 0;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    nth_nat_n' = 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    nth_nat_ret' = 0;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    nth_nat_n' = 1;
    nth_nat_x' = add_result_to_stack_aux_h s;
    nth_nat_ret' = 0;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    cons_h' = 7;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    cons_h' = cons_ret cons_ret_state;
    cons_t' = add_result_to_stack_aux_t s;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    add_result_to_stack_aux_ret' = cons_ret cons_ret_state;
    ret = \<lparr>add_result_to_stack_aux_c = add_result_to_stack_aux_c s,
          add_result_to_stack_aux_h = add_result_to_stack_aux_h s,
          add_result_to_stack_aux_con = add_result_to_stack_aux_con s,
          add_result_to_stack_aux_t = add_result_to_stack_aux_t s,
          add_result_to_stack_aux_s = add_result_to_stack_aux_s s,
          add_result_to_stack_aux_ret = add_result_to_stack_aux_ret'\<rparr>
  in 
   ret)"

lemma add_result_to_stack_aux_con_eq_six_imp_correct[let_function_correctness]:
  "add_result_to_stack_aux_ret (add_result_to_stack_aux_con_eq_six_imp s) = 
    ((7## (nth_nat (Suc 0) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc 0)) (add_result_to_stack_aux_h s)) 
      ## (nth_nat (Suc (Suc (Suc 0))) (add_result_to_stack_aux_h s)) 
      ## (nth_nat (Suc (Suc (Suc (Suc 0)))) (add_result_to_stack_aux_h s)) 
      ## (add_result_to_stack_aux_c s) ## 0) ## (add_result_to_stack_aux_t s))"
  apply (subst add_result_to_stack_aux_con_eq_six_imp_def)
  apply (auto simp add: cons_imp_correct nth_nat_imp_correct eval_nat_numeral Let_def)
  done 

definition "add_result_to_stack_aux_con_eq_six_imp_time t s = 
  (let 
    cons_h' = add_result_to_stack_aux_c s;
    t = t + 2;
    cons_t' = 0;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    nth_nat_n' = 4;
    t = t + 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    t = t + 2;
    nth_nat_ret' = 0;
    t = t + 2;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;
    t = t + nth_nat_imp_time 0 nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    nth_nat_n' = 3;
    t = t + 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    t = t + 2;
    nth_nat_ret' = 0;
    t = t + 2;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;
    t = t + nth_nat_imp_time 0 nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    nth_nat_n' = 2;
    t = t + 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    t = t + 2;
    nth_nat_ret' = 0;
    t = t + 2;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;
    t = t + nth_nat_imp_time 0 nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    nth_nat_n' = 1;
    t = t + 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    t = t + 2;
    nth_nat_ret' = 0;
    t = t + 2;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;
    t = t + nth_nat_imp_time 0 nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    cons_h' = 7;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    cons_h' = cons_ret cons_ret_state;
    t = t + 2;
    cons_t' = add_result_to_stack_aux_t s;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    add_result_to_stack_aux_ret' = cons_ret cons_ret_state;
    t = t + 2;
    ret = \<lparr>add_result_to_stack_aux_c = add_result_to_stack_aux_c s,
          add_result_to_stack_aux_h = add_result_to_stack_aux_h s,
          add_result_to_stack_aux_con = add_result_to_stack_aux_con s,
          add_result_to_stack_aux_t = add_result_to_stack_aux_t s,
          add_result_to_stack_aux_s = add_result_to_stack_aux_s s,
          add_result_to_stack_aux_ret = add_result_to_stack_aux_ret'\<rparr>
  in 
   t)"

definition "add_result_to_stack_aux_con_eq_six_IMP_Minus \<equiv> 
  (cons_prefix @ cons_h_str) ::= A (V add_result_to_stack_aux_c_str);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 4);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V add_result_to_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
    
  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 3);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V add_result_to_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 2);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V add_result_to_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 1);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V add_result_to_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (N 7);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V add_result_to_stack_aux_t_str);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  add_result_to_stack_aux_ret_str ::= A (V (cons_prefix @ cons_ret_str))"

lemma add_result_to_stack_aux_con_eq_six_IMP_Minus_correct_function:
  "(invoke_subprogram p add_result_to_stack_aux_con_eq_six_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p add_result_to_stack_aux_ret_str)
      = add_result_to_stack_aux_ret
          (add_result_to_stack_aux_con_eq_six_imp (add_result_to_stack_aux_imp_to_HOL_state p s))"
apply (subst add_result_to_stack_aux_con_eq_six_imp_def)
apply (simp only: add_result_to_stack_aux_con_eq_six_IMP_Minus_def prefix_simps)
apply (erule Seq_E)+
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(45) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(47) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(49) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(51) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(53) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(55) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(57) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(59) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(61) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(63) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(65) by fastforce 
apply (fastforce simp : add_result_to_stack_aux_state_translators Let_def)
done 

lemma add_result_to_stack_aux_con_eq_six_IMP_Minus_correct_time :
  "(invoke_subprogram p add_result_to_stack_aux_con_eq_six_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = add_result_to_stack_aux_con_eq_six_imp_time 0 (add_result_to_stack_aux_imp_to_HOL_state p s)"
apply (subst add_result_to_stack_aux_con_eq_six_imp_time_def)
apply (simp only: add_result_to_stack_aux_con_eq_six_IMP_Minus_def prefix_simps)
apply (erule Seq_tE)+
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(89) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(91) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(93) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(95) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(97) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(99) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(101) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(103) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(105) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(107) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(109) by fastforce 
apply (fastforce simp : add_result_to_stack_aux_state_translators Let_def)
done

paragraph "con_eq_nine"

definition "add_result_to_stack_aux_con_eq_nine_imp s = 
  (let 
    cons_h' = add_result_to_stack_aux_c s;
    cons_t' = 0;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    nth_nat_n' = 3;
    nth_nat_x' = add_result_to_stack_aux_h s;
    nth_nat_ret' = 0;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    nth_nat_n' = 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    nth_nat_ret' = 0;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    nth_nat_n' = 1;
    nth_nat_x' = add_result_to_stack_aux_h s;
    nth_nat_ret' = 0;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    cons_h' = 10;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    cons_h' = cons_ret cons_ret_state;
    cons_t' = add_result_to_stack_aux_t s;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    add_result_to_stack_aux_ret' = cons_ret cons_ret_state;
    ret = \<lparr>add_result_to_stack_aux_c = add_result_to_stack_aux_c s,
          add_result_to_stack_aux_h = add_result_to_stack_aux_h s,
          add_result_to_stack_aux_con = add_result_to_stack_aux_con s,
          add_result_to_stack_aux_t = add_result_to_stack_aux_t s,
          add_result_to_stack_aux_s = add_result_to_stack_aux_s s,
          add_result_to_stack_aux_ret = add_result_to_stack_aux_ret'\<rparr>
  in 
   ret)"

lemma add_result_to_stack_aux_con_eq_nine_imp_correct[let_function_correctness]:
  "add_result_to_stack_aux_ret (add_result_to_stack_aux_con_eq_nine_imp s) = 
    ((10## (nth_nat (Suc 0) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc 0)) (add_result_to_stack_aux_h s)) 
      ## (nth_nat (Suc (Suc (Suc 0))) (add_result_to_stack_aux_h s)) 
      ## (add_result_to_stack_aux_c s) ## 0) ## (add_result_to_stack_aux_t s))"
  apply (subst add_result_to_stack_aux_con_eq_nine_imp_def)
  apply (auto simp add: cons_imp_correct nth_nat_imp_correct eval_nat_numeral Let_def)
  done 

definition "add_result_to_stack_aux_con_eq_nine_imp_time t s = 
  (let 
    cons_h' = add_result_to_stack_aux_c s;
    t = t + 2;
    cons_t' = 0;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    nth_nat_n' = 3;
    t = t + 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    t = t + 2;
    nth_nat_ret' = 0;
    t = t + 2;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;
    t = t + nth_nat_imp_time 0 nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    nth_nat_n' = 2;
    t = t + 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    t = t + 2;
    nth_nat_ret' = 0;
    t = t + 2;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;
    t = t + nth_nat_imp_time 0 nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    nth_nat_n' = 1;
    t = t + 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    t = t + 2;
    nth_nat_ret' = 0;
    t = t + 2;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;
    t = t + nth_nat_imp_time 0 nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    cons_h' = 10;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    cons_h' = cons_ret cons_ret_state;
    t = t + 2;
    cons_t' = add_result_to_stack_aux_t s;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    add_result_to_stack_aux_ret' = cons_ret cons_ret_state;
    t = t + 2;
    ret = \<lparr>add_result_to_stack_aux_c = add_result_to_stack_aux_c s,
          add_result_to_stack_aux_h = add_result_to_stack_aux_h s,
          add_result_to_stack_aux_con = add_result_to_stack_aux_con s,
          add_result_to_stack_aux_t = add_result_to_stack_aux_t s,
          add_result_to_stack_aux_s = add_result_to_stack_aux_s s,
          add_result_to_stack_aux_ret = add_result_to_stack_aux_ret'\<rparr>
  in 
   t)"

definition "add_result_to_stack_aux_con_eq_nine_IMP_Minus \<equiv> 
  (cons_prefix @ cons_h_str) ::= A (V add_result_to_stack_aux_c_str);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
    
  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 3);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V add_result_to_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 2);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V add_result_to_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 1);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V add_result_to_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (N 10);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V add_result_to_stack_aux_t_str);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  add_result_to_stack_aux_ret_str ::= A (V (cons_prefix @ cons_ret_str))"

lemma add_result_to_stack_aux_con_eq_nine_IMP_Minus_correct_function:
  "(invoke_subprogram p add_result_to_stack_aux_con_eq_nine_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p add_result_to_stack_aux_ret_str)
      = add_result_to_stack_aux_ret
          (add_result_to_stack_aux_con_eq_nine_imp (add_result_to_stack_aux_imp_to_HOL_state p s))"
apply (subst add_result_to_stack_aux_con_eq_nine_imp_def)
apply (simp only: add_result_to_stack_aux_con_eq_nine_IMP_Minus_def prefix_simps)
apply (erule Seq_E)+
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(37) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(39) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(41) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(43) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(45) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(47) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(49) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(51) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(53) by fastforce 
apply (fastforce simp : add_result_to_stack_aux_state_translators Let_def)
done 

lemma add_result_to_stack_aux_con_eq_nine_IMP_Minus_correct_time :
  "(invoke_subprogram p add_result_to_stack_aux_con_eq_nine_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = add_result_to_stack_aux_con_eq_nine_imp_time 0 (add_result_to_stack_aux_imp_to_HOL_state p s)"
apply (subst add_result_to_stack_aux_con_eq_nine_imp_time_def)
apply (simp only: add_result_to_stack_aux_con_eq_nine_IMP_Minus_def prefix_simps)
apply (erule Seq_tE)+
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(73) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(75) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(77) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(79) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(81) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(83) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(85) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(87) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(89) by fastforce 
apply (fastforce simp : add_result_to_stack_aux_state_translators Let_def)
done 

paragraph "con_eq_seven"

definition "add_result_to_stack_aux_con_eq_seven_imp s = 
  (let 
    cons_h' = add_result_to_stack_aux_c s;
    cons_t' = 0;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    nth_nat_n' = 5;
    nth_nat_x' = add_result_to_stack_aux_h s;
    nth_nat_ret' = 0;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    nth_nat_n' = 4;
    nth_nat_x' = add_result_to_stack_aux_h s;
    nth_nat_ret' = 0;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    nth_nat_n' = 3;
    nth_nat_x' = add_result_to_stack_aux_h s;
    nth_nat_ret' = 0;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    nth_nat_n' = 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    nth_nat_ret' = 0;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    nth_nat_n' = 1;
    nth_nat_x' = add_result_to_stack_aux_h s;
    nth_nat_ret' = 0;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    cons_h' = 8;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    cons_h' = cons_ret cons_ret_state;
    cons_t' = add_result_to_stack_aux_t s;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    add_result_to_stack_aux_ret' = cons_ret cons_ret_state;
    ret = \<lparr>add_result_to_stack_aux_c = add_result_to_stack_aux_c s,
          add_result_to_stack_aux_h = add_result_to_stack_aux_h s,
          add_result_to_stack_aux_con = add_result_to_stack_aux_con s,
          add_result_to_stack_aux_t = add_result_to_stack_aux_t s,
          add_result_to_stack_aux_s = add_result_to_stack_aux_s s,
          add_result_to_stack_aux_ret = add_result_to_stack_aux_ret'\<rparr>
  in 
   ret)"

lemma add_result_to_stack_aux_con_eq_seven_imp_correct[let_function_correctness]:
  "add_result_to_stack_aux_ret (add_result_to_stack_aux_con_eq_seven_imp s) = 
    ((8## (nth_nat (Suc 0) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc 0)) (add_result_to_stack_aux_h s)) 
      ## (nth_nat (Suc (Suc (Suc 0))) (add_result_to_stack_aux_h s)) 
      ## (nth_nat (Suc (Suc (Suc (Suc 0)))) (add_result_to_stack_aux_h s))
      ## (nth_nat (Suc (Suc (Suc (Suc (Suc 0))))) (add_result_to_stack_aux_h s)) 
      ## (add_result_to_stack_aux_c s) ## 0) ## (add_result_to_stack_aux_t s))"
  apply (subst add_result_to_stack_aux_con_eq_seven_imp_def)
  apply (auto simp add: cons_imp_correct nth_nat_imp_correct eval_nat_numeral Let_def)
  done 

definition "add_result_to_stack_aux_con_eq_seven_imp_time t s = 
  (let 
    cons_h' = add_result_to_stack_aux_c s;
    t = t + 2;
    cons_t' = 0;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    nth_nat_n' = 5;
    t = t + 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    t = t + 2;
    nth_nat_ret' = 0;
    t = t + 2;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;
    t = t + nth_nat_imp_time 0 nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    nth_nat_n' = 4;
    t = t + 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    t = t + 2;
    nth_nat_ret' = 0;
    t = t + 2;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;
    t = t + nth_nat_imp_time 0 nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    nth_nat_n' = 3;
    t = t + 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    t = t + 2;
    nth_nat_ret' = 0;
    t = t + 2;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;
    t = t + nth_nat_imp_time 0 nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    nth_nat_n' = 2;
    t = t + 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    t = t + 2;
    nth_nat_ret' = 0;
    t = t + 2;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;
    t = t + nth_nat_imp_time 0 nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    nth_nat_n' = 1;
    t = t + 2;
    nth_nat_x' = add_result_to_stack_aux_h s;
    t = t + 2;
    nth_nat_ret' = 0;
    t = t + 2;
    nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;
    t = t + nth_nat_imp_time 0 nth_nat_state;

    cons_h' = nth_nat_ret nth_nat_ret_state;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    cons_h' = 8;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    cons_h' = cons_ret cons_ret_state;
    t = t + 2;
    cons_t' = add_result_to_stack_aux_t s;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    add_result_to_stack_aux_ret' = cons_ret cons_ret_state;
    t = t + 2;
    ret = \<lparr>add_result_to_stack_aux_c = add_result_to_stack_aux_c s,
          add_result_to_stack_aux_h = add_result_to_stack_aux_h s,
          add_result_to_stack_aux_con = add_result_to_stack_aux_con s,
          add_result_to_stack_aux_t = add_result_to_stack_aux_t s,
          add_result_to_stack_aux_s = add_result_to_stack_aux_s s,
          add_result_to_stack_aux_ret = add_result_to_stack_aux_ret'\<rparr>
  in 
   t)"

definition "add_result_to_stack_aux_con_eq_seven_IMP_Minus \<equiv> 
  (cons_prefix @ cons_h_str) ::= A (V add_result_to_stack_aux_c_str);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 5);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V add_result_to_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 4);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V add_result_to_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
    
  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 3);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V add_result_to_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 2);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V add_result_to_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 1);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V add_result_to_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (N 8);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V add_result_to_stack_aux_t_str);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  add_result_to_stack_aux_ret_str ::= A (V (cons_prefix @ cons_ret_str))"

lemma add_result_to_stack_aux_con_eq_seven_IMP_Minus_correct_function:
  "(invoke_subprogram p add_result_to_stack_aux_con_eq_seven_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p add_result_to_stack_aux_ret_str)
      = add_result_to_stack_aux_ret
          (add_result_to_stack_aux_con_eq_seven_imp (add_result_to_stack_aux_imp_to_HOL_state p s))"
apply (subst add_result_to_stack_aux_con_eq_seven_imp_def)
apply (simp only: add_result_to_stack_aux_con_eq_seven_IMP_Minus_def prefix_simps)
apply (erule Seq_E)+
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(53) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(55) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(57) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(59) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(61) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(63) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(65) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(67) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(69) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(71) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(73) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(75) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(77) by fastforce 
apply (fastforce simp : add_result_to_stack_aux_state_translators Let_def)
done 

lemma add_result_to_stack_aux_con_eq_seven_IMP_Minus_correct_time :
  "(invoke_subprogram p add_result_to_stack_aux_con_eq_seven_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = add_result_to_stack_aux_con_eq_seven_imp_time 0 (add_result_to_stack_aux_imp_to_HOL_state p s)"
apply (subst add_result_to_stack_aux_con_eq_seven_imp_time_def)
apply (simp only: add_result_to_stack_aux_con_eq_seven_IMP_Minus_def prefix_simps)
apply (erule Seq_tE)+
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(105) by fastforce
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(107) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(109) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(111) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(113) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(115) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(117) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(119) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(121) by fastforce 
apply (erule nth_nat_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
subgoal premises p using p(123) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(125) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(127) by fastforce 
apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_aux_IMP_vars])
subgoal premises p using p(129) by fastforce 
apply (fastforce simp : add_result_to_stack_aux_state_translators Let_def)
done

paragraph separations_of_nested_ifs

abbreviation "add_result_to_stack_aux_cond_str \<equiv> ''cond''"

definition "add_result_to_stack_aux_sub_branch_aux1 s \<equiv>
  (let 
  NOTEQUAL_neq_zero_a' = add_result_to_stack_aux_con s;
  NOTEQUAL_neq_zero_b' = 9;
  NOTEQUAL_neq_zero_ret' = 0;
  NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                            NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                            NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
  NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
  add_result_to_stack_aux_cond = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state)
  in 
   (if add_result_to_stack_aux_cond \<noteq> 0
     then (let 
         add_result_to_stack_aux_ret' =  add_result_to_stack_aux_s s;
         ret = \<lparr>add_result_to_stack_aux_c = add_result_to_stack_aux_c s,
               add_result_to_stack_aux_h = add_result_to_stack_aux_h s,
               add_result_to_stack_aux_con = add_result_to_stack_aux_con s,
               add_result_to_stack_aux_t = add_result_to_stack_aux_t s,
               add_result_to_stack_aux_s = add_result_to_stack_aux_s s,
               add_result_to_stack_aux_ret = add_result_to_stack_aux_ret'\<rparr>
        in 
         ret)
     else add_result_to_stack_aux_con_eq_nine_imp s
       ))"

lemma add_result_to_stack_aux_sub_branch_aux1_imp_correct:
  "add_result_to_stack_aux_ret (add_result_to_stack_aux_sub_branch_aux1 s) = 
    (if (add_result_to_stack_aux_con s)=9 
     then ((10## (nth_nat (Suc 0) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc 0)) (add_result_to_stack_aux_h s)) 
      ## (nth_nat (Suc (Suc (Suc 0))) (add_result_to_stack_aux_h s)) 
      ## (add_result_to_stack_aux_c s) ## 0) ## (add_result_to_stack_aux_t s))
     else (add_result_to_stack_aux_s s))"
  apply (subst add_result_to_stack_aux_sub_branch_aux1_def)
  apply (auto simp add: NOTEQUAL_neq_zero_imp_correct add_result_to_stack_aux_con_eq_nine_imp_correct)
  done 

definition "add_result_to_stack_aux_sub_branch_aux1_time t s \<equiv>
  (let 
  NOTEQUAL_neq_zero_a' = add_result_to_stack_aux_con s;
  t = t + 2;
  NOTEQUAL_neq_zero_b' = 9;
  t = t + 2;
  NOTEQUAL_neq_zero_ret' = 0;
  t = t + 2;
  NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                            NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                            NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
  NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
  t = t + NOTEQUAL_neq_zero_imp_time 0 NOTEQUAL_neq_zero_state;
  add_result_to_stack_aux_cond = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state);
  t = t + 2
  in 
   (if add_result_to_stack_aux_cond \<noteq> 0
     then (let 
         t = t + 1;
         add_result_to_stack_aux_ret' =  add_result_to_stack_aux_s s;
         t = t + 2;
         ret = \<lparr>add_result_to_stack_aux_c = add_result_to_stack_aux_c s,
               add_result_to_stack_aux_h = add_result_to_stack_aux_h s,
               add_result_to_stack_aux_con = add_result_to_stack_aux_con s,
               add_result_to_stack_aux_t = add_result_to_stack_aux_t s,
               add_result_to_stack_aux_s = add_result_to_stack_aux_s s,
               add_result_to_stack_aux_ret = add_result_to_stack_aux_ret'\<rparr>
        in 
         t)
     else (let 
            t = t + 1;
            t = t + add_result_to_stack_aux_con_eq_nine_imp_time 0 s
           in 
            t)
       ))"

definition "add_result_to_stack_aux_sub_branch_aux1_IMP_Minus \<equiv> 
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_a_str) ::= A (V add_result_to_stack_aux_con_str);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_b_str) ::= A (N 9);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str) ::= A (N 0);;
  invoke_subprogram NOTEQUAL_neq_zero_prefix NOTEQUAL_neq_zero_IMP_Minus;;
  add_result_to_stack_aux_cond_str ::= A (V (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str));;
  (IF add_result_to_stack_aux_cond_str\<noteq>0
   THEN add_result_to_stack_aux_ret_str ::= A (V add_result_to_stack_aux_s_str)
   ELSE add_result_to_stack_aux_con_eq_nine_IMP_Minus)
  "

lemma add_result_to_stack_aux_sub_branch_aux1_IMP_Minus_correct_function:
  "(invoke_subprogram p add_result_to_stack_aux_sub_branch_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p add_result_to_stack_aux_ret_str)
      = add_result_to_stack_aux_ret
          (add_result_to_stack_aux_sub_branch_aux1 (add_result_to_stack_aux_imp_to_HOL_state p s))"
  apply (subst add_result_to_stack_aux_sub_branch_aux1_def)
  apply (simp only: add_result_to_stack_aux_sub_branch_aux1_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars"])
  subgoal premises p using p(6) by fastforce
  apply (erule If_E)
    subgoal
      apply (fastforce simp: add_result_to_stack_aux_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def)
    done 
    subgoal
     apply (fastforce dest!: add_result_to_stack_aux_con_eq_nine_IMP_Minus_correct_function 
      simp: add_result_to_stack_aux_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def Let_def)
    done
  done

lemma add_result_to_stack_aux_sub_branch_aux1_IMP_Minus_correct_time:
  "(invoke_subprogram p add_result_to_stack_aux_sub_branch_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (add_result_to_stack_aux_sub_branch_aux1_time 0 (add_result_to_stack_aux_imp_to_HOL_state p s))"
  apply (subst add_result_to_stack_aux_sub_branch_aux1_time_def)
  apply (simp only: add_result_to_stack_aux_sub_branch_aux1_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars"])
  subgoal premises p using p(11) by fastforce
  apply (erule If_tE)
    subgoal
      apply (fastforce simp: add_result_to_stack_aux_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def)
    done 
    subgoal
     apply (fastforce dest!: add_result_to_stack_aux_con_eq_nine_IMP_Minus_correct_time
      simp: add_result_to_stack_aux_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def Let_def)
    done
  done

definition "add_result_to_stack_aux_sub_branch_aux2 s \<equiv>
  (let 
  NOTEQUAL_neq_zero_a' = add_result_to_stack_aux_con s;
  NOTEQUAL_neq_zero_b' = 7;
  NOTEQUAL_neq_zero_ret' = 0;
  NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                            NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                            NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
  NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
  add_result_to_stack_aux_cond = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state)
  in 
   (if add_result_to_stack_aux_cond \<noteq> 0
     then add_result_to_stack_aux_sub_branch_aux1 s
     else add_result_to_stack_aux_con_eq_seven_imp s
       ))"

lemma add_result_to_stack_aux_sub_branch_aux2_imp_correct:
  "add_result_to_stack_aux_ret (add_result_to_stack_aux_sub_branch_aux2 s) = 
    (if (add_result_to_stack_aux_con s)=7 
     then ( ((8## (nth_nat (Suc 0) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc 0)) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc (Suc 0))) (add_result_to_stack_aux_h s))  
     ## (nth_nat (Suc (Suc (Suc ( Suc 0)))) (add_result_to_stack_aux_h s))  ## (nth_nat (Suc (Suc (Suc ( Suc (Suc 0))))) (add_result_to_stack_aux_h s)) ## (add_result_to_stack_aux_c s) ## 0) 
     ## (add_result_to_stack_aux_t s)))
     else (if (add_result_to_stack_aux_con s)=9 
     then ((10## (nth_nat (Suc 0) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc 0)) (add_result_to_stack_aux_h s)) 
      ## (nth_nat (Suc (Suc (Suc 0))) (add_result_to_stack_aux_h s)) 
      ## (add_result_to_stack_aux_c s) ## 0) ## (add_result_to_stack_aux_t s))
     else (add_result_to_stack_aux_s s)))"
  apply (subst add_result_to_stack_aux_sub_branch_aux2_def)
  apply (auto simp add: NOTEQUAL_neq_zero_imp_correct add_result_to_stack_aux_con_eq_seven_imp_correct
  add_result_to_stack_aux_sub_branch_aux1_imp_correct)
  done 

definition "add_result_to_stack_aux_sub_branch_aux2_time t s \<equiv>
  (let 
  NOTEQUAL_neq_zero_a' = add_result_to_stack_aux_con s;
  t = t + 2;
  NOTEQUAL_neq_zero_b' = 7;
  t = t + 2;
  NOTEQUAL_neq_zero_ret' = 0;
  t = t + 2;
  NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                            NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                            NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
  NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
  t = t + NOTEQUAL_neq_zero_imp_time 0 NOTEQUAL_neq_zero_state;
  add_result_to_stack_aux_cond = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state);
  t = t + 2
  in 
   (if add_result_to_stack_aux_cond \<noteq> 0
     then (let 
         t = t + 1;
         t = t + add_result_to_stack_aux_sub_branch_aux1_time 0 s
        in 
         t)
     else (let 
            t = t + 1;
            t = t + add_result_to_stack_aux_con_eq_seven_imp_time 0 s
           in 
            t)
       ))"

definition "add_result_to_stack_aux_sub_branch_aux2_IMP_Minus \<equiv> 
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_a_str) ::= A (V add_result_to_stack_aux_con_str);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_b_str) ::= A (N 7);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str) ::= A (N 0);;
  invoke_subprogram NOTEQUAL_neq_zero_prefix NOTEQUAL_neq_zero_IMP_Minus;;
  add_result_to_stack_aux_cond_str ::= A (V (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str));;
  (IF add_result_to_stack_aux_cond_str\<noteq>0
   THEN add_result_to_stack_aux_sub_branch_aux1_IMP_Minus
   ELSE add_result_to_stack_aux_con_eq_seven_IMP_Minus)
  "

lemma add_result_to_stack_aux_sub_branch_aux2_IMP_Minus_correct_function:
  "(invoke_subprogram p add_result_to_stack_aux_sub_branch_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p add_result_to_stack_aux_ret_str)
      = add_result_to_stack_aux_ret
          (add_result_to_stack_aux_sub_branch_aux2 (add_result_to_stack_aux_imp_to_HOL_state p s))"
  apply (subst add_result_to_stack_aux_sub_branch_aux2_def)
  apply (simp only: add_result_to_stack_aux_sub_branch_aux2_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars"])
  subgoal premises p using p(6) by fastforce
  apply (erule If_E)
    subgoal
      apply (fastforce dest!: add_result_to_stack_aux_sub_branch_aux1_IMP_Minus_correct_function
         simp: add_result_to_stack_aux_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def)
    done 
    subgoal
     apply (fastforce dest!: add_result_to_stack_aux_con_eq_seven_IMP_Minus_correct_function 
      simp: add_result_to_stack_aux_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def Let_def)
    done
  done

lemma add_result_to_stack_aux_sub_branch_aux2_IMP_Minus_correct_time:
  "(invoke_subprogram p add_result_to_stack_aux_sub_branch_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (add_result_to_stack_aux_sub_branch_aux2_time 0 (add_result_to_stack_aux_imp_to_HOL_state p s))"
  apply (subst add_result_to_stack_aux_sub_branch_aux2_time_def)
  apply (simp only: add_result_to_stack_aux_sub_branch_aux2_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars"])
  subgoal premises p using p(11) by fastforce
  apply (erule If_tE)
    subgoal
      apply (force dest!: add_result_to_stack_aux_sub_branch_aux1_IMP_Minus_correct_time
       simp: add_result_to_stack_aux_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def)
    done 
    subgoal
     apply (force dest!: add_result_to_stack_aux_con_eq_seven_IMP_Minus_correct_time
      simp: add_result_to_stack_aux_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def Let_def)
    done
  done

definition "add_result_to_stack_aux_sub_branch_aux3 s \<equiv>
  (let 
  NOTEQUAL_neq_zero_a' = add_result_to_stack_aux_con s;
  NOTEQUAL_neq_zero_b' = 6;
  NOTEQUAL_neq_zero_ret' = 0;
  NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                            NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                            NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
  NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
  add_result_to_stack_aux_cond = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state)
  in 
   (if add_result_to_stack_aux_cond \<noteq> 0
     then add_result_to_stack_aux_sub_branch_aux2 s
     else add_result_to_stack_aux_con_eq_six_imp s
       ))"

lemma add_result_to_stack_aux_sub_branch_aux3_imp_correct:
  "add_result_to_stack_aux_ret (add_result_to_stack_aux_sub_branch_aux3 s) = 
    (if (add_result_to_stack_aux_con s)=6 
     then ((7## (nth_nat (Suc 0) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc 0)) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc (Suc 0))) (add_result_to_stack_aux_h s))  
       ## (nth_nat (Suc (Suc (Suc ( Suc 0)))) (add_result_to_stack_aux_h s)) ## (add_result_to_stack_aux_c s) ## 0) ## (add_result_to_stack_aux_t s))
     else (if (add_result_to_stack_aux_con s)=7 
     then ( ((8## (nth_nat (Suc 0) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc 0)) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc (Suc 0))) (add_result_to_stack_aux_h s))  
     ## (nth_nat (Suc (Suc (Suc ( Suc 0)))) (add_result_to_stack_aux_h s))  ## (nth_nat (Suc (Suc (Suc ( Suc (Suc 0))))) (add_result_to_stack_aux_h s)) ## (add_result_to_stack_aux_c s) ## 0) 
     ## (add_result_to_stack_aux_t s)))
     else (if (add_result_to_stack_aux_con s)=9 
     then ((10## (nth_nat (Suc 0) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc 0)) (add_result_to_stack_aux_h s)) 
      ## (nth_nat (Suc (Suc (Suc 0))) (add_result_to_stack_aux_h s)) 
      ## (add_result_to_stack_aux_c s) ## 0) ## (add_result_to_stack_aux_t s))
     else (add_result_to_stack_aux_s s))))"
  apply (subst add_result_to_stack_aux_sub_branch_aux3_def)
  apply (auto simp add: NOTEQUAL_neq_zero_imp_correct add_result_to_stack_aux_con_eq_six_imp_correct
  add_result_to_stack_aux_sub_branch_aux2_imp_correct)
  done 

definition "add_result_to_stack_aux_sub_branch_aux3_time t s \<equiv>
  (let 
  NOTEQUAL_neq_zero_a' = add_result_to_stack_aux_con s;
  t = t + 2;
  NOTEQUAL_neq_zero_b' = 6;
  t = t + 2;
  NOTEQUAL_neq_zero_ret' = 0;
  t = t + 2;
  NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                            NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                            NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
  NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
  t = t + NOTEQUAL_neq_zero_imp_time 0 NOTEQUAL_neq_zero_state;
  add_result_to_stack_aux_cond = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state);
  t = t + 2
  in 
   (if add_result_to_stack_aux_cond \<noteq> 0
     then (let 
         t = t + 1;
         t = t + add_result_to_stack_aux_sub_branch_aux2_time 0 s
        in 
         t)
     else (let 
            t = t + 1;
            t = t + add_result_to_stack_aux_con_eq_six_imp_time 0 s
           in 
            t)
       ))"

definition "add_result_to_stack_aux_sub_branch_aux3_IMP_Minus \<equiv> 
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_a_str) ::= A (V add_result_to_stack_aux_con_str);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_b_str) ::= A (N 6);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str) ::= A (N 0);;
  invoke_subprogram NOTEQUAL_neq_zero_prefix NOTEQUAL_neq_zero_IMP_Minus;;
  add_result_to_stack_aux_cond_str ::= A (V (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str));;
  (IF add_result_to_stack_aux_cond_str\<noteq>0
   THEN add_result_to_stack_aux_sub_branch_aux2_IMP_Minus
   ELSE add_result_to_stack_aux_con_eq_six_IMP_Minus)
  "

lemma add_result_to_stack_aux_sub_branch_aux3_IMP_Minus_correct_function:
  "(invoke_subprogram p add_result_to_stack_aux_sub_branch_aux3_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p add_result_to_stack_aux_ret_str)
      = add_result_to_stack_aux_ret
          (add_result_to_stack_aux_sub_branch_aux3 (add_result_to_stack_aux_imp_to_HOL_state p s))"
  apply (subst add_result_to_stack_aux_sub_branch_aux3_def)
  apply (simp only: add_result_to_stack_aux_sub_branch_aux3_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars"])
  subgoal premises p using p(6) by fastforce
  apply (erule If_E)
    subgoal
      apply (fastforce dest!: add_result_to_stack_aux_sub_branch_aux2_IMP_Minus_correct_function
         simp: add_result_to_stack_aux_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def)
    done 
    subgoal
     apply (fastforce dest!: add_result_to_stack_aux_con_eq_six_IMP_Minus_correct_function 
      simp: add_result_to_stack_aux_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def Let_def)
    done
  done

lemma add_result_to_stack_aux_sub_branch_aux3_IMP_Minus_correct_time:
  "(invoke_subprogram p add_result_to_stack_aux_sub_branch_aux3_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (add_result_to_stack_aux_sub_branch_aux3_time 0 (add_result_to_stack_aux_imp_to_HOL_state p s))"
  apply (subst add_result_to_stack_aux_sub_branch_aux3_time_def)
  apply (simp only: add_result_to_stack_aux_sub_branch_aux3_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars"])
  subgoal premises p using p(11) by fastforce
  apply (erule If_tE)
    subgoal
      apply (fastforce dest!: add_result_to_stack_aux_sub_branch_aux2_IMP_Minus_correct_time
       simp: add_result_to_stack_aux_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def)
    done 
    subgoal
     apply (force dest!: add_result_to_stack_aux_con_eq_six_IMP_Minus_correct_time
      simp: add_result_to_stack_aux_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def Let_def)
    done
  done

definition "add_result_to_stack_aux_sub_branch_aux4 s \<equiv>
  (let 
  NOTEQUAL_neq_zero_a' = add_result_to_stack_aux_con s;
  NOTEQUAL_neq_zero_b' = 4;
  NOTEQUAL_neq_zero_ret' = 0;
  NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                            NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                            NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
  NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
  add_result_to_stack_aux_cond = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state)
  in 
   (if add_result_to_stack_aux_cond \<noteq> 0
     then add_result_to_stack_aux_sub_branch_aux3 s
     else add_result_to_stack_aux_con_eq_four_imp s
       ))"

lemma add_result_to_stack_aux_sub_branch_aux4_imp_correct:
  "add_result_to_stack_aux_ret (add_result_to_stack_aux_sub_branch_aux4 s) = 
    (if (add_result_to_stack_aux_con s)=4 
     then ((5## (nth_nat (Suc 0) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc 0)) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc (Suc 0))) (add_result_to_stack_aux_h s))  
       ## (nth_nat (Suc (Suc (Suc ( Suc 0)))) (add_result_to_stack_aux_h s)) ## (add_result_to_stack_aux_c s) ## 0) ## (add_result_to_stack_aux_t s))
     else (if (add_result_to_stack_aux_con s)=6 
     then ((7## (nth_nat (Suc 0) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc 0)) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc (Suc 0))) (add_result_to_stack_aux_h s))  
       ## (nth_nat (Suc (Suc (Suc ( Suc 0)))) (add_result_to_stack_aux_h s)) ## (add_result_to_stack_aux_c s) ## 0) ## (add_result_to_stack_aux_t s))
     else (if (add_result_to_stack_aux_con s)=7 
     then ( ((8## (nth_nat (Suc 0) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc 0)) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc (Suc 0))) (add_result_to_stack_aux_h s))  
     ## (nth_nat (Suc (Suc (Suc ( Suc 0)))) (add_result_to_stack_aux_h s))  ## (nth_nat (Suc (Suc (Suc ( Suc (Suc 0))))) (add_result_to_stack_aux_h s)) ## (add_result_to_stack_aux_c s) ## 0) 
     ## (add_result_to_stack_aux_t s)))
     else (if (add_result_to_stack_aux_con s)=9 
     then ((10## (nth_nat (Suc 0) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc 0)) (add_result_to_stack_aux_h s)) 
      ## (nth_nat (Suc (Suc (Suc 0))) (add_result_to_stack_aux_h s)) 
      ## (add_result_to_stack_aux_c s) ## 0) ## (add_result_to_stack_aux_t s))
     else (add_result_to_stack_aux_s s)))))"
  apply (subst add_result_to_stack_aux_sub_branch_aux4_def)
  apply (auto simp add: NOTEQUAL_neq_zero_imp_correct add_result_to_stack_aux_con_eq_four_imp_correct
  add_result_to_stack_aux_sub_branch_aux3_imp_correct)
  done 

definition "add_result_to_stack_aux_sub_branch_aux4_time t s \<equiv>
  (let 
  NOTEQUAL_neq_zero_a' = add_result_to_stack_aux_con s;
  t = t + 2;
  NOTEQUAL_neq_zero_b' = 4;
  t = t + 2;
  NOTEQUAL_neq_zero_ret' = 0;
  t = t + 2;
  NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                            NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                            NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
  NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
  t = t + NOTEQUAL_neq_zero_imp_time 0 NOTEQUAL_neq_zero_state;
  add_result_to_stack_aux_cond = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state);
  t = t + 2
  in 
   (if add_result_to_stack_aux_cond \<noteq> 0
     then (let 
         t = t + 1;
         t = t + add_result_to_stack_aux_sub_branch_aux3_time 0 s
        in 
         t)
     else (let 
            t = t + 1;
            t = t + add_result_to_stack_aux_con_eq_four_imp_time 0 s
           in 
            t)
       ))"

definition "add_result_to_stack_aux_sub_branch_aux4_IMP_Minus \<equiv> 
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_a_str) ::= A (V add_result_to_stack_aux_con_str);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_b_str) ::= A (N 4);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str) ::= A (N 0);;
  invoke_subprogram NOTEQUAL_neq_zero_prefix NOTEQUAL_neq_zero_IMP_Minus;;
  add_result_to_stack_aux_cond_str ::= A (V (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str));;
  (IF add_result_to_stack_aux_cond_str\<noteq>0
   THEN add_result_to_stack_aux_sub_branch_aux3_IMP_Minus
   ELSE add_result_to_stack_aux_con_eq_four_IMP_Minus)
  "

lemma add_result_to_stack_aux_sub_branch_aux4_IMP_Minus_correct_function:
  "(invoke_subprogram p add_result_to_stack_aux_sub_branch_aux4_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p add_result_to_stack_aux_ret_str)
      = add_result_to_stack_aux_ret
          (add_result_to_stack_aux_sub_branch_aux4 (add_result_to_stack_aux_imp_to_HOL_state p s))"
  apply (subst add_result_to_stack_aux_sub_branch_aux4_def)
  apply (simp only: add_result_to_stack_aux_sub_branch_aux4_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars"])
  subgoal premises p using p(6) by fastforce
  apply (erule If_E)
    subgoal
      apply (fastforce dest!: add_result_to_stack_aux_sub_branch_aux3_IMP_Minus_correct_function
         simp: add_result_to_stack_aux_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def)
    done 
    subgoal
     apply (fastforce dest!: add_result_to_stack_aux_con_eq_four_IMP_Minus_correct_function 
      simp: add_result_to_stack_aux_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def Let_def)
    done
  done

lemma add_result_to_stack_aux_sub_branch_aux4_IMP_Minus_correct_time:
  "(invoke_subprogram p add_result_to_stack_aux_sub_branch_aux4_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (add_result_to_stack_aux_sub_branch_aux4_time 0 (add_result_to_stack_aux_imp_to_HOL_state p s))"
  apply (subst add_result_to_stack_aux_sub_branch_aux4_time_def)
  apply (simp only: add_result_to_stack_aux_sub_branch_aux4_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars"])
  subgoal premises p using p(11) by fastforce
  apply (erule If_tE)
    subgoal
      apply (fastforce dest!: add_result_to_stack_aux_sub_branch_aux3_IMP_Minus_correct_time
       simp: add_result_to_stack_aux_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def)
    done 
    subgoal
     apply (fastforce dest!: add_result_to_stack_aux_con_eq_four_IMP_Minus_correct_time
      simp: add_result_to_stack_aux_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def Let_def)
    done
  done

definition "add_result_to_stack_aux_imp s \<equiv>
  (let 
  NOTEQUAL_neq_zero_a' = add_result_to_stack_aux_con s;
  NOTEQUAL_neq_zero_b' = 3;
  NOTEQUAL_neq_zero_ret' = 0;
  NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                            NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                            NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
  NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
  add_result_to_stack_aux_cond = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state)
  in 
   (if add_result_to_stack_aux_cond \<noteq> 0
     then add_result_to_stack_aux_sub_branch_aux4 s
     else add_result_to_stack_aux_con_eq_three_imp s
       ))"

lemma add_result_to_stack_aux_imp_correct:
  "add_result_to_stack_aux_ret (add_result_to_stack_aux_imp s) = 
    (if (add_result_to_stack_aux_con s)=3 
     then ((4## (nth_nat (Suc 0) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc 0)) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc (Suc 0))) (add_result_to_stack_aux_h s))  
       ## (add_result_to_stack_aux_c s) ## 0) ## (add_result_to_stack_aux_t s))
     else ((if (add_result_to_stack_aux_con s)=4 
     then ((5## (nth_nat (Suc 0) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc 0)) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc (Suc 0))) (add_result_to_stack_aux_h s))  
       ## (nth_nat (Suc (Suc (Suc ( Suc 0)))) (add_result_to_stack_aux_h s)) ## (add_result_to_stack_aux_c s) ## 0) ## (add_result_to_stack_aux_t s))
     else (if (add_result_to_stack_aux_con s)=6 
     then ((7## (nth_nat (Suc 0) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc 0)) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc (Suc 0))) (add_result_to_stack_aux_h s))  
       ## (nth_nat (Suc (Suc (Suc ( Suc 0)))) (add_result_to_stack_aux_h s)) ## (add_result_to_stack_aux_c s) ## 0) ## (add_result_to_stack_aux_t s))
     else (if (add_result_to_stack_aux_con s)=7 
     then ( ((8## (nth_nat (Suc 0) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc 0)) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc (Suc 0))) (add_result_to_stack_aux_h s))  
     ## (nth_nat (Suc (Suc (Suc ( Suc 0)))) (add_result_to_stack_aux_h s))  ## (nth_nat (Suc (Suc (Suc ( Suc (Suc 0))))) (add_result_to_stack_aux_h s)) ## (add_result_to_stack_aux_c s) ## 0) 
     ## (add_result_to_stack_aux_t s)))
     else (if (add_result_to_stack_aux_con s)=9 
     then ((10## (nth_nat (Suc 0) (add_result_to_stack_aux_h s)) ## (nth_nat (Suc (Suc 0)) (add_result_to_stack_aux_h s)) 
      ## (nth_nat (Suc (Suc (Suc 0))) (add_result_to_stack_aux_h s)) 
      ## (add_result_to_stack_aux_c s) ## 0) ## (add_result_to_stack_aux_t s))
     else (add_result_to_stack_aux_s s)))))))"
  apply (subst add_result_to_stack_aux_imp_def)
  apply (auto simp add: NOTEQUAL_neq_zero_imp_correct add_result_to_stack_aux_con_eq_three_imp_correct
  add_result_to_stack_aux_sub_branch_aux4_imp_correct)
  done 

definition "add_result_to_stack_aux_imp_time t s \<equiv>
  (let 
  NOTEQUAL_neq_zero_a' = add_result_to_stack_aux_con s;
  t = t + 2;
  NOTEQUAL_neq_zero_b' = 3;
  t = t + 2;
  NOTEQUAL_neq_zero_ret' = 0;
  t = t + 2;
  NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                            NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                            NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
  NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
  t = t + NOTEQUAL_neq_zero_imp_time 0 NOTEQUAL_neq_zero_state;
  add_result_to_stack_aux_cond = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state);
  t = t + 2
  in 
   (if add_result_to_stack_aux_cond \<noteq> 0
     then (let 
         t = t + 1;
         t = t + add_result_to_stack_aux_sub_branch_aux4_time 0 s
        in 
         t)
     else (let 
            t = t + 1;
            t = t + add_result_to_stack_aux_con_eq_three_imp_time 0 s
           in 
            t)
       ))"

definition "add_result_to_stack_aux_IMP_Minus \<equiv> 
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_a_str) ::= A (V add_result_to_stack_aux_con_str);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_b_str) ::= A (N 3);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str) ::= A (N 0);;
  invoke_subprogram NOTEQUAL_neq_zero_prefix NOTEQUAL_neq_zero_IMP_Minus;;
  add_result_to_stack_aux_cond_str ::= A (V (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str));;
  (IF add_result_to_stack_aux_cond_str\<noteq>0
   THEN add_result_to_stack_aux_sub_branch_aux4_IMP_Minus
   ELSE add_result_to_stack_aux_con_eq_three_IMP_Minus)
  "

lemma add_result_to_stack_aux_IMP_Minus_correct_function:
  "(invoke_subprogram p add_result_to_stack_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p add_result_to_stack_aux_ret_str)
      = add_result_to_stack_aux_ret
          (add_result_to_stack_aux_imp (add_result_to_stack_aux_imp_to_HOL_state p s))"
  apply (subst add_result_to_stack_aux_imp_def)
  apply (simp only: add_result_to_stack_aux_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars"])
  subgoal premises p using p(6) by fastforce
  apply (erule If_E)
    subgoal
      apply (fastforce dest!: add_result_to_stack_aux_sub_branch_aux4_IMP_Minus_correct_function
         simp: add_result_to_stack_aux_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def)
    done 
    subgoal
     apply (fastforce dest!: add_result_to_stack_aux_con_eq_three_IMP_Minus_correct_function 
      simp: add_result_to_stack_aux_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def Let_def)
    done
  done

lemma add_result_to_stack_aux_IMP_Minus_correct_time:
  "(invoke_subprogram p add_result_to_stack_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (add_result_to_stack_aux_imp_time 0 (add_result_to_stack_aux_imp_to_HOL_state p s))"
  apply (subst add_result_to_stack_aux_imp_time_def)
  apply (simp only: add_result_to_stack_aux_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars="add_result_to_stack_aux_IMP_vars"])
  subgoal premises p using p(11) by fastforce
  apply (erule If_tE)
    subgoal
      apply (fastforce dest!: add_result_to_stack_aux_sub_branch_aux4_IMP_Minus_correct_time
       simp: add_result_to_stack_aux_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def)
    done 
    subgoal
     apply (fastforce dest!: add_result_to_stack_aux_con_eq_three_IMP_Minus_correct_time
      simp: add_result_to_stack_aux_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def Let_def)
    done
  done

lemma add_result_to_stack_aux_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) add_result_to_stack_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (add_result_to_stack_aux_imp_time 0 (add_result_to_stack_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) add_result_to_stack_aux_ret_str) =
          add_result_to_stack_aux_ret (add_result_to_stack_aux_imp
                                        (add_result_to_stack_aux_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using add_result_to_stack_aux_IMP_Minus_correct_function 
       add_result_to_stack_aux_IMP_Minus_correct_time
       set_mono_prefix
  by (smt (verit, ccfv_SIG) com_add_prefix_valid_subset com_only_vars)

subsubsection "add_result_to_stack_nat"

record add_result_to_stack_nat_state =
  add_result_to_stack_nat_c::nat 
  add_result_to_stack_nat_s::nat
  add_result_to_stack_nat_ret::nat

abbreviation "add_result_to_stack_nat_prefix \<equiv> ''add_result_to_stack_nat.''"
abbreviation "add_result_to_stack_nat_c_str \<equiv> ''c''"
abbreviation "add_result_to_stack_nat_s_str \<equiv> ''s''"
abbreviation "add_result_to_stack_nat_ret_str \<equiv> ''ret''"

definition "add_result_to_stack_nat_imp_to_HOL_state p s \<equiv> 
  \<lparr>add_result_to_stack_nat_c = s (add_prefix p add_result_to_stack_nat_c_str),
  add_result_to_stack_nat_s = s (add_prefix p add_result_to_stack_nat_s_str),
  add_result_to_stack_nat_ret = s (add_prefix p add_result_to_stack_nat_ret_str)\<rparr>"

paragraph add_result_to_stack_nat_s_eq_zero

definition "add_result_to_stack_nat_s_eq_zero_imp s \<equiv> 
  (let 
    cons_h' = add_result_to_stack_nat_c s;
    cons_t' = 0;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    cons_h' = 0;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    cons_h' = cons_ret cons_ret_state;
    cons_t' = 0;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    add_result_to_stack_nat_ret' = cons_ret cons_ret_state;
    ret = \<lparr>add_result_to_stack_nat_c = add_result_to_stack_nat_c s,
           add_result_to_stack_nat_s = add_result_to_stack_nat_s s,
           add_result_to_stack_nat_ret = add_result_to_stack_nat_ret'\<rparr>
    in 
     ret)"

lemma add_result_to_stack_nat_s_eq_zero_imp_correct[let_function_correctness]:
   "add_result_to_stack_nat_ret (add_result_to_stack_nat_s_eq_zero_imp s) = (0##(add_result_to_stack_nat_c s)##0)##0"
   unfolding add_result_to_stack_nat_s_eq_zero_imp_def
   by (auto simp add: cons_imp_correct)

definition 
"add_result_to_stack_nat_s_eq_zero_imp_time t s \<equiv> 
  (let 
    cons_h' = add_result_to_stack_nat_c s;
    t = t + 2;
    cons_t' = 0;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    cons_h' = 0;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    cons_h' = cons_ret cons_ret_state;
    t = t + 2;
    cons_t' = 0;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    add_result_to_stack_nat_ret' = cons_ret cons_ret_state;
    t = t + 2;
    ret = \<lparr>add_result_to_stack_nat_c = add_result_to_stack_nat_c s,
           add_result_to_stack_nat_s = add_result_to_stack_nat_s s,
           add_result_to_stack_nat_ret = add_result_to_stack_nat_ret'\<rparr>
    in 
     t)"

definition 
  "add_result_to_stack_nat_s_eq_zero_IMP_Minus \<equiv> 
    (cons_prefix @ cons_h_str) ::= A (V add_result_to_stack_nat_c_str);;
    (cons_prefix @ cons_t_str) ::= A (N 0);;
    (cons_prefix @ cons_ret_str) ::= A (N 0);;
    invoke_subprogram cons_prefix cons_IMP_Minus;;

    (cons_prefix @ cons_h_str) ::= A (N 0);;
    (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
    (cons_prefix @ cons_ret_str) ::= A (N 0);;
    invoke_subprogram cons_prefix cons_IMP_Minus;;

    (cons_prefix @ cons_h_str) ::= A (V (cons_prefix @ cons_ret_str));;
    (cons_prefix @ cons_t_str) ::= A (N 0);;
    (cons_prefix @ cons_ret_str) ::= A (N 0);;
    invoke_subprogram cons_prefix cons_IMP_Minus;;

    add_result_to_stack_nat_ret_str ::= A (V (cons_prefix @ cons_ret_str))"

abbreviation "add_result_to_stack_nat_IMP_vars \<equiv> 
  {add_result_to_stack_nat_c_str, add_result_to_stack_nat_s_str, add_result_to_stack_nat_ret_str}"

lemmas add_result_to_stack_nat_s_eq_zero_state_translators = 
  add_result_to_stack_nat_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def

lemma add_result_to_stack_nat_s_eq_zero_IMP_Minus_correct_function:
  "(invoke_subprogram p add_result_to_stack_nat_s_eq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p add_result_to_stack_nat_ret_str)
      = add_result_to_stack_nat_ret
          (add_result_to_stack_nat_s_eq_zero_imp (add_result_to_stack_nat_imp_to_HOL_state p s))"
   apply (subst add_result_to_stack_nat_s_eq_zero_imp_def)
   apply (simp only: add_result_to_stack_nat_s_eq_zero_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_nat_IMP_vars])
   subgoal premises p using p(13) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_nat_IMP_vars])
   subgoal premises p using p(15) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_nat_IMP_vars])
   subgoal premises p using p(17) by fastforce
   apply (fastforce simp: add_result_to_stack_nat_s_eq_zero_state_translators)
   done 

lemma add_result_to_stack_nat_s_eq_zero_IMP_Minus_correct_time :
  "(invoke_subprogram p add_result_to_stack_nat_s_eq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = add_result_to_stack_nat_s_eq_zero_imp_time 0 (add_result_to_stack_nat_imp_to_HOL_state p s)"
   apply (subst add_result_to_stack_nat_s_eq_zero_imp_time_def)
   apply (simp only: add_result_to_stack_nat_s_eq_zero_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_nat_IMP_vars])
   subgoal premises p using p(25) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_nat_IMP_vars])
   subgoal premises p using p(27) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars=add_result_to_stack_nat_IMP_vars])
   subgoal premises p using p(29) by fastforce
   apply (fastforce simp: add_result_to_stack_nat_s_eq_zero_state_translators Let_def)
   done 

paragraph "add_result_to_stack_nat_else_aux"

record add_result_to_stack_nat_else_aux_state =
  add_result_to_stack_nat_else_aux_c::nat 
  add_result_to_stack_nat_else_aux_s::nat
  add_result_to_stack_nat_else_aux_h::nat
  add_result_to_stack_nat_else_aux_con::nat
  add_result_to_stack_nat_else_aux_t::nat

abbreviation "add_result_to_stack_nat_else_aux_prefix \<equiv> ''add_result_to_stack_nat_else_aux.''"
abbreviation "add_result_to_stack_nat_else_aux_c_str \<equiv> ''c''"
abbreviation "add_result_to_stack_nat_else_aux_s_str \<equiv> ''s''"
abbreviation "add_result_to_stack_nat_else_aux_h_str \<equiv> ''h''"
abbreviation "add_result_to_stack_nat_else_aux_con_str \<equiv> ''con''"
abbreviation "add_result_to_stack_nat_else_aux_t_str \<equiv> ''t''"

definition "add_result_to_stack_nat_else_aux_imp_to_HOL_state p s \<equiv> 
  \<lparr>add_result_to_stack_nat_else_aux_c = s (add_prefix p add_result_to_stack_nat_else_aux_c_str),
  add_result_to_stack_nat_else_aux_s = s (add_prefix p add_result_to_stack_nat_else_aux_s_str),
  add_result_to_stack_nat_else_aux_h = s (add_prefix p add_result_to_stack_nat_else_aux_h_str),
  add_result_to_stack_nat_else_aux_con = s (add_prefix p add_result_to_stack_nat_else_aux_con_str),
  add_result_to_stack_nat_else_aux_t = s (add_prefix p add_result_to_stack_nat_else_aux_t_str)\<rparr>"


abbreviation "add_result_to_stack_nat_else_aux_IMP_vars \<equiv> 
  {add_result_to_stack_nat_else_aux_c_str, add_result_to_stack_nat_else_aux_s_str, add_result_to_stack_nat_else_aux_h_str,
  add_result_to_stack_nat_else_aux_con_str, add_result_to_stack_nat_else_aux_t_str}"

definition "add_result_to_stack_nat_else_aux_imp s \<equiv> 
(let 
      hd_xs' = add_result_to_stack_nat_else_aux_s s;
      hd_ret' = 0;
      hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
      hd_ret_state = hd_imp hd_state;
      add_result_to_stack_nat_else_aux_h' = hd_ret hd_ret_state;

      hd_xs' = add_result_to_stack_nat_else_aux_h';
      hd_ret' = 0;
      hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
      hd_ret_state = hd_imp hd_state;
      add_result_to_stack_nat_else_aux_con' = hd_ret hd_ret_state;

      tl_xs' = add_result_to_stack_nat_else_aux_s s;
      tl_ret' = 0;
      tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
      tl_ret_state = tl_imp tl_state;
      add_result_to_stack_nat_else_aux_t' = tl_ret tl_ret_state;

      ret = \<lparr>add_result_to_stack_nat_else_aux_c = add_result_to_stack_nat_else_aux_c s,
            add_result_to_stack_nat_else_aux_s = add_result_to_stack_nat_else_aux_s s,
            add_result_to_stack_nat_else_aux_h = add_result_to_stack_nat_else_aux_h',
            add_result_to_stack_nat_else_aux_con = add_result_to_stack_nat_else_aux_con',
            add_result_to_stack_nat_else_aux_t = add_result_to_stack_nat_else_aux_t'\<rparr>
      in 
      ret)"


lemma add_result_to_stack_nat_else_aux_imp_correct[let_function_correctness]:
  "add_result_to_stack_nat_else_aux_h (add_result_to_stack_nat_else_aux_imp s) = hd_nat (add_result_to_stack_nat_else_aux_s s)
  \<and> add_result_to_stack_nat_else_aux_con (add_result_to_stack_nat_else_aux_imp s) = hd_nat (hd_nat (add_result_to_stack_nat_else_aux_s s))
  \<and> add_result_to_stack_nat_else_aux_t (add_result_to_stack_nat_else_aux_imp s) = tl_nat (add_result_to_stack_nat_else_aux_s s)"
  apply (subst add_result_to_stack_nat_else_aux_imp_def)+
  apply (auto simp add: Let_def
        tl_imp_correct hd_imp_correct add_result_to_stack_nat_def)
  
  done 

definition "add_result_to_stack_nat_else_aux_imp_time t s \<equiv>
(let
    hd_xs' = add_result_to_stack_nat_else_aux_s s;
    t = t + 2;
    hd_ret' = 0;
    t = t + 2;
    hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
    hd_ret_state = hd_imp hd_state;
    t = t + hd_imp_time 0 hd_state;
    add_result_to_stack_nat_else_aux_h' = hd_ret hd_ret_state;
    t = t + 2;

    hd_xs' = add_result_to_stack_nat_else_aux_h';
    t = t + 2;
    hd_ret' = 0;
    t = t + 2;
    hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
    hd_ret_state = hd_imp hd_state;
    t = t + hd_imp_time 0 hd_state;
    add_result_to_stack_nat_else_aux_con' = hd_ret hd_ret_state;
    t = t + 2;

    tl_xs' = add_result_to_stack_nat_else_aux_s s;
    t = t + 2;
    tl_ret' = 0;
    t = t + 2;
    tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
    tl_ret_state = tl_imp tl_state;
    t = t + tl_imp_time 0 tl_state;
    add_result_to_stack_nat_else_aux_t' = tl_ret tl_ret_state;
    t = t + 2;

    ret = \<lparr>add_result_to_stack_nat_else_aux_c = add_result_to_stack_nat_else_aux_c s,
          add_result_to_stack_nat_else_aux_s = add_result_to_stack_nat_else_aux_s s,
          add_result_to_stack_nat_else_aux_h = add_result_to_stack_nat_else_aux_h',
          add_result_to_stack_nat_else_aux_con = add_result_to_stack_nat_else_aux_con',
          add_result_to_stack_nat_else_aux_t = add_result_to_stack_nat_else_aux_t'\<rparr>
in
 t)
"

definition "add_result_to_stack_nat_else_aux_IMP_Minus \<equiv> 
    (hd_prefix @ hd_xs_str) ::= A (V add_result_to_stack_nat_s_str);;
    (hd_prefix @ hd_ret_str) ::= A (N 0);;
    invoke_subprogram hd_prefix hd_IMP_Minus;;
    add_result_to_stack_nat_else_aux_h_str ::= A (V (hd_prefix @ hd_ret_str));;

    (hd_prefix @ hd_xs_str) ::= A (V add_result_to_stack_nat_else_aux_h_str);;
    (hd_prefix @ hd_ret_str) ::= A (N 0);;
    invoke_subprogram hd_prefix hd_IMP_Minus;;
    add_result_to_stack_nat_else_aux_con_str ::= A (V (hd_prefix @ hd_ret_str));;

    (tl_prefix @ tl_xs_str) ::= A (V add_result_to_stack_nat_s_str);;
    (tl_prefix @ tl_ret_str) ::= A (N 0);;
    invoke_subprogram tl_prefix tl_IMP_Minus;;
    add_result_to_stack_nat_else_aux_t_str ::= A (V (tl_prefix @ tl_ret_str))"

lemma add_result_to_stack_nat_else_aux_IMP_Minus_correct_h:
  "(invoke_subprogram p add_result_to_stack_nat_else_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p add_result_to_stack_nat_else_aux_h_str)
      = add_result_to_stack_nat_else_aux_h
          (add_result_to_stack_nat_else_aux_imp (add_result_to_stack_nat_else_aux_imp_to_HOL_state p s))"
    apply (subst add_result_to_stack_nat_else_aux_imp_def)
    apply (simp only: add_result_to_stack_nat_else_aux_IMP_Minus_def prefix_simps)
    apply (erule Seq_E)+
    apply (erule hd_IMP_Minus_correct[where vars = add_result_to_stack_nat_else_aux_IMP_vars])
    subgoal premises p using p(12) by fastforce
    apply (erule hd_IMP_Minus_correct[where vars = "add_result_to_stack_nat_else_aux_IMP_vars 
        \<union> {add_result_to_stack_nat_else_aux_h_str}"])
    subgoal premises p using p(14) by fastforce
    apply (erule tl_IMP_Minus_correct[where vars = "add_result_to_stack_nat_else_aux_IMP_vars 
        \<union> {add_result_to_stack_nat_else_aux_h_str,add_result_to_stack_nat_else_aux_con_str}"])
    subgoal premises p using p(16) by fastforce
    apply (force simp: hd_imp_to_HOL_state_def tl_imp_to_HOL_state_def 
       add_result_to_stack_nat_else_aux_imp_to_HOL_state_def Let_def)
    done 

lemma add_result_to_stack_nat_else_aux_IMP_Minus_correct_con:
  "(invoke_subprogram p add_result_to_stack_nat_else_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p add_result_to_stack_nat_else_aux_con_str)
      = add_result_to_stack_nat_else_aux_con
          (add_result_to_stack_nat_else_aux_imp (add_result_to_stack_nat_else_aux_imp_to_HOL_state p s))"
    apply (subst add_result_to_stack_nat_else_aux_imp_def)
    apply (simp only: add_result_to_stack_nat_else_aux_IMP_Minus_def prefix_simps)
    apply (erule Seq_E)+
    apply (erule hd_IMP_Minus_correct[where vars = add_result_to_stack_nat_else_aux_IMP_vars])
    subgoal premises p using p(12) by fastforce
    apply (erule hd_IMP_Minus_correct[where vars = "add_result_to_stack_nat_else_aux_IMP_vars 
        \<union> {add_result_to_stack_nat_else_aux_h_str}"])
    subgoal premises p using p(14) by fastforce
    apply (erule tl_IMP_Minus_correct[where vars = "add_result_to_stack_nat_else_aux_IMP_vars 
        \<union> {add_result_to_stack_nat_else_aux_h_str,add_result_to_stack_nat_else_aux_con_str}"])
    subgoal premises p using p(16) by fastforce
    apply (force simp: hd_imp_to_HOL_state_def tl_imp_to_HOL_state_def 
       add_result_to_stack_nat_else_aux_imp_to_HOL_state_def Let_def)
    done 

lemma add_result_to_stack_nat_else_aux_IMP_Minus_correct_t:
  "(invoke_subprogram p add_result_to_stack_nat_else_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p add_result_to_stack_nat_else_aux_t_str)
      = add_result_to_stack_nat_else_aux_t
          (add_result_to_stack_nat_else_aux_imp (add_result_to_stack_nat_else_aux_imp_to_HOL_state p s))"
    apply (subst add_result_to_stack_nat_else_aux_imp_def)
    apply (simp only: add_result_to_stack_nat_else_aux_IMP_Minus_def prefix_simps)
    apply (erule Seq_E)+
    apply (erule hd_IMP_Minus_correct[where vars = add_result_to_stack_nat_else_aux_IMP_vars])
    subgoal premises p using p(12) by fastforce
    apply (erule hd_IMP_Minus_correct[where vars = "add_result_to_stack_nat_else_aux_IMP_vars 
        \<union> {add_result_to_stack_nat_else_aux_h_str}"])
    subgoal premises p using p(14) by fastforce
    apply (erule tl_IMP_Minus_correct[where vars = "add_result_to_stack_nat_else_aux_IMP_vars 
        \<union> {add_result_to_stack_nat_else_aux_h_str,add_result_to_stack_nat_else_aux_con_str}"])
    subgoal premises p using p(16) by fastforce
    apply (force simp add: hd_imp_to_HOL_state_def tl_imp_to_HOL_state_def 
       add_result_to_stack_nat_else_aux_imp_to_HOL_state_def Let_def)
    done 

  lemma add_result_to_stack_nat_else_aux_IMP_Minus_correct_time:
  "(invoke_subprogram p add_result_to_stack_nat_else_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (add_result_to_stack_nat_else_aux_imp_time 0 (add_result_to_stack_nat_else_aux_imp_to_HOL_state p s))"
    apply (subst add_result_to_stack_nat_else_aux_imp_time_def)
    apply (simp only: add_result_to_stack_nat_else_aux_IMP_Minus_def prefix_simps)
    apply (erule Seq_tE)+
    apply (erule hd_IMP_Minus_correct[where vars = add_result_to_stack_nat_else_aux_IMP_vars])
    subgoal premises p using p(23) by fastforce
    apply (erule hd_IMP_Minus_correct[where vars = "add_result_to_stack_nat_else_aux_IMP_vars 
        \<union> {add_result_to_stack_nat_else_aux_h_str}"])
    subgoal premises p using p(25) by fastforce
    apply (erule tl_IMP_Minus_correct[where vars = "add_result_to_stack_nat_else_aux_IMP_vars 
        \<union> {add_result_to_stack_nat_else_aux_h_str,add_result_to_stack_nat_else_aux_con_str}"])
    subgoal premises p using p(27) by fastforce
    apply (force simp add: hd_imp_to_HOL_state_def tl_imp_to_HOL_state_def 
       add_result_to_stack_nat_else_aux_imp_to_HOL_state_def Let_def)
    done 
   
lemma add_result_to_stack_nat_else_aux_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) add_result_to_stack_nat_else_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (add_result_to_stack_nat_else_aux_imp_time 0 (add_result_to_stack_nat_else_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) add_result_to_stack_nat_else_aux_h_str) =
          add_result_to_stack_nat_else_aux_h (add_result_to_stack_nat_else_aux_imp
                                        (add_result_to_stack_nat_else_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) add_result_to_stack_nat_else_aux_con_str) =
          add_result_to_stack_nat_else_aux_con (add_result_to_stack_nat_else_aux_imp
                                        (add_result_to_stack_nat_else_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) add_result_to_stack_nat_else_aux_t_str) =
          add_result_to_stack_nat_else_aux_t (add_result_to_stack_nat_else_aux_imp
                                        (add_result_to_stack_nat_else_aux_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using add_result_to_stack_nat_else_aux_IMP_Minus_correct_h 
        add_result_to_stack_nat_else_aux_IMP_Minus_correct_con 
        add_result_to_stack_nat_else_aux_IMP_Minus_correct_t  
       add_result_to_stack_nat_else_aux_IMP_Minus_correct_time
       set_mono_prefix
  by (smt (verit, ccfv_SIG) com_add_prefix_valid_subset com_only_vars)

paragraph "add_result_to_stack_nat_else"

definition "add_result_to_stack_nat_else_imp s \<equiv> 
(let
  add_result_to_stack_nat_else_aux_s' = add_result_to_stack_nat_s s;
  add_result_to_stack_nat_else_aux_c' = add_result_to_stack_nat_c s;
  add_result_to_stack_nat_else_aux_h' = 0;
  add_result_to_stack_nat_else_aux_con' = 0;
  add_result_to_stack_nat_else_aux_t' = 0;
  add_result_to_stack_nat_else_aux_state = 
    \<lparr>add_result_to_stack_nat_else_aux_c = add_result_to_stack_nat_else_aux_c',
    add_result_to_stack_nat_else_aux_s = add_result_to_stack_nat_else_aux_s',
    add_result_to_stack_nat_else_aux_h = add_result_to_stack_nat_else_aux_h',
    add_result_to_stack_nat_else_aux_con = add_result_to_stack_nat_else_aux_con',
    add_result_to_stack_nat_else_aux_t = add_result_to_stack_nat_else_aux_t'\<rparr>;

  add_result_to_stack_nat_else_aux_ret_state = add_result_to_stack_nat_else_aux_imp add_result_to_stack_nat_else_aux_state;
  add_result_to_stack_aux_c' = add_result_to_stack_nat_c s;
  add_result_to_stack_aux_s' = add_result_to_stack_nat_s s;
  add_result_to_stack_aux_h' = add_result_to_stack_nat_else_aux_h add_result_to_stack_nat_else_aux_ret_state;
  add_result_to_stack_aux_con' = add_result_to_stack_nat_else_aux_con add_result_to_stack_nat_else_aux_ret_state;
  add_result_to_stack_aux_t' = add_result_to_stack_nat_else_aux_t add_result_to_stack_nat_else_aux_ret_state;
  add_result_to_stack_aux_ret' = 0;
  add_result_to_stack_aux_state = 
    \<lparr>add_result_to_stack_aux_c = add_result_to_stack_aux_c',
    add_result_to_stack_aux_h = add_result_to_stack_aux_h',
    add_result_to_stack_aux_con = add_result_to_stack_aux_con',
    add_result_to_stack_aux_t = add_result_to_stack_aux_t',
    add_result_to_stack_aux_s = add_result_to_stack_aux_s',
    add_result_to_stack_aux_ret = add_result_to_stack_aux_ret'\<rparr>;
  add_result_to_stack_aux_ret_state = add_result_to_stack_aux_imp add_result_to_stack_aux_state;

  add_result_to_stack_nat_ret' = add_result_to_stack_aux_ret add_result_to_stack_aux_ret_state;

  ret = 
   \<lparr>add_result_to_stack_nat_c = add_result_to_stack_nat_c s,
   add_result_to_stack_nat_s = add_result_to_stack_nat_s s,
   add_result_to_stack_nat_ret = add_result_to_stack_nat_ret'\<rparr>
in
 ret)"

lemma add_result_to_stack_nat_else_imp_correct:
  "add_result_to_stack_nat_ret (add_result_to_stack_nat_else_imp s) = 
    (let h = hd_nat (add_result_to_stack_nat_s s); con = hd_nat h; t = tl_nat (add_result_to_stack_nat_s s)  in 
  if con = 3 then ((4## (nth_nat (Suc 0) h) ## (nth_nat (Suc (Suc 0)) h) ## (nth_nat (Suc (Suc (Suc 0))) h) 
    ## (add_result_to_stack_nat_c s) ## 0) ## t) 
  else if con = 4 then ((5## (nth_nat (Suc 0) h) ## (nth_nat (Suc (Suc 0)) h) 
    ## (nth_nat (Suc (Suc (Suc 0))) h)  ## (nth_nat (Suc (Suc (Suc ( Suc 0)))) h) 
    ## (add_result_to_stack_nat_c s) ## 0) ## t)
  else if con = 6 then ((7## (nth_nat (Suc 0) h) ## (nth_nat (Suc (Suc 0)) h) 
    ## (nth_nat (Suc (Suc (Suc 0))) h)  ## (nth_nat (Suc (Suc (Suc ( Suc 0)))) h) 
    ## (add_result_to_stack_nat_c s) ## 0) ## t)    
  else if con = 7 then ((8## (nth_nat (Suc 0) h) ## (nth_nat (Suc (Suc 0)) h) 
    ## (nth_nat (Suc (Suc (Suc 0))) h)  ## (nth_nat (Suc (Suc (Suc ( Suc 0)))) h)  
    ## (nth_nat (Suc (Suc (Suc ( Suc (Suc 0))))) h) ## (add_result_to_stack_nat_c s) ## 0) ## t)
  else if con = 9 then ((10 ## (nth_nat (Suc 0) h) ## (nth_nat (Suc (Suc 0)) h) 
    ## (nth_nat (Suc (Suc (Suc 0))) h) ## (add_result_to_stack_nat_c s) ## 0) ## t) 
  else (add_result_to_stack_nat_s s)
)"
apply (subst add_result_to_stack_nat_else_imp_def)
apply (auto simp add: add_result_to_stack_nat_else_aux_imp_correct
 add_result_to_stack_aux_imp_correct Let_def)
done 

definition "add_result_to_stack_nat_else_imp_time t s \<equiv> 
(let
  add_result_to_stack_nat_else_aux_s' = add_result_to_stack_nat_s s;
  t = t + 2;
  add_result_to_stack_nat_else_aux_c' = add_result_to_stack_nat_c s;
  t = t + 2;
  add_result_to_stack_nat_else_aux_h' = 0;
  t = t + 2;
  add_result_to_stack_nat_else_aux_con' = 0;
  t = t + 2;
  add_result_to_stack_nat_else_aux_t' = 0;
  t = t + 2;
  add_result_to_stack_nat_else_aux_state = 
    \<lparr>add_result_to_stack_nat_else_aux_c = add_result_to_stack_nat_else_aux_c',
    add_result_to_stack_nat_else_aux_s = add_result_to_stack_nat_else_aux_s',
    add_result_to_stack_nat_else_aux_h = add_result_to_stack_nat_else_aux_h',
    add_result_to_stack_nat_else_aux_con = add_result_to_stack_nat_else_aux_con',
    add_result_to_stack_nat_else_aux_t = add_result_to_stack_nat_else_aux_t'\<rparr>;
  add_result_to_stack_nat_else_aux_ret_state = add_result_to_stack_nat_else_aux_imp add_result_to_stack_nat_else_aux_state;
  t = t + add_result_to_stack_nat_else_aux_imp_time 0 add_result_to_stack_nat_else_aux_state;

  add_result_to_stack_aux_c' = add_result_to_stack_nat_c s;
    t = t + 2;
  add_result_to_stack_aux_s' = add_result_to_stack_nat_s s;
    t = t + 2;
  add_result_to_stack_aux_h' = add_result_to_stack_nat_else_aux_h add_result_to_stack_nat_else_aux_ret_state;
    t = t + 2;
  add_result_to_stack_aux_con' = add_result_to_stack_nat_else_aux_con add_result_to_stack_nat_else_aux_ret_state;
    t = t + 2;
  add_result_to_stack_aux_t' = add_result_to_stack_nat_else_aux_t add_result_to_stack_nat_else_aux_ret_state;
    t = t + 2;
  add_result_to_stack_aux_ret' = 0;
    t = t + 2;
  add_result_to_stack_aux_state = 
    \<lparr>add_result_to_stack_aux_c = add_result_to_stack_aux_c',
    add_result_to_stack_aux_h = add_result_to_stack_aux_h',
    add_result_to_stack_aux_con = add_result_to_stack_aux_con',
    add_result_to_stack_aux_t = add_result_to_stack_aux_t',
    add_result_to_stack_aux_s = add_result_to_stack_aux_s',
    add_result_to_stack_aux_ret = add_result_to_stack_aux_ret'\<rparr>;
  add_result_to_stack_aux_ret_state = add_result_to_stack_aux_imp add_result_to_stack_aux_state;
    t = t + add_result_to_stack_aux_imp_time 0 add_result_to_stack_aux_state;

  add_result_to_stack_nat_ret' = add_result_to_stack_aux_ret add_result_to_stack_aux_ret_state;
  t = t + 2;

  ret = 
   \<lparr>add_result_to_stack_nat_c = add_result_to_stack_nat_c s,
   add_result_to_stack_nat_s = add_result_to_stack_nat_s s,
   add_result_to_stack_nat_ret = add_result_to_stack_nat_ret'\<rparr>
in
 t)"

definition "add_result_to_stack_nat_else_IMP_Minus \<equiv> 
  (add_result_to_stack_nat_else_aux_prefix @ add_result_to_stack_nat_else_aux_s_str)
    ::= A (V add_result_to_stack_nat_s_str);;
  (add_result_to_stack_nat_else_aux_prefix @ add_result_to_stack_nat_else_aux_c_str)
    ::= A (V add_result_to_stack_nat_c_str);;
  (add_result_to_stack_nat_else_aux_prefix @ add_result_to_stack_nat_else_aux_h_str)
    ::= A (N 0);;
  (add_result_to_stack_nat_else_aux_prefix @ add_result_to_stack_nat_else_aux_con_str)
    ::= A (N 0);;
  (add_result_to_stack_nat_else_aux_prefix @ add_result_to_stack_nat_else_aux_t_str)
    ::= A (N 0);;
  invoke_subprogram add_result_to_stack_nat_else_aux_prefix add_result_to_stack_nat_else_aux_IMP_Minus;;

  (add_result_to_stack_aux_prefix @ add_result_to_stack_aux_s_str)
    ::= A (V add_result_to_stack_nat_s_str);;
  (add_result_to_stack_aux_prefix @ add_result_to_stack_aux_c_str)
    ::= A (V add_result_to_stack_nat_c_str);;
  (add_result_to_stack_aux_prefix @ add_result_to_stack_aux_h_str)
    ::= A (V (add_result_to_stack_nat_else_aux_prefix @ add_result_to_stack_nat_else_aux_h_str));;
  (add_result_to_stack_aux_prefix @ add_result_to_stack_aux_con_str)
    ::= A (V (add_result_to_stack_nat_else_aux_prefix @ add_result_to_stack_nat_else_aux_con_str));;
  (add_result_to_stack_aux_prefix @ add_result_to_stack_aux_t_str)
    ::= A (V (add_result_to_stack_nat_else_aux_prefix @ add_result_to_stack_nat_else_aux_t_str));;
  (add_result_to_stack_aux_prefix @ add_result_to_stack_aux_ret_str)
    ::= A (N 0);;
  invoke_subprogram add_result_to_stack_aux_prefix add_result_to_stack_aux_IMP_Minus;;
  (add_result_to_stack_nat_ret_str) ::= A (V (add_result_to_stack_aux_prefix @ add_result_to_stack_aux_ret_str))
  "

lemma add_result_to_stack_nat_else_IMP_Minus_correct_function:
"(invoke_subprogram p add_result_to_stack_nat_else_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p add_result_to_stack_nat_ret_str)
      = add_result_to_stack_nat_ret
          (add_result_to_stack_nat_else_imp (add_result_to_stack_nat_imp_to_HOL_state p s))"
apply (subst add_result_to_stack_nat_else_imp_def)
apply (simp only: add_result_to_stack_nat_else_IMP_Minus_def prefix_simps)
apply (erule Seq_E)+
apply (erule add_result_to_stack_nat_else_aux_IMP_Minus_correct[where vars=add_result_to_stack_nat_IMP_vars])
subgoal premises p using p(14) by fastforce 
apply (erule add_result_to_stack_aux_IMP_Minus_correct[where vars=add_result_to_stack_nat_IMP_vars])
subgoal premises p using p(18) by fastforce 
apply (fastforce simp add: add_result_to_stack_aux_imp_to_HOL_state_def add_result_to_stack_nat_else_aux_imp_to_HOL_state_def 
      add_result_to_stack_nat_imp_to_HOL_state_def Let_def)
done 

lemma add_result_to_stack_nat_else_IMP_Minus_correct_time:
"(invoke_subprogram p add_result_to_stack_nat_else_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (add_result_to_stack_nat_else_imp_time 0 (add_result_to_stack_nat_imp_to_HOL_state p s))"
apply (subst add_result_to_stack_nat_else_imp_time_def)
apply (simp only: add_result_to_stack_nat_else_IMP_Minus_def prefix_simps)
apply (erule Seq_tE)+
apply (erule add_result_to_stack_nat_else_aux_IMP_Minus_correct[where vars=add_result_to_stack_nat_IMP_vars])
subgoal premises p using p(27) by fastforce 
apply (erule add_result_to_stack_aux_IMP_Minus_correct[where vars=add_result_to_stack_nat_IMP_vars])
subgoal premises p using p(31) by fastforce 
apply (fastforce simp add: add_result_to_stack_aux_imp_to_HOL_state_def add_result_to_stack_nat_else_aux_imp_to_HOL_state_def 
      add_result_to_stack_nat_imp_to_HOL_state_def Let_def)
done 

paragraph "add_result_to_stack_nat"

abbreviation "add_result_to_stack_nat_cond_str \<equiv> ''cond''"

definition "add_result_to_stack_nat_imp s \<equiv> 
  (let
    add_result_to_stack_nat_cond = add_result_to_stack_nat_s s
  in 
   (if add_result_to_stack_nat_cond\<noteq> 0 then 
    add_result_to_stack_nat_else_imp s
    else (add_result_to_stack_nat_s_eq_zero_imp s))
  )"

lemma add_result_to_stack_nat_imp_correct[let_function_correctness]:
  "add_result_to_stack_nat_ret (add_result_to_stack_nat_imp s) = 
    add_result_to_stack_nat (add_result_to_stack_nat_c s) (add_result_to_stack_nat_s s)"
  apply (subst add_result_to_stack_nat_imp_def)
  apply (auto simp add: Let_def add_result_to_stack_nat_else_imp_correct add_result_to_stack_nat_s_eq_zero_imp_correct
    add_result_to_stack_nat_def)
  done 

definition "add_result_to_stack_nat_imp_time t s \<equiv> 
  (let
    add_result_to_stack_nat_cond = add_result_to_stack_nat_s s;
    t = t + 2
  in
   (if add_result_to_stack_nat_cond\<noteq> 0 then 
     (let 
        t = t + 1;
        t = t + add_result_to_stack_nat_else_imp_time 0 s
        in 
        t)
    else (
        let
          t = t + 1;
          t = t + add_result_to_stack_nat_s_eq_zero_imp_time 0 s
        in
         t))
  )"

definition "add_result_to_stack_nat_IMP_Minus \<equiv> 
  add_result_to_stack_nat_cond_str ::= A (V add_result_to_stack_nat_s_str);;
  (IF add_result_to_stack_nat_cond_str \<noteq>0
  THEN add_result_to_stack_nat_else_IMP_Minus
  ELSE add_result_to_stack_nat_s_eq_zero_IMP_Minus)"


lemma add_result_to_stack_nat_IMP_Minus_correct_function:
  "(invoke_subprogram p add_result_to_stack_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p add_result_to_stack_nat_ret_str)
      = add_result_to_stack_nat_ret
          (add_result_to_stack_nat_imp (add_result_to_stack_nat_imp_to_HOL_state p s))"
  apply (subst add_result_to_stack_nat_imp_def)
  apply (simp only: add_result_to_stack_nat_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
    apply (erule If_E)
    subgoal
      apply (fastforce dest!: add_result_to_stack_nat_else_IMP_Minus_correct_function 
      simp: add_result_to_stack_nat_imp_to_HOL_state_def Let_def)
    done 
    subgoal
     apply (fastforce dest!: add_result_to_stack_nat_s_eq_zero_IMP_Minus_correct_function 
      simp: add_result_to_stack_nat_imp_to_HOL_state_def Let_def)
    done
  done

lemma add_result_to_stack_nat_IMP_Minus_correct_time:
  "(invoke_subprogram p add_result_to_stack_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (add_result_to_stack_nat_imp_time 0 (add_result_to_stack_nat_imp_to_HOL_state p s))"
  apply (subst add_result_to_stack_nat_imp_time_def)
  apply (simp only: add_result_to_stack_nat_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
    apply (erule If_tE)
    subgoal
      apply (fastforce dest!: add_result_to_stack_nat_else_IMP_Minus_correct_time 
      simp: add_result_to_stack_nat_imp_to_HOL_state_def Let_def)
    done 
    subgoal
     apply (fastforce dest!: add_result_to_stack_nat_s_eq_zero_IMP_Minus_correct_time  
      simp: add_result_to_stack_nat_imp_to_HOL_state_def Let_def)
    done
  done

lemma add_result_to_stack_nat_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) add_result_to_stack_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (add_result_to_stack_nat_imp_time 0 (add_result_to_stack_nat_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) add_result_to_stack_nat_ret_str) =
          add_result_to_stack_nat_ret (add_result_to_stack_nat_imp
                                        (add_result_to_stack_nat_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using add_result_to_stack_nat_IMP_Minus_correct_function 
       add_result_to_stack_nat_IMP_Minus_correct_time
       set_mono_prefix
  by (smt (verit, ccfv_SIG) com_add_prefix_valid_subset com_only_vars)

subsection \<open>push_on_stack\<close>
subsubsection \<open>push_on_stack_nat\<close>
record push_on_stack_nat_state =
push_on_stack_nat_c :: nat
push_on_stack_nat_n :: nat
push_on_stack_nat_s :: nat
push_on_stack_nat_ret :: nat

abbreviation "push_on_stack_nat_prefix \<equiv> ''push_on_stack_nat.''"
abbreviation "push_on_stack_nat_c_str \<equiv> ''push_on_stack_nat_c''"
abbreviation "push_on_stack_nat_n_str \<equiv> ''push_on_stack_nat_n''"
abbreviation "push_on_stack_nat_s_str \<equiv> ''push_on_stack_nat_s''"
abbreviation "push_on_stack_nat_ret_str \<equiv> ''push_on_stack_nat_ret''"

definition "push_on_stack_nat_imp_to_HOL_state p s \<equiv>
  \<lparr>push_on_stack_nat_c = s (add_prefix p push_on_stack_nat_c_str),
  push_on_stack_nat_n = s (add_prefix p push_on_stack_nat_n_str),
  push_on_stack_nat_s = s (add_prefix p push_on_stack_nat_s_str),
  push_on_stack_nat_ret = s (add_prefix p push_on_stack_nat_ret_str)\<rparr>"

abbreviation "push_on_stack_nat_hd_c \<equiv> ''push_on_stack_nat_hd_c''"
abbreviation "push_on_stack_nat_cons_n_0 \<equiv> ''push_on_stack_nat_cons_n_0''"
abbreviation "push_on_stack_nat_nth_nat_ret_one \<equiv> ''push_on_stack_nat_nth_nat_ret_one''"
abbreviation "push_on_stack_nat_nth_nat_ret_two \<equiv> ''push_on_stack_nat_nth_nat_ret_two''"
abbreviation "push_on_stack_nat_nth_nat_ret_three \<equiv> ''push_on_stack_nat_nth_nat_ret_three''"
abbreviation "push_on_stack_nat_cons_res \<equiv> ''push_on_stack_nat_cons_res''"
abbreviation "push_on_stack_nat_cond_one \<equiv> ''push_on_stack_nat_cond_one''"
abbreviation "push_on_stack_nat_cond_two \<equiv> ''push_on_stack_nat_cond_two''"
abbreviation "push_on_stack_nat_cond_three \<equiv> ''push_on_stack_nat_cond_three''"

abbreviation "push_on_stack_nat_IMP_vars \<equiv> {
  push_on_stack_nat_c_str, push_on_stack_nat_n_str, push_on_stack_nat_s_str, push_on_stack_nat_ret_str 
}"


lemmas push_on_stack_nat_state_translators =
  push_on_stack_nat_imp_to_HOL_state_def
  hd_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  NOTEQUAL_neq_zero_imp_to_HOL_state_def
  nth_nat_imp_to_HOL_state_def

paragraph if_eq_zero 

definition "push_on_stack_nat_eq_zero s \<equiv> 
  (let
  cons_h' = push_on_stack_nat_n s;
  cons_t' = 0;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  cons_h' = 1;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  cons_h' = cons_ret cons_ret_state;
  cons_t' = push_on_stack_nat_s s;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  push_on_stack_nat_ret' = cons_ret cons_ret_state;
  ret = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c s,
        push_on_stack_nat_n = push_on_stack_nat_n s,
        push_on_stack_nat_s = push_on_stack_nat_s s,
        push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>
in
  ret)"

lemma push_on_stack_nat_eq_zero_imp_correct[let_function_correctness]:
  "push_on_stack_nat_ret (push_on_stack_nat_eq_zero s) = 
    cons (cons 1 (cons (push_on_stack_nat_n s) 0)) (push_on_stack_nat_s s)"
  unfolding push_on_stack_nat_eq_zero_def
  apply (simp add: hd_imp_correct cons_imp_correct Let_def)
  done 

definition "push_on_stack_nat_eq_zero_time t s \<equiv> 
  (let
  cons_h' = push_on_stack_nat_n s;
  t = t + 2;
  cons_t' = 0;
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

  cons_h' = cons_ret cons_ret_state;
  t = t + 2;
  cons_t' = push_on_stack_nat_s s;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  push_on_stack_nat_ret' = cons_ret cons_ret_state;
  t = t + 2;
  ret = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c s,
        push_on_stack_nat_n = push_on_stack_nat_n s,
        push_on_stack_nat_s = push_on_stack_nat_s s,
        push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>
in
  t)"

definition "push_on_stack_nat_eq_zero_IMP_Minus \<equiv> 
 (cons_prefix @ cons_h_str) ::= A (V push_on_stack_nat_n_str);;
 (cons_prefix @ cons_t_str) ::= A (N 0);;
 (cons_prefix @ cons_ret_str) ::= A (N 0);;
 invoke_subprogram cons_prefix cons_IMP_Minus;;

 (cons_prefix @ cons_h_str) ::= A (N 1);;
 (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
 (cons_prefix @ cons_ret_str) ::= A (N 0);;
 invoke_subprogram cons_prefix cons_IMP_Minus;;

 (cons_prefix @ cons_h_str) ::= A (V (cons_prefix @ cons_ret_str));;
 (cons_prefix @ cons_t_str) ::= A (V push_on_stack_nat_s_str);;
 (cons_prefix @ cons_ret_str) ::= A (N 0);;
 invoke_subprogram cons_prefix cons_IMP_Minus;;
 push_on_stack_nat_ret_str ::= A (V (cons_prefix @ cons_ret_str))
"

lemma push_on_stack_nat_eq_zero_IMP_Minus_correct_function:
  "(invoke_subprogram p push_on_stack_nat_eq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p push_on_stack_nat_ret_str)
      = push_on_stack_nat_ret
          (push_on_stack_nat_eq_zero (push_on_stack_nat_imp_to_HOL_state p s))"
   apply (subst push_on_stack_nat_eq_zero_def)
   apply (simp only: push_on_stack_nat_eq_zero_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
   subgoal premises p using p(13) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
   subgoal premises p using p(15) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
   subgoal premises p using p(17) by fastforce 
   apply (fastforce simp: 
      push_on_stack_nat_imp_to_HOL_state_def cons_imp_to_HOL_state_def Let_def)
   done 

lemma push_on_stack_nat_eq_zero_IMP_Minus_correct_time:
  "(invoke_subprogram p push_on_stack_nat_eq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = push_on_stack_nat_eq_zero_time 0 (push_on_stack_nat_imp_to_HOL_state p s)"
   apply (subst push_on_stack_nat_eq_zero_time_def)
   apply (simp only: push_on_stack_nat_eq_zero_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
   subgoal premises p using p(25) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
   subgoal premises p using p(27) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
   subgoal premises p using p(29) by fastforce 
   apply (fastforce simp:
      push_on_stack_nat_imp_to_HOL_state_def cons_imp_to_HOL_state_def Let_def)
   done

paragraph if_eq_one

definition "push_on_stack_nat_eq_one s \<equiv> 
  (let
  cons_h' = push_on_stack_nat_n s;
  cons_t' = 0;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  push_on_stack_nat_cons_res = cons_ret cons_ret_state;

  nth_nat_n' = 1;
  nth_nat_x' = push_on_stack_nat_c s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  push_on_stack_nat_nth_nat_ret_one = nth_nat_ret nth_nat_ret_state;

  nth_nat_n' = 2;
  nth_nat_x' = push_on_stack_nat_c s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  cons_t' = push_on_stack_nat_cons_res;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = push_on_stack_nat_nth_nat_ret_one;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = 2;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = cons_ret cons_ret_state;
  cons_t' = push_on_stack_nat_s s;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  push_on_stack_nat_ret' = cons_ret cons_ret_state;
  ret = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c s,
        push_on_stack_nat_n = push_on_stack_nat_n s,
        push_on_stack_nat_s = push_on_stack_nat_s s,
        push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>
in
  ret)"

lemma push_on_stack_nat_eq_one_imp_correct[let_function_correctness]:
  "push_on_stack_nat_ret (push_on_stack_nat_eq_one s) = 
    (2## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s)"
  unfolding push_on_stack_nat_eq_one_def
  apply (simp add: nth_nat_imp_correct cons_imp_correct Let_def numeral_2_eq_2)
  done

definition "push_on_stack_nat_eq_one_time t s \<equiv> 
  (let
  cons_h' = push_on_stack_nat_n s;
  t = t + 2;
  cons_t' = 0;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;
  push_on_stack_nat_cons_res = cons_ret cons_ret_state;
  t = t + 2;

  nth_nat_n' = 1;
  t = t + 2;
  nth_nat_x' = push_on_stack_nat_c s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;
  push_on_stack_nat_nth_nat_ret_one = nth_nat_ret nth_nat_ret_state;
  t = t + 2;

  nth_nat_n' = 2;
  t = t + 2;
  nth_nat_x' = push_on_stack_nat_c s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  t = t + 2;
  cons_t' = push_on_stack_nat_cons_res;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  cons_h' = push_on_stack_nat_nth_nat_ret_one;
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

  cons_h' = cons_ret cons_ret_state;
  t = t + 2;
  cons_t' = push_on_stack_nat_s s;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  push_on_stack_nat_ret' = cons_ret cons_ret_state;
  t = t + 2;
  ret = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c s,
        push_on_stack_nat_n = push_on_stack_nat_n s,
        push_on_stack_nat_s = push_on_stack_nat_s s,
        push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>
in
  t)"

definition "push_on_stack_nat_eq_one_IMP_Minus \<equiv>
  (cons_prefix @ cons_h_str) ::= A (V push_on_stack_nat_n_str);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  push_on_stack_nat_cons_res ::= A (V (cons_prefix @ cons_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 1);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V push_on_stack_nat_c_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  push_on_stack_nat_nth_nat_ret_one ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 2);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V push_on_stack_nat_c_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V push_on_stack_nat_cons_res);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V push_on_stack_nat_nth_nat_ret_one);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (N 2);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V push_on_stack_nat_s_str);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  push_on_stack_nat_ret_str ::= A (V (cons_prefix @ cons_ret_str))
"

abbreviation "push_on_stack_nat_IMP_vars_eq_one \<equiv> push_on_stack_nat_IMP_vars 
  \<union> {push_on_stack_nat_nth_nat_ret_one, push_on_stack_nat_cons_res}"

lemma push_on_stack_nat_eq_one_IMP_Minus_correct_function:
  "(invoke_subprogram p push_on_stack_nat_eq_one_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p push_on_stack_nat_ret_str)
      = push_on_stack_nat_ret
          (push_on_stack_nat_eq_one (push_on_stack_nat_imp_to_HOL_state p s))"
   apply (subst push_on_stack_nat_eq_one_def)
   apply (simp only: push_on_stack_nat_eq_one_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
   subgoal premises p using p(31) by fastforce 
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
   subgoal premises p using p(33) by fastforce 
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
   subgoal premises p using p(35) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
   subgoal premises p using p(37) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
   subgoal premises p using p(39) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
   subgoal premises p using p(41) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
   subgoal premises p using p(43) by fastforce
   apply (force simp:
      push_on_stack_nat_imp_to_HOL_state_def cons_imp_to_HOL_state_def 
      nth_nat_imp_to_HOL_state_def Let_def)
   done


lemma push_on_stack_nat_eq_one_IMP_Minus_correct_time:
  "(invoke_subprogram p push_on_stack_nat_eq_one_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = push_on_stack_nat_eq_one_time 0 (push_on_stack_nat_imp_to_HOL_state p s)"
  apply (subst push_on_stack_nat_eq_one_time_def)
  apply (simp only: push_on_stack_nat_eq_one_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
  subgoal premises p using p(61) by fastforce 
  apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
  subgoal premises p using p(63) by fastforce 
  apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
  subgoal premises p using p(65) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
  subgoal premises p using p(67) by fastforce 
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
  subgoal premises p using p(69) by fastforce 
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
  subgoal premises p using p(71) by fastforce 
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
  subgoal premises p using p(73) by fastforce
  apply (force simp: 
      push_on_stack_nat_imp_to_HOL_state_def cons_imp_to_HOL_state_def 
      nth_nat_imp_to_HOL_state_def Let_def)
  done

paragraph if_eq_two

definition "push_on_stack_nat_eq_two s \<equiv> 
  (let
  cons_h' = push_on_stack_nat_n s;
  cons_t' = 0;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  push_on_stack_nat_cons_res = cons_ret cons_ret_state;

  nth_nat_n' = 1;
  nth_nat_x' = push_on_stack_nat_c s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  push_on_stack_nat_nth_nat_ret_one = nth_nat_ret nth_nat_ret_state;

  nth_nat_n' = 2;
  nth_nat_x' = push_on_stack_nat_c s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  cons_t' = push_on_stack_nat_cons_res;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = push_on_stack_nat_nth_nat_ret_one;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = 3;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = cons_ret cons_ret_state;
  cons_t' = push_on_stack_nat_s s;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  push_on_stack_nat_ret' = cons_ret cons_ret_state;
  ret = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c s,
        push_on_stack_nat_n = push_on_stack_nat_n s,
        push_on_stack_nat_s = push_on_stack_nat_s s,
        push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>
in
  ret)"

lemma push_on_stack_nat_eq_two_imp_correct[let_function_correctness]:
  "push_on_stack_nat_ret (push_on_stack_nat_eq_two s) = 
    (3## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s)"
  unfolding push_on_stack_nat_eq_two_def
  apply (simp add: nth_nat_imp_correct cons_imp_correct Let_def numeral_2_eq_2)
  done

definition "push_on_stack_nat_eq_two_time t s \<equiv> 
  (let
  cons_h' = push_on_stack_nat_n s;
  t = t + 2;
  cons_t' = 0;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;
  push_on_stack_nat_cons_res = cons_ret cons_ret_state;
  t = t + 2;

  nth_nat_n' = 1;
  t = t + 2;
  nth_nat_x' = push_on_stack_nat_c s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;
  push_on_stack_nat_nth_nat_ret_one = nth_nat_ret nth_nat_ret_state;
  t = t + 2;

  nth_nat_n' = 2;
  t = t + 2;
  nth_nat_x' = push_on_stack_nat_c s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  t = t + 2;
  cons_t' = push_on_stack_nat_cons_res;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  cons_h' = push_on_stack_nat_nth_nat_ret_one;
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

  cons_h' = cons_ret cons_ret_state;
  t = t + 2;
  cons_t' = push_on_stack_nat_s s;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  push_on_stack_nat_ret' = cons_ret cons_ret_state;
  t = t + 2;
  ret = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c s,
        push_on_stack_nat_n = push_on_stack_nat_n s,
        push_on_stack_nat_s = push_on_stack_nat_s s,
        push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>
in
  t)"

definition "push_on_stack_nat_eq_two_IMP_Minus \<equiv>
  (cons_prefix @ cons_h_str) ::= A (V push_on_stack_nat_n_str);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  push_on_stack_nat_cons_res ::= A (V (cons_prefix @ cons_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 1);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V push_on_stack_nat_c_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  push_on_stack_nat_nth_nat_ret_one ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 2);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V push_on_stack_nat_c_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V push_on_stack_nat_cons_res);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V push_on_stack_nat_nth_nat_ret_one);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (N 3);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V push_on_stack_nat_s_str);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  push_on_stack_nat_ret_str ::= A (V (cons_prefix @ cons_ret_str))
"

abbreviation "push_on_stack_nat_IMP_vars_eq_two \<equiv> push_on_stack_nat_IMP_vars 
  \<union> {push_on_stack_nat_nth_nat_ret_one, push_on_stack_nat_cons_res}"

lemma push_on_stack_nat_eq_two_IMP_Minus_correct_function:
  "(invoke_subprogram p push_on_stack_nat_eq_two_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p push_on_stack_nat_ret_str)
      = push_on_stack_nat_ret
          (push_on_stack_nat_eq_two (push_on_stack_nat_imp_to_HOL_state p s))"
   apply (subst push_on_stack_nat_eq_two_def)
   apply (simp only: push_on_stack_nat_eq_two_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
   subgoal premises p using p(31) by fastforce 
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
   subgoal premises p using p(33) by fastforce 
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
   subgoal premises p using p(35) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
   subgoal premises p using p(37) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
   subgoal premises p using p(39) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
   subgoal premises p using p(41) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
   subgoal premises p using p(43) by fastforce
   apply (force simp:
      push_on_stack_nat_imp_to_HOL_state_def cons_imp_to_HOL_state_def 
      nth_nat_imp_to_HOL_state_def Let_def)
   done

lemma push_on_stack_nat_eq_two_IMP_Minus_correct_time:
  "(invoke_subprogram p push_on_stack_nat_eq_two_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = push_on_stack_nat_eq_two_time 0 (push_on_stack_nat_imp_to_HOL_state p s)"
  apply (subst push_on_stack_nat_eq_two_time_def)
  apply (simp only: push_on_stack_nat_eq_two_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
  subgoal premises p using p(61) by fastforce 
  apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
  subgoal premises p using p(63) by fastforce 
  apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
  subgoal premises p using p(65) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
  subgoal premises p using p(67) by fastforce 
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
  subgoal premises p using p(69) by fastforce 
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
  subgoal premises p using p(71) by fastforce 
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
  subgoal premises p using p(73) by fastforce
  apply (force simp:
      push_on_stack_nat_imp_to_HOL_state_def cons_imp_to_HOL_state_def 
      nth_nat_imp_to_HOL_state_def Let_def)
  done

paragraph if_else

definition "push_on_stack_nat_else s \<equiv> 
  (let
  cons_h' = push_on_stack_nat_n s;
  cons_t' = 0;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  push_on_stack_nat_cons_res = cons_ret cons_ret_state;

  nth_nat_n' = 1;
  nth_nat_x' = push_on_stack_nat_c s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  push_on_stack_nat_nth_nat_ret_one = nth_nat_ret nth_nat_ret_state;

  nth_nat_n' = 2;
  nth_nat_x' = push_on_stack_nat_c s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  cons_t' = push_on_stack_nat_cons_res;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = push_on_stack_nat_nth_nat_ret_one;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = 9;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = cons_ret cons_ret_state;
  cons_t' = push_on_stack_nat_s s;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  push_on_stack_nat_ret' = cons_ret cons_ret_state;
  ret = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c s,
        push_on_stack_nat_n = push_on_stack_nat_n s,
        push_on_stack_nat_s = push_on_stack_nat_s s,
        push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>
in
  ret)"

lemma push_on_stack_nat_else_imp_correct[let_function_correctness]:
  "push_on_stack_nat_ret (push_on_stack_nat_else s) = 
    (9## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s)"
  unfolding push_on_stack_nat_else_def
  apply (simp add: nth_nat_imp_correct cons_imp_correct Let_def numeral_2_eq_2)
  done

definition "push_on_stack_nat_else_time t s \<equiv> 
  (let
  cons_h' = push_on_stack_nat_n s;
  t = t + 2;
  cons_t' = 0;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;
  push_on_stack_nat_cons_res = cons_ret cons_ret_state;
  t = t + 2;

  nth_nat_n' = 1;
  t = t + 2;
  nth_nat_x' = push_on_stack_nat_c s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;
  push_on_stack_nat_nth_nat_ret_one = nth_nat_ret nth_nat_ret_state;
  t = t + 2;

  nth_nat_n' = 2;
  t = t + 2;
  nth_nat_x' = push_on_stack_nat_c s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  t = t + 2;
  cons_t' = push_on_stack_nat_cons_res;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  cons_h' = push_on_stack_nat_nth_nat_ret_one;
  t = t + 2;
  cons_t' = cons_ret cons_ret_state;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  cons_h' = 9;
  t = t + 2;
  cons_t' = cons_ret cons_ret_state;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  cons_h' = cons_ret cons_ret_state;
  t = t + 2;
  cons_t' = push_on_stack_nat_s s;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  push_on_stack_nat_ret' = cons_ret cons_ret_state;
  t = t + 2;
  ret = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c s,
        push_on_stack_nat_n = push_on_stack_nat_n s,
        push_on_stack_nat_s = push_on_stack_nat_s s,
        push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>
in
  t)"

definition "push_on_stack_nat_else_IMP_Minus \<equiv>
  (cons_prefix @ cons_h_str) ::= A (V push_on_stack_nat_n_str);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  push_on_stack_nat_cons_res ::= A (V (cons_prefix @ cons_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 1);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V push_on_stack_nat_c_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  push_on_stack_nat_nth_nat_ret_one ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 2);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V push_on_stack_nat_c_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V push_on_stack_nat_cons_res);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V push_on_stack_nat_nth_nat_ret_one);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (N 9);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V push_on_stack_nat_s_str);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  push_on_stack_nat_ret_str ::= A (V (cons_prefix @ cons_ret_str))
"

abbreviation "push_on_stack_nat_IMP_vars_else \<equiv> push_on_stack_nat_IMP_vars 
  \<union> {push_on_stack_nat_nth_nat_ret_one, push_on_stack_nat_cons_res}"

lemma push_on_stack_nat_else_IMP_Minus_correct_function:
  "(invoke_subprogram p push_on_stack_nat_else_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p push_on_stack_nat_ret_str)
      = push_on_stack_nat_ret
          (push_on_stack_nat_else (push_on_stack_nat_imp_to_HOL_state p s))"
   apply (subst push_on_stack_nat_else_def)
   apply (simp only: push_on_stack_nat_else_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
   subgoal premises p using p(31) by fastforce 
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
   subgoal premises p using p(33) by fastforce 
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
   subgoal premises p using p(35) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
   subgoal premises p using p(37) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
   subgoal premises p using p(39) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
   subgoal premises p using p(41) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
   subgoal premises p using p(43) by fastforce
   apply (force simp:
      push_on_stack_nat_imp_to_HOL_state_def cons_imp_to_HOL_state_def 
      nth_nat_imp_to_HOL_state_def Let_def)
   done


lemma push_on_stack_nat_else_IMP_Minus_correct_time:
  "(invoke_subprogram p push_on_stack_nat_else_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = push_on_stack_nat_else_time 0 (push_on_stack_nat_imp_to_HOL_state p s)"
  apply (subst push_on_stack_nat_else_time_def)
  apply (simp only: push_on_stack_nat_else_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
  subgoal premises p using p(61) by fastforce 
  apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
  subgoal premises p using p(63) by fastforce 
  apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
  subgoal premises p using p(65) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
  subgoal premises p using p(67) by fastforce 
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
  subgoal premises p using p(69) by fastforce 
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
  subgoal premises p using p(71) by fastforce 
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
  subgoal premises p using p(73) by fastforce
  apply (force simp:
      push_on_stack_nat_imp_to_HOL_state_def cons_imp_to_HOL_state_def 
      nth_nat_imp_to_HOL_state_def Let_def)
  done

paragraph if_eq_three

definition "push_on_stack_nat_eq_three s \<equiv> 
  (let
  cons_h' = push_on_stack_nat_n s;
  cons_t' = 0;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  push_on_stack_nat_cons_res = cons_ret cons_ret_state;

  nth_nat_n' = 1;
  nth_nat_x' = push_on_stack_nat_c s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  push_on_stack_nat_nth_nat_ret_one = nth_nat_ret nth_nat_ret_state;

  nth_nat_n' = 2;
  nth_nat_x' = push_on_stack_nat_c s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  push_on_stack_nat_nth_nat_ret_two = nth_nat_ret nth_nat_ret_state;
  
  nth_nat_n' = 3;
  nth_nat_x' = push_on_stack_nat_c s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  cons_t' = push_on_stack_nat_cons_res;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = push_on_stack_nat_nth_nat_ret_two;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = push_on_stack_nat_nth_nat_ret_one;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = 6;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = cons_ret cons_ret_state;
  cons_t' = push_on_stack_nat_s s;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  push_on_stack_nat_ret' = cons_ret cons_ret_state;
  ret = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c s,
        push_on_stack_nat_n = push_on_stack_nat_n s,
        push_on_stack_nat_s = push_on_stack_nat_s s,
        push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>
in
  ret)"

lemma push_on_stack_nat_eq_three_imp_correct[let_function_correctness]:
  "push_on_stack_nat_ret (push_on_stack_nat_eq_three s) = 
    (6## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
     (nth_nat (Suc (Suc (Suc 0))) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s)"
  unfolding push_on_stack_nat_eq_three_def
  apply (simp add: nth_nat_imp_correct cons_imp_correct Let_def numeral_2_eq_2 numeral_3_eq_3)
  done

definition "push_on_stack_nat_eq_three_time t s \<equiv> 
  (let
  cons_h' = push_on_stack_nat_n s;
  t = t + 2;
  cons_t' = 0;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;
  push_on_stack_nat_cons_res = cons_ret cons_ret_state;
  t = t + 2;

  nth_nat_n' = 1;
  t = t + 2;
  nth_nat_x' = push_on_stack_nat_c s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;
  push_on_stack_nat_nth_nat_ret_one = nth_nat_ret nth_nat_ret_state;
  t = t + 2;

  nth_nat_n' = 2;
  t = t + 2;
  nth_nat_x' = push_on_stack_nat_c s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;
  push_on_stack_nat_nth_nat_ret_two = nth_nat_ret nth_nat_ret_state;
  t = t + 2;
  
  nth_nat_n' = 3;
  t = t + 2;
  nth_nat_x' = push_on_stack_nat_c s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  t = t + 2;
  cons_t' = push_on_stack_nat_cons_res;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  cons_h' = push_on_stack_nat_nth_nat_ret_two;
  t = t + 2;
  cons_t' = cons_ret cons_ret_state;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  cons_h' = push_on_stack_nat_nth_nat_ret_one;
  t = t + 2;
  cons_t' = cons_ret cons_ret_state;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  cons_h' = 6;
  t = t + 2;
  cons_t' = cons_ret cons_ret_state;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  cons_h' = cons_ret cons_ret_state;
  t = t + 2;
  cons_t' = push_on_stack_nat_s s;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  push_on_stack_nat_ret' = cons_ret cons_ret_state;
  t = t + 2;
  ret = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c s,
        push_on_stack_nat_n = push_on_stack_nat_n s,
        push_on_stack_nat_s = push_on_stack_nat_s s,
        push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>
in
  t)"

definition "push_on_stack_nat_eq_three_IMP_Minus \<equiv>
  (cons_prefix @ cons_h_str) ::= A (V push_on_stack_nat_n_str);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  push_on_stack_nat_cons_res ::= A (V (cons_prefix @ cons_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 1);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V push_on_stack_nat_c_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  push_on_stack_nat_nth_nat_ret_one ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 2);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V push_on_stack_nat_c_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  push_on_stack_nat_nth_nat_ret_two ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 3);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V push_on_stack_nat_c_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V push_on_stack_nat_cons_res);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V push_on_stack_nat_nth_nat_ret_two);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V push_on_stack_nat_nth_nat_ret_one);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (N 6);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V push_on_stack_nat_s_str);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  push_on_stack_nat_ret_str ::= A (V (cons_prefix @ cons_ret_str))
"

abbreviation "push_on_stack_nat_IMP_vars_eq_three \<equiv> push_on_stack_nat_IMP_vars 
  \<union> {push_on_stack_nat_nth_nat_ret_one, push_on_stack_nat_nth_nat_ret_two, 
     push_on_stack_nat_cons_res}"

lemma push_on_stack_nat_eq_three_IMP_Minus_correct_function:
  "(invoke_subprogram p push_on_stack_nat_eq_three_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p push_on_stack_nat_ret_str)
      = push_on_stack_nat_ret
          (push_on_stack_nat_eq_three (push_on_stack_nat_imp_to_HOL_state p s))"
   apply (subst push_on_stack_nat_eq_three_def)
   apply (simp only: push_on_stack_nat_eq_three_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(40) by fastforce 
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(42) by fastforce 
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(44) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(46) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(48) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(50) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(52) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(54) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(56) by fastforce
   apply (force simp:
      push_on_stack_nat_imp_to_HOL_state_def cons_imp_to_HOL_state_def 
      nth_nat_imp_to_HOL_state_def Let_def)
   done 


lemma push_on_stack_nat_eq_three_IMP_Minus_correct_time:
  "(invoke_subprogram p push_on_stack_nat_eq_three_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = push_on_stack_nat_eq_three_time 0 (push_on_stack_nat_imp_to_HOL_state p s)"
  apply (subst push_on_stack_nat_eq_three_time_def)
  apply (simp only: push_on_stack_nat_eq_three_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(79) by fastforce 
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(81) by fastforce 
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(83) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(85) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(87) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(89) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(91) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(93) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(95) by fastforce
  apply (force simp: 
      push_on_stack_nat_imp_to_HOL_state_def cons_imp_to_HOL_state_def 
      nth_nat_imp_to_HOL_state_def Let_def)
  done

paragraph separations_of_nested_ifs

definition  "push_on_stack_nat_sub_branch_aux1 s \<equiv> 
       (let
          hd_xs' = push_on_stack_nat_c s;
          hd_ret' = 0;
          hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
          hd_ret_state = hd_imp hd_state;
          push_on_stack_nat_hd_c = hd_ret hd_ret_state;
          NOTEQUAL_neq_zero_a' = push_on_stack_nat_hd_c;
          NOTEQUAL_neq_zero_b' = 2;
          NOTEQUAL_neq_zero_ret' = 0;
          NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                                    NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                                    NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
          NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
          push_on_stack_nat_cond_three = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state)
        in 
          (if push_on_stack_nat_cond_three \<noteq> 0
                then push_on_stack_nat_else s
                else push_on_stack_nat_eq_two s))"

lemma push_on_stack_nat_sub_branch_aux1_imp_correct:
  "push_on_stack_nat_ret (push_on_stack_nat_sub_branch_aux1 s) = 
    (if (hd_nat (push_on_stack_nat_c s)) \<noteq>2
           then (9## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s)
           else (3## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s))"
  apply (subst push_on_stack_nat_sub_branch_aux1_def)
  apply (simp add: NOTEQUAL_neq_zero_imp_correct hd_imp_correct
   push_on_stack_nat_eq_one_imp_correct push_on_stack_nat_eq_two_imp_correct
   push_on_stack_nat_else_imp_correct
   Let_def)
  done

definition "push_on_stack_nat_sub_branch_aux1_IMP_Minus \<equiv>
  (hd_prefix @ hd_xs_str) ::= A (V push_on_stack_nat_c_str);;
  (hd_prefix @ hd_ret_str) ::= A (N 0);;
  invoke_subprogram hd_prefix hd_IMP_Minus;;
  push_on_stack_nat_hd_c ::= A (V (hd_prefix @ hd_ret_str));;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_a_str) ::= A (V push_on_stack_nat_hd_c);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_b_str) ::= A (N 2);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str) ::= A (N 0);;
  invoke_subprogram NOTEQUAL_neq_zero_prefix NOTEQUAL_neq_zero_IMP_Minus;;
  push_on_stack_nat_cond_three ::= A (V (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str));;
  (IF push_on_stack_nat_cond_three \<noteq>0
    THEN push_on_stack_nat_else_IMP_Minus
    ELSE push_on_stack_nat_eq_two_IMP_Minus)
  "
definition "push_on_stack_nat_sub_branch_aux1_time t s \<equiv> 
    (let
       hd_xs' = push_on_stack_nat_c s;
       t = t + 2;
       hd_ret' = 0;
       t = t + 2;
       hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
       hd_ret_state = hd_imp hd_state;
       t = t + hd_imp_time 0 hd_state;
       push_on_stack_nat_hd_c = hd_ret hd_ret_state;
       t = t + 2;
       NOTEQUAL_neq_zero_a' = push_on_stack_nat_hd_c;
       t = t + 2;
       NOTEQUAL_neq_zero_b' = 2;
       t = t + 2;
       NOTEQUAL_neq_zero_ret' = 0;
       t = t + 2;
       NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                                 NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                                 NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
       NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
       t = t + NOTEQUAL_neq_zero_imp_time 0 NOTEQUAL_neq_zero_state;
       push_on_stack_nat_cond_three = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state);
       t = t + 2
       in (if push_on_stack_nat_cond_three \<noteq> 0
                then 
                let
                 t = t + 1;
                 t = t + push_on_stack_nat_else_time 0 s
                in
                 t
                else 
                let
                 t = t + 1;
                 t = t + push_on_stack_nat_eq_two_time 0 s
                in
                 t))"

lemma push_on_stack_nat_sub_branch_aux1_IMP_Minus_correct_function:
  "(invoke_subprogram p push_on_stack_nat_sub_branch_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p push_on_stack_nat_ret_str)
      = push_on_stack_nat_ret
          (push_on_stack_nat_sub_branch_aux1 (push_on_stack_nat_imp_to_HOL_state p s))"
  apply (subst push_on_stack_nat_sub_branch_aux1_def)
  apply (simp only: push_on_stack_nat_sub_branch_aux1_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule hd_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(10) by fastforce
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(12) by fastforce
  apply (erule If_E)
    subgoal
      apply (fastforce dest!: push_on_stack_nat_else_IMP_Minus_correct_function 
      simp: push_on_stack_nat_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def
          hd_imp_to_HOL_state_def Let_def)
    done 
    subgoal
     apply (fastforce dest!: push_on_stack_nat_eq_two_IMP_Minus_correct_function 
      simp: push_on_stack_nat_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def
          hd_imp_to_HOL_state_def Let_def)
    done
  done

lemma push_on_stack_nat_sub_branch_aux1_IMP_Minus_correct_time:
  "(invoke_subprogram p push_on_stack_nat_sub_branch_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
    t = push_on_stack_nat_sub_branch_aux1_time 0 
           (push_on_stack_nat_imp_to_HOL_state p s)"
  apply (subst push_on_stack_nat_sub_branch_aux1_time_def)
  apply (simp only: push_on_stack_nat_sub_branch_aux1_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule hd_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(19) by fastforce
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(21) by fastforce
  apply (erule If_tE)
    subgoal
      apply (fastforce dest!: push_on_stack_nat_else_IMP_Minus_correct_time
      simp: push_on_stack_nat_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def
          hd_imp_to_HOL_state_def Let_def)
    done 
    subgoal
     apply (fastforce dest!: push_on_stack_nat_eq_two_IMP_Minus_correct_time 
      simp: push_on_stack_nat_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def
          hd_imp_to_HOL_state_def Let_def)
    done
  done

  definition "push_on_stack_nat_sub_branch_aux2 s \<equiv> 
    (let
       hd_xs' = push_on_stack_nat_c s;
       hd_ret' = 0;
       hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
       hd_ret_state = hd_imp hd_state;
       push_on_stack_nat_hd_c = hd_ret hd_ret_state;
       NOTEQUAL_neq_zero_a' = push_on_stack_nat_hd_c;
       NOTEQUAL_neq_zero_b' = 1;
       NOTEQUAL_neq_zero_ret' = 0;
       NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                                 NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                                 NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
       NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
       push_on_stack_nat_cond_two = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state)
       in (if push_on_stack_nat_cond_two \<noteq> 0
          then push_on_stack_nat_sub_branch_aux1 s
          else push_on_stack_nat_eq_one s))"


lemma push_on_stack_nat_sub_branch_aux2_imp_correct:
  "push_on_stack_nat_ret (push_on_stack_nat_sub_branch_aux2 s) = 
    (if (hd_nat (push_on_stack_nat_c s)) \<noteq>1
     then (if (hd_nat (push_on_stack_nat_c s)) \<noteq>2
           then (9## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s)
           else (3## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s))
     else (2## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s))"
  apply (subst push_on_stack_nat_sub_branch_aux2_def)
  apply (simp add: NOTEQUAL_neq_zero_imp_correct hd_imp_correct
   push_on_stack_nat_eq_one_imp_correct push_on_stack_nat_eq_two_imp_correct
   push_on_stack_nat_else_imp_correct push_on_stack_nat_sub_branch_aux1_imp_correct
   Let_def)
  done

definition "push_on_stack_nat_sub_branch_aux2_IMP_Minus \<equiv>
  (hd_prefix @ hd_xs_str) ::= A (V push_on_stack_nat_c_str);;
  (hd_prefix @ hd_ret_str) ::= A (N 0);;
  invoke_subprogram hd_prefix hd_IMP_Minus;;
  push_on_stack_nat_hd_c ::= A (V (hd_prefix @ hd_ret_str));;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_a_str) ::= A (V push_on_stack_nat_hd_c);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_b_str) ::= A (N 1);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str) ::= A (N 0);;
  invoke_subprogram NOTEQUAL_neq_zero_prefix NOTEQUAL_neq_zero_IMP_Minus;;
  push_on_stack_nat_cond_two ::= A (V (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str));;
  (IF push_on_stack_nat_cond_two \<noteq>0
  THEN push_on_stack_nat_sub_branch_aux1_IMP_Minus
  ELSE push_on_stack_nat_eq_one_IMP_Minus)"


lemma push_on_stack_nat_sub_branch_aux2_IMP_Minus_correct_function:
  "(invoke_subprogram p push_on_stack_nat_sub_branch_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p push_on_stack_nat_ret_str)
      = push_on_stack_nat_ret
          (push_on_stack_nat_sub_branch_aux2 (push_on_stack_nat_imp_to_HOL_state p s))"
  apply (subst push_on_stack_nat_sub_branch_aux2_def)
  apply (simp only: push_on_stack_nat_sub_branch_aux2_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule hd_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(10) by fastforce
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(12) by fastforce
  apply (erule If_E)
    subgoal 
      apply (fastforce dest!: push_on_stack_nat_sub_branch_aux1_IMP_Minus_correct_function 
      simp: push_on_stack_nat_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def
      hd_imp_to_HOL_state_def Let_def)
    done 
    subgoal 
    apply (fastforce dest!: push_on_stack_nat_eq_one_IMP_Minus_correct_function 
      simp: push_on_stack_nat_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def
      hd_imp_to_HOL_state_def Let_def)
    done
  done

definition "push_on_stack_nat_sub_branch_aux2_time t s \<equiv> 
    (let
       hd_xs' = push_on_stack_nat_c s;
       t = t + 2;
       hd_ret' = 0;
       t = t + 2;
       hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
       hd_ret_state = hd_imp hd_state;
       t = t + hd_imp_time 0 hd_state;
       push_on_stack_nat_hd_c = hd_ret hd_ret_state;
       t = t + 2;
       NOTEQUAL_neq_zero_a' = push_on_stack_nat_hd_c;
       t = t + 2;
       NOTEQUAL_neq_zero_b' = 1;
       t = t + 2;
       NOTEQUAL_neq_zero_ret' = 0;
       t = t + 2;
       NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                                 NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                                 NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
       NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
       t = t + NOTEQUAL_neq_zero_imp_time 0 NOTEQUAL_neq_zero_state;
       push_on_stack_nat_cond_two = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state);
       t = t + 2
       in (if push_on_stack_nat_cond_two \<noteq> 0
          then 
            (let 
             t = t + 1;
             t = t + push_on_stack_nat_sub_branch_aux1_time 0 s
            in 
             t)
          else 
          let 
           t = t + 1;
           t = t + push_on_stack_nat_eq_one_time 0 s
          in
           t))"

lemma push_on_stack_nat_sub_branch_aux2_IMP_Minus_correct_time:
  "(invoke_subprogram p push_on_stack_nat_sub_branch_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = push_on_stack_nat_sub_branch_aux2_time 0 
           (push_on_stack_nat_imp_to_HOL_state p s)"
  apply (subst push_on_stack_nat_sub_branch_aux2_time_def)
  apply (simp only: push_on_stack_nat_sub_branch_aux2_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule hd_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(19) by fastforce
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(21) by fastforce
  apply (erule If_tE)
    subgoal 
    apply (fastforce dest!: push_on_stack_nat_sub_branch_aux1_IMP_Minus_correct_time simp:
            push_on_stack_nat_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def Let_def
            hd_imp_to_HOL_state_def)
    done
    subgoal 
    apply (fastforce dest!: push_on_stack_nat_eq_one_IMP_Minus_correct_time simp:
            push_on_stack_nat_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def Let_def
            hd_imp_to_HOL_state_def)
    done
  done

definition "push_on_stack_nat_sub_branch_aux3 s \<equiv> 
(let
  hd_xs' = push_on_stack_nat_c s;
  hd_ret' = 0;
  hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
  hd_ret_state = hd_imp hd_state;
  push_on_stack_nat_hd_c = hd_ret hd_ret_state;
  NOTEQUAL_neq_zero_a' = push_on_stack_nat_hd_c;
  NOTEQUAL_neq_zero_b' = 3;
  NOTEQUAL_neq_zero_ret' = 0;
  NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                            NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                            NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
  NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
  push_on_stack_nat_cond_one = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state)
 in
  (if push_on_stack_nat_cond_one \<noteq> 0
      then (push_on_stack_nat_sub_branch_aux2 s)
      else push_on_stack_nat_eq_three s))"

lemma push_on_stack_nat_sub_branch_aux3_imp_correct:
   "push_on_stack_nat_ret (push_on_stack_nat_sub_branch_aux3 s) =
    (if (hd_nat (push_on_stack_nat_c s)) \<noteq>3 
    then (if (hd_nat (push_on_stack_nat_c s)) \<noteq>1
     then (if (hd_nat (push_on_stack_nat_c s)) \<noteq>2
           then (9## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s)
           else (3## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s))
     else (2## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s))
    else (6## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
       (nth_nat (Suc (Suc 0))(push_on_stack_nat_c s)) ## 
       (nth_nat (Suc (Suc (Suc 0))) (push_on_stack_nat_c s)) 
       ## (push_on_stack_nat_n s)  ## 0) ## (push_on_stack_nat_s s)
    )"
  apply (subst push_on_stack_nat_sub_branch_aux3_def)
  apply (simp add: NOTEQUAL_neq_zero_imp_correct hd_imp_correct
   push_on_stack_nat_eq_three_imp_correct push_on_stack_nat_sub_branch_aux2_imp_correct
   Let_def)
  done

definition "push_on_stack_nat_sub_branch_aux3_IMP_Minus \<equiv> 
  (hd_prefix @ hd_xs_str) ::= A (V push_on_stack_nat_c_str);;
  (hd_prefix @ hd_ret_str) ::= A (N 0);;
  invoke_subprogram hd_prefix hd_IMP_Minus;;
  push_on_stack_nat_hd_c ::= A (V (hd_prefix @ hd_ret_str));;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_a_str) ::= A (V push_on_stack_nat_hd_c);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_b_str) ::= A (N 3);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str) ::= A (N 0);;
  invoke_subprogram NOTEQUAL_neq_zero_prefix NOTEQUAL_neq_zero_IMP_Minus;;
  push_on_stack_nat_cond_one ::= A (V (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str));;
  (IF push_on_stack_nat_cond_one \<noteq>0
  THEN push_on_stack_nat_sub_branch_aux2_IMP_Minus
  ELSE push_on_stack_nat_eq_three_IMP_Minus)"

definition "push_on_stack_nat_sub_branch_aux3_time t s \<equiv> 
(let
  hd_xs' = push_on_stack_nat_c s;
  t = t + 2;
  hd_ret' = 0;
  t = t + 2;
  hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
  hd_ret_state = hd_imp hd_state;
  t = t + hd_imp_time 0 hd_state;
  push_on_stack_nat_hd_c = hd_ret hd_ret_state;
  t = t + 2;
  NOTEQUAL_neq_zero_a' = push_on_stack_nat_hd_c;
  t = t + 2;
  NOTEQUAL_neq_zero_b' = 3;
  t = t + 2;
  NOTEQUAL_neq_zero_ret' = 0;
  t = t + 2;
  NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                            NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                            NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
  NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
  t = t + NOTEQUAL_neq_zero_imp_time 0 NOTEQUAL_neq_zero_state;
  push_on_stack_nat_cond_one = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state);
  t = t + 2
 in
  (if push_on_stack_nat_cond_one \<noteq> 0
      then 
        let 
         t = t + 1;
         t = t + push_on_stack_nat_sub_branch_aux2_time 0 s
        in t
      else 
       let 
        t = t + 1;
        t = t + push_on_stack_nat_eq_three_time 0 s
        in t))"

lemma push_on_stack_nat_sub_branch_aux3_IMP_Minus_correct_function:
  "(invoke_subprogram p push_on_stack_nat_sub_branch_aux3_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p push_on_stack_nat_ret_str)
      = push_on_stack_nat_ret
          (push_on_stack_nat_sub_branch_aux3 (push_on_stack_nat_imp_to_HOL_state p s))"
  apply (subst push_on_stack_nat_sub_branch_aux3_def)
  apply (simp only: push_on_stack_nat_sub_branch_aux3_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule hd_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(10) by fastforce
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(12) by fastforce
  apply (erule If_E)
    subgoal 
      apply (fastforce dest!:push_on_stack_nat_sub_branch_aux2_IMP_Minus_correct_function simp:  
      Let_def hd_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def push_on_stack_nat_imp_to_HOL_state_def)
      done
    subgoal 
    apply (fastforce dest!:push_on_stack_nat_eq_three_IMP_Minus_correct_function simp:  
      Let_def hd_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def push_on_stack_nat_imp_to_HOL_state_def)
    done 
  done 

lemma push_on_stack_nat_sub_branch_aux3_IMP_Minus_correct_time:
  "(invoke_subprogram p push_on_stack_nat_sub_branch_aux3_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = push_on_stack_nat_sub_branch_aux3_time 0 (push_on_stack_nat_imp_to_HOL_state p s)"
  apply (subst push_on_stack_nat_sub_branch_aux3_time_def)
  apply (simp only: push_on_stack_nat_sub_branch_aux3_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule hd_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(19) by fastforce
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(21) by fastforce
  apply (erule If_tE)
    subgoal 
      apply (fastforce dest!:push_on_stack_nat_sub_branch_aux2_IMP_Minus_correct_time simp:  
      Let_def hd_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def push_on_stack_nat_imp_to_HOL_state_def)
      done
    subgoal 
    apply (fastforce dest!:push_on_stack_nat_eq_three_IMP_Minus_correct_time simp:  
      Let_def hd_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def push_on_stack_nat_imp_to_HOL_state_def)
    done 
  done 

definition "push_on_stack_nat_state_upd s \<equiv> 
 (let
  hd_xs' = push_on_stack_nat_c s;
  hd_ret' = 0;
  hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
  hd_ret_state = hd_imp hd_state;
  push_on_stack_nat_hd_c = hd_ret hd_ret_state
 in
  (if push_on_stack_nat_hd_c \<noteq> 0
  then push_on_stack_nat_sub_branch_aux3 s
  else push_on_stack_nat_eq_zero s)
  )"

function push_on_stack_nat_imp::
  "push_on_stack_nat_state \<Rightarrow> push_on_stack_nat_state" where
  "push_on_stack_nat_imp s =
    (let 
      ret = push_on_stack_nat_state_upd s
    in 
     ret)"
  by simp+
termination
  by (relation "measure (\<lambda>s. push_on_stack_nat_c s)") simp

declare push_on_stack_nat_imp.simps[simp del]

lemma push_on_stack_nat_imp_correct:
   "push_on_stack_nat_ret (push_on_stack_nat_imp s) =
    push_on_stack_nat (push_on_stack_nat_c s) (push_on_stack_nat_n s) (push_on_stack_nat_s s)"
  apply (subst push_on_stack_nat_imp.simps)
  apply (subst push_on_stack_nat_def)
  apply (simp add: push_on_stack_nat_state_upd_def hd_imp_correct cons_imp_correct 
   NOTEQUAL_neq_zero_imp_correct 
    push_on_stack_nat_eq_zero_imp_correct
   push_on_stack_nat_sub_branch_aux3_imp_correct 
   Let_def split: if_splits)  
  done

definition "push_on_stack_nat_IMP_Minus \<equiv> 
 (hd_prefix @ hd_xs_str) ::= A (V push_on_stack_nat_c_str);;
 (hd_prefix @ hd_ret_str) ::= A (N 0);;
 invoke_subprogram hd_prefix hd_IMP_Minus;;
 push_on_stack_nat_hd_c ::= A (V (hd_prefix @ hd_ret_str));;
 IF push_on_stack_nat_hd_c \<noteq>0
  THEN  push_on_stack_nat_sub_branch_aux3_IMP_Minus
  ELSE push_on_stack_nat_eq_zero_IMP_Minus"

definition "push_on_stack_nat_state_upd_time t s\<equiv> 
(let
  hd_xs' = push_on_stack_nat_c s;
  t = t + 2;
  hd_ret' = 0;
  t = t + 2;
  hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
  hd_ret_state = hd_imp hd_state;
  t = t + hd_imp_time 0 hd_state;
  push_on_stack_nat_hd_c = hd_ret hd_ret_state;
  t = t + 2
 in
  (if push_on_stack_nat_hd_c \<noteq> 0
  then 
    let 
     t = t + 1;
     t = t + push_on_stack_nat_sub_branch_aux3_time 0 s
    in 
    t 
  else 
   let 
    t = t + 1;
    t = t + push_on_stack_nat_eq_zero_time 0 s
   in
    t)
  )"

function push_on_stack_nat_imp_time :: "nat \<Rightarrow> push_on_stack_nat_state \<Rightarrow> nat" where
  "push_on_stack_nat_imp_time t s =
    (let 
      ret = push_on_stack_nat_state_upd_time t s
    in 
     ret)"
  by auto
termination
  by (relation "measure (\<lambda>(t, s). push_on_stack_nat_c s)") simp

declare push_on_stack_nat_imp_time.simps[simp del]



lemma push_on_stack_nat_IMP_Minus_correct_function:
  "(invoke_subprogram p push_on_stack_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p push_on_stack_nat_ret_str)
      = push_on_stack_nat_ret
          (push_on_stack_nat_imp (push_on_stack_nat_imp_to_HOL_state p s))"
  apply (subst push_on_stack_nat_imp.simps)
  apply (simp only: push_on_stack_nat_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule hd_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(5) by fastforce
  apply (erule If_E)
    subgoal 
      apply (fastforce dest!:push_on_stack_nat_sub_branch_aux3_IMP_Minus_correct_function simp:  
      push_on_stack_nat_state_upd_def Let_def hd_imp_to_HOL_state_def push_on_stack_nat_imp_to_HOL_state_def)
      done 
    subgoal 
    apply (fastforce dest!:push_on_stack_nat_eq_zero_IMP_Minus_correct_function simp:  
      push_on_stack_nat_state_upd_def Let_def hd_imp_to_HOL_state_def push_on_stack_nat_imp_to_HOL_state_def)
    done 
  done 

lemma push_on_stack_nat_IMP_Minus_correct_time:
  "(invoke_subprogram p push_on_stack_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = push_on_stack_nat_imp_time 0 (push_on_stack_nat_imp_to_HOL_state p s)"
  apply (subst push_on_stack_nat_imp_time.simps)
  apply (simp only: push_on_stack_nat_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule hd_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(9) by fastforce
  apply (erule If_tE)
    subgoal 
      apply (fastforce dest!:push_on_stack_nat_sub_branch_aux3_IMP_Minus_correct_time
      simp: push_on_stack_nat_state_upd_time_def 
      Let_def hd_imp_to_HOL_state_def push_on_stack_nat_imp_to_HOL_state_def)
      done 
    subgoal 
    apply (fastforce dest!:push_on_stack_nat_eq_zero_IMP_Minus_correct_time simp:  
      push_on_stack_nat_state_upd_time_def Let_def hd_imp_to_HOL_state_def push_on_stack_nat_imp_to_HOL_state_def)
    done 
  done 

lemma push_on_stack_nat_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ push_on_stack_nat_prefix) push_on_stack_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix push_on_stack_nat_prefix v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def 
  by blast

lemma push_on_stack_nat_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) push_on_stack_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (push_on_stack_nat_imp_time 0 (push_on_stack_nat_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) push_on_stack_nat_ret_str) =
          push_on_stack_nat_ret (push_on_stack_nat_imp
                                        (push_on_stack_nat_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using push_on_stack_nat_IMP_Minus_correct_function 
       push_on_stack_nat_IMP_Minus_correct_time
       push_on_stack_nat_IMP_Minus_correct_effects set_mono_prefix
  by (smt (verit, ccfv_SIG) com_add_prefix_valid_subset com_only_vars)

subsection \<open>map_var_bit_to_var\<close>

subsubsection \<open>map_var_bit_to_var_aux\<close>

fun map_var_bit_to_var_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_var_bit_to_var_aux acc v n = ((var_bit_to_var_nat (prod_encode (v,hd_nat n)))## acc)"

record map_var_bit_to_var_aux_state =
  map_var_bit_to_var_aux_acc::nat
  map_var_bit_to_var_aux_v::nat
  map_var_bit_to_var_aux_n::nat
  map_var_bit_to_var_aux_ret::nat

abbreviation "map_var_bit_to_var_aux_prefix \<equiv> ''map_var_bit_to_var_aux.''"
abbreviation "map_var_bit_to_var_aux_acc_str \<equiv> ''acc''"
abbreviation "map_var_bit_to_var_aux_v_str \<equiv> ''v''"
abbreviation "map_var_bit_to_var_aux_n_str \<equiv> ''n''"
abbreviation "map_var_bit_to_var_aux_ret_str \<equiv> ''ret''"


function map_var_bit_to_var_aux_imp :: "map_var_bit_to_var_aux_state \<Rightarrow> map_var_bit_to_var_aux_state" where 
"map_var_bit_to_var_aux_imp s = 
(let
    hd_xs' = map_var_bit_to_var_aux_n s;
    hd_ret' = 0;
    hd_state = \<lparr>hd_xs = hd_xs',
                hd_ret = hd_ret'\<rparr>;
    hd_ret_state = hd_imp hd_state;

    prod_encode_a' = map_var_bit_to_var_aux_v s;
    prod_encode_b' = hd_ret hd_ret_state;
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
    cons_t' = map_var_bit_to_var_aux_acc s;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h',
                  cons_t = cons_t', 
                  cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    map_var_bit_to_var_aux_ret' = cons_ret cons_ret_state;
    
    tl_xs' = map_var_bit_to_var_aux_n s;
    tl_ret' = 0;
    tl_state = \<lparr>tl_xs = tl_xs', 
                tl_ret = tl_ret'\<rparr>;
    tl_ret_state = tl_imp tl_state;

    map_var_bit_to_var_aux_n' = tl_ret tl_ret_state;
    ret = \<lparr>map_var_bit_to_var_aux_acc = map_var_bit_to_var_aux_acc s,
          map_var_bit_to_var_aux_v = map_var_bit_to_var_aux_v s,
          map_var_bit_to_var_aux_n = map_var_bit_to_var_aux_n',
          map_var_bit_to_var_aux_ret = map_var_bit_to_var_aux_ret'\<rparr>
    in
     ret)
    " by simp+
    termination
    apply (relation "measure map_var_bit_to_var_aux_acc")
    apply simp 
    done 

declare map_var_bit_to_var_aux_imp.simps[simp del]

lemma map_var_bit_to_var_aux_imp_correct[let_function_correctness]:
"map_var_bit_to_var_aux_ret (map_var_bit_to_var_aux_imp s) = 
  map_var_bit_to_var_aux (map_var_bit_to_var_aux_acc s) (map_var_bit_to_var_aux_v s) (map_var_bit_to_var_aux_n s)
  \<and> map_var_bit_to_var_aux_n (map_var_bit_to_var_aux_imp s) = tl_nat (map_var_bit_to_var_aux_n s)"
apply (subst map_var_bit_to_var_aux_imp.simps)+
apply (auto simp add: hd_imp_correct prod_encode_imp_correct var_bit_to_var_tail_imp_correct cons_imp_correct
  tl_imp_correct)
  using subtail_var_to_var_bit
  by (simp add: subtail_var_bit_to_var)
 

function map_var_bit_to_var_aux_imp_time :: "nat \<Rightarrow> map_var_bit_to_var_aux_state \<Rightarrow> nat" where 
"map_var_bit_to_var_aux_imp_time t s = 
(let
    hd_xs' = map_var_bit_to_var_aux_n s;
    t = t + 2;
    hd_ret' = 0;
    t = t + 2;
    hd_state = \<lparr>hd_xs = hd_xs',
                hd_ret = hd_ret'\<rparr>;
    hd_ret_state = hd_imp hd_state;
    t = t + hd_imp_time 0 hd_state;

    prod_encode_a' = map_var_bit_to_var_aux_v s;
    t = t + 2;
    prod_encode_b' = hd_ret hd_ret_state;
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
    cons_t' = map_var_bit_to_var_aux_acc s;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h',
                  cons_t = cons_t', 
                  cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;
    map_var_bit_to_var_aux_ret' = cons_ret cons_ret_state;
    t = t + 2;

    tl_xs' = map_var_bit_to_var_aux_n s;
    t = t + 2;
    tl_ret' = 0;
    t = t + 2;
    tl_state = \<lparr>tl_xs = tl_xs', 
                tl_ret = tl_ret'\<rparr>;
    tl_ret_state = tl_imp tl_state;
    t = t + tl_imp_time 0 tl_state;

    map_var_bit_to_var_aux_n' = tl_ret tl_ret_state;
    t = t + 2;
    ret = \<lparr>map_var_bit_to_var_aux_acc = map_var_bit_to_var_aux_acc s,
          map_var_bit_to_var_aux_v = map_var_bit_to_var_aux_v s,
          map_var_bit_to_var_aux_n = map_var_bit_to_var_aux_n',
          map_var_bit_to_var_aux_ret = map_var_bit_to_var_aux_ret'\<rparr>
    in
     t)
    " by auto
    termination
    apply (relation "measure (map_var_bit_to_var_aux_acc \<circ> snd)")
    apply simp 
    done 

declare map_var_bit_to_var_aux_imp_time.simps[simp del]

definition  "map_var_bit_to_var_aux_IMP_Minus \<equiv> 
  (hd_prefix @ hd_xs_str) ::= (A (V map_var_bit_to_var_aux_n_str));;
  (hd_prefix @ hd_ret_str) ::= (A (N 0));;
  invoke_subprogram hd_prefix hd_IMP_Minus;;

  (prod_encode_prefix @ prod_encode_a_str) ::= (A (V map_var_bit_to_var_aux_v_str));;
  (prod_encode_prefix @ prod_encode_b_str) ::= (A (V (hd_prefix @ hd_ret_str)));;
  (prod_encode_prefix @ prod_encode_ret_str) ::= (A (N 0));;
  invoke_subprogram prod_encode_prefix prod_encode_IMP_Minus;;

  (var_bit_to_var_tail_prefix @ var_bit_to_var_tail_n_str) ::= (A (V (prod_encode_prefix @ prod_encode_ret_str)));;
  (var_bit_to_var_tail_prefix @ var_bit_to_var_tail_ret_str) ::= (A (N 0));;
  invoke_subprogram var_bit_to_var_tail_prefix var_bit_to_var_tail_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= (A (V (var_bit_to_var_tail_prefix @ var_bit_to_var_tail_ret_str)));;
  (cons_prefix @ cons_t_str) ::= (A (V map_var_bit_to_var_aux_acc_str));;
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  map_var_bit_to_var_aux_ret_str ::= (A (V (cons_prefix @ cons_ret_str)));;

  (tl_prefix @ tl_xs_str) ::= (A (V map_var_bit_to_var_aux_n_str));;
  (tl_prefix @ tl_ret_str) ::= (A (N 0));;
  invoke_subprogram tl_prefix tl_IMP_Minus;;

  map_var_bit_to_var_aux_n_str ::= (A (V (tl_prefix @ tl_ret_str)))
"

definition "map_var_bit_to_var_aux_imp_to_HOL_state p s =
  \<lparr>map_var_bit_to_var_aux_acc = (s (add_prefix p map_var_bit_to_var_aux_acc_str)),
  map_var_bit_to_var_aux_v = (s (add_prefix p map_var_bit_to_var_aux_v_str)),
  map_var_bit_to_var_aux_n = (s (add_prefix p map_var_bit_to_var_aux_n_str)),
  map_var_bit_to_var_aux_ret = (s (add_prefix p map_var_bit_to_var_aux_ret_str))\<rparr>"

lemmas map_var_bit_to_var_aux_state_translators =
  map_var_bit_to_var_aux_imp_to_HOL_state_def
  hd_imp_to_HOL_state_def
  prod_encode_imp_to_HOL_state_def
  var_bit_to_var_tail_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  tl_imp_to_HOL_state_def

abbreviation "map_var_bit_to_var_aux_IMP_vars \<equiv> {
  map_var_bit_to_var_aux_acc_str, map_var_bit_to_var_aux_v_str, 
  map_var_bit_to_var_aux_n_str, map_var_bit_to_var_aux_ret_str}"

lemma map_var_bit_to_var_aux_IMP_Minus_correct_function_ret:
  "(invoke_subprogram p map_var_bit_to_var_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p map_var_bit_to_var_aux_ret_str)
      = map_var_bit_to_var_aux_ret
          (map_var_bit_to_var_aux_imp (map_var_bit_to_var_aux_imp_to_HOL_state p s))"
apply (simp only: map_var_bit_to_var_aux_IMP_Minus_def prefix_simps)
apply (erule Seq_E)+
apply (erule  hd_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(19) by fastforce
apply (erule  prod_encode_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(21) by fastforce
apply (erule  var_bit_to_var_tail_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(23) by fastforce
apply (erule  cons_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(25) by fastforce
apply (erule  tl_IMP_Minus_correct[where vars="map_var_bit_to_var_aux_IMP_vars"])
subgoal premises p using p(27) by fastforce
apply (clarsimp simp add:
  map_var_bit_to_var_aux_state_translators Let_def map_var_bit_to_var_aux_imp.simps)
subgoal premises p
  using p(10) p(8) p(6) p(4) p(2) by force 
done 

lemma map_var_bit_to_var_aux_IMP_Minus_correct_function_n:
  "(invoke_subprogram p map_var_bit_to_var_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p map_var_bit_to_var_aux_n_str)
      = map_var_bit_to_var_aux_n
          (map_var_bit_to_var_aux_imp (map_var_bit_to_var_aux_imp_to_HOL_state p s))"
apply (simp only: map_var_bit_to_var_aux_IMP_Minus_def prefix_simps)
apply (erule Seq_E)+
apply (erule  hd_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(19) by fastforce
apply (erule  prod_encode_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(21) by fastforce
apply (erule  var_bit_to_var_tail_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(23) by fastforce
apply (erule  cons_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(25) by fastforce
apply (erule  tl_IMP_Minus_correct[where vars="map_var_bit_to_var_aux_IMP_vars"])
subgoal premises p using p(27) by fastforce
apply (clarsimp simp add:
  map_var_bit_to_var_aux_state_translators Let_def map_var_bit_to_var_aux_imp.simps)
subgoal premises p
  using p(10) p(8) p(6) p(4) p(2) by force 
done 

lemma map_var_bit_to_var_aux_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ map_var_bit_to_var_aux_pref) map_var_bit_to_var_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix map_var_bit_to_var_aux_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            


lemma map_var_bit_to_var_aux_IMP_Minus_correct_time:
  "(invoke_subprogram p map_var_bit_to_var_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = map_var_bit_to_var_aux_imp_time 0 (map_var_bit_to_var_aux_imp_to_HOL_state p s)"
apply (simp only: map_var_bit_to_var_aux_IMP_Minus_def prefix_simps)
apply (erule Seq_tE)+
apply (erule hd_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(37) by fastforce
apply (erule prod_encode_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(39) by fastforce
apply (erule var_bit_to_var_tail_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(41) by fastforce
apply (erule cons_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(43) by fastforce
apply (erule tl_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(45) by fastforce
apply (force simp: map_var_bit_to_var_aux_imp_time.simps 
  Let_def map_var_bit_to_var_aux_state_translators)
done 

lemma map_var_bit_to_var_aux_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) map_var_bit_to_var_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (map_var_bit_to_var_aux_imp_time 0 (map_var_bit_to_var_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) map_var_bit_to_var_aux_ret_str) =
          map_var_bit_to_var_aux_ret (map_var_bit_to_var_aux_imp
                                        (map_var_bit_to_var_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) map_var_bit_to_var_aux_n_str) =
          map_var_bit_to_var_aux_n (map_var_bit_to_var_aux_imp
                                        (map_var_bit_to_var_aux_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using map_var_bit_to_var_aux_IMP_Minus_correct_function_ret 
  map_var_bit_to_var_aux_IMP_Minus_correct_function_n
  by (auto simp: map_var_bit_to_var_aux_IMP_Minus_correct_time)
    (meson map_var_bit_to_var_aux_IMP_Minus_correct_effects set_mono_prefix) 

subsubsection \<open>map_var_bit_to_var_acc\<close>

fun map_var_bit_to_var_acc' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_var_bit_to_var_acc' acc v n = (if n \<noteq> 0 
   then (map_var_bit_to_var_acc' ((var_bit_to_var_nat (prod_encode (v,hd_nat n)))## acc) v (tl_nat n))
   else acc)"

lemma map_var_bit_to_var_acc'_imp_correct:
"map_var_bit_to_var_acc' acc v n = map_var_bit_to_var_acc acc v n"
proof (induction n arbitrary: acc v rule: less_induct)
  case (less x)
  then show ?case
  proof(cases x)
    case (Suc nat)
    have "tl_nat x < x" using Suc
      by simp
    then show ?thesis
      using less by force
  qed (simp)
qed

record map_var_bit_to_var_acc_state =
  map_var_bit_to_var_acc_acc::nat
  map_var_bit_to_var_acc_v::nat
  map_var_bit_to_var_acc_n::nat
  map_var_bit_to_var_acc_ret::nat

abbreviation "map_var_bit_to_var_acc_prefix \<equiv> ''map_var_bit_to_var_acc.''"
abbreviation "map_var_bit_to_var_acc_acc_str \<equiv> ''acc''"
abbreviation "map_var_bit_to_var_acc_v_str \<equiv> ''v''"
abbreviation "map_var_bit_to_var_acc_n_str \<equiv> ''n''"
abbreviation "map_var_bit_to_var_acc_ret_str \<equiv> ''ret''"

definition "map_var_bit_to_var_acc_state_upd s \<equiv>
  let
    map_var_bit_to_var_aux_acc' = map_var_bit_to_var_acc_acc s;
    map_var_bit_to_var_aux_v' = map_var_bit_to_var_acc_v s;
    map_var_bit_to_var_aux_n' = map_var_bit_to_var_acc_n s;
    map_var_bit_to_var_aux_ret' = 0;
    map_var_bit_to_var_aux_state = 
      \<lparr>map_var_bit_to_var_aux_acc = map_var_bit_to_var_aux_acc',
      map_var_bit_to_var_aux_v = map_var_bit_to_var_aux_v',
      map_var_bit_to_var_aux_n = map_var_bit_to_var_aux_n',
      map_var_bit_to_var_aux_ret = map_var_bit_to_var_aux_ret'\<rparr>;
    map_var_bit_to_var_aux_ret_state = 
        map_var_bit_to_var_aux_imp map_var_bit_to_var_aux_state;


    map_var_bit_to_var_acc_acc' = map_var_bit_to_var_aux_ret map_var_bit_to_var_aux_ret_state;
    map_var_bit_to_var_acc_n' = map_var_bit_to_var_aux_n map_var_bit_to_var_aux_ret_state;
    ret = \<lparr>map_var_bit_to_var_acc_acc = map_var_bit_to_var_acc_acc',
           map_var_bit_to_var_acc_v = map_var_bit_to_var_acc_v s,
           map_var_bit_to_var_acc_n = map_var_bit_to_var_acc_n',
           map_var_bit_to_var_acc_ret = map_var_bit_to_var_acc_ret s\<rparr>
    in ret
"

definition "map_var_bit_to_var_acc_imp_compute_loop_condition s \<equiv>
  (let
    condition = map_var_bit_to_var_acc_n s
   in condition
  )
"

definition "map_var_bit_to_var_acc_imp_after_loop s \<equiv>
  (let
    map_var_bit_to_var_acc_ret' = map_var_bit_to_var_acc_acc s;
    ret = \<lparr>map_var_bit_to_var_acc_acc = map_var_bit_to_var_acc_acc s,
           map_var_bit_to_var_acc_v = map_var_bit_to_var_acc_v s,
           map_var_bit_to_var_acc_n = map_var_bit_to_var_acc_n s,
           map_var_bit_to_var_acc_ret = map_var_bit_to_var_acc_ret'\<rparr>
   in ret
  )"

lemmas map_var_bit_to_var_acc_imp_subprogram_simps = 
  map_var_bit_to_var_acc_state_upd_def
  map_var_bit_to_var_acc_imp_compute_loop_condition_def
  map_var_bit_to_var_acc_imp_after_loop_def

function map_var_bit_to_var_acc_imp::
  "map_var_bit_to_var_acc_state \<Rightarrow> map_var_bit_to_var_acc_state" where
  "map_var_bit_to_var_acc_imp s =
  (if map_var_bit_to_var_acc_imp_compute_loop_condition s \<noteq> 0
   then
    let next_iteration = map_var_bit_to_var_acc_imp (map_var_bit_to_var_acc_state_upd s)
    in next_iteration
   else
    let ret = map_var_bit_to_var_acc_imp_after_loop s
    in ret
  )"
  by simp+
termination 
  apply (relation "measure map_var_bit_to_var_acc_n")
   apply (simp add: map_var_bit_to_var_acc_imp_subprogram_simps 
      map_var_bit_to_var_aux_imp_correct Let_def)+
  done

declare map_var_bit_to_var_acc_imp.simps [simp del]

lemma map_var_bit_to_var_acc_imp_correct[let_function_correctness]:
  "map_var_bit_to_var_acc_ret (map_var_bit_to_var_acc_imp s) =
    map_var_bit_to_var_acc' (map_var_bit_to_var_acc_acc s) 
  (map_var_bit_to_var_acc_v s) (map_var_bit_to_var_acc_n s)"
  apply (induction s rule: map_var_bit_to_var_acc_imp.induct)
  apply (subst map_var_bit_to_var_acc_imp.simps)
  apply (subst map_var_bit_to_var_acc'.simps)
  apply (simp del: map_var_bit_to_var_acc'.simps 
              add: map_var_bit_to_var_acc_imp_subprogram_simps Let_def 
                   fst_nat_fst'_nat snd_nat_snd'_nat snd'_imp_correct fst'_imp_correct
                   map_var_bit_to_var_aux_imp_correct tl_imp_correct)
  done            

definition "map_var_bit_to_var_acc_state_upd_time t s \<equiv>
  let
    map_var_bit_to_var_aux_acc' = map_var_bit_to_var_acc_acc s;
    t = t + 2;
    map_var_bit_to_var_aux_v' = map_var_bit_to_var_acc_v s;
    t = t + 2;
    map_var_bit_to_var_aux_n' = map_var_bit_to_var_acc_n s;
    t = t + 2;
    map_var_bit_to_var_aux_ret' = 0;
    t = t + 2;
    map_var_bit_to_var_aux_state = 
      \<lparr>map_var_bit_to_var_aux_acc = map_var_bit_to_var_aux_acc',
      map_var_bit_to_var_aux_v = map_var_bit_to_var_aux_v',
      map_var_bit_to_var_aux_n = map_var_bit_to_var_aux_n',
      map_var_bit_to_var_aux_ret = map_var_bit_to_var_aux_ret'\<rparr>;
    map_var_bit_to_var_aux_ret_state = 
        map_var_bit_to_var_aux_imp map_var_bit_to_var_aux_state;
    t = t + map_var_bit_to_var_aux_imp_time 0 map_var_bit_to_var_aux_state;

    map_var_bit_to_var_acc_acc' = map_var_bit_to_var_aux_ret map_var_bit_to_var_aux_ret_state;
    t = t + 2;
    map_var_bit_to_var_acc_n' = map_var_bit_to_var_aux_n map_var_bit_to_var_aux_ret_state;
    t = t + 2;
    ret = \<lparr>map_var_bit_to_var_acc_acc = map_var_bit_to_var_acc_acc',
           map_var_bit_to_var_acc_v = map_var_bit_to_var_acc_v s,
           map_var_bit_to_var_acc_n = map_var_bit_to_var_acc_n',
           map_var_bit_to_var_acc_ret = map_var_bit_to_var_acc_ret s\<rparr>
  in
    t
"

definition "map_var_bit_to_var_acc_imp_compute_loop_condition_time t s \<equiv>
  let
    condition = map_var_bit_to_var_acc_n s;
    t = t + 2
  in
    t
"

definition "map_var_bit_to_var_acc_imp_after_loop_time t s \<equiv>
  let
    map_var_bit_to_var_acc_ret' = map_var_bit_to_var_acc_acc s;
    t = t + 2;
    ret = \<lparr>map_var_bit_to_var_acc_acc = map_var_bit_to_var_acc_acc s,
           map_var_bit_to_var_acc_v = map_var_bit_to_var_acc_v s,
           map_var_bit_to_var_acc_n = map_var_bit_to_var_acc_n s,
           map_var_bit_to_var_acc_ret = map_var_bit_to_var_acc_ret'\<rparr>
  in
    t
"

lemmas map_var_bit_to_var_acc_imp_subprogram_time_simps = 
  map_var_bit_to_var_acc_state_upd_time_def
  map_var_bit_to_var_acc_imp_compute_loop_condition_time_def
  map_var_bit_to_var_acc_imp_after_loop_time_def
  map_var_bit_to_var_acc_imp_subprogram_simps

function map_var_bit_to_var_acc_imp_time::
  "nat \<Rightarrow> map_var_bit_to_var_acc_state \<Rightarrow> nat" where
  "map_var_bit_to_var_acc_imp_time t s =
  map_var_bit_to_var_acc_imp_compute_loop_condition_time 0 s +
  (if map_var_bit_to_var_acc_imp_compute_loop_condition s \<noteq> 0
    then
      (let
        t = t + 1;
        next_iteration =
          map_var_bit_to_var_acc_imp_time (t + map_var_bit_to_var_acc_state_upd_time 0 s)
                         (map_var_bit_to_var_acc_state_upd s)
       in next_iteration)
    else
      (let
        t = t + 2;
        ret = t + map_var_bit_to_var_acc_imp_after_loop_time 0 s
       in ret)
  )"
  by auto
termination
  apply (relation "measure (map_var_bit_to_var_acc_n \<circ> snd)")
  by (auto simp add: map_var_bit_to_var_acc_imp_subprogram_time_simps
        map_var_bit_to_var_aux_imp_correct Let_def)

declare map_var_bit_to_var_acc_imp_time.simps [simp del]            

lemma map_var_bit_to_var_acc_imp_time_acc:
  "(map_var_bit_to_var_acc_imp_time (Suc t) s) = Suc (map_var_bit_to_var_acc_imp_time t s)"
  by (induction t s rule: map_var_bit_to_var_acc_imp_time.induct)
    ((subst (1 2) map_var_bit_to_var_acc_imp_time.simps);
      (simp add: map_var_bit_to_var_acc_state_upd_def))            

lemma map_var_bit_to_var_acc_imp_time_acc_2_aux:
  "(map_var_bit_to_var_acc_imp_time t s) = t + (map_var_bit_to_var_acc_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: map_var_bit_to_var_acc_imp_time_acc)+            

lemma map_var_bit_to_var_acc_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (map_var_bit_to_var_acc_imp_time t s) = t + (map_var_bit_to_var_acc_imp_time 0 s)"
  by (rule map_var_bit_to_var_acc_imp_time_acc_2_aux)            

lemma map_var_bit_to_var_acc_imp_time_acc_3:
  "(map_var_bit_to_var_acc_imp_time (a + b) s) = a + (map_var_bit_to_var_acc_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: map_var_bit_to_var_acc_imp_time_acc)+            

abbreviation "map_var_bit_to_var_acc_while_cond \<equiv> ''condition''"

definition "map_var_bit_to_var_acc_IMP_init_while_cond \<equiv>
  \<comment> \<open>condition = map_var_bit_to_var_acc_n s\<close>
  map_var_bit_to_var_acc_while_cond ::= A (V map_var_bit_to_var_acc_n_str)
"

definition "map_var_bit_to_var_acc_IMP_loop_body \<equiv>
 (map_var_bit_to_var_aux_prefix @ map_var_bit_to_var_aux_acc_str)
   ::= A (V map_var_bit_to_var_acc_acc_str);;
 (map_var_bit_to_var_aux_prefix @ map_var_bit_to_var_aux_v_str)
   ::= A (V map_var_bit_to_var_acc_v_str);;
 (map_var_bit_to_var_aux_prefix @ map_var_bit_to_var_aux_n_str)
   ::= A (V map_var_bit_to_var_acc_n_str);;
 (map_var_bit_to_var_aux_prefix @ map_var_bit_to_var_aux_ret_str)
   ::= A (N 0);;
 invoke_subprogram map_var_bit_to_var_aux_prefix map_var_bit_to_var_aux_IMP_Minus;;
  
  (map_var_bit_to_var_acc_acc_str) ::= (A (V (map_var_bit_to_var_aux_prefix 
                                             @ map_var_bit_to_var_aux_ret_str)));;
  (map_var_bit_to_var_acc_n_str) ::=  (A (V (map_var_bit_to_var_aux_prefix 
                                             @ map_var_bit_to_var_aux_n_str)))
"

definition "map_var_bit_to_var_acc_IMP_after_loop \<equiv>
  (map_var_bit_to_var_acc_ret_str) ::= (A (V map_var_bit_to_var_acc_acc_str))
  \<comment> \<open>ret = \<lparr>map_var_bit_to_var_acc_acc = map_var_bit_to_var_acc_acc',\<close>
  \<comment> \<open>       map_var_bit_to_var_acc_v = map_var_bit_to_var_acc_v',\<close>
  \<comment> \<open>       map_var_bit_to_var_acc_n = map_var_bit_to_var_acc_n',\<close>
  \<comment> \<open>       map_var_bit_to_var_acc_ret = map_var_bit_to_var_acc_ret'\<rparr>\<close>
"

definition map_var_bit_to_var_acc_IMP_Minus where
  "map_var_bit_to_var_acc_IMP_Minus \<equiv>
  map_var_bit_to_var_acc_IMP_init_while_cond;;
  WHILE map_var_bit_to_var_acc_while_cond \<noteq>0 DO (
    map_var_bit_to_var_acc_IMP_loop_body;;
    map_var_bit_to_var_acc_IMP_init_while_cond
  );;
  map_var_bit_to_var_acc_IMP_after_loop"

abbreviation "map_var_bit_to_var_acc_IMP_vars\<equiv>
  {map_var_bit_to_var_acc_while_cond,
    map_var_bit_to_var_acc_acc_str, map_var_bit_to_var_acc_v_str,
  map_var_bit_to_var_acc_n_str,  map_var_bit_to_var_acc_ret_str}"

lemmas map_var_bit_to_var_acc_IMP_subprogram_simps =
  map_var_bit_to_var_acc_IMP_init_while_cond_def
  map_var_bit_to_var_acc_IMP_loop_body_def
  map_var_bit_to_var_acc_IMP_after_loop_def

definition "map_var_bit_to_var_acc_imp_to_HOL_state p s =
  \<lparr>map_var_bit_to_var_acc_acc = (s (add_prefix p map_var_bit_to_var_acc_acc_str)),
  map_var_bit_to_var_acc_v = (s (add_prefix p map_var_bit_to_var_acc_v_str)),
  map_var_bit_to_var_acc_n = (s (add_prefix p map_var_bit_to_var_acc_n_str)),
  map_var_bit_to_var_acc_ret = (s (add_prefix p map_var_bit_to_var_acc_ret_str))\<rparr>"

lemmas map_var_bit_to_var_acc_state_translators =
  map_var_bit_to_var_acc_imp_to_HOL_state_def
  map_var_bit_to_var_aux_imp_to_HOL_state_def

lemmas map_var_bit_to_var_acc_complete_simps =
  map_var_bit_to_var_acc_IMP_subprogram_simps
  map_var_bit_to_var_acc_imp_subprogram_simps
  map_var_bit_to_var_acc_state_translators

lemma map_var_bit_to_var_acc_IMP_Minus_correct_function:
  "(invoke_subprogram p map_var_bit_to_var_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p map_var_bit_to_var_acc_ret_str)
      = map_var_bit_to_var_acc_ret
          (map_var_bit_to_var_acc_imp (map_var_bit_to_var_acc_imp_to_HOL_state p s))"
  apply(induction "map_var_bit_to_var_acc_imp_to_HOL_state p s" arbitrary: s s' t
    rule: map_var_bit_to_var_acc_imp.induct)
  apply(subst map_var_bit_to_var_acc_imp.simps)
  apply(simp only: map_var_bit_to_var_acc_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule While_tE)

    subgoal 
      apply (simp only: map_var_bit_to_var_acc_IMP_subprogram_simps prefix_simps)
      apply (clarsimp simp: map_var_bit_to_var_acc_complete_simps) 
      done 

  apply(erule Seq_E)+
  apply(dest_com_gen)

  subgoal
      apply(simp only: map_var_bit_to_var_acc_IMP_init_while_cond_def prefix_simps)
      by(fastforce simp add: map_var_bit_to_var_acc_complete_simps)

  subgoal
      apply(subst (asm) map_var_bit_to_var_acc_IMP_init_while_cond_def)
      apply(simp only: map_var_bit_to_var_acc_IMP_loop_body_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule map_var_bit_to_var_aux_IMP_Minus_correct[where vars = "map_var_bit_to_var_acc_IMP_vars"])
      subgoal premises p using p(12) by fastforce
      apply (force simp add: map_var_bit_to_var_acc_imp_subprogram_simps 
         map_var_bit_to_var_acc_state_translators Let_def)
      done 

  subgoal
      apply(simp only: map_var_bit_to_var_acc_IMP_init_while_cond_def prefix_simps
          map_var_bit_to_var_acc_IMP_loop_body_def)
      apply(erule Seq_E)+
      apply(erule map_var_bit_to_var_aux_IMP_Minus_correct[where vars = "map_var_bit_to_var_acc_IMP_vars"])
      subgoal premises p using p(12) by fastforce
      apply (force simp add: map_var_bit_to_var_acc_imp_subprogram_simps 
         map_var_bit_to_var_acc_state_translators Let_def split: if_splits)
      done 
  done 

lemma map_var_bit_to_var_acc_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ map_var_bit_to_var_acc_pref) map_var_bit_to_var_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix map_var_bit_to_var_acc_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemmas map_var_bit_to_var_acc_complete_time_simps =
  map_var_bit_to_var_acc_imp_subprogram_time_simps
  map_var_bit_to_var_acc_imp_time_acc
  map_var_bit_to_var_acc_imp_time_acc_2
  map_var_bit_to_var_acc_imp_time_acc_3
  map_var_bit_to_var_acc_state_translators

lemma map_var_bit_to_var_acc_IMP_Minus_correct_time:
  "(invoke_subprogram p map_var_bit_to_var_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = map_var_bit_to_var_acc_imp_time 0 (map_var_bit_to_var_acc_imp_to_HOL_state p s)"
  apply(induction "map_var_bit_to_var_acc_imp_to_HOL_state p s" arbitrary: s s' t
      rule: map_var_bit_to_var_acc_imp.induct)
  apply(subst map_var_bit_to_var_acc_imp_time.simps)
  apply(simp only: map_var_bit_to_var_acc_IMP_Minus_def prefix_simps)

  apply(erule Seq_tE)+
  apply(erule While_tE_time)
  subgoal
    apply(simp only: map_var_bit_to_var_acc_IMP_subprogram_simps prefix_simps
     map_var_bit_to_var_acc_complete_time_simps Let_def split: if_splits) 
    apply force
    done 

  apply(erule Seq_tE)+
  apply(simp add: add.assoc)
  apply(dest_com_gen_time)

  subgoal
    apply(simp only: map_var_bit_to_var_acc_IMP_init_while_cond_def prefix_simps)
    by(fastforce simp add: map_var_bit_to_var_acc_complete_simps)

  subgoal
    apply(subst (asm) map_var_bit_to_var_acc_IMP_init_while_cond_def)
    apply(simp only: map_var_bit_to_var_acc_IMP_loop_body_def prefix_simps)
    apply(erule Seq_tE)+
    apply(erule map_var_bit_to_var_aux_IMP_Minus_correct[where vars = "map_var_bit_to_var_acc_IMP_vars"])
    subgoal premises p using p(21) by fastforce
    apply (force simp: map_var_bit_to_var_acc_imp_subprogram_time_simps
        map_var_bit_to_var_acc_state_translators Let_def)
    done 

  subgoal
    apply(simp only: prefix_simps map_var_bit_to_var_acc_IMP_init_while_cond_def
        map_var_bit_to_var_acc_IMP_loop_body_def)
    apply(erule Seq_tE)+
    apply(erule map_var_bit_to_var_aux_IMP_Minus_correct[where vars = "map_var_bit_to_var_acc_IMP_vars"])
    subgoal premises p using p(21) by fastforce
    apply (clarsimp simp add: map_var_bit_to_var_acc_complete_time_simps Let_def)
    subgoal premises p 
      using p(10) 
      by (smt (z3) fun_upd_def list.inject list.simps(3) 
      map_var_bit_to_var_acc_imp_time_acc_2_aux same_append_eq)
    done  
  done   

lemma map_var_bit_to_var_acc_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) map_var_bit_to_var_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (map_var_bit_to_var_acc_imp_time 0 (map_var_bit_to_var_acc_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) map_var_bit_to_var_acc_ret_str) =
          map_var_bit_to_var_acc_ret (map_var_bit_to_var_acc_imp
                                        (map_var_bit_to_var_acc_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using map_var_bit_to_var_acc_IMP_Minus_correct_function
  by (auto simp: map_var_bit_to_var_acc_IMP_Minus_correct_time)
    (meson map_var_bit_to_var_acc_IMP_Minus_correct_effects set_mono_prefix) 

subsubsection \<open>map_var_bit_to_var_tail\<close>
record map_var_bit_to_var_tail_state =
map_var_bit_to_var_tail_v::nat
map_var_bit_to_var_tail_n::nat
map_var_bit_to_var_tail_ret::nat 

abbreviation "map_var_bit_to_var_tail_prefix \<equiv> ''map_var_bit_to_var_tail.''"
abbreviation "map_var_bit_to_var_tail_v_str \<equiv> ''v''"
abbreviation "map_var_bit_to_var_tail_n_str \<equiv> ''n''"
abbreviation "map_var_bit_to_var_tail_ret_str \<equiv> ''ret''"

function map_var_bit_to_var_tail_imp :: 
"map_var_bit_to_var_tail_state \<Rightarrow> map_var_bit_to_var_tail_state"where 
"map_var_bit_to_var_tail_imp s =
 (let 
   map_var_bit_to_var_acc_acc' = 0;
   map_var_bit_to_var_acc_v' = map_var_bit_to_var_tail_v s;
   map_var_bit_to_var_acc_n' = map_var_bit_to_var_tail_n s;
   map_var_bit_to_var_acc_ret' = 0;
   map_var_bit_to_var_acc_state = 
     \<lparr>map_var_bit_to_var_acc_acc = map_var_bit_to_var_acc_acc',
     map_var_bit_to_var_acc_v = map_var_bit_to_var_acc_v',
     map_var_bit_to_var_acc_n = map_var_bit_to_var_acc_n',
     map_var_bit_to_var_acc_ret = map_var_bit_to_var_acc_ret'\<rparr>;
  map_var_bit_to_var_acc_ret_state = map_var_bit_to_var_acc_imp map_var_bit_to_var_acc_state;

  reverse_nat_n' = map_var_bit_to_var_acc_ret map_var_bit_to_var_acc_ret_state;
  reverse_nat_ret' = 0;
  reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n',
                       reverse_nat_ret = reverse_nat_ret'\<rparr>;
  reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;
  map_var_bit_to_var_tail_ret' = reverse_nat_ret reverse_nat_ret_state;
  ret = \<lparr>map_var_bit_to_var_tail_v = map_var_bit_to_var_tail_v s,
        map_var_bit_to_var_tail_n = map_var_bit_to_var_tail_n s,
        map_var_bit_to_var_tail_ret = map_var_bit_to_var_tail_ret'\<rparr>
 in 
  ret)" by simp+
 termination 
 apply (relation "measure map_var_bit_to_var_tail_n")
 apply auto 
 done 

declare map_var_bit_to_var_tail_imp.simps[simp del]

lemma map_var_bit_to_var_tail_imp_correct[let_function_correctness]:
  "map_var_bit_to_var_tail_ret (map_var_bit_to_var_tail_imp s)
    = map_var_bit_to_var_tail (map_var_bit_to_var_tail_v s) (map_var_bit_to_var_tail_n s)"
apply (subst map_var_bit_to_var_tail_imp.simps)
apply auto
using  map_var_bit_to_var_tail_def reverse_nat_imp_correct 
map_var_bit_to_var_acc_imp_correct map_var_bit_to_var_acc'_imp_correct
by auto

function map_var_bit_to_var_tail_imp_time :: 
"nat \<Rightarrow> map_var_bit_to_var_tail_state \<Rightarrow> nat"where 
"map_var_bit_to_var_tail_imp_time t s =
 (let 
   map_var_bit_to_var_acc_acc' = 0;
   t = t + 2;
   map_var_bit_to_var_acc_v' = map_var_bit_to_var_tail_v s;
   t = t + 2;
   map_var_bit_to_var_acc_n' = map_var_bit_to_var_tail_n s;
   t = t + 2;
   map_var_bit_to_var_acc_ret' = 0;
   t = t + 2;
   map_var_bit_to_var_acc_state = 
     \<lparr>map_var_bit_to_var_acc_acc = map_var_bit_to_var_acc_acc',
     map_var_bit_to_var_acc_v = map_var_bit_to_var_acc_v',
     map_var_bit_to_var_acc_n = map_var_bit_to_var_acc_n',
     map_var_bit_to_var_acc_ret = map_var_bit_to_var_acc_ret'\<rparr>;
  map_var_bit_to_var_acc_ret_state = map_var_bit_to_var_acc_imp map_var_bit_to_var_acc_state;
  t = t + map_var_bit_to_var_acc_imp_time 0 map_var_bit_to_var_acc_state;

  reverse_nat_n' = map_var_bit_to_var_acc_ret map_var_bit_to_var_acc_ret_state;
  t = t + 2;
  reverse_nat_ret' = 0;
  t = t + 2;
  reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n',
                       reverse_nat_ret = reverse_nat_ret'\<rparr>;
  reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;
  t = t + reverse_nat_imp_time 0 reverse_nat_state;
  
  map_var_bit_to_var_tail_ret' = reverse_nat_ret reverse_nat_ret_state;
  t = t + 2;
  ret = \<lparr>map_var_bit_to_var_tail_v = map_var_bit_to_var_tail_v s,
        map_var_bit_to_var_tail_n = map_var_bit_to_var_tail_n s,
        map_var_bit_to_var_tail_ret = map_var_bit_to_var_tail_ret'\<rparr>
 in 
  t)" by auto
 termination 
 apply (relation "measure (map_var_bit_to_var_tail_n \<circ> snd)")
 apply auto 
 done 

declare map_var_bit_to_var_tail_imp_time.simps[simp del]

definition "map_var_bit_to_var_tail_IMP_Minus \<equiv> 
 (map_var_bit_to_var_acc_prefix @ map_var_bit_to_var_acc_acc_str) ::= A (N 0);;
 (map_var_bit_to_var_acc_prefix @ map_var_bit_to_var_acc_v_str) ::= A (V map_var_bit_to_var_tail_v_str);;
 (map_var_bit_to_var_acc_prefix @ map_var_bit_to_var_acc_n_str) ::= A (V map_var_bit_to_var_tail_n_str);;
 (map_var_bit_to_var_acc_prefix @ map_var_bit_to_var_acc_ret_str) ::= A (N 0);;
 invoke_subprogram map_var_bit_to_var_acc_prefix map_var_bit_to_var_acc_IMP_Minus;;

 (reverse_nat_prefix @ reverse_nat_n_str) ::= A (V (map_var_bit_to_var_acc_prefix @ map_var_bit_to_var_acc_ret_str));;
 (reverse_nat_prefix @ reverse_nat_ret_str) ::= A (N 0);;
 invoke_subprogram reverse_nat_prefix reverse_nat_IMP_Minus;;

 map_var_bit_to_var_tail_ret_str ::= A (V (reverse_nat_prefix @ reverse_nat_ret_str))
"

abbreviation "map_var_bit_to_var_tail_IMP_vars \<equiv> 
  {map_var_bit_to_var_tail_ret_str, map_var_bit_to_var_tail_n_str, map_var_bit_to_var_tail_v_str}"

definition "map_var_bit_to_var_tail_imp_to_HOL_state p s = 
\<lparr>  map_var_bit_to_var_tail_v = (s (add_prefix p map_var_bit_to_var_tail_v_str)),
  map_var_bit_to_var_tail_n = (s (add_prefix p map_var_bit_to_var_tail_n_str)),
  map_var_bit_to_var_tail_ret = (s (add_prefix p map_var_bit_to_var_tail_ret_str))\<rparr>"

lemmas map_var_bit_to_var_tail_state_translators = 
  map_var_bit_to_var_tail_imp_to_HOL_state_def
  map_var_bit_to_var_acc_imp_to_HOL_state_def
  reverse_nat_imp_to_HOL_state_def

lemma map_var_bit_to_var_tail_IMP_Minus_correct_function:
"(invoke_subprogram p map_var_bit_to_var_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p map_var_bit_to_var_tail_ret_str)
      = map_var_bit_to_var_tail_ret
          (map_var_bit_to_var_tail_imp (map_var_bit_to_var_tail_imp_to_HOL_state p s))"
apply (simp only: map_var_bit_to_var_tail_IMP_Minus_def prefix_simps)
apply (erule Seq_E)+
apply (erule map_var_bit_to_var_acc_IMP_Minus_correct[where vars=map_var_bit_to_var_tail_IMP_vars])
subgoal premises p using p(9) by fastforce
apply (erule reverse_nat_IMP_Minus_correct[where vars=map_var_bit_to_var_tail_IMP_vars])
subgoal premises p using p(11) by fastforce
apply (clarsimp simp add: map_var_bit_to_var_tail_state_translators Let_def
 map_var_bit_to_var_tail_imp.simps)
done 

lemma map_var_bit_to_var_tail_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ map_var_bit_to_var_tail_pref) map_var_bit_to_var_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix map_var_bit_to_var_tail_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            


lemma map_var_bit_to_var_tail_IMP_Minus_correct_time:
  "(invoke_subprogram p map_var_bit_to_var_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = map_var_bit_to_var_tail_imp_time 0 (map_var_bit_to_var_tail_imp_to_HOL_state p s)"
apply (simp only: map_var_bit_to_var_tail_IMP_Minus_def prefix_simps)
apply (erule Seq_tE)+
apply (erule map_var_bit_to_var_acc_IMP_Minus_correct[where vars=map_var_bit_to_var_tail_IMP_vars])
subgoal premises p using p(17) by fastforce
apply (erule reverse_nat_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(19) by fastforce
apply (force simp: map_var_bit_to_var_tail_imp_time.simps 
  Let_def map_var_bit_to_var_tail_state_translators)
done 

lemma map_var_bit_to_var_tail_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) map_var_bit_to_var_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (map_var_bit_to_var_tail_imp_time 0 (map_var_bit_to_var_tail_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) map_var_bit_to_var_tail_ret_str) =
          map_var_bit_to_var_tail_ret (map_var_bit_to_var_tail_imp
                                        (map_var_bit_to_var_tail_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using map_var_bit_to_var_tail_IMP_Minus_correct_function 
   map_var_bit_to_var_tail_IMP_Minus_correct_time
  by (meson com_add_prefix_valid_subset com_only_vars)

subsection var_bit_list_tail

record var_bit_list_tail_state = 
  var_bit_list_tail_n::nat
  var_bit_list_tail_v::nat
  var_bit_list_tail_ret::nat

abbreviation "var_bit_list_tail_prefix \<equiv> ''var_bit_list_tail.''"
abbreviation "var_bit_list_tail_n_str \<equiv> ''n''"
abbreviation "var_bit_list_tail_v_str \<equiv> ''v''"
abbreviation "var_bit_list_tail_ret_str \<equiv> ''ret''"

definition "var_bit_list_tail_state_upd s \<equiv>
(let
  list_less_tail_n' = var_bit_list_tail_n s;
  list_less_tail_ret' = 0;
  list_less_tail_state = \<lparr>list_less_tail_n = list_less_tail_n', list_less_tail_ret = list_less_tail_ret'\<rparr>;
  list_less_tail_ret_state = list_less_tail_imp list_less_tail_state;

  map_var_bit_to_var_tail_v' = var_bit_list_tail_v s;
  map_var_bit_to_var_tail_n' = list_less_tail_ret list_less_tail_ret_state;
  map_var_bit_to_var_tail_ret' = 0;
  map_var_bit_to_var_tail_state = 
    \<lparr>map_var_bit_to_var_tail_v = map_var_bit_to_var_tail_v',
    map_var_bit_to_var_tail_n = map_var_bit_to_var_tail_n',
    map_var_bit_to_var_tail_ret = map_var_bit_to_var_tail_ret'\<rparr>;
  map_var_bit_to_var_tail_ret_state = map_var_bit_to_var_tail_imp map_var_bit_to_var_tail_state;

  var_bit_list_tail_ret' = map_var_bit_to_var_tail_ret map_var_bit_to_var_tail_ret_state;
  ret = \<lparr>var_bit_list_tail_n = var_bit_list_tail_n s,
  var_bit_list_tail_v = var_bit_list_tail_v s,
  var_bit_list_tail_ret = var_bit_list_tail_ret'\<rparr>
in
 ret)
"

function var_bit_list_tail_imp ::
  "var_bit_list_tail_state \<Rightarrow> var_bit_list_tail_state" where
  "var_bit_list_tail_imp s =
  (let 
      ret = var_bit_list_tail_state_upd s
    in 
      ret
  )"
  by simp+
termination
  by (relation "measure var_bit_list_tail_n") simp

declare var_bit_list_tail_imp.simps [simp del]

lemma var_bit_list_tail_imp_correct[let_function_correctness]:
  "var_bit_list_tail_ret (var_bit_list_tail_imp s) =
    var_bit_list_nat (var_bit_list_tail_n s) (var_bit_list_tail_v s)"
  apply (simp only: var_bit_list_tail_imp.simps Let_def var_bit_list_tail_state_upd_def
  var_bit_list_tail_def subtail_var_bit_list[symmetric])
  apply (simp add: list_less_tail_imp_correct map_var_bit_to_var_tail_imp_correct)
  done 

function var_bit_list_tail_imp_time ::
  "nat \<Rightarrow> var_bit_list_tail_state \<Rightarrow> nat" where
  "var_bit_list_tail_imp_time t s =
  (let
  list_less_tail_n' = var_bit_list_tail_n s;
  t = t + 2;
  list_less_tail_ret' = 0;
  t = t + 2;
  list_less_tail_state = \<lparr>list_less_tail_n = list_less_tail_n', list_less_tail_ret = list_less_tail_ret'\<rparr>;
  list_less_tail_ret_state = list_less_tail_imp list_less_tail_state;
  t = t + list_less_tail_imp_time 0 list_less_tail_state;

  map_var_bit_to_var_tail_v' = var_bit_list_tail_v s;
  t = t + 2;
  map_var_bit_to_var_tail_n' = list_less_tail_ret list_less_tail_ret_state;
  t = t + 2;
  map_var_bit_to_var_tail_ret' = 0;
  t = t + 2;
  map_var_bit_to_var_tail_state = 
    \<lparr>map_var_bit_to_var_tail_v = map_var_bit_to_var_tail_v',
    map_var_bit_to_var_tail_n = map_var_bit_to_var_tail_n',
    map_var_bit_to_var_tail_ret = map_var_bit_to_var_tail_ret'\<rparr>;
  map_var_bit_to_var_tail_ret_state = map_var_bit_to_var_tail_imp map_var_bit_to_var_tail_state;
  t = t + map_var_bit_to_var_tail_imp_time 0 map_var_bit_to_var_tail_state;

  var_bit_list_tail_ret' = map_var_bit_to_var_tail_ret map_var_bit_to_var_tail_ret_state;
  t = t + 2;
  ret = \<lparr>var_bit_list_tail_n = var_bit_list_tail_n s,
  var_bit_list_tail_v = var_bit_list_tail_v s,
  var_bit_list_tail_ret = var_bit_list_tail_ret'\<rparr>
  in
      t
  )"
  by auto
termination
  by (relation "measure (var_bit_list_tail_n \<circ> snd)") simp

declare var_bit_list_tail_imp_time.simps [simp del]

lemma var_bit_list_tail_imp_time_acc:
  "(var_bit_list_tail_imp_time (Suc t) s) = Suc (var_bit_list_tail_imp_time t s)"
  by (induction t s rule: var_bit_list_tail_imp_time.induct)
    ((subst (1 2) var_bit_list_tail_imp_time.simps);
      (simp add: var_bit_list_tail_state_upd_def Let_def))            

lemma var_bit_list_tail_imp_time_acc_2_aux:
  "(var_bit_list_tail_imp_time t s) = t + (var_bit_list_tail_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: var_bit_list_tail_imp_time_acc)+            

lemma var_bit_list_tail_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (var_bit_list_tail_imp_time t s) = t + (var_bit_list_tail_imp_time 0 s)"
  by (rule var_bit_list_tail_imp_time_acc_2_aux)            

lemma var_bit_list_tail_imp_time_acc_3:
  "(var_bit_list_tail_imp_time (a + b) s) = a + (var_bit_list_tail_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: var_bit_list_tail_imp_time_acc)+            

definition var_bit_list_tail_IMP_Minus where
  "var_bit_list_tail_IMP_Minus \<equiv>
  (list_less_tail_prefix @ list_less_tail_n_str) ::= A (V var_bit_list_tail_n_str);;
  (list_less_tail_prefix @ list_less_tail_ret_str) ::= A (N 0);;
  invoke_subprogram list_less_tail_prefix list_less_tail_IMP_Minus;;

  (map_var_bit_to_var_tail_prefix @ map_var_bit_to_var_tail_n_str)
    ::= A (V (list_less_tail_prefix @ list_less_tail_ret_str));;
  (map_var_bit_to_var_tail_prefix @ map_var_bit_to_var_tail_v_str)
    ::= A (V var_bit_list_tail_v_str);;
  (map_var_bit_to_var_tail_prefix @ map_var_bit_to_var_tail_ret_str)
    ::= A (N 0);;
  invoke_subprogram map_var_bit_to_var_tail_prefix map_var_bit_to_var_tail_IMP_Minus;;

  var_bit_list_tail_ret_str 
    ::= A (V (map_var_bit_to_var_tail_prefix @ map_var_bit_to_var_tail_ret_str)) 
"

abbreviation "var_bit_list_tail_IMP_vars \<equiv>
  {var_bit_list_tail_n_str, var_bit_list_tail_v_str}"

definition "var_bit_list_tail_imp_to_HOL_state p s =
  \<lparr>var_bit_list_tail_n = (s (add_prefix p var_bit_list_tail_n_str)),
   var_bit_list_tail_v = (s (add_prefix p var_bit_list_tail_v_str)),
   var_bit_list_tail_ret = (s (add_prefix p var_bit_list_tail_ret_str))\<rparr>"

lemmas var_bit_list_tail_state_translators =
  var_bit_list_tail_imp_to_HOL_state_def
  list_less_tail_imp_to_HOL_state_def
  map_var_bit_to_var_tail_imp_to_HOL_state_def

lemma var_bit_list_tail_IMP_Minus_correct_function:
  "(invoke_subprogram p var_bit_list_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p var_bit_list_tail_ret_str)
      = var_bit_list_tail_ret
          (var_bit_list_tail_imp (var_bit_list_tail_imp_to_HOL_state p s))"
  apply(subst var_bit_list_tail_imp.simps)
  apply(simp only: var_bit_list_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule list_less_tail_IMP_Minus_correct[where vars = "var_bit_list_tail_IMP_vars"])
  subgoal premises p using p(8) by fastforce
  apply(erule map_var_bit_to_var_tail_IMP_Minus_correct[where vars = "var_bit_list_tail_IMP_vars"])
  subgoal premises p using p(10) by fastforce
  by(fastforce simp: var_bit_list_tail_state_translators
    var_bit_list_tail_state_upd_def)        

lemma var_bit_list_tail_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ var_bit_list_tail_pref) var_bit_list_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix var_bit_list_tail_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemma var_bit_list_tail_IMP_Minus_correct_time:
  "(invoke_subprogram p var_bit_list_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = var_bit_list_tail_imp_time 0 (var_bit_list_tail_imp_to_HOL_state p s)"
  apply(subst var_bit_list_tail_imp_time.simps)
  apply(simp only: var_bit_list_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule list_less_tail_IMP_Minus_correct[where vars = "var_bit_list_tail_IMP_vars"])
  subgoal premises p using p(15) by fastforce
  apply(erule map_var_bit_to_var_tail_IMP_Minus_correct[where vars = "var_bit_list_tail_IMP_vars"])
  subgoal premises p using p(17) by fastforce
  by(fastforce simp add: Let_def var_bit_list_tail_state_translators)        

lemma var_bit_list_tail_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) var_bit_list_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (var_bit_list_tail_imp_time 0 (var_bit_list_tail_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) var_bit_list_tail_ret_str) =
          var_bit_list_tail_ret (var_bit_list_tail_imp
                                        (var_bit_list_tail_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using var_bit_list_tail_IMP_Minus_correct_function
    var_bit_list_tail_IMP_Minus_correct_time
    var_bit_list_tail_IMP_Minus_correct_effects
  by (meson set_mono_prefix) 




 


end