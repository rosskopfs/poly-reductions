\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Filter_Defined_Acc_Call
  imports
    IMP_Minus.IMP_Calls
    Filter_Defined_Acc_Base
    IMP_Minus_Views.Let_To_IMP_Minus_Calls_Locale
    IMP_Minus_Views.Let_To_IMP_Minus_Calls_Tactics
begin

unbundle Com.no_com_syntax
unbundle IMP_Calls.com'_syntax

ML\<open>
  structure LT = Let_To_IMP_Minus_Calls_Tactics
  structure SCL = State_Cook_Levin_IMP_Minus_Calls
\<close>

definition "filter_defined_acc_IMP_Minus_Calls_init_while_cond \<equiv>
  \<comment> \<open>condition = filter_defined_acc_n s\<close>
  (filter_defined_acc_while_cond) ::= (A (V filter_defined_acc_n_str))
"

definition "filter_defined_acc_IMP_Minus_Calls_after_loop \<equiv>
  \<comment> \<open>filter_defined_acc_ret' = filter_defined_acc_acc s;\<close>
  filter_defined_acc_ret_str ::= (A (V filter_defined_acc_acc_str))
  \<comment> \<open>ret = \<lparr>
      filter_defined_acc_s = filter_defined_acc_s s,
      filter_defined_acc_acc = filter_defined_acc_acc s,
      filter_defined_acc_n = filter_defined_acc_n s,
      filter_defined_acc_ret = filter_defined_acc_ret'
    \<rparr>\<close>"

definition "filter_defined_acc_IMP_Minus_Calls_loop_body \<equiv>
  \<comment> \<open>hd_xs' = filter_defined_acc_n s;\<close>
  hd_xs_str ::= (A (V filter_defined_acc_n_str));;
  \<comment> \<open>hd_ret' = 0;\<close>
  hd_ret_str ::= (A (N 0));;
  \<comment> \<open>hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
     hd_ret_state = hd_imp hd_state;\<close>
  (CALL hd_IMP_Minus RETURN hd_ret_str);;
  \<comment> \<open>map_list_find_aux_xs' = filter_defined_acc_s s;
     map_list_find_aux_a' = hd_ret hd_ret_state;
     map_list_find_aux_ret' = 0;\<close>
  map_list_find_aux_xs_str ::= (A (V filter_defined_acc_s_str));;
  map_list_find_aux_a_str ::= (A (V hd_ret_str));;
  map_list_find_aux_ret_str ::= (A (N 0));;
  \<comment> \<open>map_list_find_aux_state = \<lparr>
      map_list_find_aux_xs = map_list_find_aux_xs',
      map_list_find_aux_a = map_list_find_aux_a',
      map_list_find_aux_ret = map_list_find_aux_ret'
    \<rparr>;
    map_list_find_aux_ret_state = map_list_find_aux_imp map_list_find_aux_state;\<close>
  (CALL map_list_find_aux_IMP_Minus RETURN map_list_find_aux_ret_str);;
  filter_defined_acc_loop_body_if_cond ::= (A (V map_list_find_aux_ret_str));;
  IF filter_defined_acc_loop_body_if_cond\<noteq>0
  THEN ( \<comment> \<open>filter_defined_acc_s' = filter_defined_acc_s s;\<close>
      (filter_defined_acc_s_str) ::= (A (V filter_defined_acc_s_str));;
      \<comment> \<open>hd_xs' = filter_defined_acc_n s;\<close>
      hd_xs_str ::= (A (V filter_defined_acc_n_str));;
      \<comment> \<open>hd_ret' = 0;\<close>
      hd_ret_str ::= (A (N 0));;
      \<comment> \<open>hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
         hd_ret_state = hd_imp hd_state;\<close>
      (CALL hd_IMP_Minus RETURN hd_ret_str);;
      \<comment> \<open>cons_h' = hd_ret hd_ret_state;\<close>
      cons_h_str ::= (A (V hd_ret_str));;
      \<comment> \<open>cons_t' = filter_defined_acc_acc s;\<close>
      cons_t_str ::= (A (V filter_defined_acc_acc_str));;
      \<comment>\<open>cons_ret' = 0;\<close>
      cons_ret_str ::= (A (N 0));;
      \<comment>\<open>cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
      \<comment>\<open>cons_ret_state = cons_imp cons_state;\<close>
      (CALL cons_IMP_Minus RETURN cons_ret_str);;
      \<comment>\<open>filter_defined_acc_acc' = cons_ret cons_ret_state;\<close>
      filter_defined_acc_acc_str ::= (A (V cons_ret_str));;
      \<comment>\<open>tl_xs' = filter_defined_acc_n s;\<close>
      tl_xs_str ::= (A (V filter_defined_acc_n_str));;
      \<comment>\<open>tl_ret' = 0;\<close>
      tl_ret_str ::= (A (N 0));;
      \<comment>\<open>tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;\<close>
      \<comment>\<open>tl_ret_state = tl_imp tl_state;\<close>
      (CALL tl_IMP_Minus RETURN tl_ret_str);;
      \<comment>\<open>filter_defined_acc_n' = tl_ret tl_ret_state;\<close>
      filter_defined_acc_n_str ::= (A (V tl_ret_str));;
      \<comment>\<open>filter_defined_acc_ret' = 0;\<close>
      (filter_defined_acc_ret_str) ::= (A (N 0))
    )
  ELSE (
      \<comment> \<open>filter_defined_acc_s' = filter_defined_acc_s s;\<close>
      filter_defined_acc_s_str ::= (A (V filter_defined_acc_s_str));;
      \<comment> \<open>filter_defined_acc_acc' = filter_defined_acc_acc s;\<close>
      filter_defined_acc_acc_str ::= (A (V filter_defined_acc_acc_str));;
      \<comment> \<open>tl_xs' = filter_defined_acc_n s;\<close>
      tl_xs_str ::= (A (V filter_defined_acc_n_str));;
      \<comment> \<open>tl_ret' = 0;\<close>
      tl_ret_str ::= (A (N 0));;
      \<comment> \<open>tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;\<close>
      \<comment> \<open>tl_ret_state = tl_imp tl_state;\<close>
      (CALL tl_IMP_Minus RETURN tl_ret_str);;
      \<comment> \<open>filter_defined_acc_n' = tl_ret tl_ret_state;\<close>
      filter_defined_acc_n_str ::= (A (V tl_ret_str));;
      \<comment> \<open>filter_defined_acc_ret' = 0;\<close>
      filter_defined_acc_ret_str ::= (A (N 0))
    )"

lemma filter_defined_acc_IMP_Minus_Calls_loop_body_correct:
  assumes "(filter_defined_acc_IMP_Minus_Calls_loop_body, s) \<Rightarrow>'\<^bsup>t\<^esup> s'"
  shows "filter_defined_acc_imp_to_HOL_state [] s' =
    filter_defined_acc_state_upd (filter_defined_acc_imp_to_HOL_state [] s)"
  apply (insert assms)
  apply (tactic \<open>HEADGOAL (LT.run_finish_tac'
    @{thm filter_defined_acc_state_upd_def} @{thm filter_defined_acc_IMP_Minus_Calls_loop_body_def}
    @{thm filter_defined_acc_imp_to_HOL_state_def}
    [
      (@{thm hd_IMP_Minus_correct}, @{thm hd_imp_to_HOL_state_def}),
      (@{thm tl_IMP_Minus_correct}, @{thm tl_imp_to_HOL_state_def}),
      (@{thm cons_IMP_Minus_correct}, @{thm cons_imp_to_HOL_state_def}),
      (@{thm map_list_find_aux_IMP_Minus_correct}, @{thm map_list_find_aux_imp_to_HOL_state_def})
    ] @{context})\<close>)
  done

interpretation I: Let_To_IMP_Minus_Calls where
  cond_var = filter_defined_acc_while_cond and
  cond_let = filter_defined_acc_imp_compute_loop_condition and
  body_let = filter_defined_acc_state_upd and
  base_let = filter_defined_acc_imp_after_loop and
  loop_let = filter_defined_acc_imp and
  cond_imp = filter_defined_acc_IMP_Minus_Calls_init_while_cond and
  body_imp = filter_defined_acc_IMP_Minus_Calls_loop_body and
  base_imp = filter_defined_acc_IMP_Minus_Calls_after_loop and
  imp_to_let_state = "filter_defined_acc_imp_to_HOL_state []"
  apply unfold_locales
  subgoal by (simp add: filter_defined_acc_imp_to_HOL_state_def
    filter_defined_acc_IMP_Minus_Calls_init_while_cond_def
    filter_defined_acc_IMP_Minus_Calls_loop_body_def
    filter_defined_acc_IMP_Minus_Calls_after_loop_def)
  subgoal by (tactic \<open>HEADGOAL (LT.run_finish_tac (resolve0_tac @{thms conjI})
    @{thm filter_defined_acc_imp_compute_loop_condition_def} @{thm filter_defined_acc_IMP_Minus_Calls_init_while_cond_def}
    @{thm filter_defined_acc_imp_to_HOL_state_def} [] @{context})\<close>)
  subgoal by (fact filter_defined_acc_IMP_Minus_Calls_loop_body_correct)
  subgoal by (tactic \<open>HEADGOAL (LT.run_finish_tac'
    @{thm filter_defined_acc_imp_after_loop_def} @{thm filter_defined_acc_IMP_Minus_Calls_after_loop_def}
    @{thm filter_defined_acc_imp_to_HOL_state_def} [] @{context})\<close>)
  using filter_defined_acc_imp.induct filter_defined_acc_imp.simps by auto

(* lemma filter_defined_acc_IMP_Minus_loop_body_correct_time:
  assumes "(invoke_subprogram p filter_defined_acc_IMP_loop_body, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "t = filter_defined_acc_state_upd_time 0 (filter_defined_acc_imp_to_HOL_state p s)"
  apply (insert assms)
  apply (tactic \<open>HEADGOAL (Let_To_IMP_Minus_Tactics.IMP_Minus_run_finish_tac'
    @{thm filter_defined_acc_state_upd_time_def} @{thm filter_defined_acc_IMP_loop_body_def}
    @{thm filter_defined_acc_imp_to_HOL_state_def}
    [
      (@{thm hd_IMP_Minus_correct}, @{thm hd_imp_to_HOL_state_def}),
      (@{thm tl_IMP_Minus_correct}, @{thm tl_imp_to_HOL_state_def}),
      (@{thm cons_IMP_Minus_correct}, @{thm cons_imp_to_HOL_state_def}),
      (@{thm map_list_find_aux_IMP_Minus_correct}, @{thm map_list_find_aux_imp_to_HOL_state_def})
    ]
    @{cterm "filter_defined_acc_IMP_vars"} @{cterm p}
    @{context})\<close>)
  oops *)
(*probably an error in the definition of the time function*)

end
