\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Filter_Defined_Acc
  imports
    Filter_Defined_Acc_Base
    IMP_Minus_Views.While_To_IMP_Minus_Locale
    IMP_Minus_Views.While_To_IMP_Minus_Tactics
begin

lemma filter_defined_acc_IMP_Minus_loop_body_correct:
  assumes "(invoke_subprogram p filter_defined_acc_IMP_loop_body, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "filter_defined_acc_imp_to_HOL_state p s' =
    filter_defined_acc_state_upd (filter_defined_acc_imp_to_HOL_state p s)"
  apply (insert assms)
  apply (tactic \<open>HEADGOAL (While_To_IMP_Minus_Tactics.IMP_Minus_run_finish_tac'
    @{thm filter_defined_acc_state_upd_def} @{thm filter_defined_acc_IMP_loop_body_def}
    @{thm filter_defined_acc_imp_to_HOL_state_def}
    [
      (@{thm hd_IMP_Minus_correct}, @{thm hd_imp_to_HOL_state_def}),
      (@{thm tl_IMP_Minus_correct}, @{thm tl_imp_to_HOL_state_def}),
      (@{thm cons_IMP_Minus_correct}, @{thm cons_imp_to_HOL_state_def}),
      (@{thm map_list_find_aux_IMP_Minus_correct}, @{thm map_list_find_aux_imp_to_HOL_state_def})
    ]
    @{cterm "filter_defined_acc_IMP_vars"} @{cterm p}
    @{context})\<close>)
  done

interpretation I: While_To_IMP_Minus where
  cond_var = filter_defined_acc_while_cond and
  cond_let = filter_defined_acc_imp_compute_loop_condition and
  body_let = filter_defined_acc_state_upd and
  base_let = filter_defined_acc_imp_after_loop and
  loop_let = filter_defined_acc_imp and
  cond_imp = filter_defined_acc_IMP_init_while_cond and
  body_imp = filter_defined_acc_IMP_loop_body and
  base_imp = filter_defined_acc_IMP_after_loop and
  imp_to_let_state = filter_defined_acc_imp_to_HOL_state and
  vars = filter_defined_acc_IMP_vars
  apply unfold_locales
  subgoal by (simp add: filter_defined_acc_imp_to_HOL_state_def)
  subgoal by auto
  subgoal by (auto simp: filter_defined_acc_complete_simps filter_defined_acc_IMP_after_loop_def)
  subgoal by (fact filter_defined_acc_IMP_Minus_loop_body_correct)
  subgoal for s t s' p
    apply (tactic \<open>HEADGOAL (While_To_IMP_Minus_Tactics.IMP_Minus_run_finish_tac (resolve0_tac @{thms conjI})
      @{thm filter_defined_acc_imp_compute_loop_condition_def} @{thm filter_defined_acc_IMP_init_while_cond_def}
      @{thm filter_defined_acc_imp_to_HOL_state_def}
      []
      @{cterm "filter_defined_acc_IMP_vars"} @{cterm p}
      @{context})\<close>)
    done
  using filter_defined_acc_imp.induct filter_defined_acc_imp.simps by auto

lemma filter_defined_acc_IMP_Minus_loop_body_correct_time:
  assumes "(invoke_subprogram p filter_defined_acc_IMP_loop_body, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "t = filter_defined_acc_state_upd_time 0 (filter_defined_acc_imp_to_HOL_state p s)"
  apply (insert assms)
  apply (tactic \<open>HEADGOAL (While_To_IMP_Minus_Tactics.IMP_Minus_run_finish_tac'
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
  oops (*probably an error in the definition of the time function*)


end
