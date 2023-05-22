\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Filter_Defined_Acc
  imports
    Filter_Defined_Acc_Base
    While_To_IMP_Minus_Tactics
begin

lemma filter_defined_acc_IMP_loop_body_correct:
  assumes "(invoke_subprogram p filter_defined_acc_IMP_loop_body, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "filter_defined_acc_imp_to_HOL_state p s' =
    filter_defined_acc_state_upd (filter_defined_acc_imp_to_HOL_state p s)"
  apply (insert assms)
  apply (tactic \<open>HEADGOAL (IMP_start_tac @{cterm "add_prefix p ` filter_defined_acc_IMP_vars"}
    @{thm filter_defined_acc_state_upd_def} @{thm filter_defined_acc_IMP_loop_body_def}
    @{context})\<close>)
  apply (tactic \<open>HEADGOAL (IMP_step_update_view_tac @{cterm filter_defined_acc_IMP_vars}
    @{thm hd_IMP_Minus_correct} @{thm hd_imp_to_HOL_state_def}
    @{context})\<close>)+
  apply (tactic \<open>HEADGOAL (IMP_step_update_view_tac @{cterm filter_defined_acc_IMP_vars}
    @{thm map_list_find_aux_IMP_Minus_correct} @{thm map_list_find_aux_imp_to_HOL_state_def}
    @{context})\<close>)+
    apply (tactic \<open>HEADGOAL (IMP_if_tac @{thms filter_defined_acc_state_translators} @{context})\<close>)
    apply (tactic \<open>HEADGOAL (IMP_step_update_view_tac @{cterm filter_defined_acc_IMP_vars}
      @{thm hd_IMP_Minus_correct} @{thm hd_imp_to_HOL_state_def}
      @{context})\<close>)+
    apply (tactic \<open>HEADGOAL (IMP_step_update_view_tac @{cterm filter_defined_acc_IMP_vars}
      @{thm cons_IMP_Minus_correct} @{thm cons_imp_to_HOL_state_def}
      @{context})\<close>)+
    apply (tactic \<open>HEADGOAL (IMP_step_update_view_tac @{cterm filter_defined_acc_IMP_vars}
      @{thm tl_IMP_Minus_correct} @{thm tl_imp_to_HOL_state_def}
      @{context})\<close>)+
    apply (tactic \<open>HEADGOAL (IMP_finish_state_eq_tac @{thms filter_defined_acc_state_translators}
      "Filter_Defined_Acc_Base.filter_defined_acc_state"
      @{context})\<close>)
    apply (tactic \<open>HEADGOAL (IMP_step_update_view_tac @{cterm filter_defined_acc_IMP_vars}
      @{thm tl_IMP_Minus_correct} @{thm tl_imp_to_HOL_state_def}
      @{context})\<close>)+
    apply (tactic \<open>HEADGOAL (IMP_finish_state_eq_tac @{thms filter_defined_acc_state_translators}
      "Filter_Defined_Acc_Base.filter_defined_acc_state"
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
  subgoal
    apply (simp add: filter_defined_acc_imp_to_HOL_state_def)
    done
  subgoal
    apply auto
    done
  subgoal
    apply (auto simp: filter_defined_acc_complete_simps filter_defined_acc_IMP_after_loop_def)
    done
  subgoal
    apply (fact filter_defined_acc_IMP_loop_body_correct)
    done
  subgoal for s t s' p
    apply (tactic \<open>HEADGOAL (IMP_start_tac @{cterm "add_prefix p ` filter_defined_acc_IMP_vars"}
      @{thm filter_defined_acc_imp_compute_loop_condition_def} @{thm filter_defined_acc_IMP_init_while_cond_def}
      @{context})\<close>)
    apply (tactic \<open>HEADGOAL (IMP_step_update_view_tac @{cterm filter_defined_acc_IMP_vars}
      @{thm hd_IMP_Minus_correct} @{thm hd_imp_to_HOL_state_def}
      @{context})\<close>)+
    apply (rule conjI;
      tactic \<open>HEADGOAL (IMP_finish_state_tac @{thms filter_defined_acc_state_translators}
        "Filter_Defined_Acc_Base.filter_defined_acc_state"
        @{context})\<close>)
    done
  using filter_defined_acc_imp.induct filter_defined_acc_imp.simps
    apply auto
  done


end