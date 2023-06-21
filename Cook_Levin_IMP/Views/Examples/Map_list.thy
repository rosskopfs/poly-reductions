\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Map_list
  imports
    Cook_Levin_IMP.Primitives_IMP_Minus
    IMP_Minus_Views.Let_To_IMP_Minus_Locale
    IMP_Minus_Views.Let_To_IMP_Minus_Tactics
begin

lemma map_list_find_aux_IMP_loop_body_correct_time:
  assumes "(invoke_subprogram p map_list_find_aux_IMP_loop_body, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "t = map_list_find_aux_state_upd_time 0 (map_list_find_aux_imp_to_HOL_state p s)"
  apply (insert assms)
  apply (tactic \<open>HEADGOAL (Let_To_IMP_Minus_Tactics.IMP_Minus_run_finish_tac'
    @{thm map_list_find_aux_state_upd_time_def} @{thm map_list_find_aux_IMP_loop_body_def}
    @{thm map_list_find_aux_imp_to_HOL_state_def}
    [(@{thm tl_IMP_Minus_correct}, @{thm tl_imp_to_HOL_state_def})]
    @{cterm "map_list_find_aux_IMP_vars"} @{cterm p}
    @{context})\<close>)
  done

lemma map_list_find_aux_IMP_after_loop_correct_time:
  assumes "(invoke_subprogram p map_list_find_aux_IMP_after_loop, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "t = map_list_find_aux_imp_after_loop_time 0 (map_list_find_aux_imp_to_HOL_state p s)"
  apply (insert assms)
  apply (tactic \<open>HEADGOAL (Let_To_IMP_Minus_Tactics.IMP_Minus_run_finish_tac'
    @{thm map_list_find_aux_imp_after_loop_time_def} @{thm map_list_find_aux_IMP_after_loop_def}
    @{thm map_list_find_aux_imp_to_HOL_state_def}
    [
      (@{thm tl_IMP_Minus_correct}, @{thm tl_imp_to_HOL_state_def}),
      (@{thm hd_IMP_Minus_correct}, @{thm hd_imp_to_HOL_state_def}),
      (@{thm snd'_IMP_Minus_correct}, @{thm snd'_imp_to_HOL_state_def}),
      (@{thm some_nat_IMP_Minus_correct}, @{thm some_nat_imp_to_HOL_state_def})
    ]
    @{cterm "map_list_find_aux_IMP_vars"} @{cterm p}
    @{context})\<close>)
  done

interpretation I: Let_To_IMP_Minus where
  cond_var = map_list_find_aux_while_cond and
  cond_let = map_list_find_aux_imp_compute_loop_condition and
  body_let = map_list_find_aux_state_upd and
  base_let = map_list_find_aux_imp_after_loop and
  loop_let = map_list_find_aux_imp and
  cond_imp = map_list_find_aux_IMP_init_while_cond and
  body_imp = map_list_find_aux_IMP_loop_body and
  base_imp = map_list_find_aux_IMP_after_loop and
  imp_to_let_state = map_list_find_aux_imp_to_HOL_state and
  vars = "map_list_find_aux_IMP_vars - {map_list_find_aux_while_cond}"
  apply unfold_locales
  subgoal by (simp add: map_list_find_aux_imp_to_HOL_state_def)
  subgoal by auto
  subgoal for s t s' p
    apply (tactic \<open>HEADGOAL (Let_To_IMP_Minus_Tactics.IMP_Minus_run_finish_tac'
      @{thm map_list_find_aux_imp_after_loop_def} @{thm map_list_find_aux_IMP_after_loop_def}
      @{thm map_list_find_aux_imp_to_HOL_state_def}
      [
        (@{thm tl_IMP_Minus_correct}, @{thm tl_imp_to_HOL_state_def}),
        (@{thm hd_IMP_Minus_correct}, @{thm hd_imp_to_HOL_state_def}),
        (@{thm snd'_IMP_Minus_correct}, @{thm snd'_imp_to_HOL_state_def}),
        (@{thm some_nat_IMP_Minus_correct}, @{thm some_nat_imp_to_HOL_state_def})
      ]
      @{cterm "map_list_find_aux_IMP_vars"} @{cterm p}
      @{context})\<close>)
    done
  subgoal for s t s' p
    apply (tactic \<open>HEADGOAL (Let_To_IMP_Minus_Tactics.IMP_Minus_run_finish_tac'
    @{thm map_list_find_aux_state_upd_def} @{thm map_list_find_aux_IMP_loop_body_def}
    @{thm map_list_find_aux_imp_to_HOL_state_def}
    [(@{thm tl_IMP_Minus_correct}, @{thm tl_imp_to_HOL_state_def})]
    @{cterm "map_list_find_aux_IMP_vars"} @{cterm p}
    @{context})\<close>)
    done
  subgoal for s t s' p
    apply (tactic \<open>HEADGOAL (Let_To_IMP_Minus_Tactics.IMP_Minus_run_finish_tac (resolve0_tac @{thms conjI})
      @{thm map_list_find_aux_imp_compute_loop_condition_def} @{thm map_list_find_aux_IMP_init_while_cond_def}
      @{thm map_list_find_aux_imp_to_HOL_state_def}
      [
        (@{thm fst'_IMP_Minus_correct}, @{thm fst'_imp_to_HOL_state_def}),
        (@{thm hd_IMP_Minus_correct}, @{thm hd_imp_to_HOL_state_def}),
        (@{thm NOTEQUAL_neq_zero_IMP_Minus_correct}, @{thm NOTEQUAL_neq_zero_imp_to_HOL_state_def}),
        (@{thm AND_neq_zero_IMP_Minus_correct}, @{thm AND_neq_zero_imp_to_HOL_state_def})
      ]
      @{cterm "map_list_find_aux_IMP_vars"} @{cterm p}
      @{context})\<close>)
    done
  using map_list_find_aux_imp.induct map_list_find_aux_imp.simps by auto

end
