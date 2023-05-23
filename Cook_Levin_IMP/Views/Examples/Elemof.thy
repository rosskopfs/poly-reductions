\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Elemof
  imports
    Cook_Levin_IMP.Primitives_IMP_Minus
    Cook_Levin_IMP.Compile_Nat
    IMP_Minus_Views.While_To_IMP_Minus_Locale
    IMP_Minus_Views.While_To_IMP_Minus_Tactics
begin

lemma elemof_IMP_Minus_loop_body_correct_time:
  "(invoke_subprogram p elemof_IMP_loop_body, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = elemof_state_upd_time 0 (elemof_imp_to_HOL_state p s)"
  by (tactic \<open>HEADGOAL (While_To_IMP_Minus_Tactics.IMP_Minus_run_finish_tac'
    @{thm elemof_state_upd_time_def} @{thm elemof_IMP_loop_body_def}
    @{thm elemof_imp_to_HOL_state_def}
    [(@{thm tl_IMP_Minus_correct}, @{thm tl_imp_to_HOL_state_def})]
    @{cterm "elemof_IMP_vars"} @{cterm p}
    @{context})\<close>)

interpretation A : While_To_IMP_Minus where
  cond_var = elemof_while_cond and
  cond_let = elemof_imp_compute_loop_condition and
  body_let = elemof_state_upd and
  base_let = elemof_imp_after_loop and
  loop_let = elemof_imp and
  cond_imp = elemof_IMP_init_while_cond and
  body_imp = elemof_IMP_loop_body and
  base_imp = elemof_IMP_after_loop and
  imp_to_let_state = elemof_imp_to_HOL_state and
  vars = elemof_IMP_vars
  apply unfold_locales
  subgoal by (simp add: elemof_imp_to_HOL_state_def)
  subgoal by auto
  subgoal by (auto simp: elemof_complete_simps)
  subgoal for s t s' p
    apply (tactic \<open>HEADGOAL (While_To_IMP_Minus_Tactics.IMP_Minus_run_finish_tac'
      @{thm elemof_state_upd_def} @{thm elemof_IMP_loop_body_def}
      @{thm elemof_imp_to_HOL_state_def}
      [(@{thm tl_IMP_Minus_correct}, @{thm tl_imp_to_HOL_state_def})]
      @{cterm "elemof_IMP_vars"} @{cterm p}
      @{context})\<close>)
    done
  subgoal for s t s' p
    apply (tactic \<open>HEADGOAL (While_To_IMP_Minus_Tactics.IMP_Minus_run_finish_tac (resolve0_tac @{thms conjI})
      @{thm elemof_imp_compute_loop_condition_def} @{thm elemof_IMP_init_while_cond_def}
      @{thm elemof_imp_to_HOL_state_def}
      [
        (@{thm hd_IMP_Minus_correct}, @{thm hd_imp_to_HOL_state_def}),
        (@{thm NOTEQUAL_neq_zero_IMP_Minus_correct}, @{thm NOTEQUAL_neq_zero_imp_to_HOL_state_def}),
        (@{thm AND_neq_zero_IMP_Minus_correct}, @{thm AND_neq_zero_imp_to_HOL_state_def})
      ]
      @{cterm "elemof_IMP_vars"} @{cterm p}
      @{context})\<close>)
    done
  using elemof_imp.induct elemof_imp.simps by auto

end
