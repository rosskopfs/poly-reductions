\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Elemof
  imports
    Cook_Levin_IMP.Primitives_IMP_Minus
    While_To_IMP_Minus_Tactics
begin

lemma elemof_IMP_loop_body_correct:
  assumes "(invoke_subprogram p elemof_IMP_loop_body, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "elemof_imp_to_HOL_state p s' =
    elemof_state_upd (elemof_imp_to_HOL_state p s)"
  apply (insert assms)
  apply (tactic \<open>HEADGOAL (IMP_start_tac @{cterm "add_prefix p ` elemof_IMP_vars"}
    @{thm elemof_state_upd_def} @{thm elemof_IMP_loop_body_def}
    @{context})\<close>)
  apply (tactic \<open>HEADGOAL (IMP_step_update_view_tac @{cterm elemof_IMP_vars}
    @{thm tl_IMP_Minus_correct} @{thm tl_imp_to_HOL_state_def}
    @{context})\<close>)+
  apply (tactic \<open>HEADGOAL (IMP_finish_state_eq_tac @{thms elemof_state_translators}
    "Primitives_IMP_Minus.elemof_state"
    @{context})\<close>)
  done

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
  subgoal
    apply (simp add: elemof_imp_to_HOL_state_def)
    done
  subgoal
    apply auto
    done
  subgoal
    apply (auto simp: elemof_complete_simps)
    done
  subgoal
    apply (fact elemof_IMP_loop_body_correct)
    done
  subgoal for s t s' p
    apply (tactic \<open>HEADGOAL (IMP_start_tac @{cterm "add_prefix p ` elemof_IMP_vars"}
      @{thm elemof_imp_compute_loop_condition_def} @{thm elemof_IMP_init_while_cond_def}
      @{context})\<close>)
    apply (tactic \<open>HEADGOAL (IMP_step_update_view_tac @{cterm elemof_IMP_vars}
      @{thm hd_IMP_Minus_correct} @{thm hd_imp_to_HOL_state_def}
      @{context})\<close>)+
    apply (tactic \<open>HEADGOAL (IMP_step_update_view_tac @{cterm elemof_IMP_vars}
      @{thm NOTEQUAL_neq_zero_IMP_Minus_correct} @{thm NOTEQUAL_neq_zero_imp_to_HOL_state_def}
      @{context})\<close>)+
    apply (tactic \<open>HEADGOAL (IMP_step_update_view_tac @{cterm elemof_IMP_vars}
      @{thm AND_neq_zero_IMP_Minus_correct} @{thm AND_neq_zero_imp_to_HOL_state_def}
      @{context})\<close>)+
    apply (rule conjI;
      tactic \<open>HEADGOAL (IMP_finish_state_tac @{thms elemof_state_translators}
        "Primitives_IMP_Minus.elemof_state"
        @{context})\<close>)
    done
  using elemof_imp.induct elemof_imp.simps
    apply auto
  done

end