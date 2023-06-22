\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Elemof_Call
  imports
    Cook_Levin_IMP.Primitives_IMP_Minus
    Cook_Levin_IMP.Compile_Nat
    IMP_Minus.IMP_Calls
    IMP_Minus_Views.Let_To_IMP_Minus_Calls_Locale
    IMP_Minus_Views.Let_To_IMP_Minus_Calls_Tactics
begin

unbundle Com.no_com_syntax
unbundle IMP_Calls.com'_syntax

ML\<open>
  structure LT = Let_To_IMP_Minus_Calls_Tactics
  structure SCL = State_Cook_Levin_IMP_Minus_Calls
\<close>

definition "elemof_IMP_init_while_cond' \<equiv>
  \<comment> \<open>  hd_xs' = elemof_l s;\<close>
  (hd_xs_str) ::= (A (V elemof_l_str));;
  \<comment> \<open>  hd_ret' = 0;\<close>
  (hd_ret_str) ::= (A (N 0));;
  \<comment> \<open>  hd_state = \<lparr>hd_xs = hd_xs',\<close> 
  \<comment> \<open>              hd_ret = hd_ret'\<rparr>;\<close>
  \<comment> \<open>  hd_ret_state = hd_imp hd_state;\<close>
  (CALL hd_IMP_Minus RETURN hd_ret_str);;
  \<comment> \<open>  NOTEQUAL_neq_zero_a' = hd_ret hd_ret_state;\<close>
  (NOTEQUAL_neq_zero_a_str) ::= (A (V (hd_ret_str)));;
  \<comment> \<open>  NOTEQUAL_neq_zero_b' = elemof_e s;\<close>
  (NOTEQUAL_neq_zero_b_str) ::= (A (V elemof_e_str));;
  \<comment> \<open>  NOTEQUAL_neq_zero_ret' = 0;\<close>
  (NOTEQUAL_neq_zero_ret_str) ::= (A (N 0));;
  \<comment> \<open>  NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',\<close>
  \<comment> \<open>                             NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',\<close>
  \<comment> \<open>                             NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;\<close>
  \<comment> \<open>  NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;\<close>
  (CALL NOTEQUAL_neq_zero_IMP_Minus RETURN NOTEQUAL_neq_zero_ret_str);;
  \<comment> \<open>  AND_neq_zero_a' = elemof_l s;\<close>
  (AND_neq_zero_a_str) ::= (A (V elemof_l_str));;
  \<comment> \<open>  AND_neq_zero_b' = NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state;\<close>
  (AND_neq_zero_b_str) ::= 
    (A (V (NOTEQUAL_neq_zero_ret_str)));;
  \<comment> \<open>  AND_neq_zero_ret' = 0;\<close>
  (AND_neq_zero_ret_str) ::= (A (N 0));;
  \<comment> \<open>  AND_neq_zero_state = \<lparr>AND_neq_zero_a = AND_neq_zero_a',\<close>
  \<comment> \<open>                        AND_neq_zero_b = AND_neq_zero_b',\<close>
  \<comment> \<open>                        AND_neq_zero_ret = AND_neq_zero_ret'\<rparr>;\<close>
  \<comment> \<open>  AND_neq_zero_ret_state = AND_neq_zero_imp AND_neq_zero_state;\<close>
  (CALL AND_neq_zero_IMP_Minus RETURN AND_neq_zero_ret_str);;
  \<comment> \<open>  condition = AND_neq_zero_ret AND_neq_zero_ret_state\<close>
  (elemof_while_cond) ::= (A (V (AND_neq_zero_ret_str)))
"

lemma "(elemof_IMP_init_while_cond', s) \<Rightarrow>'\<^bsup>t\<^esup> s' \<Longrightarrow>
  s' (BigAnd_acc_while_cond) = elemof_imp_compute_loop_condition (elemof_imp_to_HOL_state [] s) \<and>
  elemof_imp_to_HOL_state [] s' = elemof_imp_to_HOL_state [] s"
  apply (tactic \<open>HEADGOAL (LT.run_finish_tac (resolve0_tac @{thms conjI})
    @{thm elemof_imp_compute_loop_condition_def} @{thm elemof_imp_to_HOL_state_def}
    @{thm elemof_IMP_init_while_cond'_def}
    [
      (@{thm hd_IMP_Minus_correct}, @{thm hd_imp_to_HOL_state_def}),
      (@{thm NOTEQUAL_neq_zero_IMP_Minus_correct}, @{thm NOTEQUAL_neq_zero_imp_to_HOL_state_def}),
      (@{thm AND_neq_zero_IMP_Minus_correct}, @{thm AND_neq_zero_imp_to_HOL_state_def})
    ]
    @{context})\<close>)
  done


end
