\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory While_To_IMP_Minus_Tactics
  imports
    IMP_Minus_Views.Views_Cook_Levin
    While_To_IMP_Minus_Locale
begin
          
lemma If_E:
  "\<lbrakk>(IF b\<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> y \<^esup> t;
    \<And>x. \<lbrakk>0 < s b; (c1, s) \<Rightarrow>\<^bsup> x \<^esup> t\<rbrakk> \<Longrightarrow> P; \<And>x. \<lbrakk>s b = 0; (c2, s) \<Rightarrow>\<^bsup> x \<^esup> t\<rbrakk> \<Longrightarrow> P\<rbrakk>
    \<Longrightarrow> P"
  by blast

lemma Seq_assoc:
  "((Com.Seq p1 (Com.Seq p2 p3), s) \<Rightarrow>\<^bsup>t\<^esup> s') \<longleftrightarrow> ((Com.Seq (Com.Seq p1 p2) p3, s) \<Rightarrow>\<^bsup>t\<^esup> s')"
  by auto        

ML\<open>
  structure U = View_Util
  structure VCL = View_Cook_Levin
  
  fun Seq_assoc_left_tac ctxt =
    safe_full_simp_tac (View_Util.set_simps ctxt @{thms Seq_assoc[symmetric]})

  fun IMP_start_tac cvars_view let_update_def IMP_loop_body_def ctxt =
    U.subst_first_tac ctxt let_update_def
    THEN' View_Util.TRY' (REPEAT_ALL_NEW (U.subst_first_tac ctxt @{thm Let_def}))
    THEN' U.subst_first_asm_tac ctxt IMP_loop_body_def
    THEN' safe_full_simp_tac (View_Util.set_simps ctxt @{thms prefix_simps})
    THEN' Seq_assoc_left_tac ctxt
    THEN' VCL.init_view_eq_tac cvars_view ctxt

  fun IMP_seq_tac ctxt = eresolve_tac ctxt @{thms Seq_E}
  fun IMP_assign_tac ctxt = dresolve_tac ctxt @{thms AssignD}
    THEN' eresolve_tac ctxt @{thms conjE}
    THEN' VCL.update_view_assign_tac ctxt

  fun IMP_invoke_subprogram_tac cvars correctness_thm state_def_thm ctxt =
    let val correctness_thm =
      Drule.infer_instantiate ctxt [(("vars", 0), cvars)] correctness_thm
      |> Local_Defs.unfold ctxt @{thms atomize_ball}
    in
      eresolve_tac ctxt [correctness_thm]
      THEN' Subgoal.SUBPROOF (#context #> auto_tac) ctxt
      THEN' VCL.update_view_invoke_subprogram_tac state_def_thm ctxt
    end

  fun if_split_tac ctxt =
    split_tac ctxt @{thms if_split}
    THEN_ALL_NEW
      (resolve_tac ctxt @{thms conjI}
      THEN_ALL_NEW resolve_tac ctxt @{thms impI})

  fun IMP_if_tac state_defs ctxt =
    let val simp_tac = full_simp_tac (ctxt addsimps state_defs) |> SOLVED'
    in
      eresolve_tac ctxt @{thms If_E}
      THEN_ALL_NEW
        (VCL.rewrite_all_state_app_tac' U.subst_first_asm_tac ctxt
        THEN' if_split_tac ctxt)
      THEN' RANGE [Seq_assoc_left_tac ctxt, simp_tac, simp_tac, Seq_assoc_left_tac ctxt]
    end

  fun IMP_step_update_view_tac cvars correctness_thm state_def ctxt =
    View_Util.TRY' (IMP_seq_tac ctxt)
    THEN' FIRST'
      [IMP_assign_tac ctxt,
      IMP_invoke_subprogram_tac cvars correctness_thm state_def ctxt]

  fun IMP_finish_tac ctxt =
    VCL.rewrite_all_state_app_tac' U.subst_first_tac ctxt
    THEN' resolve_tac ctxt @{thms refl}

  fun get_record_info ctxt = Record.the_info (Proof_Context.theory_of ctxt)

  fun IMP_finish_state_tac state_defs record ctxt =
    let val {select_convs,...} = Record.the_info (Proof_Context.theory_of ctxt) record
    in
      REPEAT_ALL_NEW (EqSubst.eqsubst_tac ctxt [0] state_defs)
      THEN_ALL_NEW
        (asm_simp_tac (View_Util.set_simps ctxt select_convs)
        THEN_ALL_NEW (IMP_finish_tac ctxt))
    end

  fun IMP_finish_state_eq_tac state_defs record ctxt =
    let val {equality,...} = Record.the_info (Proof_Context.theory_of ctxt) record
    in
      resolve_tac ctxt [equality]
      THEN_ALL_NEW (IMP_finish_state_tac state_defs record ctxt)
    end
\<close>

end
