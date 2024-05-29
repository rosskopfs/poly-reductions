\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Tactics
  imports
    HOL_To_IMP_Utils
    HOL_To_IMP_Minus_Goal_Commands
    State_Update_Tracking_IMP_Tailcalls
    ML_Unification.ML_Functor_Instances
    ML_Unification.ML_Method_Utils
    ML_Unification.ML_Parsing_Utils
begin

paragraph \<open>Summary\<close>
text \<open>Tactics and mehtods to refine HOL programs to IMP-Minus via IMP with tailcalls.\<close>

lemma tailcall_to_IMP_Minus_complete:
  assumes "(tailcall_to_IMP_Minus c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  and "invar c"
  obtains t' s'' where
    "c \<turnstile> (c, s) \<Rightarrow>\<^bsup>t' - 7\<^esup> s''" "s' = s'' on set (vars c)"
    "t' \<le> t" "t \<le> (t' + 1) * (1 + size\<^sub>c (compile c))"
proof -
  from assms inline obtain t' s'' where
    "(compile c, s) \<Rightarrow>'\<^bsup>t'\<^esup> s''"
    "s' = s'' on set (vars (compile c))" and
    t': "t' \<le> t" "t \<le> (t' + 1) * (1 + size\<^sub>c (compile c))"
    unfolding tailcall_to_IMP_Minus_eq by blast
  from compile_complete[OF this(1) \<open>invar c\<close>] obtain s''' where
    "c \<turnstile> (c, s) \<Rightarrow>\<^bsup>t' - 7\<^esup> s'''" "s'' = s''' on set (vars c)"
    by blast
  with \<open>s' = s'' on set (vars (compile c))\<close> have "s' = s''' on set (vars c)"
    by (simp add: eq_on_def set_vars_compile)
  with \<open>c \<turnstile> (c, s) \<Rightarrow>\<^bsup>t' - 7\<^esup> s'''\<close> t' show ?thesis
    using that by blast
qed

lemma tailcall_to_IMP_Minus_correct_if_correct:
  assumes "(tailcall_to_IMP_Minus c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  and "invar c"
  and "x \<in> set (vars c)"
  and "\<And>t s'. c \<turnstile> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> s' x = v"
  shows "s' x = v"
proof -
  from tailcall_to_IMP_Minus_complete[OF assms(1,2)] obtain t' s'' where
    c_eval: "c \<turnstile> (c, s) \<Rightarrow>\<^bsup>t' - 7\<^esup> s''" and "s' = s'' on set (vars c)" by blast
  with assms(3) have "s' x = s'' x" by blast
  also from c_eval assms(4) have "... = v" by auto
  finally show ?thesis .
qed

context includes Com.no_com_syntax IMP_Tailcalls_Dynamic.tcom_syntax
begin

(*rules without time*)
theorem tSeq_E:
  assumes "c \<turnstile>(c1;; c2, s1) \<Rightarrow>\<^bsup>t\<^esup>  s3"
  obtains t' s2 t'' where "c \<turnstile>(c1, s1) \<Rightarrow>\<^bsup>t'\<^esup> s2" and "c \<turnstile>(c2, s2) \<Rightarrow>\<^bsup>t''\<^esup> s3"
  using assms by auto

lemma tAssignD: "c \<turnstile> (x ::= a, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> s' = s(x := aval a s)"
  by auto

theorem tIf_E:
  assumes "c \<turnstile>(IF b\<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup>t\<^esup>  s'"
  obtains t' where "s b \<noteq> 0" and "c \<turnstile>(c1, s) \<Rightarrow>\<^bsup>t'\<^esup> s'"
    | t' where "s b = 0" and "c \<turnstile>(c2, s) \<Rightarrow>\<^bsup>t'\<^esup> s'"
  using assms by auto

theorem tCall_E:
  assumes "c \<turnstile>(CALL C RETURN v, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  obtains t' s'' where "s' = s(v := s'' v)" and "(C, s) \<Rightarrow>\<^bsup>t'\<^esup> s''"
  using assms by auto

lemma tTail_E:
  assumes "c \<turnstile>(tTAIL, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  obtains t' where "c \<turnstile>(c, s) \<Rightarrow>\<^bsup>t'\<^esup> s'"
  using assms by auto

end

ML_file \<open>hol_to_imp_tactics_base.ML\<close>
ML_file \<open>hol_to_imp_tailcalls_tactics.ML\<close>
ML_file \<open>hol_to_imp_tactics-new.ML\<close>
ML\<open>
  @{functor_instance struct_name = Standard_HOL_To_IMP_Tactics
    and functor_name = HOL_To_IMP_Tactics
    and id = \<open>""\<close>
    and more_args = \<open>val init_args = {
      get_IMP_def = SOME HOL_To_IMP_Tailcalls_Tactics.get_IMP_def,
      get_func_corrects = SOME HOL_To_IMP_Tailcalls_Tactics.get_func_corrects,
      get_HOL_eqs = SOME HOL_To_IMP_Tactics_Base.get_HOL_eqs,
      get_HOL_inducts = SOME HOL_To_IMP_Minus_Tactics_Args.get_HOL_inducts
    }\<close>}
\<close>
local_setup \<open>Standard_HOL_To_IMP_Tactics.setup_attribute NONE\<close>
local_setup \<open>Standard_HOL_To_IMP_Tactics.setup_method NONE\<close>
ML \<open>
  structure HB = HOL_To_IMP_Tactics_Base
  structure H = HOL_To_IMP_Tailcalls_Tactics
  structure HA = HOL_To_IMP_Minus_Tactics_Args
  structure SUTIT = State_Update_Tracking_IMP_Tailcalls
  structure SUT = State_Update_Tracking
\<close>


end
