\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Tactics
  imports
    HOL_To_IMP_Utils
    HOL_To_IMP_Minus_Goal_Commands
    State_Update_Tracking_IMP_Tailcalls
    HOL_To_IMP_Terminates_With_Res
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

(* isolates the return value in its own subgoal *)
lemma rewrite_terminates_with_res_IMP_Tailcall_value:
  assumes "v = v'" and "terminates_with_res_IMP_Tailcall tc c s r v'"
  shows "terminates_with_res_IMP_Tailcall tc c s r v"
  using assms by blast

(* isolates the function and its argument from a function application *)
lemma rewrite_comb: assumes "f = g" "x = y" shows "f x = g y" using assms by blast

(* lemmas for targeted retrieval from states *)
lemma retrieve_udpate_eq:
  "STATE (interp_state (update_state s k v)) k = v"
  unfolding STATE_def by simp
lemma retrieve_udpate_neq:
  assumes "k \<noteq> k'"
  shows "STATE (interp_state (update_state s k' v)) k = STATE (interp_state s) k"
  unfolding STATE_def using assms by simp
lemma retrieve_State:
  "STATE (interp_state (State s)) k = s k"
  unfolding STATE_def interp_state_def by simp

(* lemmas for state simplification/normalization *)
lemma state_simp_eq:
  "STATE (interp_state (update_state (update_state s k v1) k v2))
    = STATE (interp_state (update_state s k v2))"
  unfolding STATE_def by simp
lemma state_simp_neq:
  assumes "k \<noteq> k'"
    and "STATE (interp_state (update_state s k v)) = STATE (interp_state s')"
  shows
    "STATE (interp_state (update_state (update_state s k' v') k v))
      = STATE (interp_state (update_state s' k' v'))"
  using assms unfolding STATE_def by (simp add: fun_upd_twist)
(* lemma state_simp_update:
  assumes "STATE (interp_state s1) = STATE (interp_state s2)"
  shows
    "STATE (interp_state (update_state s1 k v)) = STATE (interp_state (update_state s2 k v))"
  using assms unfolding STATE_def by simp *)

(* for solving (in)equalities between strings *)
lemmas string_equality_simps = list.inject list.distinct (* bool.distinct *) char.inject bool_simps
lemmas retrieval_simps = retrieve_udpate_eq retrieve_udpate_neq retrieve_State string_equality_simps

(* lemma add_subgoal: assumes P and Q shows Q using assms(2) . *)

ML_file \<open>hol_to_imp_tactics_base.ML\<close>
ML_file \<open>hol_to_imp_tailcalls_tactics.ML\<close>
ML_file \<open>hol_to_imp_tactics.ML\<close>
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
