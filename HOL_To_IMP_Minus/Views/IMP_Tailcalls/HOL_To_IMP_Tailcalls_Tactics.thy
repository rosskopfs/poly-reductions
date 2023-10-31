\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Tailcalls_Tactics
  imports
    States_IMP_Tailcalls
    Compile_Nat
begin

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

lemma tAssignD: "c \<turnstile> (x ::= a, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> t = 2 \<and> s' = s(x := aval a s)"
  by auto

theorem tIf_tE':
  assumes "c \<turnstile>(IF b\<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup>t\<^esup>  s'"
  obtains t' where "t = Suc t'" and "s b \<noteq> 0" and "c \<turnstile>(c1, s) \<Rightarrow>\<^bsup>t'\<^esup> s'"
    | t' where "t = Suc t'" and "s b = 0" and "c \<turnstile>(c2, s) \<Rightarrow>\<^bsup>t'\<^esup> s'"
  using assms by auto

end

ML_file \<open>hol_to_imp_tailcalls_tactics.ML\<close>

ML \<open>
  structure H = HOL_To_IMP_Tailcalls_Tactics
  structure SIT = State_IMP_Tailcalls
\<close>
  

end
