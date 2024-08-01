\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory IMP_Terminates_With
  imports IMP_Minus.IMP_Tailcalls_Dynamic
begin

definition "tailcall_to_IMP_Minus \<equiv> inline o compile"

lemma tailcall_to_IMP_Minus_eq: "tailcall_to_IMP_Minus c = inline (compile c)"
  unfolding tailcall_to_IMP_Minus_def by simp


definition "terminates_with_IMP_Minus c s s' \<equiv> \<exists>t. (c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"

lemma terminates_with_IMP_MinusI:
  assumes "(c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "terminates_with_IMP_Minus c s s'"
  using assms unfolding terminates_with_IMP_Minus_def by blast

lemma terminates_with_IMP_MinusE:
  assumes "terminates_with_IMP_Minus c s s'"
  obtains t where "(c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  using assms unfolding terminates_with_IMP_Minus_def by blast

definition "terminates_with_res_IMP_Minus c s r val \<equiv> \<exists>s'. terminates_with_IMP_Minus c s s' \<and> s' r = val"

lemma terminates_with_res_IMP_MinusI:
  assumes "terminates_with_IMP_Minus c s s'"
  and "s' r = val"
  shows "terminates_with_res_IMP_Minus c s r val"
  using assms unfolding terminates_with_res_IMP_Minus_def by blast

lemma terminates_with_res_IMP_MinusE:
  assumes "terminates_with_res_IMP_Minus c s r val"
  obtains s' where "terminates_with_IMP_Minus c s s'" "s' r = val"
  using assms unfolding terminates_with_res_IMP_Minus_def by blast

definition "terminates_with_IMP_Tailcall tc c s s' \<equiv> \<exists>t. tc \<turnstile> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"

lemma terminates_with_IMP_TailcallI:
  assumes "tc \<turnstile> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "terminates_with_IMP_Tailcall tc c s s'"
  using assms unfolding terminates_with_IMP_Tailcall_def by blast

lemma terminates_with_IMP_TailcallE:
  assumes "terminates_with_IMP_Tailcall tc c s s'"
  obtains t where "tc \<turnstile> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  using assms unfolding terminates_with_IMP_Tailcall_def by blast

definition "terminates_with_res_IMP_Tailcall tc c s r val \<equiv>
  \<exists>s'. terminates_with_IMP_Tailcall tc c s s' \<and> s' r = val"

lemma terminates_with_res_IMP_TailcallI:
  assumes "terminates_with_IMP_Tailcall tc c s s'"
  and "s' r = val"
  shows "terminates_with_res_IMP_Tailcall tc c s r val"
  using assms unfolding terminates_with_res_IMP_Tailcall_def by blast

lemma terminates_with_res_IMP_TailcallE:
  assumes "terminates_with_res_IMP_Tailcall tc c s r val"
  obtains s' where "terminates_with_IMP_Tailcall tc c s s'" "s' r = val"
  using assms unfolding terminates_with_res_IMP_Tailcall_def by blast

context
  notes
    terminates_with_IMP_MinusE[elim] terminates_with_res_IMP_MinusE[elim]
    terminates_with_IMP_TailcallE[elim] terminates_with_res_IMP_TailcallE[elim]
    terminates_with_res_IMP_MinusI[intro] terminates_with_IMP_MinusI[intro]
    terminates_with_res_IMP_TailcallI[intro] terminates_with_IMP_TailcallI[intro]
begin

lemma terminates_with_res_IMP_Minus_if_terminates_with_res_IMP_TailcallI:
  assumes "invar c"
  and "r \<in> set (vars c)"
  and "terminates_with_res_IMP_Tailcall c c s r val"
  shows "terminates_with_res_IMP_Minus (tailcall_to_IMP_Minus c) s r val"
  using assms by (elim terminates_with_res_IMP_TailcallE terminates_with_IMP_TailcallE
    compile_sound inline_sound[where ?s=s and ?s'=s for s])
  (force simp: set_vars_compile tailcall_to_IMP_Minus_eq)+

lemma terminates_with_tAssignI:
  assumes "s' = s(k := aval aexp s)"
  shows "terminates_with_IMP_Tailcall c (tAssign k aexp) s s'"
  using assms by blast

lemma terminates_with_tCallI:
  assumes "terminates_with_res_IMP_Minus c s r val"
  and "s' = s(r := val)"
  shows "terminates_with_IMP_Tailcall tc (tCall c r) s s'"
  using assms by blast

lemma terminates_with_res_tSeqI:
  assumes "terminates_with_IMP_Tailcall c c1 s s'"
  and "terminates_with_res_IMP_Tailcall c c2 s' r val"
  shows "terminates_with_res_IMP_Tailcall c (tSeq c1 c2) s r val"
  using assms by blast

lemma terminates_with_res_tAssignI:
  assumes "s' = s(k := aval aexp s)"
  and "s' r = val"
  shows "terminates_with_res_IMP_Tailcall c (tAssign k aexp) s r val"
  using assms by blast

lemma terminates_with_res_tIfI:
  assumes "s vb \<noteq> 0 \<Longrightarrow> terminates_with_res_IMP_Tailcall c c1 s r val"
  and "s vb = 0 \<Longrightarrow> terminates_with_res_IMP_Tailcall c c2 s r val"
  shows "terminates_with_res_IMP_Tailcall c (tIf vb c1 c2) s r val"
  using assms by (cases "s vb = 0") blast+

lemma terminates_with_res_tTailI:
  assumes "terminates_with_res_IMP_Tailcall c c s r val"
  shows "terminates_with_res_IMP_Tailcall c tTAIL s r val"
  using assms by blast+

end

end