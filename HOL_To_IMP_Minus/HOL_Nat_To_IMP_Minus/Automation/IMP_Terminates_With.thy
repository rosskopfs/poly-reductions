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

lemma terminates_with_tSeqI:
  assumes "terminates_with_IMP_Tailcall c c1 s s'"
  and "terminates_with_IMP_Tailcall c c2 s' s''"
  shows "terminates_with_IMP_Tailcall c (tSeq c1 c2) s s''"
  using assms by blast

lemma terminates_with_tAssignI:
  assumes "s' = s(k := aval aexp s)"
  shows "terminates_with_IMP_Tailcall c (tAssign k aexp) s s'"
  using assms by blast

lemma terminates_with_tIfI:
  assumes "s vb \<noteq> 0 \<Longrightarrow> terminates_with_IMP_Tailcall c c1 s s'"
  and "s vb = 0 \<Longrightarrow> terminates_with_IMP_Tailcall c c2 s s'"
  shows "terminates_with_IMP_Tailcall c (tIf vb c1 c2) s s'"
  using assms by (cases "s vb = 0") blast+

lemma terminates_with_tCallI:
  assumes "terminates_with_res_IMP_Minus c s r val"
  and "s' = s(r := val)"
  shows "terminates_with_IMP_Tailcall tc (tCall c r) s s'"
  using assms by blast

lemma terminates_with_tTailI:
  assumes "terminates_with_IMP_Tailcall c c s s'"
  shows "terminates_with_IMP_Tailcall c tTAIL s s'"
  using assms by blast+

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

lemma terminates_with_res_tCallI:
  assumes "terminates_with_res_IMP_Minus c s r val"
  and "(s(r := val)) r' = val"
  shows "terminates_with_res_IMP_Tailcall tc (tCall c r) s r' val"
  using assms by blast

lemma terminates_with_res_tTailI:
  assumes "terminates_with_res_IMP_Tailcall c c s r val"
  shows "terminates_with_res_IMP_Tailcall c tTAIL s r val"
  using assms by blast+

end

paragraph \<open>With Times\<close>

definition "in_poly xs x \<equiv> \<exists>c n. x \<le> c + (sum_list xs)^n"

lemma in_polyI:
  assumes "x \<le> c + (sum_list xs)^n"
  shows "in_poly xs x"
  using assms unfolding in_poly_def by blast

lemma in_polyE:
  assumes "in_poly xs x"
  obtains c n where "x \<le> c + (sum_list xs)^n"
  using assms unfolding in_poly_def by blast

(*TODO: generalise to arbitrary number of arguments*)
lemma in_poly_appI:
  assumes "in_poly xs' (f x)"
  and "ListMem x xs'"
  and "in_poly xs x"
  shows "in_poly xs (f x :: nat)"
  using assms by (meson in_polyI le_add1)

lemma in_poly_sum_list_nil: "in_poly xs (sum_list [] :: nat)"
  by (rule in_polyI[where ?c=1 and ?n=0]) auto

lemma in_poly_sum_list_cons:
  assumes "in_poly xs x"
  and "in_poly xs (sum_list xs')"
  shows "in_poly xs (sum_list (x # xs') :: nat)"
  using assms in_polyE in_polyI by (metis le_add1)

definition "terminates_with_poly_time_IMP_Minus c s s' xs \<equiv> \<exists>t. (c, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<and> in_poly xs t"

lemma terminates_with_poly_time_IMP_MinusI:
  assumes "(c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  and "in_poly xs t"
  shows "terminates_with_poly_time_IMP_Minus c s s' xs"
  using assms unfolding terminates_with_poly_time_IMP_Minus_def by blast

lemma terminates_with_poly_time_IMP_MinusE:
  assumes "terminates_with_poly_time_IMP_Minus c s s' xs"
  obtains t where "(c, s) \<Rightarrow>\<^bsup>t\<^esup> s'" "in_poly xs t"
  using assms unfolding terminates_with_poly_time_IMP_Minus_def by blast

definition "terminates_with_res_poly_time_IMP_Minus c s r val xs \<equiv>
  \<exists>s'. terminates_with_poly_time_IMP_Minus c s s' xs \<and> s' r = val"

lemma terminates_with_res_poly_time_IMP_MinusI:
  assumes "terminates_with_poly_time_IMP_Minus c s s' xs"
  and "s' r = val"
  shows "terminates_with_res_poly_time_IMP_Minus c s r val xs"
  using assms unfolding terminates_with_res_poly_time_IMP_Minus_def by blast

lemma terminates_with_res_poly_time_IMP_MinusE:
  assumes "terminates_with_res_poly_time_IMP_Minus c s r val xs"
  obtains s' where "terminates_with_poly_time_IMP_Minus c s s' xs" "s' r = val"
  using assms unfolding terminates_with_res_poly_time_IMP_Minus_def by blast

definition "terminates_with_poly_time_IMP_Tailcall tc c s s' xs \<equiv>
  \<exists>t. tc \<turnstile> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<and> in_poly xs t"

lemma terminates_with_poly_time_IMP_TailcallI:
  assumes "tc \<turnstile> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  and "in_poly xs t"
  shows "terminates_with_poly_time_IMP_Tailcall tc c s s' xs"
  using assms unfolding terminates_with_poly_time_IMP_Tailcall_def by blast

lemma terminates_with_poly_time_IMP_TailcallE:
  assumes "terminates_with_poly_time_IMP_Tailcall tc c s s' xs"
  obtains t where "tc \<turnstile> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s'" "in_poly xs t"
  using assms unfolding terminates_with_poly_time_IMP_Tailcall_def by blast

definition "terminates_with_res_poly_time_IMP_Tailcall tc c s r val xs \<equiv>
  \<exists>s'. terminates_with_poly_time_IMP_Tailcall tc c s s' xs \<and> s' r = val"

lemma terminates_with_res_poly_time_IMP_TailcallI:
  assumes "terminates_with_poly_time_IMP_Tailcall tc c s s' xs"
  and "s' r = val"
  shows "terminates_with_res_poly_time_IMP_Tailcall tc c s r val xs"
  using assms unfolding terminates_with_res_poly_time_IMP_Tailcall_def by blast

lemma terminates_with_res_poly_time_IMP_TailcallE:
  assumes "terminates_with_res_poly_time_IMP_Tailcall tc c s r val xs"
  obtains s' where "terminates_with_poly_time_IMP_Tailcall tc c s s' xs" "s' r = val"
  using assms unfolding terminates_with_res_poly_time_IMP_Tailcall_def by blast

context
  notes
    terminates_with_poly_time_IMP_MinusE[elim] terminates_with_res_poly_time_IMP_MinusE[elim]
    terminates_with_poly_time_IMP_TailcallE[elim] terminates_with_res_poly_time_IMP_TailcallE[elim]
    terminates_with_res_poly_time_IMP_MinusI[intro] terminates_with_poly_time_IMP_MinusI[intro]
    terminates_with_res_poly_time_IMP_TailcallI[intro] terminates_with_poly_time_IMP_TailcallI[intro]
begin

lemma in_poly_compile_aux:
  assumes "in_poly xs t"
  and "a + t \<le> t'"
  and "t' \<le> (7 + t + 1) * (1 + size\<^sub>c (compile c))"
  shows "in_poly xs t'"
  using assms by (meson in_polyI nat_le_iff_add)

lemma terminates_with_res_time_IMP_Minus_if_terminates_with_res_time_IMP_TailcallI:
  assumes "invar c"
  and "r \<in> set (vars c)"
  and "terminates_with_res_poly_time_IMP_Tailcall c c s r val xs"
  shows "terminates_with_res_poly_time_IMP_Minus (tailcall_to_IMP_Minus c) s r val xs"
  using assms by (elim terminates_with_res_poly_time_IMP_TailcallE
    terminates_with_poly_time_IMP_TailcallE compile_sound
    inline_sound[where ?s=s and ?s'=s for s])
  (force simp: set_vars_compile tailcall_to_IMP_Minus_eq
    intro: terminates_with_res_poly_time_IMP_MinusI
    terminates_with_poly_time_IMP_MinusI in_poly_compile_aux)+

lemma terminates_with_poly_time_tAssignI:
  assumes "s' = s(k := aval aexp s)"
  shows "terminates_with_poly_time_IMP_Tailcall c (tAssign k aexp) s s' xs"
  using assms
  by (meson in_polyI nat_le_iff_add tAssign terminates_with_poly_time_IMP_Tailcall_def)

lemma terminates_with_poly_time_tCallI:
  assumes "terminates_with_res_poly_time_IMP_Minus c s r val xs'"
  and "s' = s(r := val)"
  and "in_poly xs (sum_list xs')"
  shows "terminates_with_poly_time_IMP_Tailcall tc (tCall c r) s s' xs"
  using assms
  by (metis in_poly_def le_iff_add tCall
    terminates_with_poly_time_IMP_Minus_def terminates_with_poly_time_IMP_Tailcall_def
    terminates_with_res_poly_time_IMP_Minus_def)

lemma terminates_with_res_poly_time_tSeqI:
  assumes "terminates_with_poly_time_IMP_Tailcall c c1 s s' xs"
  and "terminates_with_res_poly_time_IMP_Tailcall c c2 s' r val xs"
  shows "terminates_with_res_poly_time_IMP_Tailcall c (tSeq c1 c2) s r val xs"
  using assms
  by (metis in_polyI le_add1 tSeq terminates_with_poly_time_IMP_Tailcall_def terminates_with_res_poly_time_IMP_TailcallE terminates_with_res_poly_time_IMP_TailcallI)

lemma terminates_with_res_poly_time_tAssignI:
  assumes "s' = s(k := aval aexp s)"
  and "s' r = val"
  shows "terminates_with_res_poly_time_IMP_Tailcall c (tAssign k aexp) s r val xs"
  using assms terminates_with_poly_time_tAssignI by blast

lemma terminates_with_res_poly_time_tIfI:
  assumes "s vb \<noteq> 0 \<Longrightarrow> terminates_with_res_poly_time_IMP_Tailcall c c1 s r val xs"
  and "s vb = 0 \<Longrightarrow> terminates_with_res_poly_time_IMP_Tailcall c c2 s r val xs"
  shows "terminates_with_res_poly_time_IMP_Tailcall c (tIf vb c1 c2) s r val xs"
  using assms
  apply (cases "s vb = 0")
  apply (metis in_polyI le_iff_add tbig_step_t.intros
    terminates_with_poly_time_IMP_Tailcall_def terminates_with_res_poly_time_IMP_Tailcall_def)
  by (metis in_polyI le_iff_add tbig_step_t.intros(4) terminates_with_poly_time_IMP_Tailcall_def terminates_with_res_poly_time_IMP_TailcallE terminates_with_res_poly_time_IMP_TailcallI)

lemma terminates_with_res_poly_time_tTailI:
  assumes "terminates_with_res_poly_time_IMP_Tailcall c c s r val xs"
  shows "terminates_with_res_poly_time_IMP_Tailcall c tTAIL s r val xs"
  using assms
  by (metis in_polyI nat_le_iff_add tTail terminates_with_poly_time_IMP_TailcallE
    terminates_with_poly_time_IMP_TailcallI terminates_with_res_poly_time_IMP_Tailcall_def)

end

end