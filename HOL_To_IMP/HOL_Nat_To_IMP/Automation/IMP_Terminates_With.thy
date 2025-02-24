\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory IMP_Terminates_With
  imports IMP.IMP_Tailcall
begin

definition "tailcall_to_IMP \<equiv> inline o compile"

lemma tailcall_to_IMP_eq: "tailcall_to_IMP p = inline (compile p)"
  unfolding tailcall_to_IMP_def by simp

definition "terminates_with_pred_time_IMP p s s' P \<equiv> \<exists>t. (p, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<and> P t"

lemma terminates_with_pred_time_IMPI:
  assumes "(p, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  and "P t"
  shows "terminates_with_pred_time_IMP p s s' P"
  using assms unfolding terminates_with_pred_time_IMP_def by blast

lemma terminates_with_pred_time_IMPE:
  assumes "terminates_with_pred_time_IMP p s s' P"
  obtains t where "(p, s) \<Rightarrow>\<^bsup>t\<^esup> s'" "P t"
  using assms unfolding terminates_with_pred_time_IMP_def by blast

definition "terminates_with_IMP p s s' \<equiv> terminates_with_pred_time_IMP p s s' (\<lambda>_. True)"

lemma terminates_with_IMPI:
  assumes "(p, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "terminates_with_IMP p s s'"
  using assms terminates_with_pred_time_IMPI unfolding terminates_with_IMP_def by auto

lemma terminates_with_IMPE:
  assumes "terminates_with_IMP p s s'"
  obtains t where "(p, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  using assms terminates_with_pred_time_IMPE unfolding terminates_with_IMP_def by blast

definition "terminates_with_res_pred_time_IMP p s r val P \<equiv>
  \<exists>s'. terminates_with_pred_time_IMP p s s' P \<and> s' r = val"

lemma terminates_with_res_pred_time_IMPI:
  assumes "terminates_with_pred_time_IMP p s s' P"
  and "s' r = val"
  shows "terminates_with_res_pred_time_IMP p s r val P"
  using assms unfolding terminates_with_res_pred_time_IMP_def by blast

lemma terminates_with_res_pred_time_IMPE:
  assumes "terminates_with_res_pred_time_IMP p s r val P"
  obtains s' where "terminates_with_pred_time_IMP p s s' P" "s' r = val"
  using assms unfolding terminates_with_res_pred_time_IMP_def by blast

definition "terminates_with_res_IMP p s r val \<equiv>
  terminates_with_res_pred_time_IMP p s r val (\<lambda>_. True)"

lemma terminates_with_res_IMPI:
  assumes "terminates_with_IMP p s s'"
  and "s' r = val"
  shows "terminates_with_res_IMP p s r val"
  using assms unfolding terminates_with_res_IMP_def
  by (intro terminates_with_res_pred_time_IMPI)
  (simp only: flip: terminates_with_IMP_def)

lemma terminates_with_res_IMPE:
  assumes "terminates_with_res_IMP p s r val"
  obtains s' where "terminates_with_IMP p s s'" "s' r = val"
  using assms unfolding terminates_with_res_IMP_def
  by (elim terminates_with_res_pred_time_IMPE)
  (simp only: flip: terminates_with_IMP_def)

definition "terminates_with_pred_time_IMP_Tailcall tp p s s' P \<equiv> \<exists>t. tp \<turnstile> (p, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<and> P t"

lemma terminates_with_pred_time_IMP_TailcallI:
  assumes "tp \<turnstile> (p, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  and "P t"
  shows "terminates_with_pred_time_IMP_Tailcall tp p s s' P"
  using assms unfolding terminates_with_pred_time_IMP_Tailcall_def by blast

lemma terminates_with_pred_time_IMP_TailcallE:
  assumes "terminates_with_pred_time_IMP_Tailcall tp p s s' P"
  obtains t where "tp \<turnstile> (p, s) \<Rightarrow>\<^bsup>t\<^esup> s'" "P t"
  using assms unfolding terminates_with_pred_time_IMP_Tailcall_def by blast

definition "terminates_with_IMP_Tailcall tp p s s' \<equiv>
  terminates_with_pred_time_IMP_Tailcall tp p s s' (\<lambda>_. True)"

lemma terminates_with_IMP_TailcallI:
  assumes "tp \<turnstile> (p, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "terminates_with_IMP_Tailcall tp p s s'"
  using assms terminates_with_pred_time_IMP_TailcallI unfolding terminates_with_IMP_Tailcall_def by auto

lemma terminates_with_IMP_TailcallE:
  assumes "terminates_with_IMP_Tailcall tp p s s'"
  obtains t where "tp \<turnstile> (p, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  using assms terminates_with_pred_time_IMP_TailcallE unfolding terminates_with_IMP_Tailcall_def by blast

definition "terminates_with_res_pred_time_IMP_Tailcall tp p s r val P \<equiv>
  \<exists>s'. terminates_with_pred_time_IMP_Tailcall tp p s s' P \<and> s' r = val"

lemma terminates_with_res_pred_time_IMP_TailcallI:
  assumes "terminates_with_pred_time_IMP_Tailcall tp p s s' P"
  and "s' r = val"
  shows "terminates_with_res_pred_time_IMP_Tailcall tp p s r val P"
  using assms unfolding terminates_with_res_pred_time_IMP_Tailcall_def by blast

lemma terminates_with_res_pred_time_IMP_TailcallE:
  assumes "terminates_with_res_pred_time_IMP_Tailcall tp p s r val P"
  obtains s' where "terminates_with_pred_time_IMP_Tailcall tp p s s' P" "s' r = val"
  using assms unfolding terminates_with_res_pred_time_IMP_Tailcall_def by blast

definition "terminates_with_res_IMP_Tailcall tp p s r val \<equiv>
  terminates_with_res_pred_time_IMP_Tailcall tp p s r val (\<lambda>_. True)"

lemma terminates_with_res_IMP_TailcallI:
  assumes "terminates_with_IMP_Tailcall tp p s s'"
  and "s' r = val"
  shows "terminates_with_res_IMP_Tailcall tp p s r val"
  using assms unfolding terminates_with_res_IMP_Tailcall_def
  by (intro terminates_with_res_pred_time_IMP_TailcallI)
  (simp only: flip: terminates_with_IMP_Tailcall_def)

lemma terminates_with_res_IMP_TailcallE:
  assumes "terminates_with_res_IMP_Tailcall tp p s r val"
  obtains s' where "terminates_with_IMP_Tailcall tp p s s'" "s' r = val"
  using assms unfolding terminates_with_res_IMP_Tailcall_def
  by (elim terminates_with_res_pred_time_IMP_TailcallE)
  (simp only: flip: terminates_with_IMP_Tailcall_def)

context
  notes
    terminates_with_IMPE[elim] terminates_with_res_IMPE[elim]
    terminates_with_IMP_TailcallE[elim] terminates_with_res_IMP_TailcallE[elim]
    terminates_with_res_IMPI[intro] terminates_with_IMPI[intro]
    terminates_with_res_IMP_TailcallI[intro] terminates_with_IMP_TailcallI[intro]
begin

lemma terminates_with_res_IMP_if_terminates_with_res_IMP_TailcallI:
  assumes "invar p"
  and "r \<in> set (vars p)"
  and "terminates_with_res_IMP_Tailcall p p s r val"
  shows "terminates_with_res_IMP (tailcall_to_IMP p) s r val"
  using assms by (elim terminates_with_res_IMP_TailcallE terminates_with_IMP_TailcallE
    compile_sound inline_sound[where ?s=s and ?s'=s for s])
  (force simp: set_vars_compile tailcall_to_IMP_eq)+

lemma terminates_with_tSeqI:
  assumes "terminates_with_IMP_Tailcall p p1 s s'"
  and "terminates_with_IMP_Tailcall p p2 s' s''"
  shows "terminates_with_IMP_Tailcall p (tSeq p1 p2) s s''"
  using assms by blast

lemma terminates_with_tAssignI:
  assumes "s' = s(k := aval aexp s)"
  shows "terminates_with_IMP_Tailcall p (tAssign k aexp) s s'"
  using assms by blast

lemma terminates_with_tIfI:
  assumes "s vb \<noteq> 0 \<Longrightarrow> terminates_with_IMP_Tailcall p p1 s s'"
  and "s vb = 0 \<Longrightarrow> terminates_with_IMP_Tailcall p p2 s s'"
  shows "terminates_with_IMP_Tailcall p (tIf vb p1 p2) s s'"
  using assms by (cases "s vb = 0") blast+

lemma terminates_with_tCallI:
  assumes "terminates_with_res_IMP p s r val"
  and "s' = s(r := val)"
  shows "terminates_with_IMP_Tailcall tp (tCall p r) s s'"
  using assms by blast

lemma terminates_with_tTailI:
  assumes "terminates_with_IMP_Tailcall p p s s'"
  shows "terminates_with_IMP_Tailcall p tTAIL s s'"
  using assms by blast+

lemma terminates_with_res_tSeqI:
  assumes "terminates_with_IMP_Tailcall p p1 s s'"
  and "terminates_with_res_IMP_Tailcall p p2 s' r val"
  shows "terminates_with_res_IMP_Tailcall p (tSeq p1 p2) s r val"
  using assms by blast

lemma terminates_with_res_tAssignI:
  assumes "s' = s(k := aval aexp s)"
  and "s' r = val"
  shows "terminates_with_res_IMP_Tailcall p (tAssign k aexp) s r val"
  using assms by blast

lemma terminates_with_res_tIfI:
  assumes "s vb \<noteq> 0 \<Longrightarrow> terminates_with_res_IMP_Tailcall p p1 s r val"
  and "s vb = 0 \<Longrightarrow> terminates_with_res_IMP_Tailcall p p2 s r val"
  shows "terminates_with_res_IMP_Tailcall p (tIf vb p1 p2) s r val"
  using assms by (cases "s vb = 0") blast+

lemma terminates_with_res_tCallI:
  assumes "terminates_with_res_IMP p s r val"
  and "(s(r := val)) r' = val'"
  shows "terminates_with_res_IMP_Tailcall tp (tCall p r) s r' val'"
  using assms by blast

lemma terminates_with_res_tTailI:
  assumes "terminates_with_res_IMP_Tailcall p p s r val"
  shows "terminates_with_res_IMP_Tailcall p tTAIL s r val"
  using assms by blast+

end

end