theory Compile_Nat
imports
  IMP_Minus.IMP_Tailcalls_Dynamic
keywords
  "compile_nat" :: thy_decl and "basename" and
  "declare_compiled_const" :: thy_decl and
  "return_register" and "argument_registers" and "compiled" and
  "print_compiled_consts" :: diag
begin

fun measure_assoc where
  "measure_assoc (tSeq i1 i2) = Suc (measure_assoc i1 + measure_assoc i1 + measure_assoc i2)"
| "measure_assoc (tIf _ i1 i2) = Suc (measure_assoc i1 + measure_assoc i2)"
| "measure_assoc _ = 0"

function (sequential) assoc_right_tSeq where
  "assoc_right_tSeq (tSeq (tSeq i1 i2) i3) = assoc_right_tSeq (tSeq i1 (tSeq i2 i3))"
| "assoc_right_tSeq (tSeq i1 i2) = tSeq i1 (assoc_right_tSeq i2)"
| "assoc_right_tSeq (tIf r i1 i2) = tIf r (assoc_right_tSeq i1) (assoc_right_tSeq i2)"
| "assoc_right_tSeq i = i"
  by pat_completeness auto
termination by (relation "measure measure_assoc") auto

lemma tbig_step_t_tSeq_assoc:
  includes tcom_syntax
  shows "C \<turnstile> ((c1 ;; c2) ;; c3, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<longleftrightarrow> C \<turnstile> (c1 ;; (c2 ;; c3), s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  by auto

lemma tbig_step_t_assoc_right_tSeq:
  shows "C \<turnstile> (assoc_right_tSeq c, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<longleftrightarrow> C \<turnstile> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
proof(induction c arbitrary: s t s' rule: assoc_right_tSeq.induct)
  case (3 r i1 i2)
  then show ?case
    using tIfFalse by fastforce
qed(auto simp: tbig_step_t_tSeq_assoc intro!: Suc_eq_plus1)

fun tseq where
  "tseq tSKIP c = c"
| "tseq c tSKIP = c"
| "tseq c1 c2 = tSeq c1 c2"

fun rm_tSKIP where
  "rm_tSKIP (tSeq c1 c2) = tseq (rm_tSKIP c1) (rm_tSKIP c2)"
| "rm_tSKIP (tIf v c1 c2) = tIf v (rm_tSKIP c1) (rm_tSKIP c2)"
| "rm_tSKIP c = c"

lemma tbig_step_t_tseq:
  assumes "C \<turnstile> (c1, s0) \<Rightarrow>\<^bsup>t1\<^esup> s1" "C \<turnstile> (c2, s1) \<Rightarrow>\<^bsup>t2\<^esup> s2"
  shows "\<exists>t'. C \<turnstile> (tseq c1 c2, s0) \<Rightarrow>\<^bsup>t'\<^esup> s2 \<and> t' \<le> t1 + t2"
proof -
  consider
    "c1 = tSKIP" | "c1 \<noteq> tSKIP" "c2 = tSKIP" | "c1 \<noteq> tSKIP" "c2 \<noteq> tSKIP"
    by (cases c1; cases c2) auto
  then show ?thesis
  proof cases
    case 1
    with assms show ?thesis
      using tSkip by auto
  next
    case 2
    with assms show ?thesis
      using tSkip by (cases c1) auto
  next
    case 3
    then have "tseq c1 c2 = tSeq c1 c2"
      by (cases c1; cases c2) simp_all
    with assms show ?thesis
      using tSeq by auto
  qed
qed

lemma tbig_step_t_rm_tSKIP:
  assumes "C \<turnstile> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "\<exists>t'. C \<turnstile> (rm_tSKIP c, s) \<Rightarrow>\<^bsup>t'\<^esup> s' \<and> t' \<le> t"
  using assms
proof(induction c arbitrary: s t s' rule: rm_tSKIP.induct)
  case (1 c1 c2)
  then obtain t1 s1 t2 where
    "C \<turnstile> (rm_tSKIP c1, s) \<Rightarrow>\<^bsup>t1\<^esup> s1" "C \<turnstile> (rm_tSKIP c2, s1) \<Rightarrow>\<^bsup>t2\<^esup> s'"
    "t1 + t2 \<le> t"
    by (metis add_mono tSeq_tE)
  with 1 show ?case using tbig_step_t_tseq by fastforce
next
  case (2 v c1 c2)
  then show ?case
  proof(cases "s v = 0")
    case True
    with "2.prems"[THEN tIf_tE] "2.IH"(2) obtain t' where
      "C \<turnstile> (rm_tSKIP c2, s) \<Rightarrow>\<^bsup>t'\<^esup> s'" "Suc t' \<le> t"
      by (metis Suc_le_mono less_numeral_extra(3))
    with True show ?thesis
      unfolding rm_tSKIP.simps by force
  next
    case False
    with "2.prems"[THEN tIf_tE] "2.IH"(1) obtain t' where
      "C \<turnstile> (rm_tSKIP c1, s) \<Rightarrow>\<^bsup>t'\<^esup> s'" "Suc t' \<le> t"
      by (metis Suc_le_mono)
    with False show ?thesis
      unfolding rm_tSKIP.simps by force
  qed
qed auto

definition "tailcall_to_IMP_Minus \<equiv> inline o compile"

lemma tailcall_to_IMP_Minus_eq: "tailcall_to_IMP_Minus c = inline (compile c)"
  unfolding tailcall_to_IMP_Minus_def by simp

named_theorems compiled_const_defs
ML_file\<open>compile_nat.ML\<close>


end
