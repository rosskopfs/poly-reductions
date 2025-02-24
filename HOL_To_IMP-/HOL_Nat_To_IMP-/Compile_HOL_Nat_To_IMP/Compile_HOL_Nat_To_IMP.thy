\<^marker>\<open>creator "Lukas Stevens"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
theory Compile_HOL_Nat_To_IMP
  imports
    IMP_Terminates_With
    HOL_Nat_To_IMP_Minus_Base
    HOL_To_HOL_Nat.HOL_To_HOL_Nat_Basics
    "HOL-Library.AList"
  keywords
    "compile_nat" :: thy_decl and "basename" and "non-optimized" and
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

lemma size_assoc_right_tSeq [termination_simp]: "size (assoc_right_tSeq t) = size t"
  by (induction t rule: assoc_right_tSeq.induct) auto

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

fun rm_tSkip_tseq where
  "rm_tSkip_tseq tSKIP c = c"
| "rm_tSkip_tseq c tSKIP = c"
| "rm_tSkip_tseq c1 c2 = tSeq c1 c2"

fun rm_tSKIP where
  "rm_tSKIP (tSeq c1 c2) = rm_tSkip_tseq (rm_tSKIP c1) (rm_tSKIP c2)"
| "rm_tSKIP (tIf v c1 c2) = tIf v (rm_tSKIP c1) (rm_tSKIP c2)"
| "rm_tSKIP c = c"

lemma tbig_step_t_rm_tSkip_tseq:
  assumes "C \<turnstile> (c1, s0) \<Rightarrow>\<^bsup>t1\<^esup> s1" "C \<turnstile> (c2, s1) \<Rightarrow>\<^bsup>t2\<^esup> s2"
  shows "\<exists>t'. C \<turnstile> (rm_tSkip_tseq c1 c2, s0) \<Rightarrow>\<^bsup>t'\<^esup> s2 \<and> t' \<le> t1 + t2"
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
    then have "rm_tSkip_tseq c1 c2 = tSeq c1 c2"
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
  with 1 show ?case using tbig_step_t_rm_tSkip_tseq by fastforce
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

(*input: right-associated program*)
(*output: all ifs are pulled out + right-associated*)
fun pull_tIf_assoc_right where
  "pull_tIf_assoc_right (tSeq (tIf v c1 c2) c3) = tIf v
    (pull_tIf_assoc_right (assoc_right_tSeq (tSeq c1 c3)))
    (pull_tIf_assoc_right (assoc_right_tSeq (tSeq c2 c3)))"
| "pull_tIf_assoc_right (tSeq c1 c2) = tSeq c1 (pull_tIf_assoc_right c2)"
| "pull_tIf_assoc_right (tIf v c1 c2) = tIf v (pull_tIf_assoc_right c1) (pull_tIf_assoc_right c2)"
| "pull_tIf_assoc_right c = c"

lemma tbig_step_pull_tIf_iff_aux:
  includes tcom_syntax
  shows "C \<turnstile> (tSeq (tIf v c1 c2) c3, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<longleftrightarrow> C \<turnstile> (tIf v (tSeq c1 c3) (tSeq c2 c3), s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  by auto

lemma tbig_step_pull_tIf_iff:
  shows "C \<turnstile> (pull_tIf_assoc_right c, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<longleftrightarrow> C \<turnstile> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  by (induction c arbitrary: s t s' rule: pull_tIf_assoc_right.induct)
  (fastforce simp: tbig_step_t_assoc_right_tSeq tbig_step_pull_tIf_iff_aux)+

definition "get_reg al r \<equiv> case map_of al r of None \<Rightarrow> V r | Some x \<Rightarrow> x"

lemma get_reg_upadte_eq: "get_reg (AList.update x y al) x = y"
  unfolding get_reg_def by (induction al) auto

fun subst_atomExp :: "atomExp \<Rightarrow> (vname \<times> atomExp) list \<Rightarrow> atomExp" where
  "subst_atomExp (V r) al = get_reg al r"
| "subst_atomExp a _ = a"

fun subst_aexp :: "aexp \<Rightarrow> (vname \<times> atomExp) list \<Rightarrow> aexp" where
  "subst_aexp (A a) al = A (subst_atomExp a al)"
| "subst_aexp (Plus a1 a2) al = Plus (subst_atomExp a1 al) (subst_atomExp a2 al)"
| "subst_aexp (Sub a1 a2) al = Sub (subst_atomExp a1 al) (subst_atomExp a2 al)"

fun trans_assigns_aux :: "tcom \<Rightarrow> (vname \<times> atomExp) list \<Rightarrow> tcom \<times> (vname \<times> atomExp) list" where
  "trans_assigns_aux (tSeq c1 c2) al = (
    let
      (c1', al') = trans_assigns_aux c1 al;
      (c2', al'') = trans_assigns_aux c2 al'
    in (tSeq c1' c2', al''))"
| "trans_assigns_aux (tIf v c1 c2) al = (
    let
      (c1', al'1) = trans_assigns_aux c1 al;
      (c2', al'2) = trans_assigns_aux c2 al
    in (tIf (case get_reg al v of (V v') \<Rightarrow> v' | _ \<Rightarrow> v) c1' c2', filter (List.member al'2) al'1))"
| "trans_assigns_aux (tAssign v a) al = (let a' = subst_aexp a al
    in (tAssign v a', case a' of A atom \<Rightarrow> AList.update v atom al | _ \<Rightarrow> al))"
| "trans_assigns_aux (tCall c v) al = (tCall c v, filter (\<lambda>(_, v'). v' \<noteq> V v) al)"
| "trans_assigns_aux c al = (c, al)"

definition "trans_assigns c \<equiv> fst (trans_assigns_aux c [])"

definition "register_sep \<equiv> ''.''"
definition "arg_sep \<equiv> ''arg''"

definition "is_prefix xs ys \<equiv> take (length ys) xs = ys"

fun is_arg :: "vname \<Rightarrow> bool" where
  "is_arg (x # xs) = (is_prefix xs (register_sep @ arg_sep @ register_sep) \<or> is_arg xs)"
| "is_arg [] = False"

fun bury_aux :: "tcom \<Rightarrow> vname list \<Rightarrow> tcom \<times> vname list" where
  "bury_aux (tSeq c1 c2) vl = (
    let
      (c2', vl') = bury_aux c2 vl;
      (c1', vl'') = bury_aux c1 vl'
    in (tSeq c1' c2', vl''))"
| "bury_aux (tIf v c1 c2) vl = (
    let
      (c1', vl'1) = bury_aux c1 vl;
      (c2', vl'2) = bury_aux c2 vl
    in (tIf v c1' c2', v # vl'1 @ vl'2))"
| "bury_aux (tAssign v a) vl = (if a = A (V v) \<or> (v \<notin> set vl \<and> \<not>is_arg v)
    then (tSKIP, vl)
    else (tAssign v a, vars a @ filter ((\<noteq>) v) vl))"
| "bury_aux (tCall c v) vl = (if v \<in> set vl
    then (tCall c v, filter ((\<noteq>) v) vl)
    else (tSKIP, vl))"
| "bury_aux c vl = (c, vl)"
definition
  "bury ret_reg c \<equiv> fst (bury_aux c [ret_reg])"

unbundle tcom_syntax

context HOL_To_HOL_Nat
begin

definition "If_nat b x y \<equiv> HOL.If (b = False_nat) y x"

lemma Rel_nat_If_nat [Rel_nat]: "(Rel_nat ===> Rel_nat ===> Rel_nat ===> Rel_nat) If_nat HOL.If"
  unfolding If_nat_def by (fastforce simp: Rel_nat_bool_iff True_nat_ne_False_nat)

end

declare tailcall_to_IMP_Minus_def[code del]

ML_file\<open>compile_hol_nat_to_imp.ML\<close>

end
