\<^marker>\<open>creator "Lukas Stevens"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
\<^marker>\<open>contributor "Nico Lintner"\<close>
theory Compile_HOL_Nat_To_IMP
  imports
    IMP_Terminates_With
    HOL_Nat_To_IMP_Base
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

fun subst_atomExp :: "atomExp \<Rightarrow> (vname \<times> atomExp) list \<Rightarrow> atomExp" where
  "subst_atomExp (V r) al = get_reg al r"
| "subst_atomExp a _ = a"

fun subst_aexp :: "aexp \<Rightarrow> (vname \<times> atomExp) list \<Rightarrow> aexp" where
  "subst_aexp (A a) al = A (subst_atomExp a al)"
| "subst_aexp (Plus a1 a2) al = (case (subst_atomExp a1 al, subst_atomExp a2 al) of
    (N n1, N n2) \<Rightarrow> A (N (n1 + n2)) |
    (N 0, V v) \<Rightarrow> A (V v) | (V v, N 0) \<Rightarrow> A (V v) |
    (a1', a2') \<Rightarrow> Plus a1' a2')"
| "subst_aexp (Sub a1 a2) al = (case (subst_atomExp a1 al, subst_atomExp a2 al) of
    (N n1, N n2) \<Rightarrow> A (N (n1 - n2)) |
    (N 0, V v) \<Rightarrow> A (N 0) | (V v, N 0) \<Rightarrow> A (V v) |
    (a1', a2') \<Rightarrow> Sub a1' a2')"

definition
  "rm_assn_var v \<equiv> filter (\<lambda>(_, v'). v' \<noteq> V v)"

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
    in (case get_reg al v of V v' \<Rightarrow> (tIf v' c1' c2', filter (List.member al'2) al'1) |
          N 0 \<Rightarrow> (tSeq tSKIP c2', al'2) | N n \<Rightarrow> (tSeq tSKIP c1', al'1)))"
| "trans_assigns_aux (tAssign v a) al = (let a' = subst_aexp a al
    in (tAssign v a',
      rm_assn_var v (case a' of A atom \<Rightarrow> AList.update v atom al | _ \<Rightarrow> AList.delete_aux v al)))"
| "trans_assigns_aux (tCall c v) al = (tCall c v, rm_assn_var v (AList.delete_aux v al))"
| "trans_assigns_aux tTAIL al = (tTAIL, [])"
| "trans_assigns_aux tSKIP al = (tSKIP, al)"

definition "trans_assigns c \<equiv> fst (trans_assigns_aux c [])"

lemma al_delete_keep_invar:
  assumes "\<And>x y. (x, y) \<in> set al \<Longrightarrow> s x = atomVal y s" "distinct (map fst al)"
  shows "\<And>x y. (x, y) \<in> set (rm_assn_var v (AList.delete_aux v al)) \<Longrightarrow>
    (s (v := a)) x = atomVal y (s (v := a))"
  using assms by (auto simp: rm_assn_var_def set_delete_aux)
    (metis fun_upd_other atomExp.exhaust atomVal.simps)

lemma atomVal_get_reg_eq_atomVal:
  assumes "\<And>x y. (x, y) \<in> set al \<Longrightarrow> s x = atomVal y s"
  shows "atomVal (get_reg al v) s = atomVal (V v) s"
  using assms by (induction al) (fastforce simp: get_reg_def)+

lemma atomVal_subst_atomExp_eq_atomVal:
  assumes "\<And>x y. (x, y) \<in> set al \<Longrightarrow> s x = atomVal y s"
  shows "atomVal (subst_atomExp a al) s = atomVal a s"
  using atomVal_get_reg_eq_atomVal[OF assms] by (cases a) simp_all

lemma aval_subst_aexp_eq_aval:
  assumes "\<And>x y. (x, y) \<in> set al \<Longrightarrow> s x = atomVal y s"
  shows "aval (subst_aexp a al) s = aval a s"
  using atomVal_subst_atomExp_eq_atomVal[OF assms] atomVal_get_reg_eq_atomVal[OF assms]
  by (cases a) 
    (auto simp: nat.case_eq_if split: atomExp.split;
      metis add_cancel_left_left add_cancel_left_right atomVal.simps less_eq_nat.simps(1) diff_zero)+


lemma trans_assigns_aux_al_distinct:
  assumes "(c', al') = trans_assigns_aux c al" "distinct (map fst al)"
  shows "distinct (map fst al')"
  using assms by (induction c al arbitrary: c' al' rule: trans_assigns_aux.induct)
    (auto simp: distinct_map_filter distinct_update distinct_delete rm_assn_var_def Let_def
      split: prod.splits aexp.split atomExp.splits nat.splits)

lemma tbig_step_trans_assigns_aux1:
  includes tcom_syntax
  assumes "(c', al') = trans_assigns_aux c al"
    and "C \<turnstile> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
    and "\<And>x y. (x, y) \<in> set al \<Longrightarrow> s x = atomVal y s" "distinct (map fst al)"
  shows "C \<turnstile> (c', s) \<Rightarrow>\<^bsup>t\<^esup> s'" "\<And>x y. ((x, y) \<in> set al' \<Longrightarrow> s' x = atomVal y s')"
proof -
  from assms have "C \<turnstile> (c', s) \<Rightarrow>\<^bsup>t\<^esup> s' \<and> (\<forall>(x, y) \<in> set al'. s' x = atomVal y s')"
  proof (induction c al arbitrary: c' al' s t s' rule: trans_assigns_aux.induct)
    case (1 c1 c2 al)
    from 1(3) obtain c1' al1 c2' where prod: "(c1', al1) = trans_assigns_aux c1 al"
        "(c2', al') = trans_assigns_aux c2 al1"
      by (simp split: prod.splits)
    obtain t1 s1 t2 where obt: "C \<turnstile> (c1, s) \<Rightarrow>\<^bsup>t1\<^esup>  s1" "C \<turnstile> (c2, s1) \<Rightarrow>\<^bsup>t2\<^esup>  s'" "t1 + t2 = t"
      using 1(4) by blast
    have left: "C \<turnstile> (c1', s) \<Rightarrow>\<^bsup>t1\<^esup>  s1" "\<And>x y. (x, y) \<in> set al1 \<Longrightarrow> s1 x = atomVal y s1"
      using 1(1)[OF prod(1) obt(1) 1(5,6)] by blast+
    have right: "C \<turnstile> (c2', s1) \<Rightarrow>\<^bsup>t2\<^esup>  s'" "\<And>x y. (x, y) \<in> set al' \<Longrightarrow> s' x = atomVal y s'"
      using 1(2)[OF prod(1) refl prod(2) obt(2) left(2)
          trans_assigns_aux_al_distinct[OF prod(1) 1(6)]] by blast+
    from left right obt(3) 1(3) prod show ?case by (auto split: prod.splits)
  next                               
    case (2 v c1 c2 al)
    have v': "s (case get_reg al v of V v' \<Rightarrow> v' | _ \<Rightarrow> v) = s v" 
      using atomVal_get_reg_eq_atomVal[OF 2(5), of al v] by (auto split: atomExp.split)
    show ?case
    proof (cases "s v = 0")
      case True
      with 2(4)[THEN tIf_tE] obtain t' where t': "C \<turnstile> (c2, s) \<Rightarrow>\<^bsup>t'\<^esup> s'" "t = t' + 1" "t = Suc 0 + t'"
        using bot_nat_0.not_eq_extremum by auto
      obtain c2' al2 where obt2: "(c2', al2) = trans_assigns_aux c2 al" by (simp add: split_pairs)
      have 1: "C \<turnstile> (c2', s) \<Rightarrow>\<^bsup>t'\<^esup>  s'" "\<And>x y. (x, y) \<in> set al2 \<Longrightarrow> s' x = atomVal y s'"
        using 2(2)[OF _ refl obt2 t'(1) 2(5,6)] prod.collapse by blast+
      have case_dest: "case get_reg al v of N n \<Rightarrow> n = 0 | V v' \<Rightarrow> s v' = 0"
        using True obt2 2(3) atomVal_get_reg_eq_atomVal[OF 2(5), of al v]
        by (simp split: prod.splits atomExp.splits nat.splits)
      with 2(3) obt2 have "set al' \<subseteq> set al2"
        by (auto split: prod.splits atomExp.splits simp: member_def)
      with 1(2) have "\<And>x y. (x, y) \<in> set al' \<Longrightarrow> s' x = atomVal y s'" by blast
      moreover from True case_dest 2(3) obt2 have "C \<turnstile> (c', s) \<Rightarrow>\<^bsup>t\<^esup>  s'" 
        using tIfFalse[OF True[folded v'] 1(1) t'(2)] tSeq[OF tSkip t'(1) t'(3)]
        by (fastforce split: prod.splits atomExp.splits nat.splits) 
      ultimately show ?thesis by blast
    next
      case False
      with 2(4)[THEN tIf_tE] obtain t' where t': "C \<turnstile> (c1, s) \<Rightarrow>\<^bsup>t'\<^esup> s'" "t = t' + 1" "t = Suc 0 + t'"
        using bot_nat_0.not_eq_extremum by auto
      obtain c1' al1 where obt1: "(c1', al1) = trans_assigns_aux c1 al" by (simp add: split_pairs)
      have 1: "C \<turnstile> (c1', s) \<Rightarrow>\<^bsup>t'\<^esup>  s'" "\<And>x y. (x, y) \<in> set al1 \<Longrightarrow> s' x = atomVal y s'"
        using 2(1)[OF obt1 t'(1) 2(5,6)] by blast+
      have case_dest: "case get_reg al v of N n \<Rightarrow> n \<noteq> 0 | V v' \<Rightarrow> s v' \<noteq> 0"
        using False obt1 2(3) atomVal_get_reg_eq_atomVal[OF 2(5), of al v]
        by (simp split: prod.splits atomExp.splits nat.splits)
      with obt1 2(3) have "set al' \<subseteq> set al1"
        by (auto simp: member_def split: prod.splits atomExp.splits nat.splits)
      with 1(2) have "\<And>x y. (x, y) \<in> set al' \<Longrightarrow> s' x = atomVal y s'" by blast
      moreover from False case_dest 2(3) obt1 have "C \<turnstile> (c', s) \<Rightarrow>\<^bsup>t\<^esup>  s'" 
        using tIfTrue[OF False[folded v'] 1(1) t'(2)] tSeq[OF tSkip t'(1) t'(3)]
        by (fastforce split: prod.splits atomExp.splits nat.splits)
      ultimately show ?thesis by blast
    qed
  next
    case (3 v a al)
    from 3(1,2) have t: "t = Suc (Suc 0)" and s': "s' = s (v := aval a s)" by blast+
    have aval_same: "aval (subst_aexp a al) s = aval a s"
      using aval_subst_aexp_eq_aval[OF 3(3)] by blast
    with 3(1) t s' have "C \<turnstile> (c', s) \<Rightarrow>\<^bsup>t\<^esup> s'"
      using tAssign[of C v "subst_aexp a al" s] by (simp add: split_pairs Let_def)
    moreover have "s' x = atomVal y s'" if asm: "(x, y) \<in> set al'" for x y
    proof -
      have s': "s' = s (v := aval a s)"
        using 3(1,2) by auto
      from asm 3(1) have "y \<noteq> (V v)"
        by (auto simp: rm_assn_var_def Let_def)
      then have y_same: "atomVal y s' = atomVal y s"
        unfolding s' by (cases y) simp_all
      show "s' x = atomVal y s'"
      proof (cases "subst_aexp a al")
        case (A atom)
        then have al': "al' = rm_assn_var v (AList.update v atom al)"
          using 3(1) by simp
        show ?thesis
        proof (cases "x = v")
          case True
          from asm update_Some_unfold[of v atom al x y] have "y = atom"
            using Some_eq_map_of_iff[OF distinct_update[OF 3(4)], of y v atom x]
            unfolding al' rm_assn_var_def True by simp
          from aval_same y_same show ?thesis by (simp add: A  \<open>y = atom\<close> True s')
        next
          case False
          then have x_same: "s' x = s x"
            unfolding s' by simp
          from distinct_update[OF 3(4), of v atom] have "(x, y) \<in> set al"
            using False asm update_Some_unfold[of v atom al x y] 3(4)
            unfolding rm_assn_var_def al' by simp
          with 3(3) x_same y_same show ?thesis by presburger
        qed
      next
        case (Plus x21 x22)
        then have "(x, y) \<in> set (rm_assn_var v (AList.delete_aux v al))"
          using 3(1) asm by simp
        from al_delete_keep_invar[OF 3(3,4) this] s' show ?thesis by blast
      next
        case (Sub x31 x32)
        then have "(x, y) \<in> set (rm_assn_var v (AList.delete_aux v al))"
          using 3(1) asm by simp
        from al_delete_keep_invar[OF 3(3,4) this] s' show ?thesis by blast
      qed
    qed
    ultimately show ?case by blast
  next
    case (4 c v al)
    from 4(1,2) al_delete_keep_invar[OF 4(3,4)] show ?case by auto
  qed auto
  then show "C \<turnstile> (c', s) \<Rightarrow>\<^bsup>t\<^esup> s'" "\<And>x y. ((x, y) \<in> set al' \<Longrightarrow> s' x = atomVal y s')" by blast+
qed

lemma tbig_step_trans_assigns_aux2:
  includes tcom_syntax
  assumes "(c', al') = trans_assigns_aux c al"
    and "C \<turnstile> (c', s) \<Rightarrow>\<^bsup>t\<^esup> s'"
    and "\<And>x y. (x, y) \<in> set al \<Longrightarrow> s x = atomVal y s" "distinct (map fst al)"
  shows "C \<turnstile> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s'" "\<And>x y. ((x, y) \<in> set al' \<Longrightarrow> s' x = atomVal y s')"
proof -
  from assms have "C \<turnstile> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<and> (\<forall>(x, y) \<in> set al'. s' x = atomVal y s')"
  proof (induction c al arbitrary: c' al' s t s' rule: trans_assigns_aux.induct)
    case (1 c1 c2 al)
    from 1(3) obtain c1' al1 c2' where prod: "(c1', al1) = trans_assigns_aux c1 al"
        "(c2', al') = trans_assigns_aux c2 al1"
      by (simp split: prod.splits)
    obtain t1 s1 t2 where obt: "C \<turnstile> (c1', s) \<Rightarrow>\<^bsup>t1\<^esup>  s1" "C \<turnstile> (c2', s1) \<Rightarrow>\<^bsup>t2\<^esup>  s'" "t1 + t2 = t"
      using prod 1(3,4) by (auto split: prod.splits)
    have left: "C \<turnstile> (c1, s) \<Rightarrow>\<^bsup>t1\<^esup>  s1" "\<And>x y. (x, y) \<in> set al1 \<Longrightarrow> s1 x = atomVal y s1"
      using 1(1)[OF prod(1) obt(1) 1(5,6)] by blast+
    have right: "C \<turnstile> (c2, s1) \<Rightarrow>\<^bsup>t2\<^esup>  s'" "\<And>x y. (x, y) \<in> set al' \<Longrightarrow> s' x = atomVal y s'"
      using 1(2)[OF prod(1) refl prod(2) obt(2) left(2)
          trans_assigns_aux_al_distinct[OF prod(1) 1(6)]] by blast+
    from left right obt(3) 1(3) prod show ?case by (auto split: prod.splits)
  next
    case (2 v c1 c2 al)
    have v_same: "(case get_reg al v of (V v') \<Rightarrow> s v' | (N n) \<Rightarrow> n) = s v"
      using atomVal_get_reg_eq_atomVal[OF 2(5), of al v] by (auto split: atomExp.splits)
    have "C \<turnstile> (IF v\<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup>t\<^esup>  s'"
    proof (cases "get_reg al v")
      case (N n)
      show ?thesis
      proof (cases "n = 0")
        case True
        with v_same 2(3,4) N have c': "c' = tSKIP;;fst (trans_assigns_aux c2 al)" 
          by (auto split: prod.splits atomExp.splits nat.splits)
        then obtain t' where "C \<turnstile> (fst (trans_assigns_aux c2 al), s) \<Rightarrow>\<^bsup>t'\<^esup>  s'" "t = t' + 1"
          using 2(4)[unfolded c'] by auto
        with True tIfFalse[of s v] v_same 2(2) 2(5,6) N show ?thesis by (simp add: split_pairs)
      next
        case False
        with v_same 2(3,4) N have c': "c' = tSKIP;;fst (trans_assigns_aux c1 al)" 
          by (auto split: prod.splits atomExp.splits nat.splits)
        then obtain t' where "C \<turnstile> (fst (trans_assigns_aux c1 al), s) \<Rightarrow>\<^bsup>t'\<^esup>  s'" "t = t' + 1"
          using 2(4)[unfolded c'] by auto
        with False tIfTrue[of s v] v_same 2(1) 2(5,6) N show ?thesis by (simp add: split_pairs)
      qed
    next
      case (V v')
      with 2(3) have c': "c' = IF v'\<noteq>0 THEN (fst (trans_assigns_aux c1 al)) ELSE (fst (trans_assigns_aux c2 al))"
        by (auto split: prod.splits atomExp.splits nat.splits)
      show ?thesis
      proof (cases "s v = 0")
        case True
        then obtain t' where "C \<turnstile> (fst (trans_assigns_aux c2 al), s) \<Rightarrow>\<^bsup>t'\<^esup>  s'" "t = t' + 1"
          using V 2(4)[unfolded c', THEN tIf_tE] v_same by auto
        then show ?thesis
          using tIfFalse[of s, OF True] 2(2) 2(5,6) by (simp add: split_pairs)
      next
        case False
        then obtain t' where "C \<turnstile> (fst (trans_assigns_aux c1 al), s) \<Rightarrow>\<^bsup>t'\<^esup>  s'" "t = t' + 1"
          using V 2(4)[unfolded c', THEN tIf_tE] v_same by auto
        then show ?thesis
          using tIfTrue[of s, OF False] 2(1) 2(5,6) by (simp add: split_pairs)
      qed
    qed
    with tbig_step_trans_assigns_aux1(2)[OF 2(3) this 2(5,6)] show ?case by blast
  next
    case (3 v a al)
    from 3(1,2) have "C \<turnstile> (v ::= a, s) \<Rightarrow>\<^bsup>t\<^esup>  s'"
      using aval_subst_aexp_eq_aval[OF 3(3)] by (auto simp: Let_def)
    with tbig_step_trans_assigns_aux1(2)[OF 3(1) this 3(3,4)] show ?case by blast
  next
    case (4 c v al)
    from tbig_step_trans_assigns_aux1(2)[OF 4(1) _ 4(3,4)] 4(1,2) show ?case by fastforce
  qed auto
  then show "C \<turnstile> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s'" "\<And>x y. ((x, y) \<in> set al' \<Longrightarrow> s' x = atomVal y s')" by blast+
qed

lemma tbig_step_trans_assigns_aux_iff:
  notes impl_1_2 = tbig_step_trans_assigns_aux1(1) tbig_step_trans_assigns_aux2(1)
  assumes "(c', al') = trans_assigns_aux c al"
    and "\<And>x y. (x, y) \<in> set al \<Longrightarrow> s x = atomVal y s" "distinct (map fst al)"
  shows "C \<turnstile> (c', s) \<Rightarrow>\<^bsup>t\<^esup> s' \<longleftrightarrow> C \<turnstile> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  using impl_1_2[OF assms(1) _ assms(2,3)] by blast

lemma tbig_step_trans_assigns_iff: "C \<turnstile> (trans_assigns c, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<longleftrightarrow> C \<turnstile> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  using tbig_step_trans_assigns_aux_iff[of _ _ c "[]" s C t s']
  by (simp add: split_pairs trans_assigns_def)


(*FIXME: proper analysis of arguments used in calls instead of comparison against unstable naming
convention*)

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
| "bury_aux (tCall c v) vl = (if v \<in> set vl \<or> is_arg v
    then (tCall c v, filter ((\<noteq>) v) vl)
    else (tSKIP, vl))"
| "bury_aux tTAIL vl = (tTAIL, [])"
| "bury_aux tSKIP vl = (tSKIP, vl)"

definition
  "bury ret_reg c \<equiv> fst (bury_aux c [ret_reg])"

context HOL_To_HOL_Nat
begin

definition "If_nat b x y \<equiv> HOL.If (b = False_nat) y x"

lemma Rel_nat_If_nat [Rel_nat]: "(Rel_nat ===> Rel_nat ===> Rel_nat ===> Rel_nat) If_nat HOL.If"
  unfolding If_nat_def by (fastforce simp: Rel_nat_bool_iff True_nat_ne_False_nat)

end

lemma Let_lambda_eq_Let: "(let x = t in (\<lambda>y. f y x)) y = (let x = t in f y x)" by simp
lemmas Let_compile_simps = Let_const Let_lambda_eq_Let

declare tailcall_to_IMP_def[code del]

ML_file\<open>compile_hol_nat_to_imp.ML\<close>

end
