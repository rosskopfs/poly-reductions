\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory IMP_Terminates_With_Time
  imports IMP_Terminates_With
begin

(*time experiments*)
paragraph \<open>With Times\<close>

definition "scale_linear c n x \<equiv> c + n * x"

lemma scale_linear_eq_add_mul [simp]: "scale_linear c n x = c + n * x"
  unfolding scale_linear_def by simp

definition "linear_in c n x y \<equiv> y \<le> scale_linear c n x"

lemma linear_in_eq_le_scale_linear: "linear_in c n x = (\<ge>) (scale_linear c n x)"
  unfolding linear_in_def by (intro ext) simp

lemma linear_inI [intro]:
  assumes "y \<le> scale_linear c n x"
  shows "linear_in c n x y"
  using assms unfolding linear_in_eq_le_scale_linear by auto

lemma linear_inD [dest]:
  assumes "linear_in c n x y"
  shows "y \<le> scale_linear c n x"
  using assms unfolding linear_in_eq_le_scale_linear by auto

definition "terminates_with_res_linear_in_IMP_Minus P p r f ft \<equiv> \<exists>c n. \<forall>s. P s \<longrightarrow>
  terminates_with_res_pred_time_IMP_Minus p s r (f s) (linear_in c n (ft s))"

lemma terminates_with_res_linear_in_IMP_MinusI:
  assumes "\<And>s. P s \<Longrightarrow> terminates_with_res_pred_time_IMP_Minus p s r (f s) (linear_in c n (ft s))"
  shows "terminates_with_res_linear_in_IMP_Minus P p r f ft"
  using assms unfolding terminates_with_res_linear_in_IMP_Minus_def by blast

lemma terminates_with_res_linear_in_IMP_MinusE:
  assumes "terminates_with_res_linear_in_IMP_Minus P p r f ft"
  obtains c n where
    "\<And>s. P s \<Longrightarrow> terminates_with_res_pred_time_IMP_Minus p s r (f s) (linear_in c n (ft s))"
  using assms unfolding terminates_with_res_linear_in_IMP_Minus_def by blast

definition "terminates_with_res_linear_in_IMP_Tailcall P tp p r f ft \<equiv> \<exists>c n. \<forall>s. P s \<longrightarrow>
  terminates_with_res_pred_time_IMP_Tailcall tp p s r (f s) (linear_in c n (ft s))"

lemma terminates_with_res_linear_in_IMP_TailcallI:
  assumes "\<And>s. P s \<Longrightarrow> terminates_with_res_pred_time_IMP_Tailcall tp p s r (f s) (linear_in c n (ft s))"
  shows "terminates_with_res_linear_in_IMP_Tailcall P tp p r f ft"
  using assms unfolding terminates_with_res_linear_in_IMP_Tailcall_def by blast

lemma terminates_with_res_linear_in_IMP_TailcallE:
  assumes "terminates_with_res_linear_in_IMP_Tailcall P tp p r f ft"
  obtains c n where
    "\<And>s. P s \<Longrightarrow> terminates_with_res_pred_time_IMP_Tailcall tp p s r (f s) (linear_in c n (ft s))"
  using assms unfolding terminates_with_res_linear_in_IMP_Tailcall_def by blast

context
  notes
    terminates_with_res_linear_in_IMP_TailcallE[elim]
    terminates_with_res_linear_in_IMP_TailcallI[intro]
begin

lemma terminates_with_res_linear_in_IMP_Minus_if_terminates_with_res_linear_in_IMP_TailcallI:
  assumes "invar p"
  and "r \<in> set (vars p)"
  and "terminates_with_res_linear_in_IMP_Tailcall P p p r f ft"
  shows "terminates_with_res_linear_in_IMP_Minus P (tailcall_to_IMP_Minus p) r f ft"
proof -
  from assms obtain c n where termtc:
    "terminates_with_res_pred_time_IMP_Tailcall p p s r (f s) (linear_in c n (ft s))" if "P s" for s
    by fastforce
  let ?c' = 8 and ?n' = "1 + size\<^sub>c (compile p)"
  let ?c = "(c + ?c') * ?n'" and ?n = "n * ?n'"
  show ?thesis
  proof (rule terminates_with_res_linear_in_IMP_MinusI)
    fix s assume "P s"
    with termtc have "terminates_with_res_pred_time_IMP_Tailcall p p s r (f s) (linear_in c n (ft s))"
      by blast
    with assms(1,2) obtain t t' s' where
      correct: "s' r = f s" "(tailcall_to_IMP_Minus p, s) \<Rightarrow>\<^bsup> t'\<^esup> s'"
      and linears: "linear_in c n (ft s) t" "t' \<le> (?c' + t) * ?n'"
      by (elim terminates_with_res_pred_time_IMP_TailcallE terminates_with_pred_time_IMP_TailcallE
        compile_sound inline_sound[where ?s=s and ?s'=s for s])
      (auto simp: tailcall_to_IMP_Minus_eq eq_on_def set_vars_compile algebra_simps)
    have "linear_in ?c ?n (ft s) t'"
    proof -
      from linears have "t' \<le> (?c' + t) * ?n'" by simp
      also have "... = ?c' * ?n' + t * ?n'" by (auto simp: algebra_simps)
      also from linears have "... \<le> ?c' * ?n' + (c + n * ft s) * ?n'"
        unfolding linear_in_eq_le_scale_linear scale_linear_eq_add_mul
        using mult_le_mono1 nat_add_left_cancel_le by blast
      also have "... = ?c + ?n * (ft s)" by (auto simp: algebra_simps)
      finally show ?thesis by auto
    qed
    with correct show "terminates_with_res_pred_time_IMP_Minus (tailcall_to_IMP_Minus p) s r (f s)
      (linear_in ?c ?n (ft s))"
      by (intro terminates_with_res_pred_time_IMP_MinusI terminates_with_pred_time_IMP_MinusI)
  qed
qed

(*FIXME: this approach does not work; instead, one needs to pre-compute suitable c, n by taking the
all c_i, n_i of all contained subprograms (+ some constant for assignments, etc.)*)
lemma linear_in_add_tSeqI:
  assumes "linear_in c1 n1 x y"
  and "linear_in c2 n2 x y'"
  and "c1 + c2 \<le> c"
  and "n1 + n2 \<le> n"
  shows "linear_in (c :: nat) n x (y + y')"
  apply (rule linear_inI, unfold scale_linear_eq_add_mul)
  apply (rule le_trans[of _ "c1 + c2 + (n1 + n2) * x"])
  using assms apply (simp_all only: algebra_simps)
  apply (fastforce simp: algebra_simps)[]
  using nat_le_iff_add by (auto simp: algebra_simps)

lemma terminates_with_res_linear_in_tSeqI:
  assumes "terminates_with_pred_time_IMP_Tailcall p p1 s s' (linear_in c1 n1 x)"
  and "terminates_with_res_pred_time_IMP_Tailcall p p2 s' r val (linear_in c2 n2 x)"
  and "c1 + c2 \<le> c"
  and "n1 + n2 \<le> n"
  shows "terminates_with_res_pred_time_IMP_Tailcall p (tSeq p1 p2) s r val (linear_in c n x)"
  using assms
  apply (elim terminates_with_pred_time_IMP_TailcallE terminates_with_res_pred_time_IMP_TailcallE)
  apply (intro terminates_with_res_pred_time_IMP_TailcallI terminates_with_pred_time_IMP_TailcallI tSeq)
  apply (assumption | rule refl)+
  by (auto intro: linear_in_add_tSeqI)

lemma terminates_with_res_linear_in_tAssignI:
  assumes "s' = s(k := aval aexp s)"
  and "s' r = val"
  and "2 \<le> c"
  shows "terminates_with_res_pred_time_IMP_Tailcall p (tAssign k aexp) s r val (linear_in c n x)"
  using assms unfolding linear_in_def scale_linear_def
  apply (intro terminates_with_res_pred_time_IMP_TailcallI terminates_with_pred_time_IMP_TailcallI)
  apply (rule tAssign)
  by auto

lemma linear_in_tIfTrueI:
  assumes "linear_in c1 n1 x y"
  and "max c1 c2 + d \<le> c"
  and "max n1 n2 \<le> n"
  shows "linear_in (c :: nat) n x (y + d)"
  apply (rule linear_inI, unfold scale_linear_eq_add_mul)
  apply (rule le_trans[of _ "max c1 c2 + d + (max n1 n2) * x"])
  using assms nat_mult_max_left by (auto simp: add_le_mono)

lemma linear_in_tIfFalseI:
  assumes "linear_in c2 n2 x y"
  and "max c1 c2 + d \<le> c"
  and "max n1 n2 \<le> n"
  shows "linear_in (c :: nat) n x (y + d)"
  apply (rule linear_inI, unfold scale_linear_eq_add_mul)
  apply (rule le_trans[of _ "max c1 c2 + d + (max n1 n2) * x"])
  using assms nat_mult_max_left by (auto simp: add_le_mono)

lemma terminates_with_res_linear_in_tIfI:
  assumes "s vb \<noteq> 0 \<Longrightarrow> terminates_with_res_pred_time_IMP_Tailcall p p1 s r val (linear_in c1 n1 x)"
  and "s vb = 0 \<Longrightarrow> terminates_with_res_pred_time_IMP_Tailcall p p2 s r val (linear_in c2 n2 x)"
  and "max c1 c2 + 1 \<le> c"
  and "max n1 n2 \<le> n"
  shows "terminates_with_res_pred_time_IMP_Tailcall p (tIf vb p1 p2) s r val (linear_in c n x)"
proof (cases "s vb = 0")
  case True
  with assms have "terminates_with_res_pred_time_IMP_Tailcall p p2 s r val (linear_in c2 n2 x)" by auto
  with True show ?thesis
    apply (elim terminates_with_pred_time_IMP_TailcallE terminates_with_res_pred_time_IMP_TailcallE)
    apply (intro terminates_with_res_pred_time_IMP_TailcallI terminates_with_pred_time_IMP_TailcallI
      tIfFalse)
    defer
    by (assumption | rule refl)+ (auto intro: linear_in_tIfFalseI assms simp del: Nat.One_nat_def)
  next
    case False
    with assms have "terminates_with_res_pred_time_IMP_Tailcall p p1 s r val (linear_in c1 n1 x)" by auto
    with False show ?thesis
      apply (elim terminates_with_pred_time_IMP_TailcallE terminates_with_res_pred_time_IMP_TailcallE)
      apply (intro terminates_with_res_pred_time_IMP_TailcallI terminates_with_pred_time_IMP_TailcallI
        tIfTrue)
      defer
      by (assumption | rule refl)+ (auto intro: linear_in_tIfTrueI assms simp del: Nat.One_nat_def)
qed

lemma terminates_with_res_linear_in_tTailI:
  assumes "terminates_with_res_pred_time_IMP_Tailcall p p s r val (linear_in c n x)"
  shows "terminates_with_res_pred_time_IMP_Tailcall p tTAIL s r val (linear_in c n x)"
  oops (*TODO: need to find a cleverer way*)

end

end