\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Arithmetics
  imports
    HOL_To_IMP_Minus_Fun_Pattern_Setup
    "HOL-Library.Discrete"
begin

context HOL_To_IMP_Minus
begin

definition [compiled_IMP_Minus_const_def]:
  "suc_IMP \<equiv> Com.Assign ''suc.ret'' (V ''suc.args.x'' \<oplus> N 1)"

declare_compiled_const Suc
  return_register "suc.ret"
  argument_registers "suc.args.x"
  compiled suc_IMP

HOL_To_IMP_Minus_func_correct Suc
  unfolding suc_IMP_def by auto

fun mul_acc_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"mul_acc_nat 0 _ z = z" |
"mul_acc_nat (Suc x) y z = mul_acc_nat x y (y + z)"
declare mul_acc_nat.simps[simp del]

case_of_simps mul_acc_nat_eq[simplified Nitpick.case_nat_unfold] : mul_acc_nat.simps
compile_nat mul_acc_nat_eq basename mul_acc

HOL_To_IMP_Minus_func_correct mul_acc_nat by (cook mode = tailcall)

lemma mul_acc_nat_eq_mul_add[simp]: "mul_acc_nat x y z = x * y + z"
  by (induction x y z arbitrary: z rule: mul_acc_nat.induct)
  (auto simp: mul_acc_nat.simps mult_eq_if)

definition mul_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mul_nat x y = mul_acc_nat x y 0"

compile_nat mul_nat_def basename mul

declare_compiled_const "times"
  return_register "mul.ret"
  argument_registers "mul.args.x" "mul.args.y"
  compiled "tailcall_to_IMP_Minus mul_IMP_tailcall"

HOL_To_IMP_Minus_func_correct mul_nat by cook


lemma
  "(tailcall_to_IMP_Minus mul_IMP_tailcall, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<Longrightarrow>
    s' ''mul.ret'' = mul_nat (s ''mul.args.x'') (s ''mul.args.y'')"
  apply (tactic \<open>HA.preprocess_tac H.get_IMP_def @{context} 1\<close>)
  apply (subst (asm) (2) mul_IMP_tailcall_def)
  apply (erule tSeq_E)
  oops

lemma terminates_compile_sound:
  assumes "invar c"
  and "\<exists>t s'. c \<turnstile> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "\<exists>t s'.(compile c,s) \<Rightarrow>'\<^bsup>t\<^esup> s'"
  using assms compile_sound by blast

theorem terminates_inline_sound:
  assumes "\<exists>t s'. (c, s) \<Rightarrow>'\<^bsup>t\<^esup> s'"
  shows "terminates (inline c, s)"
  using assms inline_sound by blast

corollary terminates_tailcall_to_IMP_Minus_sound:
  assumes "invar c"
  and "\<exists>t s'. c \<turnstile> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "terminates (tailcall_to_IMP_Minus c, s)"
  unfolding tailcall_to_IMP_Minus_eq
  using assms terminates_compile_sound terminates_inline_sound
  by blast

lemma terminates_tSeqI:
  assumes "\<exists>t s'. (c \<turnstile>(c1, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<and> (\<exists>t' s''. c \<turnstile>(c2, s') \<Rightarrow>\<^bsup>t'\<^esup> s''))"
  shows "\<exists>t s'. c \<turnstile>(tSeq c1 c2, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  using assms by blast

lemma terminates_mul_acc_IMP:
  "terminates (tailcall_to_IMP_Minus mul_acc_IMP_tailcall, s)"
  sorry

lemma terminatesE:
  assumes "terminates (c, s)"
  obtains t s' where "(c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  using assms by blast

lemma terminates_mul_IMP_tailcall:
  "terminates (tailcall_to_IMP_Minus mul_IMP_tailcall, s)"
  (* thm compile_sound[of mul_IMP_tailcall s] *)
  apply (rule terminates_tailcall_to_IMP_Minus_sound)
  apply (subst mul_IMP_tailcall_def)
  apply simp
  apply (subst (2) mul_IMP_tailcall_def)
  apply (rule terminates_tSeqI)
  apply (rule exI)
  apply (rule exI)
  apply (rule conjI)
  apply (rule tAssign)
  apply (rule terminates_tSeqI)
  apply (rule exI, rule exI, rule conjI)
  apply (rule tAssign)
  apply (rule terminates_tSeqI)
  apply (rule exI, rule exI, rule conjI)
  apply (rule tAssign)
  apply (rule terminates_tSeqI)
  apply (rule terminatesE[OF terminates_mul_acc_IMP])
  apply (rule exI, rule exI, rule conjI)
  apply (rule tCall)
  apply (rule terminatesE[OF terminates_mul_acc_IMP])
  apply assumption
  apply (tactic \<open>Tactic_Util.thin_tac 1 1\<close>)
  apply (rule exI, rule exI)
  apply (rule tAssign)
  done

lemma mul_nat_eq_mul[simp]: "mul_nat x y = x * y"
  unfolding mul_nat_def by simp

fun div_acc_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "div_acc_nat x y z = (if y = 0 then z else if x < y then z else div_acc_nat (x - y) y (z + 1))"
declare div_acc_nat.simps[simp del]

compile_nat div_acc_nat.simps basename div_acc

HOL_To_IMP_Minus_func_correct div_acc_nat by (cook mode = tailcall)

lemma terminates_eq_IMP:
  "terminates (eq_IMP, s)"
  sorry

lemma terminates_tIfI:
  assumes "s v \<noteq> 0 \<Longrightarrow> \<exists>t s'. c \<turnstile>(c1, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  and "s v = 0 \<Longrightarrow> \<exists>t s'. c \<turnstile>(c2, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "\<exists>t s'. c \<turnstile> (tIf v c1 c2, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  using assms by (cases "s ''v'' = 0") blast+

lemma terminates_tTailI:
  assumes "\<exists>t s'. c \<turnstile> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "\<exists>t s'. c \<turnstile> (tTAIL, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  using assms by blast+

lemma terminates_div_acc_nat_tailcall:
  "terminates (tailcall_to_IMP_Minus div_acc_IMP_tailcall, s)"
  (* thm compile_sound[of mul_IMP_tailcall s] *)
  apply (rule terminates_tailcall_to_IMP_Minus_sound)
  apply (subst div_acc_IMP_tailcall_def)
  apply simp
  (* apply (induction "s ''x''" "s ''y''" "s ''z''"
  arbitrary: s rule: div_acc_nat.induct) *)
  apply (subst (2) div_acc_IMP_tailcall_def)
  apply (rule terminates_tSeqI)
  apply (rule exI)
  apply (rule exI)
  apply (rule conjI)
  apply (rule tAssign)
  apply (rule terminates_tSeqI)
  apply (rule exI, rule exI, rule conjI)
  apply (rule tAssign)
  apply (rule terminates_tSeqI)
  apply (rule terminatesE[OF terminates_eq_IMP])
  apply (frule eq_nat_IMP_Minus_func_correct)
  apply (rule exI, rule exI, rule conjI)
  apply (rule tCall)
  apply assumption
  apply (simp only: eq_nat_def)
  apply (tactic \<open>Tactic_Util.thin_tac 1 1\<close>)
  apply (rule terminates_tSeqI)
  apply (rule exI, rule exI, rule conjI)
  apply (rule tAssign)
  apply (rule terminates_tIfI)
  apply (rule exI, rule exI)
  apply (rule tAssign)
  apply (rule terminates_tSeqI)
  apply (rule exI, rule exI, rule conjI)
  apply (rule tAssign)
  apply (rule terminates_tSeqI)
  apply (rule exI, rule exI, rule conjI)
  apply (rule tAssign)
  oops

lemma div_acc_nat_eq_div[simp]: "div_acc_nat x y z = x div y + z"
  by (induction x y z rule: div_acc_nat.induct) (auto simp: div_acc_nat.simps div_if)

definition div_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "div_nat x y = div_acc_nat x y 0"

compile_nat div_nat_def basename div

declare_compiled_const "divide"
  return_register "div.ret"
  argument_registers "div.args.x" "div.args.y"
  compiled "tailcall_to_IMP_Minus div_IMP_tailcall"

HOL_To_IMP_Minus_func_correct div_nat by cook

lemma div_nat_eq_div[simp]: "div_nat x y = x div y"
  unfolding div_nat_def by simp

definition square_nat :: "nat \<Rightarrow> nat" where
  "square_nat x \<equiv> mul_nat x x"

compile_nat square_nat_def basename square

HOL_To_IMP_Minus_func_correct square_nat by cook

lemma square_nat_eq_square[simp]: "square_nat x = x\<^sup>2"
  unfolding square_nat_def by (simp add: power2_eq_square)

(*takes lower and upper bound for root*)
function sqrt_aux_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sqrt_aux_nat x L R = (if Suc L < R
    then
      let M = (L + R) div 2
      in
        if square_nat M \<le> x
        then sqrt_aux_nat x M R
        else sqrt_aux_nat x L M
    else L)"
  by auto
termination by (relation "Wellfounded.measure (\<lambda>(_, L, R). R - L)") auto
declare sqrt_aux_nat.simps[simp del]

compile_nat sqrt_aux_nat.simps basename sqrt_aux

HOL_To_IMP_Minus_func_correct sqrt_aux_nat by (cook mode = tailcall)
(*Example step-by-step tactic invocation. Do not remove for debugging purposes*)
(*
apply (tactic \<open>HA.preprocess_tac H.get_IMP_def @{context} 1\<close>)
apply (tactic \<open>HA.setup_induction_tac HA.get_HOL_inducts @{context} 1\<close>)
apply (tactic \<open>H.start_tac H.get_IMP_def @{context} 1\<close>)
apply (tactic \<open>H.run_tac H.get_func_corrects @{context} 1\<close>)
apply (tactic \<open>H.finish_tailcall_tac HOL_To_IMP_Tactics_Base.get_HOL_eqs @{context} 1\<close>)
apply (tactic \<open>H.finish_tailcall_tac HOL_To_IMP_Tactics_Base.get_HOL_eqs @{context} 1\<close>)
apply (tactic \<open>H.finish_non_tailcall_tac HOL_To_IMP_Tactics_Base.get_HOL_eqs @{context} 1\<close>)
done
*)

lemma square_sqrt_aux_nat_le:
  assumes "L\<^sup>2 \<le> x" "x < R\<^sup>2"
  shows "(sqrt_aux_nat x L R)\<^sup>2 \<le> x"
  using assms
  by (induction x L R rule: sqrt_aux_nat.induct)
  (auto simp: sqrt_aux_nat.simps Let_def)

lemma lt_square_Suc_sqrt_aux_nat:
  assumes "L\<^sup>2 \<le> x" "x < R\<^sup>2"
  shows "x < (Suc (sqrt_aux_nat x L R))\<^sup>2"
  using assms
  by (induction x L R rule: sqrt_aux_nat.induct)
  (use order_less_le_trans in \<open>force simp: sqrt_aux_nat.simps Let_def\<close>)

definition sqrt_nat :: "nat \<Rightarrow> nat" where
  "sqrt_nat x = sqrt_aux_nat x 0 (Suc x)"

compile_nat sqrt_nat_def basename sqrt

HOL_To_IMP_Minus_func_correct sqrt_nat by cook

lemma square_sqrt_nat_le: "(sqrt_nat x)\<^sup>2 \<le> x"
  using square_sqrt_aux_nat_le unfolding sqrt_nat_def by (simp add: power2_eq_square)

lemma lt_square_Suc_sqrt_nat: "x < (Suc (sqrt_nat x))\<^sup>2"
  using lt_square_Suc_sqrt_aux_nat unfolding sqrt_nat_def by (simp add: power2_eq_square)

corollary sqrt_nat_sqrt[simp]: "sqrt_nat y = Discrete.sqrt y"
  using square_sqrt_nat_le lt_square_Suc_sqrt_nat
  by (intro sqrt_unique[symmetric]) auto

end

end
