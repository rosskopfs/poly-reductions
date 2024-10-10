\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Arithmetics
  imports
    HOL_To_IMP_Minus_Primitives
    "HOL-Library.Discrete"
begin

paragraph \<open>Squaring\<close>

context HOL_To_HOL_Nat
begin

definition square_nat :: "nat \<Rightarrow> nat" where
  "square_nat x \<equiv> mul_nat x x"

lemma square_nat_eq_square [simp]: "square_nat x = x\<^sup>2"
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

lemma square_sqrt_nat_le: "(sqrt_nat x)\<^sup>2 \<le> x"
  using square_sqrt_aux_nat_le unfolding sqrt_nat_def by (simp add: power2_eq_square)

lemma lt_square_Suc_sqrt_nat: "x < (Suc (sqrt_nat x))\<^sup>2"
  using lt_square_Suc_sqrt_aux_nat unfolding sqrt_nat_def by (simp add: power2_eq_square)

corollary sqrt_nat_eq_sqrt [simp]: "sqrt_nat y = Discrete.sqrt y"
  using square_sqrt_nat_le lt_square_Suc_sqrt_nat
  by (intro sqrt_unique[symmetric]) auto

end

context HOL_Nat_To_IMP_Minus
begin

compile_nat HTHN.square_nat_def basename square
HOL_To_IMP_Minus_correct HTHN.square_nat by cook

compile_nat HTHN.sqrt_aux_nat.simps basename sqrt_aux

HOL_To_IMP_Minus_correct HTHN.sqrt_aux_nat by (cook mode = tailcall)
  (*Example step-by-step tactic invocation. Do not remove for debugging purposes*)
  (* apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  apply (tactic \<open>HT.setup_induction_tac HT.get_fun_inducts @{context} 1\<close>)
  apply (tactic \<open>HT.start_case_tac HT.get_IMP_def @{context} 1\<close>)
  apply (tactic \<open>HT.run_tac HT.get_imp_minus_correct @{context} 1\<close>)
  apply (tactic \<open>HT.finish_tac HB.get_HOL_eqs @{context} 1\<close>)
  apply (tactic \<open>HT.finish_tac HB.get_HOL_eqs @{context} 1\<close>)
  apply (tactic \<open>HT.finish_tac HB.get_HOL_eqs @{context} 1\<close>)
  oops *)

compile_nat HTHN.sqrt_nat_def basename sqrt

declare_compiled_const Discrete.sqrt
  return_register "sqrt.ret"
  argument_registers "sqrt.args.x"
  compiled "tailcall_to_IMP_Minus sqrt_IMP_tailcall"

HOL_To_IMP_Minus_correct HTHN.sqrt_nat by cook

end

end
