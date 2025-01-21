\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Arithmetics
  imports
    HOL_To_IMP_Minus_Primitives
    "HOL-Library.Discrete_Functions"
begin

paragraph \<open>Power\<close>

context HOL_To_HOL_Nat
begin

fun power_acc_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"power_acc_nat x 0 acc = acc" |
"power_acc_nat x (Suc n) acc = power_acc_nat x n (x * acc)"
declare power_acc_nat.simps[simp del]

lemma power_acc_nat_eq_power_mul: "power_acc_nat x y z = x^y * z"
  by (induction x y z arbitrary: z rule: power_acc_nat.induct)
  (auto simp: power_acc_nat.simps)

lemma power_eq_power_acc_nat_one: "x^y = power_acc_nat x y 1"
  using power_acc_nat_eq_power_mul by simp

lemma Rel_nat_power [Rel_nat]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) power (power :: nat \<Rightarrow> _)"
  by (auto simp: Rel_nat_nat_eq_eq)

end

context HOL_Nat_To_IMP_Minus
begin

case_of_simps power_acc_nat_eq[simplified case_nat_eq_if] : HTHN.power_acc_nat.simps
compile_nat power_acc_nat_eq basename power_acc

HOL_To_IMP_Minus_correct HTHN.power_acc_nat by (cook mode = tailcall)

compile_nat HTHN.power_eq_power_acc_nat_one basename power
HOL_To_IMP_Minus_correct power by cook

end

context HOL_To_HOL_Nat
begin

(*takes lower and upper bound for root*)
function sqrt_aux_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sqrt_aux_nat x L R = (if Suc L < R
    then
      let M = (L + R) div 2
      in
        if M\<^sup>2 \<le> x
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

corollary sqrt_nat_eq: "sqrt_nat y = floor_sqrt y"
  using square_sqrt_nat_le lt_square_Suc_sqrt_nat
  by (intro floor_sqrt_unique[symmetric]) auto

corollary floor_sqrt_eq_sqrt_aux_nat: "floor_sqrt x = sqrt_aux_nat x 0 (Suc x)"
  using sqrt_nat_eq sqrt_nat_def by simp

lemma Rel_nat_floor_sqrt [Rel_nat]:
  "(Rel_nat ===> Rel_nat) floor_sqrt floor_sqrt"
  by (auto simp: Rel_nat_nat_eq_eq)

end

context HOL_Nat_To_IMP_Minus
begin

compile_nat HTHN.sqrt_aux_nat.simps basename sqrt_aux

(*FIXME: make work with cook method (but without adding SOLVED' to finish_tac)*)
HOL_To_IMP_Minus_correct HTHN.sqrt_aux_nat
(* by (cook mode = tailcall) *)
  (*Example step-by-step tactic invocation. Do not remove for debugging purposes*)
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  apply (tactic \<open>HT.setup_induction_tac HT.get_fun_inducts @{context} 1\<close>)
  apply (tactic \<open>HT.start_case_tac HT.get_IMP_def @{context} 1\<close>)
  apply (tactic \<open>HT.run_tac HT.get_imp_minus_correct @{context} 1\<close>)
  apply (tactic \<open>SOLVED' (HT.finish_tac HB.get_HOL_eqs @{context}) 1\<close>)
  apply (tactic \<open>SOLVED' (HT.finish_tac HB.get_HOL_eqs @{context}) 1\<close>)
  apply (tactic \<open>SOLVED' (HT.finish_tac HB.get_HOL_eqs @{context}) 1\<close>)
  done

compile_nat HTHN.sqrt_nat_def basename sqrt

declare_compiled_const floor_sqrt
  return_register "sqrt.ret"
  argument_registers "sqrt.args.x"
  compiled "tailcall_to_IMP_Minus sqrt_IMP_tailcall"

HOL_To_IMP_Minus_correct HTHN.sqrt_nat by cook

end

end
