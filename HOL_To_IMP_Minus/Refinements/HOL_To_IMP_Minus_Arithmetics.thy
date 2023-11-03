\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Arithmetics
  imports
    HOL_To_IMP_Minus_Fun_Pattern_Setup
    "HOL-Library.Discrete"
begin

context HOL_To_IMP_Minus
begin

definition [compiled_const_defs add]: "suc_IMP \<equiv> Com.Assign ''suc_ret'' (V ''suc_x'' \<oplus> N 1)"

declare_compiled_const Suc
  return_register "suc_ret"
  argument_registers "suc_x"
  compiled suc_IMP

HOL_To_IMP_Minus_func_correct Suc
  unfolding suc_IMP_def by auto

fun mul_acc_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"mul_acc_nat 0 _ z = z" |
"mul_acc_nat (Suc x) y z = mul_acc_nat x y (y + z)"
declare mul_acc_nat.simps[simp del]

case_of_simps mul_acc_nat_eq[simplified Nitpick.case_nat_unfold] : mul_acc_nat.simps
compile_nat mul_acc_nat_eq basename mul_acc

HOL_To_IMP_Minus_func_correct mul_acc_nat
  apply preprocess_HOL_To_IMP_Minus_func_correct
  apply(start_run_finish (induction, pattern) mul_acc_nat_eq)
  done

lemma mul_acc_nat_eq_mul_add[simp]: "mul_acc_nat x y z = x * y + z"
  by (induction x y z arbitrary: z rule: mul_acc_nat.induct)
  (auto simp: mul_acc_nat.simps mult_eq_if)

definition mul_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mul_nat x y = mul_acc_nat x y 0"

compile_nat mul_nat_def basename mul

declare_compiled_const "times"
  return_register "mul_ret"
  argument_registers "mul_x" "mul_y"
  compiled "tailcall_to_IMP_Minus mul_IMP_tailcall"

HOL_To_IMP_Minus_func_correct mul_nat
  apply preprocess_HOL_To_IMP_Minus_func_correct
  apply(start_run_finish mul_nat_def)
  done

lemma mul_nat_eq_mul[simp]: "mul_nat x y = x * y"
  unfolding mul_nat_def by simp

fun div_acc_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "div_acc_nat x y z = (if y = 0 then z else if x < y then z else div_acc_nat (x - y) y (z + 1))"
declare div_acc_nat.simps[simp del]

compile_nat div_acc_nat.simps basename div_acc

HOL_To_IMP_Minus_func_correct div_acc_nat
  apply preprocess_HOL_To_IMP_Minus_func_correct
  apply(start_run_finish (induction) div_acc_nat.simps)
  done

lemma div_acc_nat_eq_div[simp]: "div_acc_nat x y z = x div y + z"
  by (induction x y z rule: div_acc_nat.induct) (auto simp: div_acc_nat.simps div_if)

definition div_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "div_nat x y = div_acc_nat x y 0"

compile_nat div_nat_def basename div

declare_compiled_const "divide"
  return_register "div_ret"
  argument_registers "div_x" "div_y"
  compiled "tailcall_to_IMP_Minus div_IMP_tailcall"

HOL_To_IMP_Minus_func_correct div_nat
  apply preprocess_HOL_To_IMP_Minus_func_correct
  apply (start_run_finish div_nat_def)
  done

lemma div_nat_eq_div[simp]: "div_nat x y = x div y"
  unfolding div_nat_def by simp

definition square_nat :: "nat \<Rightarrow> nat" where
  "square_nat x \<equiv> mul_nat x x"

compile_nat square_nat_def basename square

HOL_To_IMP_Minus_func_correct square_nat
  apply preprocess_HOL_To_IMP_Minus_func_correct
  apply (start_run_finish square_nat_def)
  done

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

HOL_To_IMP_Minus_func_correct sqrt_aux_nat
  apply preprocess_HOL_To_IMP_Minus_func_correct
  apply(start_run_finish (induction) sqrt_aux_nat.simps)
  done

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

HOL_To_IMP_Minus_func_correct sqrt_nat
  apply preprocess_HOL_To_IMP_Minus_func_correct
  apply (start_run_finish sqrt_nat_def)
  done

lemma square_sqrt_nat_le: "(sqrt_nat x)\<^sup>2 \<le> x"
  using square_sqrt_aux_nat_le unfolding sqrt_nat_def by (simp add: power2_eq_square)

lemma lt_square_Suc_sqrt_nat: "x < (Suc (sqrt_nat x))\<^sup>2"
  using lt_square_Suc_sqrt_aux_nat unfolding sqrt_nat_def by (simp add: power2_eq_square)

corollary sqrt_nat_sqrt[simp]: "sqrt_nat y = Discrete.sqrt y"
  using square_sqrt_nat_le lt_square_Suc_sqrt_nat
  by (intro sqrt_unique[symmetric]) auto

end

end