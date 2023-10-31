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

lemma suc_IMP_func_correct [func_correct]:
  assumes "(suc_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "s' ''suc_ret'' = Suc (s ''suc_x'')"
  using assms unfolding suc_IMP_def by auto

fun mul_acc_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"mul_acc_nat 0 _ z = z" |
"mul_acc_nat (Suc x) y z = mul_acc_nat x y (y + z)"
declare mul_acc_nat.simps[simp del]
                        
case_of_simps mul_acc_nat_eq[simplified Nitpick.case_nat_unfold] : mul_acc_nat.simps
compile_nat mul_acc_nat_eq basename mul_acc

lemma mul_acc_nat_IMP_func_correct[func_correct]:
  assumes "(tailcall_to_IMP_Minus mul_acc_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "s' ''mul_acc_ret'' = mul_acc_nat (s ''mul_acc_x1a'') (s ''mul_acc_x2a'') (s ''mul_acc_x3ba'')"
  using assms                                 
  apply (rule tailcall_to_IMP_Minus_correct_if_correct)
  apply (subst compiled_const_defs, simp)
  apply (subst compiled_const_defs, simp)
  subgoal for t s'
  apply (induction "(s ''mul_acc_x1a'')" "(s ''mul_acc_x2a'')" "(s ''mul_acc_x3ba'')" arbitrary: s t rule: mul_acc_nat.induct)
  apply (tactic \<open>H.start_run_finish_pattern_fun_tac @{thms compiled_const_defs} @{thms func_correct} 
    @{thms mul_acc_nat.simps} @{context} 1\<close>)+
  done
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
  compiled "tailcall_to_IMP_Minus mul_IMP"

lemma mul_nat_IMP_func_correct[func_correct]:
  assumes "(tailcall_to_IMP_Minus mul_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "s' ''mul_ret'' = mul_nat (s ''mul_x'') (s ''mul_y'')"
  using assms                                 
  apply (rule tailcall_to_IMP_Minus_correct_if_correct)
  apply (subst compiled_const_defs, simp)
  apply (subst compiled_const_defs, simp)
  apply (tactic \<open>H.start_run_finish_no_pattern_fun_tac @{thms compiled_const_defs} @{thms func_correct} 
    @{thms mul_nat_def} @{context} 1\<close>)
  done

lemma mul_nat_eq_mul[simp]: "mul_nat x y = x * y"
  unfolding mul_nat_def by simp

fun div_acc_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "div_acc_nat x y z = (if y = 0 then z else if x < y then z else div_acc_nat (x - y) y (z + 1))"
declare div_acc_nat.simps[simp del]

compile_nat div_acc_nat.simps basename div_acc

lemma div_acc_nat_IMP_func_correct[func_correct]:
  assumes "(tailcall_to_IMP_Minus div_acc_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "s' ''div_acc_ret'' = div_acc_nat (s ''div_acc_x'') (s ''div_acc_y'') (s ''div_acc_z'')"
  using assms                                 
  apply (rule tailcall_to_IMP_Minus_correct_if_correct)
  apply (subst compiled_const_defs, simp)
  apply (subst compiled_const_defs, simp)
  subgoal for t s'
  apply (induction "(s ''div_acc_x'')" "(s ''div_acc_y'')" "(s ''div_acc_z'')" arbitrary: s t rule: div_acc_nat.induct)
  apply (tactic \<open>H.start_run_finish_no_pattern_fun_tac @{thms compiled_const_defs} @{thms func_correct}
    @{thms div_acc_nat.simps} @{context} 1\<close>)
  done
  done

lemma div_acc_nat_eq_div[simp]: "div_acc_nat x y z = x div y + z"
  by (induction x y z rule: div_acc_nat.induct) (auto simp: div_acc_nat.simps div_if)

definition div_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "div_nat x y = div_acc_nat x y 0"

compile_nat div_nat_def basename div

declare_compiled_const "divide"
  return_register "div_ret"
  argument_registers "div_x" "div_y"
  compiled "tailcall_to_IMP_Minus div_IMP"

lemma div_nat_IMP_func_correct[func_correct]:
  assumes "(tailcall_to_IMP_Minus div_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "s' ''div_ret'' = div_nat (s ''div_x'') (s ''div_y'')"
  using assms                                 
  apply (rule tailcall_to_IMP_Minus_correct_if_correct)
  apply (subst compiled_const_defs, simp)
  apply (subst compiled_const_defs, simp)
  apply (tactic \<open>H.start_run_finish_no_pattern_fun_tac @{thms compiled_const_defs} @{thms func_correct}
    @{thms div_nat_def} @{context} 1\<close>)
  done

lemma div_nat_eq_div[simp]: "div_nat x y = x div y"
  unfolding div_nat_def by simp

definition square_nat :: "nat \<Rightarrow> nat" where
  "square_nat x \<equiv> mul_nat x x"
  
compile_nat square_nat_def basename square

lemma square_nat_IMP_func_correct[func_correct]:
  assumes "(tailcall_to_IMP_Minus square_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "s' ''square_ret'' = square_nat (s ''square_x'')"
  using assms                                 
  apply (rule tailcall_to_IMP_Minus_correct_if_correct)
  apply (subst compiled_const_defs, simp)
  apply (subst compiled_const_defs, simp)
  apply (tactic \<open>H.start_run_finish_no_pattern_fun_tac @{thms compiled_const_defs} @{thms func_correct} 
     @{thms square_nat_def} @{context} 1\<close>)
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

lemma sqrt_aux_IMP_func_correct[func_correct]:
  assumes "(tailcall_to_IMP_Minus sqrt_aux_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "s' ''sqrt_aux_ret'' = sqrt_aux_nat (s ''sqrt_aux_x'') (s ''sqrt_aux_L'') (s ''sqrt_aux_R'')"
  using assms                                 
  apply (rule tailcall_to_IMP_Minus_correct_if_correct)
  apply (subst compiled_const_defs, simp)
  apply (subst compiled_const_defs, simp)
  subgoal for t s'
  apply (induction "s ''sqrt_aux_x''" "s ''sqrt_aux_L''" "s ''sqrt_aux_R''" arbitrary: s t rule: sqrt_aux_nat.induct)
  apply (tactic \<open>H.start_run_finish_no_pattern_fun_tac @{thms compiled_const_defs} @{thms func_correct} 
     @{thms sqrt_aux_nat.simps} @{context} 1\<close>)
  done
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

lemma sqrt_IMP_func_correct[func_correct]:
  assumes "(tailcall_to_IMP_Minus sqrt_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "s' ''sqrt_ret'' = sqrt_nat (s ''sqrt_x'')"
  using assms                                 
  apply (rule tailcall_to_IMP_Minus_correct_if_correct)
  apply (subst compiled_const_defs, simp)
  apply (subst compiled_const_defs, simp)
  apply (tactic \<open>H.start_run_finish_no_pattern_fun_tac @{thms compiled_const_defs} @{thms func_correct} 
     @{thms sqrt_nat_def} @{context} 1\<close>)
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