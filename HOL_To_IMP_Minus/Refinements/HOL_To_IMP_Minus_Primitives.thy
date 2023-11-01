\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Primitives
  imports
    HOL_To_IMP_Tailcalls_Tactics
    HOL_To_IMP_Minus_Goal_Commands
begin
term tailcall_to_IMP_Minus
locale HOL_To_IMP_Minus =
  notes neq0_conv[iff del, symmetric, iff]
begin

definition "is_true_nat n \<equiv> n \<noteq> 0"

lemma is_true_nat_eq[simp]: "is_true_nat = (\<noteq>) 0"
  unfolding is_true_nat_def by simp

definition "is_false_nat n \<equiv> n = 0"

lemma is_false_nat_iff[iff]: "is_false_nat n \<longleftrightarrow> \<not>(is_true_nat n)"
  unfolding is_false_nat_def by simp

definition "true_nat \<equiv> (1 :: nat)"

compile_nat true_nat_def basename true

declare_compiled_const True
  return_register "true_ret"
  argument_registers
  compiled "tailcall_to_IMP_Minus true_IMP_tailcall"

method preprocess_HOL_To_IMP_Minus_func_correct =
  (erule tailcall_to_IMP_Minus_correct_if_correct),
  (subst compiled_const_defs, simp),
  (subst compiled_const_defs, simp)

HOL_To_IMP_Minus_func_correct true_nat
  apply preprocess_HOL_To_IMP_Minus_func_correct
  apply (tactic \<open>H.start_run_finish_no_pattern_fun_tac @{thms compiled_const_defs} @{thms IMP_Minus_func_correct}
    @{thms true_nat_def} @{context} 1\<close>)
  done

lemma true_nat_eq_one[simp]: "true_nat = 1"
  unfolding true_nat_def by simp

lemma is_true_nat_true_nat[iff]: "is_true_nat true_nat"
  by simp

definition "false_nat \<equiv> (0 :: nat)"

compile_nat false_nat_def basename false

declare_compiled_const False
  return_register "false_ret"
  argument_registers
  compiled "tailcall_to_IMP_Minus false_IMP_tailcall"

HOL_To_IMP_Minus_func_correct false_nat
  apply preprocess_HOL_To_IMP_Minus_func_correct
  apply (tactic \<open>H.start_run_finish_no_pattern_fun_tac @{thms compiled_const_defs} @{thms IMP_Minus_func_correct}
    @{thms false_nat_def} @{context} 1\<close>)
  done

lemma false_nat_eq_one[simp]: "false_nat = 0"
  unfolding false_nat_def by simp

lemma is_false_nat_false_nat[iff]: "is_false_nat false_nat"
  unfolding false_nat_def by simp

definition "id_nat x \<equiv> (x :: nat)"

compile_nat id_nat_def basename id

HOL_To_IMP_Minus_func_correct id_nat
  apply preprocess_HOL_To_IMP_Minus_func_correct
  apply (tactic \<open>H.start_run_finish_no_pattern_fun_tac @{thms compiled_const_defs} @{thms IMP_Minus_func_correct}
    @{thms id_nat_def} @{context} 1\<close>)
  done

lemma id_nat_eq_id[simp]: "id_nat = id"
  unfolding id_nat_def by (rule ext) simp

definition "nat_of_bool b \<equiv> if b then true_nat else false_nat"

declare_compiled_const nat_of_bool
  return_register "id_ret"
  argument_registers "id_x"
  compiled "tailcall_to_IMP_Minus id_IMP_tailcall"

lemma nat_of_bool_eq_zero_iff[iff]: "nat_of_bool b = 0 \<longleftrightarrow> \<not>b"
  unfolding nat_of_bool_def by simp

lemma nat_of_bool_neq_zero_iff[iff]: "nat_of_bool b \<noteq> 0 \<longleftrightarrow> b"
  unfolding nat_of_bool_def by simp

definition "eq_nat (n :: nat) m \<equiv> nat_of_bool (n = m)"

context includes com_syntax no_com'_syntax
begin

definition [compiled_const_defs add]:
  "eq_IMP \<equiv>
    ''eq_x_Sub_y'' ::= (V ''eq_x'' \<ominus> V ''eq_y'');;
    ''eq_y_Sub_x'' ::= (V ''eq_y'' \<ominus> V ''eq_x'');;
    ''eq_neq'' ::= (V ''eq_x_Sub_y'' \<oplus> V ''eq_y_Sub_x'');;
    IF ''eq_neq'' \<noteq>0
    THEN ''eq_ret'' ::= A (N false_nat)
    ELSE ''eq_ret'' ::= A (N true_nat)"

end

declare_compiled_const eq_nat
  return_register "eq_ret"
  argument_registers "eq_x" "eq_y"
  compiled eq_IMP

declare_compiled_const HOL.eq
  return_register "eq_ret"
  argument_registers "eq_x" "eq_y"
  compiled eq_IMP

HOL_To_IMP_Minus_func_correct eq_nat
  unfolding eq_IMP_def eq_nat_def nat_of_bool_def by auto

lemma eq_nat_eq_nat_of_bool_eq[simp]: "eq_nat n m = nat_of_bool (n = m)"
  unfolding eq_nat_def by simp

definition "not_nat (n :: nat) \<equiv> nat_of_bool (n = false_nat)"

compile_nat not_nat_def basename not

declare_compiled_const HOL.Not
  return_register "not_ret"
  argument_registers "not_n"
  compiled "tailcall_to_IMP_Minus not_IMP_tailcall"

HOL_To_IMP_Minus_func_correct not_nat
  apply preprocess_HOL_To_IMP_Minus_func_correct
  apply (tactic \<open>H.start_run_finish_no_pattern_fun_tac @{thms compiled_const_defs} @{thms IMP_Minus_func_correct}
    @{thms not_nat_def} @{context} 1\<close>)
  done

lemma not_nat_eq_nat_of_bool_eq_false[simp]: "not_nat n = nat_of_bool (n = false_nat)"
  unfolding not_nat_def by simp

definition max_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "max_nat x y \<equiv> if x - y \<noteq> 0 then x else y"

compile_nat max_nat_def basename max

declare_compiled_const max
  return_register "max_ret"
  argument_registers "max_x" "max_y"
  compiled "tailcall_to_IMP_Minus max_IMP_tailcall"

HOL_To_IMP_Minus_func_correct max_nat
  apply preprocess_HOL_To_IMP_Minus_func_correct
  apply (tactic \<open>H.start_run_finish_no_pattern_fun_tac @{thms compiled_const_defs} @{thms IMP_Minus_func_correct}
    @{thms max_nat_def} @{context} 1\<close>)
  done

lemma max_nat_eq[simp]: "max_nat x y = max x y"
  unfolding max_nat_def by simp

definition min_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "min_nat x y \<equiv> if x - y \<noteq> 0 then y else x"

compile_nat min_nat_def basename min

declare_compiled_const min
  return_register "min_ret"
  argument_registers "min_x" "min_y"
  compiled "tailcall_to_IMP_Minus min_IMP_tailcall"

HOL_To_IMP_Minus_func_correct min_nat
  apply preprocess_HOL_To_IMP_Minus_func_correct
  apply (tactic \<open>H.start_run_finish_no_pattern_fun_tac @{thms compiled_const_defs} @{thms IMP_Minus_func_correct}
    @{thms min_nat_def} @{context} 1\<close>)
  done

lemma min_nat_eq[simp]: "min_nat x y = min x y"
  unfolding min_nat_def by simp

definition "and_nat (x :: nat) y \<equiv> min (min x y) true_nat"

compile_nat and_nat_def basename "and"

declare_compiled_const conj
  return_register "and_ret"
  argument_registers "and_x" "and_y"
  compiled "tailcall_to_IMP_Minus and_IMP_tailcall"

HOL_To_IMP_Minus_func_correct and_nat
  apply preprocess_HOL_To_IMP_Minus_func_correct
  apply (tactic \<open>H.start_run_finish_no_pattern_fun_tac @{thms compiled_const_defs} @{thms IMP_Minus_func_correct}
    @{thms and_nat_def} @{context} 1\<close>)
  done

lemma and_nat_eq[simp]: "and_nat x y = nat_of_bool (is_true_nat x \<and> is_true_nat y)"
  unfolding and_nat_def nat_of_bool_def by auto

definition "or_nat (x :: nat) y \<equiv> min (max x y) true_nat"

compile_nat or_nat_def basename "or"

declare_compiled_const disj
  return_register "or_ret"
  argument_registers "or_x" "or_y"
  compiled "tailcall_to_IMP_Minus or_IMP_tailcall"

HOL_To_IMP_Minus_func_correct or_nat
  apply preprocess_HOL_To_IMP_Minus_func_correct
  apply (tactic \<open>H.start_run_finish_no_pattern_fun_tac @{thms compiled_const_defs} @{thms IMP_Minus_func_correct}
    @{thms or_nat_def} @{context} 1\<close>)
  done

lemma or_nat_eq[simp]: "or_nat x y = nat_of_bool (is_true_nat x \<or> is_true_nat y)"
  unfolding or_nat_def nat_of_bool_def by auto

definition "le_nat (x :: nat) y \<equiv> nat_of_bool (x - y = 0)"

compile_nat le_nat_def basename le

declare_compiled_const "ord_class.less_eq"
  return_register "le_ret"
  argument_registers "le_x" "le_y"
  compiled "tailcall_to_IMP_Minus le_IMP_tailcall"

HOL_To_IMP_Minus_func_correct le_nat
  apply preprocess_HOL_To_IMP_Minus_func_correct
  apply (tactic \<open>H.start_run_finish_no_pattern_fun_tac @{thms compiled_const_defs} @{thms IMP_Minus_func_correct}
    @{thms le_nat_def} @{context} 1\<close>)
  done

lemma le_nat_eq[simp]: "le_nat x y = nat_of_bool (x \<le> y)"
  unfolding le_nat_def by simp

definition "lt_nat (x :: nat) y \<equiv> nat_of_bool (x \<le> y \<and> x \<noteq> y)"

compile_nat lt_nat_def basename lt

declare_compiled_const "ord_class.less"
  return_register "lt_ret"
  argument_registers "lt_x" "lt_y"
  compiled "tailcall_to_IMP_Minus lt_IMP_tailcall"

HOL_To_IMP_Minus_func_correct lt_nat
  apply preprocess_HOL_To_IMP_Minus_func_correct
  apply (tactic \<open>H.start_run_finish_no_pattern_fun_tac @{thms compiled_const_defs} @{thms IMP_Minus_func_correct}
    @{thms lt_nat_def} @{context} 1\<close>)
  done

lemma lt_nat_eq[simp]: "lt_nat x y = nat_of_bool (x < y)"
  unfolding lt_nat_def nat_of_bool_def by auto

end

end
