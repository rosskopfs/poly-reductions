\<^marker>\<open>creator Florian Keßler\<close>

section "Binary Operations in IMP-"

theory Binary_Operations
  imports
    IMP_To_IMP_Minus_State_Translations
    "IMP.Com"
    "IMP-.IMP_Minus_Subprograms" 
begin

text \<open> We give programs in IMP- that work on states translated from IMP to IMP- and simulate
       the arithmetic expressions of IMP. They work by first loading the operands into some special
       operand registers, and then performing standard binary addition / subtraction. \<close>

type_synonym IMP_com = Com.com
type_synonym IMP_Minus_com = "IMP_Minus_Com.com"

unbundle no Com.com_syntax

fun com_list_to_seq:: "IMP_Minus_com list \<Rightarrow> IMP_Minus_com" where
"com_list_to_seq [] = SKIP" |
"com_list_to_seq (c # cs) = c ;; (com_list_to_seq cs)"

lemma t_small_step_fun_com_list_to_seq_terminates: "t1 + t2 < t
  \<Longrightarrow> t_small_step_fun t1 (com_list_to_seq as, s1) = (SKIP, s3)
  \<Longrightarrow> t_small_step_fun t2 (com_list_to_seq bs, s3) = (SKIP, s2)
  \<Longrightarrow> t_small_step_fun t (com_list_to_seq (as @ bs), s1) = (SKIP, s2)"
proof(induction as arbitrary: s1 t1 t)
  case Nil
  then show ?case using t_small_step_fun_increase_time
    by (metis Pair_inject append_self_conv2 com_list_to_seq.simps le_add2
        less_imp_le_nat t_small_step_fun_SKIP)
next
  case (Cons a as)
  then obtain ta sa where ta_def: "ta < t1 \<and> t_small_step_fun ta (a, s1) = (SKIP, sa)
    \<and> t_small_step_fun (t1 - (ta + 1)) (com_list_to_seq as, sa) = (SKIP, s3)"
    by (auto simp: seq_terminates_iff)
  hence "t_small_step_fun (t - (ta + 1)) (com_list_to_seq (as @ bs), sa) = (SKIP, s2)"
    apply -
    apply(rule Cons(1))
    using Cons by(auto)
  thus ?case using ta_def Cons seq_terminates_iff by fastforce
qed

thm_oracles t_small_step_fun_com_list_to_seq_terminates

declare seq_terminates_when'[intro]
lemma tsmall_seq [intro]: "
  t_small_step_fun t1 (c1, s1) = (SKIP, s2) \<Longrightarrow>
  t_small_step_fun t2 (c2, s2) = (SKIP, s3) \<Longrightarrow> 
t_small_step_fun (t1+t2+1) (c1;;c2, s1) = (SKIP, s3)"
  by (meson less_add_one seq_terminates_when')

lemma com_list_to_seq_of_length_one_terminates_iff:
  "t_small_step_fun t (com_list_to_seq [c], s1) = (SKIP, s2) \<longleftrightarrow>
  (t > 0 \<and> t_small_step_fun (t - 1) (c, s1) = (SKIP, s2))"
  apply(auto simp: seq_terminates_iff)
  using t_small_step_fun_increase_time apply (metis One_nat_def diff_Suc_1 le_add1 less_imp_Suc_add)
  using diff_Suc_less by blast

lemma com_list_to_seq_variables: "set (enumerate_variables (com_list_to_seq cs))
  = { v | v c. c \<in> set cs \<and> v \<in> set (enumerate_variables c)}"
  apply(induction cs)
  by(auto simp: set_enumerate_variables_seq)

text \<open>Computing enumerate_variables is too slow for the _anything_, this does it quickly:\<close>
fun lvarS :: "com \<Rightarrow> vname set" where
  "lvarS (Assign v _) = {v}" |
  "lvarS (c1;;c2) = lvarS c1 \<union> lvarS c2" |
  "lvarS (If v c1 c2) = {v} \<union> lvarS c1 \<union>lvarS c2" |
  "lvarS (While v c) = {v} \<union> lvarS c" |
  "lvarS _ = {}"

lemma larvs_set_enum: "lvarS c = set (enumerate_variables c)"
  apply (induction c) 
  apply simp_all
  using set_enumerate_variables_seq apply presburger
  using set_enumerate_variables_if apply auto[1]
  using set_enumerate_variables_while by auto

fun binary_assign_constant_bits:: "nat \<Rightarrow> vname \<Rightarrow> nat \<Rightarrow> IMP_Minus_com" where
"binary_assign_constant_bits 0 v x = SKIP" |
"binary_assign_constant_bits (Suc n) v x = (var_bit_to_var (v, n)) ::= nth_bit x n ;;
  binary_assign_constant_bits n v x"

lemma result_of_binary_assign_constant_bits: "t_small_step_fun (3 * n)
  (binary_assign_constant_bits n v x, s)
  = (SKIP, \<lambda>w. (case var_to_var_bit w of
      Some (w', m) \<Rightarrow> (if w' = v \<and> m < n then Some (nth_bit x m) else s w) |
      _ \<Rightarrow> s w))"
proof(induction n arbitrary: s)
  case (Suc n)
  thus ?case
    apply auto
    apply(rule seq_terminates_when[where ?t1.0=1 and ?t2.0="3*n" and
          ?s3.0="s(var_bit_to_var (v, n) \<mapsto> nth_bit x n)"])
    by(auto simp: fun_eq_iff var_to_var_bit_eq_Some_iff  split: option.splits)
qed (auto simp: fun_eq_iff split: option.splits)

lemma binary_assign_constant_bits_variables[simp]: 
  "set (enumerate_variables (binary_assign_constant_bits n v x)) = { var_bit_to_var (v, i) | i. i < n }"
  apply(induction n)
  by(auto simp: set_enumerate_variables_seq)

definition binary_assign_zero :: "nat \<Rightarrow> vname \<Rightarrow> nat \<Rightarrow> IMP_Minus_com" where
"binary_assign_zero n v x = (var_bit_to_var (v, n)) ::= zero_bit x n"

lemma result_of_binary_assign_zero: "t_small_step_fun 1
  (binary_assign_zero n v x, s) 
  = (SKIP, \<lambda>w. (case var_to_var_bit w of
      Some (w',m) \<Rightarrow> (if w' = v \<and> m = n then Some (zero_bit x m) else s w ) | _ \<Rightarrow> s w))"
  unfolding binary_assign_zero_def
  by (auto simp: numeral_eq_Suc var_to_var_bit_eq_Some_iff fun_eq_iff split: option.splits)

lemma binary_assign_zero_vars: "enumerate_variables (binary_assign_zero n v x) = [var_bit_to_var (v,n)]"
  unfolding binary_assign_zero_def by simp

definition "binary_assign_constant n v x = binary_assign_zero n v x;; binary_assign_constant_bits n v x"
declare [[names_short]]

lemma binary_assign_constant_ne_Skip[simp]: "binary_assign_constant n v x \<noteq> SKIP"
  unfolding binary_assign_constant_def by auto

lemma result_of_binary_assign_constant:
  "t_small_step_fun (3 * n + 2)
  (binary_assign_constant n v x, s)
  = (SKIP, \<lambda>w. (case var_to_var_bit w of
      Some (w', m) \<Rightarrow> (if w' = v \<and> m < n then Some (nth_bit x m) else if w' = v \<and> m = n then Some (zero_bit x m) else s w) |
      _ \<Rightarrow> s w))"
  unfolding binary_assign_constant_def
  apply (rule seq_terminates_when[of 1 "3*n"])
  apply simp
   apply (rule result_of_binary_assign_zero)
  apply (subst result_of_binary_assign_constant_bits[of n v x])
  by (auto simp add: fun_eq_iff split: option.splits if_splits)

lemma binary_assign_constant_variables[simp]: "set (enumerate_variables (binary_assign_constant n v x))
  = {var_bit_to_var (v, i) | i. i < n} \<union> { var_bit_to_var (v, n)}"
  apply (subst larvs_set_enum[symmetric]) 
  unfolding binary_assign_constant_def binary_assign_zero_def
  apply auto
   apply (auto simp add: larvs_set_enum)
  done

lemma result_of_binary_assign_constant_on_translated_state_aux:
  assumes "n > 0"
  shows "t_small_step_fun (3 * n+2) (binary_assign_constant n v x,
    IMP_State_To_IMP_Minus s n)
    = (SKIP, IMP_State_To_IMP_Minus (s(v := x)) n)"
  unfolding binary_assign_constant_def
  apply (rule seq_terminates_when[of 1 "3*n"])
  apply simp
   apply (rule result_of_binary_assign_zero)
  unfolding IMP_State_To_IMP_Minus_def
  using result_of_binary_assign_constant_bits[of n v x] 
  by (simp add: fun_eq_iff
  IMP_State_To_IMP_Minus_with_operands_a_b_def split: option.splits)

lemma result_of_binary_assign_constant_on_translated_state:
  assumes "n > 0"
  shows "t_small_step_fun (50 * (n + 2)) (binary_assign_constant n v x,
    IMP_State_To_IMP_Minus s n)
    = (SKIP, IMP_State_To_IMP_Minus (s(v := x)) n)"
  apply(rule t_small_step_fun_increase_time[where ?t="3*n+2"])
  apply simp
  apply(subst result_of_binary_assign_constant_on_translated_state_aux)
  using assms by auto

fun copy_var_to_operand:: "nat \<Rightarrow> char \<Rightarrow> vname \<Rightarrow> IMP_Minus_com" where
"copy_var_to_operand 0 op v = SKIP" |
"copy_var_to_operand (Suc i) op v =
   (IF var_bit_to_var (v, i) \<noteq>0 THEN
   (operand_bit_to_var (op, i)) ::= One
    ELSE
    (operand_bit_to_var (op, i)) ::= Zero) ;;
    copy_var_to_operand i op v"

lemma copy_var_to_operand_result:
  "t_small_step_fun (4 * n) (copy_var_to_operand n op v, s)
  = (SKIP, \<lambda>w. (case var_to_operand_bit w of
    Some (op', i) \<Rightarrow> (if op' = op \<and> i < n
  then (case s (var_bit_to_var (v, i)) of Some x \<Rightarrow> Some x | None \<Rightarrow> Some One)
  else s w) |
    _ \<Rightarrow> s w))"
proof(induction n arbitrary: s)
  case 0
  then show ?case by (auto simp: fun_eq_iff split: option.splits)
next
  case (Suc n)
  let ?s' = "s(operand_bit_to_var (op, n)
    \<mapsto> (case s (var_bit_to_var (v, n)) of Some x \<Rightarrow> x | None \<Rightarrow> One))"
  show ?case using Suc
    by(auto simp: fun_eq_iff var_to_operand_bit_eq_Some_iff numeral_3_eq_3 less_Suc_eq_le
      split!: option.splits if_splits
      intro!: seq_terminates_when[where ?t1.0=3 and ?t2.0="4 * n" and ?s3.0="?s'"])
qed

fun copy_const_to_operand:: "nat \<Rightarrow> char \<Rightarrow> nat \<Rightarrow> IMP_Minus_com" where
"copy_const_to_operand 0 op x = SKIP" |
"copy_const_to_operand (Suc i) op x =
   (operand_bit_to_var (op, i)) ::= (nth_bit x i) ;;
    copy_const_to_operand i op x "

lemma copy_const_to_operand_result:
  "t_small_step_fun (4 * n) (copy_const_to_operand n op x, s)
  = (SKIP, \<lambda>w. (case var_to_operand_bit w of
    Some (op', i) \<Rightarrow> (if op' = op \<and> i < n then Some (nth_bit x i) else s w) |
    _ \<Rightarrow> s w))"
proof(induction n arbitrary: s)
  case 0
  then show ?case by (simp add: fun_eq_iff split: option.splits)
next
  case (Suc n)
  let ?s' = "s(operand_bit_to_var (op, n) \<mapsto> nth_bit x n)"
  show ?case using Suc
    apply(auto simp: fun_eq_iff var_to_operand_bit_eq_Some_iff split!: option.splits if_splits
      intro!: seq_terminates_when[where ?t1.0=1 and ?t2.0 ="4*n" and ?s3.0="?s'"])
  using less_antisym by blast
qed


definition copy_atom_to_operand:: "nat \<Rightarrow> char \<Rightarrow> AExp.atomExp \<Rightarrow> IMP_Minus_com" where
"copy_atom_to_operand n op a = (case a of
  AExp.N x \<Rightarrow> copy_const_to_operand n op x |
  AExp.V x \<Rightarrow> copy_var_to_operand n op x)"

lemma copy_atom_to_operand_a_result:
  "t_small_step_fun (4 * n) (copy_atom_to_operand n (a_chr) a,
   IMP_State_To_IMP_Minus_with_operands_a_b s n b c)
  = (SKIP,  IMP_State_To_IMP_Minus_with_operands_a_b s n (AExp.atomVal a s) c)"
  by(auto simp: copy_atom_to_operand_def fun_eq_iff copy_const_to_operand_result
      copy_var_to_operand_result IMP_State_To_IMP_Minus_with_operands_a_b_def
      var_to_operand_bit_eq_Some_iff
      split!: option.splits AExp.atomExp.splits char.splits bool.splits)

lemma copy_atom_to_operand_b_result:
  "t_small_step_fun (4 * n) (copy_atom_to_operand n (b_chr) a,
   IMP_State_To_IMP_Minus_with_operands_a_b s n b c)
  = (SKIP,  IMP_State_To_IMP_Minus_with_operands_a_b s n b (AExp.atomVal a s))"
  by(auto simp: copy_atom_to_operand_def fun_eq_iff copy_const_to_operand_result
      copy_var_to_operand_result IMP_State_To_IMP_Minus_with_operands_a_b_def
      var_to_operand_bit_eq_Some_iff
      split!: option.splits AExp.atomExp.splits char.splits bool.splits)

lemma copy_atom_to_operand_variables:
  "set (enumerate_variables (copy_atom_to_operand n op a))
    = { operand_bit_to_var (op, i) | i. i < n }
    \<union> { var_bit_to_var (v, i) | i v. i < n \<and> v \<in> set (vars a) }"
  apply (induction n)
  apply(cases a)
    apply (auto simp: copy_atom_to_operand_def enumerate_variables_def)[1]
   apply (auto simp: copy_atom_to_operand_def enumerate_variables_def)[1]
  apply(cases a)
   apply (auto simp: copy_atom_to_operand_def set_enumerate_variables_seq)
  by(auto simp: enumerate_variables_def var_bit_to_var_neq_operand_bit_to_var[symmetric])

definition assign_var_carry::
  "nat \<Rightarrow> vname \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> IMP_Minus_com" where
"assign_var_carry i v a b c z =
  (var_bit_to_var (v, i)) ::= (if a + b + c = 1 \<or> a + b + c = 3 then One else Zero) ;;
  carry ::= (if a + b + c \<ge> 2 then One else Zero) ;;
  zero ::= (if z = 0 \<and> (a + b + c = 0 \<or> a + b + c = 2) then Zero else One)"

lemma result_of_assign_var_carry:
  "t_small_step_fun 7 (assign_var_carry i v a b c z, s)
    = (SKIP, s(var_bit_to_var (v, i) \<mapsto> (if a + b + c = 1 \<or> a + b + c = 3 then One else Zero),
     carry \<mapsto> (if a + b + c \<ge> 2 then One else Zero),
      zero \<mapsto> (if z = 0 \<and> (a + b + c = 0 \<or> a + b + c = 2) then Zero else One)))"
  by(auto simp: assign_var_carry_def t_small_step_fun_terminate_iff)

definition full_adder:: "nat \<Rightarrow> vname \<Rightarrow> IMP_Minus_com" where
"full_adder i v  = (
let
  assign = assign_var_carry i v;
  op_a = operand_bit_to_var (a_chr, i);
  op_b = operand_bit_to_var (b_chr, i)
 in
  IF op_a\<noteq>0 THEN (
    IF op_b\<noteq>0 THEN (
      IF carry\<noteq>0 THEN (
        IF zero\<noteq>0 THEN assign 1 1 1 1
                      ELSE assign 1 1 1 0)
      ELSE (
        IF zero\<noteq>0 THEN assign 1 1 0 1
                      ELSE assign 1 1 0 0))
    ELSE (
      IF carry\<noteq>0 THEN (
        IF zero\<noteq>0 THEN assign 1 0 1 1
                      ELSE assign 1 0 1 0)
      ELSE (
        IF zero\<noteq>0 THEN assign 1 0 0 1
                       ELSE assign 1 0 0 0)))
  ELSE (
    IF op_b\<noteq>0 THEN (
      IF carry\<noteq>0 THEN (
        IF zero\<noteq>0 THEN assign 0 1 1 1
                      ELSE assign 0 1 1 0)
      ELSE (
        IF zero\<noteq>0 THEN assign 0 1 0 1
                      ELSE assign 0 1 0 0))
    ELSE (
      IF carry\<noteq>0 THEN (
        IF zero\<noteq>0 THEN assign 0 0 1 1
                      ELSE assign 0 0 1 0)
      ELSE (
        IF zero\<noteq>0 THEN assign 0 0 0 1
                      ELSE assign 0 0 0 0)))
)"

lemma full_adder_correct:
  assumes 
    "i = 0 \<longrightarrow> s carry = Some Zero \<and> s zero = Some Zero"
    "i > 0 \<longrightarrow> s carry = Some (nth_carry (i - 1) a b) \<and> s zero = Some (zero_bit (a+b) i)"
    "s (operand_bit_to_var (a_chr, i)) = Some (nth_bit a i)"
    "s (operand_bit_to_var (b_chr, i)) = Some (nth_bit b i)"
  shows "t_small_step_fun 11 (full_adder i v, s) = (SKIP,
    s(var_bit_to_var (v, i) \<mapsto> nth_bit (a + b) i, carry \<mapsto> nth_carry i a b, zero \<mapsto> zero_bit (a + b) (i + 1)))"
  using assms
  apply(simp add: full_adder_def Let_def t_small_step_fun_terminate_iff result_of_assign_var_carry)
  apply(cases i)
   apply (simp_all add: fun_eq_iff first_bit_of_add nth_bit_of_add zero_bit_rec)
  done



lemma full_adder_variables: "set (enumerate_variables (full_adder i v)) =
  { operand_bit_to_var (a_chr, i), operand_bit_to_var (b_chr, i), var_bit_to_var (v, i),
    carry, zero}"
  apply (subst larvs_set_enum[symmetric])
  unfolding full_adder_def by (auto simp: Let_def assign_var_carry_def)

lemma sequence_of_full_adders:
  assumes
    "s carry = Some Zero"
    "s zero = Some Zero"
    "\<forall>j < k. s (operand_bit_to_var (a_chr, j)) = Some (nth_bit a j)"
    "\<forall>j < k. s (operand_bit_to_var (b_chr, j)) = Some (nth_bit b j)"
  shows
   "t_small_step_fun (13 * k) (com_list_to_seq (map (\<lambda>i. full_adder i v) [0..< k]), s)
  = (SKIP, (\<lambda>w. (case var_to_var_bit w of
    Some (w', m) \<Rightarrow> (if w' = v \<and> m < k then Some (nth_bit (a + b) m) else s w) |
    _ \<Rightarrow> (if w = carry \<and> k > 0 then Some (nth_carry (k-1) a b)
          else if w = zero then Some (zero_bit (a+b) k)
          else s w))))"
  using assms
proof(induction k)
  case 0
  with assms(1,2) show ?case by (auto simp: fun_eq_iff split: option.splits)
next
  case (Suc k)
  let ?s = 
    "(\<lambda>w. case var_to_var_bit w of
      Some (w', m) \<Rightarrow> if w' = v \<and> m < k then Some (nth_bit (a + b) m) else s w
    | None \<Rightarrow> 
      if w = carry \<and> 0 < k then Some (nth_carry (k - 1) a b) else
      if w = zero then Some (zero_bit (a + b) k) 
      else s w)"

  from Suc.prems have
    "\<forall>j<k. s (operand_bit_to_var (a_chr, j)) = Some (nth_bit a j)"
    "\<forall>j<k. s (operand_bit_to_var (b_chr, j)) = Some (nth_bit b j)"
    by auto
  from Suc.IH[OF Suc.prems(1,2) this] 
  have 1: "t_small_step_fun (13 * k) (com_list_to_seq (map (\<lambda>i. full_adder i v) [0..<k]), s) = (SKIP, ?s)"
    by simp
  let ?s2 =
    "(\<lambda>w. case var_to_var_bit w of
      Some (w', m) \<Rightarrow> if w' = v \<and> m < Suc k then Some (nth_bit (a + b) m) else s w
    | None \<Rightarrow>
      if w = carry \<and> 0 < Suc k then Some (nth_carry (Suc k - 1) a b) else 
      if w = zero then Some (zero_bit (a + b) (Suc k))
      else s w)"

  have 2: "t_small_step_fun 11 ((full_adder k v), ?s) = (SKIP, ?s2)"
    apply (subst full_adder_correct)
    by (auto simp: Suc.prems fun_eq_iff var_to_var_bit_eq_Some_iff split!: if_splits option.splits)
  have "map (\<lambda>i. full_adder i v) [0..<Suc k] = (map (\<lambda>i. full_adder i v) [0..<k]) @ [full_adder k v]" by simp
  with 1 2 show ?case
    apply simp
    apply (rule t_small_step_fun_com_list_to_seq_terminates)
      apply auto
    done
qed

definition write_zero where
"write_zero n v = 
  IF zero\<noteq>0 THEN 
    (var_bit_to_var (v, n)) ::= One
   ELSE (var_bit_to_var (v, n)) ::= Zero;;
   carry ::= Zero ;;
   zero ::= Zero"

lemma result_write_zero: "t_small_step_fun 6
     (write_zero n v,
      \<lambda>w. case var_to_var_bit w of
          None \<Rightarrow>
            if w = carry \<and> 0 < n then Some cv else
            if w = zero then Some (zero_bit c n) else
            IMP_State_To_IMP_Minus_with_operands_a_b s n a b w
        | Some (w', m) \<Rightarrow> 
            if w' = v \<and> m < n then Some (nth_bit c m)
            else IMP_State_To_IMP_Minus_with_operands_a_b s n a b w) =
    (SKIP,
     \<lambda>w. case var_to_var_bit w of
          None \<Rightarrow>
            if w = carry then Some Zero else
            if w = zero then Some Zero else
            IMP_State_To_IMP_Minus_with_operands_a_b s n a b w
        | Some (w', m) \<Rightarrow>
            if w' = v \<and> m = n then Some (zero_bit ((s(v := c)) w') m) else 
            if w' = v \<and> m < n then Some (nth_bit c m)
            else IMP_State_To_IMP_Minus_with_operands_a_b s n a b w)"
  unfolding write_zero_def
  by (auto simp: numeral_eq_Suc simp: fun_eq_iff var_to_var_bit_eq_Some_iff split: if_splits option.splits)

lemma write_zero_vars[simp]: 
  "set (enumerate_variables (write_zero n v)) = {zero, carry, var_bit_to_var (v,n)}"
  unfolding write_zero_def
  apply (subst larvs_set_enum[symmetric])
  by auto

definition adder:: "nat \<Rightarrow> vname \<Rightarrow> IMP_Minus_com" where
"adder n v = 
  com_list_to_seq (map (\<lambda>i. full_adder i v) [0..< n]) ;; 
  write_zero n v
"

lemma result_of_adder:
  assumes "a + b < 2 ^ n"
  shows "t_small_step_fun (13 * n + 13) (adder n v,
    IMP_State_To_IMP_Minus_with_operands_a_b s n a b)
    = (SKIP, IMP_State_To_IMP_Minus_with_operands_a_b (s(v := a + b)) n a b)"
  using assms
  apply(simp only: adder_def)
  apply(rule seq_terminates_when[OF _  sequence_of_full_adders[where a=a and b=b],of _ 6])
  apply (auto simp: fun_eq_iff var_to_var_bit_eq_Some_iff IMP_State_To_IMP_Minus_with_operands_a_b_def
      split!: option.splits if_splits)
  apply (subst result_write_zero)
  apply (auto simp: IMP_State_To_IMP_Minus_with_operands_a_b_def split: if_splits option.splits)
  done

definition binary_adder:: "nat \<Rightarrow> vname \<Rightarrow> AExp.atomExp \<Rightarrow> AExp.atomExp \<Rightarrow> IMP_Minus_com" where
"binary_adder n v a b =
  copy_atom_to_operand n (a_chr) a ;;
  (copy_atom_to_operand n (b_chr) b ;;
  (adder n v ;;
  (copy_atom_to_operand n (a_chr) (AExp.N 0) ;;
  copy_atom_to_operand n (b_chr) (AExp.N 0))))"

lemma binary_adder_correct:
  assumes "n > 0"
    "AExp.atomVal a s + AExp.atomVal b s < 2 ^ n"
  shows "t_small_step_fun (50 * (n + 1)) (binary_adder n v a b,
    IMP_State_To_IMP_Minus s n)
    = (SKIP, IMP_State_To_IMP_Minus (s(v := AExp.atomVal a s + AExp.atomVal b s)) n)"
  using seq_terminates_when'[OF copy_atom_to_operand_a_result[where ?n=n]
      seq_terminates_when'[OF copy_atom_to_operand_b_result
      seq_terminates_when'[OF result_of_adder
      seq_terminates_when'[OF copy_atom_to_operand_a_result copy_atom_to_operand_b_result]]]]
  assms
  by(fastforce simp: binary_adder_def IMP_State_To_IMP_Minus_def)


section \<open>Subtraction\<close>

definition assign_var_carry_sub::
  "nat \<Rightarrow> vname \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> IMP_Minus_com" where
"assign_var_carry_sub i v a b c z =
  (var_bit_to_var (v, i)) ::= 
    (if b + c = 0 \<or> b + c = 2 then (if a = 1 then One else Zero)
     else (if b + c = 1 \<and> a = 0 then One else Zero)) ;;
  carry ::= (if a < b + c then One else Zero);;
  zero ::= (if z = 0 \<and> ((a + b + c = 0) \<or> (b + c = 2 \<and> a = 0) \<or> (b + c = 1 \<and> a = 1)) then Zero else One)"

lemma result_of_assign_var_carry_sub:
  "t_small_step_fun 7 (assign_var_carry_sub i v a b c z, s)
    = (SKIP, s(var_bit_to_var (v, i) \<mapsto> (if b + c = 0 \<or> b + c = 2 then (if a = 1 then One else Zero)
    else (if b + c = 1 \<and> a = 0 then One else Zero)),
     carry \<mapsto>  (if a < b + c then One else Zero), 
     zero \<mapsto> (if z = 0 \<and> ((a + b + c = 0) \<or> (b + c = 2 \<and> a = 0) \<or> (b + c = 1 \<and> a = 1)) then Zero else One)))"
  by(auto simp: assign_var_carry_sub_def t_small_step_fun_terminate_iff)

definition full_subtractor:: "nat \<Rightarrow> vname \<Rightarrow> IMP_Minus_com" where
"full_subtractor i v  = (
let
  assign = assign_var_carry_sub i v;
  op_a = operand_bit_to_var (a_chr, i);
  op_b = operand_bit_to_var (b_chr, i)
  in
  IF op_a\<noteq>0 THEN (
    IF op_b\<noteq>0 THEN (
      IF carry\<noteq>0 THEN (
        IF zero\<noteq>0 THEN assign 1 1 1 1
                      ELSE assign 1 1 1 0)
      ELSE (
        IF zero\<noteq>0 THEN assign 1 1 0 1
                      ELSE assign 1 1 0 0))
    ELSE (
      IF carry\<noteq>0 THEN (
        IF zero\<noteq>0 THEN assign 1 0 1 1
                      ELSE assign 1 0 1 0)
      ELSE (
        IF zero\<noteq>0 THEN assign 1 0 0 1
                       ELSE assign 1 0 0 0)))
  ELSE (
    IF op_b\<noteq>0 THEN (
      IF carry\<noteq>0 THEN (
        IF zero\<noteq>0 THEN assign 0 1 1 1
                      ELSE assign 0 1 1 0)
      ELSE (
        IF zero\<noteq>0 THEN assign 0 1 0 1
                      ELSE assign 0 1 0 0))
    ELSE (
      IF carry\<noteq>0 THEN (
        IF zero\<noteq>0 THEN assign 0 0 1 1
                      ELSE assign 0 0 1 0)
      ELSE (
        IF zero\<noteq>0 THEN assign 0 0 0 1
                      ELSE assign 0 0 0 0)))
)"

lemma full_subtractor_correct_no_underflow:
  assumes "a \<ge> b"
    "i = 0 \<longrightarrow> s carry = Some Zero \<and> s zero = Some Zero"
    "i > 0 \<longrightarrow> s carry = Some (nth_carry_sub (i - 1) a b) \<and> s zero = Some (zero_bit (a-b) i)"
    "s (operand_bit_to_var (a_chr, i)) = Some (nth_bit a i)"
    "s (operand_bit_to_var (b_chr, i)) = Some (nth_bit b i)"
  shows "t_small_step_fun 11 (full_subtractor i v, s) = (SKIP,
    s(var_bit_to_var (v, i) \<mapsto> nth_bit (a - b) i, carry \<mapsto> nth_carry_sub i a b, zero \<mapsto> zero_bit (a - b) (i + 1)))"
  using assms
  apply(simp add: full_subtractor_def Let_def t_small_step_fun_terminate_iff result_of_assign_var_carry_sub)
  apply(cases i)
  apply (simp_all add: fun_eq_iff first_bit_of_sub_n_no_underflow nth_bit_of_sub_n_no_underflow Let_def zero_bit_rec)
  done

lemma full_subtractor_variables: "set (enumerate_variables (full_subtractor i v)) =
  { operand_bit_to_var (a_chr, i), operand_bit_to_var (b_chr, i), var_bit_to_var (v, i),
    carry, zero}"
  apply (subst larvs_set_enum[symmetric])
  unfolding full_subtractor_def Let_def
  by (auto simp: assign_var_carry_sub_def)

lemma sequence_of_full_subtractors_no_underflow:
  assumes "a \<ge> b"
    "s carry = Some Zero"
    "s zero = Some Zero"
    "\<forall>j < n. s (operand_bit_to_var (a_chr, j)) = Some (nth_bit a j)"
    "\<forall>j < n. s (operand_bit_to_var (b_chr, j)) = Some (nth_bit b j)"
  shows
   "t_small_step_fun (13 * n) (com_list_to_seq (map (\<lambda>i. full_subtractor i v) [0..< n]), s)
  = (SKIP, (\<lambda>w. (case var_to_var_bit w of
    Some (w', m) \<Rightarrow> (if w' = v \<and> m < n then Some (nth_bit (a - b) m) else s w) |
    _ \<Rightarrow> (if w = carry \<and> n > 0 then Some (nth_carry_sub (n - 1) a b)
          else if w = zero then Some (zero_bit (a-b) n)
          else s w))))"
  using assms
proof(induction n)
  case 0
  with assms(1,2) show ?case by (auto simp: fun_eq_iff split: option.splits)
next
  case (Suc n)
  have "t_small_step_fun (13 + 13 * n)
   (com_list_to_seq ((map (\<lambda>i. full_subtractor i v) [0..< n]) @ [full_subtractor n v]), s)
    = (SKIP, (\<lambda>w. (case var_to_var_bit w of
      Some (w', m) \<Rightarrow> (if w' = v \<and> m < Suc n then Some (nth_bit (a - b) m) else s w) |
      None \<Rightarrow> 
        (if w = carry \<and> Suc n > 0 then Some (nth_carry_sub n a b) else
         if w = zero then Some (zero_bit (a-b) (Suc n))
         else s w))))"
    apply(rule t_small_step_fun_com_list_to_seq_terminates[OF _ Suc.IH
          iffD2[OF com_list_to_seq_of_length_one_terminates_iff[where ?t="12"]]])
    using Suc  apply(auto)
    apply(subst full_subtractor_correct_no_underflow)
    using Suc
    by(auto simp add: fun_eq_iff var_to_var_bit_eq_Some_iff split!: option.splits)
  thus ?case by auto
qed

lemma sequence_of_full_subtractors_with_underflow:
  assumes "a < b"
    "a < 2^n" "b < 2^n"
    "s carry = Some Zero"
    "s zero = Some Zero"
    "\<forall>j < n. s (operand_bit_to_var (a_chr, j)) = Some (nth_bit a j)"
    "\<forall>j < n. s (operand_bit_to_var (b_chr, j)) = Some (nth_bit b j)"
  shows
   "t_small_step_fun (13 * n) (com_list_to_seq (map (\<lambda>i. full_subtractor i v) [0..< n]), s)
  = (SKIP, (\<lambda>w. (case var_to_var_bit w of
    Some (w', m) \<Rightarrow> (if w' = v \<and> m < n then Some (nth_bit (2^n + a - b) m) else s w) |
    _ \<Rightarrow> (if w = carry \<and> n > 0 then Some One
          else if w = zero then Some (zero_bit (2^n + a - b) n)
          else s w))))"
proof -
  have "\<forall>j < n. s (operand_bit_to_var (a_chr, j)) = Some (nth_bit (2 ^ n + a) j)"
    using nth_bit_add_out_of_range[OF \<open>a < 2^n\<close>]
      \<open>\<forall>j < n. s (operand_bit_to_var (a_chr, j)) = Some (nth_bit a j)\<close> by simp
  moreover have "2 ^ n + a > b" using \<open>b < 2^n\<close> by simp
  ultimately have "t_small_step_fun (13 * n)
                       (com_list_to_seq (map (\<lambda>i. full_subtractor i v) [0..< n]), s)
  = (SKIP, (\<lambda>w. (case var_to_var_bit w of
    Some (w', m) \<Rightarrow> (if w' = v \<and> m < n then Some (nth_bit (2^n + a - b) m) else s w) |
    _ \<Rightarrow> (if w = carry \<and> n > 0 then Some (nth_carry_sub (n - 1) (2^n + a) b) else
          if w = zero then Some (zero_bit (2^n + a - b) n)
          else s w))))"
    using sequence_of_full_subtractors_no_underflow[where ?a="2^n + a" and ?b=b] assms
    by(auto simp: fun_eq_iff)
  thus ?thesis using assms nth_carry_sub_underflow by auto
qed

definition underflow_handler:: "nat \<Rightarrow> vname \<Rightarrow> IMP_Minus_com" where
"underflow_handler n v = (
IF carry\<noteq>0 THEN 
  ((carry ::= Zero ;;
   zero ::= Zero);;
  binary_assign_constant n v 0)
ELSE SKIP)"

(* proper setup... why was this not done before ?! *)

lemma seq_intro:
 "t_small_step_fun n1 (c1,s) = (SKIP,s2) \<Longrightarrow> 
  t_small_step_fun n2 (c2,s2) = (SKIP,s3) \<Longrightarrow>
  t = n1 + n2 + 1 \<Longrightarrow>  
  t_small_step_fun t (c1;;c2,s) = (SKIP,s3)"
  apply (auto simp add: t_small_step_fun_decomposition t_small_step_fun_small_step_fun tsmall_seq)
  by (metis IMP_Minus_Small_StepT.small_step_fun.simps(3)
      t_small_step_fun_decomposition t_small_step_fun_small_step_fun
      tsmall_seq)

lemma assign_intro:
"t_small_step_fun (Suc 0) (c ::= b,s) = (SKIP,s(c := Some b))"
  by simp

lemma ifTrue_intro:
"s b \<noteq> Some Zero \<Longrightarrow> t_small_step_fun n (c, s) = (SKIP,s2) \<Longrightarrow> n2 = Suc n \<Longrightarrow>
   t_small_step_fun n2 (IF b\<noteq>0 THEN c ELSE c2,s) = (SKIP, s2)"
  by simp

lemma ifFalse_intro:
"s b = Some Zero \<Longrightarrow> t_small_step_fun n (c2, s) = (SKIP,s2) \<Longrightarrow> n2 = Suc n \<Longrightarrow>
   t_small_step_fun n2 (IF b\<noteq>0 THEN c ELSE c2,s) = (SKIP, s2)"
  by simp


lemmas intros = seq_intro assign_intro 


lemma result_underflow_handler_carry: "s carry \<noteq> Some Zero \<Longrightarrow>
 t_small_step_fun (3 * n + 8)
     (underflow_handler n v, s) =
    (SKIP, (\<lambda>w. case var_to_var_bit w of
          None \<Rightarrow>
            if w = carry then Some Zero
            else if w = zero then Some Zero
            else s w
          | Some (w', m) \<Rightarrow>
              if w' = v \<and> m < n then Some (nth_bit 0 m)
              else if w' = v \<and> m = n then Some (zero_bit 0 m)
              else s w))"
  unfolding underflow_handler_def
  apply (auto  intro!:  intros ifTrue_intro)
  apply (subst t_small_step_fun_increase_time[OF _ result_of_binary_assign_constant])
   apply (auto split!: if_splits option.splits)
  done

lemma result_underflow_handler_carry_Skip: "s carry = Some Zero \<Longrightarrow>
  t_small_step_fun (3 * n + 8)
     (underflow_handler n v, s) =
    (SKIP, s)"
  unfolding underflow_handler_def
  by (auto intro!: intros ifFalse_intro)  

definition subtract_handle_underflow::
  "nat \<Rightarrow> vname \<Rightarrow> IMP_Minus_com" where
"subtract_handle_underflow n v =
  com_list_to_seq (map (\<lambda>i. full_subtractor i v) [0..<n]) ;;
  (underflow_handler n v;;
  write_zero n v)"

lemma "Zero = zero_bit 0 n"
  using zero_bit_one by fastforce

lemma result_of_subtract_handle_underflow:
  assumes "n > 0" "a < 2 ^ n" "b < 2 ^ n"
  shows "t_small_step_fun (16 * n + 16) (subtract_handle_underflow n v,
    IMP_State_To_IMP_Minus_with_operands_a_b s n a b)
    = (SKIP, IMP_State_To_IMP_Minus_with_operands_a_b (s(v := a - b)) n a b)"
proof(cases "a < b")
  case True
  with assms show ?thesis
    apply (simp only: subtract_handle_underflow_def)
    apply (rule seq_terminates_when[OF _  sequence_of_full_subtractors_with_underflow[where ?a=a and ?b=b], of _ "3*n + 15"]) 
            apply auto
    apply (rule seq_terminates_when[of "3*n + 8" "6"])
      apply auto
    apply (subst result_underflow_handler_carry)
     apply (auto)
    unfolding write_zero_def
    apply (auto  simp: numeral_eq_Suc simp: fun_eq_iff var_to_var_bit_eq_Some_iff IMP_State_To_IMP_Minus_with_operands_a_b_of_changed_s_neq_iff split: if_splits option.splits)
     defer using zero_bit_one apply fastforce
    using IMP_State_To_IMP_Minus_with_operands_a_b_of_changed_s_neq_iff
    by (metis not_Some_eq)
next
  case False
  with assms show ?thesis
    apply(simp only: subtract_handle_underflow_def)
    apply(rule seq_terminates_when[OF _  sequence_of_full_subtractors_no_underflow[where ?a=a and ?b=b],
          where ?t2.0="3 * n + 15"])
          apply auto
    apply (rule seq_terminates_when[of "3*n+8" 6])
    apply auto
     apply (subst result_underflow_handler_carry_Skip)
      apply auto
    unfolding write_zero_def
    apply (auto simp: numeral_eq_Suc simp: fun_eq_iff var_to_var_bit_eq_Some_iff IMP_State_To_IMP_Minus_with_operands_a_b_of_changed_s_neq_iff split: if_splits option.splits)
    apply (metis One_nat_def assms(2,3) nth_carry_sub_no_underflow
        verit_comp_simplify1(3))
     using nth_carry_sub_no_underflow[OF _ \<open>a < 2 ^ n\<close> \<open>b < 2 ^ n\<close>]
    apply(auto simp:  IMP_State_To_IMP_Minus_with_operands_a_b_of_changed_s_neq_iff
        var_to_var_bit_eq_Some_iff
        split!: option.splits if_splits)
     by(auto simp: IMP_State_To_IMP_Minus_with_operands_a_b_def)
qed

lemma subtract_handle_underflow_variables:
  "set (enumerate_variables (subtract_handle_underflow n v))
  = { operand_bit_to_var (op, i) | i op. i < n \<and> (op = a_chr \<or> op = b_chr) }
    \<union> { var_bit_to_var (v, i) | i. i < n }
    \<union> { carry, zero, var_bit_to_var (v, n) }"
  by(auto simp: subtract_handle_underflow_def
       set_enumerate_variables_seq com_list_to_seq_variables full_subtractor_variables
       set_enumerate_variables_if underflow_handler_def)

definition binary_subtractor:: "nat \<Rightarrow> vname \<Rightarrow> AExp.atomExp \<Rightarrow> AExp.atomExp \<Rightarrow> IMP_Minus_com" where
"binary_subtractor n v a b =
  copy_atom_to_operand n (a_chr) a ;;
  (copy_atom_to_operand n (b_chr) b ;;
  (subtract_handle_underflow n v ;;
  (copy_atom_to_operand n (a_chr) (AExp.N 0) ;;
  copy_atom_to_operand n (b_chr) (AExp.N 0))))"

lemma binary_subtractor_correct:
  assumes "n > 0"
    "AExp.atomVal a s < 2 ^ n" "AExp.atomVal b s < 2 ^ n"
  shows "t_small_step_fun (50 * (n + 1)) (binary_subtractor n v a b,
    IMP_State_To_IMP_Minus s n)
    = (SKIP, IMP_State_To_IMP_Minus (s(v := AExp.atomVal a s - AExp.atomVal b s)) n)"
  unfolding binary_subtractor_def
  using assms
  apply (auto simp: IMP_State_To_IMP_Minus_def  intro!: intros copy_atom_to_operand_a_result copy_atom_to_operand_b_result 
      result_of_subtract_handle_underflow )
  apply (subst t_small_step_fun_increase_time[OF _ copy_atom_to_operand_b_result])
   apply auto
  done

text \<open> The two copy_atom_to_operand which don't have any effect on the output are only a hack to
       ensure that all bits of all variables in IMP occur in IMP- \<close>

fun assign_shifted_bits:: "nat \<Rightarrow> vname \<Rightarrow> IMP_Minus_com" where
"assign_shifted_bits 0 v = SKIP" |
"assign_shifted_bits (Suc i) v = (IF operand_bit_to_var ((a_chr), Suc i)\<noteq>0 THEN
    (var_bit_to_var (v, i)) ::= One
  ELSE
    (var_bit_to_var (v, i)) ::= Zero) ;;
  assign_shifted_bits i v"

lemma result_of_assign_shifted_bits:
  "t_small_step_fun (3 * k) (assign_shifted_bits k v, s) = (SKIP, (\<lambda>w.
    (case var_to_var_bit w of Some(v', i) \<Rightarrow> (if v' = v \<and> i < k then
      (if s (operand_bit_to_var (a_chr, Suc i)) \<noteq> Some Zero then Some One else Some Zero)
      else s w) |
      _ \<Rightarrow> s w)))"
proof(induction k arbitrary: s)
  case (Suc k)
  have *: "t_small_step_fun 2 (IF operand_bit_to_var ((a_chr), Suc k)\<noteq>0 THEN
      (var_bit_to_var (v, k)) ::= One
   ELSE
      (var_bit_to_var (v, k)) ::= Zero, s) = (SKIP, s(var_bit_to_var (v, k) \<mapsto>
        (if s (operand_bit_to_var (a_chr, Suc k)) \<noteq> Some Zero then One else Zero)))"
    by(auto simp: numeral_2_eq_2)
  show ?case
    using seq_terminates_when[OF _ * Suc.IH, where ?t="3 + 3 * k"]
    apply (auto simp: fun_eq_iff var_to_var_bit_eq_Some_iff split: option.splits)
    using var_bit_to_var_neq_operand_bit_to_var by (metis operand_bit_to_var.simps)+
qed (auto simp: fun_eq_iff split: option.splits)

lemma assign_shifted_bits_variables: "set (enumerate_variables (assign_shifted_bits k v))
  = { var_bit_to_var (v, i) | i. i < k } \<union> { operand_bit_to_var (a_chr, i) | i. i > 0 \<and> i \<le> k }"
  apply(induction k)
   apply(auto simp: set_enumerate_variables_seq set_enumerate_variables_if)
  done

definition assignment_to_binary:: "nat \<Rightarrow> vname \<Rightarrow> AExp.aexp \<Rightarrow> IMP_Minus_com" where
"assignment_to_binary n v aexp = (case aexp of
  AExp.A a \<Rightarrow> binary_adder n v a (AExp.N 0) |
  AExp.Plus a b \<Rightarrow> binary_adder n v a b |
  AExp.Sub a b \<Rightarrow> binary_subtractor n v a b)"

\<^marker>\<open>title "lem:bitblastExpr"\<close>
lemma assignment_to_binary_correct:
  assumes "n > 0"  "AExp.aval a s < 2 ^ n" "\<forall>v. s v < 2 ^ n" "max_const a < 2 ^ n"
  shows
    "t_small_step_fun (50 * (n + 1))
       (assignment_to_binary n v a,
        IMP_State_To_IMP_Minus s n)
  = (SKIP, IMP_State_To_IMP_Minus (s(v := AExp.aval a s)) n)"
using assms binary_adder_correct  proof(cases a)
  case (Sub x31 x32)
  then show ?thesis
    apply(simp add: assignment_to_binary_def)
    apply(rule binary_subtractor_correct[simplified])
    using assms by(cases x31; cases x32; auto)+
qed (auto simp: assignment_to_binary_def)

lemma assignment_to_binary_variables:
  "n > 0 \<Longrightarrow> set (enumerate_variables (assignment_to_binary n v a)) \<subseteq>
    { var_bit_to_var (w, i) | w i. i \<le> n \<and> (w = v \<or> w \<in> set (vars a)) }
    \<union> { operand_bit_to_var (op, i) | op i. i < n \<and> (op = a_chr \<or> op = b_chr) }
    \<union> { carry, zero }"
  apply(cases a)
  apply(auto simp: assignment_to_binary_def binary_adder_def set_enumerate_variables_seq
      copy_atom_to_operand_variables adder_def com_list_to_seq_variables full_adder_variables
    binary_subtractor_def subtract_handle_underflow_variables
    split: atomExp.splits)
  done
  

end