\<^marker>\<open>creator Florian Keßler\<close>

section "IMP- to IMP-- State Translations"

theory IMP_Minus_To_IMP_Minus_Minus_State_Translations
  imports "IMP_Minus.Small_StepT" Binary_Arithmetic
begin

text \<open> We define a translation between IMP- states, which map registers to natural numbers, and
       IMP-- state where a register can only hold a single bit. Fixing a number of bits n that
       are assumed to be sufficient to represent each natural number in the IMP- states, a register
       ''x'' in IMP- is represented by n registers in IMP--: ''#$x'', ''##$x'', ... ''#...#$x'',
        where the IMP-- register starting with k hashes represents the k- 1th bit of the
       IMP- register. Furthermore, the IMP-- states contain special registers ''carry'' and
        operands ''a'' and ''b'' with n bits respectively, which we will use when replacing
        arithmetic expressions by binary operations when translating IMP- to IMP-- programs. \<close>

type_synonym state = AExp.state
type_synonym bit_state = IMP_Minus_Minus_Small_StepT.state

definition var_to_var_bit:: "vname \<Rightarrow> (vname * nat) option" where
"var_to_var_bit v =
   (if length v > 0 then
      (if hd v = CHR ''#'' then
        (let t = dropWhile (\<lambda>i. i = CHR ''#'') v;
             l = length (takeWhile (\<lambda>i. i = CHR ''#'') v) - 1
         in
           (if length t > 0 \<and> hd t = CHR ''$'' then
              Some (tl t, l)
            else
              None))
       else
         None)
    else None)"

fun n_hashes:: "nat \<Rightarrow> string" where
"n_hashes 0 = []" |
"n_hashes (Suc n) = (CHR ''#'') # (n_hashes n)"

definition var_bit_to_var:: "(vname * nat) \<Rightarrow> vname" where
"var_bit_to_var vk = (n_hashes (snd vk + 1)) @ ''$''  @ (fst vk)"

lemma dropWhile_n_hashes[simp]: "dropWhile (\<lambda>i. i = CHR ''#'') (n_hashes x @ CHR ''$'' # y)
  = CHR ''$'' # y"
  apply(induction x)
  by(auto)

lemma length_takeWhile_n_hashes[simp]:
  "length (takeWhile (\<lambda>i. i = CHR ''#'') (n_hashes x @ CHR ''$'' # y)) = x"
  apply(induction x)
  by auto

lemma encoded_var_decomposition[simp]: "x \<noteq> [] \<Longrightarrow> hd x = CHR ''#''
  \<Longrightarrow> hd (dropWhile (\<lambda>i. i = CHR ''#'') x) = CHR ''$''
  \<Longrightarrow> c \<in> set x \<Longrightarrow> c \<noteq> CHR ''#''
  \<Longrightarrow> n_hashes (length (takeWhile (\<lambda>i. i = CHR ''#'') x))
    @ CHR ''$'' # tl (dropWhile (\<lambda>i. i = CHR ''#'') x) = x"
proof (induction x)
  case (Cons a x)
  hence *: "x \<noteq> []" by auto
  have "hd x = CHR ''#'' \<or> hd x \<noteq> CHR ''#''" by auto
  thus ?case
    apply(elim disjE)
    using Cons * apply(auto)
    by (smt hd_Cons_tl list.size(3) n_hashes.simps(1) self_append_conv2 takeWhile.simps(1)
        takeWhile_dropWhile_id takeWhile_tail)
qed auto

lemma var_to_var_bit_var_bit_to_var[simp]: "var_to_var_bit (var_bit_to_var x) = Some x"
  by (auto simp: var_to_var_bit_def var_bit_to_var_def Let_def)

lemma var_to_var_bit_eq_Some_iff: "var_to_var_bit x = Some y \<longleftrightarrow> x = var_bit_to_var y"
proof
  assume "var_to_var_bit x = Some y"
  thus "x = var_bit_to_var y"
    apply(auto simp: var_to_var_bit_def var_bit_to_var_def Let_def split: if_splits)
    using encoded_var_decomposition
    by (smt Nitpick.size_list_simp(2) One_nat_def char.inject length_tl list.expand list.sel(1)
        list.sel(3) list.simps(3) n_hashes.simps(2) self_append_conv2
        takeWhile_dropWhile_id tl_append2)
qed auto

lemma var_bit_to_var_eq_iff[simp]: "var_bit_to_var (a, b) = var_bit_to_var (c, d) \<longleftrightarrow> (a = c \<and> b = d)"
  apply(auto simp: var_bit_to_var_def)
   apply (metis dropWhile_n_hashes list.inject)
  by (metis length_takeWhile_n_hashes)

lemma var_to_var_bit_of_carry[simp]: "var_to_var_bit ''carry'' = None"
  by(auto simp: var_to_var_bit_def)

lemma var_bit_to_var_neq_carry[simp]: "''carry'' \<noteq> var_bit_to_var (x, y) "
  by(auto simp: var_bit_to_var_def)

lemma var_bit_to_var_neq_carry'[simp]: "var_bit_to_var (x, y) = ''carry'' \<longleftrightarrow> False"
  by(auto simp: var_bit_to_var_def)


(*
fun operand_bit_to_var:: "operand \<Rightarrow> vname" where
"operand_bit_to_var (a n) = replicate (n + 1) (CHR ''a'')" |
"operand_bit_to_var (b n) = replicate (n + 1) (CHR ''b'')"
*)
fun operand_bit_to_var:: "(char * nat) \<Rightarrow> vname" where
"operand_bit_to_var (c, 0) = [c]" |
"operand_bit_to_var (c, (Suc n)) = c # operand_bit_to_var (c, n)"

definition var_to_operand_bit:: "vname \<Rightarrow> (char * nat) option" where
"var_to_operand_bit v = (if v \<noteq> [] \<and> v = (operand_bit_to_var (hd v, length v - 1))
  then Some (hd v, length v - 1) else None)"

lemma hd_of_operand_bit_to_var[simp]:
  "hd (operand_bit_to_var (op, n)) = op" by (induction n) auto

lemma take_2_of_operand_bit_to_var[simp]:
  "take 2 (operand_bit_to_var (c, k)) = operand_bit_to_var (c, min k 1)"
  apply (cases k)
   apply(auto)
  using hd_of_operand_bit_to_var
  by (metis lessI less_Suc_eq_0_disj list.discI operand_bit_to_var.simps(1)
      operand_bit_to_var.simps(2) take0 take_Suc)

lemma length_of_operand_bit_to_var[simp]:
  "length (operand_bit_to_var (op, n)) = n + 1" by (induction n) auto

lemma var_to_operand_bit_of_operand_bit_to_var[simp]:
  "var_to_operand_bit (operand_bit_to_var (op, n)) = Some (op, n)"
  apply(induction n)
  by(auto simp: var_to_operand_bit_def)

lemma var_to_operand_bit_eq_Some_iff: "var_to_operand_bit x = Some (op, i)
  \<longleftrightarrow> x = operand_bit_to_var (op, i)"
  apply(auto simp: var_to_operand_bit_def)
  apply(cases i)
  by auto

lemma var_to_operand_bit_of_carry[simp]: "var_to_operand_bit ''carry'' = None"
  by(simp add: var_to_operand_bit_def)

lemma operand_bit_to_var_neq_carry[simp]: "operand_bit_to_var (op, k) = ''carry'' \<longleftrightarrow> False"
proof
  assume "operand_bit_to_var (op, k) = ''carry''"
  moreover hence "op = CHR ''c''" by (metis hd_of_operand_bit_to_var list.sel)
  ultimately show False
    by (metis option.simps var_to_operand_bit_of_carry var_to_operand_bit_of_operand_bit_to_var)
qed auto

lemma set_of_operand_bit_to_var[simp]: "set (operand_bit_to_var (op, b)) = { op }"
  by (induction b) auto

lemma var_to_operand_bit_var_bit_to_var[simp]: "var_to_operand_bit (var_bit_to_var (a, b)) = None"
  apply(simp add: var_to_operand_bit_def var_bit_to_var_def)
  apply(rule ccontr)
  apply simp
  apply(drule arg_cong[where ?f=set])
  by simp

lemma var_to_var_bit_operand_bit_to_var[simp]: "var_to_var_bit (operand_bit_to_var (c, k)) = None"
  by (simp add: var_to_var_bit_def)

lemma operand_bit_to_var_non_empty: "operand_bit_to_var (op, n) \<noteq> []"
  by (induction n) auto

lemma operand_bit_to_var_eq_operand_bit_to_var_iff[simp]:
  "operand_bit_to_var (op, a) = operand_bit_to_var (op', b)
  \<longleftrightarrow> (op = op' \<and> a = b)"
proof
  assume "operand_bit_to_var (op, a) = operand_bit_to_var (op', b)"
  hence "length (operand_bit_to_var (op, a)) = length (operand_bit_to_var (op', b))
    \<and> set (operand_bit_to_var (op, a)) = set (operand_bit_to_var (op', b))" by simp
  thus "op = op' \<and> a = b" by auto
qed auto

lemma operand_bit_to_var_eq_operand_bit_to_var_iff'[simp]:
  "op # operand_bit_to_var (op, i) = operand_bit_to_var (op', j)
    \<longleftrightarrow> (op = op' \<and> i + 1 = j)"
proof -
  have "op # operand_bit_to_var (op, i) =  operand_bit_to_var (op, i + 1)" by simp
  thus ?thesis using operand_bit_to_var_eq_operand_bit_to_var_iff by presburger
qed

lemma var_bit_to_var_neq_operand_bit_to_var[simp]:
  "var_bit_to_var (v, a) \<noteq> operand_bit_to_var (op, b)"
proof(rule ccontr)
  assume "\<not> (var_bit_to_var (v, a) \<noteq> operand_bit_to_var (op, b))"
  hence "set (var_bit_to_var (v, a)) = set (operand_bit_to_var (op, b))" by simp
  thus False using set_of_operand_bit_to_var by(auto simp: var_bit_to_var_def)
qed

definition IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b::
  "state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bit_state" where
"IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b s n a b = (\<lambda>v.
  (case var_to_var_bit v of
     Some (v', k) \<Rightarrow> if k < n then Some (nth_bit (s v') k) else None |
     None \<Rightarrow>
       (case var_to_operand_bit v of
          Some (CHR ''a'', k) \<Rightarrow> if k < n then Some (nth_bit a k) else None |
          Some (CHR ''b'', k) \<Rightarrow> if k < n then Some (nth_bit b k) else None |
          _ \<Rightarrow> (if v = ''carry'' then Some Zero else None))))"

definition IMP_Minus_State_To_IMP_Minus_Minus:: "state \<Rightarrow> nat \<Rightarrow> bit_state" where
"IMP_Minus_State_To_IMP_Minus_Minus s n
  = IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b s n 0 0 "

definition IMP_Minus_State_To_IMP_Minus_Minus_partial::
  "(vname \<rightharpoonup> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bit_state" where
"IMP_Minus_State_To_IMP_Minus_Minus_partial s n r =
 (\<lambda>v. (case var_to_var_bit v of
         Some (v', k) \<Rightarrow>
           if k \<ge> n then
             None
           else
             (if k < r then
                ((\<lambda>x. Some (nth_bit x k)) \<circ>\<^sub>m s) v'
              else
                Some Zero)
        | None \<Rightarrow> (case var_to_operand_bit v of
            Some (CHR ''a'', k) \<Rightarrow>
              if k < n then
                Some Zero
              else
                None
          | Some (CHR ''b'', k) \<Rightarrow>
              if k < n then
                Some Zero
              else
                None
          |  _ \<Rightarrow>
              if v = ''carry'' then
                Some Zero
              else
                None)))"

lemma IMP_Minus_State_To_IMP_Minus_Minus_partial_of_operand_bit_to_var:
  "IMP_Minus_State_To_IMP_Minus_Minus_partial s n r (operand_bit_to_var (op, k)) =
    (if (op = CHR ''a'' \<or> op = CHR ''b'') \<and> k < n then Some Zero else None)"
  by(auto simp: IMP_Minus_State_To_IMP_Minus_Minus_partial_def split!: char.splits bool.splits)

lemma IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_of_carry[simp]:
  "IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b s k a b ''carry'' = Some Zero"
  by(auto simp: IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_def)

lemma IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_of_operand_a[simp]:
  "j < k \<Longrightarrow> IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b s k a b
  (operand_bit_to_var (CHR ''a'', j)) = Some (nth_bit a j)"
  by(auto simp: IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_def)

lemma IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_of_operand_a'[simp]:
  "j + 1 < k \<Longrightarrow> IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b s k a b
  (CHR ''a'' # operand_bit_to_var (CHR ''a'', j)) = Some (nth_bit a (j + 1))"
proof-
  assume "j + 1 < k"
  moreover have "CHR ''a'' # operand_bit_to_var (CHR ''a'', j) = operand_bit_to_var (CHR ''a'', j + 1)"
    by simp
  ultimately show ?thesis
    using IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_of_operand_a by presburger
qed

lemma IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_of_operand_b[simp]:
  "j < k \<Longrightarrow> IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b s k a b
  (operand_bit_to_var (CHR ''b'', j)) = Some (nth_bit b j)"
  by(auto simp: IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_def)

lemma IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_of_var_bit_to_var[simp]:
  "IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b s n a b (var_bit_to_var (v, i))
    = (if i < n then Some (nth_bit (s v) i) else None)"
  by(auto simp: IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_def)

lemma IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_of_changed_s_neq_iff:
  "IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b s n a b x \<noteq>
       IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b (s(v := y)) n a b x
  \<longleftrightarrow> (\<exists>i < n. var_to_var_bit x = Some (v, i) \<and> nth_bit(s v) i \<noteq> nth_bit y i)"
  by(auto simp: IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_def split: option.splits)

lemma dom_of_IMP_Minus_State_To_IMP_Minus_Minus: "dom (IMP_Minus_State_To_IMP_Minus_Minus s n) =
  { ''carry'' }
  \<union> { var_bit_to_var (w, i) | w i. i < n }
  \<union> { operand_bit_to_var (op, i) | op i. i < n \<and> (op = CHR ''a'' \<or> op = CHR ''b'') }" for s n
  by (auto simp: IMP_Minus_State_To_IMP_Minus_Minus_def var_to_operand_bit_eq_Some_iff
                 var_to_var_bit_eq_Some_iff IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_def
           split: char.splits option.splits bool.splits if_splits)


definition IMP_Minus_Minus_State_To_IMP_Minus:: "bit_state \<Rightarrow> nat \<Rightarrow> state" where
"IMP_Minus_Minus_State_To_IMP_Minus s n = (\<lambda>v.
  bit_list_to_nat (map (\<lambda>i. case s (var_bit_to_var (v, i)) of (Some b) \<Rightarrow>  b |
  None \<Rightarrow> Zero) [0..<n]))"

lemma nth_bit_of_IMP_Minus_Minus_State_To_IMP_Minus:
  "nth_bit (IMP_Minus_Minus_State_To_IMP_Minus s1 n v) k = (if k < n then
    (case s1 (var_bit_to_var (v, k)) of (Some b) \<Rightarrow> b |
                   None \<Rightarrow> Zero)
    else Zero)"
  by(auto simp: IMP_Minus_Minus_State_To_IMP_Minus_def split: option.splits)

lemma all_bits_geq_k_Zero_then_IMP_Minus_Minus_State_To_IMP_Minus_range_limited:
  assumes "\<forall>i v. i \<ge> k \<longrightarrow> s (var_bit_to_var (v, i)) \<noteq> Some One"
  shows "finite (range (IMP_Minus_Minus_State_To_IMP_Minus s n))"
    "Max (range (IMP_Minus_Minus_State_To_IMP_Minus s n)) < 2 ^ k"
proof -
  have "\<forall>v. (IMP_Minus_Minus_State_To_IMP_Minus s n) v < 2 ^ k"
  proof (rule ccontr)
    assume "\<not> (\<forall>v. IMP_Minus_Minus_State_To_IMP_Minus s n v < 2 ^ k)"
    then obtain v where "IMP_Minus_Minus_State_To_IMP_Minus s n v \<ge> 2 ^ k" using leI by blast
    hence "bit_list_to_nat (map (\<lambda>i. case s (var_bit_to_var (v, i)) of (Some b) \<Rightarrow> b |
      None \<Rightarrow> Zero) [0..<n]) \<ge> 2 ^ k" by (auto simp: IMP_Minus_Minus_State_To_IMP_Minus_def)
    then obtain i where "i \<ge> k \<and> i < n \<and>
      (map (\<lambda>i. case s (var_bit_to_var (v, i)) of (Some b) \<Rightarrow> b | None \<Rightarrow> Zero) [0..<n]) ! i = One"
      using bit_list_to_nat_geq_two_to_the_k_then by fastforce
    moreover hence "s (var_bit_to_var (v, i)) \<noteq> Some One"
      using \<open>\<forall>i v. i \<ge> k \<longrightarrow> s (var_bit_to_var (v, i)) \<noteq> Some One\<close> by simp
    ultimately show False apply(cases "s (var_bit_to_var (v, i))") by auto
  qed
  thus  "finite (range (IMP_Minus_Minus_State_To_IMP_Minus s n))"
    "Max (range (IMP_Minus_Minus_State_To_IMP_Minus s n)) < 2 ^ k"
    using bounded_nat_set_is_finite by auto
qed

end