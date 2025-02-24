\<^marker>\<open>creator Florian Keßler\<close>
\<^marker>\<open>contributor Fabian Huch\<close>

section "IMP to IMP- State Translations"

theory IMP_To_IMP_Minus_State_Translations
  imports "IMP.IMP_Base" Binary_Arithmetic
begin

text \<open> We define a translation between IMP states, which map registers to natural numbers, and
       IMP- state where a register can only hold a single bit. Fixing a number of bits n that
       are assumed to be sufficient to represent each natural number in the IMP states, a register
       ''x'' in IMP is represented by n+1 registers in IMP-: A zeroness register in ''#$x'',
        followed by the actual bits ''##$x'', ... ''#...#$x'',
        where the IMP- register starting with k hashes represents the k-th bit of the
        IMP register. Furthermore, the IMP- states contain special registers carry and
        operands ''a'' and ''b'' with n bits respectively, which we will use when replacing
        arithmetic expressions by binary operations when translating IMP to IMP- programs. \<close>
                          
type_synonym state = IMP_Base.state
type_synonym bit_state = "IMP_Minus_Base.state"

definition "sep1 = CHR ''#''"
definition "sep2 = CHR ''$''"
definition "a_chr = CHR ''a''"
definition "b_chr = CHR ''b''"

lemma sep1_ne_sep2[simp]: "sep1 \<noteq> sep2" "sep2 \<noteq> sep1"
  unfolding sep1_def sep2_def by simp_all

lemma sep1_ne_a[simp]: "sep1 \<noteq> a_chr" "a_chr \<noteq> sep1"
  unfolding sep1_def a_chr_def by simp_all

lemma sep2_ne_a[simp]: "sep2 \<noteq> a_chr" "a_chr \<noteq> sep2"
  unfolding sep2_def a_chr_def by simp_all

lemma a_ne_b[simp]: "a_chr \<noteq> b_chr" "b_chr \<noteq> a_chr"
  unfolding a_chr_def b_chr_def by simp_all

lemma sep1_ne_b[simp]: "sep1 \<noteq> b_chr"  "b_chr \<noteq> sep1"
  unfolding sep1_def b_chr_def by simp_all

lemma sep2_ne_b[simp]: "sep2 \<noteq> b_chr" "b_chr \<noteq> sep2"
  unfolding sep2_def b_chr_def by simp_all

definition var_to_var_bit:: "vname \<Rightarrow> (vname * nat) option" where
"var_to_var_bit v =
   (if length v > 0 then
      (if hd v = sep1 then
        (let t = dropWhile (\<lambda>i. i = sep1) v;
             l = length (takeWhile (\<lambda>i. i = sep1) v) - 1
         in
           (if length t > 0 \<and> hd t = sep2 then
              Some (tl t, l)
            else
              None))
       else
         None)
    else None)"

definition n_hashes :: "nat \<Rightarrow> string" where "n_hashes n = replicate n (sep1)"

definition var_bit_to_var:: "(vname * nat) \<Rightarrow> vname" where
"var_bit_to_var vk = (n_hashes (snd vk + 1)) @ [sep2]  @ (fst vk)"

lemma dropWhile_n_hashes[simp]: "dropWhile (\<lambda>i. i = sep1) (n_hashes x @ sep2 # y)
  = sep2 # y"
  apply(induction x)
  by(auto simp: n_hashes_def sep1_def sep2_def)

lemma length_takeWhile_n_hashes[simp]:
  "length (takeWhile (\<lambda>i. i = sep1) (n_hashes x @ sep2 # y)) = x"
  apply(induction x)
  by (auto simp: n_hashes_def sep1_def sep2_def)

lemma encoded_var_decomposition[simp]: "x \<noteq> [] \<Longrightarrow> hd x = sep1
  \<Longrightarrow> hd (dropWhile (\<lambda>i. i = sep1) x) = sep2
  \<Longrightarrow> c \<in> set x \<Longrightarrow> c \<noteq> sep1
  \<Longrightarrow> n_hashes (length (takeWhile (\<lambda>i. i = sep1) x))
    @ sep2 # tl (dropWhile (\<lambda>i. i = sep1) x) = x"
proof (induction x)
  case (Cons a x)
  hence *: "x \<noteq> []" by auto
  have "hd x = sep1 \<or> hd x \<noteq> sep1" by auto
  thus ?case
    apply(elim disjE)
    using Cons * apply(auto simp: n_hashes_def)
    by (metis (lifting) dropWhile_eq_self_iff list.collapse list.size(3) replicate_empty takeWhile_dropWhile_id
        takeWhile_eq_Nil_iff)
qed auto

lemma var_to_var_bit_var_bit_to_var[simp]: "var_to_var_bit (var_bit_to_var x) = Some x"
  unfolding var_to_var_bit_def var_bit_to_var_def Let_def
  apply (auto simp: var_to_var_bit_def var_bit_to_var_def Let_def)
  unfolding sep1_def sep2_def n_hashes_def sep1_def sep2_def
  apply simp_all 
  done

lemma var_to_var_bit_eq_Some_iff: "var_to_var_bit x = Some y \<longleftrightarrow> x = var_bit_to_var y"
proof
  assume "var_to_var_bit x = Some y"
  thus "x = var_bit_to_var y"
    apply(auto simp: var_to_var_bit_def var_bit_to_var_def Let_def split: if_splits)
    using encoded_var_decomposition
    by (simp add: takeWhile_eq_Nil_iff)
qed auto

lemma var_bit_to_var_eq_iff[simp]: "var_bit_to_var (a, b) = var_bit_to_var (c, d) \<longleftrightarrow> (a = c \<and> b = d)"
  apply(auto simp: var_bit_to_var_def)
   apply (metis dropWhile_n_hashes list.inject)
  by (metis length_takeWhile_n_hashes nat.inject)

(* opaque def, otherwise automation tries to work with strings... *)
definition "zero = ''zero''"
definition "carry = ''carry''"

lemma zero_ne_carry[simp]: "zero \<noteq> carry" "carry \<noteq> zero"
  unfolding zero_def carry_def by simp_all

lemma var_to_var_bit_zero[simp]: "var_to_var_bit zero = None"
  by(simp add: var_to_var_bit_def zero_def sep1_def)

lemma var_to_var_bit_of_carry[simp]: "var_to_var_bit carry = None"
  by(auto simp: var_to_var_bit_def carry_def sep1_def)

lemma var_bit_to_var_neq_carry[simp]: "carry \<noteq> var_bit_to_var (x, y)" "var_bit_to_var (x, y) \<noteq> carry"
  by(auto simp: var_bit_to_var_def n_hashes_def carry_def sep1_def)

lemma var_bit_to_var_neq_carry'[simp]: "var_bit_to_var (x, y) = carry \<longleftrightarrow> False"
  by(auto simp: var_bit_to_var_def n_hashes_def carry_def sep1_def)

lemma var_bit_to_var_neq_zero[simp]: "zero \<noteq> var_bit_to_var (x, y)"
  by(auto simp: var_bit_to_var_def n_hashes_def zero_def sep1_def)

lemma var_bit_to_var_neq_zero'[simp]: "var_bit_to_var (x, y) = zero \<longleftrightarrow> False"
  by(auto simp: var_bit_to_var_def n_hashes_def zero_def sep1_def)

(* FIXME use def *)
fun operand_bit_to_var where "operand_bit_to_var (c,n) = replicate (Suc n) c"
declare operand_bit_to_var.simps[simp del]
lemmas operand_bit_to_var_def = operand_bit_to_var.simps

definition var_to_operand_bit:: "vname \<Rightarrow> (char * nat) option" where
"var_to_operand_bit v = (if v \<noteq> [] \<and> v = (operand_bit_to_var (hd v, length v - 1))
  then Some (hd v, length v - 1) else None)"

lemma hd_of_operand_bit_to_var[simp]:
  "hd (operand_bit_to_var (op, n)) = op" by (induction n) (auto simp: operand_bit_to_var_def)

lemma take_2_of_operand_bit_to_var[simp]:
  "take 2 (operand_bit_to_var (c, k)) = operand_bit_to_var (c, min k 1)"
  by (cases k) (auto simp: operand_bit_to_var_def)

lemma length_of_operand_bit_to_var[simp]:
  "length (operand_bit_to_var (op, n)) = n + 1" by (induction n) (auto simp: operand_bit_to_var_def)

lemma var_to_operand_bit_of_operand_bit_to_var[simp]:
  "var_to_operand_bit (operand_bit_to_var (op, n)) = Some (op, n)"
  apply(induction n)
  by(auto simp: var_to_operand_bit_def operand_bit_to_var_def)

lemma var_to_operand_bit_eq_Some_iff: "var_to_operand_bit x = Some (op, i)
  \<longleftrightarrow> x = operand_bit_to_var (op, i)"
  by(auto simp: var_to_operand_bit_def operand_bit_to_var_def)
  

lemma var_to_operand_bit_of_zero[simp]: "var_to_operand_bit zero = None"
  by(simp add: var_to_operand_bit_def zero_def operand_bit_to_var_def)

lemma var_to_operand_bit_of_carry[simp]: "var_to_operand_bit carry = None"
  by(simp add: var_to_operand_bit_def carry_def operand_bit_to_var_def)

lemma operand_bit_to_var_neq_carry[simp]: "operand_bit_to_var (op, k) = carry \<longleftrightarrow> False"
  by (metis option.distinct(1) var_to_operand_bit_eq_Some_iff var_to_operand_bit_of_carry)

lemma operand_bit_to_var_neq_zero[simp]: "operand_bit_to_var (op, k) = zero \<longleftrightarrow> False"
  by (metis option.distinct(1) var_to_operand_bit_of_operand_bit_to_var var_to_operand_bit_of_zero)

lemma set_of_operand_bit_to_var[simp]: "set (operand_bit_to_var (op, b)) = { op }"
  by (induction b) (auto simp: operand_bit_to_var_def)

lemma var_to_operand_bit_var_bit_to_var[simp]: "var_to_operand_bit (var_bit_to_var (a, b)) = None"
  unfolding var_to_operand_bit_def var_bit_to_var_def n_hashes_def
  apply (auto simp: operand_bit_to_var_def)
  by (metis in_set_conv_decomp in_set_replicate sep1_ne_sep2 set_ConsD)

lemma var_to_var_bit_operand_bit_to_var[simp]: "var_to_var_bit (operand_bit_to_var (c, k)) = None"
  by (simp add: var_to_var_bit_def)

lemma operand_bit_to_var_non_empty: "operand_bit_to_var (op, n) \<noteq> []"
  by (induction n) (auto simp: operand_bit_to_var_def)

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
  have "op # operand_bit_to_var (op, i) =  operand_bit_to_var (op, i + 1)" by (simp add: operand_bit_to_var_def)
  thus ?thesis using operand_bit_to_var_eq_operand_bit_to_var_iff by metis
qed

lemma var_bit_to_var_neq_operand_bit_to_var[simp]:
  "var_bit_to_var (v, a) \<noteq> operand_bit_to_var (op, b)"
  by (metis option.distinct(1) var_to_var_bit_operand_bit_to_var var_to_var_bit_var_bit_to_var)


definition IMP_State_To_IMP_Minus_with_operands_a_b::
  "state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bit_state" where
"IMP_State_To_IMP_Minus_with_operands_a_b s n a b = (\<lambda>v.
  (case var_to_var_bit v of
     Some (v', k) \<Rightarrow> case k of
        0 \<Rightarrow> Some (zero_bit (s v') n)
      | Suc k \<Rightarrow> if k < n then Some (nth_bit (s v') k) else None |
     None \<Rightarrow>
       (case var_to_operand_bit v of
          Some (c, k) \<Rightarrow> if k < n \<and> c = a_chr then Some (nth_bit a k) else
                         if k < n \<and> c = b_chr then Some (nth_bit b k) else
                         None |
          _ \<Rightarrow> (if v = carry \<or> v = zero then Some Zero else None))))"

definition IMP_State_To_IMP_Minus:: "state \<Rightarrow> nat \<Rightarrow> bit_state" where
"IMP_State_To_IMP_Minus s n
  = IMP_State_To_IMP_Minus_with_operands_a_b s n 0 0 "



lemma IMP_State_To_IMP_Minus_with_operands_a_b_of_carry[simp]:
  "IMP_State_To_IMP_Minus_with_operands_a_b s k a b carry = Some Zero"
  by(auto simp: IMP_State_To_IMP_Minus_with_operands_a_b_def)

lemma IMP_State_To_IMP_Minus_with_operands_a_b_of_zero[simp]:
  "IMP_State_To_IMP_Minus_with_operands_a_b s k a b zero = Some Zero"
  by(auto simp: IMP_State_To_IMP_Minus_with_operands_a_b_def)

lemma IMP_State_To_IMP_Minus_with_operands_a_b_of_operand_a[simp]:
  "j < k \<Longrightarrow> IMP_State_To_IMP_Minus_with_operands_a_b s k a b
  (operand_bit_to_var (a_chr, j)) = Some (nth_bit a j)"
  by(auto simp: IMP_State_To_IMP_Minus_with_operands_a_b_def)

lemma IMP_State_To_IMP_Minus_with_operands_a_b_of_operand_a'[simp]:
  "j + 1 < k \<Longrightarrow> IMP_State_To_IMP_Minus_with_operands_a_b s k a b
  (a_chr # operand_bit_to_var (a_chr, j)) = Some (nth_bit a (j + 1))"
proof-
  assume "j + 1 < k"
  moreover have "a_chr # operand_bit_to_var (a_chr, j) = operand_bit_to_var (a_chr, j + 1)"
    by simp
  ultimately show ?thesis
    using IMP_State_To_IMP_Minus_with_operands_a_b_of_operand_a by presburger
qed

lemma IMP_State_To_IMP_Minus_with_operands_a_b_of_operand_b[simp]:
  "j < k \<Longrightarrow> IMP_State_To_IMP_Minus_with_operands_a_b s k a b
  (operand_bit_to_var (b_chr, j)) = Some (nth_bit b j)"
  by (auto simp: IMP_State_To_IMP_Minus_with_operands_a_b_def)

lemma IMP_State_To_IMP_Minus_with_operands_a_b_of_var_bit_to_var[simp]:
  "IMP_State_To_IMP_Minus_with_operands_a_b s n a b (var_bit_to_var (v, i))
    = (case i of 0 \<Rightarrow> Some (zero_bit (s v) n) | Suc i \<Rightarrow> if i < n then Some (nth_bit (s v) i) else None)"
  by(auto simp: IMP_State_To_IMP_Minus_with_operands_a_b_def)

lemma IMP_State_To_IMP_Minus_with_operands_a_b_of_z[simp]:
  "i = 0 \<Longrightarrow> IMP_State_To_IMP_Minus_with_operands_a_b s n a b (var_bit_to_var (v, i))
    = Some (zero_bit (s v) n)"
  by(auto simp: IMP_State_To_IMP_Minus_with_operands_a_b_def)

lemma zero_IMP_State_To_IMP_Minus_with_operands_a_b[simp]:
  "IMP_State_To_IMP_Minus_with_operands_a_b s n a b (var_bit_to_var (v, 0)) = Some Zero 
  \<longleftrightarrow> zero_bit (s v) n = Zero"
  by(auto simp: IMP_State_To_IMP_Minus_with_operands_a_b_def split: option.splits)

lemma zero_IMP_State_To_IMP_Minus_with_operands_a_b2[simp]:
  "IMP_State_To_IMP_Minus_with_operands_a_b s n a b (var_bit_to_var (v, 0)) = Some One 
  \<longleftrightarrow> zero_bit (s v) n = One"
  by(auto simp: IMP_State_To_IMP_Minus_with_operands_a_b_def split: option.splits)

lemma IMP_State_To_IMP_Minus_with_operands_a_b_of_changed_s_neq_iff:
  "IMP_State_To_IMP_Minus_with_operands_a_b s n a b x \<noteq>
       IMP_State_To_IMP_Minus_with_operands_a_b (s(v := y)) n a b x
  \<longleftrightarrow> (var_to_var_bit x = Some (v, 0) \<and> zero_bit (s v) n \<noteq> zero_bit y n) \<or> 
      (\<exists>i < n. var_to_var_bit x = Some (v, Suc i) \<and> nth_bit(s v) i \<noteq> nth_bit y i)" (is "?lhs \<longleftrightarrow> ?rhs")
  by(auto simp: IMP_State_To_IMP_Minus_with_operands_a_b_def split: option.splits if_splits nat.splits)

lemma dom_of_IMP_State_To_IMP_Minus: "dom (IMP_State_To_IMP_Minus s n) =
  { carry, zero }
  \<union> { var_bit_to_var (w, i) | w i. i \<le> n }
  \<union> { operand_bit_to_var (op, i) | op i. i < n \<and> (op = a_chr \<or> op = b_chr) }" for s n
  by (auto simp: IMP_State_To_IMP_Minus_def var_to_operand_bit_eq_Some_iff
                 var_to_var_bit_eq_Some_iff IMP_State_To_IMP_Minus_with_operands_a_b_def
           split: char.splits option.splits bool.splits if_splits nat.splits)


definition IMP_Minus_State_To_IMP:: "bit_state \<Rightarrow> nat \<Rightarrow> state" where
"IMP_Minus_State_To_IMP s n = (\<lambda>v.
  bit_list_to_nat (map (\<lambda>i. case s (var_bit_to_var (v, i)) of (Some b) \<Rightarrow>  b |
  None \<Rightarrow> Zero) [0..<n]))"

\<^marker>\<open>title "def:bitblast"\<close>
lemma nth_bit_of_IMP_Minus_State_To_IMP:
  "nth_bit (IMP_Minus_State_To_IMP s1 n v) k = (if k < n then
    (case s1 (var_bit_to_var (v, k)) of (Some b) \<Rightarrow> b |
                   None \<Rightarrow> Zero)
    else Zero)"
  by(auto simp: IMP_Minus_State_To_IMP_def split: option.splits)

lemma zero_bit_le[simp]: "a + b < 2 ^ n \<Longrightarrow> zero_bit (a+b) (Suc n) = zero_bit (a+b) n"
  by (auto simp: zero_bit_def bits_zero_iff less_Suc_eq nth_bit_nat_is_right_shift)

lemma zero_IMP_Minus_State_To_IMP[simp]:
  "s b < 2 ^n \<Longrightarrow> (IMP_State_To_IMP_Minus s n) (var_bit_to_var (b, 0)) = Some Zero \<longleftrightarrow> s b = 0"
  by (auto simp: IMP_State_To_IMP_Minus_def all_bits_equal_then_equal zero_bit_zero split: option.splits)

lemma zero_IMP_Minus_State_To_IMP2[simp]:
  "s b < 2 ^n \<Longrightarrow> (IMP_State_To_IMP_Minus s n) (var_bit_to_var (b, 0)) = Some One \<longleftrightarrow> s b \<noteq> 0"
  using all_bits_equal_then_equal
  by (fastforce simp: IMP_State_To_IMP_Minus_def  zero_bit_one)
  
lemma all_bits_geq_k_Zero_then_IMP_Minus_State_To_IMP_range_limited:
  assumes "\<forall>i v. i \<ge> k \<longrightarrow> s (var_bit_to_var (v, i)) \<noteq> Some One"
  shows "finite (range (IMP_Minus_State_To_IMP s n))"
    "Max (range (IMP_Minus_State_To_IMP s n)) < 2 ^ k"
proof -
  have "\<forall>v. (IMP_Minus_State_To_IMP s n) v < 2 ^ k"
  proof (rule ccontr)
    assume "\<not> (\<forall>v. IMP_Minus_State_To_IMP s n v < 2 ^ k)"
    then obtain v where "IMP_Minus_State_To_IMP s n v \<ge> 2 ^ k" using leI by blast
    hence "bit_list_to_nat (map (\<lambda>i. case s (var_bit_to_var (v, i)) of (Some b) \<Rightarrow> b |
      None \<Rightarrow> Zero) [0..<n]) \<ge> 2 ^ k" by (auto simp: IMP_Minus_State_To_IMP_def)
    then obtain i where "i \<ge> k \<and> i < n \<and>
      (map (\<lambda>i. case s (var_bit_to_var (v, i)) of (Some b) \<Rightarrow> b | None \<Rightarrow> Zero) [0..<n]) ! i = One"
      using bit_list_to_nat_geq_two_to_the_k_then by fastforce
    moreover hence "s (var_bit_to_var (v, i)) \<noteq> Some One"
      using \<open>\<forall>i v. i \<ge> k \<longrightarrow> s (var_bit_to_var (v, i)) \<noteq> Some One\<close> by simp
    ultimately show False apply(cases "s (var_bit_to_var (v, i))") by auto
  qed
  thus  "finite (range (IMP_Minus_State_To_IMP s n))"
    "Max (range (IMP_Minus_State_To_IMP s n)) < 2 ^ k"
    using bounded_nat_set_is_finite by auto
qed

end