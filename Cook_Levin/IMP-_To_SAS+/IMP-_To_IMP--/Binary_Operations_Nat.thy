theory Binary_Operations_Nat
  imports Binary_Operations Primitives Binary_Arithmetic_Nat
          IMP_Minus_To_IMP_Minus_Minus_State_Translations_nat
          IMP_Minus_Max_Constant_Nat
begin


fun com_list_to_seq_nat:: "nat \<Rightarrow> nat" where
  "com_list_to_seq_nat n =
    (if n = 0
     then 0 ## 0
     else 2 ## ((hd_nat n) ## ((com_list_to_seq_nat (tl_nat n)) ## 0))
    )"

fun com_list_to_seq_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "com_list_to_seq_acc acc n =
    (if n = 0
     then acc
     else com_list_to_seq_acc (2 ## ((hd_nat n) ## (acc ## 0))) (tl_nat n)
    )"

lemma com_list_to_seq_induct:
  "com_list_to_seq_nat (append_nat (reverse_nat ys) xs) =
    com_list_to_seq_acc  (com_list_to_seq_nat xs) ys"
  apply(induct ys arbitrary:xs rule: length_nat.induct)
   apply (auto simp only: reverse_nat_0 append_nat.simps)
   apply(subst com_list_to_seq_acc.simps)
   apply(auto simp del:com_list_to_seq_acc.simps com_list_to_seq_nat.simps 
      simp add: append_rev_nat)
  apply(subst (2) com_list_to_seq_acc.simps)
  apply(auto simp del:com_list_to_seq_acc.simps com_list_to_seq_nat.simps 
      simp add: append_rev_nat)
  apply(subst com_list_to_seq_nat.simps)
  apply(auto simp del:com_list_to_seq_acc.simps com_list_to_seq_nat.simps 
      simp add: append_rev_nat cons_Nil hd_cons tl_cons)
  done

lemma com_list_to_seq_rev:
  "com_list_to_seq_nat (append_nat ys xs) =
    com_list_to_seq_acc (com_list_to_seq_nat xs) (reverse_nat ys)"
  using rev_rev_nat com_list_to_seq_induct by metis

definition com_list_to_seq_tail :: "nat \<Rightarrow> nat" where
  "com_list_to_seq_tail ys = com_list_to_seq_acc (0 ## 0) (reverse_nat ys)"

lemma subtail_com_list_to_seq: "com_list_to_seq_nat ys = com_list_to_seq_tail ys"
  using com_list_to_seq_rev[of ys 0] append_nat_0 com_list_to_seq_tail_def
  by auto

definition comm_list_encode :: "IMP_Minus_Minus_com list \<Rightarrow> nat" where
  "comm_list_encode xs = list_encode (map comm_encode xs)"

definition comm_list_decode :: "nat \<Rightarrow> IMP_Minus_Minus_com list" where
  "comm_list_decode xs = map comm_decode (list_decode xs)"

lemma comm_list_id[simp]: "comm_list_decode (comm_list_encode x) = x"
  by (auto simp add:comm_list_encode_def comm_list_decode_def) (metis comm_id comp_def map_idI)
    
lemma sub_com_list_to_seq:
  "com_list_to_seq_nat (comm_list_encode xs) = comm_encode (com_list_to_seq xs)"
  apply (induct xs)
  apply (subst com_list_to_seq_nat.simps)
   apply (auto simp only: comm_list_encode_def sub_cons cons0)
   apply (simp add: cons0)
  apply (subst com_list_to_seq_nat.simps)
  apply (simp only:list.map cons0 sub_cons sub_hd sub_tl head.simps tail.simps
        com_list_to_seq.simps comm_encode.simps)
  apply auto
  done

fun binary_assign_constant_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"binary_assign_constant_nat n v x = (if n = 0 then cons 0 0 else cons 2 ( cons (cons 1 
    (cons (var_bit_to_var_nat(prod_encode (v,n-1))) (cons (nth_bit_nat x (n-1)) 0 )))
  (cons (binary_assign_constant_nat (n-1) v x)0) ) )"

fun binary_assign_constant_acc:: " nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"binary_assign_constant_acc acc diff n v x = (if diff = 0 then acc else
binary_assign_constant_acc  (cons 2 ( cons (cons 1 
    (cons (var_bit_to_var_tail(prod_encode (v,n-diff))) (cons (nth_bit_tail x (n-diff)) 0 )))
  (cons acc 0) )) (diff-1) n v x )"

lemma binary_assign_constant_induct: 
  "diff \<le>n \<Longrightarrow>
 binary_assign_constant_acc (binary_assign_constant_nat (n- diff) v x)  diff n v x
= binary_assign_constant_nat n v x"
  apply(induct diff)
  apply (auto simp add: subtail_nth_bit subtail_var_bit_to_var)
  done

definition  binary_assign_constant_tail:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"binary_assign_constant_tail n v x = binary_assign_constant_acc (0##0) n n v x "
lemma subtail_binary_assign_constant:
"binary_assign_constant_tail n v x = binary_assign_constant_nat n v x"
  using binary_assign_constant_induct[of n n v x]
  apply (auto simp add:binary_assign_constant_tail_def)
  done

lemma  sub_binary_assign_constant:
"binary_assign_constant_nat n (vname_encode v) x = comm_encode (binary_assign_constant n v x)"
  apply (induct n)
   apply(subst binary_assign_constant_nat.simps)
   apply (simp only: cons0 binary_assign_constant.simps)
   apply simp
  apply(subst binary_assign_constant_nat.simps)
  apply (simp only: cons0 binary_assign_constant.simps sub_cons sub_var_bit_to_var
    comm_encode.simps  flip: vname_nat_encode.simps sub_nth_bit )
  apply auto
  done
 

fun copy_var_to_operand_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "copy_var_to_operand_nat i op v =
    (if i = 0
      then 0 ## 0
      else
        2 ## 
          (3 ## ((var_bit_to_var_nat (prod_encode (v, i - 1))) ## 0)
             ## (1 ## (operand_bit_to_var_nat (prod_encode (op, i - 1))) ## 1 ## 0)
             ## (1 ## (operand_bit_to_var_nat (prod_encode (op, i - 1))) ## 0 ## 0)
             ## 0)
          ## (copy_var_to_operand_nat (i - 1) op v)
          ## 0)"

fun copy_var_to_operand_acc ::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
 "copy_var_to_operand_acc acc diff i op v =
  (if diff = 0
   then acc
   else copy_var_to_operand_acc
          (2 ## 
            (3 ## ((var_bit_to_var_tail (prod_encode (v, i - diff))) ## 0)
               ## (1 ## (operand_bit_to_var_tail (prod_encode (op, i - diff))) ## 1 ## 0)
               ## (1 ## (operand_bit_to_var_tail (prod_encode (op, i - diff))) ## 0 ## 0)
               ## 0)
             ## acc
             ## 0)
          (diff - 1) i op v)"

lemma copy_var_to_operand_induct :
  "diff \<le> i \<Longrightarrow> copy_var_to_operand_acc (copy_var_to_operand_nat (i - diff) op v) diff i op v 
                  = copy_var_to_operand_nat i op v"
  by (induct diff) (auto simp add:subtail_var_bit_to_var subtail_operand_bit_to_var
    simp del: operand_bit_to_var_nat.simps)

definition copy_var_to_operand_tail :: "nat => nat => nat => nat" where
  "copy_var_to_operand_tail i op v = copy_var_to_operand_acc (0 ## 0) i i op v"

lemma subtail_copy_var_to_operand:
  "copy_var_to_operand_tail i op v = copy_var_to_operand_nat i op v"
  using copy_var_to_operand_induct [of i i op v]
  by(auto simp add: copy_var_to_operand_tail_def)

lemma sub_copy_var_to_operand:
  "copy_var_to_operand_nat i (encode_char op) (vname_encode v)
    = comm_encode (copy_var_to_operand i op v)"
  apply (induct i)
   apply (simp add: cons0)
  apply (subst copy_var_to_operand_nat.simps)
  apply (auto simp only: sub_cons cons0 sub_var_bit_to_var  sub_operand_bit_to_var
      copy_var_to_operand.simps comm_encode.simps bit_encode.simps vname_list_encode_def
      simp flip:vname_nat_encode.simps char_nat_encode.simps)
  apply auto
  done


fun copy_const_to_operand_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"copy_const_to_operand_nat i op x = (if i =0 then 0##0 else 
2 ## (1 ## (operand_bit_to_var_nat (prod_encode (op,i-1))) ## (nth_bit_nat x (i-1)) ## 0) ## (copy_const_to_operand_nat (i-1) op x ) ## 0
)"

fun copy_const_to_operand_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"copy_const_to_operand_acc acc diff i op x = (if diff =0 then acc  else copy_const_to_operand_acc
(2 ## (1 ## (operand_bit_to_var_tail (prod_encode (op,i-diff))) ## (nth_bit_tail x (i-diff)) ## 0) ## acc ## 0
) (diff-1) i op x )"

lemma copy_const_to_operand_induct:
"diff\<le>i \<Longrightarrow>copy_const_to_operand_acc (copy_const_to_operand_nat (i-diff) op x) diff i op x =
copy_const_to_operand_nat i op x"
  apply(induct diff)
   apply(auto simp add: subtail_operand_bit_to_var subtail_nth_bit)
  done

definition copy_const_to_operand_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"copy_const_to_operand_tail i op x = copy_const_to_operand_acc (0##0) i i op x"

lemma subtail_copy_const_to_operand:
"copy_const_to_operand_tail i op x = 
copy_const_to_operand_nat i op x "
  using copy_const_to_operand_induct [of i i op x]
  apply(auto simp add:copy_const_to_operand_tail_def)
  done

lemma sub_copy_const_to_operand:
 "copy_const_to_operand_nat i (encode_char op) x = comm_encode (copy_const_to_operand i op x)  "
 apply (induct i)
   apply (simp add: cons0)
  apply (subst copy_const_to_operand_nat.simps)
  apply (auto simp only: sub_cons cons0 sub_var_bit_to_var  sub_operand_bit_to_var
 copy_const_to_operand.simps comm_encode.simps sub_nth_bit
simp flip:vname_nat_encode.simps char_nat_encode.simps )
  apply auto
  done
 

definition copy_atom_to_operand_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"copy_atom_to_operand_nat n op a = ( if fst_nat a = 0 then  copy_var_to_operand_nat n op (snd_nat a)
 else copy_const_to_operand_nat n op (snd_nat a))"

definition copy_atom_to_operand_tail:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"copy_atom_to_operand_tail n op a = ( if fst_nat a = 0 then  copy_var_to_operand_tail n op (snd_nat a)
 else copy_const_to_operand_nat n op (snd_nat a))"

lemma subtail_copy_atom_to_operand: "copy_atom_to_operand_tail n op a = copy_atom_to_operand_nat n op a"
  apply (simp only: copy_atom_to_operand_tail_def copy_atom_to_operand_nat_def
subtail_copy_var_to_operand  ) done

lemma sub_copy_atom_to_operand: 
"copy_atom_to_operand_nat n (encode_char op) (atomExp_encode a) = comm_encode (copy_atom_to_operand n op a)"
  apply (auto simp only:copy_atom_to_operand_nat_def atomExp_encode.simps sub_fst sub_snd fst_def snd_def
          copy_atom_to_operand_def
sub_copy_const_to_operand sub_copy_var_to_operand split:atomExp.splits ) 
   apply auto
  done


definition assign_var_carry_nat:: 
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"assign_var_carry_nat i v a b c = 
2 ## (1 ## (var_bit_to_var_nat(prod_encode (v, i))) ##
(if a + b + c = 1 \<or> a + b + c = 3 then 1 else 0) ## 0 ) ## (1##(vname_encode ''carry'')## (if a + b + c \<ge> 2 then 1 else 0) ## 0) ## 0 "

definition assign_var_carry_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"  where 
"assign_var_carry_tail i v a b c = 
2 ## (1 ## (var_bit_to_var_tail(prod_encode (v, i))) ##
(if a + b + c = 1 \<or> a + b + c = 3 then 1 else 0) ## 0 ) ## (1##(vname_encode ''carry'')## (if a + b + c \<ge> 2 then 1 else 0) ## 0) ## 0 "


lemma subtail_assign_var_carry: 
"assign_var_carry_tail  i v a b c = assign_var_carry_nat  i v a b c"
  apply (auto simp  only: assign_var_carry_tail_def assign_var_carry_nat_def 
        subtail_var_bit_to_var)
  done


lemma sub_assign_var_carry: 
"assign_var_carry_nat i (vname_encode v) a b c = comm_encode(assign_var_carry i v a b c)"
  apply (auto simp only: assign_var_carry_nat_def sub_var_bit_to_var cons0 sub_cons
    assign_var_carry_def comm_encode.simps bit_encode.simps split:if_splits
 simp flip: vname_nat_encode.simps)
  done


definition full_adder_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"full_adder_nat i v  = (let assign = assign_var_carry_nat i v; op_a = operand_bit_to_var_nat (prod_encode(encode_char(CHR ''a''), i));
  op_b = operand_bit_to_var_nat (prod_encode(encode_char (CHR ''b''), i)) in 
3##(op_a ## 0) ##(3##((vname_encode ''carry'') ## 0)## (3 ## (op_b ## 0) ## (assign 1 1 1) ## ( assign 1 1 0) ## 0)##(
                                                       (3 ## (op_b ## 0) ## (assign 1 0 1) ## ( assign 1 0 0) ## 0))##0)
               ##(3##((vname_encode ''carry'') ## 0)## (3 ## (op_b ## 0) ## (assign 0 1 1) ## ( assign 0 1 0) ## 0)##(
                                                       (3 ## (op_b ## 0) ## (assign 0 0 1) ## ( assign 0 0 0) ## 0))##0)
## 0
 )"

definition full_adder_tail ::  "nat \<Rightarrow> nat \<Rightarrow> nat"  where 
"full_adder_tail i v  = (let assign = assign_var_carry_tail i v; op_a = operand_bit_to_var_tail (prod_encode(encode_char(CHR ''a''), i));
  op_b = operand_bit_to_var_tail (prod_encode(encode_char (CHR ''b''), i)) in 
3##(op_a ## 0) ##(3##((vname_encode ''carry'') ## 0)## (3 ## (op_b ## 0) ## (assign 1 1 1) ## ( assign 1 1 0) ## 0)##(
                                                       (3 ## (op_b ## 0) ## (assign 1 0 1) ## ( assign 1 0 0) ## 0))##0)
               ##(3##((vname_encode ''carry'') ## 0)## (3 ## (op_b ## 0) ## (assign 0 1 1) ## ( assign 0 1 0) ## 0)##(
                                                       (3 ## (op_b ## 0) ## (assign 0 0 1) ## ( assign 0 0 0) ## 0))##0)
## 0
 )"


lemma subtail_full_adder: "full_adder_tail i v = full_adder_nat i v" 
  apply(auto simp only: Let_def full_adder_tail_def 
          full_adder_nat_def subtail_assign_var_carry subtail_operand_bit_to_var )
  done

lemma sub_full_adder: "full_adder_nat i (vname_encode v) = comm_encode (full_adder i v)"
  apply (auto simp only:full_adder_nat_def sub_assign_var_carry
 vname_list_encode_def cons0 sub_cons sub_operand_bit_to_var full_adder_def comm_encode.simps
   Let_def simp flip: char_nat_encode.simps)
  apply auto
  done

fun map_adder :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_adder v n = (if n =0 then 0 else (full_adder_nat (hd_nat n) v) ## map_adder v (tl_nat n))"

fun map_adder_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_adder_acc acc v n = (if n =0 then acc else map_adder_acc ((full_adder_tail (hd_nat n) v)##acc)
    v (tl_nat n)) "

lemma sub_map_adder:
  "map_adder v n = map_nat (\<lambda>i. full_adder_nat i v) n"
  apply (induct v n rule:map_adder.induct)
  apply (subst map_adder.simps)
  apply auto
  done

lemma map_adder_append:
"map_adder v (append_nat xs ys) = append_nat (map_adder v xs) (map_adder v ys)"
proof -
  obtain xs' ys' where "xs= list_encode xs'" "ys = list_encode ys'"
    by (metis list_decode_inverse)
  thus ?thesis apply (auto simp add:sub_append sub_map_adder sub_map simp del:map_adder.simps 
map_nat.simps) done
qed

lemma map_adder_induct: "
reverse_nat (map_adder v (append_nat xs ys)) = 
map_adder_acc (reverse_nat (map_adder v xs)) v ys
  "
  apply(induct ys arbitrary:xs rule:length_nat.induct)
   apply(auto simp add: append_nat_0 append_nat_Suc  simp del: map_adder.simps map_adder_acc.simps)
   apply simp
  apply(subst (2) map_adder_acc.simps)
  apply(auto simp add: map_adder_append 
          reverse_append_nat subtail_full_adder  simp del: map_adder.simps map_adder_acc.simps)
  apply(subst map_adder.simps)
 apply(auto simp add:cons_Nil simp del:list_encode.simps map_adder.simps map_adder_acc.simps)
  apply(auto simp add:cons0 sub_hd sub_tl 
              simp del:list_encode.simps map_adder.simps map_adder_acc.simps)
   apply(auto simp add: reverse_cons_nat 
              simp del: map_adder.simps map_adder_acc.simps)  
      apply(subst map_adder.simps)
    apply(auto simp add: reverse_nat_0 append_singleton_nat
              simp del: map_adder.simps map_adder_acc.simps)  
  done

definition map_adder_tail  where 
"map_adder_tail v n = reverse_nat (map_adder_acc 0 v n) "

lemma subtail_map_adder : 
"map_adder_tail v n = map_adder v n"
  using map_adder_induct[of v 0 n]  append_nat_0
  apply (auto simp add: map_adder_tail_def simp  del: map_adder.simps map_adder_acc.simps)
  using rev_rev_nat 
  by (metis map_adder.simps reverse_nat_0)


definition adder_nat:: "nat \<Rightarrow> nat  \<Rightarrow> nat" where
  "adder_nat n v =
    2 ## (com_list_to_seq_nat (map_adder v (list_less_nat n)))
      ## (1 ## (vname_encode ''carry'') ## 0 ## 0)
      ## 0"

definition adder_tail:: "nat \<Rightarrow> nat  \<Rightarrow> nat" where
  "adder_tail n v =
    2 ## (com_list_to_seq_tail (map_adder_tail v (list_less_tail n)))
      ## (1 ## (vname_encode ''carry'') ## 0 ## 0)
      ## 0"

lemma subtail_adder: "adder_tail n v = adder_nat n v" 
  by(auto simp only: adder_tail_def adder_nat_def subtail_com_list_to_seq subtail_map_adder
      subtail_list_less)


  
lemma sub_adder: "adder_nat n (vname_encode v) = comm_encode (adder n v)"
  apply (simp only: sub_map_adder adder_nat_def sub_list_less sub_map  cons0 sub_cons sub_com_list_to_seq
      adder_def comm_encode.simps bit_encode.simps sub_full_adder extract_lambda flip: map_map 
      comm_list_encode_def)
  done

definition binary_adder_nat:: "nat \<Rightarrow> nat \<Rightarrow>nat\<Rightarrow> nat \<Rightarrow> nat" where
"binary_adder_nat n v a b = 2##(
    copy_atom_to_operand_nat n (encode_char(CHR ''a'')) a)##(
2##( copy_atom_to_operand_nat n (encode_char(CHR ''b'')) b)##(
2##( adder_nat n v)##(
2##(copy_atom_to_operand_nat n (encode_char(CHR ''a'')) (prod_encode(1,0)))##(
  copy_atom_to_operand_nat n (encode_char(CHR ''b'')) (prod_encode(1,0)))##0 
)##0
)##0
)##0"

definition binary_adder_tail:: "nat \<Rightarrow> nat \<Rightarrow>nat\<Rightarrow> nat \<Rightarrow> nat" where
"binary_adder_tail n v a b = 2##(
    copy_atom_to_operand_tail n (encode_char(CHR ''a'')) a)##(
2##( copy_atom_to_operand_tail n (encode_char(CHR ''b'')) b)##(
2##( adder_tail n v)##(
2##(copy_atom_to_operand_tail n (encode_char(CHR ''a'')) (prod_encode(1,0)))##(
  copy_atom_to_operand_tail n (encode_char(CHR ''b'')) (prod_encode(1,0)))##0 
)##0
)##0
)##0"

lemma subtail_binary_adder:
"binary_adder_tail n v a b  = binary_adder_nat n v a b "
  apply(auto simp only: binary_adder_nat_def binary_adder_tail_def subtail_copy_atom_to_operand
        subtail_adder)
  done

lemma sub_binary_adder:
 "binary_adder_nat n (vname_encode v) (atomExp_encode a) (atomExp_encode b) =
    comm_encode (binary_adder n v a b)"
  apply (auto simp only:binary_adder_nat_def cons0 sub_cons binary_adder_def
         sub_copy_atom_to_operand  comm_encode.simps sub_adder simp flip: atomExp_encode.simps)
  done


definition assign_var_carry_sub_nat:: 
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"assign_var_carry_sub_nat i v a b c = 
2 ## (1 ## (var_bit_to_var_nat(prod_encode (v, i))) ##
(if b + c = 0 \<or> b + c = 2 then (if a = 1 then 1 else 0)
    else (if b + c = 1 \<and> a = 0 then 1 else 0))  ## 0 ) ## 
(1##(vname_encode ''carry'')## (if a < b + c then 1 else 0) ## 0) ## 0 "

definition assign_var_carry_sub_tail:: 
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"assign_var_carry_sub_tail i v a b c = 
2 ## (1 ## (var_bit_to_var_tail (prod_encode (v, i))) ##
(if b + c = 0 \<or> b + c = 2 then (if a = 1 then 1 else 0)
    else (if b + c = 1 \<and> a = 0 then 1 else 0))  ## 0 ) ## 
(1##(vname_encode ''carry'')## (if a < b + c then 1 else 0) ## 0) ## 0 "

lemma subtail_assign_var_carry_sub:
"assign_var_carry_sub_tail i v a b c = assign_var_carry_sub_nat i v a b c"
  apply(auto simp only: assign_var_carry_sub_tail_def assign_var_carry_sub_nat_def
          subtail_var_bit_to_var)
  done


lemma sub_assign_var_carry_sub: 
"assign_var_carry_sub_nat i (vname_encode v) a b c = comm_encode(assign_var_carry_sub i v a b c)"
  apply (auto simp only: assign_var_carry_sub_nat_def sub_var_bit_to_var cons0 sub_cons
    assign_var_carry_sub_def comm_encode.simps bit_encode.simps split:if_splits
 simp flip: vname_nat_encode.simps)
  done


definition full_subtractor_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"full_subtractor_nat i v  = (let assign = assign_var_carry_sub_nat i v; op_a = operand_bit_to_var_nat (prod_encode(encode_char(CHR ''a''), i));
  op_b = operand_bit_to_var_nat (prod_encode(encode_char (CHR ''b''), i)) in 
3##(op_a ## 0) ##(3##((vname_encode ''carry'') ## 0)## (3 ## (op_b ## 0) ## (assign 1 1 1) ## ( assign 1 1 0) ## 0)##(
                                                       (3 ## (op_b ## 0) ## (assign 1 0 1) ## ( assign 1 0 0) ## 0))##0)
               ##(3##((vname_encode ''carry'') ## 0)## (3 ## (op_b ## 0) ## (assign 0 1 1) ## ( assign 0 1 0) ## 0)##(
                                                       (3 ## (op_b ## 0) ## (assign 0 0 1) ## ( assign 0 0 0) ## 0))##0)
## 0
 )"

definition full_subtractor_tail:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"full_subtractor_tail i v  = (let assign = assign_var_carry_sub_tail i v; op_a = operand_bit_to_var_tail (prod_encode(encode_char(CHR ''a''), i));
  op_b = operand_bit_to_var_tail (prod_encode(encode_char (CHR ''b''), i)) in 
3##(op_a ## 0) ##(3##((vname_encode ''carry'') ## 0)## (3 ## (op_b ## 0) ## (assign 1 1 1) ## ( assign 1 1 0) ## 0)##(
                                                       (3 ## (op_b ## 0) ## (assign 1 0 1) ## ( assign 1 0 0) ## 0))##0)
               ##(3##((vname_encode ''carry'') ## 0)## (3 ## (op_b ## 0) ## (assign 0 1 1) ## ( assign 0 1 0) ## 0)##(
                                                       (3 ## (op_b ## 0) ## (assign 0 0 1) ## ( assign 0 0 0) ## 0))##0)
## 0
 )"

lemma subtail_full_subtractor:
"full_subtractor_tail i v = full_subtractor_nat i v"
  apply(auto simp only: full_subtractor_tail_def full_subtractor_nat_def
        subtail_assign_var_carry_sub subtail_operand_bit_to_var Let_def)
  done

    
lemma sub_full_subtractor: "full_subtractor_nat i (vname_encode v) = comm_encode (full_subtractor i v)"
  apply (auto simp only:full_subtractor_nat_def sub_assign_var_carry_sub
 vname_list_encode_def cons0 sub_cons sub_operand_bit_to_var full_subtractor_def comm_encode.simps
   Let_def simp flip: char_nat_encode.simps)
  apply auto
  done

definition underflow_handler_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"underflow_handler_nat n v = 3##((vname_encode ''carry'')## 0) ## (2##(1##(vname_encode ''carry'')##0##0)##(
binary_assign_constant_nat n v 0
)##0)## (0##0) ## 0"

definition underflow_handler_tail:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"underflow_handler_tail n v = 3##((vname_encode ''carry'')## 0) ## (2##(1##(vname_encode ''carry'')##0##0)##(
binary_assign_constant_tail n v 0
)##0)## (0##0) ## 0"

lemma subtail_underflow_handler:
"underflow_handler_tail n v = underflow_handler_nat n v"
  apply(auto simp only: underflow_handler_tail_def underflow_handler_nat_def
subtail_binary_assign_constant
) done

lemma sub_underflow_handler:
 "underflow_handler_nat n (vname_encode v) = comm_encode (underflow_handler n v) "
  apply (auto simp only:underflow_handler_nat_def cons0 sub_cons underflow_handler_def
      bit_encode.simps comm_encode.simps vname_list_encode_def sub_binary_assign_constant )
  apply auto
  done

fun map_full_subtractor :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_full_subtractor v n = (if n = 0 then 0 else (full_subtractor_nat(hd_nat n) v) ## map_full_subtractor v (tl_nat n))"


lemma submap_full_subtractor: 
  "map_full_subtractor v n = map_nat (\<lambda>i. full_subtractor_nat i v) n"
  apply (induct v n rule : map_full_subtractor.induct)
  apply (subst map_full_subtractor.simps)
  apply (auto)
  done

fun map_full_subtractor_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_full_subtractor_acc acc v n = (if n =0 then acc else map_full_subtractor_acc ((full_subtractor_tail (hd_nat n) v)##acc)
    v (tl_nat n)) "

lemma map_full_subtractor_append:
"map_full_subtractor v (append_nat xs ys) = append_nat (map_full_subtractor v xs) (map_full_subtractor v ys)"
proof -
  obtain xs' ys' where "xs= list_encode xs'" "ys = list_encode ys'"
    by (metis list_decode_inverse)
  thus ?thesis apply (auto simp add:sub_append submap_full_subtractor sub_map simp del:map_full_subtractor.simps 
map_nat.simps) done
qed

lemma map_full_subtractor_induct: "
reverse_nat (map_full_subtractor v (append_nat xs ys)) = 
map_full_subtractor_acc (reverse_nat (map_full_subtractor v xs)) v ys
  "
  apply(induct ys arbitrary:xs rule:length_nat.induct)
   apply(auto simp add: append_nat_0 append_nat_Suc  simp del: map_full_subtractor.simps map_full_subtractor_acc.simps)
   apply simp
  apply(subst (2) map_full_subtractor_acc.simps)
  apply(auto simp add: map_full_subtractor_append 
          reverse_append_nat subtail_full_subtractor  simp del: map_full_subtractor.simps map_full_subtractor_acc.simps)
  apply(subst map_full_subtractor.simps)
 apply(auto simp add:cons_Nil simp del:list_encode.simps map_full_subtractor.simps map_full_subtractor_acc.simps)
  apply(auto simp add:cons0 sub_hd sub_tl 
              simp del:list_encode.simps map_full_subtractor.simps map_full_subtractor_acc.simps)
   apply(auto simp add: reverse_cons_nat 
              simp del: map_full_subtractor.simps map_full_subtractor_acc.simps)  
      apply(subst map_full_subtractor.simps)
    apply(auto simp add: reverse_nat_0 append_singleton_nat
              simp del: map_adder.simps map_adder_acc.simps)  
  done

definition map_full_subtractor_tail  where 
"map_full_subtractor_tail v n = reverse_nat (map_full_subtractor_acc 0 v n) "

lemma subtail_map_full_subtractor : 
"map_full_subtractor_tail v n = map_full_subtractor v n"
  using map_full_subtractor_induct[of v 0 n]  append_nat_0
  apply (auto simp add: map_full_subtractor_tail_def simp  del: map_full_subtractor.simps map_full_subtractor_acc.simps)
  using rev_rev_nat 
  by (metis map_full_subtractor.simps reverse_nat_0)

definition subtract_handle_underflow_nat:: 
  "nat \<Rightarrow> nat \<Rightarrow> nat" where
"subtract_handle_underflow_nat n v = 2##
  (com_list_to_seq_nat (map_full_subtractor v (list_less_nat n)))## 
  (underflow_handler_nat n v) ## 0"

definition subtract_handle_underflow_tail:: 
  "nat \<Rightarrow> nat \<Rightarrow> nat" where
"subtract_handle_underflow_tail n v = 2##
  (com_list_to_seq_tail (map_full_subtractor_tail v (list_less_tail n)))## 
  (underflow_handler_tail n v) ## 0"

lemma subtail_subtract_handle_underflow:
" subtract_handle_underflow_tail n v =  subtract_handle_underflow_nat n v"
  apply( auto simp only: subtract_handle_underflow_tail_def 
          subtract_handle_underflow_nat_def 
          subtail_com_list_to_seq subtail_map_full_subtractor subtail_list_less 
            subtail_underflow_handler)
  done

lemma sub_subtract_underflow : 
"subtract_handle_underflow_nat n (vname_encode v) = comm_encode ( subtract_handle_underflow n v)"
  apply (auto simp only: submap_full_subtractor subtract_handle_underflow_nat_def cons0 sub_cons sub_com_list_to_seq sub_map
sub_list_less sub_full_subtractor extract_lambda sub_underflow_handler
 comm_encode.simps subtract_handle_underflow_def
    simp flip:map_map comm_list_encode_def)
  done



definition binary_subtractor_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>nat" where
"binary_subtractor_nat n v a b = 
2 ## (copy_atom_to_operand_nat n (encode_char(CHR ''a'')) a) ## (
2 ## (   copy_atom_to_operand_nat n (encode_char(CHR ''b'')) b) ## (
2 ## (subtract_handle_underflow_nat n v) ##(
2##(copy_atom_to_operand_nat n (encode_char(CHR ''a'')) (prod_encode(1,0)))##(
  copy_atom_to_operand_nat n (encode_char(CHR ''b'')) (prod_encode(1,0)))##0 
) ## 0
) ## 0
) ## 0"

definition binary_subtractor_tail:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>nat" where
"binary_subtractor_tail n v a b = 
2 ## (copy_atom_to_operand_tail n (encode_char(CHR ''a'')) a) ## (
2 ## (   copy_atom_to_operand_tail n (encode_char(CHR ''b'')) b) ## (
2 ## (subtract_handle_underflow_tail n v) ##(
2##(copy_atom_to_operand_tail n (encode_char(CHR ''a'')) (prod_encode(1,0)))##(
  copy_atom_to_operand_tail n (encode_char(CHR ''b'')) (prod_encode(1,0)))##0 
) ## 0
) ## 0
) ## 0"

lemma subtail_binary_subtractor: 
"binary_subtractor_tail n v a b = binary_subtractor_nat n v a b  "
  apply(auto simp only: binary_subtractor_tail_def binary_subtractor_nat_def
        subtail_copy_atom_to_operand subtail_subtract_handle_underflow)
  done

lemma sub_binary_subtractor:
"binary_subtractor_nat n (vname_encode v) (atomExp_encode a) (atomExp_encode b) =
    comm_encode (binary_subtractor n v a b)"
  apply (auto simp only:binary_subtractor_nat_def cons0 sub_cons binary_subtractor_def
         sub_copy_atom_to_operand  comm_encode.simps sub_adder sub_subtract_underflow
 simp flip: atomExp_encode.simps)
  done


definition binary_parity_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"binary_parity_nat n v a  = (if fst_nat a \<noteq> 0 then  binary_assign_constant_nat n v (snd_nat a mod 2)
else 2## (3 ## ((var_bit_to_var_nat(prod_encode(snd_nat a, 0))) ## 0) ## (binary_assign_constant_nat n v 1) 
 ##( binary_assign_constant_nat n v 0) ## 0)## (
2 ## (copy_atom_to_operand_nat n (encode_char (CHR ''a'')) a) ##
 (copy_atom_to_operand_nat n (encode_char (CHR ''a'')) (prod_encode(1,0))) ## 0
) ## 0 )"

definition binary_parity_tail:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"binary_parity_tail n v a  = (if fst_nat a \<noteq> 0 then  binary_assign_constant_tail n v (snd_nat a mod 2)
else 2## (3 ## ((var_bit_to_var_tail(prod_encode(snd_nat a, 0))) ## 0) ## (binary_assign_constant_tail n v 1) 
 ##( binary_assign_constant_tail n v 0) ## 0)## (
2 ## (copy_atom_to_operand_tail n (encode_char (CHR ''a'')) a) ##
 (copy_atom_to_operand_tail n (encode_char (CHR ''a'')) (prod_encode(1,0))) ## 0
) ## 0 )"


lemma subtail_binary_parity:
"binary_parity_tail n v a = binary_parity_nat n v a"
  apply(auto simp only: binary_parity_tail_def binary_parity_nat_def
              subtail_var_bit_to_var subtail_binary_assign_constant
               subtail_copy_atom_to_operand)
  done

lemma sub_binary_parity:
 "binary_parity_nat n (vname_encode v) (atomExp_encode a) = comm_encode(binary_parity n v a) "
  apply (auto simp only: binary_parity_nat_def cons0 sub_cons sub_binary_assign_constant)
  apply (cases a)
    apply (auto simp add: sub_fst sub_snd )[1]
  apply (auto simp only: sub_var_bit_to_var  sub_fst sub_snd snd_def fst_def
 atomExp_encode.simps binary_parity.simps comm_encode.simps sub_copy_atom_to_operand
 simp flip: vname_nat_encode.simps )
  apply (auto simp only: sub_copy_atom_to_operand 
        vname_list_encode_def simp flip:atomExp_encode.simps)
  apply auto
  done


fun assign_shifted_bits_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"assign_shifted_bits_nat i v = (if i = 0 then 0##0 else
2##( 
3##((operand_bit_to_var_nat(prod_encode (encode_char(CHR ''a''), i)))##0)##(
1## (var_bit_to_var_nat (prod_encode(v, i-1)))## 1 ##0)##(
1## (var_bit_to_var_nat (prod_encode(v, i-1)))## 0 ##0
)##0)## (
assign_shifted_bits_nat (i-1) v
)##0
)" 

fun assign_shifted_bits_acc:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"assign_shifted_bits_acc acc diff i v = (if diff  = 0 then acc else assign_shifted_bits_acc (
2##( 
3##((operand_bit_to_var_tail (prod_encode (encode_char(CHR ''a''), i-diff +1 )))##0)##(
1## (var_bit_to_var_tail (prod_encode(v, i-diff)))## 1 ##0)##(
1## (var_bit_to_var_tail (prod_encode(v, i-diff)))## 0 ##0
)##0)## (
acc
)##0) (diff-1) i v
)"

lemma assign_shifted_bits_induct:
"diff \<le> i \<Longrightarrow>assign_shifted_bits_acc (assign_shifted_bits_nat (i-diff) v) diff i v = 
assign_shifted_bits_nat i v"
  apply(induct diff)
   apply simp
  apply(subst assign_shifted_bits_acc.simps)
  apply(auto simp add: subtail_operand_bit_to_var 
subtail_var_bit_to_var
simp del: assign_shifted_bits_acc.simps assign_shifted_bits_nat.simps operand_bit_to_var_nat.simps)
  apply(subst (asm) assign_shifted_bits_nat.simps)
 apply(auto simp add:
simp del: assign_shifted_bits_acc.simps assign_shifted_bits_nat.simps operand_bit_to_var_nat.simps)
  using Suc_diff_Suc Suc_le_lessD apply presburger
  done

definition assign_shifted_bits_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"assign_shifted_bits_tail i v = assign_shifted_bits_acc (0##0) i i v"

lemma subtail_assign_shifted_bits:
"assign_shifted_bits_tail i v =assign_shifted_bits_nat i v "
  apply(auto simp only: assign_shifted_bits_tail_def)
  using assign_shifted_bits_induct[of i i v]
  apply auto
  done

lemma sub_assign_shifted_bits:
"assign_shifted_bits_nat i (vname_encode v) = comm_encode (assign_shifted_bits i v)"
  apply (induct i)
   apply (subst assign_shifted_bits_nat.simps)
   apply  (simp only: cons0 comm_encode.simps assign_shifted_bits.simps)[1]
   apply  simp
    apply (subst assign_shifted_bits_nat.simps)
  apply (auto simp only: cons0 sub_cons comm_encode.simps assign_shifted_bits.simps
  sub_var_bit_to_var sub_operand_bit_to_var vname_list_encode_def
      simp flip: vname_nat_encode.simps char_nat_encode.simps )
  apply auto
  done


definition assign_shifted_bits_and_zero_most_significant_nat:: 
  "nat \<Rightarrow> nat \<Rightarrow> nat" where
"assign_shifted_bits_and_zero_most_significant_nat n v = 2 ## (assign_shifted_bits_nat (n - 1) v)##
  (1 ## (var_bit_to_var_nat (prod_encode(v, n - 1)))##0##0) ## 0"

definition assign_shifted_bits_and_zero_most_significant_tail:: 
  "nat \<Rightarrow> nat \<Rightarrow> nat" where
"assign_shifted_bits_and_zero_most_significant_tail n v = 2 ## (assign_shifted_bits_tail (n - 1) v)##
  (1 ## (var_bit_to_var_tail (prod_encode(v, n - 1)))##0##0) ## 0"

lemma subtail_assign_shifted_bits_and_zero_most_significant:
" assign_shifted_bits_and_zero_most_significant_tail n v =  assign_shifted_bits_and_zero_most_significant_nat n v "
  apply(auto simp only:  assign_shifted_bits_and_zero_most_significant_nat_def 
 assign_shifted_bits_and_zero_most_significant_tail_def
  subtail_var_bit_to_var subtail_assign_shifted_bits)
  done

lemma sub_assign_shifted_bits_and_zero_most_significant:
" assign_shifted_bits_and_zero_most_significant_nat n (vname_encode v) =
  comm_encode (assign_shifted_bits_and_zero_most_significant n v)"
  apply (auto simp only: assign_shifted_bits_and_zero_most_significant_nat_def 
       cons0 sub_cons sub_var_bit_to_var sub_assign_shifted_bits comm_encode.simps
  assign_shifted_bits_and_zero_most_significant_def bit_encode.simps
 simp flip: vname_nat_encode.simps )
  done


definition binary_right_shift_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"binary_right_shift_nat n v a = 2 ## (2 ## (copy_atom_to_operand_nat n (encode_char(CHR ''a'')) a) ##
(assign_shifted_bits_and_zero_most_significant_nat n v) ## 0) ##
    (copy_atom_to_operand_nat n (encode_char(CHR ''a'')) (prod_encode(1,0))) ## 0" 

definition binary_right_shift_tail:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"binary_right_shift_tail n v a = 2 ## (2 ## (copy_atom_to_operand_tail n (encode_char(CHR ''a'')) a) ##
(assign_shifted_bits_and_zero_most_significant_tail n v) ## 0) ##
    (copy_atom_to_operand_tail n (encode_char(CHR ''a'')) (prod_encode(1,0))) ## 0" 

lemma subtail_binary_right_shift:
"binary_right_shift_tail n v a = binary_right_shift_nat n v a"
  apply(auto simp only: binary_right_shift_tail_def  binary_right_shift_nat_def
   subtail_copy_atom_to_operand subtail_assign_shifted_bits_and_zero_most_significant
  )done

lemma sub_binary_right_shift:
  "binary_right_shift_nat n (vname_encode v) (atomExp_encode a) = comm_encode (binary_right_shift n v a)"
  apply (auto simp only: binary_right_shift_nat_def cons0 sub_cons sub_copy_atom_to_operand
 sub_assign_shifted_bits_and_zero_most_significant comm_encode.simps
binary_right_shift_def
 simp flip: atomExp_encode.simps)
  done


definition assignment_to_binary_nat:: "nat \<Rightarrow> nat \<Rightarrow>nat \<Rightarrow> nat" where
"assignment_to_binary_nat n v aexp = (if hd_nat aexp =0 then 
   binary_adder_nat n v (nth_nat (Suc 0) aexp) (prod_encode (1,0))
else if hd_nat aexp = 1 then binary_adder_nat n v (nth_nat (Suc 0) aexp) (nth_nat (Suc (Suc 0)) aexp)
else if hd_nat aexp = 2 then binary_subtractor_nat n v (nth_nat (Suc 0) aexp) (nth_nat (Suc (Suc 0)) aexp)
else if hd_nat aexp = 3 then binary_parity_nat n v (nth_nat (Suc 0) aexp)
else  binary_right_shift_nat n v (nth_nat (Suc 0) aexp)
)"

definition assignment_to_binary_tail:: "nat \<Rightarrow> nat \<Rightarrow>nat \<Rightarrow> nat" where
"assignment_to_binary_tail n v aexp = (if hd_nat aexp =0 then 
   binary_adder_tail n v (nth_nat (Suc 0) aexp) (prod_encode (1,0))
else if hd_nat aexp = 1 then binary_adder_tail n v (nth_nat (Suc 0) aexp) (nth_nat (Suc (Suc 0)) aexp)
else if hd_nat aexp = 2 then binary_subtractor_tail n v (nth_nat (Suc 0) aexp) (nth_nat (Suc (Suc 0)) aexp)
else if hd_nat aexp = 3 then binary_parity_tail n v (nth_nat (Suc 0) aexp)
else  binary_right_shift_tail n v (nth_nat (Suc 0) aexp)
)"

lemma subtail_assignment_to_binary :
 "assignment_to_binary_tail n v aexp = assignment_to_binary_nat n v aexp"
  apply(auto simp only: assignment_to_binary_tail_def assignment_to_binary_nat_def
    subtail_binary_adder subtail_binary_subtractor subtail_binary_right_shift subtail_binary_parity
) done

lemma sub_assignment_to_binary:
"assignment_to_binary_nat n (vname_encode v) (aexp_encode aexp) = 
  comm_encode (assignment_to_binary n v aexp)"
  apply (cases aexp)
      apply (auto simp only: assignment_to_binary_nat_def aexp_encode.simps sub_hd head.simps 
                  sub_binary_adder sub_binary_subtractor sub_binary_parity 
                  sub_nth nth.simps
        assignment_to_binary_def sub_binary_right_shift
 simp flip: atomExp_encode.simps )
      apply auto
  done


end