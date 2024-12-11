theory Binary_Arithmetic_Nat
  imports Binary_Arithmetic  Primitives
begin


fun nth_bit_of_num_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"nth_bit_of_num_nat x n  = (if x = 0 then
                              (if n = 0 then
                                 1 \<comment> \<open>x = 0 \<and> n = 0\<close>
                               else
                                 0 \<comment> \<open>x = 0 \<and> n \<noteq> 0\<close>)
                            else
                              if n = 0 then
                                (if hd_nat x = 0 then
                                   0 \<comment> \<open>x \<noteq> 0 \<and> n = 0 \<and> hd_nat x = 0\<close>
                                 else
                                   1 \<comment> \<open>x \<noteq> 0 \<and> n = 0 \<and> hd_nat x \<noteq> 0\<close>)
                              else
                                nth_bit_of_num_nat (tl_nat x) (n-1))"

definition nth_bit_of_num_tail ::"nat \<Rightarrow> nat \<Rightarrow> nat" where
"nth_bit_of_num_tail x n =  nth_bit_of_num_nat x n"

lemma subtail_nth_bit_of_num :"nth_bit_of_num_tail x n =  nth_bit_of_num_nat x n"
  using nth_bit_of_num_tail_def by simp

lemma sub_nth_bit_of_num: "nth_bit_of_num_nat (num_encode x) n = bit_encode (nth_bit_of_num x n)"
     apply (subst nth_bit_of_num_nat.simps)
  apply (induct x n rule:nth_bit_of_num.induct)
       apply (simp_all (no_asm_simp)  only:sub_hd sub_tl num_encode_def
       num_to_list.simps nth_bit_of_num.simps list_encode.simps tail.simps head.simps list_encode_eq
   del: nth_bit_of_num_nat.simps   flip:list_encode.simps )
     apply (simp_all only: flip: nth_bit_of_num_nat.simps num_encode_def)
   apply auto
  done

lemma dom_nth_bit_nat:"nth_bit_nat a n = 0 \<or> nth_bit_nat a n = Suc 0"
  apply (induction n arbitrary: a)
   apply auto
  done

lemma sub_nth_bit : "nth_bit_nat a n = bit_encode (nth_bit a n)"
  apply (cases "nth_bit_nat a n")
  apply (auto simp add: nth_bit_def )
   using  dom_nth_bit_nat
   by (metis Suc_inject old.nat.distinct(2))



fun nth_carry_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"nth_carry_nat n a b = (if n = 0 then (if (nth_bit_nat a 0 = 1 \<and> nth_bit_nat b 0 = 1) then 1 else 0)
 else (if (nth_bit_nat a n = 1 \<and> nth_bit_nat b n = 1)
  \<or> ((nth_bit_nat a n = 1 \<or> nth_bit_nat b n = 1) \<and> nth_carry_nat (n-1) a b = 1)
  then 1 else 0) )"

fun nth_carry_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>nat" where
"nth_carry_acc acc diff n a b = (if diff = 0 then acc else
if diff>n then (if (nth_bit_tail a 0 = 1 \<and> nth_bit_tail b 0 = 1) then nth_carry_acc 1 n n a b
   else  nth_carry_acc 0 n n a b )
else (if (nth_bit_tail a (n-diff+1) = 1 \<and> nth_bit_tail b (n-diff+1) = 1)
  \<or> ((nth_bit_tail a (n-diff+1) = 1 \<or> nth_bit_tail b (n-diff+1) = 1) \<and> (acc = 1))
  then nth_carry_acc 1 (diff-1) n a b else nth_carry_acc 0 (diff-1) n a b))"

lemma nth_carry_step:"diff < n \<Longrightarrow> nth_carry_acc (nth_carry_nat (n- Suc diff) a b ) (Suc diff) n a b
=  nth_carry_acc (nth_carry_nat (n-diff) a b) diff n a b "
  apply (subst (1) nth_carry_acc.simps )
  apply (auto simp add: Suc_diff_Suc subtail_nth_bit
            simp del: nth_carry_acc.simps nth_bit_nat.simps nth_carry_nat.simps simp flip: One_nat_def)
  apply (auto  simp add: subtail_nth_bit)
  done


lemma nth_carry_induct:"diff \<le>n \<Longrightarrow> nth_carry_acc (nth_carry_nat (n-diff) a b) diff n a b
= nth_carry_nat n a b"
  apply (induct diff)
  apply simp
   apply (auto simp add: nth_carry_step simp del:nth_carry_acc.simps nth_carry_nat.simps )
  done

lemma nth_carry_base:"nth_carry_nat 0 a b = (if (nth_bit_nat a 0 = 1 \<and> nth_bit_nat b 0 = 1)
            then 1 else 0)"
  apply auto
  done

definition nth_carry_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"nth_carry_tail n a b = nth_carry_acc 0 (Suc n) n a b"

lemma subtail_nth_carry:
"nth_carry_tail n a b
= nth_carry_nat n a b"
  apply (auto simp only: nth_carry_tail_def)
  apply (subst nth_carry_acc.simps)
  using nth_carry_induct[of n n a b] nth_carry_base subtail_nth_bit
   apply (auto simp add:  simp del:nth_carry_acc.simps nth_carry_nat.simps nth_bit_nat.simps )
  done

lemma sub_nth_carry: "nth_carry_nat n a b = bit_encode (nth_carry n a b)"
  apply (induct n)
  apply (auto simp add: sub_nth_bit)
  done



fun nth_carry_sub_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"nth_carry_sub_nat n a b = (if n =0
    then (if (nth_bit_nat a 0 = 0 \<and> nth_bit_nat b 0 = 1)
            then 1 else 0)
    else (if (nth_bit_nat a n = 0 \<and> ( nth_bit_nat b n = 1 \<or> nth_carry_sub_nat (n-1) a b = 1))
                \<or> (nth_bit_nat a n = 1 \<and> (nth_bit_nat b n) = 1 \<and> nth_carry_sub_nat (n-1) a b = 1)
           then 1
            else 0))"

fun nth_carry_sub_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"nth_carry_sub_acc acc diff n a b = (if diff = 0 then acc else
(if diff > n
    then (if (nth_bit_tail a 0 = 0 \<and> nth_bit_tail b 0 = 1)
            then nth_carry_sub_acc 1 n n a b  else nth_carry_sub_acc 0 n n a b)
    else (if (nth_bit_tail a (n-diff+1) = 0 \<and> ( nth_bit_tail b (n-diff+1) = 1 \<or> acc = 1))
                \<or> (nth_bit_tail a (n-diff+1) = 1 \<and> (nth_bit_tail b (n-diff+1) ) = 1 \<and> acc = 1)
           then  nth_carry_sub_acc 1 (diff -1) n a b
            else nth_carry_sub_acc 0 (diff - 1) n a b))
)  "


lemma nth_carry_sub_step:"diff < n \<Longrightarrow> nth_carry_sub_acc (nth_carry_sub_nat (n- Suc diff) a b ) (Suc diff) n a b
=  nth_carry_sub_acc (nth_carry_sub_nat (n-diff) a b) diff n a b "
  apply (subst (1) nth_carry_sub_acc.simps )
  apply (subst (1) nth_carry_sub_nat.simps)
  apply (auto simp add: Suc_diff_Suc subtail_nth_bit
            simp del: nth_carry_sub_acc.simps nth_bit_nat.simps nth_carry_sub_nat.simps simp flip: One_nat_def)
  apply (metis One_nat_def  nth_carry_sub_nat.elims)
  apply auto
  done
lemma nth_carry_sub_induct:"diff \<le>n \<Longrightarrow> nth_carry_sub_acc (nth_carry_sub_nat (n-diff) a b) diff n a b
= nth_carry_sub_nat n a b"
  apply (induct diff)
  apply simp
   apply (auto simp add: nth_carry_sub_step simp del:nth_carry_sub_acc.simps nth_carry_sub_nat.simps )
  done
lemma nth_carry_sub_base:"nth_carry_sub_nat 0 a b = (if (nth_bit_nat a 0 = 0 \<and> nth_bit_nat b 0 = 1)
            then 1 else 0)"
  apply auto
  done

definition nth_carry_sub_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"nth_carry_sub_tail n a b = nth_carry_sub_acc 0 (Suc n) n a b"

lemma subtail_nth_carry_sub:
"nth_carry_sub_tail n a b
= nth_carry_sub_nat n a b"
  apply (auto simp only: nth_carry_sub_tail_def)
  apply (subst nth_carry_sub_acc.simps)
  using nth_carry_sub_induct[of n n a b] nth_carry_sub_base subtail_nth_bit
   apply (auto simp add:  simp del:nth_carry_sub_acc.simps nth_carry_sub_nat.simps nth_bit_nat.simps )
  done

fun bit_list_to_nat_nat:: "nat \<Rightarrow> nat" where
"bit_list_to_nat_nat n = (if n =0 then 0 else if hd_nat n =0 then 2 *bit_list_to_nat_nat (tl_nat n)
   else  2*bit_list_to_nat_nat (tl_nat n) + 1)"

lemma sub_bit_list_to_nat: "bit_list_to_nat_nat (list_encode (map bit_encode x)) = bit_list_to_nat x"
  apply (induct x)
   apply (simp)
  apply (subst bit_list_to_nat_nat.simps)
  apply (auto simp only: sub_hd sub_tl sub_tail_map tl_def
          sub_head_map bit_list_to_nat.simps split:bit.splits)
   apply (auto)
  done
fun bit_list_to_nat_acc:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"bit_list_to_nat_acc acc n = (if n =0 then acc else if hd_nat n =0 then bit_list_to_nat_acc (2*acc) (tl_nat n)
   else  bit_list_to_nat_acc (2*acc +1) (tl_nat n))"



lemma bit_list_to_nat_induct: "bit_list_to_nat_nat (append_nat (reverse_nat ys) xs) = bit_list_to_nat_acc (bit_list_to_nat_nat xs) ys"
  apply(induct ys arbitrary:xs rule: length_nat.induct)
  apply (auto simp only: reverse_nat_0 append_nat.simps)
  apply(subst bit_list_to_nat_acc.simps)
   apply(auto simp del: bit_list_to_nat_nat.simps bit_list_to_nat_acc.simps
          simp add: append_rev_nat )
  apply(subst(2) bit_list_to_nat_acc.simps)
     apply(auto simp del: bit_list_to_nat_nat.simps bit_list_to_nat_acc.simps cons_def
          simp add: append_rev_nat )
     apply(subst bit_list_to_nat_nat.simps)
          apply(auto simp del:   bit_list_to_nat_nat.simps bit_list_to_nat_acc.simps cons_def
          simp add: append_cons_nat_0 cons_Nil tl_cons hd_cons)
  apply(subst bit_list_to_nat_nat.simps)
 apply(auto simp del:   bit_list_to_nat_nat.simps bit_list_to_nat_acc.simps cons_def
          simp add: append_cons_nat_0 cons_Nil tl_cons hd_cons)
  done


lemma bit_list_to_nat_inverse:
"bit_list_to_nat_nat (append_nat ys xs) = bit_list_to_nat_acc (bit_list_to_nat_nat xs) (reverse_nat ys)"
  using rev_rev_nat bit_list_to_nat_induct by metis

definition bit_list_to_nat_tail :: "nat \<Rightarrow> nat" where
"bit_list_to_nat_tail ys =  bit_list_to_nat_acc 0 (reverse_nat ys)"

lemma subtail_bit_list_to_nat:
" bit_list_to_nat_tail ys = bit_list_to_nat_nat ys"
  using bit_list_to_nat_inverse [of ys 0] append_nat_0
  by (auto simp add: bit_list_to_nat_tail_def)


fun bit_length_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bit_length_acc acc n = (if n < 2 then acc else bit_length_acc (acc + 1) (n div 2))"

lemma bit_length_induct: "bit_length_acc acc n = floor_log n + acc"
  apply(induct n arbitrary: acc rule: less_induct)
  apply(subst floor_log.simps)
  apply(simp only: HOL.if_distrib)
  by simp

definition bit_length_tail :: "nat \<Rightarrow> nat" where
  "bit_length_tail n = bit_length_acc 1 n"

lemma subtail_bit_length: "bit_length_tail n = bit_length n"
  unfolding bit_length_def bit_length_tail_def
  using bit_length_induct[of 1 n] by simp

end