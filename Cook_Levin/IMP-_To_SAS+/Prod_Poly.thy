
(* 
This theory is not used currently. I fear this is also the missing polynomial triangular root.
As this was implemented again now in Primitives, I suggest deprecating this file. 

*)

theory Prod_Poly
  imports "HOL-Library.Nat_Bijection" "Recursion-Theory-I.CPair"
begin 
(* 

Commented out to avoid errors in proofs

fun mult_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"mult_acc acc c  b  = (if b = 0 then acc else if b mod 2 = 0 then
 mult_acc acc (c*2) (b div 2) else mult_acc (acc+c) (c*2) (b div 2)
 )"


lemma mult_acc_correct:"mult_acc acc c b = acc + c*b"
  apply(induct acc c b  rule:mult_acc.induct)
  apply auto
  by (metis 
One_nat_def mod_mult_div_eq mult.assoc 
mult_Suc_right plus_1_eq_Suc)

definition mult:: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"mult a b = mult_acc 0 a b"

lemma mult_correct: "mult a b = a * b"
  using mult_def mult_acc_correct by auto

definition triangle' :: "nat \<Rightarrow> nat" where 
"triangle' n = mult n (Suc n) div 2"

lemma sub_triangle : "triangle' n = triangle n"
  using triangle_def triangle'_def mult_correct by auto

definition pair :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"pair a b = triangle' (a+b) + a"

lemma sub_pair:"pair a b = prod_encode (a,b)"
  using pair_def  sub_triangle 
  by (simp add: prod_encode_def)

lemma triangle_sf:"triangle x = sf x " 
  by (simp add: sf_def triangle_def) 

lemma  "prod_encode(a,b) = c_pair a b"
  by (auto simp add:  c_pair_def prod_encode_def triangle_sf) 

lemma prod_c_pair: "prod_decode n = (c_fst n , c_snd n)"
  by (metis (no_types) c_fst_le_c_sum c_snd_def prod_decode_aux.simps prod_encode_inverse 
prod_encode_prod_decode_aux sf_c_sum_plus_c_fst triangle_sf)

function find_triangle_search :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"find_triangle_search  a b n = (let m = ((a+b) div 2); t = triangle' m  in 
if b\<le>a  then a else if n-t \<le> m then find_triangle_search a m n else find_triangle_search (m+1) b n
)"
  by pat_completeness auto
termination by (relation "measure (\<lambda>(a,b,n).b-a)") (auto simp add: sub_triangle)

lemma mean_in_the_interval:"\<not> b \<le> a \<Longrightarrow> ((a::nat) + b ) div 2 \<ge> a \<and> b \<ge> Suc ((a::nat) + b ) div 2 "
  by auto
lemma "\<not> b \<le> a \<Longrightarrow> b = Suc ((a + b) div 2) \<Longrightarrow> b = a \<or> b = Suc a \<or> b = Suc(Suc a)"
  apply auto
  done

lemma find_triangle_search_inv:"\<lbrakk> a \<le> c_sum n ; c_sum n \<le> b\<rbrakk> \<Longrightarrow> find_triangle_search a b n = c_sum n "
  apply(induct a b n rule:find_triangle_search.induct)
  apply(subst find_triangle_search.simps)
  apply (auto simp add: Let_def sub_triangle triangle_sf simp del: find_triangle_search.simps c_sum_def)
   apply(subst find_triangle_search.simps)
   apply (auto simp add:   Let_def sub_triangle triangle_sf simp del: find_triangle_search.simps c_sum_def)
proof  (goal_cases)
  case (1 a b n)
  have "a = (a + b) div 2" using mean_in_the_interval 1(6) 1(8) by auto
  hence "b = Suc a" using 1(6) by force
  thus ?case using 1
    by (smt le_add_diff_inverse le_trans nat_less_le not_less sf_aux2 sf_c_sum_le_arg sf_mono)   
next
  case (2 a b n)
  then have "c_sum n \<le> (a+b) div 2 " 
    by (metis arg_less_sf_imp_c_sum_less_arg 
le_add_diff_inverse not_less order_less_imp_le sf_aux2)
  moreover have "find_triangle_search a ((a + b) div 2) n = find_triangle_search a ((a + (a + b) div 2) div 2) n"
    using 2 apply(subst find_triangle_search.simps)
    by (auto simp add: Let_def sub_triangle triangle_sf simp del: find_triangle_search.simps)
  ultimately show  ?case using 2(1) by auto 
next
  case (3 a b n)
 have "a = (a + b) div 2" using mean_in_the_interval 3(6) 3(8) by auto
  hence "b = Suc a" using 3(6) by force
  thus ?case using 3
    by (smt le_add_diff_inverse le_trans nat_less_le not_less sf_aux2 sf_c_sum_le_arg sf_mono) 
next
  case (4 a b n)
   then have "c_sum n \<le> (a+b) div 2 " 
    by (metis arg_less_sf_imp_c_sum_less_arg 
le_add_diff_inverse not_less order_less_imp_le sf_aux2)
  moreover have "find_triangle_search a ((a + b) div 2) n = find_triangle_search (Suc ((a + (a + b) div 2) div 2)) ((a + b) div 2) n"
    using 4 apply(subst find_triangle_search.simps)
    by (auto simp add: Let_def sub_triangle triangle_sf simp del: find_triangle_search.simps)
  ultimately show  ?case using 4(1) by auto 
next
  case (5 a b n)
  then show ?case 
    apply(subst find_triangle_search.simps)
    apply (auto simp add:   Let_def sub_triangle triangle_sf simp del: find_triangle_search.simps c_sum_def)
  proof (goal_cases)
case 1
  have "b = Suc ((a + b) div 2)" using mean_in_the_interval 1(6) 1(8) by auto
  moreover then have  " b = a \<or> b = Suc a \<or> b = Suc(Suc a)" using 1(6)  by auto
  ultimately show ?case using 1
    by (smt add_diff_cancel_left' c_sum_is_sum le_SucE le_add1 le_add_same_cancel1 linorder_not_less
 nat_less_le sf_aux2 sf_c_sum_plus_c_fst zero_less_diff)
next
  case 2
   then have " Suc ((a + b) div 2) \<le> c_sum n"
     by (smt Suc_leI add_diff_cancel_left' c_sum_is_sum le_add1 le_add_same_cancel1 le_trans
 linorder_not_less nat_less_le sf_aux2 sf_c_sum_plus_c_fst zero_less_diff) 
  moreover have "find_triangle_search (Suc ((a + b) div 2)) b n  = find_triangle_search (Suc ((a + b) div 2)) (Suc ((a + b) div 2 + b) div 2) n"
    using 2 apply(subst find_triangle_search.simps)
    by (auto simp add: Let_def sub_triangle triangle_sf simp del: find_triangle_search.simps)
  ultimately show  ?case using 2(2) by auto 
next
  case 3
  have "b = Suc ((a + b) div 2)" using mean_in_the_interval 3(6) 3(8) by auto
  moreover then have  " b = a \<or> b = Suc a \<or> b = Suc(Suc a)" using 3(6)  by auto
  ultimately show ?case using 3
    by (smt add_diff_cancel_left' c_sum_is_sum le_SucE le_add1 le_add_same_cancel1 linorder_not_less
 nat_less_le sf_aux2 sf_c_sum_plus_c_fst zero_less_diff)
next
  case 4
   then have " Suc ((a + b) div 2) \<le> c_sum n"
     by (smt Suc_leI add_diff_cancel_left' c_sum_is_sum le_add1 le_add_same_cancel1 le_trans
 linorder_not_less nat_less_le sf_aux2 sf_c_sum_plus_c_fst zero_less_diff) 
  moreover have "find_triangle_search (Suc ((a + b) div 2)) b n = find_triangle_search (Suc (Suc ((a + b) div 2 + b) div 2)) b n"
    using 4 apply(subst find_triangle_search.simps)
    by (auto simp add: Let_def sub_triangle triangle_sf simp del: find_triangle_search.simps)
  ultimately show  ?case using 4(2) by auto 
qed

qed

definition find_triangle :: "nat \<Rightarrow> nat" where 
"find_triangle n = find_triangle_search 0 n n"

lemma sub_find_triangle: "find_triangle n = c_sum n"
  apply(auto simp add: find_triangle_def  simp del: find_triangle_search.simps)
  using find_triangle_search_inv[of 0 n n]
  using c_sum_le_arg by blast

definition fst_nat' :: "nat \<Rightarrow> nat" where 
"fst_nat' n = n - triangle' (find_triangle n)"

lemma fst_nat'_correct:"fst_nat' n = c_fst n"
  by(auto simp add: fst_nat'_def c_fst_def sub_triangle triangle_sf sub_find_triangle)

lemma sub_fst':
"fst_nat' n  = fst (prod_decode n)"
  using prod_c_pair fst_nat'_correct by simp

definition snd_nat' :: "nat \<Rightarrow> nat" where 
"snd_nat' n = find_triangle n - fst_nat' n"

lemma snd_nat'_correct:"snd_nat' n = c_snd n"
  by(auto simp add: snd_nat'_def c_snd_def sub_triangle triangle_sf sub_find_triangle fst_nat'_correct)

lemma sub_snd':
"snd_nat' n  = snd (prod_decode n)"
  using prod_c_pair snd_nat'_correct  by simp
 *)
end