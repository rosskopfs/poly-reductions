
theory IMP_Minus_Nat_Bijection_Time 
  imports IMP_Minus_Nat_Bijection Multiplication_Time
    "HOL-Library.Rewrite"
begin

(* Probably useless accumulator laws *)
lemma triangle_imp_time_acc': "triangle_imp_time t s = triangle_imp_time 0 s + t"
  by (induction t) (use triangle_imp_time_acc in auto)
(* This should prevent endless unfolding *)
lemma triangle_imp_time_acc'': "NO_MATCH 0 t \<Longrightarrow> triangle_imp_time t s = triangle_imp_time 0 s + t"
  using triangle_imp_time_acc' .

definition triangle_imp_time' :: "nat \<Rightarrow> nat" where
  "triangle_imp_time' a = 10 + mul_imp_time' (a+1)"

lemma triangle_imp_time_triangle_imp_time': "triangle_imp_time t s = triangle_imp_time' (triangle_a s) + t"
  by (subst triangle_imp_time.simps) (simp add: triangle_imp_time'_def mul_imp_time_mul_imp_time')

(* Problem: Suc a in argument *)
lemma triangle_imp_time'_non_rec: "triangle_imp_time' a = 22 + 10 * Discrete.log (Suc a)"
  by (simp del: mul_imp_time'.simps add: mul_imp_time'_non_rec triangle_imp_time'_def)

lemma dlog_Suc_bound: "Discrete.log (Suc a) \<le> Suc (Discrete.log a)"
  by (metis Discrete.log_le_iff Suc_le_eq log_exp log_exp2_gt power_Suc)

lemma triangle_imp_time'_non_rec_bound: "triangle_imp_time' a \<le> 32 + 10 * (Discrete.log a)"
proof-
  have "22 + 10 * Discrete.log (Suc a) \<le> 22 + 10 * Suc (Discrete.log a)"
    using dlog_Suc_bound by (meson add_left_mono mult_le_mono2)
  thus ?thesis 
    by (subst triangle_imp_time'_non_rec) simp 
qed
 
lemma "triangle_imp_time' \<in> O(Discrete.log)"
  apply (subst triangle_imp_time'_non_rec)
  apply auto
  apply (rule bigoI[of _ 100])
  apply auto
  apply (rule eventually_sequentiallyI[of 1000])
  by (smt (z3) Multiseries_Expansion.intyness_simps(1) Suc_0_to_numeral divmod_numeral_simps(15)
      dlog_Suc_bound le_SucE le_add2 log_rec numeral_2_eq_2 numeral_le_iff of_nat_1 of_nat_mono 
      order.trans plus_1_eq_Suc trans_le_add1)

definition prod_encode_imp_time' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "prod_encode_imp_time' a b = 8 + triangle_imp_time' (a+b)"

lemma prod_encode_imp_time_prod_encode_imp_time': "prod_encode_imp_time t s 
  = prod_encode_imp_time' (prod_encode_a s) (prod_encode_b s) + t"
  by (subst prod_encode_imp_time.simps) (simp add: prod_encode_imp_time'_def triangle_imp_time_triangle_imp_time')

lemma dlog_add_bound': "a+b > 0 \<Longrightarrow> Discrete.log (a+b) \<le> Discrete.log a + Discrete.log b + 1"
  apply (induction "a+b" arbitrary: a b rule: log_induct)
   apply auto
  using log_Suc_zero apply auto[1]
  by (metis Discrete.log_le_iff add_Suc_right add_Suc_shift add_cancel_right_left add_le_mono1 
      log_twice mult_2 nat_add_left_cancel_le nat_le_linear trans_le_add1 trans_le_add2)

lemma dlog_add_bound: "Discrete.log (a+b) \<le> Suc (Discrete.log a + Discrete.log b)"
  by (metis Suc_eq_plus1 dlog_add_bound' le_SucI le_add2 not_gr0 trans_less_add2)

(* The question is whether I bound this in each step or at the end *)
lemma prod_encode_imp_time'_non_rec: "prod_encode_imp_time' a b = 30 + 10 * Discrete.log (Suc (a + b))"
  by (auto simp add: prod_encode_imp_time'_def triangle_imp_time'_non_rec)

(* Bound at the end *)
lemma "prod_encode_imp_time' a b \<le> 50 + 10 * Discrete.log a + 10 * Discrete.log b"
proof-
  have "prod_encode_imp_time' a b = 30 + 10 * Discrete.log (Suc (a + b))"
    by (simp add: prod_encode_imp_time'_non_rec)
  also have "\<dots> \<le> 30 + 10 * Suc (Discrete.log (a + b))"
    by (meson add_left_mono dlog_Suc_bound mult_le_mono2)
  also have "\<dots> \<le> 30 + 10 * Suc (Discrete.log a + Discrete.log b + 1)"
    by (metis add.commute add_le_cancel_right dlog_add_bound mult_le_mono2 plus_1_eq_Suc)
  also have "\<dots> = 50 + 10 * Discrete.log a + 10 * Discrete.log b"
    by auto
  finally show ?thesis .
qed

(* Bound every step, should scale better in the long run *)
lemma "prod_encode_imp_time' a b \<le> 50 + 10 * Discrete.log a + 10 * Discrete.log b"
proof-
  have "prod_encode_imp_time' a b = 8 + triangle_imp_time' (a+b)"
    unfolding prod_encode_imp_time'_def ..
  also have "\<dots> \<le> 40 + 10 * (Discrete.log (a+b))"
    using triangle_imp_time'_non_rec_bound by simp
  also have "\<dots> \<le> 40 + 10 * Suc (Discrete.log a + Discrete.log b)"
    using dlog_add_bound by (meson add_left_mono mult_le_mono2)
  also have "\<dots> = 50 + 10 * Discrete.log a + 10 * Discrete.log b"
    by simp
  finally show ?thesis .
qed

(* Probably useless accumulator laws *)
lemma prod_decode_aux_imp_time_acc': "prod_decode_aux_imp_time t s = prod_decode_aux_imp_time 0 s + t"
  by (induction t) (use prod_decode_aux_imp_time_acc in auto)
(* This should prevent endless unfolding *)
lemma prod_decode_aux_imp_time_acc'': "NO_MATCH 0 t \<Longrightarrow> prod_decode_aux_imp_time t s = prod_decode_aux_imp_time 0 s + t"
  using prod_decode_aux_imp_time_acc' .

function prod_decode_aux_imp_time' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "m > k \<Longrightarrow> prod_decode_aux_imp_time' m k = 7 + prod_decode_aux_imp_time' (m - Suc k) (Suc k)"
| "m \<le> k \<Longrightarrow> prod_decode_aux_imp_time' m k = 4"
  using leI by fastforce+
termination by lexicographic_order (* by (relation "Wellfounded.measure (\<lambda>(m,k). m)") auto *)

lemma prod_decode_aux_imp_time_prod_decode_aux_imp_time':
  "prod_decode_aux_imp_time t s = prod_decode_aux_imp_time' (prod_decode_aux_m s) (prod_decode_aux_k s) + t"
proof (induction "prod_decode_aux_m s" "prod_decode_aux_k s" arbitrary: t s rule: prod_decode_aux_imp_time'.induct)
  case 1
  then show ?case 
    using 1 by (subst prod_decode_aux_imp_time.simps) (simp add: prod_decode_aux_state_upd_def prod_decode_aux_imp_time_acc)
next
  case 2
  then show ?case
    by (auto simp add: prod_decode_aux_imp_time.simps)
qed

function count_rec_calls :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "m > k \<Longrightarrow> count_rec_calls m k = Suc (count_rec_calls (m - Suc k) (Suc k))"
| "m \<le> k \<Longrightarrow> count_rec_calls m k = 0"
  using leI by fastforce+
termination by lexicographic_order

lemma "prod_decode_aux_imp_time' m k = 7*count_rec_calls m k + 4"
  by (induction m k rule: prod_decode_aux_imp_time'.induct) auto

fun count_rec_calls' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "count_rec_calls' m k = (if m>k then Suc (count_rec_calls' (m - Suc k) (Suc k)) else 0)"

lemma [code]: "count_rec_calls m k = count_rec_calls' m k"
  by (induction m k rule: prod_decode_aux_imp_time'.induct) auto

value "map (\<lambda>m . count_rec_calls (nat m) 0) [0..70]"
value "map (\<lambda>m . count_rec_calls (nat m) 1) [0..70]"
value "map (\<lambda>m . count_rec_calls (nat m) 2) [0..70]"
value "map (\<lambda>m . count_rec_calls (nat m) 3) [0..70]"

lemma "(\<lambda>n . (ln n)) \<in> o(\<lambda>n . sqrt n)"
  by real_asymp


fun count_rec_calls'' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "count_rec_calls'' m k i = (if m>(k+i) then Suc (count_rec_calls'' (m - Suc k - i) k (i+1)) else 0)"


lemma "count_rec_calls' m k \<le> (if m div 2 \<le> k then 1 else (Discrete.sqrt (8*m+1)))"
proof (induction m k rule: count_rec_calls'.induct)
  case (1 m k)
  then show ?case 
  proof(cases " m div 2 \<le> k")
    case True
    then show ?thesis by auto
  next
    case False
    then show ?thesis
      
  qed
qed
  
  
  oops
(* Test *)
value "(\<lambda>m k . (sqrt (8*m+1) - 1 - 2*k) div 2 ) 2 1"

lemma "count_rec_calls' m k = (Discrete.sqrt (8*m+1) - 1 - 2*k) div 2"
  oops
lemma "count_rec_calls m 1 = (sqrt (8*m+1) - 2) div 2"
  oops

lemma "count_rec_calls m 1 = (sqrt (8*m+1) - 3) div 2"
  nitpick


(* Now I need to "solve for count_rec_calls" *)
(* In each step I substract (k+1) and increase k by 1 *)
value "m - i * k - triangle i \<le> k+i" (* i for number of recursive calls *)
value "Discrete.sqrt 32"

(* 5 1 \<rightarrow> 3 2 \<rightarrow> 0 3 *)
value "count_rec_calls 6 0"
(* 6 0 \<rightarrow> 5 1 \<rightarrow> 0 3 *)


value "count_rec_calls 7 0"
(* 7 0 \<rightarrow> 6 1 \<rightarrow> 4 2 \<rightarrow> 1 3 *)

value "count_rec_calls 13 2"
(* 13 2 \<rightarrow> 10 3 \<rightarrow> 6 4 \<rightarrow> 1 5 *)


value "count_rec_calls 8 3"
(* 8 3 \<rightarrow> 4 4 \<rightarrow> 0 5 *)

definition "test m k = (count_rec_calls m k, (Discrete.sqrt(k*k + 2*k + 1 + 4*m) - k - 1) div 2, 
  let i = count_rec_calls m k in m - i*k - i*(i+1))"

value "test 2 0"
value "test 2 1" (* Wrong *)

value "test 3 0" (* Wrong *)
value "test 3 1"
value "test 3 2" (* Wrong *)

value "test 8 
0" (* Wrong *)
value "test 8 1" 
value "test 8 2" (* Wrong *)
value "test 8 3"
value "test 8 5"
value "test 8 6"
value "test 8 7" (* Wrong *)
(* 8 0 \<rightarrow> 7 1 \<rightarrow> 5 2 \<rightarrow> 3 3 *)


value "(\<lambda>(m,k) . (m,k,count_rec_calls' m k)) ` Set.filter (\<lambda>(m,k) . m>k) {(nat m, nat k) | m k . m\<in>{1,2,3,4,5} \<and> k \<in> {1,2,3,4,5}}"

value "m - i*k - i*(i+1) = 0"
value "m = i*k + i^2 + i"
value "m = i*(k+1) + i^2"
value "0 = i^2 + i*(k+1) - m"

lemma [code]: "prod_decode_aux_imp_time' m k = prod_decode_aux_imp_time 0 \<lparr>prod_decode_aux_k = k, prod_decode_aux_m = m\<rparr>"
  by (simp add: prod_decode_aux_imp_time_prod_decode_aux_imp_time')

value "count_rec_calls' 1 0" value "Discrete.sqrt(0*0 + 2*0 + 1 + 4*3) div 2 +1" 
lemma "count_rec_calls' m k \<le> (Discrete.sqrt(k*k + 2*k + 1 + 4*m) - k - 1) div 2" 



lemma "count_rec_calls' m k = (if k = 0 \<and> m \<noteq> 0 then 1 else 0) + (Discrete.sqrt(k*k + 2*k + 1 + 4*m) - k - 1) div 2"

value "prod_decode_aux"

end