
theory Primitives_IMP_Minus_Time
  imports Primitives_IMP_Minus "Poly_Reductions_Lib.Landau_Auxiliaries"
    "HOL-Library.Rewrite" "HOL-Library.Sublist"
begin

subsubsection \<open>Multiplication\<close>

(* Accumulator in one step, not sure if necessary *)
lemma mul_imp_time_acc': "mul_imp_time t s = mul_imp_time 0 s + t"
  by (induction t) (use mul_imp_time_acc in auto)
(* Experiment, this should stop endless unfolding problems *)
corollary mul_imp_time_acc'': "NO_MATCH 0 t \<Longrightarrow> mul_imp_time t s = mul_imp_time 0 s + t"
  using mul_imp_time_acc'.

(* Experiments with simp rules, delete: *)
lemma no_match_simp: "NO_MATCH p v \<Longrightarrow> P \<Longrightarrow> P"
  by simp
lemmas mul_imp_time_simp = no_match_simp[OF _ mul_imp_time.simps, where p="mul_imp_time t (mul_state_upd s)" for s t]

(* Proving was getting ugly, so drop the accumulator *)
fun mul_imp_time' :: "nat \<Rightarrow> nat" where
  "mul_imp_time' 0 = 2"
| "mul_imp_time' n = mul_imp_time' (n div 2) + 10"

(* Equivalence of simpler version  *)
lemma mul_imp_time_mul_imp_time': "mul_imp_time t s = mul_imp_time' (mul_b s) + t"
proof (induction "mul_b s" arbitrary: s t rule: mul_imp_time'.induct)
  case 1
  then show ?case 
    by (subst mul_imp_time.simps) auto
next
  case 2
  show ?case
    by (subst mul_imp_time.simps) (auto simp add: 2(1) 2(2)[symmetric] mul_state_upd_def mul_imp_time_acc)
qed

(* Extract non recursive version *)
lemma mul_imp_time'_non_rec: "mul_imp_time' b = (if b = 0 then 0 else 10 * (1 + Discrete.log b)) + 2"
proof (induction b rule: mul_imp_time'.induct)
  case 1
  then show ?case
    by simp
next
  case (2 b)
  then show ?case
  proof(cases b)
    case 0
    then show ?thesis 
      using 2 by auto
  next
    case (Suc n)
    then show ?thesis
      using 2 by (auto simp add: log_rec)
  qed
qed 

(* Move back to mul_imp_time *)
lemma mul_imp_time_non_rec: "mul_imp_time t s = (if mul_b s = 0 then 0 else 10 * (1 + Discrete.log (mul_b s))) + 2 + t"
proof-
  have "mul_imp_time t s = mul_imp_time' (mul_b s) + t"
    by (simp add: mul_imp_time_mul_imp_time')
  also have "\<dots> = (if (mul_b s) = 0 then 0 else 10 * (1 + Discrete.log (mul_b s))) + 2 + t"
    by (simp add: mul_imp_time'_non_rec)
  finally show ?thesis
    by simp
qed

(* Hide details maybe?*)
lemma mul_imp_time_non_rec_bound: "mul_imp_time t s \<le> 10 * Discrete.log (mul_b s) + 12 + t"
  using mul_imp_time_non_rec by auto


(* Experiment, might it be suitable to just use manuel's akra-bazzi setup? *)

(* Timing function in a form the tool wants*)
function mul_imp_time'' :: "nat \<Rightarrow> real" where
  "mul_imp_time'' 0 = 2"
| "mul_imp_time'' (Suc 0) = 12"
| "n>1 \<Longrightarrow> mul_imp_time'' n = mul_imp_time'' (nat \<lfloor>real n / 2\<rfloor>) + 10"
  by force auto
termination by akra_bazzi_termination simp_all

lemma mul_imp_time''_cost_pos[simp]: "mul_imp_time'' n \<ge> 0"
  by (induction n rule: mul_imp_time''.induct) auto

lemma mul_imp_time''_mul_imp_time: "mul_imp_time'' (mul_b s) + t = mul_imp_time t s"
proof(induction "mul_b s" arbitrary: s t rule: mul_imp_time''.induct)
  case 1
  then show ?case 
    by (subst mul_imp_time.simps) simp
next thm mul_imp_time''.simps(2)
  case 2
  show ?case 
    by (subst mul_imp_time.simps, subst mul_imp_time.simps) (auto simp add: 2[symmetric] mul_state_upd_def Let_def)
next
  case (3 s)
  show ?case
    apply (subst mul_imp_time''.simps(3)[OF 3(1)])
    apply (subst mul_imp_time.simps)

    using 3 apply (auto simp add: mul_state_upd_def) 
    (* This looks like just represenatation trouble *)
    by (smt (verit, best) Multiseries_Expansion.intyness_1
        One_nat_def Suc_0_to_numeral floor_divide_of_nat_eq landau_product_preprocess(33) landau_product_preprocess(35)
        mul_state.select_convs(2) nat_int of_nat_Suc of_nat_numeral)+
qed

(* Now we get the runtime "for free" *)
lemma runtime_pre: "mul_imp_time'' \<in> \<Theta>(\<lambda>n. ln n)"
  by master_theorem simp_all

lemma runtime_master: "mul_imp_time'' \<in> O(Discrete.log)"
  using runtime_pre dlog_\<Theta>_ln by blast

(* Connect to the regular derivation *)
lemma mul_imp_time''_mul_imp_time': "mul_imp_time'' b = mul_imp_time' b"
  using mul_imp_time''_mul_imp_time mul_imp_time_mul_imp_time'
  by (metis add.right_neutral add_left_cancel mul_state.select_convs(2) of_nat_add)

(* I can now also use the infrastructure from there to show my desired result *)
(* constants used without thinking a thought *)
lemma runtime_bound': "mul_imp_time' \<in> O(Discrete.log)"
  apply (subst mul_imp_time'_non_rec)
  apply auto
  apply (rule bigoI[of _ 100])
  apply auto
  apply (rule eventually_sequentiallyI[of 1000])
  apply auto
  using log_rec numeral_2_eq_2 by auto

corollary runtime_bound'': "mul_imp_time' \<in> O(ln)"
  using dlog_in_\<Theta>ln landau_o.big.bigtheta_trans1 runtime_bound' by blast

corollary runtime_bound''': "mul_imp_time' \<in> O(ln)"
  using dlog_in_\<Theta>ln landau_o.big.bigtheta_trans1 runtime_bound' by blast


subsubsection \<open>Triangle\<close>

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


subsubsection \<open>Encoding pairs\<close>

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

subsubsection \<open>Decoding pairs\<close>

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
(*
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

value "map (triangle o nat) [0..10]"

value "map (\<lambda>m . count_rec_calls (nat m) 0) [0..70]"
value "map (\<lambda>m . count_rec_calls (nat m) 1) [0..70]"
value "map (\<lambda>m . count_rec_calls (nat m) 2) [0..70]"
value "map (\<lambda>m . count_rec_calls (nat m) 3) [0..70]"
*)
lemma triangle_Sum: "triangle n = (\<Sum>x\<in>{1..n}. x)"
  by (induction n) (auto simp add: triangle_def)

lemma "triangle n * 2 = (n*(n+1))"
  unfolding triangle_def by simp
(* I need to do this on the reals... UGH *)
lemma "triangle n = (n^2 + n) div 2"
  unfolding triangle_def by (simp add: power2_eq_square)


lemma triangle_polynomial: "triangle n = nat (floor (n^2 / 2 + n / 2))"
  unfolding triangle_def apply (auto simp add: power2_eq_square algebra_simps)
  by (metis Multiseries_Expansion.intyness_simps(1, 2) 
      add_divide_distrib floor_divide_of_nat_eq nat_int of_nat_numeral)



subsubsection \<open>Squaring\<close>

record square_state = square_x :: nat square_square :: nat

abbreviation "square_prefix \<equiv> ''square.''"
abbreviation "square_x_str \<equiv> ''x''"
abbreviation "square_square_str \<equiv> ''square''"

definition "square_state_upd s \<equiv> 
  let
    mul_a' = square_x s;
    mul_b' = square_x s;
    mul_c' = 0;
    (square_mul_state::mul_state) = \<lparr>mul_a = mul_a', mul_b = mul_b', mul_c = mul_c'\<rparr>;
    mul_ret = (mul_imp square_mul_state);
    square_square' = mul_c mul_ret;
    ret = \<lparr>square_x = square_x s, square_square = square_square'\<rparr>
  in
    ret
"

fun square_imp :: "square_state \<Rightarrow> square_state" where
  "square_imp s = (let
     ret = square_state_upd s
   in
     ret
  )"

declare square_imp.simps[simp del]

lemma square_imp_correct: "square_square (square_imp s) = (square_x s)^2"
  by (induction s rule: square_imp.induct)
    (auto simp: square_imp.simps square_state_upd_def Let_def mul_imp_correct power2_eq_square split: if_splits)

fun square_imp_time :: "nat \<Rightarrow> square_state \<Rightarrow> nat" where
  "square_imp_time t s = (let
     mul_a' = square_x s;
     t = t + 2;
     mul_b' = square_x s;
     t = t + 2;
     mul_c' = 0;
     t = t + 2;
     (square_mul_state::mul_state) = \<lparr>mul_a = mul_a', mul_b = mul_b', mul_c = mul_c'\<rparr>;
     mul_ret = (mul_imp square_mul_state);
     t = t + mul_imp_time 0 square_mul_state;
     square_square = mul_c mul_ret;
     t = t + 2;
     ret = t
   in
     ret
  )"

declare square_imp_time.simps[simp del]

lemma square_imp_time_acc: "(square_imp_time (Suc t) s) = Suc (square_imp_time t s)"
  by (induction t s rule: square_imp_time.induct) 
    (auto simp add: square_imp_time.simps Let_def split: if_splits)

definition square_IMP_Minus where
"square_IMP_Minus \<equiv>
  (
   \<comment> \<open>mul_a' = square_x s;\<close>
   (mul_prefix @ mul_a_str) ::= A (V square_x_str);;
   \<comment> \<open>mul_b' = (square_x s);\<close>
   (mul_prefix @ mul_b_str) ::= A (V square_x_str);;
   \<comment> \<open>mul_c' = 0;\<close>
   (mul_prefix @  mul_c_str) ::= (A (N 0)) ;;
   \<comment> \<open>(mul_state::mul_state) = \<lparr>mul_a = mul_a, mul_b = mul_b, mul_c = 0\<rparr>;\<close>
   \<comment> \<open>mul_ret = (mul_imp mul_state);\<close>
   invoke_subprogram mul_prefix mul_IMP_minus;;
  square_square_str ::= A (V (mul_prefix @ mul_c_str))
  )"

definition "square_imp_to_HOL_state p s =
  \<lparr>square_x = s (add_prefix p square_x_str), square_square = s (add_prefix p square_square_str)\<rparr>"

lemma square_imp_to_HOL_state_add_prefix: 
  "square_imp_to_HOL_state (add_prefix p1 p2) s = square_imp_to_HOL_state p2 (s o (add_prefix p1))"
  by (auto simp only: square_imp_to_HOL_state_def append.assoc[symmetric] comp_def)

(* But why the vars? Do they add anything? *)
lemma square_IMP_Minus_correct_function: 
  "(invoke_subprogram p square_IMP_Minus, s) 
      \<Rightarrow>\<^bsup>t \<^esup> s'
    \<Longrightarrow> s' (add_prefix p square_square_str) = square_square (square_imp (square_imp_to_HOL_state p s))"
  apply(simp only: square_IMP_Minus_def square_imp.simps com_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  \<comment> \<open>Variables that we want to preserve: variables of this program minus the variables of the
     program we call. If automation fails, this should be manually chosen variables.\<close>
  apply(erule mul_IMP_minus_correct[where vars = "{p @ ''square''}"]) (* Seems useless *)
  apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: square_state_upd_def Let_def square_imp_to_HOL_state_def)[1]
  apply(auto simp: mul_imp_to_HOL_state_def)[1]
  done

lemma square_IMP_Minus_correct_time: 
  "(invoke_subprogram p square_IMP_Minus, s) 
      \<Rightarrow>\<^bsup>t\<^esup> s'
    \<Longrightarrow> t = square_imp_time 0 (square_imp_to_HOL_state p s)"
  apply(simp only: square_IMP_Minus_def com_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
   apply(drule AssignD)+
   apply(elim conjE)
   apply(subst square_imp_time.simps)
  apply(erule mul_IMP_minus_correct[where vars = "{p @ square_square_str}"])
  \<comment> \<open>Warning: in the following, I am unfolding mul_imp_to_HOL_state_def. With more experiments, it
      should become clear if this will cascade down multiple layers\<close>
  apply(simp add: square_imp_time_acc square_imp_to_HOL_state_def square_state_upd_def)[1]
  apply (auto simp: mul_imp_to_HOL_state_def)[1]
  done


lemma square_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ square_pref) square_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>  v \<in> vars \<Longrightarrow> \<not> (prefix square_pref v) 
  \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars 
  by (metis prefix_def)

lemma square_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) square_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (square_imp_time 0 (square_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) square_square_str) = 
        square_square (square_imp (square_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using square_IMP_Minus_correct_time square_IMP_Minus_correct_function
        square_IMP_Minus_correct_effects 
  by auto

definition square_imp_time' :: "nat \<Rightarrow> nat" where
  "square_imp_time' a = 8 + mul_imp_time' a"

lemma square_imp_time_square_imp_time': "square_imp_time t s = square_imp_time' (square_x s) + t"
  by (subst square_imp_time.simps) (simp add: square_imp_time'_def mul_imp_time_mul_imp_time')

lemma square_imp_time'_non_rec: "square_imp_time' a = (if a = 0 then 0 else 10 * (1 + Discrete.log a)) + 10"
  by (simp del: mul_imp_time'.simps add: mul_imp_time'_non_rec square_imp_time'_def)

lemma square_imp_time'_non_rec_bound: "square_imp_time' a \<le> 20 + 10 * (Discrete.log a)"
proof-
  have "22 + 10 * Discrete.log (Suc a) \<le> 22 + 10 * Suc (Discrete.log a)"
    using dlog_Suc_bound by (meson add_left_mono mult_le_mono2)
  thus ?thesis 
    by (subst square_imp_time'_non_rec) simp 
qed

lemma square_imp_time'_alt_def: "square_imp_time' a = 8 + mul_imp_time'' a"
  using mul_imp_time''_mul_imp_time' square_imp_time'_def by simp



lemma square_imp_time'_in_\<Theta>_mul_imp_time'': "square_imp_time' \<in> \<Theta>(mul_imp_time'')"
  unfolding square_imp_time'_alt_def 
  apply (rule bigthetaI)
   apply (rule bigoI[of _ 100])
   apply (rule eventually_sequentiallyI[of 1000])
   apply auto
  apply (rule landau_omega.bigI[of "1/100"])
  by auto


lemma square_imp_time'_in_\<Theta>_ln': "square_imp_time' \<in> \<Theta>(ln)"
  using landau_theta.bigtheta_trans2 runtime_pre square_imp_time'_in_\<Theta>_mul_imp_time'' by blast


(* This allows bounding *)
lemma mono_mul_imp_time'_pre: "m \<le> n \<Longrightarrow> mul_imp_time' m \<le> mul_imp_time' n"
  by (auto simp add: Discrete.log_le_iff mul_imp_time'_non_rec)
corollary mono_mul_imp_time': "mono mul_imp_time'"
  using mono_mul_imp_time'_pre ..

lemma mono_square_imp_time'_pre: "m \<le> n \<Longrightarrow> square_imp_time' m \<le> square_imp_time' n"
  by (auto simp add: mono_mul_imp_time'_pre square_imp_time'_def)
corollary mono_square_imp_time': "mono square_imp_time'"
  using mono_square_imp_time'_pre ..

subsubsection \<open>Square root\<close>

text\<open>First a recursive version of square root using bisection\<close>

(* Internal 'loop' for the algorithm, takes lower and upper bound for root, returns root *)
function dsqrt' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "dsqrt' y L R = (if Suc L < R then let M = (L+R) div 2 in if M*M \<le> y then dsqrt' y M R else dsqrt' y L M else L)"
  by auto
termination by (relation "Wellfounded.measure (\<lambda>(y,L,R). R - L)") auto

declare dsqrt'.simps[simp del]

lemma dsqrt'_simps[simp]:
  "Suc L < R \<Longrightarrow> ((L+R) div 2)^2 \<le> y \<Longrightarrow> dsqrt' y L R = dsqrt' y ((L+R) div 2) R"
  "Suc L < R \<Longrightarrow> ((L+R) div 2)^2 > y \<Longrightarrow> dsqrt' y L R = dsqrt' y L ((L+R) div 2)"
  "Suc L \<ge> R \<Longrightarrow> dsqrt' y L R = L"
  by (simp_all add: dsqrt'.simps power2_eq_square Let_def)

definition dsqrt :: "nat \<Rightarrow> nat" where
  "dsqrt y = dsqrt' y 0 (Suc y)"

(* I am still not sure if there is a better way to state multiple simultaneous goals for induction*)
lemma dsqrt'_correct': 
  "(0::nat) \<le> L \<Longrightarrow> L < R \<Longrightarrow> L\<^sup>2 \<le> y \<Longrightarrow> y < R\<^sup>2 \<Longrightarrow> (dsqrt' y L R)\<^sup>2 \<le> y \<and> y < (Suc (dsqrt' y L R))\<^sup>2"
proof (induction y L R rule: dsqrt'.induct)
  case (1 y L R)
  then show ?case
  proof(cases "Suc L < R")
    case True
    then show ?thesis
      (*Real proof needed*)
      by (smt (verit, ccfv_threshold) "1.IH"(1) "1.IH"(2) "1.prems"(3) "1.prems"(4) dsqrt'_simps(1) 
          dsqrt'_simps(2) le_sqrt_iff less_eq_nat.simps(1) linorder_not_le order_trans power2_eq_square)
  next
    case False 
    hence "Suc L = R"
      using 1 by linarith
    then show ?thesis
      using "1.prems" False by fastforce
  qed
qed

(* This is what I would like *)
lemma dsqrt'_correct'': 
  assumes "(0::nat) \<le> L" "L < R" "L\<^sup>2 \<le> y" "y < R\<^sup>2" 
  shows "(dsqrt' y L R)\<^sup>2 \<le> y" "y < (Suc (dsqrt' y L R))\<^sup>2"
  using assms dsqrt'_correct' by blast+

lemma dsqrt_correct': 
  "(dsqrt y)\<^sup>2 \<le> y" "y < (Suc (dsqrt y))\<^sup>2"
  unfolding dsqrt_def by (all \<open>rule dsqrt'_correct''\<close>) (simp_all add: power2_eq_square)

corollary dsqrt_correct: "dsqrt y = Discrete.sqrt y"
  by (intro sqrt_unique[symmetric] dsqrt_correct')

(* Translating into "IMP-adjacent form" *)

(* I could probably get rid of the M *)
record dsqrt'_state = dsqrt'_state_y :: nat dsqrt'_state_L :: nat dsqrt'_state_R :: nat

value triangle_state_upd
definition "dsqrt'_imp_state_upd s = (let
    M = dsqrt'_state_L s + dsqrt'_state_R s;
    M = M div 2;
    
    square_x' = M;
    square_square' = 0; \<comment> \<open>Is this necessary? If yes, does it make sense to introduce a concept of input/output vars?\<close>
    (dsqrt'_square_state::square_state) = \<lparr>square_x = square_x', square_square = square_square'\<rparr>;
    square_ret = square_imp dsqrt'_square_state;
    M2 = square_square square_ret;
    
    \<comment> \<open>Canonical way to do general (i.e. not just one assignment) branching?\<close>
    cond = M2 - dsqrt'_state_y s;
    L = if cond \<noteq> 0 then dsqrt'_state_L s else M;
    R = if cond \<noteq> 0 then M else dsqrt'_state_R s;

    ret = \<lparr>dsqrt'_state_y = dsqrt'_state_y s, dsqrt'_state_L = L, dsqrt'_state_R = R\<rparr>
  in
    ret)
"
     
function dsqrt'_imp :: "dsqrt'_state \<Rightarrow> dsqrt'_state" where
  "dsqrt'_imp s = 
  (if dsqrt'_state_R s - (dsqrt'_state_L s + 1) \<noteq> 0 then \<comment> \<open>While L+1 < R\<close>
    (
      let
        next_iteration = dsqrt'_imp (dsqrt'_imp_state_upd s)
      in
        next_iteration
    )
  else
    (
      let
        ret = s
      in
        ret
    )
  )"
  by pat_completeness auto
termination (* Same termination proof as recursive version, just some additional decoration *)
  by (relation "Wellfounded.measure (\<lambda>s. dsqrt'_state_R s - dsqrt'_state_L s)") 
    (auto simp: dsqrt'_imp_state_upd_def Let_def split: if_splits)

declare dsqrt'_imp.simps[simp del]

lemma dsqrt'_imp_correct: "dsqrt'_state_L (dsqrt'_imp s) = dsqrt' (dsqrt'_state_y s) (dsqrt'_state_L s) (dsqrt'_state_R s)"
proof (induction s rule: dsqrt'_imp.induct)
  case (1 s)
  then show ?case
    apply(subst dsqrt'_imp.simps)
    apply (auto simp: dsqrt'_imp_state_upd_def Let_def power2_eq_square square_imp_correct split: if_splits) (* Slow, very slow, do better*)
    done
qed

function dsqrt'_imp_time :: "nat \<Rightarrow> dsqrt'_state \<Rightarrow> nat" where
  "dsqrt'_imp_time t s = 
  (if dsqrt'_state_R s - (dsqrt'_state_L s + 1) \<noteq> 0 then \<comment> \<open>While L+1 < R\<close>
    (
      let
        t = t + 5; \<comment> \<open>To account for while loop condition checking and difference computation\<close>
         \<comment> \<open>Computation of M\<close>
        M = dsqrt'_state_L s + dsqrt'_state_R s;
        t = t + 2;
        M = M div 2;
        t = t + 2;
        
        square_x' = M;
        t = t + 2;
        square_square' = 0; \<comment> \<open>Is this necessary? If yes, does it make sense to introduce a concept of input/output vars?\<close>
        t = t + 2;
        (dsqrt'_square_state::square_state) = \<lparr>square_x = square_x', square_square = square_square'\<rparr>;
        square_ret = square_imp dsqrt'_square_state;
        t = t + square_imp_time 0 dsqrt'_square_state;
        M2 = square_square square_ret;
        t = t + 2;
        
        \<comment> \<open>Canonical way to do general (i.e. not just one assignment) branching?\<close>
        cond = M2 - dsqrt'_state_y s;
        t = t + 2;
        L = if cond \<noteq> 0 then dsqrt'_state_L s else M;
        t = t + 3;
        R = if cond \<noteq> 0 then M else dsqrt'_state_R s;
        t = t + 3;

        next_iteration = dsqrt'_imp_time t (dsqrt'_imp_state_upd s)
      in
        next_iteration
    )
  else
    (
      let
        t = t + 7;
        ret = t
      in
        ret
    )
  )"
  by pat_completeness auto
termination (* Same termination proof as recursive version, just some additional decoration *)
  by (relation "Wellfounded.measure (\<lambda>(t,s). dsqrt'_state_R s - dsqrt'_state_L s)") 
    (auto simp: dsqrt'_imp_state_upd_def Let_def split: if_splits)

declare dsqrt'_imp_time.simps[simp del]

lemma dsqrt'_imp_time_acc: "(dsqrt'_imp_time (Suc t) s) = Suc (dsqrt'_imp_time t s)"
proof (induction t s arbitrary: rule: dsqrt'_imp_time.induct)
  case (1 t s)
  then show ?case
  proof(cases "dsqrt'_state_R s - (dsqrt'_state_L s + 1) \<noteq> 0")
    case True
    hence "(Suc (dsqrt'_state_L s)) < dsqrt'_state_R s"
      by simp
    with True show ?thesis
      apply (subst (2) dsqrt'_imp_time.simps)
      apply (subst dsqrt'_imp_time.simps)
      using 1 by (simp add: dsqrt'_imp_state_upd_def Let_def split: if_splits)
  next
    case False
    then show ?thesis 
      by (auto simp add: dsqrt'_imp_time.simps split: if_splits)
  qed
qed

function count_rec_calls :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "count_rec_calls y L R = (if Suc L < R 
    then let M = (L+R) div 2 in Suc (if M*M \<le> y then count_rec_calls y M R else count_rec_calls y L M)
    else 0)"
  by auto
termination by (relation "Wellfounded.measure (\<lambda>(y,L,R). R - L)") auto

declare count_rec_calls.simps[simp del]  

function dsqrt'_imp_time' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "dsqrt'_imp_time' y L R = (if Suc L < R 
    then let M = (L+R) div 2 in 23 + square_imp_time' M + (if M*M \<le> y then dsqrt'_imp_time' y M R else dsqrt'_imp_time' y L M)
    else 7)"
  by auto
termination by (relation "Wellfounded.measure (\<lambda>(y,L,R). R - L)") auto

declare dsqrt'_imp_time'.simps[simp del]

(* Bound function suitable for manuel's stuff *)
function dsqrt'_imp_time_master :: "nat \<Rightarrow> real" where
  "dsqrt'_imp_time_master 0 = 7"
| "dsqrt'_imp_time_master (Suc 0) = 7"
| "D\<ge>2 \<Longrightarrow> dsqrt'_imp_time_master D = dsqrt'_imp_time_master (nat (ceiling (D / 2))) + 23 + square_imp_time' (nat (ceiling D))"
  by force+
termination apply (relation "Wellfounded.measure (\<lambda>D. D)") by auto linarith

(* If I knew how the landau stuff worked, should be doable *)
lemma "dsqrt'_imp_time_master \<in> \<Theta>(\<lambda>n . (ln (real n))^2)"
  apply master_theorem
     apply auto
  using less_2_cases_iff apply fastforce
  apply (rule bigthetaI)
  subgoal
    apply (rule landau_o.bigI[of 100])
     apply auto
    apply (rule eventually_sequentiallyI[of 1000])
    apply auto
  using square_imp_time'_in_\<Theta>_ln'  
  oops

(* More importantly: How to bound it *)
lemma "L < R \<Longrightarrow> dsqrt'_imp_time' y L R \<le> dsqrt'_imp_time_master (R-L)"
proof (induction  y L R rule: count_rec_calls.induct)
  case (1 y L R)
  then show ?case 
  proof(cases "Suc L < R")
    case rec: True

  
    from rec have "(R - L) > 1"
      by simp
    hence size: "(R - L) div 2 > 0"
      by simp

   
    have mid_bound: "(L + R) div 2 < R" 
      using local.rec by linarith
    
    from rec have "(R - L) > 1"
      by simp
    hence size: "(R - L) div 2 > 0"
      by simp

    show ?thesis
    proof(cases "((L + R) div 2)^2 \<le> y")
      case True
      hence s: "dsqrt'_imp_time' y L R \<le> 23 + square_imp_time' R + (dsqrt'_imp_time' y ((L + R) div 2) R)"
        using mid_bound mono_square_imp_time'_pre by (subst dsqrt'_imp_time'.simps) (simp add: rec power2_eq_square Let_def)

      show ?thesis sorry
    next
      case False
      hence s: "dsqrt'_imp_time' y L R \<le> 23 + square_imp_time' R + (dsqrt'_imp_time' y L ((L + R) div 2))"
        using mid_bound mono_square_imp_time'_pre by (subst dsqrt'_imp_time'.simps) (simp add: rec power2_eq_square Let_def)
      show ?thesis sorry
    qed
  next
    case False
    hence "R=Suc L" 
      using "1.prems" by simp
    hence "R-L = 1" 
      by simp
    then show ?thesis
      by (subst dsqrt'_imp_time'.simps) auto
  qed
qed

lemma dsqrt'_imp_time_dsqrt'_imp_time': 
  "dsqrt'_imp_time t s = dsqrt'_imp_time' (dsqrt'_state_y s) (dsqrt'_state_L s) (dsqrt'_state_R s) + t"
proof (induction "dsqrt'_state_y s" "dsqrt'_state_L s" "dsqrt'_state_R s" arbitrary: s t rule: dsqrt'_imp_time'.induct)
  case 1
  then show ?case 
    apply (subst dsqrt'_imp_time.simps)
    apply (subst dsqrt'_imp_time'.simps)
    by (auto simp add: "1" dsqrt'_imp_state_upd_def dsqrt'_imp_time_acc square_imp_time_square_imp_time'
      power2_eq_square square_imp_correct Let_def)
qed

lemma "even ((L::nat)+R) \<Longrightarrow> even (L-R)"
  using even_diff_nat by blast

lemma "R-L = Suc 0 \<Longrightarrow> count_rec_calls y L R = 0"
  by (subst count_rec_calls.simps) auto

lemma middle_alternative: "Suc L < R \<Longrightarrow> (L + R) div 2 = (R - L) div 2 + L"
  by (induction L arbitrary: R) auto

lemma "1 + (L::real) < R \<Longrightarrow> R - ((R - L) div 2 + L) = (R - L) div 2"
  by (smt (z3) field_sum_of_halves)

(* Basically: Add a ceiling function. *)
lemma distance: "Suc L < R \<Longrightarrow> R - ((R - L) div 2 + L) = (R - L) div 2 + (if even (L+R) then 0 else 1)"
  apply (induction L arbitrary: R)
   apply (auto simp add: algebra_simps)[] 
  using left_add_twice apply presburger               
  apply auto
     apply (smt (verit, best) Suc_diff_1 Suc_less_eq add.right_neutral diff_diff_left even_Suc odd_pos plus_1_eq_Suc)
    apply (smt (verit, ccfv_SIG) Nat.add_0_right Suc_lessE diff_Suc_Suc even_Suc)
   apply (smt (verit, del_insts) One_nat_def Suc_diff_Suc Suc_lessD add.commute add_Suc_right
      even_diff_nat odd_Suc_div_two odd_add odd_one plus_1_eq_Suc)
  by (smt (verit, best) One_nat_def Suc_eq_plus1 Suc_less_eq diff_diff_left even_Suc odd_Suc_minus_one plus_1_eq_Suc)

(* 
  Quick and dirty version of the textbook proof
  Works for intervall with a length of a power of two
  This always allows splitting exactly in half
  Either generalize this or show some monotonicity lemma, that allows extending the interval 
*)



(* Horrible: I need to bound the square call in every iteration, just take something at the top level

  As I will probably get less and less tight now, it might be useful to move to O directly
  Basically just a decorated version of the lemma below about count_rec_calls.
  Maybe this might be a pattern? Count cost of iteration and combine with a count rec_calls function
*)
lemma dsqrt'_imp_time'_log_bound_2pow: "L < R
  \<Longrightarrow> \<exists>k. R-L = 2^k
  \<Longrightarrow> dsqrt'_imp_time' y L R \<le> (23 + square_imp_time' R) * (Discrete.log (R - L)) + 7"
proof(induction  y L R rule: count_rec_calls.induct)
  case (1 y L R)
  then show ?case 
  proof(cases "Suc L < R")
    case rec: True
    
    from rec have "(R - L) > 1"
      by simp
    hence size: "(R - L) div 2 > 0"
      by simp

    from "1.prems"(2) \<open>1 < R - L\<close> have "even (L+R)"
      by (metis One_nat_def add.commute even_diff_nat even_numeral even_power less_nat_zero_code 
          nat_diff_split nat_neq_iff nat_power_eq_Suc_0_iff)
    hence "even (R - L)"
      by simp
    with \<open>even (L + R)\<close> "1.prems"(2) have pow: "\<exists>k . R - (L + R) div 2 = 2^k"
      by (smt (verit, del_insts) Suc_leI  cancel_comm_monoid_add_class.diff_cancel distance
          even_power le_add_diff_inverse local.rec log_exp log_exp2_le middle_alternative
          power_Suc0_right power_diff_power_eq size zero_neq_numeral)
    from \<open>even (L + R)\<close> distance rec have d: "R - (L + R) div 2 = (R - L) div 2" 
      using middle_alternative by simp
    from \<open>even (L + R)\<close> distance rec have d': "(L + R) div 2 - L = (R - L) div 2" 
      using middle_alternative by simp

    have mid_bound: "(L + R) div 2 < R" 
      by (metis d size zero_less_diff)

    show ?thesis
    proof(cases "((L + R) div 2)^2 \<le> y")
      case True
      hence s: "dsqrt'_imp_time' y L R \<le> 23 + square_imp_time' R + (dsqrt'_imp_time' y ((L + R) div 2) R)"
        using mid_bound mono_square_imp_time'_pre by (subst dsqrt'_imp_time'.simps) (simp add: rec power2_eq_square Let_def)

      have I: "(dsqrt'_imp_time' y ((L + R) div 2) R) \<le> (23 + square_imp_time' R) * Discrete.log (R - ((L + R) div 2)) + 7"
        apply (subst "1.IH"(1))
        using "1.prems" rec True pow 
        by (auto simp add: power2_eq_square)

      have "dsqrt'_imp_time' y L R \<le> 23 + square_imp_time' R + (dsqrt'_imp_time' y ((L + R) div 2) R)"
        using s .
      also have "\<dots> \<le> (23 + square_imp_time' R) * Suc (Discrete.log (R - ((L + R) div 2))) + 7"
        using I by auto

      finally show ?thesis
        apply (subst log_rec)
        using div_greater_zero_iff size apply blast
        by (simp add: d)
    next
      case False
      hence s: "dsqrt'_imp_time' y L R \<le> 23 + square_imp_time' R + (dsqrt'_imp_time' y L ((L + R) div 2))"
        using mid_bound mono_square_imp_time'_pre by (subst dsqrt'_imp_time'.simps) (simp add: rec power2_eq_square Let_def)

      have I: "(dsqrt'_imp_time' y L ((L + R) div 2)) \<le> (23 + square_imp_time' ((L + R) div 2)) * Discrete.log (((L + R) div 2) - L) + 7"
        apply (subst "1.IH"(2))
        using "1.prems" rec False pow 
        by (auto simp add: power2_eq_square d d')
      hence I': "(dsqrt'_imp_time' y L ((L + R) div 2)) \<le> (23 + square_imp_time' R) * Discrete.log (((L + R) div 2) - L) + 7"
        using mid_bound mono_square_imp_time'_pre 
        by (smt (verit, best) add.left_commute add_le_mono less_or_eq_imp_le mult_le_mono1 nat_add_left_cancel_le)
      have "dsqrt'_imp_time' y L R \<le> 23 + square_imp_time' R + (dsqrt'_imp_time' y L ((L + R) div 2))"
        using s .
      also have "\<dots> \<le> (23 + square_imp_time' R) * Suc (Discrete.log (((L + R) div 2)- L)) + 7"
        using I' by auto
        
      finally show ?thesis
        apply (subst log_rec)
        using div_greater_zero_iff size apply blast
        by (simp add: d d')
    qed
  next
    case False
    then show ?thesis 
      using "1.prems" False 
      by (metis add_leD2 dsqrt'_imp_time'.simps le_refl)
  qed
qed

lemma go: "L < R
  \<Longrightarrow> \<exists>k. R-L = 2^k
  \<Longrightarrow> count_rec_calls y L R = (Discrete.log (R - L))"
proof(induction  y L R rule: count_rec_calls.induct)
  case (1 y L R)
  then show ?case 
  proof(cases "Suc L < R")
    case rec: True
    
    from rec have "(R - L) > 1"
      by simp
    hence size: "(R - L) div 2 > 0"
      by simp

    from "1.prems"(2) \<open>1 < R - L\<close> have "even (L+R)"
      by (metis One_nat_def add.commute even_diff_nat even_numeral even_power less_nat_zero_code 
          nat_diff_split nat_neq_iff nat_power_eq_Suc_0_iff)
    hence "even (R - L)"
      by simp
    with \<open>even (L + R)\<close> "1.prems"(2) have pow: "\<exists>k . R - (L + R) div 2 = 2^k"
      by (smt (verit, del_insts) Suc_leI  cancel_comm_monoid_add_class.diff_cancel distance
          even_power le_add_diff_inverse local.rec log_exp log_exp2_le middle_alternative
          power_Suc0_right power_diff_power_eq size zero_neq_numeral)
    from \<open>even (L + R)\<close> distance rec have d: "R - (L + R) div 2 = (R - L) div 2" 
      using middle_alternative by simp
    from \<open>even (L + R)\<close> distance rec have d': "(L + R) div 2 - L = (R - L) div 2" 
      using middle_alternative by simp

    show ?thesis
    proof(cases "((L + R) div 2)^2 \<le> y")
      case True
      hence s: "count_rec_calls y L R = Suc (count_rec_calls y ((L + R) div 2) R)"
        by (subst count_rec_calls.simps) (simp add: rec power2_eq_square)
      show ?thesis 
        using "1.prems" rec True size pow by (subst log_rec) (auto simp add: "1.IH"(1) s power2_eq_square d d')
    next
      case False
      hence s: "count_rec_calls y L R = Suc (count_rec_calls y L ((L + R) div 2))"
        by (subst count_rec_calls.simps) (simp add: rec power2_eq_square)
      show ?thesis 
        using "1.prems" rec False size pow by (subst log_rec) (auto simp add: "1.IH"(2) s power2_eq_square d d')
    qed
  next
    case False
    then show ?thesis 
      using "1.prems" False
      by (metis Suc_lessI add_0 count_rec_calls.simps less_diff_conv log_Suc_zero plus_nat.simps(2))
  qed
qed

(* The extra size from uneven splits is only dangerous near powers of two*)
lemma log_changes_2pow: "(\<And>k .Suc n \<noteq> 2^k) \<Longrightarrow> Discrete.log (Suc n) = Discrete.log n"
  by (metis Suc_lessD bot_nat_0.not_eq_extremum le_SucE log_Suc_zero log_eqI log_exp2_gt log_exp2_le log_zero zero_less_Suc)

(* The bigger half is a power of two, so problem should not cascade *)
lemma "k>1 \<Longrightarrow> Suc n = 2^k \<Longrightarrow> n = 2^(k-1) + 2^(k-1) - 1"
  apply (induction n) apply auto
  using log_Suc_zero apply auto[1]
  by (metis One_nat_def diff_add_inverse le_add_diff_inverse mult_2 nat_less_le plus_1_eq_Suc power_Suc)

lemma log_split_near_2pow: "Suc n = 2^k \<Longrightarrow> Discrete.log (Suc (2 * n)) = (Discrete.log (Suc n))"
  by (simp add: log_eqI)

(* 
  This should be enough. Proof is ugly
  No exact form yet (maybe ever). Basically, I would need to count how often I encounter critical points near powers of two
  More thinking: After encountering a power of two, I already have an exact way. So what I really need is
  to find out whether I will hit a power of two
*)


lemma dsqrt'_imp_time'_log: "L < R \<Longrightarrow> dsqrt'_imp_time' y L R \<le> (23 + square_imp_time' R) * (Suc (Discrete.log (R - L))) + 7"
proof(induction "R-L" arbitrary: y L R rule: less_induct)
  case less
  then show ?case
  proof(cases "Suc L < R")
    case rec: True
    
    have mid_bound: "(L + R) div 2 < R" 
      using local.rec by linarith

    then show ?thesis
    proof(cases "((L + R) div 2)^2 \<le> y")
      case True
      hence s: "dsqrt'_imp_time' y L R \<le> 23 + square_imp_time' R + (dsqrt'_imp_time' y ((L + R) div 2) R)"
        using mid_bound mono_square_imp_time'_pre by (subst dsqrt'_imp_time'.simps) (simp add: rec power2_eq_square Let_def)

      have I: "dsqrt'_imp_time' y ((L + R) div 2) R \<le> (23 + square_imp_time' R) * Suc (Discrete.log (R - ((L + R) div 2))) + 7"
        apply (rule less)
        using local.rec by linarith+

      consider (even_split) "(R - ((L + R) div 2)) = (R - L) div 2" 
        | (odd_split) "(R - ((L + R) div 2)) = Suc ((R - L) div 2)"
        by linarith
      then show ?thesis
      proof cases
        (* No problem here *)
        case even_split
        from rec have "Discrete.log (R - L) > 0"
          by (subst log_rec) simp_all
        with even_split show ?thesis 
          using I s by auto
      next
        case odd_split
        (* For an odd split we need an interval of length \<ge>3 *)
        with rec have odd: "odd (R - L)"
          using distance middle_alternative by fastforce
        with rec have size: "R - L > 2" 
          by (auto simp add: less_diff_conv intro!: Suc_lessI)

        have recomb: "R - L = Suc (2 * ((R - L) div 2))"
          by (metis Suc_eq_plus1 odd odd_two_times_div_two_succ)

        consider (power) k where "Suc ((R - L) div 2) = 2^k"
          | (unproblematic) "\<And>k. Suc ((R - L) div 2) \<noteq> 2^k"
          by blast
        then show ?thesis
        proof cases
          case power
          have "Discrete.log (Suc ((R - L) div 2)) = k"
            by (simp add: power)
          hence question: "Discrete.log (R - L) = k"
            apply (subst recomb)
            apply (subst log_split_near_2pow)
            using power apply assumption
            by simp

          have "dsqrt'_imp_time' y L R \<le> 23 + square_imp_time' R + (dsqrt'_imp_time' y ((L + R) div 2) R)" 
            using s .
          also have "\<dots> \<le> 23 + square_imp_time' R + ((23 + square_imp_time' R) * Suc (Discrete.log (R - ((L + R) div 2))) + 7)"
            using I by auto
          also have "\<dots> \<le> (23 + square_imp_time' R) * Suc (Suc (Discrete.log (R - ((L + R) div 2)))) + 7" 
            by simp

          have "23 + square_imp_time' R + (dsqrt'_imp_time' y ((L + R) div 2) R) \<le> (23 + square_imp_time' R) * Suc (Discrete.log (R - L)) + 7"
            by (simp add:  question) (metis \<open>Discrete.log (Suc ((R - L) div 2)) = k\<close> add.commute 
                dsqrt'_imp_time'_log_bound_2pow mid_bound odd_split power)
          (* Basically works because we have an exact version for the 2^k case *)
          show ?thesis 
            using \<open>23 + square_imp_time' R + dsqrt'_imp_time' y ((L + R) div 2) R \<le> (23 + square_imp_time' R) * Suc (Discrete.log (R - L)) + 7\<close> order.trans s by blast

        next
          case unproblematic
          hence "Suc ((R - L) div 2) \<noteq> 2^k" for k
            by (simp add: odd_split)
          hence irrel: "Discrete.log (Suc ((R - L) div 2)) = Discrete.log ((R - L) div 2)"
            by (rule log_changes_2pow)
          show ?thesis
            using I odd_split size s irrel by (subst log_rec) auto
        qed
      qed
    next
      case False

      
      hence s: "dsqrt'_imp_time' y L R \<le> 23 + square_imp_time' R + (dsqrt'_imp_time' y L ((L + R) div 2))"
        using mid_bound mono_square_imp_time'_pre by (subst dsqrt'_imp_time'.simps) (simp add: rec power2_eq_square Let_def)

      have I: "(dsqrt'_imp_time' y L ((L + R) div 2)) \<le> (23 + square_imp_time' R) * Suc (Discrete.log (((L + R) div 2) - L)) + 7"
        by (smt (verit, best) False One_nat_def diff_add_inverse2 diff_is_0_eq div_2_gt_zero div_greater_zero_iff div_less 
            dsqrt'_imp_time'.elims le_diff_conv le_trans less.hyps linorder_not_le local.rec mid_bound
            middle_alternative mult.commute mult_le_mono2 plus_1_eq_Suc power2_eq_square s)
        
      have split: "(((L + R) div 2) - L) = (R - L) div 2"
        by (simp add: local.rec middle_alternative)
      from rec have "Discrete.log (R - L) > 0"
        by (subst log_rec) simp_all
      with split show ?thesis 
        using I s by auto
    qed
  next
    case False
    with less.prems have "Suc L = R"
      by simp
    then show ?thesis
      apply (subst dsqrt'_imp_time'.simps)
      using False by auto
  qed
qed

lemma count_rec_calls_log: "L < R \<Longrightarrow> count_rec_calls y L R \<le> Suc (Discrete.log (R - L))"
proof(induction "R-L" arbitrary: y L R rule: less_induct)
  case less
  then show ?case
  proof(cases "Suc L < R")
    case rec: True
    then show ?thesis
    proof(cases "((L + R) div 2)^2 \<le> y")
      case True
      hence s: "count_rec_calls y L R = Suc (count_rec_calls y ((L + R) div 2) R)"
        by (subst count_rec_calls.simps) (simp add: rec power2_eq_square)

      have I: "count_rec_calls y ((L + R) div 2) R \<le> Suc (Discrete.log (R - ((L + R) div 2)))"
        apply (rule less)
        using local.rec by linarith+

      consider (even_split) "(R - ((L + R) div 2)) = (R - L) div 2" 
        | (odd_split) "(R - ((L + R) div 2)) = Suc ((R - L) div 2)"
        by linarith
      then show ?thesis
      proof cases
        (* No problem here *)
        case even_split
        from rec have "Discrete.log (R - L) > 0"
          by (subst log_rec) simp_all
        with even_split show ?thesis 
          using I by (simp add: s)
      next
        case odd_split
        (* For an odd split we need an interval of length \<ge>3 *)
        with rec have odd: "odd (R - L)"
          using distance middle_alternative by fastforce
        with rec have size: "R - L > 2" 
          by (auto simp add: less_diff_conv intro!: Suc_lessI)

        have recomb: "R - L = Suc (2 * ((R - L) div 2))"
          by (metis Suc_eq_plus1 odd odd_two_times_div_two_succ)

        consider (power) k where "Suc ((R - L) div 2) = 2^k"
          | (unproblematic) "\<And>k. Suc ((R - L) div 2) \<noteq> 2^k"
          by blast
        then show ?thesis
        proof cases
          case power
          have "Discrete.log (Suc ((R - L) div 2)) = k"
            by (simp add: power)
          hence question: "Discrete.log (R - L) = k"
            apply (subst recomb)
            apply (subst log_split_near_2pow)
            using power apply assumption
            by simp

          (* Basically works because we have a version for the 2^k case *)
          show ?thesis 
            apply (subst s)
            apply (subst le_Suc_eq)
            apply (rule disjI2)
            apply (subst go) 
            apply (metis diff_is_0_eq' linorder_not_less nat.simps(3) odd_split)
            apply (simp add: odd_split power)
            thm  less_Suc_eq_0_disj log_exp   zero_less_diff
            using question power odd_split apply (metis go le_Suc_eq less_Suc_eq_0_disj log_exp   zero_less_diff) done
        next
          case unproblematic
          hence "Suc ((R - L) div 2) \<noteq> 2^k" for k
            by (simp add: odd_split)
          hence irrel: "Discrete.log (Suc ((R - L) div 2)) = Discrete.log ((R - L) div 2)"
            by (rule log_changes_2pow)
          show ?thesis
            using I odd_split size by (subst log_rec) (auto simp add: s irrel)
        qed
      qed
    next
      case False
      hence s: "count_rec_calls y L R = Suc (count_rec_calls y L ((L + R) div 2))"
        by (subst count_rec_calls.simps) (simp add: rec power2_eq_square)
      have I: "count_rec_calls y L ((L + R) div 2) \<le> Suc (Discrete.log (((L + R) div 2) - L))"
        apply (rule less)
        using local.rec by linarith+
      have split: "(((L + R) div 2) - L) = (R - L) div 2"
        by (simp add: local.rec middle_alternative)
      from rec have "Discrete.log (R - L) > 0"
        by (subst log_rec) simp_all
      with split show ?thesis 
        using I by (simp add: s)
    qed
  next
    case False
    with less.prems have "Suc L = R"
      by simp
    then show ?thesis
      apply (subst count_rec_calls.simps)
      using False by auto
  qed
qed

(* Now only refinement to IMP remains, Mohammad help pls *)

value mul_imp_time
value triangle_IMP_Minus
value prod_decode_aux_imp_time
thm WhileI
term dsqrt'

abbreviation "dsqrt'_pref \<equiv> ''dsqrt'.''"
abbreviation "dsqrt'_y_str \<equiv> ''y''"
abbreviation "dsqrt'_L_str \<equiv> ''L''"
abbreviation "dsqrt'_R_str \<equiv> ''R''"

definition dsqrt'_IMP_Minus_while_condition where
  "dsqrt'_IMP_Minus_while_condition \<equiv> 
  ''inc'' ::= ((V dsqrt'_L_str) \<oplus> (N 1));;
   ''diff'' ::= ((V dsqrt'_R_str) \<ominus> (V ''inc''))"

definition dsqrt'_IMP_Minus_loop_body where
  "dsqrt'_IMP_Minus_loop_body =
    \<comment> \<open>M = (L+R) / 2;\<close>
    ''M'' ::= ((V dsqrt'_L_str) \<oplus> (V dsqrt'_R_str));;
    ''M'' ::= ((V ''M'')\<then>);;

    \<comment> \<open>M*M,\<close>
    (square_prefix @ square_x_str) ::= A (V ''M'');;
    (square_prefix @ square_square_str) ::= A (N 0);;
    invoke_subprogram square_prefix square_IMP_Minus;;
    ''M2'' ::= A (V (square_prefix @ square_square_str));;

    \<comment> \<open>New left bound\<close>
    ''cond'' ::= ((V ''M2'') \<ominus> (V dsqrt'_y_str));;
    (IF ''cond''\<noteq>0 THEN dsqrt'_L_str ::= A (V dsqrt'_L_str) ELSE dsqrt'_L_str ::= A (V ''M''));;
    \<comment> \<open>New right bound\<close>
    (IF ''cond''\<noteq>0 THEN dsqrt'_R_str ::= A (V ''M'') ELSE dsqrt'_R_str ::= A (V dsqrt'_R_str))"


definition dsqrt'_IMP_Minus_after_loop where
  "dsqrt'_IMP_Minus_after_loop = Com.SKIP"

definition dsqrt'_IMP_Minus where
"dsqrt'_IMP_Minus \<equiv>
  \<comment> \<open>if L+1 < R\<close>
  dsqrt'_IMP_Minus_while_condition;;
  WHILE ''diff''\<noteq>0 DO (
    dsqrt'_IMP_Minus_loop_body;;
    dsqrt'_IMP_Minus_while_condition
  );;
  dsqrt'_IMP_Minus_after_loop"

value "dsqrt'_imp_time' 4 0 8"

values "{(s' dsqrt'_y_str, s' dsqrt'_L_str,t) | s' t . 
  (dsqrt'_IMP_Minus, (\<lambda>_.0)(dsqrt'_y_str := 4, dsqrt'_L_str := 0, dsqrt'_R_str := 8)) \<Rightarrow>\<^bsup>t\<^esup> s'}"
lemmas dsqrt'_IMP_Minus_subprogram_simps =
  dsqrt'_IMP_Minus_while_condition_def dsqrt'_IMP_Minus_loop_body_def dsqrt'_IMP_Minus_after_loop_def

definition "dsqrt'_imp_to_HOL_state p s =
  \<lparr>dsqrt'_state_y = s (add_prefix p dsqrt'_y_str), dsqrt'_state_L = s (add_prefix p dsqrt'_L_str), 
    dsqrt'_state_R = s (add_prefix p dsqrt'_R_str)\<rparr>"

abbreviation 
  "dsqrt'_IMP_vars \<equiv> {dsqrt'_y_str, dsqrt'_L_str, dsqrt'_R_str, ''inc'', ''diff'', ''cond'', ''M'', ''M2''}"


(* Swapped sides of eq in premises*)
lemma square_IMP_Minus_correct':
  "\<lbrakk>(invoke_subprogram (p1 @ p2) square_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (square_imp_time 0 (square_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) square_square_str) = 
        square_square (square_imp (square_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s' (add_prefix p1 v) = s (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using square_IMP_Minus_correct by metis

(* Experimental rule to split up assumption*)
lemma test: "(\<And>v . v \<in> insert x S \<Longrightarrow> P v) \<equiv> (P x &&& (\<And>v . v \<in> S \<Longrightarrow> P v))"
  apply (rule)
  apply auto
  by presburger+
find_theorems "_ &&& _"

(*
lemma dsqrt'_IMP_Minus_correct_function_1: 
  "(invoke_subprogram p dsqrt'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p dsqrt'_L_str) = 
       dsqrt'_state_L (dsqrt'_imp (dsqrt'_imp_to_HOL_state p s))"
proof (induction "dsqrt'_imp_to_HOL_state p s" arbitrary: s s' t rule: dsqrt'_imp.induct)
  case 1
  then show ?case 
  apply (subst dsqrt'_imp.simps)
  apply (simp only: dsqrt'_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule While_tE)
   apply (auto simp add: dsqrt'_imp_state_upd_def prefix_simps Let_def dsqrt'_imp_to_HOL_state_def dsqrt'_IMP_Minus_subprogram_simps split: if_splits)[]
    apply (erule Seq_tE)+
    apply dest_com_gen

    subgoal for x s2 y xa s2a ya xb s2b yb xc s2c yc
    apply (simp only: dsqrt'_IMP_Minus_while_condition_def prefix_simps)
    apply (erule Seq_tE)+
      by (auto simp add: dsqrt'_imp_to_HOL_state_def) 

    thm square_imp_correct

    subgoal premises p for x s2 y xa s2a ya xb s2b yb xc s2c yc 
      thm p
      using p(4,5,8,9) apply -
      apply (simp only: dsqrt'_IMP_Minus_while_condition_def dsqrt'_IMP_Minus_loop_body_def prefix_simps)
      apply(erule Seq_tE)+
      apply(all \<open>erule square_IMP_Minus_correct'[where vars = "dsqrt'_IMP_vars"]\<close>)
      subgoal premises p using p(24) by auto (* Here we already see how auto gets confused by all the crap in p*)
      apply(elim If_tE)
      apply (all \<open>drule AssignD\<close>)+
      apply (all \<open>erule conjE\<close>)+
         apply (simp_all only: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_to_HOL_state_def)
        (* 4 calls to avoid tracing stopping... *)
         apply (force simp add: square_imp_correct power2_eq_square split: if_splits)[]
         apply (force simp add: square_imp_correct power2_eq_square split: if_splits)[]
         apply (force simp add: square_imp_correct power2_eq_square split: if_splits)[]
        apply (force simp add: square_imp_correct power2_eq_square split: if_splits)[]
        done

    subgoal for x s2 y xa s2a ya xb s2b yb xc s2c yc 
      apply (simp only: dsqrt'_IMP_Minus_while_condition_def dsqrt'_IMP_Minus_loop_body_def prefix_simps)
      apply(erule Seq_tE)+
      proof (erule square_IMP_Minus_correct[where vars = "dsqrt'_IMP_vars"], goal_cases)
        case (1 x s2 y xa s2a ya xb s2b yb xc s2c yc xd s2d yd xe s2e ye xf s2f yf xg s2g yg xh s2h yh xi s2i yi v)
        show ?case using 1(29) by auto
      next
        case (2 x s2 y xa s2a ya xb s2b yb xc s2c yc xd s2d yd xe s2e ye xf s2f yf xg s2g yg xh s2h yh xi s2i yi)
        

        (* Keep the correctness result of square out of goalstate *)
        from 2(1-30) show ?case 
          apply(elim If_tE)
          apply (all \<open>drule AssignD\<close>)+
          apply (all \<open>erule conjE\<close>)+

         apply (simp_all only: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_to_HOL_state_def)
          using [[linarith_split_limit=19]] apply simp apply safe 
          thm 2(31)[simplified test]
          using 2(31) apply -
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
              apply (simp add: atomize_conj) apply safe

          subgoal  by presburger 
          using 2(31) apply -
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (simp add: atomize_conj) (* done already *)

          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
              apply (simp only: atomize_conj fun_upd_other) apply safe

          subgoal  thm fun_upd_other less_numeral_extra(3) list.discI list.inject same_append_eq
            by (smt (z3) fun_upd_other less_numeral_extra(3) list.discI list.inject same_append_eq) 

          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
          apply (subst (asm) test)
              apply (simp only: atomize_conj fun_upd_other) apply safe
        
        qed oops  
*)


lemma dsqrt'_IMP_Minus_correct_function_1: 
  "(invoke_subprogram p dsqrt'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p dsqrt'_L_str) = 
       dsqrt'_state_L (dsqrt'_imp (dsqrt'_imp_to_HOL_state p s))"
proof (induction "dsqrt'_imp_to_HOL_state p s" arbitrary: s s' t rule: dsqrt'_imp.induct)
  case 1
  then show ?case 
  apply (subst dsqrt'_imp.simps)
  apply (simp only: dsqrt'_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule While_tE)
   apply (auto simp add: dsqrt'_imp_state_upd_def prefix_simps Let_def dsqrt'_imp_to_HOL_state_def dsqrt'_IMP_Minus_subprogram_simps split: if_splits)[]
    apply (erule Seq_tE)+
    apply dest_com_gen

    subgoal for x s2 y xa s2a ya xb s2b yb xc s2c yc
    apply (simp only: dsqrt'_IMP_Minus_while_condition_def prefix_simps)
    apply (erule Seq_tE)+
      by (auto simp add: dsqrt'_imp_to_HOL_state_def) 

    thm square_imp_correct

    subgoal premises p for x s2 y xa s2a ya xb s2b yb xc s2c yc 
      thm p
      using p(4,5,8,9) apply -
      apply (simp only: dsqrt'_IMP_Minus_while_condition_def dsqrt'_IMP_Minus_loop_body_def prefix_simps)
      apply(erule Seq_tE)+
      apply(all \<open>erule square_IMP_Minus_correct[where vars = "dsqrt'_IMP_vars"]\<close>)
      subgoal premises p using p(24) by auto (* Here we already see how auto gets confused by all the crap in p*)
      apply(elim If_tE)
      apply (all \<open>drule AssignD\<close>)+
      apply (all \<open>erule conjE\<close>)+
         apply (simp_all only: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_to_HOL_state_def)
         apply (force simp add: square_imp_correct power2_eq_square)
                 apply (force simp add: square_imp_correct power2_eq_square)[]
                 apply (force simp add: square_imp_correct power2_eq_square)[]
      apply (force simp add: square_imp_correct power2_eq_square)[]
      done

    subgoal for x s2 y xa s2a ya xb s2b yb xc s2c yc 
      apply (simp only: dsqrt'_IMP_Minus_while_condition_def dsqrt'_IMP_Minus_loop_body_def prefix_simps)
      apply(erule Seq_tE)+
      apply(all \<open>erule square_IMP_Minus_correct[where vars = "dsqrt'_IMP_vars"]\<close>)
      subgoal premises p using p(29) by auto 
      apply(elim If_tE)
      apply (all \<open>drule AssignD\<close>)+
      apply (all \<open>erule conjE\<close>)+
         apply (simp_all only: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_to_HOL_state_def)
      (* I managed the previous one easier, so this should be doable without the splits as well*)
      using [[linarith_split_limit = 25]] apply (simp_all split: if_splits)
       apply safe
      proof(goal_cases)
        case (1 x s2 y xa s2a ya xb s2b yb xc s2c yc xd s2d yd xe s2e ye xf s2f yf xg s2g yg xh s2h yh xi s2i yi xj xk)
        from 1(10) show ?case 
        proof - (* There really seems to be a problem with this naming thingy *)
          have "\<forall>x0. (x0 = dsqrt'_y_str \<or> x0 = dsqrt'_L_str \<or> x0 = dsqrt'_R_str \<or> x0 = CHR ''i'' # CHR ''n'' # mul_c_str \<or> x0 = ''diff'' \<or> x0 = ''cond'' \<or> x0 = ''M'' \<or> x0 = ''M2'' \<longrightarrow> (if x0 = CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_square_str then 0 else (s(add_prefix p (CHR ''i'' # CHR ''n'' # mul_c_str) := Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''diff'' := s (add_prefix p dsqrt'_R_str) - Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''M'' := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2, add_prefix p (CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_x_str) := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2)) (add_prefix p x0)) = s2e (add_prefix p x0)) = (x0 \<noteq> dsqrt'_y_str \<and> x0 \<noteq> dsqrt'_L_str \<and> x0 \<noteq> dsqrt'_R_str \<and> x0 \<noteq> CHR ''i'' # CHR ''n'' # mul_c_str \<and> x0 \<noteq> ''diff'' \<and> x0 \<noteq> ''cond'' \<and> x0 \<noteq> ''M'' \<and> x0 \<noteq> ''M2'' \<or> (if x0 = CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_square_str then 0 else (s(add_prefix p (CHR ''i'' # CHR ''n'' # mul_c_str) := Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''diff'' := s (add_prefix p dsqrt'_R_str) - Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''M'' := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2, add_prefix p (CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_x_str) := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2)) (add_prefix p x0)) = s2e (add_prefix p x0))"
            by meson
          then have "\<forall>cs. cs \<noteq> dsqrt'_y_str \<and> cs \<noteq> dsqrt'_L_str \<and> cs \<noteq> dsqrt'_R_str \<and> cs \<noteq> CHR ''i'' # CHR ''n'' # mul_c_str \<and> cs \<noteq> ''diff'' \<and> cs \<noteq> ''cond'' \<and> cs \<noteq> ''M'' \<and> cs \<noteq> ''M2'' \<or> (if cs = CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_square_str then 0 else (s(add_prefix p (CHR ''i'' # CHR ''n'' # mul_c_str) := Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''diff'' := s (add_prefix p dsqrt'_R_str) - Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''M'' := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2, add_prefix p (CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_x_str) := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2)) (add_prefix p cs)) = s2e (add_prefix p cs)"
            by (smt (z3) "1"(10)) (* failed *) (* lol no *)
          then have f1: "\<forall>cs. cs \<noteq> dsqrt'_y_str \<and> cs \<noteq> dsqrt'_L_str \<and> cs \<noteq> dsqrt'_R_str \<and> cs \<noteq> CHR ''i'' # CHR ''n'' # mul_c_str \<and> cs \<noteq> ''diff'' \<and> cs \<noteq> ''cond'' \<and> cs \<noteq> ''M'' \<and> cs \<noteq> ''M2'' \<or> (if cs = CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_square_str then 0 = s2e (add_prefix p cs) else (s(add_prefix p (CHR ''i'' # CHR ''n'' # mul_c_str) := Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''diff'' := s (add_prefix p dsqrt'_R_str) - Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''M'' := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2, add_prefix p (CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_x_str) := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2)) (add_prefix p cs) = s2e (add_prefix p cs))"
            by presburger
          then have f2: "if dsqrt'_y_str = CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_square_str then 0 = s2e (add_prefix p dsqrt'_y_str) else (s(add_prefix p (CHR ''i'' # CHR ''n'' # mul_c_str) := Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''diff'' := s (add_prefix p dsqrt'_R_str) - Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''M'' := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2, add_prefix p (CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_x_str) := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2)) (add_prefix p dsqrt'_y_str) = s2e (add_prefix p dsqrt'_y_str)"
            by blast
          have "if dsqrt'_L_str = CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_square_str then 0 = s2e (add_prefix p dsqrt'_L_str) else (s(add_prefix p (CHR ''i'' # CHR ''n'' # mul_c_str) := Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''diff'' := s (add_prefix p dsqrt'_R_str) - Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''M'' := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2, add_prefix p (CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_x_str) := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2)) (add_prefix p dsqrt'_L_str) = s2e (add_prefix p dsqrt'_L_str)"
            using f1 by blast
          then show ?thesis
            using f2 f1 by force
        qed
      next
        case (2 x s2 y xa s2a ya xb s2b yb xc s2c yc xd s2d yd xe s2e ye xf s2f yf xg s2g yg xh s2h yh xi s2i yi xj xk)
        then show ?case
          by (force simp add: square_imp_correct power2_eq_square)[]
      next
        case (3 x s2 y xa s2a ya xb s2b yb xc s2c yc xd s2d yd xe s2e ye xf s2f yf xg s2g yg xh s2h yh xi s2i yi xj xk)
        then show ?case
          by (force simp add: square_imp_correct power2_eq_square)[]
      next
        case (4 x s2 y xa s2a ya xb s2b yb xc s2c yc xd s2d yd xe s2e ye xf s2f yf xg s2g yg xh s2h yh xi s2i yi xj xk)
        from 4(10) show ?case
        proof -
          have f1: "\<forall>b ba bb bc bd be bf bg bh bi bj bk bl bm bn bo. (Char b ba bb bc bd be bf bg = Char bh bi bj bk bl bm bn bo) = ((\<not> b) \<noteq> bh \<and> (\<not> ba) \<noteq> bi \<and> (\<not> bb) \<noteq> bj \<and> (\<not> bc) \<noteq> bk \<and> (\<not> bd) \<noteq> bl \<and> (\<not> be) \<noteq> bm \<and> (\<not> bf) \<noteq> bn \<and> (\<not> bg) \<noteq> bo)"
            by simp
          have "\<forall>x0. (x0 = dsqrt'_y_str \<or> x0 = dsqrt'_L_str \<or> x0 = dsqrt'_R_str \<or> x0 = CHR ''i'' # CHR ''n'' # mul_c_str \<or> x0 = ''diff'' \<or> x0 = ''cond'' \<or> x0 = ''M'' \<or> x0 = ''M2'' \<longrightarrow> (if x0 = CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_square_str then 0 else (s(add_prefix p (CHR ''i'' # CHR ''n'' # mul_c_str) := Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''diff'' := s (add_prefix p dsqrt'_R_str) - Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''M'' := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2, add_prefix p (CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_x_str) := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2)) (add_prefix p x0)) = s2e (add_prefix p x0)) = (x0 \<noteq> dsqrt'_y_str \<and> x0 \<noteq> dsqrt'_L_str \<and> x0 \<noteq> dsqrt'_R_str \<and> x0 \<noteq> CHR ''i'' # CHR ''n'' # mul_c_str \<and> x0 \<noteq> ''diff'' \<and> x0 \<noteq> ''cond'' \<and> x0 \<noteq> ''M'' \<and> x0 \<noteq> ''M2'' \<or> (if x0 = CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_square_str then 0 else (s(add_prefix p (CHR ''i'' # CHR ''n'' # mul_c_str) := Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''diff'' := s (add_prefix p dsqrt'_R_str) - Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''M'' := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2, add_prefix p (CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_x_str) := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2)) (add_prefix p x0)) = s2e (add_prefix p x0))"
            by meson
          then have "\<forall>cs. cs \<noteq> dsqrt'_y_str \<and> cs \<noteq> dsqrt'_L_str \<and> cs \<noteq> dsqrt'_R_str \<and> cs \<noteq> CHR ''i'' # CHR ''n'' # mul_c_str \<and> cs \<noteq> ''diff'' \<and> cs \<noteq> ''cond'' \<and> cs \<noteq> ''M'' \<and> cs \<noteq> ''M2'' \<or> (if cs = CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_square_str then 0 else (s(add_prefix p (CHR ''i'' # CHR ''n'' # mul_c_str) := Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''diff'' := s (add_prefix p dsqrt'_R_str) - Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''M'' := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2, add_prefix p (CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_x_str) := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2)) (add_prefix p cs)) = s2e (add_prefix p cs)"
            by (smt (z3) "4"(10)) (* failed *)
          then show ?thesis
            using f1 by (smt (z3) fun_upd_apply list.inject same_append_eq)
        qed
      qed
      done

  qed


lemma dsqrt'_imp_time_acc': "(dsqrt'_imp_time t s) = t + (dsqrt'_imp_time 0 s)"
  by (induction t) (auto simp add: dsqrt'_imp_time_acc)
lemma dsqrt'_imp_time_acc'': "NO_MATCH 0 t \<Longrightarrow> (dsqrt'_imp_time t s) = t + (dsqrt'_imp_time 0 s)"
  using dsqrt'_imp_time_acc' .

lemma dsqrt'_IMP_Minus_correct_time: 
  "(invoke_subprogram p dsqrt'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> t = dsqrt'_imp_time 0 (dsqrt'_imp_to_HOL_state p s)"
proof (induction "dsqrt'_imp_to_HOL_state p s" arbitrary: s s' t rule: dsqrt'_imp.induct)
  case 1
  from "1.prems" show ?case 
  apply (subst dsqrt'_imp_time.simps)
  apply (simp only: dsqrt'_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule While_tE_time)
     apply (auto simp add: dsqrt'_imp_state_upd_def prefix_simps Let_def dsqrt'_imp_to_HOL_state_def dsqrt'_IMP_Minus_subprogram_simps 
          dsqrt'_imp_time_acc split: if_splits)[]
    apply (erule Seq_tE)+
    using "1.hyps"[unfolded dsqrt'_IMP_Minus_def] apply -
    apply (simp add: add.assoc)
    apply (dest_com_gen_time)

    subgoal for x s2 y xa s2a ya xb s2b yb xc s2c yc
    apply (simp only: dsqrt'_IMP_Minus_while_condition_def prefix_simps)
    apply (erule Seq_tE)+
      by (auto simp add: dsqrt'_imp_to_HOL_state_def) 

    subgoal premises p for x s2 y xa s2a ya xb s2b yb xc s2c yc 
      thm p
      using p(4,5,8,9) apply -
      apply (simp only: dsqrt'_IMP_Minus_while_condition_def dsqrt'_IMP_Minus_loop_body_def prefix_simps)
      apply(erule Seq_tE)+

      apply(all \<open>erule square_IMP_Minus_correct[where vars = "dsqrt'_IMP_vars"]\<close>)
      subgoal premises p using p(24) by auto (* Here we already see how auto gets confused by all the crap in p*)
      apply(elim If_tE)
      apply (all \<open>drule AssignD\<close>)+
      apply (all \<open>erule conjE\<close>)+
         apply (simp_all only: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_to_HOL_state_def)
      using [[linarith_split_limit=23]]
         apply (simp split: if_splits)
      thm square_imp_correct
      apply safe
         apply (force simp add: square_imp_correct power2_eq_square)[]
                 apply (force simp add: square_imp_correct power2_eq_square)[]
      subgoal premises p using p(5,6,7) by (smt (z3) fun_upd_apply gr_implies_not0)
                 apply (force simp add: square_imp_correct power2_eq_square)+
    (*proof - (* For the third subgoal, we only needed that variables are not affected *)
      fix xl :: nat and s2j :: "char list \<Rightarrow> nat" and yj :: nat and xaa :: nat 
        and s2aa :: "char list \<Rightarrow> nat" and yaa :: nat and xba :: nat and s2ba :: "char list \<Rightarrow> nat" 
        and yba :: nat and xca :: nat and s2ca :: "char list \<Rightarrow> nat" and yca :: nat and xd :: nat 
        and s2d :: "char list \<Rightarrow> nat" and yd :: nat and xe :: nat and s2e :: "char list \<Rightarrow> nat" 
        and ye :: nat and xf :: nat and s2f :: "char list \<Rightarrow> nat" and yf :: nat and xg :: nat and s2g :: "char list \<Rightarrow> nat" 
        and yg :: nat and xh :: nat and s2h :: "char list \<Rightarrow> nat" and yh :: nat and xi :: nat and s2i :: "char list \<Rightarrow> nat"
        and yi :: nat and xj :: nat and xk :: nat
      assume a1: "\<And>v. v = dsqrt'_y_str \<or> v = dsqrt'_L_str \<or> v = dsqrt'_R_str \<or> v = CHR ''i'' # CHR ''n'' # mul_c_str \<or> v = ''diff'' 
        \<or> v = ''cond'' \<or> v = ''M'' \<or> v = ''M2'' 
      \<Longrightarrow> (if v = CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_square_str then 0 
        else (s(add_prefix p (CHR ''i'' # CHR ''n'' # mul_c_str) := Suc (s (add_prefix p dsqrt'_L_str)), 
          add_prefix p ''diff'' := s (add_prefix p dsqrt'_R_str) - Suc (s (add_prefix p dsqrt'_L_str)),
          add_prefix p ''M'' := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2, 
          add_prefix p (CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_x_str) 
          := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2)) (add_prefix p v)) = s2e (add_prefix p v)"
      have "CHR ''M'' \<noteq> CHR ''s''"
        by force
      then show "(s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2 = s2e (add_prefix p ''M'')"
        using a1 by (smt (z3) fun_upd_apply list.inject)
    next*)done

    subgoal for x s2 y xa s2a ya xb s2b yb xc s2c yc 
      apply (simp only: dsqrt'_IMP_Minus_while_condition_def dsqrt'_IMP_Minus_loop_body_def prefix_simps)
      apply(erule Seq_tE)+
      apply(all \<open>erule square_IMP_Minus_correct[where vars = "dsqrt'_IMP_vars"]\<close>)
      subgoal premises p using p(29) by auto 
      apply(elim If_tE)
      apply (all \<open>drule AssignD\<close>)+
      apply (all \<open>erule conjE\<close>)+
         apply (simp_all only: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_to_HOL_state_def)
      using [[linarith_split_limit = 25]] apply (simp_all split: if_splits)
       apply safe
      proof(goal_cases)
        case (1 x s2 y xa s2a ya xb s2b yb xc s2c yc xd s2d yd xe s2e ye xf s2f yf xg s2g yg xh s2h yh xi s2i yi xj xk)
        then show ?case  
          apply (simp add: dsqrt'_imp_time_acc'' square_imp_correct power2_eq_square)
         (* Again, problems with the naming stuff, everywhere maybe try changing the style of correctness lemma *)
         proof -
           assume a1: "\<And>v. v = dsqrt'_y_str \<or> v = dsqrt'_L_str \<or> v = dsqrt'_R_str \<or> v = CHR ''i'' # CHR ''n'' # mul_c_str \<or> v = ''diff'' \<or> v = ''cond'' \<or> v = ''M'' \<or> v = ''M2'' \<Longrightarrow> (if v = CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_square_str then 0 else (s(add_prefix p (CHR ''i'' # CHR ''n'' # mul_c_str) := Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''diff'' := s (add_prefix p dsqrt'_R_str) - Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''M'' := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2, add_prefix p (CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_x_str) := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2)) (add_prefix p v)) = s2e (add_prefix p v)"
           have "\<forall>b ba bb bc bd be bf bg bh bi bj bk bl bm bn bo. (Char b ba bb bc bd be bf bg = Char bh bi bj bk bl bm bn bo) = ((\<not> b) \<noteq> bh \<and> (\<not> ba) \<noteq> bi \<and> (\<not> bb) \<noteq> bj \<and> (\<not> bc) \<noteq> bk \<and> (\<not> bd) \<noteq> bl \<and> (\<not> be) \<noteq> bm \<and> (\<not> bf) \<noteq> bn \<and> (\<not> bg) \<noteq> bo)"
             by simp
           then show "dsqrt'_imp_time 0 \<lparr>dsqrt'_state_y = s2e (add_prefix p dsqrt'_y_str), dsqrt'_state_L = s2e (add_prefix p dsqrt'_L_str), dsqrt'_state_R = s2e (add_prefix p ''M'')\<rparr> = dsqrt'_imp_time 0 \<lparr>dsqrt'_state_y = s (add_prefix p dsqrt'_y_str), dsqrt'_state_L = s (add_prefix p dsqrt'_L_str), dsqrt'_state_R = (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2\<rparr>"
             using a1 by (smt (z3) fun_upd_apply list.inject same_append_eq)
         qed
      next
        case (2 x s2 y xa s2a ya xb s2b yb xc s2c yc xd s2d yd xe s2e ye xf s2f yf xg s2g yg xh s2h yh xi s2i yi xj xk)
        then show ?case
          apply (simp add: dsqrt'_imp_time_acc'' square_imp_correct power2_eq_square)
        proof -
          assume a1: "(s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2 * ((s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2) \<le> s (add_prefix p dsqrt'_y_str)"
          assume a2: "s2e (add_prefix p dsqrt'_y_str) < (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2 * ((s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2)"
          assume a3: "\<And>v. v = dsqrt'_y_str \<or> v = dsqrt'_L_str \<or> v = dsqrt'_R_str \<or> v = CHR ''i'' # CHR ''n'' # mul_c_str \<or> v = ''diff'' \<or> v = ''cond'' \<or> v = ''M'' \<or> v = ''M2'' \<Longrightarrow> (if v = CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_square_str then 0 else (s(add_prefix p (CHR ''i'' # CHR ''n'' # mul_c_str) := Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''diff'' := s (add_prefix p dsqrt'_R_str) - Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''M'' := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2, add_prefix p (CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_x_str) := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2)) (add_prefix p v)) = s2e (add_prefix p v)"
          have f4: "True \<noteq> False"
            by presburger
          have f5: "\<forall>b ba bb bc bd be bf bg bh bi bj bk bl bm bn bo. (Char b ba bb bc bd be bf bg = Char bh bi bj bk bl bm bn bo) = ((\<not> b) \<noteq> bh \<and> (\<not> ba) \<noteq> bi \<and> (\<not> bb) \<noteq> bj \<and> (\<not> bc) \<noteq> bk \<and> (\<not> bd) \<noteq> bl \<and> (\<not> be) \<noteq> bm \<and> (\<not> bf) \<noteq> bn \<and> (\<not> bg) \<noteq> bo)"
            by simp
          have "CHR ''y'' \<noteq> CHR ''d''"
            by force
          then show "dsqrt'_imp_time 0 \<lparr>dsqrt'_state_y = s2e (add_prefix p dsqrt'_y_str), dsqrt'_state_L = s2e (add_prefix p dsqrt'_L_str), dsqrt'_state_R = s2e (add_prefix p ''M'')\<rparr> = dsqrt'_imp_time 0 \<lparr>dsqrt'_state_y = s (add_prefix p dsqrt'_y_str), dsqrt'_state_L = (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2, dsqrt'_state_R = s (add_prefix p dsqrt'_R_str)\<rparr>"
            using f5 f4 a3 a2 a1 by (smt (z3) fun_upd_other linorder_not_less list.inject same_append_eq)
        qed
      next
        case (3 x s2 y xa s2a ya xb s2b yb xc s2c yc xd s2d yd xe s2e ye xf s2f yf xg s2g yg xh s2h yh xi s2i yi xj xk)
        then show ?case
          apply (simp add: dsqrt'_imp_time_acc'' square_imp_correct power2_eq_square)
        proof -
          assume a1: "\<not> (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2 * ((s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2) \<le> s (add_prefix p dsqrt'_y_str)"
          assume a2: "(s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2 * ((s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2) \<le> s2e (add_prefix p dsqrt'_y_str)"
          assume a3: "\<And>v. v = dsqrt'_y_str \<or> v = dsqrt'_L_str \<or> v = dsqrt'_R_str \<or> v = CHR ''i'' # CHR ''n'' # mul_c_str \<or> v = ''diff'' \<or> v = ''cond'' \<or> v = ''M'' \<or> v = ''M2'' \<Longrightarrow> (if v = CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_square_str then 0 else (s(add_prefix p (CHR ''i'' # CHR ''n'' # mul_c_str) := Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''diff'' := s (add_prefix p dsqrt'_R_str) - Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''M'' := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2, add_prefix p (CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_x_str) := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2)) (add_prefix p v)) = s2e (add_prefix p v)"
          have f4: "True \<noteq> False"
            by meson
          have f5: "\<forall>b ba bb bc bd be bf bg bh bi bj bk bl bm bn bo. (Char b ba bb bc bd be bf bg = Char bh bi bj bk bl bm bn bo) = ((\<not> b) \<noteq> bh \<and> (\<not> ba) \<noteq> bi \<and> (\<not> bb) \<noteq> bj \<and> (\<not> bc) \<noteq> bk \<and> (\<not> bd) \<noteq> bl \<and> (\<not> be) \<noteq> bm \<and> (\<not> bf) \<noteq> bn \<and> (\<not> bg) \<noteq> bo)"
            by simp
          have f6: "CHR ''y'' \<noteq> CHR ''i''"
            by blast
          have f7: "CHR ''y'' \<noteq> CHR ''d''"
            by force
          have "CHR ''y'' \<noteq> CHR ''M''"
            by blast
          then show "dsqrt'_imp_time 0 \<lparr>dsqrt'_state_y = s2e (add_prefix p dsqrt'_y_str), dsqrt'_state_L = s2e (add_prefix p ''M''), dsqrt'_state_R = s2e (add_prefix p dsqrt'_R_str)\<rparr> = dsqrt'_imp_time 0 \<lparr>dsqrt'_state_y = s (add_prefix p dsqrt'_y_str), dsqrt'_state_L = s (add_prefix p dsqrt'_L_str), dsqrt'_state_R = (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2\<rparr>"
            using f7 f6 f5 f4 a3 a2 a1 by (smt (z3) fun_upd_other list.inject same_append_eq)
        qed
      next
        case (4 x s2 y xa s2a ya xb s2b yb xc s2c yc xd s2d yd xe s2e ye xf s2f yf xg s2g yg xh s2h yh xi s2i yi xj xk)
        then show ?case
          apply (simp add: dsqrt'_imp_time_acc'' square_imp_correct power2_eq_square)
        proof -
          assume "\<And>v. v = dsqrt'_y_str \<or> v = dsqrt'_L_str \<or> v = dsqrt'_R_str \<or> v = CHR ''i'' # CHR ''n'' # mul_c_str \<or> v = ''diff'' \<or> v = ''cond'' \<or> v = ''M'' \<or> v = ''M2'' \<Longrightarrow> (if v = CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_square_str then 0 else (s(add_prefix p (CHR ''i'' # CHR ''n'' # mul_c_str) := Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''diff'' := s (add_prefix p dsqrt'_R_str) - Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''M'' := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2, add_prefix p (CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_x_str) := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2)) (add_prefix p v)) = s2e (add_prefix p v)"
          then have f1: "\<forall>cs. cs \<noteq> dsqrt'_y_str \<and> cs \<noteq> dsqrt'_L_str \<and> cs \<noteq> dsqrt'_R_str \<and> cs \<noteq> CHR ''i'' # CHR ''n'' # mul_c_str \<and> cs \<noteq> ''diff'' \<and> cs \<noteq> ''cond'' \<and> cs \<noteq> ''M'' \<and> cs \<noteq> ''M2'' \<or> (if cs = CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_square_str then 0 = s2e (add_prefix p cs) else (s(add_prefix p (CHR ''i'' # CHR ''n'' # mul_c_str) := Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''diff'' := s (add_prefix p dsqrt'_R_str) - Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''M'' := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2, add_prefix p (CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_x_str) := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2)) (add_prefix p cs) = s2e (add_prefix p cs))"
            by (smt (z3))
          then have f2: "if dsqrt'_y_str = CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_square_str then 0 = s2e (add_prefix p dsqrt'_y_str) else (s(add_prefix p (CHR ''i'' # CHR ''n'' # mul_c_str) := Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''diff'' := s (add_prefix p dsqrt'_R_str) - Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''M'' := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2, add_prefix p (CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_x_str) := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2)) (add_prefix p dsqrt'_y_str) = s2e (add_prefix p dsqrt'_y_str)"
            by blast
          have f3: "if ''M'' = CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_square_str then 0 = s2e (add_prefix p ''M'') else (s(add_prefix p (CHR ''i'' # CHR ''n'' # mul_c_str) := Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''diff'' := s (add_prefix p dsqrt'_R_str) - Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''M'' := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2, add_prefix p (CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_x_str) := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2)) (add_prefix p ''M'') = s2e (add_prefix p ''M'')"
            using f1 by blast
          have "if dsqrt'_R_str = CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_square_str then 0 = s2e (add_prefix p dsqrt'_R_str) else (s(add_prefix p (CHR ''i'' # CHR ''n'' # mul_c_str) := Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''diff'' := s (add_prefix p dsqrt'_R_str) - Suc (s (add_prefix p dsqrt'_L_str)), add_prefix p ''M'' := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2, add_prefix p (CHR ''s'' # CHR ''q'' # CHR ''u'' # CHR ''a'' # CHR ''r'' # CHR ''e'' # CHR ''.'' # square_x_str) := (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2)) (add_prefix p dsqrt'_R_str) = s2e (add_prefix p dsqrt'_R_str)"
            using f1 by blast
          then show "dsqrt'_imp_time 0 \<lparr>dsqrt'_state_y = s2e (add_prefix p dsqrt'_y_str), dsqrt'_state_L = s2e (add_prefix p ''M''), dsqrt'_state_R = s2e (add_prefix p dsqrt'_R_str)\<rparr> = dsqrt'_imp_time 0 \<lparr>dsqrt'_state_y = s (add_prefix p dsqrt'_y_str), dsqrt'_state_L = (s (add_prefix p dsqrt'_L_str) + s (add_prefix p dsqrt'_R_str)) div 2, dsqrt'_state_R = s (add_prefix p dsqrt'_R_str)\<rparr>"
            using f3 f2 by simp
        qed
      qed
      done

  qed
lemma dsqrt'_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ dsqrt'_prefix) dsqrt'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>  v \<in> vars \<Longrightarrow> \<not> (set dsqrt'_prefix \<subseteq> set v) 
  \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma dsqrt'_IMP_Minus_correct_effects':
  "(invoke_subprogram (p @ dsqrt'_prefix) dsqrt'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>  v \<in> vars \<Longrightarrow> \<not> (prefix dsqrt'_prefix v) 
  \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars
  by (metis prefix_def)

lemma dsqrt'_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) dsqrt'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
     \<lbrakk>t = (dsqrt'_imp_time 0 (dsqrt'_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) dsqrt'_L_str) = 
        dsqrt'_state_L (dsqrt'_imp (dsqrt'_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using dsqrt'_IMP_Minus_correct_time dsqrt'_IMP_Minus_correct_function_1
        dsqrt'_IMP_Minus_correct_effects 
  by auto


lemma dsqrt'_IMP_Minus_correct':
  "\<lbrakk>(invoke_subprogram (p1 @ p2) dsqrt'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (dsqrt'_imp_time 0 (dsqrt'_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) dsqrt'_L_str) = 
        dsqrt'_state_L (dsqrt'_imp (dsqrt'_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using dsqrt'_IMP_Minus_correct_time dsqrt'_IMP_Minus_correct_function_1
        dsqrt'_IMP_Minus_correct_effects' 
  by auto



thm dsqrt_def
record dsqrt_state = dsqrt_state_y :: nat dsqrt_state_ret :: nat 
thm dsqrt'_imp.simps

(* I am testing if I can go farther*)
abbreviation "dsqrt_prefix \<equiv> ''dsqrt.''"
abbreviation "dsqrt_y_str \<equiv> ''y''"
abbreviation "dsqrt_ret_str \<equiv> ''ret''"

abbreviation 
  "dsqrt_IMP_vars \<equiv> {dsqrt_y_str, dsqrt_ret_str}"

(* What I do not like is that I need to track changes is "input variables" *)
definition "dsqrt_imp_state_upd s = (let
    dsqrt'_y = dsqrt_state_y s;
    dsqrt'_L = 0;
    dsqrt'_R = Suc (dsqrt_state_y s);
    
    dsqrt_dsqrt'_state = \<lparr>dsqrt'_state_y = dsqrt'_y, dsqrt'_state_L = dsqrt'_L, dsqrt'_state_R = dsqrt'_R\<rparr>;
    dsqrt'_ret = dsqrt'_imp dsqrt_dsqrt'_state;
    
    dsqrt_ret = dsqrt'_state_L dsqrt'_ret;
    ret = \<lparr>dsqrt_state_y = dsqrt_state_y s, dsqrt_state_ret = dsqrt_ret\<rparr>
  in
    ret)
"
     
fun dsqrt_imp :: "dsqrt_state \<Rightarrow> dsqrt_state" where
  "dsqrt_imp s = 
  (let
    ret = dsqrt_imp_state_upd s
  in
    ret
  )"

declare dsqrt_imp.simps [simp del]

lemma dsqrt_imp_correct:
   "dsqrt_state_ret (dsqrt_imp s) = Discrete.sqrt (dsqrt_state_y s)"
  by (subst dsqrt_imp.simps) (auto simp: dsqrt'_imp_correct dsqrt_def dsqrt_imp_state_upd_def
      Let_def dsqrt_correct[symmetric] split: if_splits)

fun dsqrt_imp_time:: "nat \<Rightarrow> dsqrt_state\<Rightarrow> nat" where
  "dsqrt_imp_time t s = 
    (
      let
        dsqrt'_y = dsqrt_state_y s;
        t = t+2;
        dsqrt'_L = 0;
        t = t+2;
        dsqrt'_R = Suc (dsqrt_state_y s);
        t = t+2;
        
        dsqrt_dsqrt'_state = \<lparr>dsqrt'_state_y = dsqrt'_y, dsqrt'_state_L = dsqrt'_L, dsqrt'_state_R = dsqrt'_R\<rparr>;
        dsqrt'_ret = dsqrt'_imp dsqrt_dsqrt'_state;
        t = t + dsqrt'_imp_time 0 dsqrt_dsqrt'_state;
        
        dsqrt_ret = dsqrt'_state_L dsqrt'_ret;
        t = t+2;
        ret = t
      in
        ret
    )
"

lemmas [simp del] = dsqrt_imp_time.simps

lemma dsqrt_imp_time_acc: "(dsqrt_imp_time (Suc t) s) = Suc (dsqrt_imp_time t s)"
  apply(subst dsqrt_imp_time.simps)
  apply(subst dsqrt_imp_time.simps)
  apply (auto simp add: dsqrt_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)
  done

lemma dsqrt_imp_time_acc_2: "(dsqrt_imp_time x s) = x + (dsqrt_imp_time 0 s)"
  by (induction x arbitrary: s)
     (auto simp add: dsqrt_imp_time_acc dsqrt_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)

thm dsqrt'_imp_time_dsqrt'_imp_time'

fun dsqrt_imp_time' :: "nat \<Rightarrow> nat" where
  "dsqrt_imp_time' y = 8 + dsqrt'_imp_time' y 0 (Suc y)"

(* Move up *)
lemma dsqrt'_imp_time'_non_rec_bound: 
  assumes "L < R" shows "dsqrt'_imp_time' y L R \<le> 60 + (63 * Discrete.log R + 10 * (Discrete.log R)^2)"
proof-
  have "dsqrt'_imp_time' y L R \<le> (23 + 20 + 10 * Suc (Discrete.log R)) * Suc (Discrete.log (R - L)) + 7"
    apply (rule le_trans[OF dsqrt'_imp_time'_log[OF assms, of y]]) 
    apply (rule add_le_mono1)
    apply (rule mult_le_mono1)
    using square_imp_time'_non_rec_bound[of R] by simp
  also have "\<dots> = (43 + 10 * Suc (Discrete.log R)) * Suc (Discrete.log (R - L)) + 7"
    by simp
  also have "\<dots> \<le> (43 + 10 * Suc (Discrete.log R)) * Suc (Discrete.log R) + 7"
    by (simp add: Discrete.log_le_iff)
  finally show ?thesis
    by (auto simp add: power2_eq_square algebra_simps)
qed

lemma "dsqrt'_state_L s < dsqrt'_state_R s \<Longrightarrow> dsqrt'_imp_time t s \<le> t + 
  60 + (63 * Discrete.log (dsqrt'_state_R s) + 10 * (Discrete.log (dsqrt'_state_R s))^2)"
  by (simp add: dsqrt'_imp_time'_non_rec_bound dsqrt'_imp_time_dsqrt'_imp_time')

lemma dsqrt_imp_time_dsqrt_imp_time': "dsqrt_imp_time t s = t + dsqrt_imp_time' (dsqrt_state_y s)"
  by (subst dsqrt_imp_time.simps) (auto simp add: dsqrt_imp_time_acc_2 dsqrt'_imp_time_dsqrt'_imp_time')

lemma dsqrt_imp_time'_non_rec_bound: "dsqrt_imp_time' y \<le> 141 + (83 * Discrete.log y + 10 * (Discrete.log y)\<^sup>2)"
proof-
  have "dsqrt_imp_time' y \<le> 68 + (63 * Discrete.log (Suc y) + 10 * (Discrete.log (Suc y))^2)"
    by (auto simp add: dsqrt'_imp_time'_non_rec_bound)
  also have "\<dots> \<le> 131 + (63 * Discrete.log y + 10 * (Discrete.log (Suc y))^2)"
    by simp (metis dlog_Suc_bound le_refl mult_Suc_right mult_le_mono)
  also have "\<dots> \<le> 131 + (63 * Discrete.log y + 10 * (Suc (Discrete.log y))^2)"
    by (simp add: dlog_Suc_bound)
  also have "\<dots> = 131 + (63 * Discrete.log y + 10 * (1 + 2 * Discrete.log y + (Discrete.log y)^2))"
    by (smt (verit, del_insts) Suc_eq_plus1_left add.assoc add.commute mult.assoc mult_1 power2_sum power_one)
  also have "\<dots> \<le> 141 + (83 * Discrete.log y + 10 * (Discrete.log y)^2)"
    by simp
  finally show ?thesis .
qed


definition dsqrt_IMP_Minus where
"dsqrt_IMP_Minus \<equiv>
  (
    (dsqrt'_pref @ dsqrt'_y_str) ::= A (V dsqrt_y_str);;
    (dsqrt'_pref @ dsqrt'_L_str) ::= A (N 0);;
    (dsqrt'_pref @ dsqrt'_R_str) ::= (V dsqrt_y_str \<oplus> N 1);;
    
    invoke_subprogram dsqrt'_pref dsqrt'_IMP_Minus;;

    dsqrt_ret_str ::= A (V (dsqrt'_pref @ dsqrt'_L_str))
  )"

definition "dsqrt_imp_to_HOL_state p s =
  \<lparr>dsqrt_state_y = (s (add_prefix p dsqrt_y_str)), dsqrt_state_ret = (s (add_prefix p dsqrt_ret_str))\<rparr>"


lemma dsqrt_IMP_Minus_correct_function: 
  "(invoke_subprogram p dsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p dsqrt_ret_str) = dsqrt_state_ret (dsqrt_imp (dsqrt_imp_to_HOL_state p s))"
  apply(subst dsqrt_imp.simps)
  apply(simp only: dsqrt_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(all \<open>erule dsqrt'_IMP_Minus_correct[where vars = "dsqrt_IMP_vars"]\<close>) (* Probably do not need this here *)
   apply simp
  apply (drule AssignD)+
  apply (auto simp add: dsqrt_imp_state_upd_def dsqrt_imp_to_HOL_state_def dsqrt'_imp_to_HOL_state_def)
  done

lemma dsqrt_IMP_Minus_correct_time: 
  "(invoke_subprogram p dsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = dsqrt_imp_time 0 (dsqrt_imp_to_HOL_state p s)"
  apply(subst dsqrt_imp_time.simps)
  apply(simp only: dsqrt_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(all \<open>erule dsqrt'_IMP_Minus_correct[where vars = "dsqrt_IMP_vars"]\<close>) (* Probably do not need this here *)
   apply simp
  apply (drule AssignD)+
  apply (auto simp add: dsqrt_imp_state_upd_def dsqrt_imp_to_HOL_state_def dsqrt'_imp_to_HOL_state_def)
  done

lemma dsqrt_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ dsqrt_pref) dsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>  v \<in> vars 
  \<Longrightarrow> \<not> (set dsqrt_pref \<subseteq> set v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma dsqrt_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) dsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
     \<lbrakk>t = (dsqrt_imp_time 0 (dsqrt_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) dsqrt_ret_str) = 
        dsqrt_state_ret (dsqrt_imp (dsqrt_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using dsqrt_IMP_Minus_correct_time dsqrt_IMP_Minus_correct_function
        dsqrt_IMP_Minus_correct_effects 
  by auto

term prod_encode
term prod_decode

(* Triangular root *)

(* Proofs in here are ugly, look at again, I also do quite a lot by just doing it on reals and transfering back *)
lemma sqrt_power2_iff_eq: "x \<ge> 0 \<Longrightarrow> y\<ge>0\<Longrightarrow> sqrt x = y \<longleftrightarrow> x = y^2" by auto

lemma triangle_invert_real: "n\<ge>0 \<Longrightarrow> (sqrt (8*(n*(n+1) / 2)+1) - 1) / 2 = n"
proof-
  have s: "(8*(n*(n+1) / 2)+1) = (2 * n + 1)^2" if "n\<ge>0"
    using that by (auto simp add: power2_eq_square distrib_left mult.commute)
  have "sqrt (8*(n*(n+1) / 2)+1) = 2*n + 1" if "n\<ge>0"
    apply (subst sqrt_power2_iff_eq)
    using that apply simp
    using that apply simp
    using that s apply simp
    done
  then show ?thesis if "n\<ge>0"
    using that by auto 
qed

lemma sqrt_Discrete_sqrt: "nat (floor (sqrt n)) = Discrete.sqrt n"
  apply (rule antisym)
  apply (rule le_sqrtI)
  apply (smt (verit, ccfv_threshold) of_int_floor_le of_nat_0_le_iff of_nat_le_of_nat_power_cancel_iff
      of_nat_nat real_less_lsqrt real_sqrt_ge_0_iff zero_le_floor)
  apply (rule sqrt_leI)
  by (simp add: le_nat_floor real_le_rsqrt)
  
lemma step: "nat (floor (sqrt (8*n + 1))) = (Discrete.sqrt (8*n + 1))"
proof -
  have "\<And>n na. real (numeral n * na) = numeral n * real na"
    by simp
  then show ?thesis
    by (metis One_nat_def add.commute add_0 of_nat_Suc plus_nat.simps(2) sqrt_Discrete_sqrt)
qed
lemma step2: "nat (floor (sqrt ((8*n + 1)) -1)) = (Discrete.sqrt (8*n + 1) -1)"
  by (simp add: Primitives_IMP_Minus_Time.step nat_diff_distrib')

lemma divide2_div2: "nat (floor (n/2)) = n div 2"
  by linarith
lemma divide2_div2': "nat (floor (n/2)) = nat (floor (n::real)) div 2"
  by linarith

lemma step3: "nat (floor (((sqrt (8*n + 1)) -1) /2))  = (Discrete.sqrt (8*n + 1) -1) div 2"
  apply (subst divide2_div2')
  using step2 by presburger

lemma triangle_invert_real_typ: "(sqrt (8*(n*(n+1) / 2)+1) - 1) / 2 = (n::nat)"
  using triangle_invert_real by simp

lemma triangle_invert_real_typ': "nat (floor ((sqrt (8*(n*(n+1) / 2)+1) - 1) / 2)) = (n::nat)"
  using triangle_invert_real by simp

term triangle

definition "tsqrt n \<equiv> (Discrete.sqrt (8*n + 1) - 1) div 2"

lemma tsqrt_0[simp]: "tsqrt 0 = 0"
  by code_simp
lemma tsqrt_1[simp]: "tsqrt 1 = 1"
  by code_simp
lemma tsqrt_2[simp]: "tsqrt 2 = 1"
  by code_simp

lemma tsqrt_correct[simp]: "tsqrt (triangle n) = n"
proof(unfold triangle_def tsqrt_def)
  have s: "real (n * Suc n div 2) = real n * (real n + 1) / 2"
    by (smt (verit, del_insts) Multiseries_Expansion.intyness_1 add.commute double_gauss_sum gauss_sum id_apply nat_1_add_1 nonzero_mult_div_cancel_left of_nat_Suc of_nat_eq_id of_nat_mult plus_1_eq_Suc)
  show "(Discrete.sqrt (8 * (n * Suc n div 2) + 1) - 1) div 2 = n"
apply (subst step3[symmetric]) apply (subst s)
    using triangle_invert_real_typ' by simp
qed

lemma mono_tsqrt: "mono tsqrt"
  unfolding tsqrt_def
  apply (rule monoI) 
  unfolding tsqrt_def 
  by simp (meson Suc_le_mono diff_le_mono div_le_mono le_less mono_sqrt' mult_le_mono)
lemma mono_tsqrt': "x\<le>y \<Longrightarrow> tsqrt x \<le> tsqrt y"
  using mono_tsqrt by (drule monoD)

(* Experiment: Defining "inverse" triangle function by searching biggest element which produces smaller triangle number.
  Should give exactly "Rounded down triangular root". Based on Discrete.sqrt.
   maybe an interesting student topic? Inverting "general" functions this way and generate code.

  So far I did not continue looking at this much more
*)

definition "tsqrt_alt n \<equiv> Max {m. triangle m \<le> n}"

lemma tsqrt_alt_aux:
  fixes n :: nat
  shows "finite {m. triangle m \<le> n}" and "{m. triangle m \<le> n} \<noteq> {}"
proof -
  { fix m
    assume "triangle m \<le> n"
    then have "m \<le> n"
      by (cases m) (simp_all)
  } note ** = this
  then have "{m. triangle m \<le> n} \<subseteq> {m. m \<le> n}" by auto
  then show "finite {m. triangle m \<le> n}" by (rule finite_subset) rule
  have "triangle 0 \<le> n" by simp
  then show *: "{m. triangle m \<le> n} \<noteq> {}" by blast
qed

lemma tsqrt_alt_unique:
  assumes "triangle m \<le> n" "n < triangle (Suc m)"
  shows   "tsqrt_alt n = m"
proof -
  have "m' \<le> m" if "triangle m' \<le> n" for m'
  proof -
    note that
    also note assms(2)
    finally have "m' < Suc m" (* Apparently I already have some connection to tsqrt here *)
      by (metis le_neq_implies_less less_or_eq_imp_le mono_tsqrt' nat_neq_iff tsqrt_correct)
    thus "m' \<le> m" by simp
  qed
  with \<open>triangle m \<le> n\<close> tsqrt_alt_aux[of n] show ?thesis unfolding tsqrt_alt_def
    by (intro antisym Max.boundedI Max.coboundedI) simp_all
qed


lemma triangle_nat_le_imp_le:
  fixes m n :: nat
  assumes "triangle m \<le> n"
  shows "m \<le> n"
proof (cases m)
  case 0
  then show ?thesis 
    by simp
next
  case (Suc nat)
  then show ?thesis 
    using assms by auto
qed

(* Real proof *)
lemma triangle_nat_le_eq_le: "triangle m \<le> triangle n \<longleftrightarrow> m \<le> n"
  for m n :: nat
  by (metis linorder_le_cases mono_tsqrt' tsqrt_correct verit_la_disequality)

(* basically linear search, delete this code equation once you have a better one *)
lemma tsqrt_alt_code_1 [code]: "tsqrt_alt n = Max (Set.filter (\<lambda>m. triangle m \<le> n) {0..n})"
proof -
  from triangle_nat_le_imp_le [of _ n] have "{m. m \<le> n \<and> triangle m \<le> n} = {m. triangle m \<le> n}" by auto
  then show ?thesis by (simp add: tsqrt_alt_def Set.filter_def)
qed

lemma tsqrt_alt_inverse_triangle [simp]: "tsqrt_alt (triangle n) = n"
proof -
  have "{m. m \<le> n} \<noteq> {}" by auto
  then have "Max {m. m \<le> n} \<le> n" by auto
  then show ?thesis
    by (auto simp add: tsqrt_alt_def triangle_nat_le_eq_le intro: antisym)
qed

lemma tsqrt_alt_zero [simp]: "tsqrt_alt 0 = 0"
  using tsqrt_alt_inverse_triangle [of 0] by simp

lemma tsqrt_alt_one [simp]: "tsqrt_alt 1 = 1"
  using tsqrt_alt_inverse_triangle [of 1] by simp

lemma mono_tsqrt_alt: "mono tsqrt_alt"
proof
  fix m n :: nat
  have *: "0 * 0 \<le> m" by simp
  assume "m \<le> n"
  then show "tsqrt_alt m \<le> tsqrt_alt n"
    apply (auto intro!: Max_mono \<open>0 * 0 \<le> m\<close> finite_less_ub simp add: tsqrt_alt_def triangle_nat_le_imp_le)
    apply (metis triangle_0 zero_le)
    done
qed

lemma mono_tsqrt_alt_': "m \<le> n \<Longrightarrow> tsqrt_alt m \<le> tsqrt_alt n"
  using mono_tsqrt_alt unfolding mono_def by auto

lemma tsqrt_alt_greater_zero_iff [simp]: "tsqrt_alt n > 0 \<longleftrightarrow> n > 0"
proof -
  have *: "0 < Max {m. triangle m \<le> n} \<longleftrightarrow> (\<exists>a\<in>{m. triangle m \<le> n}. 0 < a)"
    by (rule Max_gr_iff) (fact tsqrt_alt_aux)+
  show ?thesis
  proof
    assume "0 < tsqrt_alt n"
    then have "0 < Max {m. triangle m \<le> n}" by (simp add: tsqrt_alt_def)
    with * show "0 < n" by (auto dest: triangle_nat_le_imp_le)
  next
    assume "0 < n"
    then have "triangle 1 \<le> n \<and> 0 < (1::nat)" by simp
    then have "\<exists>q. triangle q \<le> n \<and> 0 < q" ..
    with * have "0 < Max {m. triangle m \<le> n}" by blast
    then show "0 < tsqrt_alt n" by (simp add: tsqrt_alt_def)
  qed
qed

(* No idea what this proof does, find out sometime :) *)
lemma tsqrt_alt_triangle_le [simp]: "triangle (tsqrt_alt n) \<le> n" (* FIXME tune proof *)
proof (cases "n > 0")
  case False then show ?thesis by simp
next
  case True then have "tsqrt_alt n > 0" by simp
  then have "mono (times (Max {m. triangle m \<le> n}))" by (auto intro: mono_times_nat simp add: tsqrt_alt_def)
  then have *: "Max {m. triangle m \<le> n} * Max {m. triangle m \<le> n} = Max (times (Max {m. triangle m \<le> n}) ` {m. triangle m \<le> n})"
    using tsqrt_alt_aux [of n] by (rule mono_Max_commute)
  have "\<And>a. a * a \<le> n \<Longrightarrow> Max {m. m * m \<le> n} * a \<le> n"
  proof -
    fix q
    assume "q * q \<le> n"
    show "Max {m. m * m \<le> n} * q \<le> n"
    proof (cases "q > 0")
      case False then show ?thesis by simp
    next
      case True then have "mono (times q)" by (rule mono_times_nat)
      then have "q * Max {m. m * m \<le> n} = Max (times q ` {m. m * m \<le> n})"
        using sqrt_aux [of n] by (auto simp add: power2_eq_square intro: mono_Max_commute)
      then have "Max {m. m * m \<le> n} * q = Max (times q ` {m. m * m \<le> n})" by (simp add: ac_simps)
      moreover have "finite ((*) q ` {m. m * m \<le> n})"
        by (metis (mono_tags) finite_imageI finite_less_ub le_square)
      moreover have "\<exists>x. x * x \<le> n"
        by (metis \<open>q * q \<le> n\<close>)
      ultimately show ?thesis
        by simp (metis \<open>q * q \<le> n\<close> le_cases mult_le_mono1 mult_le_mono2 order_trans)
    qed
  qed
  then have "Max ((*) (Max {m. m * m \<le> n}) ` {m. m * m \<le> n}) \<le> n"
    apply (subst Max_le_iff)
      apply (metis (mono_tags) finite_imageI finite_less_ub le_square)
     apply auto
    apply (metis le0 mult_0_right)
    done
  with * show ?thesis 
    using tsqrt_alt_aux Max_in by (auto simp add: tsqrt_alt_def)
qed

lemma tsqrt_alt_le: "tsqrt_alt n \<le> n"
  using tsqrt_alt_aux [of n] by (auto simp add: tsqrt_alt_def intro: triangle_nat_le_imp_le)

lemma Suc_tsqrt_alt_triangle_gt: "n < triangle (Suc (tsqrt_alt n))"
  using Max_ge[OF tsqrt_alt_aux(1), of "tsqrt_alt n + 1" n]
  by (cases "n < triangle (Suc (tsqrt_alt n))") (simp_all add: tsqrt_alt_def)

lemma le_tsqrt_alt_iff: "x \<le> tsqrt_alt y \<longleftrightarrow> triangle x \<le> y"
proof -
  have "x \<le> tsqrt_alt y \<longleftrightarrow> (\<exists>z. triangle z \<le> y \<and> x \<le> z)"    
    using Max_ge_iff[OF tsqrt_alt_aux, of x y] by (simp add: tsqrt_alt_def)
  also have "\<dots> \<longleftrightarrow> triangle x \<le> y"
  proof safe
    fix z assume "x \<le> z" "triangle z \<le> y"
    thus "triangle x \<le> y" by (intro le_trans[of "triangle x" "triangle z" y]) (simp_all add: triangle_nat_le_eq_le)
  qed auto
  finally show ?thesis .
qed
  
lemma le_tsqrt_altI: "triangle x \<le> y \<Longrightarrow> x \<le> tsqrt_alt y"
  by (simp add: le_tsqrt_alt_iff)

lemma tsqrt_alt_le_iff: "tsqrt_alt y \<le> x \<longleftrightarrow> (\<forall>z. triangle z \<le> y \<longrightarrow> z \<le> x)"
  using Max.bounded_iff[OF tsqrt_alt_aux] by (simp add: tsqrt_alt_def)

lemma sqrt_leI:
  "(\<And>z. triangle z \<le> y \<Longrightarrow> z \<le> x) \<Longrightarrow> tsqrt_alt y \<le> x"
  by simp
    
lemma triangle_less_imp_less: "triangle x < triangle y \<Longrightarrow> 0 \<le> y \<Longrightarrow> x < y"
  by (simp add: less_le_not_le triangle_nat_le_eq_le)
lemma tsqrt_alt_Suc:
  "tsqrt_alt (Suc n) = (if \<exists>m. Suc n = triangle m then Suc (tsqrt_alt n) else tsqrt_alt n)"
proof cases
  assume "\<exists> m. Suc n = triangle m"
  then obtain m where m_def: "Suc n = triangle m" by blast
  then have lhs: "tsqrt_alt (Suc n) = m" by simp
  from m_def tsqrt_alt_triangle_le[of n] 
    have "triangle (tsqrt_alt n) < triangle m" by linarith
  with triangle_less_imp_less have lt_m: "tsqrt_alt n < m" by blast
  from m_def Suc_tsqrt_alt_triangle_gt[of "n"]
    have "triangle m \<le> triangle (Suc(tsqrt_alt n))"
      by linarith
  with triangle_nat_le_eq_le have "m \<le> Suc (tsqrt_alt n)" by blast
  with lt_m have "m = Suc (tsqrt_alt n)" by simp
  with lhs m_def show ?thesis by metis
next
  assume asm: "\<not> (\<exists> m. Suc n = triangle m)"
  hence "Suc n \<noteq> triangle (tsqrt_alt (Suc n))" by simp
  with tsqrt_alt_triangle_le[of "Suc n"] 
    have "tsqrt_alt (Suc n) \<le> tsqrt_alt n" by (intro le_tsqrt_altI) linarith
  moreover have "tsqrt_alt (Suc n) \<ge> tsqrt_alt n"
    by (intro monoD[OF mono_tsqrt_alt]) simp_all
  ultimately show ?thesis using asm by simp
qed

(* Continue with direct definition, once again by moving to reals*)

lemma triangle_tsqrt_le_real: 
  "nat (floor (((sqrt (8 * n + 1) - 1) / 2) * ((1 + ((sqrt (8 * n + 1) - 1) / 2)) / 2))) \<le> n"
  by (auto simp add: triangle_def algebra_simps divide_simps)

lemma tsqrt_real: "tsqrt n = nat (floor (((sqrt (8 * n + 1) - 1) / 2)))"
  unfolding tsqrt_def
  apply (auto simp add: algebra_simps divide_simps field_simps)
  by (metis One_nat_def add.commute divide2_div2' mult.commute plus_1_eq_Suc step2)

lemma triangle_tsqrt_real_pre:
  "triangle (tsqrt n) = nat (floor ((nat (floor (((sqrt (8 * n + 1) - 1) / 2))) * nat (floor (1 + ((sqrt (8 * n + 1) - 1) / 2)))) / 2))"
  unfolding triangle_def tsqrt_real divide2_div2
  apply (auto simp add: algebra_simps divide_simps field_simps)
  by (smt (verit, best) Suc_eq_plus1 add_mult_distrib2 floor_diff_of_int int_nat_eq
      nat_int_comparison(1) nat_mult_1_right of_int_1 of_nat_1 of_nat_add plus_1_eq_Suc real_average_minus_first)

lemma triangle_tsqrt_le_real_bound: "nat (floor ((nat (floor (((sqrt (8 * n + 1) - 1) / 2))) * nat (floor (1 + ((sqrt (8 * n + 1) - 1) / 2)))) / 2))
  \<le> nat (floor (((sqrt (8 * n + 1) - 1) / 2) * ((1 + ((sqrt (8 * n + 1) - 1) / 2)) / 2)))"
  by (metis div_le_mono divide2_div2' le_mult_nat_floor times_divide_eq_right triangle_invert_real_typ triangle_invert_real_typ')

lemma triangle_tsqrt_le: "triangle (tsqrt n) \<le> n"
  unfolding triangle_tsqrt_real_pre
  using triangle_tsqrt_le_real triangle_tsqrt_le_real_bound
  by (meson le_trans)
  
lemma tsqrt_unique:
  assumes "triangle m \<le> n" "n < triangle (Suc m)"
  shows "tsqrt n = m"
  using assms triangle_tsqrt_le tsqrt_correct
  by (metis le_SucE le_antisym mono_tsqrt' nat_less_le)

lemma tsqrt_tsqrt: "tsqrt_alt n = tsqrt n"
  by (metis Suc_tsqrt_alt_triangle_gt tsqrt_unique tsqrt_alt_triangle_le)

lemma tsqrt_Suc:
  "tsqrt (Suc n) = (if \<exists>m. Suc n = triangle m then Suc (tsqrt n) else tsqrt n)"
  using tsqrt_alt_Suc tsqrt_tsqrt by force


(* Use triangular root to define fst and snd (with polynomial runtime) *)

definition "fst'_nat p \<equiv> p - triangle (tsqrt p)"

lemma fst'_nat_correct: "fst'_nat (prod_encode (m,n)) = m"
  unfolding prod_encode_def apply simp unfolding fst'_nat_def
  by (metis add.commute add_diff_cancel_left' le_add1 less_add_Suc2 nat_add_left_cancel_less triangle_Suc tsqrt_unique)

definition "snd'_nat p \<equiv> tsqrt p - fst'_nat p"

lemma snd'_nat_correct: "snd'_nat (prod_encode (m,n)) = n"
  unfolding prod_encode_def apply simp unfolding snd'_nat_def
  using fst'_nat_correct 
  by (metis add.commute add_diff_cancel_left' fst'_nat_def le_add1 less_add_Suc2 nat_add_left_cancel_less triangle_Suc tsqrt_unique)

(* Refinement... *)

record tsqrt_state = tsqrt_state_y :: nat tsqrt_state_ret :: nat 
(* I am testing if I can go farther, names exactly as in dsqrt, see if prefix work*)
abbreviation "tsqrt_prefix \<equiv> ''tsqrt.''"
abbreviation "tsqrt_y_str \<equiv> ''y''"
abbreviation "tsqrt_ret_str \<equiv> ''ret''"

abbreviation 
  "tsqrt_IMP_vars \<equiv> {tsqrt_y_str, tsqrt_ret_str}"

thm tsqrt_def
term A

(* What I do not like is that I need to track changes is "input variables" *)
definition "tsqrt_imp_state_upd s = (let
    tsqrt_mul_a = tsqrt_state_y s;
    tsqrt_mul_b = 8;
    tsqrt_mul_c = 0;
    tsqrt_mul_state = \<lparr>mul_a = tsqrt_mul_a, mul_b = tsqrt_mul_b, mul_c = tsqrt_mul_c\<rparr>;
    mul_ret = mul_imp tsqrt_mul_state;
    
    tsqrt_y = mul_c mul_ret + 1;

    tsqrt_dsqrt_y = tsqrt_y;
    tsqrt_dsqrt_ret = 0;
    tsqrt_dsqrt_state = \<lparr>dsqrt_state_y = tsqrt_dsqrt_y, dsqrt_state_ret = tsqrt_dsqrt_ret\<rparr>;
    dsqrt_ret = dsqrt_imp tsqrt_dsqrt_state;

    tsqrt_y = dsqrt_state_ret dsqrt_ret - 1;
    tsqrt_ret = tsqrt_y div 2;
    ret = \<lparr>tsqrt_state_y = tsqrt_y, tsqrt_state_ret = tsqrt_ret\<rparr>
  in
    ret)
"

fun tsqrt_imp :: "tsqrt_state \<Rightarrow> tsqrt_state" where
  "tsqrt_imp s = 
  (let
    ret = tsqrt_imp_state_upd s
  in
    ret
  )"

declare tsqrt_imp.simps [simp del]

thm dsqrt_correct
lemma tsqrt_imp_correct:
   "tsqrt_state_ret (tsqrt_imp s) = tsqrt (tsqrt_state_y s)"
  by (subst tsqrt_imp.simps) (auto simp: dsqrt_imp_correct tsqrt_def tsqrt_imp_state_upd_def
      Let_def mul_imp_correct mult.commute split: if_splits)

fun tsqrt_imp_time:: "nat \<Rightarrow> tsqrt_state\<Rightarrow> nat" where
  "tsqrt_imp_time t s = 
    (
      let
        tsqrt_mul_a = tsqrt_state_y s;
        t = t+2;
        tsqrt_mul_b = 8;
        t = t+2;
        tsqrt_mul_c = 0;
        t = t+2;
        tsqrt_mul_state = \<lparr>mul_a = tsqrt_mul_a, mul_b = tsqrt_mul_b, mul_c = tsqrt_mul_c\<rparr>;
        mul_ret = mul_imp tsqrt_mul_state;
        t = t+ mul_imp_time 0 tsqrt_mul_state;
        
        tsqrt_y = mul_c mul_ret + 1;
        t = t+2;
    
        tsqrt_dsqrt_y = tsqrt_y;
        t = t+2;
        tsqrt_dsqrt_ret = 0;
        t = t+2;
        tsqrt_dsqrt_state = \<lparr>dsqrt_state_y = tsqrt_dsqrt_y, dsqrt_state_ret = tsqrt_dsqrt_ret\<rparr>;
        dsqrt_ret = dsqrt_imp tsqrt_dsqrt_state;
        t = t + dsqrt_imp_time 0 tsqrt_dsqrt_state;
    
        tsqrt_y = dsqrt_state_ret dsqrt_ret - 1;
        t = t+2;
        tsqrt_ret = tsqrt_y div 2;
        t = t+2;
        ret = t
      in
        ret
    )
"

lemmas [simp del] = tsqrt_imp_time.simps

lemma tsqrt_imp_time_acc: "(tsqrt_imp_time (Suc t) s) = Suc (tsqrt_imp_time t s)"
  apply(subst tsqrt_imp_time.simps)
  apply(subst tsqrt_imp_time.simps)
  apply (auto simp add: tsqrt_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)
  done

lemma tsqrt_imp_time_acc_2: "(tsqrt_imp_time x s) = x + (tsqrt_imp_time 0 s)"
  by (induction x arbitrary: s)
     (auto simp add: tsqrt_imp_time_acc tsqrt_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)

fun tsqrt_imp_time' :: "nat \<Rightarrow> nat" where
  "tsqrt_imp_time' y = 16 + mul_imp_time' 8 + dsqrt_imp_time' (8*y+1)"


lemma tsqrt_imp_time_tsqrt_imp_time': "tsqrt_imp_time t s = t + tsqrt_imp_time' (tsqrt_state_y s)"
  by (subst tsqrt_imp_time.simps) (auto simp add: tsqrt_imp_time_acc_2 dsqrt_imp_time_dsqrt_imp_time' 
      mul_imp_time_mul_imp_time' mul_imp_correct Let_def mult.commute)

lemma tsqrt_imp_time'_non_rec_bound: "tsqrt_imp_time' y \<le> 691 + (163 * Discrete.log y + 10 * (Discrete.log y)\<^sup>2)"
proof-
  have "tsqrt_imp_time' y = 58 + dsqrt_imp_time' (8*y+1)"
    by code_simp
  also have "\<dots> \<le> 58 + (141 + (83 * Discrete.log (8*y+1) + 10 * (Discrete.log (8*y+1))\<^sup>2))"
    using dsqrt_imp_time'_non_rec_bound by auto
  also have "\<dots> \<le> 282 + (83 * Discrete.log (8*y) + 10 * (Discrete.log (8*y+1))\<^sup>2)"
    by simp (metis dlog_Suc_bound le_refl mult_Suc_right mult_le_mono)
  also have "\<dots> \<le> 282 + (83 * (3 + Discrete.log y) + 10 * (Discrete.log (8*y+1))\<^sup>2)"
  proof- (* \<le> because of y=0 case*)
    have s: "8*y = (2*(2*(2*y)))" by simp
    have "Discrete.log (8*y) = 3 + Discrete.log y" if "y>0"
      apply (subst s)
      using that apply (subst log_twice, simp)+
      by presburger
    thus ?thesis
      by force
  qed
  also have "\<dots> = 531 + (83 * Discrete.log y + 10 * (Discrete.log (8*y+1))\<^sup>2)"
    by simp
  also have "\<dots> \<le> 531 + (83 * Discrete.log y + 10 * (1 + Discrete.log (8*y))\<^sup>2)"
    by (simp add: dlog_Suc_bound)
  also have "\<dots> \<le> 531 + (83 * Discrete.log y + 10 * (4 + Discrete.log y)\<^sup>2)"
  proof-
    have s: "8*y = (2*(2*(2*y)))" by simp
    have "Discrete.log (8*y) = 3 + Discrete.log y" if "y>0"
      apply (subst s)
      using that apply (subst log_twice, simp)+
      by presburger
    thus ?thesis
      by force
  qed
  also have "\<dots> = 531 + (83 * Discrete.log y + 10 * (Discrete.log y)^2 + 80 * Discrete.log y + 160)"
    by (auto simp add: power2_eq_square algebra_simps)
  also have "\<dots> = 691 + (163 * Discrete.log y + 10 * (Discrete.log y)^2)"
    by simp
  finally show ?thesis .
qed

definition tsqrt_IMP_Minus where
"tsqrt_IMP_Minus \<equiv>
  (
    (mul_prefix @ mul_a_str) ::= A (V tsqrt_y_str);;
    (mul_prefix @ mul_b_str) ::= A (N 8);;
    (mul_prefix @ mul_c_str) ::= A (N 0);;
    invoke_subprogram mul_prefix mul_IMP_minus;;

    \<comment> \<open>Could save an assignment here, combine with next one\<close>
    tsqrt_y_str ::= (V (mul_prefix @ mul_c_str) \<oplus> N 1);;

    (dsqrt_prefix @ dsqrt_y_str) ::= A (V tsqrt_y_str);;
    (dsqrt_prefix @ dsqrt_ret_str) ::= A (N 0);;
    invoke_subprogram dsqrt_prefix dsqrt_IMP_Minus;;

    tsqrt_y_str ::= (V (dsqrt_prefix @ dsqrt_ret_str) \<ominus> N 1);;
    tsqrt_ret_str ::= (V tsqrt_y_str\<then>)
  )"

definition "tsqrt_imp_to_HOL_state p s =
  \<lparr>tsqrt_state_y = (s (add_prefix p tsqrt_y_str)), tsqrt_state_ret = (s (add_prefix p tsqrt_ret_str))\<rparr>"



(* Use the new style correctness lemma to be safe, replace the old ones later, also we need to do
  a standardization pass for naming *)
lemma mul_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ mul_pref) mul_IMP_minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>  v \<in> vars 
  \<Longrightarrow> \<not> (prefix mul_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars
  using prefix_def by blast

lemma mul_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) mul_IMP_minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (mul_imp_time 0 (mul_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) mul_c_str) = 
        mul_c (mul_imp (mul_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using mul_IMP_minus_correct_time mul_IMP_minus_correct_function
        mul_IMP_Minus_correct_effects 
  by auto


lemma tsqrt_IMP_Minus_correct_function: 
  "(invoke_subprogram p tsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p tsqrt_ret_str) = tsqrt_state_ret (tsqrt_imp (tsqrt_imp_to_HOL_state p s))"
  apply(subst tsqrt_imp.simps)
  apply(simp only: tsqrt_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(erule mul_IMP_Minus_correct[where vars = "tsqrt_IMP_vars"])
   apply auto[]
  apply(erule dsqrt_IMP_Minus_correct[where vars = "tsqrt_IMP_vars"])
   apply auto[]
  apply (drule AssignD)+
   apply (auto simp add: tsqrt_imp_state_upd_def tsqrt_imp_to_HOL_state_def dsqrt_imp_to_HOL_state_def
      mul_imp_to_HOL_state_def Let_def)
  done

lemma tsqrt_IMP_Minus_correct_time: 
  "(invoke_subprogram p tsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = tsqrt_imp_time 0 (tsqrt_imp_to_HOL_state p s)"
  apply(subst tsqrt_imp_time.simps)
  apply(simp only: tsqrt_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(erule mul_IMP_Minus_correct[where vars = "tsqrt_IMP_vars"])
   apply auto[]
  apply(erule dsqrt_IMP_Minus_correct[where vars = "tsqrt_IMP_vars"])
   apply auto[]
  apply (drule AssignD)+
   apply (auto simp add: tsqrt_imp_state_upd_def tsqrt_imp_to_HOL_state_def dsqrt_imp_to_HOL_state_def
      mul_imp_to_HOL_state_def Let_def)
  done

lemma tsqrt_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ tsqrt_pref) tsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>  v \<in> vars 
  \<Longrightarrow> \<not> (prefix tsqrt_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma tsqrt_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) tsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (tsqrt_imp_time 0 (tsqrt_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) tsqrt_ret_str) = 
        tsqrt_state_ret (tsqrt_imp (tsqrt_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using tsqrt_IMP_Minus_correct_time tsqrt_IMP_Minus_correct_function
        tsqrt_IMP_Minus_correct_effects 
  by auto



(* Another test, use input/output same and have "hidden" internal variable not recorded *)
record fst'_state = fst'_state_p :: nat
(* I am testing if I can go farther, names exactly as in dsqrt, see if prefix work*)
abbreviation "fst'_prefix \<equiv> ''fst'.''"
abbreviation "fst'_p_str \<equiv> ''p''"
abbreviation "fst'_internal_str \<equiv> ''internal''"

abbreviation 
  "fst'_IMP_vars \<equiv> {fst'_p_str, fst'_internal_str}"

(* Copying directly from function outputs *)
definition "fst'_imp_state_upd s = (let
    fst'_tsqrt_y = fst'_state_p s;
    fst'_tsqrt_ret = 0;
    fst'_tsqrt_state = \<lparr>tsqrt_state_y = fst'_tsqrt_y, tsqrt_state_ret = fst'_tsqrt_ret\<rparr>;
    fst'_tsqrt_ret = tsqrt_imp fst'_tsqrt_state;
    
    fst'_triangle_a = tsqrt_state_ret fst'_tsqrt_ret;
    fst'_triangle_triangle = 0;
    fst'_triangle_state = \<lparr>triangle_a = fst'_triangle_a, triangle_triangle = fst'_triangle_triangle\<rparr>;
    fst'_triangle_ret = triangle_imp fst'_triangle_state;

    fst'_p = fst'_state_p s - triangle_triangle fst'_triangle_ret;
    
    ret = \<lparr>fst'_state_p = fst'_p\<rparr>
  in
    ret)
"

fun fst'_imp :: "fst'_state \<Rightarrow> fst'_state" where
  "fst'_imp s = 
  (let
    ret = fst'_imp_state_upd s
  in
    ret
  )"

declare fst'_imp.simps [simp del]

lemma fst'_imp_correct:
   "fst'_state_p (fst'_imp s) = fst'_nat (fst'_state_p s)"
  by (subst fst'_imp.simps) (auto simp: dsqrt_imp_correct fst'_imp_state_upd_def tsqrt_imp_correct
      Let_def triangle_imp_correct fst'_nat_def split: if_splits)

fun fst'_imp_time:: "nat \<Rightarrow> fst'_state\<Rightarrow> nat" where
  "fst'_imp_time t s = 
    (
      let
        fst'_tsqrt_y = fst'_state_p s;
        t = t+2;
        fst'_tsqrt_ret = 0;
        t = t+2;
        fst'_tsqrt_state = \<lparr>tsqrt_state_y = fst'_tsqrt_y, tsqrt_state_ret = fst'_tsqrt_ret\<rparr>;
        fst'_tsqrt_ret = tsqrt_imp fst'_tsqrt_state;
        t = t + tsqrt_imp_time 0 fst'_tsqrt_state;
        
        fst'_triangle_a = tsqrt_state_ret fst'_tsqrt_ret;
        t = t+2;
        fst'_triangle_triangle = 0;
        t = t+2;
        fst'_triangle_state = \<lparr>triangle_a = fst'_triangle_a, triangle_triangle = fst'_triangle_triangle\<rparr>;
        fst'_triangle_ret = triangle_imp fst'_triangle_state;
        t = t + triangle_imp_time 0 fst'_triangle_state;
    
        fst'_p = fst'_state_p s - triangle_triangle fst'_triangle_ret;
        t = t+2;
        
        ret = t
      in
        ret
    )
"

lemmas [simp del] = fst'_imp_time.simps

lemma fst'_imp_time_acc: "(fst'_imp_time (Suc t) s) = Suc (fst'_imp_time t s)"
  apply(subst fst'_imp_time.simps)
  apply(subst fst'_imp_time.simps)
  apply (auto simp add: fst'_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)
  done

lemma fst'_imp_time_acc_2: "(fst'_imp_time x s) = x + (fst'_imp_time 0 s)"
  by (induction x arbitrary: s)
     (auto simp add: fst'_imp_time_acc fst'_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)


fun fst'_imp_time' :: "nat \<Rightarrow> nat" where
  "fst'_imp_time' p = 10 + tsqrt_imp_time' p + triangle_imp_time' (tsqrt p)"

lemma fst'_imp_time_fst'_imp_time': "fst'_imp_time t s = t + fst'_imp_time' (fst'_state_p s)"
  by (subst fst'_imp_time.simps) (auto simp add: fst'_imp_time_acc_2 tsqrt_imp_time_tsqrt_imp_time' 
      triangle_imp_time_triangle_imp_time' tsqrt_imp_correct Let_def mult.commute)

lemma tsqrt_le: "tsqrt p \<le> p" 
  using triangle_nat_le_imp_le triangle_tsqrt_le by blast

lemma fst'_imp_time'_non_rec_bound: "fst'_imp_time' p \<le> 733 + 173 * Discrete.log p + 10 * (Discrete.log p)\<^sup>2"
proof-
  have "fst'_imp_time' p = 10 + tsqrt_imp_time' p + triangle_imp_time' (tsqrt p)"
    by simp
  also have "\<dots> \<le> 10 + 691 + (163 * Discrete.log p + 10 * (Discrete.log p)\<^sup>2) + triangle_imp_time' (tsqrt p)"
    using tsqrt_imp_time'_non_rec_bound by simp
  also have "\<dots> \<le> 10 + 691 + (163 * Discrete.log p + 10 * (Discrete.log p)\<^sup>2) + 32 + 10 * (Discrete.log (tsqrt p))"
    using triangle_imp_time'_non_rec_bound by simp
  also have "\<dots> \<le> 10 + 691 + (163 * Discrete.log p + 10 * (Discrete.log p)\<^sup>2) + 32 + 10 * (Discrete.log p)"
    using tsqrt_le by (simp add: Discrete.log_le_iff)
  also have "\<dots> \<le> 733 + 173 * Discrete.log p + 10 * (Discrete.log p)\<^sup>2"
    by simp
  finally show ?thesis .
qed

definition fst'_IMP_Minus where
"fst'_IMP_Minus \<equiv>
  (
    (tsqrt_prefix @ tsqrt_y_str) ::= A (V fst'_p_str);;
    (tsqrt_prefix @ tsqrt_ret_str) ::= A (N 0);;
    invoke_subprogram tsqrt_prefix tsqrt_IMP_Minus;;

    (triangle_prefix @ triangle_a_str) ::= A (V (tsqrt_prefix @ tsqrt_ret_str));;
    (triangle_prefix @ triangle_triangle_str) ::= A (N 0);;
    invoke_subprogram triangle_prefix triangle_IMP_Minus;;

    fst'_p_str ::= ((V fst'_p_str) \<ominus> V (triangle_prefix @ triangle_triangle_str))
  )"

definition "fst'_imp_to_HOL_state p s = \<lparr>fst'_state_p = (s (add_prefix p fst'_p_str))\<rparr>"


(* New correctness lemma, replace above *)
lemma triangle_IMP_Minus_correct_effects':
  "(invoke_subprogram (p @ triangle_pref) triangle_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> v \<in> vars 
  \<Longrightarrow> \<not> (prefix triangle_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def by blast

lemma triangle_IMP_Minus_correct':
  "\<lbrakk>(invoke_subprogram (p1 @ p2) triangle_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (triangle_imp_time 0 (triangle_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) triangle_triangle_str) = 
        triangle_triangle (triangle_imp (triangle_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using triangle_IMP_Minus_correct_time triangle_IMP_Minus_correct_function
        triangle_IMP_Minus_correct_effects'
  by auto


lemma fst'_IMP_Minus_correct_function: 
  "(invoke_subprogram p fst'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p fst'_p_str) = fst'_state_p (fst'_imp (fst'_imp_to_HOL_state p s))"
  apply(subst fst'_imp.simps)
  apply(simp only: fst'_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(erule tsqrt_IMP_Minus_correct[where vars = "fst'_IMP_vars"])
   apply auto[]
  apply(erule triangle_IMP_Minus_correct'[where vars = "fst'_IMP_vars"])
  apply auto[]
  (* Seems to work, but looks like automation needs to figure out that the input variable is not changed during the program
    No idea if this is new
  *)
   apply (fastforce simp add: fst'_imp_state_upd_def fst'_imp_to_HOL_state_def tsqrt_imp_to_HOL_state_def
      triangle_imp_to_HOL_state_def Let_def)
  done

lemma fst'_IMP_Minus_correct_time: 
  "(invoke_subprogram p fst'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = fst'_imp_time 0 (fst'_imp_to_HOL_state p s)"
  apply(subst fst'_imp_time.simps)
  apply(simp only: fst'_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(erule tsqrt_IMP_Minus_correct[where vars = "fst'_IMP_vars"])
   apply auto[]
  apply(erule triangle_IMP_Minus_correct'[where vars = "fst'_IMP_vars"])
  apply auto[]
  (* Seems to work, but looks like automation needs to figure out that the input variable is not changed during the program
    No idea if this is new
  *)
   apply (fastforce simp add: fst'_imp_state_upd_def fst'_imp_to_HOL_state_def tsqrt_imp_to_HOL_state_def
      triangle_imp_to_HOL_state_def Let_def)
  done

lemma fst'_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ fst'_pref) fst'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>  v \<in> vars 
  \<Longrightarrow> \<not> (prefix fst'_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma fst'_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) fst'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (fst'_imp_time 0 (fst'_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) fst'_p_str) = 
        fst'_state_p (fst'_imp (fst'_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using fst'_IMP_Minus_correct_time fst'_IMP_Minus_correct_function
        fst'_IMP_Minus_correct_effects 
  by auto


record snd'_state = snd'_state_p :: nat
abbreviation "snd'_prefix \<equiv> ''snd'.''"
abbreviation "snd'_p_str \<equiv> ''p''"

abbreviation 
  "snd'_IMP_vars \<equiv> {snd'_p_str}"

thm snd'_nat_def
(* Copying directly from function outputs *)
definition "snd'_imp_state_upd s = (let
    snd'_tsqrt_y = snd'_state_p s;
    snd'_tsqrt_ret = 0;
    snd'_tsqrt_state = \<lparr>tsqrt_state_y = snd'_tsqrt_y, tsqrt_state_ret = snd'_tsqrt_ret\<rparr>;
    snd'_tsqrt_ret = tsqrt_imp snd'_tsqrt_state;
    
    snd'_fst'_p = snd'_state_p s;
    snd'_fst'_state = \<lparr>fst'_state_p = snd'_fst'_p\<rparr>;
    snd'_fst'_ret = fst'_imp snd'_fst'_state;

    snd'_p = tsqrt_state_ret snd'_tsqrt_ret - fst'_state_p snd'_fst'_ret;
    
    ret = \<lparr>snd'_state_p = snd'_p\<rparr>
  in
    ret)
"

fun snd'_imp :: "snd'_state \<Rightarrow> snd'_state" where
  "snd'_imp s = 
  (let
    ret = snd'_imp_state_upd s
  in
    ret
  )"

declare snd'_imp.simps [simp del]

lemma snd'_imp_correct:
   "snd'_state_p (snd'_imp s) = snd'_nat (snd'_state_p s)"
  by (subst snd'_imp.simps) (auto simp: dsqrt_imp_correct snd'_imp_state_upd_def tsqrt_imp_correct
      fst'_imp_correct snd'_nat_def)

fun snd'_imp_time:: "nat \<Rightarrow> snd'_state\<Rightarrow> nat" where
  "snd'_imp_time t s = 
    (
      let
        snd'_tsqrt_y = snd'_state_p s;
        t = t+2;
        snd'_tsqrt_ret = 0;
        t = t+2;
        snd'_tsqrt_state = \<lparr>tsqrt_state_y = snd'_tsqrt_y, tsqrt_state_ret = snd'_tsqrt_ret\<rparr>;
        snd'_tsqrt_ret = tsqrt_imp snd'_tsqrt_state;
        t = t + tsqrt_imp_time 0 snd'_tsqrt_state;
        
        snd'_fst'_p = snd'_state_p s;
        t = t+2;
        snd'_fst'_state = \<lparr>fst'_state_p = snd'_fst'_p\<rparr>;
        snd'_fst'_ret = fst'_imp snd'_fst'_state;
        t = t + fst'_imp_time 0 snd'_fst'_state;
    
        snd'_p = tsqrt_state_ret snd'_tsqrt_ret - fst'_state_p snd'_fst'_ret;
        t = t+2;
        
        ret = t
      in
        ret
    )
"

lemmas [simp del] = snd'_imp_time.simps

lemma snd'_imp_time_acc: "(snd'_imp_time (Suc t) s) = Suc (snd'_imp_time t s)"
  apply(subst snd'_imp_time.simps)
  apply(subst snd'_imp_time.simps)
  apply (auto simp add: snd'_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)
  done

lemma snd'_imp_time_acc_2: "(snd'_imp_time x s) = x + (snd'_imp_time 0 s)"
  by (induction x arbitrary: s)
     (auto simp add: snd'_imp_time_acc snd'_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)

fun snd'_imp_time' :: "nat \<Rightarrow> nat" where
  "snd'_imp_time' p = 8 + tsqrt_imp_time' p + fst'_imp_time' p"

lemma snd'_imp_time_snd'_imp_time': "snd'_imp_time t s = t + snd'_imp_time' (snd'_state_p s)"
  by (subst snd'_imp_time.simps) (auto simp add: snd'_imp_time_acc_2 tsqrt_imp_time_tsqrt_imp_time' 
      fst'_imp_time_fst'_imp_time' Let_def)

lemma snd'_imp_time'_non_rec_bound: "snd'_imp_time' p \<le> 1432 + 336 * Discrete.log p + 20 * (Discrete.log p)\<^sup>2"
proof-
  have "snd'_imp_time' p = 8 + tsqrt_imp_time' p + fst'_imp_time' p"
    by simp
  also have "\<dots> \<le> 8 + 691 + (163 * Discrete.log p + 10 * (Discrete.log p)\<^sup>2) + fst'_imp_time' p"
    using tsqrt_imp_time'_non_rec_bound by (metis (no_types, lifting) add_mono eq_imp_le group_cancel.add1)
  also have "\<dots> \<le> 8 + 691 + (163 * Discrete.log p + 10 * (Discrete.log p)\<^sup>2) + 733 + 173 * Discrete.log p + 10 * (Discrete.log p)\<^sup>2"
    using fst'_imp_time'_non_rec_bound by (metis (mono_tags, lifting) add.assoc nat_add_left_cancel_le) 
  also have "\<dots> \<le> 1432 + 336 * Discrete.log p + 20 * (Discrete.log p)\<^sup>2"
    by auto
  finally show ?thesis .
qed

definition snd'_IMP_Minus where
"snd'_IMP_Minus \<equiv>
  (
    (tsqrt_prefix @ tsqrt_y_str) ::= A (V snd'_p_str);;
    (tsqrt_prefix @ tsqrt_ret_str) ::= A (N 0);;
    invoke_subprogram tsqrt_prefix tsqrt_IMP_Minus;;

    (fst'_prefix @ fst'_p_str) ::= A (V snd'_p_str);;
    invoke_subprogram fst'_prefix fst'_IMP_Minus;;

    snd'_p_str ::= ((V (tsqrt_prefix @ tsqrt_ret_str)) \<ominus> V (fst'_prefix @ fst'_p_str))
  )"

definition "snd'_imp_to_HOL_state p s = \<lparr>snd'_state_p = (s (add_prefix p snd'_p_str))\<rparr>"

lemma snd'_IMP_Minus_correct_function: 
  "(invoke_subprogram p snd'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p snd'_p_str) = snd'_state_p (snd'_imp (snd'_imp_to_HOL_state p s))"
  apply(subst snd'_imp.simps)
  apply(simp only: snd'_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(erule tsqrt_IMP_Minus_correct[where vars = "snd'_IMP_vars"])
   apply auto[]
  (* Not copying means I might have to pass the return variables here *)
  apply(erule fst'_IMP_Minus_correct[where vars = "insert (tsqrt_prefix @ tsqrt_ret_str) snd'_IMP_vars"])
  apply auto[]
   apply (force simp add: snd'_imp_state_upd_def snd'_imp_to_HOL_state_def tsqrt_imp_to_HOL_state_def
      fst'_imp_to_HOL_state_def Let_def)
  done
    

lemma snd'_IMP_Minus_correct_time: 
  "(invoke_subprogram p snd'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = snd'_imp_time 0 (snd'_imp_to_HOL_state p s)"
  apply(subst snd'_imp_time.simps)
  apply(simp only: snd'_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(erule tsqrt_IMP_Minus_correct[where vars = "snd'_IMP_vars"])
   apply auto[]
  (* Not copying means I might have to pass the return variables here *)
  apply(erule fst'_IMP_Minus_correct[where vars = "insert (tsqrt_prefix @ tsqrt_ret_str) snd'_IMP_vars"])
  apply auto[]
   apply (force simp add: snd'_imp_state_upd_def snd'_imp_to_HOL_state_def tsqrt_imp_to_HOL_state_def
      fst'_imp_to_HOL_state_def Let_def)
  done

lemma snd'_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ snd'_pref) snd'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>  v \<in> vars 
  \<Longrightarrow> \<not> (prefix snd'_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma snd'_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) snd'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (snd'_imp_time 0 (snd'_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) snd'_p_str) = 
        snd'_state_p (snd'_imp (snd'_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using snd'_IMP_Minus_correct_time snd'_IMP_Minus_correct_function
        snd'_IMP_Minus_correct_effects 
  by auto

(* Restore prod_decode *)

record prod_decode'_state = prod_decode'_state_p :: nat prod_decode'_state_fst :: nat prod_decode'_state_snd :: nat
abbreviation "prod_decode'_prefix \<equiv> ''prod_decode'.''"
abbreviation "prod_decode'_p_str \<equiv> ''p''"
abbreviation "prod_decode'_fst_str \<equiv> ''fst''"
abbreviation "prod_decode'_snd_str \<equiv> ''snd''"

abbreviation 
  "prod_decode'_IMP_vars \<equiv> {prod_decode'_p_str, prod_decode'_fst_str, prod_decode'_snd_str}"

(* Copying directly from function outputs *)
definition "prod_decode'_imp_state_upd s = (let
    prod_decode'_fst'_p = prod_decode'_state_p s;
    prod_decode'_fst'_state = \<lparr>fst'_state_p = prod_decode'_fst'_p\<rparr>;
    prod_decode'_fst'_ret = fst'_imp prod_decode'_fst'_state;
    prod_decode'_fst = fst'_state_p prod_decode'_fst'_ret;

    prod_decode'_snd'_p = prod_decode'_state_p s;
    prod_decode'_snd'_state = \<lparr>snd'_state_p = prod_decode'_snd'_p\<rparr>;
    prod_decode'_snd'_ret = snd'_imp prod_decode'_snd'_state;
    prod_decode'_snd = snd'_state_p prod_decode'_snd'_ret;
    
    ret = \<lparr>prod_decode'_state_p = prod_decode'_state_p s, 
      prod_decode'_state_fst = prod_decode'_fst, prod_decode'_state_snd = prod_decode'_snd\<rparr>
  in
    ret)
"

fun prod_decode'_imp :: "prod_decode'_state \<Rightarrow> prod_decode'_state" where
  "prod_decode'_imp s = 
  (let
    ret = prod_decode'_imp_state_upd s
  in
    ret
  )"

declare prod_decode'_imp.simps [simp del]

lemma prod_decode'_imp_correct:
   "prod_decode'_state_fst (prod_decode'_imp s) = fst'_nat (prod_decode'_state_p s)"
   "prod_decode'_state_snd (prod_decode'_imp s) = snd'_nat (prod_decode'_state_p s)"
  by (all \<open>subst prod_decode'_imp.simps\<close>) (auto simp: fst'_imp_correct snd'_imp_correct 
      prod_decode'_imp_state_upd_def)

fun prod_decode'_imp_time:: "nat \<Rightarrow> prod_decode'_state\<Rightarrow> nat" where
  "prod_decode'_imp_time t s = 
    (
      let
        prod_decode'_fst'_p = prod_decode'_state_p s;
        t = t+2;
        prod_decode'_fst'_state = \<lparr>fst'_state_p = prod_decode'_fst'_p\<rparr>;
        prod_decode'_fst'_ret = fst'_imp prod_decode'_fst'_state;
        t = t + fst'_imp_time 0 prod_decode'_fst'_state;
        prod_decode'_fst = fst'_state_p prod_decode'_fst'_ret;
        t = t+2;
    
        prod_decode'_snd'_p = prod_decode'_state_p s;
        t = t+2;
        prod_decode'_snd'_state = \<lparr>snd'_state_p = prod_decode'_snd'_p\<rparr>;
        prod_decode'_snd'_ret = snd'_imp prod_decode'_snd'_state;
        t = t + snd'_imp_time 0 prod_decode'_snd'_state;
        prod_decode'_snd = snd'_state_p prod_decode'_snd'_ret;
        t = t+2;
        
        ret = t
      in
        ret
    )
"

lemmas [simp del] = prod_decode'_imp_time.simps

lemma prod_decode'_imp_time_acc: "(prod_decode'_imp_time (Suc t) s) = Suc (prod_decode'_imp_time t s)"
  apply(subst prod_decode'_imp_time.simps)
  apply(subst prod_decode'_imp_time.simps)
  apply (auto simp add: prod_decode'_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)
  done

lemma prod_decode'_imp_time_acc_2: "(prod_decode'_imp_time x s) = x + (prod_decode'_imp_time 0 s)"
  by (induction x arbitrary: s)
     (auto simp add: prod_decode'_imp_time_acc prod_decode'_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)

fun prod_decode'_imp_time' :: "nat \<Rightarrow> nat" where
  "prod_decode'_imp_time' p = 8 + fst'_imp_time' p + snd'_imp_time' p"

lemma prod_decode'_imp_time_prod_decode'_imp_time': "prod_decode'_imp_time t s = t + prod_decode'_imp_time' (prod_decode'_state_p s)"
  by (subst prod_decode'_imp_time.simps) (auto simp add: prod_decode'_imp_time_acc_2 tsqrt_imp_time_tsqrt_imp_time' 
      fst'_imp_time_fst'_imp_time' snd'_imp_time_snd'_imp_time' Let_def)

lemma prod_decode'_imp_time'_non_rec_bound: "prod_decode'_imp_time' p \<le> 2173 + 509 * Discrete.log p + 30 * (Discrete.log p)\<^sup>2"
proof-
  have "prod_decode'_imp_time' p = 8 + fst'_imp_time' p + snd'_imp_time' p"
    by simp
  also have "\<dots> \<le> 8 + 733 + 173 * Discrete.log p + 10 * (Discrete.log p)\<^sup>2 + snd'_imp_time' p"
    using fst'_imp_time'_non_rec_bound by (metis (no_types, lifting) add_mono eq_imp_le group_cancel.add1)
  also have "\<dots> \<le> 8 + 733 + 173 * Discrete.log p + 10 * (Discrete.log p)\<^sup>2 + 1432 + 336 * Discrete.log p + 20 * (Discrete.log p)\<^sup>2"
    using snd'_imp_time'_non_rec_bound by (metis (no_types, lifting) add_mono eq_imp_le group_cancel.add1)
  also have "\<dots> \<le> 2173 + 509 * Discrete.log p + 30 * (Discrete.log p)\<^sup>2" 
    by auto
  finally show ?thesis .
qed

definition prod_decode'_IMP_Minus where
"prod_decode'_IMP_Minus \<equiv>
  (
    (fst'_prefix @ fst'_p_str) ::= A (V prod_decode'_p_str);;
    invoke_subprogram fst'_prefix fst'_IMP_Minus;;
    prod_decode'_fst_str ::= A (V (fst'_prefix @ fst'_p_str));;

    (snd'_prefix @ snd'_p_str) ::= A (V prod_decode'_p_str);;
    invoke_subprogram snd'_prefix snd'_IMP_Minus;;
    prod_decode'_snd_str ::= A (V (snd'_prefix @ snd'_p_str))
  )"

definition "prod_decode'_imp_to_HOL_state p s = \<lparr>prod_decode'_state_p = (s (add_prefix p prod_decode'_p_str)),
  prod_decode'_state_fst = (s (add_prefix p prod_decode'_fst_str)),
  prod_decode'_state_snd = (s (add_prefix p prod_decode'_snd_str))\<rparr>"

lemma prod_decode'_IMP_Minus_correct_function: 
  "(invoke_subprogram p prod_decode'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p prod_decode'_p_str) = prod_decode'_state_p (prod_decode'_imp (prod_decode'_imp_to_HOL_state p s))"
  apply(subst prod_decode'_imp.simps)
  apply(simp only: prod_decode'_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(erule fst'_IMP_Minus_correct[where vars = "prod_decode'_IMP_vars"])
   apply auto[]
  apply(erule snd'_IMP_Minus_correct[where vars = "prod_decode'_IMP_vars"])
   apply auto[] (* Check why this is taking so much longer *)
  apply (force simp add: prod_decode'_imp_state_upd_def prod_decode'_imp_to_HOL_state_def tsqrt_imp_to_HOL_state_def
      fst'_imp_to_HOL_state_def snd'_imp_to_HOL_state_def Let_def)
  done
    

lemma prod_decode'_IMP_Minus_correct_time: 
  "(invoke_subprogram p prod_decode'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = prod_decode'_imp_time 0 (prod_decode'_imp_to_HOL_state p s)"
  apply(subst prod_decode'_imp_time.simps)
  apply(simp only: prod_decode'_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(erule fst'_IMP_Minus_correct[where vars = "prod_decode'_IMP_vars"])
   apply auto[]
  apply(erule snd'_IMP_Minus_correct[where vars = "prod_decode'_IMP_vars"])
   apply auto[]
  apply (force simp add: prod_decode'_imp_state_upd_def prod_decode'_imp_to_HOL_state_def tsqrt_imp_to_HOL_state_def
      fst'_imp_to_HOL_state_def snd'_imp_to_HOL_state_def Let_def)
  done

lemma prod_decode'_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ prod_decode'_pref) prod_decode'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>  v \<in> vars 
  \<Longrightarrow> \<not> (prefix prod_decode'_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma prod_decode'_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) prod_decode'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (prod_decode'_imp_time 0 (prod_decode'_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) prod_decode'_p_str) = 
        prod_decode'_state_p (prod_decode'_imp (prod_decode'_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using prod_decode'_IMP_Minus_correct_time prod_decode'_IMP_Minus_correct_function
        prod_decode'_IMP_Minus_correct_effects 
  by auto

(* hole should be plugged, now to smash this into the other theory *)


(* This is now somewhat suspect, as not connected back yet *)
term hd_xs
fun hd_imp_time' :: "nat \<Rightarrow> nat" where
  "hd_imp_time' l = 8 + prod_decode'_imp_time' (l-1)"


(* List stuff skipped as prod_encode_aux missing :( *)


subsubsection \<open>Logical and\<close>

fun AND_neq_zero_imp_time' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "AND_neq_zero_imp_time' a b = 1 + (if a \<noteq> 0 then 3 else 2)"

lemma AND_neq_zero_imp_time_AND_neq_zero_imp_time': 
  "AND_neq_zero_imp_time t s = AND_neq_zero_imp_time' (AND_neq_zero_a s) (AND_neq_zero_b s) + t"
  by (auto simp add: AND_neq_zero_imp_time.simps)

subsubsection \<open>Logical or\<close>

fun OR_neq_zero_imp_time' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "OR_neq_zero_imp_time' a b = 1 + (if a \<noteq> 0 then 2 else 3)"

lemma OR_neq_zero_imp_time_OR_neq_zero_imp_time': 
  "OR_neq_zero_imp_time t s = OR_neq_zero_imp_time' (OR_neq_zero_a s) (OR_neq_zero_b s) + t"
  by (auto simp add: OR_neq_zero_imp_time.simps)


end