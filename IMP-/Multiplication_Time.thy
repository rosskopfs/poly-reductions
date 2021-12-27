
(* My experiments with timing *)

theory Multiplication_Time 
  imports Multiplication "Poly_Reductions_Lib.Landau_Auxiliaries"
begin

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
    apply (smt (verit, best) One_nat_def Suc_0_to_numeral floor_divide_of_nat_eq 
        landau_product_preprocess(33) landau_product_preprocess(35) nat_int of_nat_1 of_nat_Suc of_nat_numeral select_convs(2))+
    done
qed

(* Now we get the runtime "for free" *)
lemma runtime_pre: "mul_imp_time'' \<in> \<Theta>(\<lambda>n. ln n)"
  by master_theorem simp_all

lemma runtime_master: "mul_imp_time'' \<in> O(Discrete.log)"
  using runtime_pre dlog_\<Theta>_ln by blast

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

end