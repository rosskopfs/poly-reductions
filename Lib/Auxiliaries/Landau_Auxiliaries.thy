
(* 
  Some quickly thrown together stuff about landau symbols
  In particular concerning discrete logarithm 
  Might help to offload some running time analysis to manuel's akra-bazzi thing
*)

theory Landau_Auxiliaries
  imports "Akra_Bazzi.Akra_Bazzi_Method" "HOL-Library.Discrete" "HOL-Real_Asymp.Real_Asymp"
begin

(* 
  Following are some hammered lemmas to connect logs and Discrete.log 
  Not much thought went into the proofs
*)
lemma dlog_log2_bound: "n > 0 \<Longrightarrow> Discrete.log n \<le> log 2 n"
  by (simp add: le_log2_of_power log_exp2_le)

lemma log2_floor_dlog_eq: 
  assumes "n > 0" 
  shows "Discrete.log n = nat \<lfloor>log 2 n\<rfloor>"
  apply (rule Discrete.log_eqI)
  using assms apply assumption
  using assms log_altdef log_exp2_le apply auto[1]
  using assms bot_nat_0.not_eq_extremum log_altdef log_exp2_gt by presburger

(* Experiment: Set up real_asymp for Discrete.log. Makes everything below, but the last lemma superflouus  *)
lemma dlog_express_as_real[real_asymp_nat_reify]:
  "real (Discrete.log n) = Multiseries_Expansion.rfloor (log 2 (max (real n) 1))"
  using log2_floor_dlog_eq rfloor_def by (cases n) auto

corollary log2_dlog_bound: "n > 0 \<Longrightarrow> Discrete.log n \<ge> nat \<lfloor>log 2 n\<rfloor>"
  using log2_floor_dlog_eq by force

lemma log2_floor_dlog_bound:
  assumes "n > 0" 
  shows "1 + Discrete.log n \<ge> nat \<lceil>log 2 n\<rceil>"
  by (metis Discrete.log_le_iff assms log2_of_power_le log_exp nat_ceiling_le_eq nat_le_linear not_less_eq_eq plus_1_eq_Suc)

lemma log2_ceil_in_Odlog': "(\<lambda>n. \<lceil>log 2 n\<rceil>) \<in> O(\<lambda>n. 1 + Discrete.log n)"
  by real_asymp
  (*
  apply (rule bigoI[of _ "1"])
  apply (auto simp add: )
  apply (rule eventually_sequentiallyI[where c=1])
  apply (auto simp add: )
  by (smt (verit) bot_nat_0.not_eq_extremum ceiling_of_int dlog_log2_bound le_of_int_ceiling 
      log2_floor_dlog_bound nat_ceiling_le_eq not_less_eq_eq of_nat_0_le_iff of_nat_0_less_iff of_nat_Suc plus_1_eq_Suc)
  *)
lemma pos_const_in_odlog: "const > 0 \<Longrightarrow>(\<lambda>_. const::real) \<in> o(Discrete.log)"
  by real_asymp
  (*
  apply (rule landau_o.smallI)
  apply auto 
  subgoal for c
    apply (rule eventually_at_top_linorderI[where c="2 ^ nat \<lceil>(const/c)\<rceil>"])
    subgoal premises p for x
    proof-
      note p

      have "c * Discrete.log (2 ^ nat \<lceil>(const/c)\<rceil>) \<ge> const"
        using p(1,2) apply auto 
        by (smt (verit, del_insts) divide_strict_right_mono nonzero_mult_div_cancel_left of_nat_ceiling) 
      moreover have "x>0"
        using p(3) 
        using gr0I by force
      ultimately show ?thesis
        using p(2,3) apply auto 
        by (metis Discrete.log_le_iff linorder_not_less log_exp mult.commute of_nat_le_iff order_less_le_trans pos_less_divide_eq)
    qed
    done
  done
  *)

lemma const_in_odlog: "(\<lambda>_. const::real) \<in> o(Discrete.log)"
  by real_asymp
  (*by (metis landau_o.small.const_in_iff landau_o.small_trans less_numeral_extra(1) pos_const_in_odlog smallo_1_tendsto_0 tendsto_const)
  *)

lemma pos_const_in_oln: "const > 0 \<Longrightarrow> (\<lambda>_. const::real) \<in> o(ln)"
  by real_asymp
  (* I learned about real_asymp to late *)
  (*
  apply (rule landau_o.smallI)
  apply auto 
  subgoal for c
    apply (rule eventually_at_top_linorderI[where c="exp (const/c)"])
    subgoal premises p for x
    proof-
      note p

      have 1: "c * ln (exp (const / c)) = const"
        using p(2) by auto 
      moreover have "x>0"
        using exp_gt_zero order_less_le_trans p(3) by blast
      ultimately show ?thesis
        using p(2,3) apply auto 
        by (smt (verit, del_insts) 1 exp_gt_zero ln_le_cancel_iff mult_le_cancel_left_pos)
    qed
    done
  done
  *)

lemma const_in_oln: "(\<lambda>_. const::real) \<in> o(ln)"
  by real_asymp
  (*
  by (metis landau_o.small.const_in_iff landau_o.small_trans less_numeral_extra(1) 
      pos_const_in_oln smallo_1_tendsto_0 tendsto_const)
*)

lemma dlog_plus1_theta: "\<Theta>(\<lambda>n. Discrete.log n + 1) = \<Theta>(Discrete.log)"
  using const_in_odlog by auto

lemma log2_ceil_in_Odlog: "(\<lambda>n. \<lceil>log 2 n\<rceil>) \<in> O(Discrete.log)"
  by real_asymp
(*
proof-
  have "(\<lambda>n. Discrete.log n) \<in> \<Theta>(\<lambda>n. Discrete.log n + 1)"
    using dlog_plus1_theta by auto
  hence 1: "(\<lambda>n. Discrete.log n + 1) \<in> O(\<lambda>n. Discrete.log n)" 
    by (meson landau_o.big.bigtheta_trans2' landau_o.big_refl)
  have 2: "(\<lambda>n. \<lceil>log 2 n\<rceil>) \<in> O(\<lambda>n. Discrete.log n + 1)"
    apply (rule bigoI[of _ 1])
    apply auto
    apply (rule eventually_at_top_linorderI[of 1])
    apply auto
    by (smt (verit, ccfv_threshold) Multiseries_Expansion.intyness_simps(1) ceiling_le_iff 
        ceiling_of_int dlog_log2_bound less_eq_Suc_le log2_floor_dlog_bound nat_ceiling_le_eq of_nat_0_le_iff of_nat_1)
  from 2 1 show ?thesis
    unfolding comp_def
    by (rule landau_o.big_trans)
qed
*)

lemma dlog_in_Olog2: "Discrete.log \<in> O(log 2)"
  by real_asymp
(*by (rule bigoI[of _ 1]) (simp add: log_altdef)*)

lemma floor_log2_in_Odlog: "(\<lambda>n. \<lfloor>log 2 n\<rfloor>) \<in> O(Discrete.log)"
  by real_asymp
(*
  apply (rule bigoI[of _ "1"])
  apply (auto simp add: log_altdef log_exp2_gt)
  using eventually_at_top_linorder by blast
*)

lemma log2_\<Theta>_ln: "\<Theta>(log (2::real)) = \<Theta>(ln)"
proof-
  have "\<Theta>(log 2) = \<Theta>(\<lambda>n :: real. ln n / ln 2)"
    unfolding log_def by (rule refl)
  have s: "ln n / ln 2 = ln n * (1/ln 2)" for n::real
    by simp
  show ?thesis
    unfolding log_def s by auto
qed

(* fix the type *)
lemma log2_\<Theta>_ln': "\<Theta>(\<lambda>n :: nat . log (2::real) n) = \<Theta>(ln)"
proof-
  have "\<Theta>(log 2) = \<Theta>(\<lambda>n :: real. ln n / ln 2)"
    unfolding log_def by (rule refl)
  have s: "ln n / ln 2 = ln n * (1/ln 2)" for n::real
    by simp
  show ?thesis
    unfolding log_def s by auto
qed

corollary log2_in_Oln: "log (2::real) \<in> O(ln)"
  by real_asymp
  (*by (simp add: log2_\<Theta>_ln)*)

lemma dlog_in_Oln: "Discrete.log \<in> O(ln)"
  by real_asymp
  (* using dlog_in_Olog2 landau_o.big_trans log2_in_Oln by blast*)

lemma log2_in_Odlog: "log 2 \<in> O(Discrete.log)"
  by real_asymp
(*
proof-
  have 1: "(log 2) \<in> O(\<lambda>n :: nat. \<lceil>log 2 n\<rceil>)"
    apply (rule bigoI[of _ 1])
    apply (rule eventually_sequentiallyI[of 3])
    apply auto
    by linarith
  show ?thesis
    by (rule landau_o.big_trans[where g="(\<lambda>n :: nat. \<lceil>log 2 n\<rceil>  )"]) (use 1 log2_ceil_in_Odlog in simp_all)
qed                     
*)

corollary dlog_in_\<Omega>log2: "Discrete.log \<in> \<Omega>(log 2)"
  by real_asymp (* using bigo_imp_bigomega log2_in_Odlog by blast*)
corollary dlog_in_\<Theta>log2: "Discrete.log \<in> \<Theta>(log 2)"
  by real_asymp
  (*
  using dlog_in_\<Omega>log2 dlog_in_Olog2 by auto*)
corollary dlog_in_\<Theta>ln: "Discrete.log \<in> \<Theta>(ln)"
  by real_asymp
  (*
  using dlog_in_\<Theta>log2 log2_\<Theta>_ln' by blast*)

(* The result of the whole diversion *)
corollary dlog_\<Theta>_ln: "\<Theta>(Discrete.log) = \<Theta>(ln)"
  using dlog_in_\<Theta>ln by (meson landau_theta.cong_bigtheta)


end