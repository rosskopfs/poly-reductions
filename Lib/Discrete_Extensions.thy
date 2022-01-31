
text \<open>Extensions to Discrete.thy, in particular an implementation of square root by bisection\<close>

theory Discrete_Extensions
  imports "HOL-Library.Discrete" "HOL-Eisbach.Eisbach"
begin

(* Internal 'loop' for the algorithm, takes lower and upper bound for root, returns root *)
function dsqrt' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "dsqrt' y L R = (if Suc L < R then let M = (L+R) div 2 in if M*M \<le> y then dsqrt' y M R else dsqrt' y L M else L)"
  by auto
termination by (relation "Wellfounded.measure (\<lambda>(y,L,R). R - L)") auto

declare dsqrt'.simps[simp del]

(* Probably not better... *)
lemma dsqrt'_simps[]:
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
      using "1.prems" False by (fastforce simp add: dsqrt'.simps)
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

end