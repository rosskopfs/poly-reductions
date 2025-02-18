\<^marker>\<open>creator Florian Keßler\<close>
\<^marker>\<open>creator Fabian Huch\<close>

section "IMP Max Constant"

theory Max_Constant
  imports Small_StepT Vars
begin

text \<open>We define functions to derive the constant with the highest value and enumerate all variables
  in IMP programs. \<close>

class max_const =
  fixes max_const :: "'a \<Rightarrow> nat"

instantiation atomExp :: max_const
begin

fun max_const_atomExp :: "atomExp \<Rightarrow> nat" where
"max_const (V _) = 0" |
"max_const (N n) = n"

instance ..

end

instantiation aexp :: max_const
begin

fun max_const_aexp :: "aexp \<Rightarrow> nat" where
"max_const (A e) = max_const e" |
"max_const (Plus e\<^sub>1 e\<^sub>2) = max (max_const e\<^sub>1) (max_const e\<^sub>2)" |
"max_const (Sub e\<^sub>1 e\<^sub>2) = max (max_const e\<^sub>1) (max_const e\<^sub>2)"

instance ..

end

instantiation com :: max_const
begin

fun max_const_com :: "com \<Rightarrow> nat" where
"max_const SKIP = 0" |
"max_const (_ ::= e) = max_const e" |
"max_const (c1;;c2) = max (max_const c1) (max_const c2)" |
"max_const (IF _\<noteq>0 THEN c1 ELSE c2) = max (max_const c1) (max_const c2)" |
"max_const (WHILE _\<noteq>0 DO c) = max_const c"

instance ..

end

lemma max_constant_not_increasing_step:
  "(c1, s1) \<rightarrow> (c2, s2) \<Longrightarrow> max_const c2 \<le> max_const c1"
  by (induction c1 s1 c2 s2 rule: small_step_induct) auto

lemma Max_range_le_then_element_le: "finite (range s) \<Longrightarrow> 2 * Max (range s) < (x :: nat) \<Longrightarrow> 2 * (s y) < x"
proof -
  assume "2 * Max (range s) < (x :: nat)"
  moreover have "s y \<in> range s" by simp
  moreover assume "finite (range s)"
  moreover hence "s y \<le> Max (range s)" by simp
  ultimately show ?thesis by linarith
qed

lemma aval_le_when:
  assumes "finite (range s)" "2 * max (Max (range s)) (max_const a) < x"
  shows "AExp.aval a s < x"
using assms proof(cases a)
  case (A x1)
  thus ?thesis using assms
  proof(cases x1)
    case (V x2)
    thus ?thesis using assms A Max_range_le_then_element_le[where ?s=s and ?x = x and ?y=x2] by simp
  qed simp
next
  case (Plus x21 x22)
  hence "2 * max (AExp.atomVal x21 s) (AExp.atomVal x22 s) < x"
    apply(cases x21; cases x22)
    using assms
    by (auto simp add: Max_range_le_then_element_le nat_mult_max_right)
  thus ?thesis using Plus by auto
next
  case (Sub x31 x32)
  then show ?thesis
    apply(cases x31 ; cases x32)
    using assms apply(auto simp add: Max_range_le_then_element_le nat_mult_max_right)
    using Max_range_le_then_element_le
    by (metis gr_implies_not0 lessI less_imp_diff_less less_imp_le_nat less_le_trans
        linorder_neqE_nat n_less_m_mult_n numeral_2_eq_2)+
qed

definition num_variables:: "com \<Rightarrow> nat" where
"num_variables c = length (remdups (vars c))"

lemma all_variables_subset_step: "(c1, s1) \<rightarrow> (c2, s2)
  \<Longrightarrow> set (vars c2) \<subseteq> set (vars c1)"
  apply(induction c1 s1 c2 s2 rule: small_step_induct)
  by auto

lemma subset_then_length_remdups_le: "set as \<subseteq> set bs
  \<Longrightarrow> length (remdups (as @ cs)) \<le> length (remdups (bs @ cs))"
  apply(induction cs)
   apply (auto simp: card_mono length_remdups_card_conv)
  by (metis (no_types, lifting) List.finite_set Un_insert_right card_mono dual_order.trans
      finite.insertI finite_Un sup.boundedI sup.cobounded1 sup.cobounded2)

lemma num_variables_not_increasing_step: "(c1, s1) \<rightarrow> (c2, s2)
  \<Longrightarrow> num_variables c2 \<le> num_variables c1"
  apply(induction c1 s1 c2 s2 rule: small_step_induct)
  using subset_then_length_remdups_le[OF all_variables_subset_step]
        apply(auto simp: num_variables_def length_remdups_card_conv)
        apply (meson List.finite_set card_mono finite_Un sup.cobounded1 sup.cobounded2 le_SucI)+
  by (simp add: insert_absorb)

lemma num_variables_not_increasing: "(c1, s1) \<rightarrow>\<^bsup> t \<^esup> (c2, s2)
  \<Longrightarrow> num_variables c2 \<le> num_variables c1"
proof (induction t arbitrary: c1 s1)
  case (Suc t)
  then obtain c3 s3 where "(c1, s1) \<rightarrow> (c3, s3)" "(c3, s3) \<rightarrow>\<^bsup> t \<^esup> (c2, s2)"
    by auto
  then show ?case
    using num_variables_not_increasing_step[OF \<open>(c1, s1) \<rightarrow> (c3, s3)\<close>]
      Suc.IH[OF \<open>(c3, s3) \<rightarrow>\<^bsup> t \<^esup> (c2, s2)\<close>]
    by simp
qed auto

end