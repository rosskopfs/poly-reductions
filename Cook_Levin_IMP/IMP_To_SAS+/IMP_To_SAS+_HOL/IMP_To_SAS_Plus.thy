\<^marker>\<open>creator Florian Keßler\<close>
\<^marker>\<open>contributor Mohammad Abdulaziz, Bilel Ghorbel\<close>

section "IMP to SAS+"

theory IMP_To_SAS_Plus
  imports "IMP_To_IMP-.IMP_To_IMP_Minus"
    IMP_Minus_To_SAS_Plus_Plus_Correctness
    SAS_Plus_Plus_To_SAS_Plus
begin

text \<open> We combine our reduction steps from IMP to IMP-, then from IMP- to SAS++ and finally 
  from SAS++ to SAS+ to give a reduction IMP to SAS+. We then proceed to show the correctness of
  this reduction, by combining the correctness results we have derived for the individual parts
  of the reduction. \<close> 

type_synonym SAS_problem = "(IMP_Minus_To_SAS_Plus_Plus_State_Translations.variable, 
  IMP_Minus_To_SAS_Plus_Plus_State_Translations.domain_element) problem" 

lemma le_two_to_the_bit_length_intro: "x \<le> y \<Longrightarrow> x \<le> 2 ^ (bit_length y)"
  using floor_log_exp2_gt[of y]
  by (auto simp: bit_length_def)

text \<open> We give a definition to compute the upper bound on the number of bits needed to represent
       all of the fixed input of some IMP program, the biggest constant therein and all guessed
       values up to some r. \<close>

definition max_input_bits:: "IMP_com \<Rightarrow> (vname \<rightharpoonup> nat) \<Rightarrow> nat \<Rightarrow> nat" where
"max_input_bits c I r = 
  bit_length (max (max (Max (ran I)) r) (max_const c))" 

lemma bit_at_index_geq_max_input_bits_is_zero:
  assumes "x < r" "max_input_bits c I r \<le> b"
  shows "nth_bit x b = Zero" 
  using \<open>x < r\<close>
  by (fastforce intro: bit_geq_bit_length_is_Zero bit_length_monotonic 
                       le_trans[OF _ \<open>max_input_bits c I r \<le> b\<close>]
                simp: max_input_bits_def)

lemma bit_at_index_geq_max_input_bits_is_zero_in_initial_state:
  assumes "finite (ran I)" "max_input_bits c I r \<le> b" "I x = Some y" 
  shows "nth_bit y b = Zero"
  using assms(1,3)
  by(fastforce intro: bit_geq_bit_length_is_Zero le_trans[OF _ \<open>max_input_bits c I r \<le> b\<close>] 
                      Max_ge ranI max.coboundedI1 bit_length_monotonic
               simp: max_input_bits_def)

lemma max_const_less_two_to_the_max_input_bits:
  "max_const c < 2 ^ (max_input_bits c I r)"
  using floor_log_exp2_gt max_less_iff_conj
  by(fastforce simp: max_input_bits_def bit_length_def)

lemma initial_state_element_less_two_to_the_max_input_bits: 
  "\<lbrakk>finite (ran I); I x = Some y\<rbrakk> \<Longrightarrow> y < (2 :: nat) ^ (max_input_bits c I r)" 
  by(force intro: floor_log_exp2_gt Max_ge ranI order.strict_trans1[of y "Max (ran I)"]
                  order.strict_trans1[of _ "(max (max (Max (ran I)) r) (max_const c))"]
           simp: algebra_simps max_input_bits_def bit_length_def)

text \<open> Translation of a (partial) initial state from IMP to IMP-. Observe that in order to avoid
       overflows when executing IMP-, we require all bits beyond a certain guess_range in the bit
       blasted IMP- registers that are unspecified in the IMP initial state to be zero. \<close>

text \<open> We give our reduction, by composing the steps IMP \<Rightarrow> IMP- \<Rightarrow> SAS++ \<Rightarrow> SAS+. For the IMP
       \<Rightarrow> IMP- step, we compute a number of bits n that is guaranteed to suffice for all
      executions of the program for at most t steps, starting in initial states where the maximal 
      value of any register is bounded by the maximum of the maximal value of any register in the 
      partial initial state I and r. \<close>

definition IMP_to_SAS_Plus:: "IMP_com \<Rightarrow> (vname \<rightharpoonup> nat) \<Rightarrow> nat \<Rightarrow> (vname \<rightharpoonup> nat) 
  \<Rightarrow>  nat \<Rightarrow> SAS_problem" where
"IMP_to_SAS_Plus c I r G t =
 (let 
    guess_range = max_input_bits c I r;
    n = t + guess_range + 1;
    c' = IMP_To_IMP_Minus c n;
    I' = IMP_State_To_IMP_Minus_partial I n guess_range |` (set (enumerate_variables c'));
    G' = (IMP_State_To_IMP_Minus_partial G n n) |` (set (enumerate_variables c'));
    sas_pp = imp_minus_minus_to_sas_plus c' I' G';
    sas_p = SAS_Plus_Plus_To_SAS_Plus sas_pp
  in 
    sas_p)"

lemma le_mul_intro: "0 < b \<Longrightarrow> a \<le> b \<Longrightarrow> (1 :: nat) < c \<Longrightarrow> a < c * b"
  by (metis One_nat_def dual_order.strict_trans le_neq_implies_less n_less_m_mult_n)

text \<open> First direction of the correctness proof for the IMP to SAS+ reduction, showing that when
       the IMP program terminates in some state, then in SAS+ there is a plan that will reach any
      goal state that matches the end state of the IMP program, such that the plan is polynomially
      longer than the execution in IMP. The constants used to bound the length of the plan have
      no significance, rather they are just derived by adding up the various constants that we
      used in the correctness proofs for the different parts of the reduction. \<close>           

lemma map_le_proj: "m1 \<subseteq>\<^sub>m m2 \<Longrightarrow> m1 |` s \<subseteq>\<^sub>m m2 |` s"
  by (auto simp: map_le_def)

lemma map_le_IMP_State_To_IMP_Minus:
  "\<lbrakk>s1 \<subseteq>\<^sub>m Some \<circ> s2\<rbrakk> \<Longrightarrow>
   IMP_State_To_IMP_Minus_partial s1 n n \<subseteq>\<^sub>m IMP_State_To_IMP_Minus s2 n"
    apply (auto simp: IMP_State_To_IMP_Minus_partial_def
                   IMP_State_To_IMP_Minus_def
                   IMP_State_To_IMP_Minus_with_operands_a_b_def
                   map_le_def
             split!: option.splits if_splits char.splits bool.splits)
    by (smt domI map_comp_Some_iff option.inject)+

lemma map_le_IMP_State_To_IMP_Minus_2:
  "\<lbrakk>s1 \<subseteq>\<^sub>m Some \<circ> s2; range s2 \<noteq> {}; finite (range s2); Max (range s2) < r; (bit_length r) \<le> rbl\<rbrakk> \<Longrightarrow>
   IMP_State_To_IMP_Minus_partial s1 n rbl \<subseteq>\<^sub>m IMP_State_To_IMP_Minus s2 n"
    apply (auto simp: IMP_State_To_IMP_Minus_partial_def
                   IMP_State_To_IMP_Minus_def
                   IMP_State_To_IMP_Minus_with_operands_a_b_def
                   map_le_def image_def
             split!: option.splits if_splits char.splits bool.splits)
   apply (smt domI map_comp_Some_iff option.inject)
  apply(intro bit_geq_bit_length_is_Zero[symmetric])
  by (metis bit_length_monotonic leI le_less less_le_trans)




lemma IMP_to_SAS_Plus_correctness:
  assumes
    "I \<subseteq>\<^sub>m Some \<circ> s1" 
    "finite (range s1)" 
    "Max (range s1) < r"
    "G \<subseteq>\<^sub>m Some \<circ> s2"
    "(c, s1) \<Rightarrow>\<^bsup>t\<^esup> s2"
    "t \<le> t'"
  shows
    "\<exists>plan. length plan \<le> 100 * (max_input_bits c I r + t' + 1) * (t' - 1) 
                            + (max_input_bits c I r + t' + 1 + 1) * (num_vars c + 2) + 52
            \<and> is_serial_solution_for_problem (IMP_to_SAS_Plus c I r G t') plan"
proof -
  let ?guess_range = " max_input_bits c I r"
  let ?n = "?guess_range + t' + 1"
  let ?c' = "IMP_To_IMP_Minus c ?n"
  let ?s1' = "IMP_State_To_IMP_Minus s1 ?n |` (set (enumerate_variables ?c'))"
  let ?s2' = "IMP_State_To_IMP_Minus s2 ?n |` (set (enumerate_variables ?c'))"
  let ?I = "(IMP_State_To_IMP_Minus_partial I ?n ?guess_range) 
    |` (set (enumerate_variables ?c'))"
  let ?G = "(IMP_State_To_IMP_Minus_partial G ?n ?n) 
    |` (set (enumerate_variables ?c'))"
  let ?t = "100 * ?n * (t' - 1) + 51"
  let ?sas_plus_plus_problem 
    = "imp_minus_minus_to_sas_plus ?c' ?I ?G"

  have "?n > 0" by simp

  have "Suc 0 < 2 ^ t'"
    using \<open>(c, s1) \<Rightarrow>\<^bsup> t \<^esup> s2\<close> \<open>t \<le> t'\<close> floor_log_Suc_zero
    by (fastforce intro: Suc_lessI dest: bigstep_progress)
  moreover have "2 ^ t * max (Max (range s1)) (max_const c) \<le> 2 ^ t' * 2 ^ max_input_bits c I r"
           (is "?max_bits_t \<le> _")
    using \<open>Max (range s1) < r\<close> \<open>t \<le> t'\<close> le_two_to_the_bit_length_intro mult_le_mono
    by (auto simp: max_input_bits_def)
  ultimately have "?max_bits_t < 2 ^ (t' + max_input_bits c I r + 1)"
    by(auto simp: power_add intro!: le_mul_intro)
  moreover have "t < t' + max_input_bits c I r + 1"
    using assms
    by auto

  ultimately have "t_small_step_fun (100 * ?n * (t - 1) + 50)
      (IMP_To_IMP_Minus c ?n, IMP_State_To_IMP_Minus s1 ?n)
     = (SKIP, IMP_State_To_IMP_Minus s2 ?n)" 
    using assms(2,5)
    by (fastforce intro!: IMP_To_IMP_Minus simp: add.commute)+
  moreover have "(100 * ?n * (t - 1) + 50) \<le> (100 * ?n * (t' - 1) + 50)"
    using \<open>t \<le> t'\<close>
    by auto
  ultimately have 
    "t_small_step_fun (100 * ?n * (t' - 1) + 50) (?c', IMP_State_To_IMP_Minus s1 ?n)
       = (SKIP, IMP_State_To_IMP_Minus s2 ?n)" 
    using t_small_step_fun_increase_time by blast
  hence "\<exists>t'' \<le> 100 * ?n * (t' - 1) + 50. (?c', ?s1') \<rightarrow>\<^bsup>t''\<^esup> (SKIP, ?s2')" 
    by(auto simp: t_small_step_fun_restrict_variables
            intro: iffD1[OF t_small_step_fun_t_small_step_equivalence])
  then obtain t'' where t''_def: "t'' \<le> 100 * ?n * (t' - 1) + 50" "(?c', ?s1') \<rightarrow>\<^bsup>t''\<^esup> (SKIP, ?s2')" 
    by blast

  have "?G \<subseteq>\<^sub>m ?s2'"
    by (intro map_le_proj map_le_IMP_State_To_IMP_Minus[OF \<open>G \<subseteq>\<^sub>m Some \<circ> s2\<close>])

  have "?I  \<subseteq>\<^sub>m ?s1'"
    by (auto simp: range max_input_bits_def
             intro!: map_le_proj bit_length_monotonic
                     map_le_IMP_State_To_IMP_Minus_2
                      [OF \<open>I \<subseteq>\<^sub>m Some \<circ> s1\<close> _ \<open>finite (range s1)\<close> \<open>Max (range s1) < r\<close>])

  let ?ss1'' = "imp_minus_state_to_sas_plus (?c', ?s1')" 
  let ?ss2'' = "imp_minus_state_to_sas_plus (SKIP, ?s2')"
                                                          
  thm set_mp[OF IMP_To_IMP_Minus_variables[OF \<open>?n > 0\<close>, simplified]]
                                                                    
  obtain plan where plan_def:
     "is_serial_solution_for_problem_sas_plus_plus ?sas_plus_plus_problem plan"
     "length plan \<le> t''"
    apply(rule exE[OF imp_minus_minus_to_sas_plus_plus[OF \<open>(?c', ?s1') \<rightarrow>\<^bsup>t''\<^esup> (SKIP, ?s2')\<close>,
                      where ?I="?I" and ?G="?G" and t' = t'']])
    using \<open>?I  \<subseteq>\<^sub>m ?s1'\<close> \<open>?G \<subseteq>\<^sub>m ?s2'\<close> 
    by (auto simp add: dom_of_IMP_State_To_IMP_Minus 
        dest: set_mp[OF IMP_To_IMP_Minus_variables[OF \<open>?n > 0\<close>, simplified]])

   hence "\<exists>prefix. length prefix \<le> length ((?sas_plus_plus_problem)\<^sub>\<V>\<^sub>+) + 1
                   \<and> is_serial_solution_for_problem
                        (SAS_Plus_Plus_To_SAS_Plus ?sas_plus_plus_problem) 
                        (prefix @ (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator plan))"
     by(fastforce simp: IMP_State_To_IMP_Minus_partial_def map_comp_def 
                  intro!: SAS_Plus_Plus_To_SAS_Plus imp_minus_minus_to_sas_plus_valid
                  split: option.splits)

   then obtain prefix where
     prefix_def: "length prefix \<le> length ((?sas_plus_plus_problem)\<^sub>\<V>\<^sub>+) + 1
                  \<and> is_serial_solution_for_problem 
                       (SAS_Plus_Plus_To_SAS_Plus ?sas_plus_plus_problem) 
                       (prefix @ (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator plan))"
     by rule

   let ?plan' = "prefix @ (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator plan)"
   have "length ((?sas_plus_plus_problem)\<^sub>\<V>\<^sub>+) \<le> (?n + 1) * (num_vars c + 2) + 1"
     using IMP_To_IMP_Minus_variables_length
             [where ?c=c and ?n="(Suc (t' + max_input_bits c I r))"]
     by(auto simp: imp_minus_minus_to_sas_plus_def Let_def add.commute)
   hence "length prefix \<le> (?n + 1) * (num_vars c + 2) + 2"
     using prefix_def
     by simp
   hence "length ?plan' \<le> 100 * ?n * (t' - 1) + (?n + 1) * (num_vars c + 2) + 52
           \<and> is_serial_solution_for_problem (IMP_to_SAS_Plus c I r G t') ?plan'"
     using plan_def prefix_def t''_def
     by(auto simp: IMP_to_SAS_Plus_def Let_def add.commute)
   thus ?thesis
     by rule
qed

lemma not_in_superset_of_dom_then_None:
 "dom s \<subseteq> S \<Longrightarrow> x \<notin> S \<Longrightarrow> s x = None" by auto

text \<open> Second direction of the correctness proof. We show that for an IMP program that will
      terminate after at most t steps on any input, if there is a solution in the reduced 
      SAS+ problem, then there is an IMP state which matches the initial state of the SAS+ problem,
      such that when the IMP program is run starting from that state, it reaches a terminating 
      state matching the goal state of the SAS+ problem. \<close>

lemma SAS_Plus_to_IMP_correctness: 
  assumes 
    "dom I \<subseteq> set (vars c)"
    "dom G \<subseteq> set (vars c)" 
    "Max (ran G) < 2 ^ (t + max_input_bits c I r)" 
    "is_serial_solution_for_problem (IMP_to_SAS_Plus c I r G t) plan"
    "\<forall>s1. I \<subseteq>\<^sub>m Some o s1 \<longrightarrow> (\<exists>s2. \<exists>t' \<le> t. (c, s1) \<Rightarrow>\<^bsup>t'\<^esup> s2)" 
  shows "\<exists>s1 s2 t'. t' \<le> t \<and> I \<subseteq>\<^sub>m Some \<circ> s1 \<and> G \<subseteq>\<^sub>m Some \<circ> s2 \<and> (c, s1)  \<Rightarrow>\<^bsup>t'\<^esup> s2" 
proof -
  let ?guess_range = "max_input_bits c I r"
  let ?n = "t + ?guess_range + 1"
  let ?c' = "IMP_To_IMP_Minus c ?n"
  let ?I = "(IMP_State_To_IMP_Minus_partial I ?n ?guess_range) 
    |` (set (enumerate_variables ?c'))"
  let ?G = "(IMP_State_To_IMP_Minus_partial G ?n ?n) |` (set (enumerate_variables ?c'))"

  have "finite (ran I)" "finite (ran G)" 
    using \<open>dom I \<subseteq> set (vars c)\<close> 
      \<open>dom G \<subseteq> set (vars c)\<close>
    finite_set by(auto simp: finite_subset intro!: finite_ran)

  have "?n > 0" by simp 

  obtain plan' where "length plan' \<le> length plan
    \<and> is_serial_solution_for_problem_sas_plus_plus (imp_minus_minus_to_sas_plus ?c' ?I ?G) plan'" 
    using SAS_Plus_To_SAS_Plus_Plus 
      \<open>is_serial_solution_for_problem (IMP_to_SAS_Plus c I r G t) plan\<close>
    by (metis IMP_to_SAS_Plus_def imp_minus_minus_to_sas_plus_valid)

  then obtain s1 s2 t' where "(?I|` set (enumerate_variables ?c')) \<subseteq>\<^sub>m s1"
    "dom s1 = set (enumerate_variables ?c')"
    "(?G|` set (enumerate_variables ?c')) \<subseteq>\<^sub>m s2" "t' \<le> length plan'" 
    "(?c', s1) \<rightarrow>\<^bsup>t'\<^esup> (SKIP, s2)"
    using sas_plus_plus_to_imp_minus_minus by fastforce

  let ?s1' = "IMP_Minus_State_To_IMP s1 ?n" 
  let ?s2' = "IMP_Minus_State_To_IMP s2 ?n"

  have "s1 v = (IMP_State_To_IMP_Minus ?s1' ?n |` (set (enumerate_variables ?c'))) v" 
    for v
  proof(cases "v \<in> set (enumerate_variables ?c')")
    case True
    thus ?thesis
    proof (cases "v \<in> dom ?I")
      case True
      hence "s1 v = ?I v" using \<open>(?I|` set (enumerate_variables ?c')) \<subseteq>\<^sub>m s1\<close> 
        by(auto simp: map_le_def)
      thus ?thesis using \<open>v \<in> set (enumerate_variables ?c')\<close> 
          using \<open>v \<in> dom ?I\<close> 
          by(auto simp: map_comp_def IMP_State_To_IMP_Minus_partial_def  
              IMP_State_To_IMP_Minus_with_operands_a_b_def
              var_to_var_bit_eq_Some_iff
              var_bit_to_var_neq_operand_bit_to_var[symmetric]
              var_to_operand_bit_eq_Some_iff 
              IMP_State_To_IMP_Minus_partial_of_operand_bit_to_var
              IMP_State_To_IMP_Minus_def
              nth_bit_of_IMP_Minus_State_To_IMP 
              split: option.splits
              dest!: set_mp[OF IMP_To_IMP_Minus_variables[OF \<open>?n > 0\<close>, simplified]] 
              split: option.splits char.splits bool.splits)
    next
      case False
      then obtain v' i where "v = var_bit_to_var (v', i) \<and> i < ?guess_range" using \<open>\<not>(v \<in> dom ?I)\<close>
         \<open>v \<in> set (enumerate_variables ?c')\<close>
        set_mp[OF IMP_To_IMP_Minus_variables \<open>v \<in> set (enumerate_variables ?c')\<close>]
        by(auto simp: map_comp_def
            IMP_State_To_IMP_Minus_partial_def split: option.splits)
      thus ?thesis using \<open>v \<in> set (enumerate_variables ?c')\<close> 
          \<open>dom s1 = set (enumerate_variables ?c')\<close>
        by(auto simp: IMP_State_To_IMP_Minus_def 
            nth_bit_of_IMP_Minus_State_To_IMP
            IMP_State_To_IMP_Minus_with_operands_a_b_def split: option.splits)
    qed
  next
    case False
    thus ?thesis using \<open>dom s1 = set (enumerate_variables ?c')\<close> by auto
  qed
  hence "s1 = IMP_State_To_IMP_Minus ?s1' ?n |` (set (enumerate_variables ?c'))" by auto

  have "?s1' v = y" if "I v = Some y" for v y 
  proof -
    from that have "v \<in> set (vars c)" 
      using \<open>dom I \<subseteq> set (vars c)\<close>
      by auto
    hence "\<forall>i < ?n. var_bit_to_var (v, i) \<in> set (enumerate_variables ?c')" 
      by(auto simp: var_bit_in_IMP_Minus_variables)
    moreover hence "i < ?n \<Longrightarrow> s1 (var_bit_to_var (v, i)) = ?I (var_bit_to_var (v, i))" for i
      using \<open>(?I|` set (enumerate_variables ?c')) \<subseteq>\<^sub>m s1\<close> \<open>I v = Some y\<close>
      by(auto simp: map_le_def
                    IMP_State_To_IMP_Minus_def dom_def
                    IMP_State_To_IMP_Minus_partial_def map_comp_def
                    split: option.splits) 
    ultimately show "?s1' v = y"
      using
        \<open>(?I|` set (enumerate_variables ?c')) \<subseteq>\<^sub>m s1\<close>
        less_le_trans[OF initial_state_element_less_two_to_the_max_input_bits[where ?c=c and ?r=r]]
        \<open>I v = Some y\<close> \<open>finite (ran I)\<close>
      by(auto simp add: map_comp_def 
          power_add 
          algebra_simps nth_append bit_list_to_nat_eq_nat_iff
          IMP_Minus_State_To_IMP_def 
          IMP_State_To_IMP_Minus_partial_def
          intro!: bit_at_index_geq_max_input_bits_is_zero_in_initial_state
          [symmetric, where ?c=c and ?I = I and ?r=r])
  qed
  hence "I \<subseteq>\<^sub>m Some \<circ> ?s1'" by(auto simp: map_le_def)
  
  hence "t_small_step_fun t' 
  (?c', IMP_State_To_IMP_Minus ?s1' ?n |` set (enumerate_variables ?c')) = (SKIP, s2)"
    using \<open>(?c', s1) \<rightarrow>\<^bsup>t'\<^esup> (SKIP, s2)\<close> 
      \<open>s1 = IMP_State_To_IMP_Minus ?s1' ?n |` (set (enumerate_variables ?c'))\<close>
    by(auto simp: t_small_step_fun_t_small_step_equivalence)
  moreover have "t_small_step_fun t' 
    (?c', IMP_State_To_IMP_Minus ?s1' ?n |` set (enumerate_variables ?c')) 
    = (fst (t_small_step_fun t' (?c', IMP_State_To_IMP_Minus ?s1' ?n)),
       snd  (t_small_step_fun t' (?c', IMP_State_To_IMP_Minus ?s1' ?n)) 
      |` set (enumerate_variables ?c'))" 
    by (auto simp: t_small_step_fun_restrict_variables)
  ultimately obtain s2' where "t_small_step_fun t' (?c', IMP_State_To_IMP_Minus ?s1' ?n)
    = (SKIP, s2')" "s2' |` set (enumerate_variables ?c') = s2" by auto (metis prod.collapse)

  moreover obtain t'' s2'' where "t'' \<le> t" "(c, ?s1') \<Rightarrow>\<^bsup>t''\<^esup> s2''" 
    using \<open>\<forall>s1. I \<subseteq>\<^sub>m Some o s1 \<longrightarrow> (\<exists>s2. \<exists>t' \<le> t. (c, s1) \<Rightarrow>\<^bsup>t'\<^esup> s2)\<close>
    using \<open>I \<subseteq>\<^sub>m Some \<circ> IMP_Minus_State_To_IMP s1 (t + max_input_bits c I r + 1)\<close>
    by blast
  moreover have "?guess_range \<le> i \<Longrightarrow> s1 (var_bit_to_var (v, i)) \<noteq> Some One" for i v 
  proof(cases "(var_bit_to_var (v, i)) \<in> set (enumerate_variables ?c')")
    case True
    assume "?guess_range \<le> i"
    hence "?I (var_bit_to_var (v, i)) = Some Zero" 
      using set_mp[OF IMP_To_IMP_Minus_variables 
          \<open>(var_bit_to_var (v, i)) \<in> set (enumerate_variables ?c')\<close>] 
      by (auto simp: IMP_State_To_IMP_Minus_partial_def 
              intro!: var_bit_in_IMP_Minus_variables 
              split: option.splits)
    thus ?thesis using \<open>(?I|` set (enumerate_variables ?c')) \<subseteq>\<^sub>m s1\<close> 
      by(auto simp: map_le_def dom_def)
  next
    case False
    then show ?thesis using \<open>dom s1 = set (enumerate_variables ?c')\<close> by auto
  qed
   
  moreover hence "finite (range (IMP_Minus_State_To_IMP s1 ?n))" 
    "Max (range (IMP_Minus_State_To_IMP s1 ?n)) < 2 ^ ?guess_range" 
    using all_bits_geq_k_Zero_then_IMP_Minus_State_To_IMP_range_limited by blast+
  ultimately have "s2' = IMP_State_To_IMP_Minus s2'' ?n" 
    using IMP_Minus_To_IMP_aux max_const_less_two_to_the_max_input_bits
    by(auto simp: power_add algebra_simps mult_2 trans_less_add2)

  have "G v = Some y \<Longrightarrow> s2'' v = y" for v y 
  proof -
    assume "G v = Some y" 
    hence "v \<in> set (vars c)" 
      using \<open>dom G \<subseteq> set (vars c)\<close> by auto
    hence "\<forall>i < ?n. var_bit_to_var (v, i) \<in> set (enumerate_variables ?c')" 
      by(auto simp: var_bit_in_IMP_Minus_variables)
    moreover hence "i < ?n \<longrightarrow> s2 (var_bit_to_var (v, i)) = ?G (var_bit_to_var (v, i))" for i
      using \<open>(?G|` set (enumerate_variables ?c')) \<subseteq>\<^sub>m s2\<close> \<open>G v = Some y\<close>
      by(auto simp:  map_le_def
          IMP_State_To_IMP_Minus_def dom_def
          IMP_State_To_IMP_Minus_partial_def map_comp_def split: option.splits) 
    moreover hence "i < ?n \<longrightarrow> s2' (var_bit_to_var (v, i)) = ?G (var_bit_to_var (v, i))" for i 
      using \<open>s2' |` set (enumerate_variables ?c') = s2\<close> 
        \<open>\<forall>i < ?n. var_bit_to_var (v, i) \<in> set (enumerate_variables ?c')\<close> by auto
    ultimately have "i < ?n \<Longrightarrow> map_option (\<lambda>x. nth_bit x i) (G v) = Some (nth_bit (s2'' v) i)" for i 
      using  \<open>s2' = IMP_State_To_IMP_Minus s2'' ?n\<close> \<open>G v = Some y\<close>
      by(auto simp: IMP_State_To_IMP_Minus_def 
          IMP_State_To_IMP_Minus_partial_def
          IMP_State_To_IMP_Minus_with_operands_a_b_def)
    show "s2'' v = y"
    proof(rule all_bits_equal_then_equal[where ?n = "?n"], goal_cases)
      case 1
      find_theorems "_ \<and> _ \<Longrightarrow> _"
      have "Max (range s2'') < 2 ^ (max_input_bits c I r + t'')"
        apply(rule 
                conjunct2[OF IMP_space_growth[OF \<open>(c, ?s1') \<Rightarrow>\<^bsup>t''\<^esup> s2''\<close> 
                                                       \<open>finite (range (IMP_Minus_State_To_IMP s1 ?n))\<close>, where ?k="?guess_range"]])
        using \<open>Max (range (IMP_Minus_State_To_IMP s1 ?n)) < 2 ^ ?guess_range\<close> max_const_less_two_to_the_max_input_bits 
        by auto
      also have "... \<le> 2 ^ (t + max_input_bits c I r)" 
        using \<open>t'' \<le> t\<close>
        by auto
      finally have "s2'' v < 2 ^ (t + max_input_bits c I r)"
        using \<open>(c, IMP_Minus_State_To_IMP s1 (t + max_input_bits c I r + 1)) \<Rightarrow>\<^bsup> t'' \<^esup> s2''\<close>
          \<open>finite (range (IMP_Minus_State_To_IMP s1 (t + max_input_bits c I r + 1)))\<close>
          finite_range_stays_finite
        by auto
      thus ?case
        apply(rule less_le_trans[where ?y="2 ^ (t + max_input_bits c I r)"])
        by auto
    next
      case 2
      then show ?case
        by (smt (verit, del_insts) Max_ge Nat.add_0_right \<open>G v = Some y\<close> \<open>finite (ran G)\<close> assms(3) less_exp less_nat_zero_code
            linorder_not_less nat_add_left_cancel_less order_le_less_trans power_one_right power_strict_increasing_iff ranI)
    next
      case (3 i)
      then show ?case
        using \<open>G v = Some y\<close>
              \<open>\<And>i. i < t + max_input_bits c I r + 1 \<Longrightarrow> map_option (\<lambda>x. nth_bit x i) (G v) = Some (nth_bit (s2'' v) i)\<close>
        by auto 
    qed
  qed
  hence "G \<subseteq>\<^sub>m Some \<circ> s2''" by(auto simp: map_le_def)

  show ?thesis using \<open>t'' \<le> t\<close> \<open>(c, ?s1') \<Rightarrow>\<^bsup>t''\<^esup> s2''\<close> \<open>I \<subseteq>\<^sub>m Some \<circ> ?s1'\<close> \<open>G \<subseteq>\<^sub>m Some \<circ> s2''\<close>
    by auto
qed
 
end