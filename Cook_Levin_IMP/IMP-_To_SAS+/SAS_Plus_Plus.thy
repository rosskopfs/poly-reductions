(*
  Author: Mohammad Abdulaziz, Fred Kurz, Florian Keßler
*)
theory SAS_Plus_Plus
  imports "Verified_SAT_Based_AI_Planning.SAS_Plus_Representation" 
    "Verified_SAT_Based_AI_Planning.SAS_Plus_Semantics"
begin

section "SAS++ Representation"

text \<open> We introduce SAS++, an adopted version of SAS+ that allows for partial initial states
      where not all variables need to have a defined value. \<close>

definition "is_valid_problem_sas_plus_plus \<Psi> 
  \<equiv> let ops = operators_of \<Psi>
      ; vs = variables_of \<Psi>
      ; I = initial_of \<Psi>
      ; G = goal_of \<Psi>
      ; D = range_of \<Psi>
    in list_all (\<lambda>v. D v \<noteq> None) vs
    \<and> list_all (is_valid_operator_sas_plus \<Psi>) ops 
    \<and> list_all (\<lambda> v. length (the (D v)) > 0) vs  
    \<and> (\<forall>v. I v \<noteq> None \<longrightarrow> ListMem v vs) 
    \<and> (\<forall>v. I v \<noteq> None \<longrightarrow> ListMem (the (I v)) (the (D v)))
    \<and> (\<forall>v. G v \<noteq> None \<longrightarrow> ListMem v vs)
    \<and> (\<forall>v. G v \<noteq> None \<longrightarrow> ListMem (the (G v)) (the (D v)))" 


lemma is_valid_problem_sas_plus_plus_then:
  fixes \<Psi>::"('v,'d) sas_plus_problem"
  assumes "is_valid_problem_sas_plus_plus \<Psi>"
  shows "\<forall>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). (\<R>\<^sub>+ \<Psi> v) \<noteq> {}"
    and "\<forall>op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+). is_valid_operator_sas_plus \<Psi> op"
    and "dom ((\<Psi>)\<^sub>I\<^sub>+) \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>v \<in> dom ((\<Psi>)\<^sub>I\<^sub>+). the (((\<Psi>)\<^sub>I\<^sub>+) v) \<in> \<R>\<^sub>+ \<Psi> v"
    and "dom ((\<Psi>)\<^sub>G\<^sub>+) \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>v \<in> dom ((\<Psi>)\<^sub>G\<^sub>+). the (((\<Psi>)\<^sub>G\<^sub>+) v) \<in> \<R>\<^sub>+ \<Psi> v" 
proof -
  let ?vs = "sas_plus_problem.variables_of \<Psi>"
    and ?ops = "sas_plus_problem.operators_of \<Psi>"
    and ?I = "sas_plus_problem.initial_of \<Psi>"
    and ?G = "sas_plus_problem.goal_of \<Psi>"
    and ?D = "sas_plus_problem.range_of \<Psi>"
  {
    fix v 
    have "(?D v \<noteq> None \<and> ?D v \<noteq> Some []) \<longleftrightarrow> ((\<R>\<^sub>+ \<Psi> v) \<noteq> {})"
      by (cases "?D v"; (auto simp: range_of'_def))
  } note nb = this
  have nb\<^sub>1: "\<forall>v \<in> set ?vs. ?D v \<noteq> None"
    and nb\<^sub>4: "\<forall>v \<in> set ?vs. length (the (?D v)) > 0" 
    and "\<forall>op \<in> set ?ops. is_valid_operator_sas_plus \<Psi> op"
    and "\<forall>v. ?I v \<noteq> None \<longrightarrow> v \<in> set ?vs"
    and nb\<^sub>2: "\<forall>v. ?I v \<noteq> None \<longrightarrow> the (?I v) \<in> set (the (?D v))"
    and "\<forall>v. ?G v \<noteq> None \<longrightarrow> v \<in> set ?vs"
    and nb\<^sub>3: "\<forall>v. ?G v \<noteq> None \<longrightarrow> the (?G v) \<in> set (the (?D v))"
    using assms 
    unfolding SAS_Plus_Plus.is_valid_problem_sas_plus_plus_def Let_def 
      list_all_iff ListMem_iff 
    by argo+
  then have G3: "\<forall>op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+). is_valid_operator_sas_plus \<Psi> op"
    and G4: "dom ((\<Psi>)\<^sub>I\<^sub>+) \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and G5: "dom ((\<Psi>)\<^sub>G\<^sub>+) \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    unfolding variables_of_def operators_of_def
    by auto+
  moreover {
    fix v
    assume "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    then have "?D v \<noteq> None"
      using nb\<^sub>1 
      by force+
  } note G6 = this
  moreover {
    fix v
    assume "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    then have "(\<R>\<^sub>+ \<Psi> v) \<noteq> {}"
      using G6 nb\<^sub>4
      by(auto simp: range_of'_def split: option.splits)
  }
  moreover {
    fix v
    assume "v \<in> dom ((\<Psi>)\<^sub>I\<^sub>+)"
    moreover have "((\<Psi>)\<^sub>I\<^sub>+) v \<noteq> None"
      using calculation
      by blast+
    moreover {
      have "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
        using G4 calculation(1)
        by fast
      then have "sas_plus_problem.range_of \<Psi> v \<noteq> None" 
        using range_of_not_empty
        unfolding range_of'_def
        using G6 
        by fast+
      hence "set (the (?D v)) = \<R>\<^sub>+ \<Psi> v" 
        by (simp add: \<open>sas_plus_problem.range_of \<Psi> v \<noteq> None\<close> option.case_eq_if range_of'_def)
    }
    ultimately have "the (((\<Psi>)\<^sub>I\<^sub>+) v) \<in> \<R>\<^sub>+ \<Psi> v"
      using nb\<^sub>2
      by force
  }
  moreover {
    fix v
    assume "v \<in> dom ((\<Psi>)\<^sub>G\<^sub>+)"
    then have "((\<Psi>)\<^sub>G\<^sub>+) v \<noteq> None"
      by blast
    moreover {
      have "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
        using G5 calculation(1)
        by fast
      then have "sas_plus_problem.range_of \<Psi> v \<noteq> None" 
        using range_of_not_empty
        using G6
        by fast+
      hence "set (the (?D v)) = \<R>\<^sub>+ \<Psi> v" 
        by (simp add: \<open>sas_plus_problem.range_of \<Psi> v \<noteq> None\<close> option.case_eq_if range_of'_def)
    }
    ultimately have "the (((\<Psi>)\<^sub>G\<^sub>+) v) \<in> \<R>\<^sub>+ \<Psi> v"
      using nb\<^sub>3
      by auto
  }
  ultimately show "\<forall>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). (\<R>\<^sub>+ \<Psi> v) \<noteq> {}"
    and "\<forall>op \<in> set((\<Psi>)\<^sub>\<O>\<^sub>+). is_valid_operator_sas_plus \<Psi> op"
    and "dom ((\<Psi>)\<^sub>I\<^sub>+) \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>v \<in> dom ((\<Psi>)\<^sub>I\<^sub>+). the (((\<Psi>)\<^sub>I\<^sub>+) v) \<in> \<R>\<^sub>+ \<Psi> v"
    and "dom ((\<Psi>)\<^sub>G\<^sub>+) \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>v \<in> dom ((\<Psi>)\<^sub>G\<^sub>+). the (((\<Psi>)\<^sub>G\<^sub>+) v) \<in> \<R>\<^sub>+ \<Psi> v"
    by auto
qed

section "SAS++ Semantics"

subsection "Serial Execution Semantics"

text \<open> Similarly, serial SAS++ solutions are defined like in SAS+, but instead of having a single
      initial state, we assert that there exists one that conforms to the partial initial state,
      and from which a goal state is reachable, using the SAS+ definition of executing a plan. \<close>

definition is_serial_solution_for_problem_sas_plus_plus
  :: "('variable, 'domain) sas_plus_problem \<Rightarrow> ('variable, 'domain) sas_plus_plan \<Rightarrow> bool" 
  where "is_serial_solution_for_problem_sas_plus_plus \<Psi> \<psi>
    \<equiv> let 
        I = sas_plus_problem.initial_of \<Psi>
        ; G = sas_plus_problem.goal_of \<Psi>
        ; ops = sas_plus_problem.operators_of \<Psi>
      in (\<exists>I'. I \<subseteq>\<^sub>m I' \<and> dom I' = set ((\<Psi>)\<^sub>\<V>\<^sub>+)
        \<and> (\<forall> v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). the (I' v) \<in> range_of' \<Psi> v)
        \<and> G \<subseteq>\<^sub>m execute_serial_plan_sas_plus I' \<psi> 
        \<and> list_all (\<lambda>op. ListMem op ops) \<psi>)" 

fun chain_applicable where
"chain_applicable s [] = True" |
"chain_applicable s (op # ops) = (is_operator_applicable_in s op \<and> chain_applicable (s \<then>\<^sub>+ op) ops)" 

fun chain_applicable_prefix where
"chain_applicable_prefix s [] = []" |
"chain_applicable_prefix s (op # ops) = (if is_operator_applicable_in s op 
  then op # (chain_applicable_prefix (s \<then>\<^sub>+ op) ops) else [])"

lemma chain_applicable_append[simp]: "chain_applicable s (as @ bs)
  \<longleftrightarrow> (chain_applicable s as \<and> (chain_applicable (execute_serial_plan_sas_plus s as) bs))" 
  apply(induction as arbitrary: s)
  by(auto)

lemma chain_applicable_prefix_chain_applicable[simp]: 
  "chain_applicable s (chain_applicable_prefix s ops)"
  apply(induction ops arbitrary: s)
  by(auto)

lemma execute_chain_applicable_prefix: "execute_serial_plan_sas_plus 
  s (chain_applicable_prefix s ops) = execute_serial_plan_sas_plus s ops"
  apply(induction ops arbitrary: s)
  by(auto)

lemma set_of_chain_applicable_prefix: "set (chain_applicable_prefix s ops) \<subseteq> set ops"
  apply(induction ops arbitrary: s)
  by(auto)

lemma length_of_chain_applicable_prefix: "length (chain_applicable_prefix s ops) \<le> length ops"
  apply(induction ops arbitrary: s)
  by(auto)

lemma execute_serial_plan_sas_plus_append[simp]: "chain_applicable s as 
  \<Longrightarrow> execute_serial_plan_sas_plus s (as @ bs) 
    = execute_serial_plan_sas_plus (execute_serial_plan_sas_plus s as) bs"
  apply(induction as arbitrary: s)
  by auto

lemma dom_of_execute_serial_plan_sas_plus: "is_valid_problem_sas_plus P
  \<Longrightarrow> \<forall>op \<in> set ops. op \<in> set ((P)\<^sub>\<O>\<^sub>+)
  \<Longrightarrow> dom s = set ((P)\<^sub>\<V>\<^sub>+)
  \<Longrightarrow> dom (execute_serial_plan_sas_plus s ops) = set ((P)\<^sub>\<V>\<^sub>+)" 
proof(induction ops arbitrary: s)
  case Nil
  then show ?case by auto
next
  case (Cons op ops)
  hence "\<forall>(v, a)\<in>set (effect_of op). v \<in> set ((P)\<^sub>\<V>\<^sub>+)"
    apply -
    apply(rule is_valid_operator_sas_plus_then(3))
    by (auto simp: is_valid_problem_sas_plus_def Let_def list_all_def)
  hence "dom (s \<then>\<^sub>+ op) = set ((P)\<^sub>\<V>\<^sub>+)" using Cons  apply(auto) 
    using map_of_SomeD by fastforce
  thus ?case using Cons by simp
qed
 

end