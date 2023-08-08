\<^marker>\<open>creator Florian Keßler\<close>

section "SAS++ to SAS+"

theory SAS_Plus_Plus_To_SAS_Plus
  imports SAS_Plus_Plus
begin 

text \<open> We give a reduction from SAS++ to SAS+. The challenge here is to replace the semantics of 
       SAS++ that permit initial states with some variables unspecified to be guessed by the solver,
       by SAS+, where initial states need to specify all variables. We do this by constructing 
       SAS+ problems where every solution plan is divided into two phases, first one where 
       unspecified variables in the initial state are guessed, and the one where the SAS++ problem
       is simulated. \<close>

datatype 'v variable =  Var 'v | Stage
datatype 'd domain_element = DE 'd | Init | NonInit

instantiation variable :: (order_bot) order_bot
begin

fun less_eq_variable :: "'a variable \<Rightarrow> 'a variable \<Rightarrow> bool" where
  "less_eq_variable (Var v1) (Var v2) \<longleftrightarrow> v1 \<le> v2"
| "less_eq_variable Stage _ \<longleftrightarrow> True"
| "less_eq_variable _ Stage \<longleftrightarrow> False"

definition less_variable :: "'a variable \<Rightarrow> 'a variable \<Rightarrow> bool" where
  "less_variable c1 c2 = (c1 \<le> c2 \<and> \<not> c2 \<le> c1)"

definition bot_variable :: "'a variable" where
  "bot_variable = Stage"

instance
proof(standard, goal_cases)
  case 1 show ?case by (simp add: less_variable_def)
next
  case 2 show ?case
    using less_eq_variable.elims(3) by fastforce
next
  case 3 thus ?case by (fastforce elim: less_eq_variable.elims)
next
  case 4 thus ?case by (fastforce elim: less_eq_variable.elims)
next
  case 5 show ?case unfolding bot_variable_def by simp
qed
end

instantiation domain_element :: (order_bot) order_bot
begin

fun less_eq_domain_element :: "'a domain_element \<Rightarrow> 'a domain_element \<Rightarrow> bool" where
  "less_eq_domain_element (DE v1) (DE v2) \<longleftrightarrow> v1 \<le> v2"
| "less_eq_domain_element Init _ \<longleftrightarrow> True"
| "less_eq_domain_element _ Init \<longleftrightarrow> False"
| "less_eq_domain_element NonInit _ \<longleftrightarrow> True"
| "less_eq_domain_element _ NonInit \<longleftrightarrow> False"

definition less_domain_element :: "'a domain_element \<Rightarrow> 'a domain_element \<Rightarrow> bool" where
  "less_domain_element c1 c2 = (c1 \<le> c2 \<and> \<not> c2 \<le> c1)"

definition bot_domain_element :: "'a domain_element" where
  "bot_domain_element = Init"

instance
proof(standard, goal_cases)
  case 1 show ?case by (simp add: less_domain_element_def)
next
  case 2 show ?case
    using less_eq_domain_element.elims(3) by fastforce
next
  case 3 thus ?case by (fastforce elim: less_eq_domain_element.elims)
next
  case 4 thus ?case by (fastforce elim: less_eq_domain_element.elims)
next
  case 5 show ?case unfolding bot_domain_element_def by simp
qed
end

                                                               
type_synonym ('v, 'd) state = "('v, 'd) State_Variable_Representation.state"
type_synonym ('v, 'd) operator = "('v variable, 'd domain_element) sas_plus_operator"
type_synonym ('v, 'd) problem = "('v variable, 'd domain_element) sas_plus_problem"

definition SAS_Plus_Plus_State_To_SAS_Plus:: 
  "('d domain_element \<times> ('v, 'd) state) \<Rightarrow> ('v variable, 'd domain_element) state" where
"SAS_Plus_Plus_State_To_SAS_Plus is = ((\<lambda>x. Some (DE x)) \<circ>\<^sub>m (snd is)
  \<circ>\<^sub>m (\<lambda>x. (case x of Var x \<Rightarrow> Some x | Stage \<Rightarrow> None)))(Stage \<mapsto> (fst is))"

lemma SAS_Plus_Plus_State_To_SAS_Plus_eq_iff_snd_eq[simp]:
  "SAS_Plus_Plus_State_To_SAS_Plus (i, s) = SAS_Plus_Plus_State_To_SAS_Plus (i, s') 
  \<longleftrightarrow> s = s'" 
  apply (auto simp: SAS_Plus_Plus_State_To_SAS_Plus_def map_comp_def fun_eq_iff 
      split: option.splits variable.splits)
  by (metis option.exhaust_sel)

lemma SAS_Plus_Plus_State_To_SAS_Plus_Stage[simp]: 
  "SAS_Plus_Plus_State_To_SAS_Plus (i, s) Stage = Some i"
  by (auto simp: SAS_Plus_Plus_State_To_SAS_Plus_def)

lemma SAS_Plus_Plus_State_To_SAS_Plus_update_stage[simp]:
  "SAS_Plus_Plus_State_To_SAS_Plus (a, s)(Stage \<mapsto> b) = SAS_Plus_Plus_State_To_SAS_Plus (b, s)"
  by (auto simp: SAS_Plus_Plus_State_To_SAS_Plus_def map_comp_def fun_eq_iff)

lemma SAS_Plus_Plus_State_To_SAS_Plus_update_Var[simp]:
  "SAS_Plus_Plus_State_To_SAS_Plus (i, s)(Var x \<mapsto> DE y) 
    = SAS_Plus_Plus_State_To_SAS_Plus(i, s(x \<mapsto> y))"
  by (auto simp: SAS_Plus_Plus_State_To_SAS_Plus_def map_comp_def fun_eq_iff 
      split: option.splits variable.splits)

lemma SAS_Plus_Plus_State_To_SAS_Plus_map_le[simp]: 
  "SAS_Plus_Plus_State_To_SAS_Plus (a, s) \<subseteq>\<^sub>m m 
    \<Longrightarrow> SAS_Plus_Plus_State_To_SAS_Plus (b, s) \<subseteq>\<^sub>m m(Stage \<mapsto> b)" 
  by(auto simp: SAS_Plus_Plus_State_To_SAS_Plus_def map_le_def map_comp_def 
      split: option.splits variable.splits)

lemma Stage_map_le_SAS_Plus_Plus_State_To_SAS_Plus[simp]:
  "[Stage \<mapsto> i] \<subseteq>\<^sub>m SAS_Plus_Plus_State_To_SAS_Plus (i, s)"
  by(auto simp: SAS_Plus_Plus_State_To_SAS_Plus_def map_le_def)

lemma Var_not_in_map_Var_iff[simp]: "Var x \<notin> Var ` S \<longleftrightarrow> x \<notin> S" by auto

lemma dom_of_SAS_Plus_Plus_State_To_SAS_Plus: 
  "dom (SAS_Plus_Plus_State_To_SAS_Plus (i, s)) = { Stage } \<union> (Var ` dom s)" 
  by(auto simp: SAS_Plus_Plus_State_To_SAS_Plus_def map_comp_def 
      split: option.splits variable.splits)

lemma SAS_Plus_Plus_State_To_SAS_Plus_map_le_SAS_Plus_Plus_State_To_SAS_Plus[simp]:
  "SAS_Plus_Plus_State_To_SAS_Plus (a, s1) \<subseteq>\<^sub>m SAS_Plus_Plus_State_To_SAS_Plus (b, s2)
    \<longleftrightarrow> (a = b \<and> s1 \<subseteq>\<^sub>m s2)" 
  apply(auto simp: map_le_def dom_of_SAS_Plus_Plus_State_To_SAS_Plus)
   apply(auto simp: SAS_Plus_Plus_State_To_SAS_Plus_def map_comp_def split: option.splits)
  by force+

definition SAS_Plus_Plus_Operator_To_SAS_Plus_Operator:: 
  "('v, 'd) sas_plus_operator \<Rightarrow> ('v, 'd) operator" where
"SAS_Plus_Plus_Operator_To_SAS_Plus_Operator op = 
  \<lparr> precondition_of = (Stage, NonInit) # (map (\<lambda> x. (Var (fst x), DE (snd x))) (precondition_of op)),
    effect_of = (map (\<lambda> x. (Var (fst x), DE (snd x))) (effect_of op))\<rparr>"

lemma dom_of_map_of_map[simp]: 
  "dom (map_of (map (\<lambda>x. (Var (fst x), DE (snd x))) l)) = (\<lambda>x. Var (fst x)) ` set l" 
  apply(induction l)
  apply(auto)
  by (metis (mono_tags, lifting) domD fst_conv imageI)

lemma map_of_map_eq_None_iff[simp]: "(map_of (map (\<lambda>x. (Var (fst x), DE (snd x))) l) (Var y) = None)
  \<longleftrightarrow> (y \<notin> fst ` set l)"
  apply(induction l)
  by(auto)

lemma map_of_map_eq_Some_iff[simp]: "(map_of (map (\<lambda>x. (Var (fst x), DE (snd x))) l) (Var x) = Some (DE y))
  \<longleftrightarrow> (map_of l x = Some y)"
  apply(induction l)
  by(auto)

lemma SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_applicable[simp]: 
  "is_operator_applicable_in (SAS_Plus_Plus_State_To_SAS_Plus (i, s)) 
    (SAS_Plus_Plus_Operator_To_SAS_Plus_Operator op)
  \<longleftrightarrow> (i = NonInit \<and> is_operator_applicable_in s op)"
  apply(auto simp: SAS_Plus_Plus_State_To_SAS_Plus_def map_comp_def 
      SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_def)
    apply(simp_all add: map_le_def)
   apply(auto split: option.splits variable.splits)
    apply(frule map_of_SomeD)
    apply auto
  by (metis domI weak_map_of_SomeI)+

lemma SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_execute[simp]:
  "SAS_Plus_Plus_State_To_SAS_Plus (i, s) ++ map_of (effect_of (SAS_Plus_Plus_Operator_To_SAS_Plus_Operator op))
  = SAS_Plus_Plus_State_To_SAS_Plus(i, s \<then>\<^sub>+ op)" 
  using map_of_SomeD
  apply(auto simp: SAS_Plus_Plus_State_To_SAS_Plus_def map_comp_def fun_eq_iff map_add_def 
      SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_def split: option.splits variable.splits)
            apply force+
          prefer 9 using map_of_SomeD apply fastforce
  using map_of_map_eq_None_iff map_of_map_eq_Some_iff
  by (metis (mono_tags, lifting) map_of_eq_None_iff map_of_map_eq_Some_iff option.simps 
      option.distinct domI  domIff option.simps)+

lemma execute_SAS_Plus_Plus_ops_in_SAS_Plus[simp]:
  "execute_serial_plan_sas_plus (SAS_Plus_Plus_State_To_SAS_Plus (NonInit, s))
    (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator ops) 
    = SAS_Plus_Plus_State_To_SAS_Plus (NonInit, execute_serial_plan_sas_plus s ops)"
  apply(induction ops arbitrary: s)
   apply(simp add: SAS_Plus_Plus_State_To_SAS_Plus_def 
      SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_def)
  by(auto simp: SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_applicable[simplified])

fun thef:: "'a list option \<Rightarrow> 'a list" where 
"thef None = []"|
"thef (Some x) = x"



definition initialization_operators:: "('v, 'd) sas_plus_problem \<Rightarrow> ('v, 'd) operator list" where
"initialization_operators P = 
  concat (map (\<lambda> v. (if v \<in> dom ((P)\<^sub>I\<^sub>+) then [] 
    else map (\<lambda> y. \<lparr> precondition_of = [(Stage, Init)],  effect_of = [(Var v, DE y)]\<rparr>) 
      (thef (range_of P v)))) ((P)\<^sub>\<V>\<^sub>+))"

lemma in_initialization_operators_iff: 
  "\<lparr>precondition_of = [(Stage, Init)], effect_of = [(Var x, DE y)]\<rparr> 
    \<in> set (initialization_operators P) 
  \<longleftrightarrow> (x \<in> set ((P)\<^sub>\<V>\<^sub>+) \<and> ((P)\<^sub>I\<^sub>+) x = None \<and> y \<in> set (thef (range_of P x)))"
  by(auto simp: initialization_operators_def)

lemma Stage_after_initialization_operator[simp]:
  "op \<in> set (initialization_operators P) \<Longrightarrow> (s ++ map_of (effect_of op)) Stage = s Stage" 
  by(auto simp: initialization_operators_def)

definition initial_state:: 
  "('v, 'd) sas_plus_problem \<Rightarrow> ('v variable, 'd domain_element) state" where
"initial_state P = SAS_Plus_Plus_State_To_SAS_Plus (Init, (\<lambda> v.
  (if v \<in> set ((P)\<^sub>\<V>\<^sub>+) then Some (case ((P)\<^sub>I\<^sub>+) v of 
        Some val \<Rightarrow> val |
        None \<Rightarrow> (the (range_of P v)) ! 0)
   else None)))"

definition SAS_Plus_Plus_To_SAS_Plus:: "('v, 'd) sas_plus_problem \<Rightarrow> ('v, 'd) problem" where
"SAS_Plus_Plus_To_SAS_Plus P = \<lparr> variables_of = Stage # (map Var ((P)\<^sub>\<V>\<^sub>+)),
      operators_of = \<lparr> precondition_of = [(Stage, Init)], effect_of = [(Stage, NonInit)]\<rparr> 
        # (initialization_operators P) 
        @ (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator ((P)\<^sub>\<O>\<^sub>+)), 
      initial_of = initial_state P ,
      goal_of = SAS_Plus_Plus_State_To_SAS_Plus (NonInit, ((P)\<^sub>G\<^sub>+)),
      range_of = ((\<lambda>x. Some (map DE x)) \<circ>\<^sub>m (range_of P) 
        \<circ>\<^sub>m (\<lambda>x. (case x of Var x \<Rightarrow> Some x | Stage \<Rightarrow> None)))(Stage \<mapsto> [Init, NonInit])\<rparr>"

lemma SAS_Plus_Plus_To_SAS_Plus_valid: 
  assumes "is_valid_problem_sas_plus_plus P"
  shows "is_valid_problem_sas_plus (SAS_Plus_Plus_To_SAS_Plus P)" 
  using assms apply(auto simp: is_valid_problem_sas_plus_plus_def is_valid_problem_sas_plus_def 
      SAS_Plus_Plus_To_SAS_Plus_def list_all_def is_valid_operator_sas_plus_def Let_def
      initialization_operators_def SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_def ListMem_iff)
               apply auto
              apply fastforce
             apply fastforce
            apply fastforce
           apply fastforce
          apply blast
         apply blast
         apply(auto simp: initial_state_def map_comp_def SAS_Plus_Plus_State_To_SAS_Plus_def 
        split: variable.splits if_splits option.splits)
  by (meson assms is_valid_problem_sas_plus_plus_then(1) range_of_not_empty)+

lemma stage_of_initial_state[simp]: "((SAS_Plus_Plus_To_SAS_Plus P)\<^sub>I\<^sub>+) Stage = Some Init" 
  by(auto simp: SAS_Plus_Plus_To_SAS_Plus_def initial_state_def)

definition initialization_sequence:: "('v \<times> 'd) list \<Rightarrow> ('v, 'd) operator list" where
  "initialization_sequence vs = map (\<lambda>v. \<lparr> precondition_of = [(Stage, Init)],  
      effect_of = [(Var (fst v), DE (snd v))]\<rparr>) vs"

lemma result_of_initialization_sequence[simp]: 
  assumes "I Stage = Some Init"
    "distinct (map fst vs)"
  shows "execute_serial_plan_sas_plus I (initialization_sequence vs) = 
  I ++ SAS_Plus_Plus_State_To_SAS_Plus (Init, map_of vs)"
using assms proof (induction vs arbitrary: I)
  case Nil
  then show ?case using Nil
    by (auto simp: initialization_sequence_def SAS_Plus_Plus_State_To_SAS_Plus_def map_add_def)
next
  case (Cons v vs)
  hence "execute_serial_plan_sas_plus I (initialization_sequence (v # vs)) 
    = execute_serial_plan_sas_plus (I(Var (fst v) \<mapsto> DE (snd v))) (initialization_sequence vs)"
    by (auto simp: initialization_sequence_def map_le_def)
  also have "... = I ++ SAS_Plus_Plus_State_To_SAS_Plus (Init, map_of (v # vs))" using Cons
    by(auto simp: SAS_Plus_Plus_State_To_SAS_Plus_def map_add_def fun_eq_iff map_comp_def 
        rev_image_eqI split: option.splits variable.splits)
  ultimately show ?case by metis
qed

lemma initialization_sequence_chain_applicable_condition[simp]:
  assumes "s Stage = Some Init"
  shows "chain_applicable s (initialization_sequence vs)"
  using assms apply(induction vs arbitrary: s)
  by(auto simp:  initialization_sequence_def map_le_def)

lemma map_of_conact_map_cases_eq_Some[simp]: 
  "map_of (concat (map (\<lambda>v. case m v of None \<Rightarrow> [(v, f v)] | Some x \<Rightarrow> []) l)) x = Some y 
  \<longleftrightarrow> (x \<in> set l \<and> f x = y \<and> m x = None)"
proof
  assume "map_of (concat (map (\<lambda>v. case m v of None \<Rightarrow> [(v, f v)] | Some x \<Rightarrow> []) l)) x = Some y" 
  then show "x \<in> set l \<and> f x = y \<and> m x = None"  
    apply -
    apply(drule map_of_SomeD)
    by(auto)
next
  assume "x \<in> set l \<and> f x = y \<and> m x = None"
  hence "(x, y) \<in> set (concat (map (\<lambda>v. case m v of None \<Rightarrow> [(v, f v)] | Some x \<Rightarrow> []) l))"
    by auto
  moreover have "\<forall>y'. (x, y') \<in> set (concat (map (\<lambda>v. case m v of None \<Rightarrow> [(v, f v)] | Some x \<Rightarrow> []) l))
    \<longrightarrow> y' = f x" by auto
  ultimately show "map_of (concat (map (\<lambda>v. case m v of None \<Rightarrow> [(v, f v)] | Some x \<Rightarrow> []) l)) x = Some y"
    by (metis (no_types, lifting) map_of_SomeD weak_map_of_SomeI)
qed

lemma map_of_conact_map_cases_eq_None[simp]: 
  "map_of (concat (map (\<lambda>v. case m v of None \<Rightarrow> [(v, f v)] | Some x \<Rightarrow> []) l)) x = None 
  \<longleftrightarrow> (x \<notin> set l \<or> m x \<noteq> None)"
proof -
  have "(map_of (concat (map (\<lambda>v. case m v of None \<Rightarrow> [(v, f v)] | Some x \<Rightarrow> []) l)) x = None)
    = (\<not>(\<exists>y. map_of (concat (map (\<lambda>v. case m v of None \<Rightarrow> [(v, f v)] | Some x \<Rightarrow> []) l)) x = Some y))"
    by fastforce
  also have "... = (\<not>(\<exists>y. x \<in> set l \<and> f x = y \<and> m x = None))" by auto
  ultimately show ?thesis by simp
qed

lemma distinct_map_fst_concat[simp]:
  "distinct (map fst (concat (map (\<lambda>v. case m v of None \<Rightarrow> [(v, f v)] | Some x \<Rightarrow> []) (remdups l))))"
  apply(induction l) 
  by(auto split: option.splits)

lemma length_concat_map[simp]: 
  "length (concat (map (\<lambda>v. case m v of None \<Rightarrow> [f v] | Some _ \<Rightarrow> []) (remdups l))) \<le> length l"
  apply(induction l)
  by(auto split: option.splits)

subsection \<open>Correctness\<close>

lemma SAS_Plus_Plus_To_SAS_Plus:
  assumes "is_valid_problem_sas_plus_plus P" 
    "is_serial_solution_for_problem_sas_plus_plus P plan"
  shows "\<exists>prefix. length prefix \<le> length ((P)\<^sub>\<V>\<^sub>+) + 1 
    \<and> is_serial_solution_for_problem (SAS_Plus_Plus_To_SAS_Plus P) 
        (prefix @ (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator plan))" 
proof -
  obtain I where I_def: "((P)\<^sub>I\<^sub>+) \<subseteq>\<^sub>m I \<and> dom I = set ((P)\<^sub>\<V>\<^sub>+)
        \<and> (\<forall> v \<in> set ((P)\<^sub>\<V>\<^sub>+). the (I v) \<in> range_of' P v)
        \<and> ((P)\<^sub>G\<^sub>+) \<subseteq>\<^sub>m execute_serial_plan_sas_plus I plan
        \<and> list_all (\<lambda>op. ListMem op ((P)\<^sub>\<O>\<^sub>+)) plan" using assms 
    by (auto simp: is_serial_solution_for_problem_sas_plus_plus_def Let_def)
  let ?P' = "SAS_Plus_Plus_To_SAS_Plus P"
  let ?missing_vs = "(concat (map (\<lambda>v. case ((P)\<^sub>I\<^sub>+) v of Some _ \<Rightarrow> [] |
    None \<Rightarrow> [(v, the (I v))]) (remdups ((P)\<^sub>\<V>\<^sub>+))))"
  let ?prefix' = "initialization_sequence ?missing_vs"
  let ?prefix = "?prefix' @ [\<lparr> precondition_of = [(Stage, Init)], effect_of = [(Stage, NonInit)]\<rparr>]"
  have "execute_serial_plan_sas_plus ((?P')\<^sub>I\<^sub>+) ?prefix' 
    = SAS_Plus_Plus_State_To_SAS_Plus (Init, I)" using I_def
    apply(auto simp: SAS_Plus_Plus_To_SAS_Plus_def SAS_Plus_Plus_State_To_SAS_Plus_def map_le_def
        initial_state_def map_add_def map_comp_def fun_eq_iff split: option.splits variable.splits)
    by (metis domI option.inject)
  hence "execute_serial_plan_sas_plus ((?P')\<^sub>I\<^sub>+) 
    (?prefix @ (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator plan)) 
    = SAS_Plus_Plus_State_To_SAS_Plus (NonInit, execute_serial_plan_sas_plus I plan)" by auto
  hence "((?P')\<^sub>G\<^sub>+) \<subseteq>\<^sub>m execute_serial_plan_sas_plus ((?P')\<^sub>I\<^sub>+) 
    (?prefix @ (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator plan))" using I_def 
    apply(auto simp:  SAS_Plus_Plus_To_SAS_Plus_def SAS_Plus_Plus_State_To_SAS_Plus_def 
        map_add_def map_comp_def split: option.splits variable.splits)
    apply(simp add: map_le_def fun_eq_iff)
    by (metis (no_types, lifting) domIff option.case_eq_if)
  hence "length ?prefix \<le> length ((P)\<^sub>\<V>\<^sub>+) + 1 
    \<and> is_serial_solution_for_problem (SAS_Plus_Plus_To_SAS_Plus P) 
        (?prefix @ (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator plan))"
    using I_def
    by(auto simp: is_serial_solution_for_problem_def Let_def in_initialization_operators_iff
        initialization_sequence_def ListMem_iff SAS_Plus_Plus_To_SAS_Plus_def range_of'_def 
        list_all_def split: option.splits)
  thus ?thesis by blast
qed

lemma map_of_map_Stage[simp]: 
  "map_of (map (\<lambda>x. (Var (fst x), DE (snd x))) l) Stage = None"
  apply(induction l) 
  by(auto)

lemma chain_applicable_in_Stage_NonInit:
  "s Stage = Some NonInit \<Longrightarrow> chain_applicable s plan 
  \<Longrightarrow> \<forall>op \<in> set plan. op \<in> set ((SAS_Plus_Plus_To_SAS_Plus P)\<^sub>\<O>\<^sub>+)
  \<Longrightarrow> \<forall>op \<in> set plan. op \<in> set (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator ((P)\<^sub>\<O>\<^sub>+))"
proof(induction plan arbitrary: s)
  case Nil
  then show ?case by auto
next
  case (Cons a plan)
  hence "a \<in> set (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator ((P)\<^sub>\<O>\<^sub>+))"
    "(s \<then>\<^sub>+ a) Stage = Some NonInit"
    using Cons
    by (auto simp: SAS_Plus_Plus_To_SAS_Plus_def map_le_def map_add_def option.case_eq_if
        SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_def initialization_operators_def)
  thus ?case using Cons by auto
qed

lemma in_set_take_then: "op \<in> set (take k (a # as)) \<Longrightarrow> (op = a \<or> op \<in> set (take (k - 1) as))"
  by (metis empty_iff empty_set set_ConsD take_Cons') 
  
lemma SAS_plus_plan_structure:
  assumes "s Stage = Some Init"
    "chain_applicable s plan"
    "execute_serial_plan_sas_plus s plan Stage = Some NonInit"
    "list_all (\<lambda>op. ListMem op ((SAS_Plus_Plus_To_SAS_Plus P)\<^sub>\<O>\<^sub>+) ) plan"
  shows "\<exists>k. k < length plan 
    \<and> list_all (\<lambda>op. op \<in> set (initialization_operators P)) (take k plan)
    \<and> plan ! k = \<lparr> precondition_of = [(Stage, Init)], effect_of = [(Stage, NonInit)]\<rparr>
    \<and> list_all (\<lambda>op. op \<in> set (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator ((P)\<^sub>\<O>\<^sub>+))) 
      (drop (k + 1) plan)"
using assms proof(induction plan arbitrary: s)
  case (Cons a plan)
  hence "a \<in> set (initialization_operators P) 
    \<or> a = \<lparr> precondition_of = [(Stage, Init)], effect_of = [(Stage, NonInit)]\<rparr>
    \<or> a \<in> set (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator ((P)\<^sub>\<O>\<^sub>+))" 
    by (auto simp: SAS_Plus_Plus_To_SAS_Plus_def ListMem_iff)
  thus ?case
  using Cons proof(elim disjE)
    assume *: "a \<in> set (initialization_operators P)"
    hence "(s ++ map_of (effect_of a)) Stage = Some Init" using Cons by simp
    then obtain k where "k < length plan 
      \<and> list_all (\<lambda>op. op \<in> set (initialization_operators P)) (take k plan)
      \<and> plan ! k = \<lparr> precondition_of = [(Stage, Init)], effect_of = [(Stage, NonInit)]\<rparr>
      \<and> list_all (\<lambda>op. op \<in> set (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator ((P)\<^sub>\<O>\<^sub>+))) 
      (drop (k + 1) plan)" using Cons apply(simp) by presburger
    thus ?thesis using Cons * by auto
  next
    assume *: "a = \<lparr> precondition_of = [(Stage, Init)], effect_of = [(Stage, NonInit)]\<rparr>" 
    hence "\<forall>op \<in> set plan. op \<in> set (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator ((P)\<^sub>\<O>\<^sub>+))" 
      apply -
      apply(rule chain_applicable_in_Stage_NonInit[where ?s = "s ++ map_of(effect_of a)"]) 
      using Cons by (auto simp: list_all_def ListMem_iff)
    thus ?thesis using * by (auto simp: list_all_def)
  qed (auto simp: SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_def list_all_def map_le_def)
qed auto

lemma result_of_initialization_operator:
  "is_valid_problem_sas_plus_plus P
    \<Longrightarrow> op \<in> set (initialization_operators P)
    \<Longrightarrow> ((P)\<^sub>I\<^sub>+) \<subseteq>\<^sub>m I
    \<Longrightarrow> (\<forall>v \<in> dom I. the (I v) \<in> \<R>\<^sub>+ P v)
    \<Longrightarrow> (\<exists>I'. (SAS_Plus_Plus_State_To_SAS_Plus (Init, I)) ++ map_of(effect_of op) 
        = SAS_Plus_Plus_State_To_SAS_Plus (Init, I')
      \<and> ((P)\<^sub>I\<^sub>+) \<subseteq>\<^sub>m I' \<and> (\<forall>v \<in> dom I'. the (I' v) \<in> \<R>\<^sub>+ P v))"
  apply(auto simp: initialization_operators_def map_le_def range_of'_def dom_def ListMem_iff
       is_valid_problem_sas_plus_plus_def Let_def list_all_def split: if_splits option.splits)
   apply (meson domI domIff)
  by (metis option.sel option.simps)


lemma result_of_initialization_operators:
  "is_valid_problem_sas_plus_plus P 
    \<Longrightarrow> list_all (\<lambda>op. op \<in> set (initialization_operators P)) ops
    \<Longrightarrow> ((P)\<^sub>I\<^sub>+) \<subseteq>\<^sub>m I 
    \<Longrightarrow> (\<forall>v \<in> dom I. the (I v) \<in> \<R>\<^sub>+ P v)
    \<Longrightarrow> (\<exists>I'. execute_serial_plan_sas_plus (SAS_Plus_Plus_State_To_SAS_Plus (Init, I)) ops 
        = SAS_Plus_Plus_State_To_SAS_Plus (Init, I')
      \<and> ((P)\<^sub>I\<^sub>+) \<subseteq>\<^sub>m I' \<and> (\<forall>v \<in> dom I'. the (I' v) \<in> \<R>\<^sub>+ P v))"
proof(induction ops arbitrary: I)
  case (Cons op ops)
  thus ?case using result_of_initialization_operator[OF Cons(2)] by force
qed auto

lemma list_all_in_map_set_then: 
  "\<forall>a\<in>set as. a \<in> f ` S  \<Longrightarrow> (\<exists>bs. as = map f bs \<and> (\<forall>b \<in> set bs. b \<in> S))" 
  apply(induction as)
   apply(auto)
  by (metis list.simps set_ConsD)

lemma result_of_initialization_operators_on_initial_state:
  "is_valid_problem_sas_plus_plus P
    \<Longrightarrow> list_all (\<lambda>op. op \<in> set (initialization_operators P)) ops
    \<Longrightarrow> (\<exists>I'. execute_serial_plan_sas_plus ((SAS_Plus_Plus_To_SAS_Plus P)\<^sub>I\<^sub>+) ops 
        = SAS_Plus_Plus_State_To_SAS_Plus (Init, I')
      \<and> ((P)\<^sub>I\<^sub>+) \<subseteq>\<^sub>m I' \<and> (\<forall>v \<in> dom I'. the (I' v) \<in> \<R>\<^sub>+ P v))"
  apply(simp add: SAS_Plus_Plus_To_SAS_Plus_def initial_state_def)
  apply(rule result_of_initialization_operators)
  apply(auto simp: list_all_def map_le_def is_valid_problem_sas_plus_plus_def Let_def ListMem_iff 
      range_of'_def split: option.splits)
  by auto

lemma length_of_mapped: "l' = map f l \<Longrightarrow> length l' \<le> x \<Longrightarrow> length l \<le> x" by simp

lemma SAS_Plus_To_SAS_Plus_Plus:
  assumes "is_valid_problem_sas_plus_plus P" 
    "is_serial_solution_for_problem (SAS_Plus_Plus_To_SAS_Plus P) plan"
  shows "\<exists>plan'. length plan' \<le> length plan
    \<and> is_serial_solution_for_problem_sas_plus_plus P plan'"
proof-
  let ?plan = "chain_applicable_prefix ((SAS_Plus_Plus_To_SAS_Plus P)\<^sub>I\<^sub>+) plan" 
  obtain k where k_def: "k < length ?plan 
    \<and> list_all (\<lambda>op. op \<in> set (initialization_operators P)) (take k ?plan)
    \<and> ?plan ! k = \<lparr> precondition_of = [(Stage, Init)], effect_of = [(Stage, NonInit)]\<rparr>
    \<and> list_all (\<lambda>op. op \<in> set (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator ((P)\<^sub>\<O>\<^sub>+))) 
      (drop (k + 1) ?plan)"
    using exE[OF SAS_plus_plan_structure[where ?s ="((SAS_Plus_Plus_To_SAS_Plus P)\<^sub>I\<^sub>+)" 
            and ?P = P and ?plan = ?plan]] assms set_of_chain_applicable_prefix 
    by(force simp: is_serial_solution_for_problem_def list_all_def map_le_def Let_def 
        execute_chain_applicable_prefix SAS_Plus_Plus_To_SAS_Plus_def initial_state_def ListMem_iff 
        SAS_Plus_Plus_State_To_SAS_Plus_def)+

  let ?prefix = "take k ?plan" 
  obtain I' where I'_def: "execute_serial_plan_sas_plus ((SAS_Plus_Plus_To_SAS_Plus P)\<^sub>I\<^sub>+) ?prefix 
        = SAS_Plus_Plus_State_To_SAS_Plus (Init, I')
      \<and> ((P)\<^sub>I\<^sub>+) \<subseteq>\<^sub>m I' \<and> (\<forall>v \<in> dom I'. the (I' v) \<in> \<R>\<^sub>+ P v)" 
    using result_of_initialization_operators_on_initial_state assms k_def by blast
  moreover have  "dom (execute_serial_plan_sas_plus ((SAS_Plus_Plus_To_SAS_Plus P)\<^sub>I\<^sub>+) ?prefix) 
    = set ((SAS_Plus_Plus_To_SAS_Plus P)\<^sub>\<V>\<^sub>+)" 
    apply(rule dom_of_execute_serial_plan_sas_plus)
    using SAS_Plus_Plus_To_SAS_Plus_valid assms k_def 
    by(auto simp: list_all_def SAS_Plus_Plus_To_SAS_Plus_def initial_state_def 
        SAS_Plus_Plus_State_To_SAS_Plus_def map_comp_def split: option.splits variable.splits)
  ultimately have dom_of_I': "dom I' = set ((P)\<^sub>\<V>\<^sub>+)" 
    by (auto simp: dom_of_SAS_Plus_Plus_State_To_SAS_Plus SAS_Plus_Plus_To_SAS_Plus_def)

  have "\<exists>plan'. drop (k + 1) ?plan = map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator plan'
    \<and> (\<forall>op \<in> set plan'. op \<in> set ((P)\<^sub>\<O>\<^sub>+))" 
    using k_def list_all_in_map_set_then by(auto simp: list_all_def)
  then obtain plan' where plan'_def: "map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator plan'
    = drop (k + 1) ?plan  \<and> (\<forall>op \<in> set plan'. op \<in> set ((P)\<^sub>\<O>\<^sub>+))" by fastforce

  have "?plan = ((take k ?plan) 
    @ [\<lparr> precondition_of = [(Stage, Init)], effect_of = [(Stage, NonInit)]\<rparr>]
    @ (drop (k + 1) ?plan))" using k_def
    by (metis One_nat_def add.right_neutral add_Suc_right append.assoc append_take_drop_id 
        hd_drop_conv_nth take_hd_drop)
  hence "execute_serial_plan_sas_plus ((SAS_Plus_Plus_To_SAS_Plus P)\<^sub>I\<^sub>+) ?plan 
    = execute_serial_plan_sas_plus (SAS_Plus_Plus_State_To_SAS_Plus (Init, I'))
        ([\<lparr> precondition_of = [(Stage, Init)], effect_of = [(Stage, NonInit)]\<rparr>]
        @ (drop (k + 1) ?plan))" using I'_def
    by (metis chain_applicable_append chain_applicable_prefix_chain_applicable 
        execute_serial_plan_sas_plus_append)
  also have "... = SAS_Plus_Plus_State_To_SAS_Plus (NonInit, execute_serial_plan_sas_plus I' plan')"
    using plan'_def by auto (metis execute_SAS_Plus_Plus_ops_in_SAS_Plus)
  ultimately have "(P)\<^sub>G\<^sub>+ \<subseteq>\<^sub>m execute_serial_plan_sas_plus I' plan'"
    using assms(2) plan'_def 
    by(auto simp: execute_chain_applicable_prefix is_serial_solution_for_problem_def 
        SAS_Plus_Plus_To_SAS_Plus_def)
  hence "(P)\<^sub>I\<^sub>+ \<subseteq>\<^sub>m I' \<and> dom I' = set ((P)\<^sub>\<V>\<^sub>+)
        \<and> (\<forall> v \<in> set ((P)\<^sub>\<V>\<^sub>+). the (I' v) \<in> range_of' P v)
        \<and> (P)\<^sub>G\<^sub>+ \<subseteq>\<^sub>m execute_serial_plan_sas_plus I' plan' 
        \<and> list_all (\<lambda>op. ListMem op ((P)\<^sub>\<O>\<^sub>+)) plan'"
    using plan'_def I'_def dom_of_I' by (auto simp: list_all_def ListMem_iff)
  hence "length plan' \<le> length plan
    \<and> is_serial_solution_for_problem_sas_plus_plus P plan'" using plan'_def
    apply (auto simp: is_serial_solution_for_problem_sas_plus_plus_def)
    using length_of_mapped length_of_chain_applicable_prefix le_add1 le_diff_conv le_trans 
    by (metis (mono_tags, lifting) length_drop)
  thus ?thesis by blast
qed

end