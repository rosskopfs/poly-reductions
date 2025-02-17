\<^marker>\<open>creator Florian Keßler\<close>

section "IMP- to SAS++ Reduction"

theory IMP_Minus_To_SAS_Plus_Plus_Reduction                             
  imports IMP_Minus_To_SAS_Plus_Plus_State_Translations IMP_Minus_Subprograms
begin

text \<open> We define a reduction from IMP- to SAS++. The reduction is pretty straightforward, 
      simulating a single step in IMP- with a single operation in SAS++ in the obvious way,
      given the translation of states from IMP- to SAS++ defined earlier. \<close>

definition domain :: "domain_element list" where
"domain = [EV Zero, EV One]"

declare domain_def[simp]

type_synonym operator = "(variable, domain_element) sas_plus_operator"
type_synonym problem = "(variable, domain_element) sas_plus_problem"

definition pc_to_com :: "(variable \<times> domain_element) list \<Rightarrow> com" where
"pc_to_com l = (if l = [] then SKIP else (case  l ! 0 of (_, PCV x) \<Rightarrow> x | t \<Rightarrow> SKIP))"

lemma pc_to_com_def2 :"l \<noteq> [] \<Longrightarrow> pc_to_com l = (case  l ! 0 of (_, PCV x) \<Rightarrow> x | t \<Rightarrow> SKIP)"
  apply (auto simp add: pc_to_com_def)
  done

fun com_to_operators :: "com \<Rightarrow> operator list" where
"com_to_operators (SKIP) = []" |
"com_to_operators (v ::= b) = 
   [\<lparr> precondition_of = [(PC, PCV (v ::= b))], 
      effect_of = [(PC, PCV SKIP), (VN v, EV b)]\<rparr>]" |
"com_to_operators (c1;; c2) = 
  (if c1 = SKIP then  [\<lparr> precondition_of = [(PC, PCV (c1 ;; c2))],
                                                   effect_of = [(PC, PCV c2)]\<rparr>]
   else (let ops = com_to_operators c1 in map (\<lambda> op. 
    (let c1' = pc_to_com (effect_of op) in 
      \<lparr> precondition_of = 
        list_update (precondition_of op) 0 (PC, PCV (c1 ;; c2)),
        effect_of = 
        list_update (effect_of op) 0 (PC, PCV (c1' ;; c2))\<rparr>)) ops))" |
"com_to_operators (IF vs\<noteq>0 THEN c1 ELSE c2) = (let i = PCV (IF vs\<noteq>0 THEN c1 ELSE c2)
   in  \<lparr> precondition_of = (PC, i) # map (\<lambda>v. (VN v, EV Zero)) (remdups vs), 
        effect_of = [(PC, PCV c2)]\<rparr> 
      # map (\<lambda> v. 
      \<lparr> precondition_of = [(PC, i), (VN v, EV One)], 
         effect_of = [(PC, PCV c1)]\<rparr>) vs)" |
"com_to_operators (WHILE vs\<noteq>0 DO c) = (let i = PCV (WHILE vs\<noteq>0 DO c) ;
  j = PCV (c ;; (WHILE vs\<noteq>0 DO c)); k = PCV SKIP in 
    \<lparr> precondition_of = (PC, i) # map (\<lambda>v. (VN v, EV Zero)) (remdups vs), 
        effect_of = [(PC, k)]\<rparr> 
      # map (\<lambda> v. 
      \<lparr> precondition_of = [(PC, i), (VN v, EV One)], 
         effect_of = [(PC, j)]\<rparr>) vs)"

lemma precondition_nonempty[simp]: "op \<in> set (com_to_operators c) 
  \<Longrightarrow> length (precondition_of op) > 0"
  by (induction c arbitrary: op rule: com_to_operators.induct)
    (auto simp: Let_def split: if_splits)

lemma effect_nonempty[simp]: "op \<in> set (com_to_operators c) 
  \<Longrightarrow> length (effect_of op) > 0"
  by (induction c arbitrary: op rule: com_to_operators.induct)
    (auto simp: Let_def split: if_splits)

lemma PC_in_effect_precondition: "op \<in> set (com_to_operators c) 
  \<Longrightarrow> (\<exists>y1 y2. (PC, PCV y1) = (precondition_of op) ! 0 \<and> (PC, PCV y2) = (effect_of op) ! 0)"
proof(induction c arbitrary: op rule: com_to_operators.induct)
  case (2 v aexp d)
  then show ?case by (cases aexp) (auto simp: Let_def)
next
  case (3 c1 c2 d)
  have "c1 = SKIP \<or> c1 \<noteq> SKIP" by simp
  then show ?case using 3 precondition_nonempty effect_nonempty by (auto split: if_splits)
qed(auto simp: Let_def)

lemma fst_of_effect[simp]: "op \<in> set (com_to_operators c) 
  \<Longrightarrow> fst (effect_of op ! 0) = PC" 
  using PC_in_effect_precondition by (metis fst_conv)

lemma fst_of_precondition[simp]: "op \<in> set (com_to_operators c) 
  \<Longrightarrow> fst (precondition_of op ! 0) = PC" 
  using PC_in_effect_precondition by (metis fst_conv)

lemma com_to_operators_seq_registers:
  assumes "c1 \<noteq> SKIP" and  "op \<in> set (com_to_operators (c1 ;; c2))" 
    and "(VN x, y) \<in> set (precondition_of op) \<or> (VN x, y) \<in> set (effect_of op)"
  shows "\<exists>op'. op' \<in> set (com_to_operators c1) 
          \<and> ((VN x, y) \<in> set (precondition_of op') \<or> (VN x, y) \<in> set (effect_of op'))"
proof -
  obtain op' where "op' \<in> set (com_to_operators c1) 
    \<and> op = (let c1' = pc_to_com (effect_of op') in 
      \<lparr> precondition_of = 
        list_update (precondition_of op') 0 (PC, PCV (c1 ;; c2)),
        effect_of = 
        list_update (effect_of op') 0 (PC, PCV (c1' ;; c2))\<rparr>)" using assms by auto
  moreover then have "(VN x, y) \<in> set (precondition_of op') \<or> (VN x, y) \<in> set (effect_of op')" 
    using assms PC_in_effect_precondition precondition_nonempty effect_nonempty 
    by (metis (no_types, lifting) eq_fst_iff in_set_conv_nth length_list_update nth_list_update 
        sas_plus_operator.select_convs sas_plus_operator.select_convs variable.simps)
  ultimately show ?thesis by auto
qed

lemma com_to_operators_registers_in_d: 
  "op \<in> set (com_to_operators c) 
  \<Longrightarrow> ((VN x, y) \<in> set (precondition_of op) \<or> (VN x, y) \<in> set (effect_of op))  
  \<Longrightarrow> (y = EV Zero \<or> y = EV One)"
proof (induction c arbitrary: op rule: com_to_operators.induct)
  case (3 c1 c2 d)
  have "c1 = SKIP \<or> c1 \<noteq> SKIP" by simp
  then show ?case
  proof (elim disjE)
    assume "c1 \<noteq> SKIP"
    then show ?thesis using 3 com_to_operators_seq_registers by blast
  next
    assume "c1 = SKIP" 
    then show ?thesis using 3 by auto
  qed
qed (auto simp: Let_def split: if_splits domain_element.splits)

lemma update_preserve_distinct: "distinct (map fst l) \<Longrightarrow> fst (l ! 0) = x 
  \<Longrightarrow> distinct (map fst (l[0 := (x, y)]))"
  by (induction l) auto

lemma map_fst_pair[simp]: "map (fst \<circ> (\<lambda>v. (VN v, EV Zero))) vs = map VN vs"
  by (induction vs) auto

lemma distinct_map_VN[simp]: "distinct (map VN vs) = distinct vs" 
  by (induction vs) auto

lemma com_to_operators_variables_distinct: 
  "op \<in> set (com_to_operators c) \<Longrightarrow> (l = precondition_of op \<or> l = effect_of op)
  \<Longrightarrow> distinct (map fst l)"
by (induction c  arbitrary: op l rule: com_to_operators.induct)
 (auto simp: Let_def update_preserve_distinct split: if_splits)

lemma PC_of_precondition[simp]: "op \<in> set (com_to_operators c) 
  \<Longrightarrow> (PC, y) \<in> set (precondition_of op) \<longleftrightarrow> y = PCV c"
  using com_to_operators_variables_distinct PC_in_effect_precondition
  apply(cases c)
      apply(auto simp: pc_to_com_def Let_def split:  if_splits)
  by(metis eq_key_imp_eq_value fst_of_precondition precondition_nonempty 
      set_update_memI update_preserve_distinct)+

lemma map_of_precondition_of_op_PC[simp]: "op \<in> set (com_to_operators c) 
  \<Longrightarrow> (map_of (precondition_of op)) PC = Some (PCV c)"
  using PC_of_precondition com_to_operators_variables_distinct by auto

lemma pc_to_com_precondition_of_op_PC [simp]: "op \<in> set (com_to_operators c) 
  \<Longrightarrow> pc_to_com (precondition_of op) = c"
  using PC_of_precondition  pc_to_com_def2
  by (metis PC_in_effect_precondition domain_element.simps(6) 
        length_greater_0_conv nth_mem old.prod.case precondition_nonempty)
  

lemma pc_to_com_effect[simp]: "op \<in> set (com_to_operators c) 
  \<Longrightarrow> (PC, y) \<in> set (effect_of op) \<longleftrightarrow> y = PCV (pc_to_com (effect_of op))"
  using com_to_operators_variables_distinct PC_in_effect_precondition 
  pc_to_com_def2
  by (metis domain_element.simps(6) effect_nonempty eq_key_imp_eq_value length_greater_0_conv
 nth_mem old.prod.case)
  
lemma PC_of_effect[simp]: "op \<in> set (com_to_operators c) 
  \<Longrightarrow> map_of (effect_of op) PC = Some (PCV (pc_to_com (effect_of op)))"
  using com_to_operators_variables_distinct PC_in_effect_precondition 
  by (auto simp: pc_to_com_def)

lemma com_to_operators_PC_is_subprogram: 
  "op \<in> set (com_to_operators c)
  \<Longrightarrow>  (pc_to_com (precondition_of op) \<in> set (enumerate_subprograms c)
      \<and> pc_to_com (effect_of op) \<in> set (enumerate_subprograms c))"
  apply (induction c arbitrary: op rule: com_to_operators.induct)
  using c_in_all_subprograms_c precondition_nonempty effect_nonempty
      by (auto simp: Let_def pc_to_com_def split: if_splits )

lemma com_to_operators_variables_in_enumerate_variables: "op \<in> set (com_to_operators c)
  \<Longrightarrow> ((VN x, y) \<in> set (precondition_of op) \<or> (VN x, y) \<in> set (effect_of op))
  \<Longrightarrow> x \<in> set (enumerate_variables c)"
proof (induction c arbitrary: op rule: com_to_operators.induct)
  case (3 c1 c2 d)
  have "c1 = SKIP \<or> c1 \<noteq> SKIP" by auto
  then show ?case
  proof (elim disjE)
    assume "c1 = SKIP"
    then show ?thesis using 3 by auto
  next
    assume "c1 \<noteq> SKIP"
    moreover then obtain op' where "op' \<in> set (com_to_operators c1) 
          \<and> ((VN x, y) \<in> set (precondition_of op') \<or> (VN x, y) \<in> set (effect_of op'))"
      using 3 com_to_operators_seq_registers by metis
    moreover have "c1 \<in> set (enumerate_subprograms (c1 ;; c2))" using c_in_all_subprograms_c by auto
    moreover then have "set (enumerate_variables c1) \<subseteq> set (enumerate_variables (c1 ;; c2))"
      using enumerate_subprograms_enumerate_variables
      by simp
    ultimately show ?thesis using 3 by auto
  qed
qed (auto simp: Let_def split: if_splits)

lemma VN_PCV_not_in_effect[simp]: 
  "op \<in> set (com_to_operators c1) \<Longrightarrow> (VN v, PCV c') \<notin> set (effect_of op)"
  apply(induction c1 arbitrary: op)
      apply(auto simp: Let_def split: if_splits)
  by (metis (no_types, lifting) in_set_conv_nth length_list_update nth_list_update 
      nth_list_update_neq prod.inject variable.distinct(1))

lemma in_set_effect: "op \<in> set (com_to_operators c1) 
  \<Longrightarrow> (VN v, y) \<in> set (effect_of op)
  \<Longrightarrow> \<exists>y'. y = EV y'"
  apply(induction c1 arbitrary: op)
      apply(auto simp: Let_def split: if_splits)
  by (metis in_set_conv_nth length_list_update nth_list_update nth_list_update_neq 
      prod.inject variable.distinct)

lemma in_set_precondition: "op \<in> set (com_to_operators c1) 
  \<Longrightarrow> (VN v, y) \<in> set (precondition_of op)
  \<Longrightarrow> \<exists>y'. y = EV y'"
  apply(induction c1 arbitrary: op)
      apply(auto simp: domain_def Let_def split: if_splits)
  by (metis in_set_conv_nth length_list_update nth_list_update nth_list_update_neq 
      prod.inject variable.distinct)

lemma map_of_precondition_eq_Some[simp]: 
  assumes "op \<in> set (com_to_operators c1)"
   "map_of (precondition_of op) (VN v) = Some y"
 shows "\<exists>y'. y = EV y'"
proof -
  have "(VN v, y) \<in> set (precondition_of op)" using assms by (auto simp: map_of_SomeD)
  then show ?thesis using assms in_set_precondition by simp
qed

lemma not_in_set_then_map_of_eq_None:
  "\<forall>y. (x, y) \<notin> set m \<Longrightarrow> (map_of m) x = None"
  apply(induction m)
  by auto

lemma variables_in_effect[simp]: 
  assumes "op \<in> set (com_to_operators c1)"
  shows "\<exists>x. (VN v, EV x) \<in> set (effect_of op) \<or> map_of (effect_of op) (VN v) = None"
proof -
  have "(\<exists>y. (VN v, y) \<in> set (effect_of op)) \<or> \<not>((\<exists>y. (VN v, y) \<in> set (effect_of op)))" by auto
  then show ?thesis
    apply(elim disjE)
    using assms in_set_effect apply blast using not_in_set_then_map_of_eq_None by simp
qed
  
lemma in_precondition_not_VN_then_PC[simp]: 
  assumes "op \<in> set (com_to_operators c1)"
    "(a, b) \<in> set (precondition_of op)"
    "c1 \<in> set (enumerate_subprograms c)"
    "a \<notin> VN ` set (enumerate_variables c)" 
  shows "a = PC"
proof (cases a)
  case (VN v)
  have "set (enumerate_variables c1) \<subseteq> set (enumerate_variables c)" 
    using assms enumerate_subprograms_enumerate_variables by auto
  then show ?thesis using VN com_to_operators_variables_in_enumerate_variables assms by blast
qed auto

lemma in_effect_not_VN_then_PC[simp]: 
  assumes "op \<in> set (com_to_operators c1)"
    "(a, b) \<in> set (effect_of op)"
    "c1 \<in> set (enumerate_subprograms c)"
    "a \<notin> VN ` set (enumerate_variables c)" 
  shows "a = PC"
proof (cases a)
  case (VN v)
  have "set (enumerate_variables c1) \<subseteq> set (enumerate_variables c)" 
    using assms enumerate_subprograms_enumerate_variables by auto
  then show ?thesis using VN com_to_operators_variables_in_enumerate_variables assms by blast
qed auto

definition coms_to_operators :: "com list \<Rightarrow> operator list" where
"coms_to_operators cs = concat (map com_to_operators cs)"

definition imp_minus_minus_to_sas_plus :: 
"com \<Rightarrow> imp_state \<Rightarrow> imp_state \<Rightarrow> problem" where
"imp_minus_minus_to_sas_plus c I G = (let cs = enumerate_subprograms c ; 
  initial_vs = I|`(set (enumerate_variables c)) ;
  goal_vs = G|`(set (enumerate_variables c)) ;
  pc_d = map (\<lambda> i. PCV i) cs in
    \<lparr> variables_of = PC # (map VN (enumerate_variables c)),
      operators_of = coms_to_operators cs, 
      initial_of = imp_minus_state_to_sas_plus (c, initial_vs),
      goal_of = imp_minus_state_to_sas_plus (SKIP, goal_vs),
      range_of = (map_of (map (\<lambda> v. (VN v, domain)) (enumerate_variables c)))(PC \<mapsto> pc_d)\<rparr>)"

lemma range_defined: 
  assumes "v \<in> set (variables_of (imp_minus_minus_to_sas_plus c I G))" 
  shows "(\<exists>y. range_of (imp_minus_minus_to_sas_plus c I G) v = Some y)"
proof(cases v)
  case (VN x)
  then have "(VN x, domain) \<in> set (map (\<lambda> v. (VN v, domain)) (enumerate_variables c))" 
    using assms by (auto simp: Let_def imp_minus_minus_to_sas_plus_def)    
  then show ?thesis using VN by (auto simp: Let_def imp_minus_minus_to_sas_plus_def weak_map_of_SomeI) 
qed (auto simp: imp_minus_minus_to_sas_plus_def Let_def)

lemma range_non_empty: 
  assumes "v \<in> set (variables_of (imp_minus_minus_to_sas_plus c I G))" 
  shows "(\<exists>y. y \<in> range_of' (imp_minus_minus_to_sas_plus c I G) v)"
proof (cases v)
  case (VN x)
  then have *: "(VN x, domain) \<in> set (map (\<lambda> v. (VN v, domain)) (enumerate_variables c))" 
    using assms by (auto simp: Let_def imp_minus_minus_to_sas_plus_def)
  then have "range_of (imp_minus_minus_to_sas_plus c I G) v = Some domain" 
    using VN
    apply - apply(frule weak_map_of_SomeI)
    apply (simp add: Let_def imp_minus_minus_to_sas_plus_def)
    using map_of_SomeD by force 
  thus ?thesis by(auto simp: range_of'_def)
next
  case PC
  then show ?thesis using SKIP_in_enumerate_subprograms
    by (auto simp:  range_of'_def Let_def imp_minus_minus_to_sas_plus_def) 
      (metis empty_iff empty_set) 
qed

lemma [simp]: "x \<in> set l \<Longrightarrow> (map_of (map (\<lambda>v. (VN v, d)) l) (VN x)) = Some d"
  by (induction l) auto

lemma distinct_list_all: 
  assumes "distinct (map fst l)" 
  shows "list_all (\<lambda>(v, a). list_all (\<lambda>(v', a'). v \<noteq> v' \<or> a = a') l) l"
proof -
  have "(v1, a1) \<in> set l \<Longrightarrow> list_all (\<lambda>(v', a'). v1 \<noteq> v' \<or> a1 = a') l" for v1 a1
  proof -
    assume "(v1, a1) \<in> set l"
    then have "(v2, a2) \<in> set l \<Longrightarrow> v1 \<noteq> v2 \<or> a1 = a2" for v2 a2 
      using assms by (meson eq_key_imp_eq_value)
    then show ?thesis using Ball_set_list_all by blast
  qed
  then show ?thesis
    by (metis (no_types, lifting) case_prodI2 list.pred_set)
qed 

lemma operators_valid: 
  assumes "cs = enumerate_subprograms c" and "c1 \<in> set cs"
         and  "op \<in> set (com_to_operators c1)"
  shows "is_valid_operator_sas_plus (imp_minus_minus_to_sas_plus c I G) op" 
proof -                   
  let ?\<Psi> = "imp_minus_minus_to_sas_plus c I G"
  let ?pre = "precondition_of op" and ?eff = "effect_of op" and ?vs = "variables_of ?\<Psi>" 
      and ?D = "range_of ?\<Psi>" and ?pc_d = "map (\<lambda> i. PCV i) (enumerate_subprograms c)"

  have *: "list_all (\<lambda>(v, a). ListMem v ?vs) ?pre \<and> list_all (\<lambda>(v, a). ListMem v ?vs) ?eff"
    using assms by(auto simp: imp_minus_minus_to_sas_plus_def Let_def ListMem_iff list_all_def)

  have "((VN x, a) \<in> set ?pre \<or> (VN x, a) \<in> set ?eff) \<Longrightarrow> ?D (VN x) = Some domain 
    \<and> a \<in> set domain" for x a
    using assms com_to_operators_registers_in_d com_to_operators_variables_in_enumerate_variables
        enumerate_subprograms_enumerate_variables 
    by (fastforce simp: imp_minus_minus_to_sas_plus_def Let_def)    
  then have "((v, a) \<in> set ?pre \<or> (v, a) \<in> set ?eff) \<Longrightarrow> (?D v \<noteq> None \<and> ListMem a (the (?D v)))" for v a
    using com_to_operators_PC_is_subprogram assms enumerate_subprograms_transitive
    by (cases v) 
      (auto simp: imp_minus_minus_to_sas_plus_def Let_def ListMem_iff Ball_set_list_all)
  then have "list_all (\<lambda>(v, a). (?D v \<noteq> None) \<and> ListMem a (the (?D v))) ?pre" 
    and "list_all (\<lambda>(v, a). (?D v \<noteq> None) \<and> ListMem a (the (?D v))) ?eff" 
    using Ball_set_list_all by blast+

  then show ?thesis 
    using com_to_operators_variables_distinct assms distinct_list_all *
    by (fastforce simp: is_valid_operator_sas_plus_def Let_def) 
qed

lemma restricted_map_eq_Some_iff[simp]: "((f |` S) x = Some y) \<longleftrightarrow> (f x = Some y \<and> x \<in> S)" 
  by(auto simp: restrict_map_def)

lemma not_in_enumerate_variables_not_PC_then[simp]:
  "\<forall>x \<in> set (enumerate_variables c). v \<noteq> VN x \<Longrightarrow> v \<noteq> PC 
    \<Longrightarrow> (\<exists>x. x \<notin> set (enumerate_variables c) \<and> v = VN x)"
  apply(cases v) by auto

lemma imp_minus_minus_to_sas_plus_valid:
  "is_valid_problem_sas_plus_plus (imp_minus_minus_to_sas_plus c I G)"
proof -
  let ?\<Psi> = "imp_minus_minus_to_sas_plus c I G"
  let ?ops = "operators_of ?\<Psi>"
      and ?vs = "variables_of ?\<Psi>"
      and ?I = "initial_of ?\<Psi>"
      and ?G = "goal_of ?\<Psi>"
      and ?D = "range_of ?\<Psi>"
  have "\<forall>x \<in> set ?ops. is_valid_operator_sas_plus ?\<Psi> x" 
    and "\<forall>v \<in> set ?vs. length (the (?D v)) > 0"
    using operators_valid c_in_all_subprograms_c[where ?c = c] 
    by (auto simp: imp_minus_minus_to_sas_plus_def Let_def coms_to_operators_def)
  moreover have  "?I v \<noteq> None \<longrightarrow> ListMem v ?vs"
    and "?G v \<noteq> None \<longrightarrow> ListMem v ?vs"
    and "?I v \<noteq> None \<longrightarrow> ListMem (the (?I v)) (the (?D v))"
    and "?G v \<noteq> None \<longrightarrow> ListMem (the (?G v)) (the (?D v))" for v
       apply(cases v)
       using c_in_all_subprograms_c[where ?c = c] SKIP_in_enumerate_subprograms
       by (auto simp: imp_minus_minus_to_sas_plus_def Let_def coms_to_operators_def 
        imp_minus_state_to_sas_plus_def map_comp_def ListMem_iff image_def 
        split: variable.splits option.splits)
    ultimately show ?thesis
    by (auto simp: is_valid_problem_sas_plus_plus_def range_defined list_all_def)
qed

end