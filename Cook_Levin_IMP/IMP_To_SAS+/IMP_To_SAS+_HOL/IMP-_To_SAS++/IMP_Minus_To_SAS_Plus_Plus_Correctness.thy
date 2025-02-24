\<^marker>\<open>creator Florian Keßler\<close>

section "IMP- to SAS++ Correctness"

theory IMP_Minus_To_SAS_Plus_Plus_Correctness 
  imports IMP_Minus_To_SAS_Plus_Plus_Reduction SAS_Plus_Plus
begin 

text \<open> We show correctness for the IMP- to SAS++ reduction. \<close>

lemma sas_plus_state_to_imp_minus_of_effect: 
  assumes "op \<in> set (com_to_operators c1)"
  shows "sas_plus_state_to_imp_minus (imp_minus_state_to_sas_plus (c, is) ++ map_of (effect_of op)) 
  = (pc_to_com (effect_of op), 
  snd (sas_plus_state_to_imp_minus (imp_minus_state_to_sas_plus (c, is) ++ map_of (effect_of op))))"
proof -
  have "fst (sas_plus_state_to_imp_minus 
    (imp_minus_state_to_sas_plus (c, is) ++ map_of (effect_of op))) = pc_to_com (effect_of op)"
    using assms by(auto simp: imp_minus_state_to_sas_plus_def sas_plus_state_to_imp_minus_def 
                   com_to_operators_variables_distinct) 
  moreover have "snd (sas_plus_state_to_imp_minus 
    (imp_minus_state_to_sas_plus (c, is) ++ map_of (effect_of op))) a = (is ++ ((\<lambda>x. (case x of 
      EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) \<circ>\<^sub>m (map_of (effect_of op)) \<circ>\<^sub>m (\<lambda>x. Some (VN x)))) a"
    for a using assms
    by(auto simp: imp_minus_state_to_sas_plus_def sas_plus_state_to_imp_minus_def 
      option.case_eq_if map_comp_def map_add_def com_to_operators_variables_distinct 
      split: domain_element.splits)
  moreover then have "snd (sas_plus_state_to_imp_minus 
    (imp_minus_state_to_sas_plus (c, is) ++ map_of (effect_of op))) = (is 
   ++ ((\<lambda>x. (case x of EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) \<circ>\<^sub>m (map_of (effect_of op)) \<circ>\<^sub>m (\<lambda>x. Some (VN x))))"
    by auto
  ultimately show ?thesis using assms by (metis prod.collapse)
qed

lemma imp_minus_state_to_sas_plus_update_PC[simp]: 
  "(imp_minus_state_to_sas_plus (c1, is1))(PC \<mapsto> PCV c2) 
  = imp_minus_state_to_sas_plus (c2, is1)"
  by(auto simp: imp_minus_state_to_sas_plus_def option.case_eq_if)

lemma sas_plus_state_to_imp_minus_of_lambda_PC[simp]: "sas_plus_state_to_imp_minus
  (\<lambda>a. if a = PC then Some (PCV c1)
       else ss a)
  = (c1, snd (sas_plus_state_to_imp_minus ss))"
  by (auto simp: imp_minus_state_to_sas_plus_def sas_plus_state_to_imp_minus_def map_comp_def)

lemma sas_plus_state_to_imp_minus_of_PC_updated[simp]: 
  "sas_plus_state_to_imp_minus (ss(PC \<mapsto> PCV c)) 
  = (c, snd (sas_plus_state_to_imp_minus ss))"
  by (auto simp: sas_plus_state_to_imp_minus_def map_comp_def)

lemma imp_minus_state_to_sas_plus_VN_eq_Some_Iff[simp]: 
  "(imp_minus_state_to_sas_plus (c, s) (VN x) = Some y) 
  \<longleftrightarrow> ((map_option EV (s x)) = Some y)"
  by (simp add: imp_minus_state_to_sas_plus_def map_comp_Some_iff)

lemma imp_minus_state_to_sas_plus_add_effect: 
  assumes "op \<in> set (com_to_operators c)"
  shows "imp_minus_state_to_sas_plus (c1, is) ++ map_of (effect_of op) 
      = imp_minus_state_to_sas_plus (pc_to_com (effect_of op), is) ++ map_of (effect_of op)"
  using assms com_to_operators_variables_distinct 
  by(auto simp: map_add_def imp_minus_state_to_sas_plus_def fun_eq_iff split: option.splits)
  
lemma imp_minus_state_to_sas_plus_of_effect: 
  assumes "op \<in> set (com_to_operators cB)"
  shows "((imp_minus_state_to_sas_plus (c1, s) ++ map_of (effect_of op))(PC \<mapsto> PCV c2) =
    imp_minus_state_to_sas_plus (c2, s')) \<longleftrightarrow> ((s ++ ((\<lambda>x. (case x of EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) 
    \<circ>\<^sub>m map_of (effect_of op) \<circ>\<^sub>m (\<lambda>x. Some (VN x)))) = s')"
proof
  assume *: "(imp_minus_state_to_sas_plus (c1, s) ++ map_of (effect_of op))(PC \<mapsto> PCV c2) 
    = imp_minus_state_to_sas_plus (c2, s')"
  have "\<forall>a. (s ++ ((\<lambda>x. (case x of EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) 
    \<circ>\<^sub>m map_of (effect_of op) \<circ>\<^sub>m (\<lambda>x. Some (VN x)))) a = s' a"
  proof(rule ccontr)
    assume "\<not>(\<forall>a. (s ++ ((\<lambda>x. (case x of EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) 
      \<circ>\<^sub>m map_of (effect_of op) \<circ>\<^sub>m (\<lambda>x. Some (VN x)))) a = s' a)"
    then obtain a where "(s ++ ((\<lambda>x. (case x of EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) 
      \<circ>\<^sub>m map_of (effect_of op) \<circ>\<^sub>m (\<lambda>x. Some (VN x)))) a \<noteq> s' a" by auto
    then have "((imp_minus_state_to_sas_plus (c1, s) ++ map_of (effect_of op))(PC \<mapsto> PCV c2)) (VN a)
      \<noteq> imp_minus_state_to_sas_plus (c2, s') (VN a)"
      by(auto simp: imp_minus_state_to_sas_plus_def map_comp_def map_add_def domD domIff 
            split: option.splits)
    then show "False" using * by auto
  qed
  then show "((s ++ ((\<lambda>x. (case x of EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) 
    \<circ>\<^sub>m map_of (effect_of op) \<circ>\<^sub>m (\<lambda>x. Some (VN x)))) = s')" by auto
next
  assume *: "((s ++ ((\<lambda>x. (case x of EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) 
    \<circ>\<^sub>m map_of (effect_of op) \<circ>\<^sub>m (\<lambda>x. Some (VN x)))) = s')"
  then have "((imp_minus_state_to_sas_plus (c1, s) ++ map_of (effect_of op))(PC \<mapsto> PCV c2)) a
      = imp_minus_state_to_sas_plus (c2, s') a" for a
    using assms by(cases a) (auto simp: com_to_operators_variables_distinct 
        imp_minus_state_to_sas_plus_def map_comp_def map_add_def option.case_eq_if
        split: option.splits domain_element.splits)
  then show "(imp_minus_state_to_sas_plus (c1, s) ++ map_of (effect_of op))(PC \<mapsto> PCV c2) 
    = imp_minus_state_to_sas_plus (c2, s')" by auto
qed

lemma imp_minus_state_to_sas_plus_of_effect': 
  assumes "op \<in> set (com_to_operators cB)"
  shows "((imp_minus_state_to_sas_plus (c1, s) ++ map_of (effect_of op)) =
    imp_minus_state_to_sas_plus (c2, s')) \<longleftrightarrow> ((pc_to_com (effect_of op) = c2) \<and> 
  (s ++ ((\<lambda>x. (case x of EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) 
    \<circ>\<^sub>m map_of (effect_of op) \<circ>\<^sub>m (\<lambda>x. Some (VN x)))) = s')"
proof -
  have "imp_minus_state_to_sas_plus (c1, s) ++ map_of (effect_of op) = 
    ((imp_minus_state_to_sas_plus (c1, s) ++ map_of (effect_of op))
    (PC \<mapsto> PCV (pc_to_com (effect_of op))))"
    using assms com_to_operators_variables_distinct by auto
  moreover have "((imp_minus_state_to_sas_plus (c1, s) ++ map_of (effect_of op))
  (PC \<mapsto> PCV (pc_to_com (effect_of op))) =
    imp_minus_state_to_sas_plus ((pc_to_com (effect_of op)), s')) 
    \<longleftrightarrow> ((s ++ ((\<lambda>x. (case x of EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) 
    \<circ>\<^sub>m map_of (effect_of op) \<circ>\<^sub>m (\<lambda>x. Some (VN x)))) = s')" 
    using assms imp_minus_state_to_sas_plus_of_effect by blast
  ultimately show ?thesis using assms imp_minus_state_to_sas_plus_def map_upd_eqD1 
    by (metis domain_element.inject fst_conv)
qed

lemma updated_state_is_sane:
  assumes "op \<in> set (com_to_operators c)" 
    "sane_sas_plus_state ss1"
  shows "sane_sas_plus_state (ss1 \<then>\<^sub>+ op)"
proof -
  have "\<exists>x. (VN v, EV x) \<in> set (effect_of op) \<or> map_of (effect_of op) (VN v) = None" for v
    using assms variables_in_effect by simp
  then show ?thesis using assms 
    apply(auto simp: sane_sas_plus_state_def com_to_operators_variables_distinct 
        map_add_Some_iff) 
    using in_set_effect by blast
qed

lemma imp_minus_state_to_sas_plus_update_VN[simp]: "(\<lambda>a. if a = PC then Some (PCV c2) 
   else ((imp_minus_state_to_sas_plus (c1, is1))(VN x \<mapsto> EV y)) a)
    = imp_minus_state_to_sas_plus (c2, is1(x \<mapsto> y))"
proof -
  have "(if a = PC then Some (PCV c2) else (((imp_minus_state_to_sas_plus (c1, is1))(VN x \<mapsto> EV y)) a))
    = (imp_minus_state_to_sas_plus (c2, is1(x \<mapsto> y))) a" for a
    by (auto simp: imp_minus_state_to_sas_plus_def map_comp_def split: variable.splits)
  then show ?thesis by auto
qed

lemma VN_PC_map_le_iff[simp]: "[VN v \<mapsto> y, PC \<mapsto> x] \<subseteq>\<^sub>m (imp_minus_state_to_sas_plus (c1, is)) 
  = (x = PCV c1 \<and> map_option EV (is v) = Some y)"
  by (auto simp: map_le_def imp_minus_state_to_sas_plus_def option.case_eq_if map_comp_def)

lemma operator_with_PC_updated_applicable_iff[simp]: "op \<in> set (com_to_operators c1) \<Longrightarrow> 
  (map_of (precondition_of op))(PC \<mapsto> PCV c2) \<subseteq>\<^sub>m imp_minus_state_to_sas_plus (c2, s)
  \<longleftrightarrow>  map_of (precondition_of op) \<subseteq>\<^sub>m imp_minus_state_to_sas_plus (c1, s)"
  by(auto simp: imp_minus_state_to_sas_plus_def map_le_def)

lemma applicable_in_imp_minus_then[simp]: 
  "is_operator_applicable_in (imp_minus_state_to_sas_plus (c1, is)) 
  \<lparr>precondition_of = [(PC, x), (VN v, y)], effect_of = effect\<rparr> 
  \<longleftrightarrow> (x = PCV c1 \<and> map_option EV (is v) = Some y)"
  by (auto simp: map_le_def imp_minus_state_to_sas_plus_def option.case_eq_if map_comp_def)

lemma op_in_com_operators[simp]:
  "\<lbrakk>op \<in> set ((imp_minus_minus_to_sas_plus c I G)\<^sub>\<O>\<^sub>+);
    is_operator_applicable_in s op\<rbrakk> 
    \<Longrightarrow> op \<in> set (com_to_operators (fst (sas_plus_state_to_imp_minus s)))"
proof (goal_cases)
  case 1
  {
  fix x
  assume  "map_of (precondition_of op) \<subseteq>\<^sub>m s"
    "op \<in> set (com_to_operators x)"
  moreover then have "(map_of (precondition_of op)) PC = Some (PCV x)" by auto
  ultimately have "the (s PC) = PCV x" by (metis domI map_le_def option.sel)
  then have "op \<in> set (com_to_operators (case the (s PC) of PCV c \<Rightarrow> c))" 
    by (simp add: \<open>op \<in> set (com_to_operators x)\<close>)
  }
  thus ?thesis
    using 1
  by(auto simp: imp_minus_minus_to_sas_plus_def Let_def coms_to_operators_def 
      sas_plus_state_to_imp_minus_def)

qed

lemma PC_map_le_iff[simp]: "[PC \<mapsto> x] \<subseteq>\<^sub>m (imp_minus_state_to_sas_plus (c1, is)) 
  = (x = PCV c1)"
  by (auto simp: map_le_def imp_minus_state_to_sas_plus_def)

lemma map_of_list_update: "distinct (map fst l) \<Longrightarrow> length l > 0 \<Longrightarrow> fst (l ! 0) = x  \<Longrightarrow> z \<noteq> x
  \<Longrightarrow> map_of (list_update l 0 (x, y)) z = map_of l z"
  by (induction l) auto

lemma map_of_update_PC_in_effect_of_op[simp]: assumes "op \<in> set (com_to_operators c)"
  shows "map_of (list_update (effect_of op) 0 (PC, y)) = (map_of (effect_of op))(PC \<mapsto> y)"
proof -
  have "map_of (list_update (effect_of op) 0 (PC, y)) x = ((map_of (effect_of op))(PC \<mapsto> y)) x" for x
    using assms com_to_operators_variables_distinct effect_nonempty 
      map_of_list_update[where ?l = "effect_of op"]
    by (auto) 
      (metis effect_nonempty fst_of_effect map_of_eq_Some_iff set_update_memI update_preserve_distinct)
  then show ?thesis by auto
qed

lemma map_of_update_PC_in_precondition_of_op[simp]: assumes "op \<in> set (com_to_operators c)"
  shows "map_of (list_update (precondition_of op) 0 (PC, y)) = (map_of (precondition_of op))(PC \<mapsto> y)"
proof -
  have "map_of (list_update (precondition_of op) 0 (PC, y)) x = ((map_of (precondition_of op))(PC \<mapsto> y)) x" for x
    using assms com_to_operators_variables_distinct precondition_nonempty 
      map_of_list_update[where ?l = "precondition_of op"]
    by (auto) 
     (metis precondition_nonempty fst_of_precondition map_of_eq_Some_iff set_update_memI update_preserve_distinct)
  then show ?thesis by auto
qed

lemma pc_of_op: 
  assumes "op \<in> set (com_to_operators c2)"
    "ss2 = imp_minus_state_to_sas_plus (c1, is)" 
    "ss1 \<then>\<^sub>+ op = ss2"
  shows "pc_to_com (effect_of op) = c1" 
proof -
  have "(ss1 \<then>\<^sub>+ op) PC = Some (PCV c1)" using assms by simp
  then show ?thesis using assms com_to_operators_variables_distinct by auto
qed

lemma effect_in_updated[simp]: 
  assumes "op' \<in> set (com_to_operators c)" 
    "map_of (precondition_of op') = (map_of (precondition_of op))(PC \<mapsto> PCV c)"
    "map_of (effect_of op') = (map_of (effect_of op))(PC \<mapsto> PCV (pc_to_com (effect_of op')))"
    "s \<then>\<^sub>+ op = s'"
  shows "s(PC \<mapsto> PCV c) \<then>\<^sub>+ op' = s'(PC \<mapsto> PCV (pc_to_com (effect_of op')))" 
proof -
  have "(s(PC \<mapsto> PCV c)  \<then>\<^sub>+ op') x = (s'(PC \<mapsto> PCV (pc_to_com (effect_of op')))) x" for x
    using assms PC_in_effect_precondition com_to_operators_variables_distinct apply auto
    by (metis fun_upd_other map_add_def)
  then show ?thesis by auto
qed

lemma applicable_in_PC_updated: "m \<subseteq>\<^sub>m s(PC \<mapsto> y) \<Longrightarrow> s PC = Some x \<Longrightarrow> m(PC \<mapsto> x) \<subseteq>\<^sub>m s"
  by (simp add: map_le_def)

text \<open> We first show that every operation in SAS++ corresponds to a single step in IMP- \<close>

lemma sas_plus_plus_to_imp_minus_minus_single_step:
  "op \<in> set (com_to_operators c1)
  \<Longrightarrow> c1 \<in> set (enumerate_subprograms c) \<Longrightarrow> t > 0 
  \<Longrightarrow> is_operator_applicable_in (imp_minus_state_to_sas_plus (c1, is1)) op
  \<Longrightarrow> (c1, is1) \<rightarrow>
  sas_plus_state_to_imp_minus ((imp_minus_state_to_sas_plus (c1, is1)) \<then>\<^sub>+ op)"
proof (induction c1 arbitrary: op is1)
  case (Seq cA cB)
  have "cA = SKIP \<or> cA \<noteq> SKIP" by auto
  then show ?case using Seq
  proof (elim disjE)
    assume "cA \<noteq> SKIP"
    then obtain op' where op'_def: "op' \<in> set (com_to_operators cA)"
      "op = (let c1' = pc_to_com (effect_of op') in 
      \<lparr> precondition_of = list_update (precondition_of op') 0 (PC, PCV (cA ;; cB)),
        effect_of = list_update (effect_of op') 0 (PC, PCV (c1' ;; cB))\<rparr>)" using Seq by auto
    let ?c1' = "pc_to_com (effect_of op')"
    let ?ss1' = "(imp_minus_state_to_sas_plus ((cA ;; cB), is1))(PC \<mapsto> PCV cA)"
    let ?ss2' = "((imp_minus_state_to_sas_plus ((cA ;; cB), is1)) \<then>\<^sub>+ op)(PC \<mapsto> PCV ?c1')"
    have "cA \<in> set (enumerate_subprograms c)" 
      using \<open>cA;;cB \<in> set (enumerate_subprograms c)\<close> c_in_all_subprograms_c
      by (force intro!: enumerate_subprograms_transitive[where ?c2.0 = "cA;; cB"])
    then have "(cA, is1) \<rightarrow> sas_plus_state_to_imp_minus ?ss2'"
      using \<open>0 < t\<close> op'_def Seq  imp_minus_state_to_sas_plus_add_effect[where ?c1.0="cA;; cB"]
      imp_minus_state_to_sas_plus_add_effect[where ?c1.0="cA"] 
      by(auto simp: com_to_operators_variables_distinct fun_upd_idem)
    then show ?thesis using op'_def by auto
  qed auto
qed(auto simp: Let_def map_leq_imp_minus_state_to_sas_plus_iff)


text \<open> Next, we show that a plan in SAS++ corresponds to executing several steps in IMP- \<close>

lemma sas_plus_plus_to_imp_minus_minus_aux:
  "set ops \<subseteq> set ((imp_minus_minus_to_sas_plus c I G)\<^sub>\<O>\<^sub>+) 
  \<Longrightarrow> sane_sas_plus_state ss1
  \<Longrightarrow> execute_serial_plan_sas_plus ss1 ops = ss2
  \<Longrightarrow> (\<exists>t'. t' \<le> length ops 
    \<and> sas_plus_state_to_imp_minus ss1 \<rightarrow>\<^bsup>t'\<^esup> sas_plus_state_to_imp_minus ss2)"
proof (induction ops arbitrary: ss1)
  case (Cons op ops)
  let ?c1 = "fst (sas_plus_state_to_imp_minus ss1)"
  let ?is1 = "snd (sas_plus_state_to_imp_minus ss1)"
  let ?ss1' = "ss1 \<then>\<^sub>+ op" 
  have "is_operator_applicable_in ss1 op \<or> \<not>(is_operator_applicable_in ss1 op)" by auto
  then show ?case using Cons
  proof (elim disjE)
    assume a: "is_operator_applicable_in ss1 op"
    then have op_in_cto_c1: "op \<in> set (com_to_operators ?c1)" using Cons by auto
    moreover then have "?c1 \<in> set (enumerate_subprograms c)" using Cons a 
      apply(auto simp: imp_minus_minus_to_sas_plus_def Let_def coms_to_operators_def)
      by (metis PC_of_precondition domain_element.simps op_in_cto_c1)
    ultimately have c1_to_c1': "(?c1, ?is1) \<rightarrow> sas_plus_state_to_imp_minus 
      (imp_minus_state_to_sas_plus (?c1, ?is1) \<then>\<^sub>+ op)" 
      apply(rule sas_plus_plus_to_imp_minus_minus_single_step)
      using Cons a op_in_cto_c1 by auto
    moreover then have "execute_serial_plan_sas_plus ?ss1' ops = ss2"
      and "sane_sas_plus_state ?ss1'" 
      using Cons a op_in_cto_c1 updated_state_is_sane by auto 
    ultimately have "\<exists>t'. t' \<le> length ops \<and> sas_plus_state_to_imp_minus ?ss1' 
      \<rightarrow>\<^bsup>t'\<^esup> sas_plus_state_to_imp_minus ss2"
      using Cons by(auto)
    moreover have "imp_minus_state_to_sas_plus (?c1, ?is1) \<then>\<^sub>+ op = ?ss1'" using Cons by auto
    ultimately show ?case using c1_to_c1' by auto
  qed auto
qed auto

lemma all_zero_than_zero_map_le: "\<forall>b\<in>set bs. s b = Some Zero 
  \<Longrightarrow> map_of (map (\<lambda>v. (v, Zero)) (remdups bs)) \<subseteq>\<^sub>m s" 
  apply(induction bs) 
  by(auto simp: map_le_def)

text \<open> For the other direction, we again first show that a single step in IMP- always 
      corresponds to applying one operation in SAS++ \<close>

lemma imp_minus_minus_to_sas_plus_plus_single_step:
   "(c1, is1) \<rightarrow> (c2, is2) 
  \<Longrightarrow> c1 \<in> set (enumerate_subprograms c)
  \<Longrightarrow> dom is1 = set (enumerate_variables c)
  \<Longrightarrow> (\<exists>op \<in> set (com_to_operators c1).
      execute_operator_sas_plus (imp_minus_state_to_sas_plus (c1, is1)) op 
        =  imp_minus_state_to_sas_plus (c2, is2)
    \<and> is_operator_applicable_in (imp_minus_state_to_sas_plus (c1, is1)) op)"
proof (induction c1 is1 c2 is2 rule: small_step_induct)
  case (Assign x a s)
  thus ?case by auto
next
  case (Seq2 c\<^sub>1 s c\<^sub>1' s' c\<^sub>2)
  have "c\<^sub>1 \<in> set (enumerate_subprograms (c\<^sub>1 ;; c\<^sub>2))" using c_in_all_subprograms_c by auto
  then have "c\<^sub>1 \<in> set (enumerate_subprograms c)" using Seq2 enumerate_subprograms_transitive by blast
  then obtain op' where op'_def: "op' \<in> set (com_to_operators c\<^sub>1) \<and>
    execute_operator_sas_plus (imp_minus_state_to_sas_plus (c\<^sub>1, s)) op'
        =  imp_minus_state_to_sas_plus (c\<^sub>1', s')
    \<and> is_operator_applicable_in (imp_minus_state_to_sas_plus (c\<^sub>1, s)) op'" 
    using Seq2 by fastforce
  let ?op = "\<lparr> precondition_of = list_update (precondition_of op') 0 (PC, PCV (c\<^sub>1 ;; c\<^sub>2)),
        effect_of = list_update (effect_of op') 0 (PC, PCV (c\<^sub>1' ;; c\<^sub>2))\<rparr>"
  have "?op \<in> set (com_to_operators (c\<^sub>1 ;; c\<^sub>2))"
    and "execute_operator_sas_plus (imp_minus_state_to_sas_plus ((c\<^sub>1 ;; c\<^sub>2), s)) ?op 
        = imp_minus_state_to_sas_plus ((c\<^sub>1' ;; c\<^sub>2), s')"
    and "is_operator_applicable_in (imp_minus_state_to_sas_plus ((c\<^sub>1 ;; c\<^sub>2), s)) ?op"
    using Seq2 op'_def imp_minus_state_to_sas_plus_of_effect imp_minus_state_to_sas_plus_of_effect'
    by auto
  then show ?case using Seq2 by blast
next
  case (IfTrue s b c\<^sub>1 c\<^sub>2)
  have "b \<in> set (enumerate_variables c)" 
    using IfTrue enumerate_subprograms_enumerate_variables by fastforce
  hence "\<exists>y. s b = Some y" using \<open>dom s = set (enumerate_variables c)\<close> by auto
  then show ?case using IfTrue by (auto simp: Let_def) 
next
  case (IfFalse s b c\<^sub>1 c\<^sub>2)
  hence "b \<in> set (enumerate_variables c)" 
    using enumerate_subprograms_enumerate_variables by fastforce
  thus ?case using IfFalse 
    by(auto simp: Let_def map_leq_imp_minus_state_to_sas_plus_iff all_zero_than_zero_map_le) 
next
  case (WhileTrue s b c1)
  hence "b \<in> set (enumerate_variables c)" 
    using  enumerate_subprograms_enumerate_variables by fastforce
  then show ?case using WhileTrue
    by(force simp: Let_def map_leq_imp_minus_state_to_sas_plus_iff all_zero_than_zero_map_le)
next
  case (WhileFalse s b c1)
   hence "b \<in> set (enumerate_variables c)" 
    using  enumerate_subprograms_enumerate_variables by fastforce
  then show ?case using WhileFalse
    by(force simp: Let_def map_leq_imp_minus_state_to_sas_plus_iff all_zero_than_zero_map_le)
qed auto

text \<open> Next, we show that taking multiple steps in IMP- corresponds to executing multiple
      operations in SAS++ \<close>

lemma imp_minus_minus_to_sas_plus_plus_aux:
   "(c1, is1) \<rightarrow>\<^bsup>t\<^esup> (c2, is2)
  \<Longrightarrow> c1 \<in> set (enumerate_subprograms c)
  \<Longrightarrow> dom is1 = set (enumerate_variables c)
  \<Longrightarrow> (\<exists>ops. set ops \<subseteq> set ((imp_minus_minus_to_sas_plus c I G)\<^sub>\<O>\<^sub>+)
     \<and> length ops = t
     \<and> (execute_serial_plan_sas_plus (imp_minus_state_to_sas_plus (c1, is1)) ops)
        = imp_minus_state_to_sas_plus (c2, is2))"
proof (induction t arbitrary: c1 is1)
  case (Suc t)
  obtain c1' is1' where c1'_def: "(c1, is1) \<rightarrow> (c1', is1')
    \<and> (c1', is1') \<rightarrow>\<^bsup>t\<^esup> (c2, is2)" using Suc by auto
  then obtain op where op_def: "op \<in> set (com_to_operators c1)
    \<and> execute_operator_sas_plus (imp_minus_state_to_sas_plus (c1, is1)) op 
        =  imp_minus_state_to_sas_plus (c1', is1')
    \<and> is_operator_applicable_in (imp_minus_state_to_sas_plus (c1, is1)) op" 
    using imp_minus_minus_to_sas_plus_plus_single_step Suc by metis
  then have "dom is1' = set (enumerate_variables c)" 
    using c1'_def Suc step_doesnt_add_variables
     apply (auto simp: domIff)
    by (metis domD domIff option.simps(3) step_doesnt_add_variables)+
  moreover have "c1' \<in> set (enumerate_subprograms c)" using c1'_def enumerate_subprograms_transitive 
    enumerate_subprograms_complete_step
    using Suc.prems by blast+
  ultimately obtain ops where ops_def: "set ops \<subseteq> set ((imp_minus_minus_to_sas_plus c I G)\<^sub>\<O>\<^sub>+)
     \<and> length ops = t
     \<and> (execute_serial_plan_sas_plus (imp_minus_state_to_sas_plus (c1', is1')) ops)
        = imp_minus_state_to_sas_plus (c2, is2)"
    using Suc c1'_def Suc_lessD by blast
  let ?ops' = "op # ops"
  have "set ?ops' \<subseteq> set ((imp_minus_minus_to_sas_plus c I G)\<^sub>\<O>\<^sub>+)
     \<and> length ?ops' = Suc t
     \<and> (execute_serial_plan_sas_plus (imp_minus_state_to_sas_plus (c1, is1)) ?ops')
        = imp_minus_state_to_sas_plus (c2, is2)"
    using Suc c1'_def op_def ops_def
    by (auto simp: imp_minus_minus_to_sas_plus_def Let_def coms_to_operators_def)
  then show ?case by blast
qed auto

text \<open> In the previous correctness lemmas, we formulated the statements as to permit arbitrary
       initial and final states that could occur sometime during the execution. We now proceed 
       to reformulate them in simpler terms, using the initial initial and final states as specified
       in the SAS++ problem translated from IMP-. \<close>

lemma imp_minus_minus_to_sas_plus_plus:
  assumes "(c, is1) \<rightarrow>\<^bsup>t\<^esup> (SKIP, is2)"
   "dom is1 = set (enumerate_variables c)"
   "I \<subseteq>\<^sub>m is1"
   "G \<subseteq>\<^sub>m is2"
   "t \<le> t'"
  shows "(\<exists>plan.
     is_serial_solution_for_problem_sas_plus_plus (imp_minus_minus_to_sas_plus c I G) plan
     \<and> length plan \<le> t')"
proof -
  let ?\<Psi> = "imp_minus_minus_to_sas_plus c I G"
  let ?I' = "imp_minus_state_to_sas_plus (c, is1)" 
  obtain plan where plan_def: "set plan \<subseteq> set ((?\<Psi>)\<^sub>\<O>\<^sub>+)
     \<and> length plan = t
     \<and> (execute_serial_plan_sas_plus ?I' plan)
        = imp_minus_state_to_sas_plus (SKIP, is2)"
    using imp_minus_minus_to_sas_plus_plus_aux[OF assms(1)] assms c_in_all_subprograms_c by blast
  moreover then have "(?\<Psi>)\<^sub>G\<^sub>+ \<subseteq>\<^sub>m execute_serial_plan_sas_plus ?I' plan"
    and "dom ?I' = set (((?\<Psi>))\<^sub>\<V>\<^sub>+)"
    and "(\<forall> v \<in> set ((?\<Psi>)\<^sub>\<V>\<^sub>+). the (?I' v) \<in> range_of' ?\<Psi> v)"
    and "((?\<Psi>)\<^sub>I\<^sub>+) \<subseteq>\<^sub>m ?I'"
    using assms plan_def c_in_all_subprograms_c
    apply(auto simp: imp_minus_minus_to_sas_plus_def Let_def 
                     range_of'_def imp_minus_state_to_sas_plus_def map_comp_def map_le_def
               split: option.splits variable.splits)
        apply (auto )
    by (metis domIff option.distinct option.inject)+
  ultimately have "is_serial_solution_for_problem_sas_plus_plus ?\<Psi> plan" 
    using assms
    by(auto simp: is_serial_solution_for_problem_sas_plus_plus_def Let_def list_all_def ListMem_iff)
  then show ?thesis using plan_def \<open>t \<le> t'\<close>
    by blast
qed

lemma sas_plus_plus_to_imp_minus_minus:
  assumes "is_serial_solution_for_problem_sas_plus_plus (imp_minus_minus_to_sas_plus c I G) plan"
    "EV ` (ran I) \<subseteq> set domain"
    "EV ` (ran G) \<subseteq> set domain"
  shows "\<exists>is1 is2 t. (I|` set (enumerate_variables c)) \<subseteq>\<^sub>m is1 \<and> dom is1 = set (enumerate_variables c)
    \<and> (G|` set (enumerate_variables c)) \<subseteq>\<^sub>m is2 \<and> t \<le> length plan 
    \<and> (c, is1) \<rightarrow>\<^bsup>t\<^esup> (SKIP, is2)" 
proof -
  let ?\<Psi> = "imp_minus_minus_to_sas_plus c I G"
  obtain I' where I'_def: "((?\<Psi>)\<^sub>I\<^sub>+) \<subseteq>\<^sub>m I' \<and> dom I' = set ((?\<Psi>)\<^sub>\<V>\<^sub>+) 
        \<and> (\<forall>v \<in> set ((?\<Psi>)\<^sub>\<V>\<^sub>+). the (I' v) \<in> range_of' ?\<Psi> v)
        \<and> ((?\<Psi>)\<^sub>G\<^sub>+) \<subseteq>\<^sub>m execute_serial_plan_sas_plus I' plan" 
    using assms by (auto simp: is_serial_solution_for_problem_sas_plus_plus_def Let_def)
  let ?ss2 = "execute_serial_plan_sas_plus I' plan"
  let ?is1 = "snd (sas_plus_state_to_imp_minus I')"
  let ?is2 = "snd (sas_plus_state_to_imp_minus ?ss2)"
  have "\<forall>v\<in>set (enumerate_variables c). (\<exists>y \<in> set domain. I' (VN v) = Some y)" 
    using I'_def 
    apply (auto simp: imp_minus_minus_to_sas_plus_def Let_def range_of'_def)[1]
    by (metis domIff image_insert insertI1 insertI2 mk_disjoint_insert option.collapse)
  then have "sane_sas_plus_state I'"
    using I'_def assms
    apply(auto simp: domIff sane_sas_plus_state_def imp_minus_minus_to_sas_plus_def Let_def map_le_def 
                     range_of'_def)[1]
    by (metis domIff insertI1 option.collapse)
  then obtain t where t_def: "t \<le> length plan \<and> sas_plus_state_to_imp_minus I' 
    \<rightarrow>\<^bsup>t\<^esup> sas_plus_state_to_imp_minus ?ss2"
    apply - apply(rule exE[OF sas_plus_plus_to_imp_minus_minus_aux[where ?ops=plan]])
    using assms I'_def  
    by(auto simp: is_serial_solution_for_problem_sas_plus_plus_def Let_def list_all_def ListMem_iff)
    
  moreover have "fst (sas_plus_state_to_imp_minus I') = c"
                "fst (sas_plus_state_to_imp_minus ?ss2) = SKIP"
    using assms(3) I'_def  
   by(clarsimp simp: imp_minus_minus_to_sas_plus_def Let_def 
                     sas_plus_state_to_imp_minus_def map_le_def imp_minus_state_to_sas_plus_def
                     sane_sas_plus_state_def
                   split: option.splits if_splits domain_element.splits)+
  ultimately have "((c, ?is1) \<rightarrow>\<^bsup>t\<^esup> (SKIP, ?is2))" 
    using I'_def by (metis prod.collapse)
  moreover have "(I|` set (enumerate_variables c)) \<subseteq>\<^sub>m ?is1"
    "(G|` set (enumerate_variables c)) \<subseteq>\<^sub>m ?is2"
    using assms(2) I'_def 
    by (auto simp: imp_minus_minus_to_sas_plus_def imp_minus_state_to_sas_plus_map_le_then Let_def 
        range_of'_def)
  moreover have "dom ?is1 = set (enumerate_variables c)"
    using \<open>sane_sas_plus_state I'\<close> I'_def by(auto simp: imp_minus_minus_to_sas_plus_def 
        dom_snd_sas_plus_state_to_imp_minus Let_def)
  ultimately show ?thesis using I'_def t_def by auto
qed
    
    
end