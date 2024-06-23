theory GOTO_Prog_to_While_Prog
  imports GOTO_Instr_to_While_Prog
begin

definition if_neq :: "char list \<Rightarrow> nat \<Rightarrow> com \<Rightarrow> com \<Rightarrow> com" where
  "if_neq y k C1 C2 = 
    y ::= (atomExp.V y \<ominus> atomExp.N k) ;; 
    IF y\<noteq>0 THEN 
      (y ::= (atomExp.V y \<oplus> atomExp.N k) ;; C1)
    ELSE
      (y ::= (atomExp.V y \<oplus> atomExp.N k) ;; C2)"

lemma if_neq_trans_ins_2_out_eq:
  assumes "s y = k"
    and "(C2, s) \<Rightarrow>\<^bsup> i \<^esup> t"
  shows "(if_neq y k C1 C2, s) \<Rightarrow>\<^bsup> i + 5 \<^esup> t"
proof -
  let ?step1 = "y ::= (atomExp.V y \<ominus> atomExp.N k)"
  let ?state1 = "s(y := s y - k)"
  let ?step2 = "y ::= (atomExp.V y \<oplus> atomExp.N k)"
  let ?step23 = "
    IF y\<noteq>0 THEN 
      (y ::= (atomExp.V y \<oplus> atomExp.N k) ;; C1)
    ELSE
      (y ::= (atomExp.V y \<oplus> atomExp.N k) ;; C2)
  "
  have aux1: "(?step1, s) \<Rightarrow>\<^bsup> 2 \<^esup> ?state1" by (simp add: assign_t_simp numeral_2_eq_2)
  hence aux3: "?state1 y = 0" by (simp add: assms(1))
  hence aux4: "(?step2, ?state1) \<Rightarrow>\<^bsup> 2 \<^esup> s" 
    by (smt (verit) ASSnot add_0 assms(1) atomVal.simps(1) atomVal.simps(2) aval.simps(2) fun_upd_triv fun_upd_upd numeral_2_eq_2)
  hence "(?step2 ;; C2, ?state1) \<Rightarrow>\<^bsup> 2 + i \<^esup> t" using Seq assms(2) by presburger
  hence aux2: "(?step23, ?state1) \<Rightarrow>\<^bsup> 3 + i \<^esup> t" using aux3 by fastforce
  thus "(if_neq y k C1 C2, s) \<Rightarrow>\<^bsup> i + 5 \<^esup> t" using aux1 aux2 if_neq_def by fastforce
qed

lemma if_neq_trans_ins_2_out_gt:
  assumes "s y > k"
    and "(C1, s) \<Rightarrow>\<^bsup> i \<^esup> t"
  shows "(if_neq y k C1 C2, s) \<Rightarrow>\<^bsup> i + 5 \<^esup> t"
proof -
  let ?step1 = "y ::= (atomExp.V y \<ominus> atomExp.N k)"
  let ?state1 = "s(y := s y - k)"
  let ?step2 = "y ::= (atomExp.V y \<oplus> atomExp.N k)"
  let ?step23 = "
    IF y\<noteq>0 THEN 
      (y ::= (atomExp.V y \<oplus> atomExp.N k) ;; C1)
    ELSE
      (y ::= (atomExp.V y \<oplus> atomExp.N k) ;; C2)
  "
  have aux1: "(?step1, s) \<Rightarrow>\<^bsup> 2 \<^esup> ?state1" by (simp add: assign_t_simp numeral_2_eq_2)
  hence aux3: "?state1 y = s y - k" by (simp add: assms(1))
  hence aux5: "?state1 y \<noteq> 0" using assms(1) by linarith
  have aux4: "(?step2, ?state1) \<Rightarrow>\<^bsup> 2 \<^esup> s" using aux3
    by (simp add: assign_t_simp assms(1) less_or_eq_imp_le numeral_2_eq_2)
  hence aux6: "(?step2 ;; C1, ?state1) \<Rightarrow>\<^bsup> 2 + i \<^esup> t" using Seq assms(2) by presburger
  have aux2: "(?step23, ?state1) \<Rightarrow>\<^bsup> 3 + i \<^esup> t" 
    using IfTrue[of ?state1 y "?step2 ;; C1" "2 + i" t "3 + i" "y ::= (atomExp.V y \<oplus> atomExp.N k) ;; C2", OF aux5 aux6] by simp
  thus "(if_neq y k C1 C2, s) \<Rightarrow>\<^bsup> i + 5 \<^esup> t" using aux1 aux2 if_neq_def by fastforce
qed

lemma if_neq_trans_out_2_ins_eq:
  assumes "s y = k"
    and "(if_neq y k C1 C2, s) \<Rightarrow>\<^bsup> i + 5 \<^esup> t"
  shows "(C2, s) \<Rightarrow>\<^bsup> i \<^esup> t"
proof -
  let ?step1 = "y ::= (atomExp.V y \<ominus> atomExp.N k)"
  let ?state1 = "s(y := s y - k)"
  let ?step2 = "y ::= (atomExp.V y \<oplus> atomExp.N k)"
  let ?step23 = "
    IF y\<noteq>0 THEN 
      (y ::= (atomExp.V y \<oplus> atomExp.N k) ;; C1)
    ELSE
      (y ::= (atomExp.V y \<oplus> atomExp.N k) ;; C2)
  "
  have aux1: "(?step1, s) \<Rightarrow>\<^bsup> 2 \<^esup> ?state1" by (simp add: assign_t_simp numeral_2_eq_2)
  hence aux2: "?state1 y = 0" by (simp add: assms(1))
  hence aux3: "(?step23, ?state1) \<Rightarrow>\<^bsup> i + 3 \<^esup> t"
    by (smt (verit, del_insts) Seq_tE add.commute add_diff_cancel_left' add_diff_cancel_right' add_numeral_left assms(2) aux1 bigstep_det if_neq_def numeral_Bit0 numeral_plus_numeral semiring_norm(5))
  hence aux4: "(y ::= (atomExp.V y \<oplus> atomExp.N k) ;; C2, ?state1) \<Rightarrow>\<^bsup> i + 2 \<^esup> t" using aux2 by auto
  have "(y ::= (atomExp.V y \<oplus> atomExp.N k), ?state1) \<Rightarrow>\<^bsup> 2 \<^esup> s"
    by (smt (verit, ccfv_SIG) Suc_eq_plus1 add.commute add.right_neutral assign_t_simp assms(1) atomVal.simps(1) atomVal.simps(2) aval.simps(2) diff_self_eq_0 fun_upd_same fun_upd_triv fun_upd_upd one_add_one)
  thus "(C2, s) \<Rightarrow>\<^bsup> i \<^esup> t" using aux4 by force
qed

lemma if_neq_trans_out_2_ins_gt:
  assumes "s y > k"
    and "(if_neq y k C1 C2, s) \<Rightarrow>\<^bsup> i + 5 \<^esup> t"
  shows "(C1, s) \<Rightarrow>\<^bsup> i \<^esup> t"
proof -
  let ?step1 = "y ::= (atomExp.V y \<ominus> atomExp.N k)"
  let ?state1 = "s(y := s y - k)"
  let ?step2 = "y ::= (atomExp.V y \<oplus> atomExp.N k)"
  let ?step23 = "
    IF y\<noteq>0 THEN 
      (y ::= (atomExp.V y \<oplus> atomExp.N k) ;; C1)
    ELSE
      (y ::= (atomExp.V y \<oplus> atomExp.N k) ;; C2)
  "
  have aux1: "(?step1, s) \<Rightarrow>\<^bsup> 2 \<^esup> ?state1" by (simp add: assign_t_simp numeral_2_eq_2)
  hence aux2: "?state1 y \<noteq> 0" using assms(1) by auto
  hence aux3: "(?step23, ?state1) \<Rightarrow>\<^bsup> i + 3 \<^esup> t"
    by (smt (verit, del_insts) Seq_tE add.commute add_diff_cancel_left' add_diff_cancel_right' add_numeral_left assms(2) aux1 bigstep_det if_neq_def numeral_Bit0 numeral_plus_numeral semiring_norm(5))
  hence aux4: "(y ::= (atomExp.V y \<oplus> atomExp.N k) ;; C1, ?state1) \<Rightarrow>\<^bsup> i + 2 \<^esup> t" using aux2 by auto
  have "(y ::= (atomExp.V y \<oplus> atomExp.N k), ?state1) \<Rightarrow>\<^bsup> 2 \<^esup> s" by (simp add: AssignI'' assms(1) less_or_eq_imp_le)
  thus "(C1, s) \<Rightarrow>\<^bsup> i \<^esup> t" using aux4 by force
qed

function (sequential) GOTO_Prog_to_WHILE_IF' :: "GOTO_Prog \<Rightarrow> nat \<Rightarrow> com" where 
  "GOTO_Prog_to_WHILE_IF' prog t = (if t > length prog then SKIP else if_neq ''pc'' t 
    (GOTO_Prog_to_WHILE_IF' prog (Suc t)) (GOTO_Instr_to_WHILE (prog !! t)))"
  apply pat_completeness apply auto done
termination apply (relation "measure (\<lambda>(prog, t) . length prog + 1 - t)") apply auto[] apply auto[] done

definition GOTO_Prog_to_WHILE_IF :: "GOTO_Prog \<Rightarrow> com" where 
  "GOTO_Prog_to_WHILE_IF prog = GOTO_Prog_to_WHILE_IF' prog 1"

value "GOTO_Prog_to_WHILE_IF [''x'' ;;= N 3, ''y'' ;;= N 4, ''z'' ;;= V ''x'', ''z'' += V ''y'', HALT]"

lemma GOTO_Prog_to_WHILE_IF'_correctness_complexity:
  assumes "1 \<le> min_pc" and "min_pc \<le> pc" and "pc \<le> length prog" and "s ''pc'' = pc"
    and "(GOTO_Instr_to_WHILE (prog !! pc), s) \<Rightarrow>\<^bsup> i \<^esup> t"
  shows "(GOTO_Prog_to_WHILE_IF' prog min_pc, s) \<Rightarrow>\<^bsup> i + (pc + 1 - min_pc) * 5 \<^esup> t" using assms
proof (induction prog min_pc arbitrary: rule: GOTO_Prog_to_WHILE_IF'.induct)
  case (1 prog min_pc)
  consider (c1) "min_pc = pc" | (c2) "min_pc < pc" using "1.prems"(2) by linarith
  then show ?case using 1 
  proof cases
    case c1
    have "(GOTO_Prog_to_WHILE_IF' prog min_pc, s) \<Rightarrow>\<^bsup> i + 5 \<^esup> t" using if_neq_trans_ins_2_out_eq "1.prems"(3) "1.prems"(5) assms(4) c1 by auto
    thus ?thesis using c1 by auto
  next
    case c2
    thm if_neq_trans_ins_2_out_gt
    have "(GOTO_Prog_to_WHILE_IF' prog (Suc min_pc), s) \<Rightarrow>\<^bsup> i + (pc + 1 - Suc min_pc) * 5 \<^esup> t" using "1.IH" "1.prems"(3) "1.prems"(5) assms(4) c2 by linarith
    hence "(GOTO_Prog_to_WHILE_IF' prog min_pc, s) \<Rightarrow>\<^bsup> i + (pc - min_pc) * 5 + 5 \<^esup> t" using if_neq_trans_ins_2_out_gt assms(4) c2 by force
    hence "(GOTO_Prog_to_WHILE_IF' prog min_pc, s) \<Rightarrow>\<^bsup> i + (pc + 1 - min_pc) * 5 \<^esup> t" by (metis "1.prems"(2) Suc_diff_le add.commute group_cancel.add1 mult_Suc plus_1_eq_Suc)
    thus ?thesis by simp
  qed
qed

lemma GOTO_Prog_to_WHILE_IF_correctness_complexity:
  assumes "1 \<le> s ''pc''" and "s ''pc'' \<le> length prog"
    and "(GOTO_Instr_to_WHILE (prog !! s ''pc''), s) \<Rightarrow>\<^bsup> i \<^esup> t"
  shows "(GOTO_Prog_to_WHILE_IF prog, s) \<Rightarrow>\<^bsup> i + s ''pc'' * 5 \<^esup> t" using assms
  by (metis GOTO_Prog_to_WHILE_IF'_correctness_complexity GOTO_Prog_to_WHILE_IF_def add.commute diff_Suc_1 less_or_eq_imp_le plus_1_eq_Suc)

lemma GOTO_Prog_to_WHILE_IF_correctness_complexity':
  assumes "1 \<le> s ''pc''" and "s ''pc'' \<le> length prog"
    and "\<exists>t. (GOTO_Instr_to_WHILE (prog !! s ''pc''), s) \<Rightarrow>\<^bsup> i \<^esup> t"
  shows "\<exists>t. (GOTO_Prog_to_WHILE_IF prog, s) \<Rightarrow>\<^bsup> i + s ''pc'' * 5 \<^esup> t" using assms
  using GOTO_Prog_to_WHILE_IF_correctness_complexity by blast

definition GOTO_Prog_to_WHILE :: "GOTO_Prog \<Rightarrow> com" where
  "GOTO_Prog_to_WHILE prog = ''pc'' ::= A (atomExp.N 1) ;; WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF prog"

(*reversed version necessary !!! *)
lemma GOTO_Prog_to_WHILE_IF'_correctness_complexity_reversed:
  assumes "1 \<le> min_pc" and "min_pc \<le> pc" and "pc \<le> length prog" and "s ''pc'' = pc"
    and "(GOTO_Prog_to_WHILE_IF' prog min_pc, s) \<Rightarrow>\<^bsup> i + (pc + 1 - min_pc) * 5 \<^esup> t"
  shows "(GOTO_Instr_to_WHILE (prog !! pc), s) \<Rightarrow>\<^bsup> i \<^esup> t" using assms
proof (induction prog min_pc arbitrary: rule: GOTO_Prog_to_WHILE_IF'.induct)
  case (1 prog min_pc)
  consider (c1) "min_pc = pc" | (c2) "min_pc < pc" using "1.prems"(2) by linarith
  then show ?case using 1
  proof cases
    case c1
    have "(GOTO_Instr_to_WHILE (prog !! pc), s) \<Rightarrow>\<^bsup> i \<^esup> t"
      by (metis "1.prems"(3) "1.prems"(5) GOTO_Prog_to_WHILE_IF'.elims add_diff_cancel_left' assms(4) c1 if_neq_trans_out_2_ins_eq lambda_one verit_comp_simplify1(3))
    thus ?thesis using 1 c1 by simp
  next
    case c2
    thm if_neq_trans_out_2_ins_gt
    show ?thesis using c2 1 if_neq_trans_out_2_ins_gt
      by (smt (verit, ccfv_threshold) GOTO_Prog_to_WHILE_IF'.elims Suc_diff_le Suc_eq_plus1 add.commute add.left_commute add_diff_cancel_right' diff_diff_left less_eq_Suc_le mult_Suc nat_less_le not_less_eq_eq order_less_le_trans)
  qed
qed

lemma GOTO_Prog_to_WHILE_IF_correctness_complexity_reversed:
  assumes "1 \<le> s ''pc''" and "s ''pc'' \<le> length prog"
    and "(GOTO_Prog_to_WHILE_IF prog, s) \<Rightarrow>\<^bsup> i + s ''pc'' * 5 \<^esup> t"
  shows "(GOTO_Instr_to_WHILE (prog !! s ''pc''), s) \<Rightarrow>\<^bsup> i \<^esup> t" using assms
  by (metis GOTO_Prog_to_WHILE_IF'_correctness_complexity_reversed GOTO_Prog_to_WHILE_IF_def add.commute add_diff_cancel_left' le_refl)

definition well_defined_prog :: "GOTO_Prog \<Rightarrow> bool" where
  "well_defined_prog prog = (length prog \<ge> 1 \<and> (\<forall>i. (1 \<le> i \<and> i \<le> length prog) \<longrightarrow> (
    well_defined_instr (prog !! i) \<and> 
    (case prog !! i of GOTO j \<Rightarrow> j \<le> length prog | IF x\<noteq>0 THEN GOTO j \<Rightarrow> j \<le> length prog | _ \<Rightarrow> True) \<and> 
    prog !! (length prog) = HALT)
  ))"

lemma well_defined_prog_pc_range:
  assumes "prog \<turnstile> (pc, s) \<rightarrow>\<^bsup> k \<^esup> (pc', t)"
    and "well_defined_prog prog"
    and "1 \<le> pc \<and> pc \<le> length prog"
  shows "0 \<le> pc' \<and> pc' \<le> length prog" using assms
proof (induct prog pc s k pc' t rule: exec_t_induct)
  case (step0 P s)
  then show ?case by simp
next
  case (step1 P pc\<^sub>1 s\<^sub>1 pc\<^sub>2 s\<^sub>2 x pc\<^sub>3 s\<^sub>3)
  have expand: "iexec (P !! pc\<^sub>1) (pc\<^sub>1, s\<^sub>1) = (pc\<^sub>2, s\<^sub>2)" using step1.hyps(1) exec1_def by auto
  show ?case
  proof (cases "P !! pc\<^sub>1")
    case HALT
    have "pc\<^sub>2 = 0" using HALT expand by auto
    thus ?thesis using step1 HALT by blast
  next
    case (ASSIGN v op)
    have "pc\<^sub>2 = pc\<^sub>1 + 1" using ASSIGN expand by auto
    thus ?thesis using step1 ASSIGN
      by (metis Suc_eq_plus1 instr.distinct(2) le_neq_implies_less less_eq_Suc_le trans_le_add1 well_defined_prog_def)
  next
    case (ADD v op)
    have "pc\<^sub>2 = pc\<^sub>1 + 1" using ADD expand by auto
    thus ?thesis using step1 ADD
      by (metis Suc_eq_plus1 instr.distinct(4) le_neq_implies_less less_eq_Suc_le trans_le_add1 well_defined_prog_def)
  next
    case (SUB v op)
    have "pc\<^sub>2 = pc\<^sub>1 + 1" using SUB expand by auto
    thus ?thesis using step1 SUB
      by (metis Suc_eq_plus1 instr.distinct(6) le_neq_implies_less less_eq_Suc_le trans_le_add1 well_defined_prog_def)
  next
    case (RSH v)
    have "pc\<^sub>2 = pc\<^sub>1 + 1" using RSH expand by auto
    thus ?thesis using step1 RSH
      using less_eq_Suc_le well_defined_prog_def by fastforce
  next
    case (MOD v)
    have "pc\<^sub>2 = pc\<^sub>1 + 1" using MOD expand by auto
    thus ?thesis using step1 MOD
      using less_eq_Suc_le well_defined_prog_def by fastforce
  next
    case (JMP i)
    have "pc\<^sub>2 = i" using JMP expand by auto
    have "i > 0" using step1.hyps(2) \<open>pc\<^sub>2 = i\<close> by fastforce
    have "case P !! i of GOTO j \<Rightarrow> j \<le> length P | IF x\<noteq>0 THEN GOTO j \<Rightarrow> j \<le> length P | _ \<Rightarrow> True"
      by (metis step1.prems(1) step1.prems(2) JMP One_nat_def \<open>0 < i\<close> instr.simps(70) less_eq_Suc_le well_defined_prog_def)
    hence "i \<le> length P" using step1.prems(1) step1.prems(2) JMP well_defined_prog_def by auto
    thus ?thesis using step1.hyps(2) step1.hyps(4) step1.prems(1) \<open>pc\<^sub>2 = i\<close> by force
  next
    case (CONDJMP v i)
    consider (c1) "s\<^sub>1 v = 0" | (c2) "s\<^sub>1 v > 0" by blast
    then show ?thesis
    proof cases
      case c1
      have "pc\<^sub>2 = pc\<^sub>1 + 1" using CONDJMP expand c1 by auto
      thus ?thesis using CONDJMP step1 c1
        by (smt (verit) Suc_eq_plus1 instr.case(1) instr.case(8) less_Suc_eq_le less_or_eq_imp_le linorder_le_less_linear order_antisym well_defined_prog_def)
    next
      case c2
      have "pc\<^sub>2 = i" using CONDJMP expand c2 by auto
      have "i > 0" using step1.hyps(2) \<open>pc\<^sub>2 = i\<close> by fastforce
      have "case P !! i of GOTO j \<Rightarrow> j \<le> length P | IF x\<noteq>0 THEN GOTO j \<Rightarrow> j \<le> length P | _ \<Rightarrow> True"
        by (metis step1.prems(1) step1.prems(2) CONDJMP One_nat_def \<open>0 < i\<close> instr.simps(71) less_eq_Suc_le well_defined_prog_def)
      hence "i \<le> length P" using step1.prems(1) step1.prems(2) CONDJMP well_defined_prog_def by auto
      thus ?thesis using step1.hyps(4) step1.prems(1) \<open>0 < i\<close> \<open>pc\<^sub>2 = i\<close> by fastforce
    qed
  qed
qed

lemma well_defined_prog_pc_range_single:
  assumes "prog \<turnstile> (pc, s) \<rightarrow> (pc', t)"
    and "well_defined_prog prog"
    and "1 \<le> pc \<and> pc \<le> length prog"
  shows "0 \<le> pc' \<and> pc' \<le> length prog" using assms sorry

lemma prog_if_pc_consist:
  assumes "prog \<turnstile> (pc, s') \<rightarrow> (pc', t')"
    and "1 \<le> pc" and "pc \<le> length prog"
    and "well_defined_prog prog"
    and "(GOTO_Prog_to_WHILE_IF prog, s) \<Rightarrow>\<^bsup> i + s ''pc'' * 5 \<^esup> t"
    and "s ''pc'' = pc" and "\<forall>x \<noteq> ''pc''. s x = s' x"
  shows "t ''pc'' = pc'" using assms
proof -
  have pre2: "(GOTO_Instr_to_WHILE (prog !! s ''pc''), s) \<Rightarrow>\<^bsup> i \<^esup> t"
    using GOTO_Prog_to_WHILE_IF_correctness_complexity_reversed assms(2) assms(3) assms(5) assms(6) by blast
  have pre1: "well_defined_instr (prog !! s ''pc'')" using assms(2) assms(3) assms(4) assms(6) well_defined_prog_def by blast
  have pre3: "iexec (prog !! s ''pc'') (pc, s') = (pc', t')" using assms(1) assms(6) exec1_def by auto
  thus "t ''pc'' = pc'" using pre1 pre2 pre3 assms by (simp add: instr_pc_consist)
qed

lemma prog_if_var_consist:
  assumes "prog \<turnstile> (pc, s') \<rightarrow> (pc', t')"
    and "1 \<le> pc" and "pc \<le> length prog"
    and "well_defined_prog prog"
    and "(GOTO_Prog_to_WHILE_IF prog, s) \<Rightarrow>\<^bsup> i + s ''pc'' * 5 \<^esup> t"
    and "s ''pc'' = pc" and "\<forall>x \<noteq> ''pc''. s x = s' x"
  shows "\<forall>z \<noteq> ''pc''. t z = t' z" using assms
proof -
  have pre2: "(GOTO_Instr_to_WHILE (prog !! s ''pc''), s) \<Rightarrow>\<^bsup> i \<^esup> t"
    using GOTO_Prog_to_WHILE_IF_correctness_complexity_reversed assms(2) assms(3) assms(5) assms(6) by blast
  have pre1: "well_defined_instr (prog !! s ''pc'')" using assms(2) assms(3) assms(4) assms(6) well_defined_prog_def by blast
  have pre3: "iexec (prog !! s ''pc'') (pc, s') = (pc', t')" using assms(1) assms(6) exec1_def by auto
  thus "\<forall>z \<noteq> ''pc''. t z = t' z" using pre1 pre2 pre3 assms by (simp add: instr_var_consist)
qed

fun WHILE_complexity :: "GOTO_Prog \<Rightarrow> config \<Rightarrow> nat \<Rightarrow> nat" where
  "WHILE_complexity _ _ 0 = 0" | 
  "WHILE_complexity prog (pc, s) (Suc step) = WHILE_complexity prog (iexec (prog !! pc) (pc, s)) step + 5 * pc + 1 + 
    (case (prog !! pc) of 
      HALT \<Rightarrow> 2 |
      x ;;= t \<Rightarrow> 4 |
      x += t \<Rightarrow> 4 | 
      x -= t \<Rightarrow> 4 | 
      x \<bind>1 \<Rightarrow> 4 |
      x %=2 \<Rightarrow> 4 |
      GOTO i \<Rightarrow> 2 | 
      IF x\<noteq>0 THEN GOTO i \<Rightarrow> 3
    )"

lemma "(com1;;com2, s1) \<Rightarrow>\<^bsup> c \<^esup> s3 \<Longrightarrow> (com1, s1) \<Rightarrow>\<^bsup> c1 \<^esup> s2 \<Longrightarrow> (com2, s2) \<Rightarrow>\<^bsup> c - c1 \<^esup> s3"
  using bigstep_det by fastforce

lemma "(WHILE b \<noteq>0 DO c, s1) \<Rightarrow>\<^bsup> z \<^esup> s3 \<Longrightarrow> s1 b \<noteq> 0 \<Longrightarrow> (c,s1) \<Rightarrow>\<^bsup> x \<^esup> s2 \<Longrightarrow> (WHILE b \<noteq>0 DO c, s2) \<Rightarrow>\<^bsup> z - x - 1 \<^esup> s3"
  by (smt (verit) One_nat_def While_tE_time add.commute add_0 add_diff_cancel_left' bigstep_det diff_Suc_Suc diff_diff_eq)

lemma prog_pc_consist:
  assumes "prog \<turnstile> (pc, s') \<rightarrow>\<^bsup> k \<^esup> (pc', t')"
    and "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF prog, s) \<Rightarrow>\<^bsup> (WHILE_complexity prog (pc, s') k) \<^esup> t"
    and "1 \<le> pc" and "pc \<le> length prog"
    and "well_defined_prog prog"
    and "s ''pc'' = pc" and "\<forall>x \<noteq> ''pc''. s x = s' x"
  shows "t ''pc'' = pc'" using assms 
proof (induction prog pc s' k pc' t' arbitrary: s t rule: exec_t_induct)
  case (step0 P pc s)
  then show ?case by auto 
next
  case (step1 P pc\<^sub>1 s\<^sub>1 pc\<^sub>2 s\<^sub>2 step pc\<^sub>3 s\<^sub>3)
  have aux1: "1 \<le> pc\<^sub>2 \<and> pc\<^sub>2 \<le> length P" using step1.hyps step1.prems well_defined_prog_pc_range_single by auto
  have aux2: "iexec (P !! pc\<^sub>1) (pc\<^sub>1, s\<^sub>1) = (pc\<^sub>2, s\<^sub>2)" using step1.hyps(1) exec1_def by auto
  let ?var = "(case (P !! pc\<^sub>1) of HALT \<Rightarrow> 2 | x ;;= t \<Rightarrow> 4 | x += t \<Rightarrow> 4 | x -= t \<Rightarrow> 4 | 
      x \<bind>1 \<Rightarrow> 4 | x %=2 \<Rightarrow> 4 | GOTO i \<Rightarrow> 2 | IF x\<noteq>0 THEN GOTO i \<Rightarrow> 3)"
  have aux3: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step + 5 * pc\<^sub>1 + ?var + 1 \<^esup> t" 
    using aux2 step1.prems(1) by auto
  show ?case using step1
  proof (cases "P !! pc\<^sub>1")
    case HALT
    have "\<exists>s'. (GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 2 \<^esup> s'" using step1.hyps(2) HALT aux2 by auto
    then obtain s' where aux_i: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 2 \<^esup> s'" by blast
    hence aux4: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" 
      using step1.hyps(2) HALT aux2 by auto 
    have "s' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s' x = s\<^sub>2 x)"
      using step1.hyps(2) HALT aux2 by auto
    thus ?thesis using HALT step1 using aux2 by fastforce
  next
    case (ASSIGN x c)
    have aux5: "\<exists>s'. (GOTO_Instr_to_WHILE (x ;;= c), s) \<Rightarrow>\<^bsup> 4 \<^esup> s'" using instr_assign_complexity by auto
    hence aux6: "\<exists>s'. (GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 4 \<^esup> s'" using GOTO_Prog_to_WHILE_IF_correctness_complexity' by (metis step1.prems(2) step1.prems(3) step1.prems(5) ASSIGN add.commute mult.commute)
    then obtain s' where aux_i: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 4 \<^esup> s'" by blast
    hence aux4: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" by (smt (verit) step1.prems(2) step1.prems(5) ASSIGN One_nat_def While_tE_time aux3 add.commute add_diff_cancel_right' bigstepT_the_cost bigstepT_the_state diff_diff_left instr.simps(65) le_zero_eq not_less_eq_eq plus_1_eq_Suc)
    have "s' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s' x = s\<^sub>2 x)" by (smt (verit, ccfv_SIG) step1(1) step1(10) step1(7) step1(8) step1(9) step1.prems(2) ASSIGN GOTO_Prog_to_WHILE_IF_correctness_complexity aux5 aux_i bigstepT_the_cost prog_if_pc_consist prog_if_var_consist)
    thus ?thesis using ASSIGN step1 aux1 aux4 by presburger
  next
    case (ADD x c)
    have aux5: "\<exists>s'. (GOTO_Instr_to_WHILE (x += c), s) \<Rightarrow>\<^bsup> 4 \<^esup> s'" using instr_add_complexity by auto
    hence aux6: "\<exists>s'. (GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 4 \<^esup> s'" using GOTO_Prog_to_WHILE_IF_correctness_complexity' by (metis step1.prems(2) step1.prems(3) step1.prems(5) ADD add.commute mult.commute)
    then obtain s' where aux_i: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 4 \<^esup> s'" by blast
    hence aux4: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" by (smt (verit, ccfv_threshold) step1.prems(2) step1.prems(5) ADD One_nat_def While_tE_time add.commute add_diff_cancel_left' aux3 bigstepT_the_cost bigstepT_the_state diff_diff_left instr.simps(66) le_zero_eq not_less_eq_eq plus_1_eq_Suc)
    have "s' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s' x = s\<^sub>2 x)" by (smt (verit, ccfv_SIG) step1(1) step1(10) step1(7) step1(8) step1(9) step1.prems(2) ADD GOTO_Prog_to_WHILE_IF_correctness_complexity aux5 aux_i bigstepT_the_cost prog_if_pc_consist prog_if_var_consist)
    thus ?thesis using ADD step1 aux1 aux4 by presburger
  next
    case (SUB x c)
    have aux5: "\<exists>s'. (GOTO_Instr_to_WHILE (x -= c), s) \<Rightarrow>\<^bsup> 4 \<^esup> s'" using instr_sub_complexity by auto
    hence aux6: "\<exists>s'. (GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 4 \<^esup> s'" using GOTO_Prog_to_WHILE_IF_correctness_complexity' by (metis step1.prems(2) step1.prems(3) step1.prems(5) SUB add.commute mult.commute)
    then obtain s' where aux_i: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 4 \<^esup> s'" by blast
    hence aux4: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" by (smt (verit, ccfv_threshold) step1.prems(2) step1.prems(5) One_nat_def SUB While_tE_time add.commute add_diff_cancel_left' aux3 bigstepT_the_cost bigstepT_the_state diff_diff_left instr.simps(67) le_zero_eq not_less_eq_eq plus_1_eq_Suc)
    have "s' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s' x = s\<^sub>2 x)" by (smt (verit, ccfv_SIG) step1(1) step1(10) step1(7) step1(8) step1(9) step1.prems(2) SUB GOTO_Prog_to_WHILE_IF_correctness_complexity aux5 aux_i bigstepT_the_cost prog_if_pc_consist prog_if_var_consist)
    thus ?thesis using SUB step1 aux1 aux4 by presburger
  next
    case (RSH x)
    have aux5: "\<exists>s'. (GOTO_Instr_to_WHILE (x \<bind>1), s) \<Rightarrow>\<^bsup> 4 \<^esup> s'" using instr_right_shift_complexity by auto
    hence aux6: "\<exists>s'. (GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 4 \<^esup> s'" using GOTO_Prog_to_WHILE_IF_correctness_complexity' by (metis step1.prems(2) step1.prems(3) step1.prems(5) RSH add.commute mult.commute)
    then obtain s' where aux_i: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 4 \<^esup> s'" by blast
    hence aux4: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" by (smt (verit, del_insts) step1.prems(2) step1.prems(5) One_nat_def RSH While_tE_time add.commute add_diff_cancel_right' aux3 bigstepT_the_cost bigstepT_the_state diff_diff_left instr.simps(68) le_zero_eq not_less_eq_eq plus_1_eq_Suc)
    have "s' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s' x = s\<^sub>2 x)" by (smt (verit, ccfv_SIG) step1(1) step1(10) step1(7) step1(8) step1(9) step1.prems(2) RSH GOTO_Prog_to_WHILE_IF_correctness_complexity aux5 aux_i bigstepT_the_cost prog_if_pc_consist prog_if_var_consist)
    thus ?thesis using RSH step1 aux1 aux4 by presburger
  next
    case (MOD x)
    have aux5: "\<exists>s'. (GOTO_Instr_to_WHILE (x %=2), s) \<Rightarrow>\<^bsup> 4 \<^esup> s'" using instr_right_shift_complexity by auto
    hence aux6: "\<exists>s'. (GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 4 \<^esup> s'" using GOTO_Prog_to_WHILE_IF_correctness_complexity' by (metis step1.prems(2) step1.prems(3) step1.prems(5) MOD add.commute mult.commute)
    then obtain s' where aux_i: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 4 \<^esup> s'" by blast
    hence aux4: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" by (smt (verit, ccfv_SIG) step1.prems(2) step1.prems(5) MOD One_nat_def While_tE_time add.commute add_diff_cancel_left' aux3 bigstepT_the_cost bigstepT_the_state diff_diff_left instr.simps(69) le_zero_eq not_less_eq_eq plus_1_eq_Suc)
    have "s' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s' x = s\<^sub>2 x)" by (smt (verit, ccfv_SIG) step1(1) step1(10) step1(7) step1(8) step1(9) step1.prems(2) MOD GOTO_Prog_to_WHILE_IF_correctness_complexity aux5 aux_i bigstepT_the_cost prog_if_pc_consist prog_if_var_consist)
    thus ?thesis using MOD step1 aux1 aux4 by presburger
  next
    case (JMP i)
    have aux5: "\<exists>s'. (GOTO_Instr_to_WHILE (GOTO i), s) \<Rightarrow>\<^bsup> 2 \<^esup> s'" using instr_jump_complexity by auto
    hence aux6: "\<exists>s'. (GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 2 \<^esup> s'" using GOTO_Prog_to_WHILE_IF_correctness_complexity' by (metis step1.prems(2) step1.prems(3) step1.prems(5) JMP add.commute mult.commute)
    then obtain s' where aux_i: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 2 \<^esup> s'" by blast
    hence aux4: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" by (smt (verit, del_insts) step1.prems(2) step1.prems(5) JMP One_nat_def While_tE_time add.commute add_diff_cancel_right' aux3 bigstepT_the_cost bigstepT_the_state diff_diff_left instr.simps(70) le_zero_eq not_less_eq_eq plus_1_eq_Suc)
    have "s' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s' x = s\<^sub>2 x)" by (smt (verit, ccfv_SIG) step1(1) step1(10) step1(7) step1(8) step1(9) step1.prems(2) JMP GOTO_Prog_to_WHILE_IF_correctness_complexity aux5 aux_i bigstepT_the_cost prog_if_pc_consist prog_if_var_consist)
    thus ?thesis using JMP step1 aux1 aux4 by presburger
  next
    case (CONDJMP x i)
    have aux5: "\<exists>s'. (GOTO_Instr_to_WHILE (IF x\<noteq>0 THEN GOTO i), s) \<Rightarrow>\<^bsup> 3 \<^esup> s'" using instr_cond_jump_complexity by auto
    hence aux6: "\<exists>s'. (GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 3 \<^esup> s'" using GOTO_Prog_to_WHILE_IF_correctness_complexity' by (metis step1.prems(2) step1.prems(3) step1.prems(5) CONDJMP add.commute mult.commute)
    then obtain s' where aux_i: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 3 \<^esup> s'" by blast
    hence aux4: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" by (smt (verit) step1.prems(2) step1.prems(5) CONDJMP One_nat_def While_tE_time add.commute add_diff_cancel_left' aux3 bigstepT_the_cost bigstepT_the_state diff_diff_left instr.simps(71) le_zero_eq not_less_eq_eq plus_1_eq_Suc)
    have "s' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s' x = s\<^sub>2 x)" by (smt (verit, ccfv_SIG) step1(1) step1(10) step1(7) step1(8) step1(9) step1.prems(2) CONDJMP GOTO_Prog_to_WHILE_IF_correctness_complexity aux5 aux_i bigstepT_the_cost prog_if_pc_consist prog_if_var_consist)
    thus ?thesis using CONDJMP step1 aux1 aux4 by presburger
  qed
qed

lemma prog_var_consist:
  assumes "prog \<turnstile> (pc, s') \<rightarrow>\<^bsup> k \<^esup> (pc', t')"
    and "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF prog, s) \<Rightarrow>\<^bsup> (WHILE_complexity prog (pc, s') k) \<^esup> t"
    and "1 \<le> pc" and "pc \<le> length prog"
    and "well_defined_prog prog"
    and "s ''pc'' = pc" and "\<forall>x \<noteq> ''pc''. s x = s' x"
  shows "\<forall>x \<noteq> ''pc''. t x = t' x" using assms 
proof (induction prog pc s' k pc' t' arbitrary: s t rule: exec_t_induct)
  case (step0 P pc s)
  then show ?case by auto 
next
  case (step1 P pc\<^sub>1 s\<^sub>1 pc\<^sub>2 s\<^sub>2 step pc\<^sub>3 s\<^sub>3)
  have aux1: "1 \<le> pc\<^sub>2 \<and> pc\<^sub>2 \<le> length P" using step1.hyps step1.prems well_defined_prog_pc_range_single by auto
  have aux2: "iexec (P !! pc\<^sub>1) (pc\<^sub>1, s\<^sub>1) = (pc\<^sub>2, s\<^sub>2)" using step1.hyps(1) exec1_def by auto
  let ?var = "(case (P !! pc\<^sub>1) of HALT \<Rightarrow> 2 | x ;;= t \<Rightarrow> 4 | x += t \<Rightarrow> 4 | x -= t \<Rightarrow> 4 | 
      x \<bind>1 \<Rightarrow> 4 | x %=2 \<Rightarrow> 4 | GOTO i \<Rightarrow> 2 | IF x\<noteq>0 THEN GOTO i \<Rightarrow> 3)"
  have aux3: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step + 5 * pc\<^sub>1 + ?var + 1 \<^esup> t" 
    using aux2 step1.prems(1) by auto
  show ?case using step1
  proof (cases "P !! pc\<^sub>1")
    case HALT
    have "\<exists>s'. (GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 2 \<^esup> s'" using step1.hyps(2) HALT aux2 by auto
    then obtain s' where aux_i: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 2 \<^esup> s'" by blast
    hence aux4: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" 
      using step1.hyps(2) HALT aux2 by auto 
    have "s' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s' x = s\<^sub>2 x)"
      using step1.hyps(2) HALT aux2 by auto
    thus ?thesis using HALT step1 using aux2 by fastforce
  next
    case (ASSIGN x c)
    have aux5: "\<exists>s'. (GOTO_Instr_to_WHILE (x ;;= c), s) \<Rightarrow>\<^bsup> 4 \<^esup> s'" using instr_assign_complexity by auto
    hence aux6: "\<exists>s'. (GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 4 \<^esup> s'" using GOTO_Prog_to_WHILE_IF_correctness_complexity' by (metis step1.prems(2) step1.prems(3) step1.prems(5) ASSIGN add.commute mult.commute)
    then obtain s' where aux_i: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 4 \<^esup> s'" by blast
    hence aux4: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" by (smt (verit) step1.prems(2) step1.prems(5) ASSIGN One_nat_def While_tE_time aux3 add.commute add_diff_cancel_right' bigstepT_the_cost bigstepT_the_state diff_diff_left instr.simps(65) le_zero_eq not_less_eq_eq plus_1_eq_Suc)
    have "s' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s' x = s\<^sub>2 x)" by (smt (verit, ccfv_SIG) step1(1) step1(10) step1(7) step1(8) step1(9) step1.prems(2) ASSIGN GOTO_Prog_to_WHILE_IF_correctness_complexity aux5 aux_i bigstepT_the_cost prog_if_pc_consist prog_if_var_consist)
    thus ?thesis using ASSIGN step1 aux1 aux4 by presburger
  next
    case (ADD x c)
    have aux5: "\<exists>s'. (GOTO_Instr_to_WHILE (x += c), s) \<Rightarrow>\<^bsup> 4 \<^esup> s'" using instr_add_complexity by auto
    hence aux6: "\<exists>s'. (GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 4 \<^esup> s'" using GOTO_Prog_to_WHILE_IF_correctness_complexity' by (metis step1.prems(2) step1.prems(3) step1.prems(5) ADD add.commute mult.commute)
    then obtain s' where aux_i: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 4 \<^esup> s'" by blast
    hence aux4: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" by (smt (verit, ccfv_threshold) step1.prems(2) step1.prems(5) ADD One_nat_def While_tE_time add.commute add_diff_cancel_left' aux3 bigstepT_the_cost bigstepT_the_state diff_diff_left instr.simps(66) le_zero_eq not_less_eq_eq plus_1_eq_Suc)
    have "s' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s' x = s\<^sub>2 x)" by (smt (verit, ccfv_SIG) step1(1) step1(10) step1(7) step1(8) step1(9) step1.prems(2) ADD GOTO_Prog_to_WHILE_IF_correctness_complexity aux5 aux_i bigstepT_the_cost prog_if_pc_consist prog_if_var_consist)
    thus ?thesis using ADD step1 aux1 aux4 by presburger
  next
    case (SUB x c)
    have aux5: "\<exists>s'. (GOTO_Instr_to_WHILE (x -= c), s) \<Rightarrow>\<^bsup> 4 \<^esup> s'" using instr_sub_complexity by auto
    hence aux6: "\<exists>s'. (GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 4 \<^esup> s'" using GOTO_Prog_to_WHILE_IF_correctness_complexity' by (metis step1.prems(2) step1.prems(3) step1.prems(5) SUB add.commute mult.commute)
    then obtain s' where aux_i: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 4 \<^esup> s'" by blast
    hence aux4: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" by (smt (verit, ccfv_threshold) step1.prems(2) step1.prems(5) One_nat_def SUB While_tE_time add.commute add_diff_cancel_left' aux3 bigstepT_the_cost bigstepT_the_state diff_diff_left instr.simps(67) le_zero_eq not_less_eq_eq plus_1_eq_Suc)
    have "s' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s' x = s\<^sub>2 x)" by (smt (verit, ccfv_SIG) step1(1) step1(10) step1(7) step1(8) step1(9) step1.prems(2) SUB GOTO_Prog_to_WHILE_IF_correctness_complexity aux5 aux_i bigstepT_the_cost prog_if_pc_consist prog_if_var_consist)
    thus ?thesis using SUB step1 aux1 aux4 by presburger
  next
    case (RSH x)
    have aux5: "\<exists>s'. (GOTO_Instr_to_WHILE (x \<bind>1), s) \<Rightarrow>\<^bsup> 4 \<^esup> s'" using instr_right_shift_complexity by auto
    hence aux6: "\<exists>s'. (GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 4 \<^esup> s'" using GOTO_Prog_to_WHILE_IF_correctness_complexity' by (metis step1.prems(2) step1.prems(3) step1.prems(5) RSH add.commute mult.commute)
    then obtain s' where aux_i: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 4 \<^esup> s'" by blast
    hence aux4: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" by (smt (verit, del_insts) step1.prems(2) step1.prems(5) One_nat_def RSH While_tE_time add.commute add_diff_cancel_right' aux3 bigstepT_the_cost bigstepT_the_state diff_diff_left instr.simps(68) le_zero_eq not_less_eq_eq plus_1_eq_Suc)
    have "s' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s' x = s\<^sub>2 x)" by (smt (verit, ccfv_SIG) step1(1) step1(10) step1(7) step1(8) step1(9) step1.prems(2) RSH GOTO_Prog_to_WHILE_IF_correctness_complexity aux5 aux_i bigstepT_the_cost prog_if_pc_consist prog_if_var_consist)
    thus ?thesis using RSH step1 aux1 aux4 by presburger
  next
    case (MOD x)
    have aux5: "\<exists>s'. (GOTO_Instr_to_WHILE (x %=2), s) \<Rightarrow>\<^bsup> 4 \<^esup> s'" using instr_right_shift_complexity by auto
    hence aux6: "\<exists>s'. (GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 4 \<^esup> s'" using GOTO_Prog_to_WHILE_IF_correctness_complexity' by (metis step1.prems(2) step1.prems(3) step1.prems(5) MOD add.commute mult.commute)
    then obtain s' where aux_i: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 4 \<^esup> s'" by blast
    hence aux4: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" by (smt (verit, ccfv_SIG) step1.prems(2) step1.prems(5) MOD One_nat_def While_tE_time add.commute add_diff_cancel_left' aux3 bigstepT_the_cost bigstepT_the_state diff_diff_left instr.simps(69) le_zero_eq not_less_eq_eq plus_1_eq_Suc)
    have "s' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s' x = s\<^sub>2 x)" by (smt (verit, ccfv_SIG) step1(1) step1(10) step1(7) step1(8) step1(9) step1.prems(2) MOD GOTO_Prog_to_WHILE_IF_correctness_complexity aux5 aux_i bigstepT_the_cost prog_if_pc_consist prog_if_var_consist)
    thus ?thesis using MOD step1 aux1 aux4 by presburger
  next
    case (JMP i)
    have aux5: "\<exists>s'. (GOTO_Instr_to_WHILE (GOTO i), s) \<Rightarrow>\<^bsup> 2 \<^esup> s'" using instr_jump_complexity by auto
    hence aux6: "\<exists>s'. (GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 2 \<^esup> s'" using GOTO_Prog_to_WHILE_IF_correctness_complexity' by (metis step1.prems(2) step1.prems(3) step1.prems(5) JMP add.commute mult.commute)
    then obtain s' where aux_i: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 2 \<^esup> s'" by blast
    hence aux4: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" by (smt (verit, del_insts) step1.prems(2) step1.prems(5) JMP One_nat_def While_tE_time add.commute add_diff_cancel_right' aux3 bigstepT_the_cost bigstepT_the_state diff_diff_left instr.simps(70) le_zero_eq not_less_eq_eq plus_1_eq_Suc)
    have "s' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s' x = s\<^sub>2 x)" by (smt (verit, ccfv_SIG) step1(1) step1(10) step1(7) step1(8) step1(9) step1.prems(2) JMP GOTO_Prog_to_WHILE_IF_correctness_complexity aux5 aux_i bigstepT_the_cost prog_if_pc_consist prog_if_var_consist)
    thus ?thesis using JMP step1 aux1 aux4 by presburger
  next
    case (CONDJMP x i)
    have aux5: "\<exists>s'. (GOTO_Instr_to_WHILE (IF x\<noteq>0 THEN GOTO i), s) \<Rightarrow>\<^bsup> 3 \<^esup> s'" using instr_cond_jump_complexity by auto
    hence aux6: "\<exists>s'. (GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 3 \<^esup> s'" using GOTO_Prog_to_WHILE_IF_correctness_complexity' by (metis step1.prems(2) step1.prems(3) step1.prems(5) CONDJMP add.commute mult.commute)
    then obtain s' where aux_i: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 5 * pc\<^sub>1 + 3 \<^esup> s'" by blast
    hence aux4: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" by (smt (verit) step1.prems(2) step1.prems(5) CONDJMP One_nat_def While_tE_time add.commute add_diff_cancel_left' aux3 bigstepT_the_cost bigstepT_the_state diff_diff_left instr.simps(71) le_zero_eq not_less_eq_eq plus_1_eq_Suc)
    have "s' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s' x = s\<^sub>2 x)" by (smt (verit, ccfv_SIG) step1(1) step1(10) step1(7) step1(8) step1(9) step1.prems(2) CONDJMP GOTO_Prog_to_WHILE_IF_correctness_complexity aux5 aux_i bigstepT_the_cost prog_if_pc_consist prog_if_var_consist)
    thus ?thesis using CONDJMP step1 aux1 aux4 by presburger
  qed
qed

lemma prog_complexity:
  assumes "prog \<turnstile> (pc, s') \<rightarrow>\<^bsup> k \<^esup> (pc', t')"
    and "1 \<le> pc" and "pc \<le> length prog"
    and "well_defined_prog prog"
    and "s ''pc'' = pc" and "\<forall>x \<noteq> ''pc''. s x = s' x"
  shows "\<exists>t. (WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF prog, s) \<Rightarrow>\<^bsup> (WHILE_complexity prog (pc, s') k) \<^esup> t" using assms
proof (induction prog pc s' k pc' t' arbitrary: s rule: exec_t_induct)
  case (step0 P s1)
  then show ?case by simp
next
  case (step1 P pc\<^sub>1 s\<^sub>1 pc\<^sub>2 s\<^sub>2 step pc\<^sub>3 s\<^sub>3)
  have aux1: "1 \<le> pc\<^sub>2 \<and> pc\<^sub>2 \<le> length P" using step1.hyps step1.prems well_defined_prog_pc_range_single by auto
  have aux2: "iexec (P !! pc\<^sub>1) (pc\<^sub>1, s\<^sub>1) = (pc\<^sub>2, s\<^sub>2)" using step1.hyps(1) exec1_def by auto
  let ?var = "(case (P !! pc\<^sub>1) of HALT \<Rightarrow> 2 | x ;;= t \<Rightarrow> 4 | x += t \<Rightarrow> 4 | x -= t \<Rightarrow> 4 | 
      x \<bind>1 \<Rightarrow> 4 | x %=2 \<Rightarrow> 4 | GOTO i \<Rightarrow> 2 | IF x\<noteq>0 THEN GOTO i \<Rightarrow> 3)"
  show ?case using step1
  proof (cases "P !! pc\<^sub>1")
    case HALT
    then show ?thesis using aux2 step1.hyps(2) by auto
  next
    case (ASSIGN x v)
    have pre1: "well_defined_instr (x ;;= v)" by (metis ASSIGN step1.prems(1) step1.prems(2) step1.prems(3) well_defined_prog_def)
    have pre2: "iexec (x ;;= v) (pc\<^sub>1, s\<^sub>1) = (pc\<^sub>2, s\<^sub>2)" using ASSIGN aux2 by fastforce
    have pre3: "s ''pc'' = pc\<^sub>1" using step1.prems(4) by blast
    thm instr_assign[OF pre1 pre2]
    have "\<exists>s'. ((GOTO_Instr_to_WHILE (x ;;= v), s) \<Rightarrow>\<^bsup> 4 \<^esup> s') \<and> (s' ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. s' x = t' x)" sorry
    show ?thesis using step1 ASSIGN sorry
  next
    case (ADD x31 x32)
    then show ?thesis sorry
  next
    case (SUB x41 x42)
    then show ?thesis sorry
  next
    case (RSH x5)
    then show ?thesis sorry
  next
    case (MOD x6)
    then show ?thesis sorry
  next
    case (JMP x7)
    then show ?thesis sorry
  next
    case (CONDJMP x81 x82)
    then show ?thesis sorry
  qed
qed

lemma 
assumes "prog \<turnstile> (pc, s') \<rightarrow>\<^bsup> k \<^esup> (pc', t')"
    and "(GOTO_Prog_to_WHILE prog, s) \<Rightarrow>\<^bsup> 2 + (WHILE_complexity prog (pc, s') k) \<^esup> t"
    and "well_defined_prog prog" and "pc = 1"
    and "\<forall>x \<noteq> ''pc''. s x = s' x"
  shows "\<forall>x \<noteq> ''pc''. t x = t' x" using assms
proof -
  have "(''pc'' ::= A (atomExp.N 1), s) \<Rightarrow>\<^bsup> 2 \<^esup> s(''pc'' := 1)" by (simp add: assign_t_simp numeral_2_eq_2)
  let ?s = "s(''pc'' := 1)"
  have aux1: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF prog, ?s) \<Rightarrow>\<^bsup> (WHILE_complexity prog (pc, s') k) \<^esup> t" 
    using GOTO_Prog_to_WHILE_def assms(2) by fastforce
  have aux2: "1 \<le> pc" by (simp add: assms(4))
  have aux3: "pc \<le> length prog" using assms(3) assms(4) well_defined_prog_def by blast
  have aux4: "?s ''pc'' = pc" by (simp add: assms(4))
  have aux5: "\<forall>x \<noteq> ''pc''. ?s x = s' x" by (simp add: assms(5))
  show "\<forall>x \<noteq> ''pc''. t x = t' x" 
    using prog_var_consist[of prog pc s' k pc' t' ?s t, OF assms(1) aux1 aux2 aux3 assms(3) aux4 aux5] by blast
qed

lemma 
assumes "prog \<turnstile> (pc, s') \<rightarrow>\<^bsup> k \<^esup> (pc', t')"
    and "(GOTO_Prog_to_WHILE prog, s) \<Rightarrow>\<^bsup> 2 + (WHILE_complexity prog (pc, s') k) \<^esup> t"
    and "well_defined_prog prog" and "pc = 1"
    and "\<forall>x \<noteq> ''pc''. s x = s' x"
  shows "t ''pc'' = pc'" using assms
proof -
  have "(''pc'' ::= A (atomExp.N 1), s) \<Rightarrow>\<^bsup> 2 \<^esup> s(''pc'' := 1)" by (simp add: assign_t_simp numeral_2_eq_2)
  let ?s = "s(''pc'' := 1)"
  have aux1: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF prog, ?s) \<Rightarrow>\<^bsup> (WHILE_complexity prog (pc, s') k) \<^esup> t" 
    using GOTO_Prog_to_WHILE_def assms(2) by fastforce
  have aux2: "1 \<le> pc" by (simp add: assms(4))
  have aux3: "pc \<le> length prog" using assms(3) assms(4) well_defined_prog_def by blast
  have aux4: "?s ''pc'' = pc" by (simp add: assms(4))
  have aux5: "\<forall>x \<noteq> ''pc''. ?s x = s' x" by (simp add: assms(5))
  show "t ''pc'' = pc'" 
    using prog_pc_consist[of prog pc s' k pc' t' ?s t, OF assms(1) aux1 aux2 aux3 assms(3) aux4 aux5] by blast
qed

(*

complexity problem is the same as prog_complexity, need big_step to be fixed.

*)

end