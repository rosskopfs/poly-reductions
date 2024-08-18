theory GOTO_Prog_to_While_Prog
  imports GOTO_Instr_to_While_Prog
begin

text \<open>This is the basic block of the transformed WHILE program\<close>
definition if_neq :: "char list \<Rightarrow> nat \<Rightarrow> com \<Rightarrow> com \<Rightarrow> com" where
  "if_neq y k C1 C2 = 
    y ::= (atomExp.V y \<ominus> atomExp.N k) ;; 
    IF y\<noteq>0 THEN 
      (y ::= (atomExp.V y \<oplus> atomExp.N k) ;; C1)
    ELSE
      (y ::= (atomExp.V y \<oplus> atomExp.N k) ;; C2)"

text \<open>This lemma shows that the if_neq only adds 5 on complexity for the equal branch\<close>
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

text \<open>This lemma shows that the if_neq only adds 5 on complexity for the inequal branch\<close>
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

text \<open>The reversed lemma of the above lemma\<close>
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

text \<open>The reversed lemma of the above lemma\<close>
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

text \<open>define the IF part in the WHILE loop of the transformed WHILE program\<close>
function (sequential) GOTO_Prog_to_WHILE_IF' :: "GOTO_Prog \<Rightarrow> nat \<Rightarrow> com" where 
  "GOTO_Prog_to_WHILE_IF' prog t = (if t > length prog then SKIP else if_neq ''pc'' t 
    (GOTO_Prog_to_WHILE_IF' prog (Suc t)) (GOTO_Instr_to_WHILE (prog !! t)))"
  apply pat_completeness apply auto done
termination apply (relation "measure (\<lambda>(prog, t) . length prog + 1 - t)") apply auto[] apply auto[] done

definition GOTO_Prog_to_WHILE_IF :: "GOTO_Prog \<Rightarrow> com" where 
  "GOTO_Prog_to_WHILE_IF prog = GOTO_Prog_to_WHILE_IF' prog 1"

text \<open>An example of GOTO_Prog_to_WHILE_IF\<close>
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

text \<open>Prove that the GOTO_Prog_to_WHILE_IF's complexity is linear to the complexity of GOTO program\<close>
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

text \<open>The definition of the WHILE program to a GOTO program\<close>
definition GOTO_Prog_to_WHILE :: "GOTO_Prog \<Rightarrow> com" where
  "GOTO_Prog_to_WHILE prog = ''pc'' ::= A (atomExp.N 1) ;; WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF prog"

text \<open>reversed version is also necessary\<close>
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

text \<open>Here defines which GOTO program is well defined\<close>
definition well_defined_prog :: "GOTO_Prog \<Rightarrow> bool" where
  "well_defined_prog prog = (length prog \<ge> 1 \<and> (\<forall>i. (1 \<le> i \<and> i \<le> length prog) \<longrightarrow> (
    well_defined_instr (prog !! i) \<and> 
    (case prog !! i of GOTO j \<Rightarrow> j \<le> length prog | IF x\<noteq>0 THEN GOTO j \<Rightarrow> j \<le> length prog | _ \<Rightarrow> True))) \<and> 
    (case (prog !! (length prog)) of 
      HALT \<Rightarrow> True | x ;;= c \<Rightarrow> False | x += c \<Rightarrow> False | x -= c \<Rightarrow> False | x \<bind>1 \<Rightarrow> False | x %=2 \<Rightarrow> False | GOTO i \<Rightarrow> True | IF x\<noteq>0 THEN GOTO i \<Rightarrow> False))"

text \<open>This lemma proves that is the GOTO program is well defined, the program counter will be within a fixed range during the execution of a single GOTO instruction\<close>
lemma well_defined_prog_pc_range_single:
  assumes "prog \<turnstile> (pc, s) \<rightarrow> (pc', t)"
    and "well_defined_prog prog"
    and "1 \<le> pc \<and> pc \<le> length prog"
  shows "0 \<le> pc' \<and> pc' \<le> length prog" using assms
proof (cases "prog !! pc")
  case HALT
  have "iexec (prog !! pc) (pc, s) = (pc', t)" using assms(1) exec1_def by auto
  hence "pc' = 0" using HALT by auto
  thus ?thesis using step1 HALT by blast
next
  case (ASSIGN x c)
  consider (c1) "pc = length prog" | (c2) "pc < length prog" using assms(3) le_neq_implies_less by blast
  thus ?thesis
    proof cases
      case c1
      let ?case = "case (prog !! (length prog)) of 
        HALT \<Rightarrow> True | x ;;= c \<Rightarrow> False | x += c \<Rightarrow> False | x -= c \<Rightarrow> False | x \<bind>1 \<Rightarrow> False | x %=2 \<Rightarrow> False | GOTO i \<Rightarrow> True | IF x\<noteq>0 THEN GOTO i \<Rightarrow> False"
      have ?case using assms(2) well_defined_prog_def by auto
      then show ?thesis using ASSIGN c1 by simp
    next
      case c2
      have "iexec (prog !! pc) (pc, s) = (pc', t)" using assms(1) exec1_def by auto
      hence "pc' = pc + 1" using ASSIGN by auto
      then show ?thesis using c2 by auto
    qed
next
  case (ADD x c)
  consider (c1) "pc = length prog" | (c2) "pc < length prog" using assms(3) le_neq_implies_less by blast
  thus ?thesis
    proof cases
      case c1
      let ?case = "case (prog !! (length prog)) of 
        HALT \<Rightarrow> True | x ;;= c \<Rightarrow> False | x += c \<Rightarrow> False | x -= c \<Rightarrow> False | x \<bind>1 \<Rightarrow> False | x %=2 \<Rightarrow> False | GOTO i \<Rightarrow> True | IF x\<noteq>0 THEN GOTO i \<Rightarrow> False"
      have ?case using assms(2) well_defined_prog_def by auto
      then show ?thesis using ADD c1 by simp
    next
      case c2
      have "iexec (prog !! pc) (pc, s) = (pc', t)" using assms(1) exec1_def by auto
      hence "pc' = pc + 1" using ADD by auto
      then show ?thesis using c2 by auto
    qed
next
  case (SUB x c)
  consider (c1) "pc = length prog" | (c2) "pc < length prog" using assms(3) le_neq_implies_less by blast
  thus ?thesis
    proof cases
      case c1
      let ?case = "case (prog !! (length prog)) of 
        HALT \<Rightarrow> True | x ;;= c \<Rightarrow> False | x += c \<Rightarrow> False | x -= c \<Rightarrow> False | x \<bind>1 \<Rightarrow> False | x %=2 \<Rightarrow> False | GOTO i \<Rightarrow> True | IF x\<noteq>0 THEN GOTO i \<Rightarrow> False"
      have ?case using assms(2) well_defined_prog_def by auto
      then show ?thesis using SUB c1 by simp
    next
      case c2
      have "iexec (prog !! pc) (pc, s) = (pc', t)" using assms(1) exec1_def by auto
      hence "pc' = pc + 1" using SUB by auto
      then show ?thesis using c2 by auto
    qed
next
  case (RSH x5)
  consider (c1) "pc = length prog" | (c2) "pc < length prog" using assms(3) le_neq_implies_less by blast
  thus ?thesis
    proof cases
      case c1
      let ?case = "case (prog !! (length prog)) of 
        HALT \<Rightarrow> True | x ;;= c \<Rightarrow> False | x += c \<Rightarrow> False | x -= c \<Rightarrow> False | x \<bind>1 \<Rightarrow> False | x %=2 \<Rightarrow> False | GOTO i \<Rightarrow> True | IF x\<noteq>0 THEN GOTO i \<Rightarrow> False"
      have ?case using assms(2) well_defined_prog_def by auto
      then show ?thesis using RSH c1 by simp
    next
      case c2
      have "iexec (prog !! pc) (pc, s) = (pc', t)" using assms(1) exec1_def by auto
      hence "pc' = pc + 1" using RSH by auto
      then show ?thesis using c2 by auto
    qed
next
  case (MOD x6)
  consider (c1) "pc = length prog" | (c2) "pc < length prog" using assms(3) le_neq_implies_less by blast
  thus ?thesis
    proof cases
      case c1
      let ?case = "case (prog !! (length prog)) of 
        HALT \<Rightarrow> True | x ;;= c \<Rightarrow> False | x += c \<Rightarrow> False | x -= c \<Rightarrow> False | x \<bind>1 \<Rightarrow> False | x %=2 \<Rightarrow> False | GOTO i \<Rightarrow> True | IF x\<noteq>0 THEN GOTO i \<Rightarrow> False"
      have ?case using assms(2) well_defined_prog_def by auto
      then show ?thesis using MOD c1 by simp
    next
      case c2
      have "iexec (prog !! pc) (pc, s) = (pc', t)" using assms(1) exec1_def by auto
      hence "pc' = pc + 1" using MOD by auto
      then show ?thesis using c2 by auto
    qed
next
  case (JMP i)
  have "(\<forall>i. (1 \<le> i \<and> i \<le> length prog) \<longrightarrow> (
    well_defined_instr (prog !! i) \<and> 
    (case prog !! i of GOTO j \<Rightarrow> j \<le> length prog | IF x\<noteq>0 THEN GOTO j \<Rightarrow> j \<le> length prog | _ \<Rightarrow> True)))" using assms(2) well_defined_prog_def by auto
  hence tmp: "well_defined_instr (prog !! pc) \<and> 
    (case prog !! pc of GOTO j \<Rightarrow> j \<le> length prog | IF x\<noteq>0 THEN GOTO j \<Rightarrow> j \<le> length prog | _ \<Rightarrow> True)" using assms(3) by simp
  hence "well_defined_instr (prog !! pc)" by simp
  hence goal1: "i > 0" using JMP by simp

  have "case prog !! pc of GOTO j \<Rightarrow> j \<le> length prog | IF x\<noteq>0 THEN GOTO j \<Rightarrow> j \<le> length prog | _ \<Rightarrow> True" using tmp by simp
  hence goal2: "i \<le> length prog" using JMP by simp

  have "iexec (GOTO i) (pc, s) = (i, s)" using assms(1) exec1_def JMP by auto
  hence "pc' = i" using JMP assms(1) exec1_def by auto
  thus ?thesis using goal1 goal2 by blast
next
  case (CONDJMP x i)
  consider (x1) "s x = 0" | (x2) "s x \<noteq> 0" by blast
  then show ?thesis
  proof cases
    case x1
    consider (c1) "pc = length prog" | (c2) "pc < length prog" using assms(3) le_neq_implies_less by blast
    thus ?thesis
      proof cases
        case c1
        let ?case = "case (prog !! (length prog)) of 
          HALT \<Rightarrow> True | x ;;= c \<Rightarrow> False | x += c \<Rightarrow> False | x -= c \<Rightarrow> False | x \<bind>1 \<Rightarrow> False | x %=2 \<Rightarrow> False | GOTO i \<Rightarrow> True | IF x\<noteq>0 THEN GOTO i \<Rightarrow> False"
        have ?case using assms(2) well_defined_prog_def by auto
        then show ?thesis using CONDJMP c1 by simp
      next
        case c2
        have "iexec (IF x\<noteq>0 THEN GOTO i) (pc, s) = (pc + 1, s)" using assms(1) exec1_def CONDJMP x1 by auto
        hence "pc' = pc + 1" using CONDJMP using assms(1) exec1_def by auto
        then show ?thesis using c2 by auto
      qed
  next
    case x2
    have "(\<forall>i. (1 \<le> i \<and> i \<le> length prog) \<longrightarrow> (
      well_defined_instr (prog !! i) \<and> 
      (case prog !! i of GOTO j \<Rightarrow> j \<le> length prog | IF x\<noteq>0 THEN GOTO j \<Rightarrow> j \<le> length prog | _ \<Rightarrow> True)))" using assms(2) well_defined_prog_def by auto
    hence tmp: "well_defined_instr (prog !! pc) \<and> 
      (case prog !! pc of GOTO j \<Rightarrow> j \<le> length prog | IF x\<noteq>0 THEN GOTO j \<Rightarrow> j \<le> length prog | _ \<Rightarrow> True)" using assms(3) by simp
    hence "well_defined_instr (prog !! pc)" by simp
    hence goal1: "i > 0" using CONDJMP by simp
  
    have "case prog !! pc of GOTO j \<Rightarrow> j \<le> length prog | IF x\<noteq>0 THEN GOTO j \<Rightarrow> j \<le> length prog | _ \<Rightarrow> True" using tmp by simp
    hence goal2: "i \<le> length prog" using CONDJMP by simp
  
    have "iexec (IF x\<noteq>0 THEN GOTO i) (pc, s) = (i, s)" using assms(1) exec1_def CONDJMP x2 by auto
    hence "pc' = i" using CONDJMP assms(1) exec1_def by simp
    thus ?thesis using goal1 goal2 by blast
  qed
qed

text \<open>This lemma proves that is the GOTO program is well defined, the program counter will be within a fixed range during the execution of a GOTO program\<close>
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
  have "1 \<le> pc\<^sub>2 \<and> pc\<^sub>2 \<le> length P" using well_defined_prog_pc_range_single step1.hyps step1.prems by auto
  thus ?case using step1 by blast
qed

text \<open>This lemma proves that: \<close>
text \<open>Under the assumption that GOTO program and WHILE program starts from the same program counter and state,\<close>
text \<open>If a GOTO instruction ends with program counter pc' and state t'\<close>
text \<open>If a IF part of the WHILE program ends with program counter pc and state t\<close>
text \<open>The two program counter should be the same\<close>
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

text \<open>This lemma proves that: \<close>
text \<open>Under the assumption that GOTO program and WHILE program starts from the same program counter and state,\<close>
text \<open>If a GOTO instruction ends with program counter pc' and state t'\<close>
text \<open>If a IF part of the WHILE program ends with program counter pc and state t\<close>
text \<open>All the variable in state t and t' should have the same value\<close>
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

text \<open>Here the exact complexity of the WHILE loop part is calculated\<close>
fun WHILE_complexity :: "GOTO_Prog \<Rightarrow> config \<Rightarrow> nat \<Rightarrow> nat" where
  "WHILE_complexity _ _ 0 = 0" | 
  "WHILE_complexity prog (pc, s) (Suc step) = 1 + (case (prog !! pc) of 
      HALT \<Rightarrow> 2 |
      x ;;= t \<Rightarrow> 4 |
      x += t \<Rightarrow> 4 | 
      x -= t \<Rightarrow> 4 | 
      x \<bind>1 \<Rightarrow> 4 |
      x %=2 \<Rightarrow> 4 |
      GOTO i \<Rightarrow> 2 | 
      IF x\<noteq>0 THEN GOTO i \<Rightarrow> 3
    ) + 5 * pc + WHILE_complexity prog (iexec (prog !! pc) (pc, s)) step 
    "

lemma "(com1;;com2, s1) \<Rightarrow>\<^bsup> c \<^esup> s3 \<Longrightarrow> (com1, s1) \<Rightarrow>\<^bsup> c1 \<^esup> s2 \<Longrightarrow> (com2, s2) \<Rightarrow>\<^bsup> c - c1 \<^esup> s3"
  using bigstep_det by fastforce

lemma "(WHILE b \<noteq>0 DO c, s1) \<Rightarrow>\<^bsup> z \<^esup> s3 \<Longrightarrow> s1 b \<noteq> 0 \<Longrightarrow> (c,s1) \<Rightarrow>\<^bsup> x \<^esup> s2 \<Longrightarrow> (WHILE b \<noteq>0 DO c, s2) \<Rightarrow>\<^bsup> z - x - 1 \<^esup> s3"
  by (smt (verit) One_nat_def While_tE_time add.commute add_0 add_diff_cancel_left' bigstep_det diff_Suc_Suc diff_diff_eq)

text \<open>This lemma proves that: \<close>
text \<open>Under the assumption that GOTO program and WHILE program starts from the same program counter and state,\<close>
text \<open>If a GOTO instruction ends with program counter pc' and state t'\<close>
text \<open>If a WHILE loop part of the WHILE program ends with program counter pc and state t\<close>
text \<open>The two program counter should be the same\<close>
lemma prog_while_pc_consist:
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
  have aux3: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 1 + ?var + 5 * pc\<^sub>1 + WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" 
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

text \<open>This lemma proves that: \<close>
text \<open>Under the assumption that GOTO program and WHILE program starts from the same program counter and state,\<close>
text \<open>If a GOTO instruction ends with program counter pc' and state t'\<close>
text \<open>If a WHILE loop part of the WHILE program ends with program counter pc and state t\<close>
text \<open>All the variable in state t and t' should have the same value\<close>
lemma prog_while_var_consist:
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
  have aux3: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 1 + ?var + 5 * pc\<^sub>1 + WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" 
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

text \<open>This theorem proves the existence of the WHILE part of the GOTO program\<close>
lemma prog_while_complexity_existence:
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
  have pre1: "s ''pc'' = pc\<^sub>1" using step1.prems(4) by blast
  have pre2: "\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s x = s\<^sub>1 x" using step1.prems(5) by auto
  have aux3: "1 \<le> pc\<^sub>1 \<and> pc\<^sub>1 \<le> length P" using step1 by blast
  have aux4: "0 \<le> pc\<^sub>2 \<and> pc\<^sub>2 \<le> length P" using well_defined_prog_pc_range_single[OF step1(1) step1(7) aux3] by blast
  have aux5: "1 \<le> pc\<^sub>2" using aux2 step1(2) by simp
  have aux6: "pc\<^sub>2 \<le> length P" using aux4 by blast
  have aux7: "1 \<le> s ''pc''" using assms pre1 step1.prems by auto
  have aux8: "s ''pc'' \<le> length P" using assms pre1 step1.prems by auto
  show ?case using step1
  proof (cases "P !! pc\<^sub>1")
    case HALT
    then show ?thesis using aux2 step1.hyps(2) by auto
  next
    case (ASSIGN x v)
    let ?single_rt = 4
    have pre3: "well_defined_instr (x ;;= v)" by (metis ASSIGN step1.prems(1) step1.prems(2) step1.prems(3) well_defined_prog_def)
    have pre4: "iexec (x ;;= v) (pc\<^sub>1, s\<^sub>1) = (pc\<^sub>2, s\<^sub>2)" using ASSIGN aux2 by fastforce
    have "\<exists>s\<^sub>1'. ((GOTO_Instr_to_WHILE (x ;;= v), s) \<Rightarrow>\<^bsup> ?single_rt \<^esup> s\<^sub>1' \<and> s\<^sub>1' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x))" 
      using instr_assign[OF pre3 pre4, of s, OF pre1 pre2] by blast
    then obtain s\<^sub>1' where def_s\<^sub>1': "((GOTO_Instr_to_WHILE (x ;;= v), s) \<Rightarrow>\<^bsup> ?single_rt \<^esup> s\<^sub>1' \<and> s\<^sub>1' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x))" by blast

    have tmp1: "((GOTO_Instr_to_WHILE (P !! s ''pc''), s) \<Rightarrow>\<^bsup> ?single_rt \<^esup> s\<^sub>1')" using def_s\<^sub>1' ASSIGN pre1 by auto
    have tmp2: "s\<^sub>1' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x)" using def_s\<^sub>1' by blast
    have pre5: "s\<^sub>1' ''pc'' = pc\<^sub>2" using tmp2 by blast
    have pre6: "\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x" using tmp2 by blast
    have "\<exists>t. ((WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s\<^sub>1') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t)" 
      using step1(4)[OF aux5 aux6 step1(7), of s\<^sub>1', OF pre5 pre6] by blast
    then obtain t where def_t: "((WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s\<^sub>1') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t)" by blast

    have tmp3: "?var = ?single_rt" by (simp add: ASSIGN)
    have "WHILE_complexity P (pc\<^sub>1, s\<^sub>1) (1 + step) = 1 + 5 * pc\<^sub>1 + ?var + WHILE_complexity P (iexec (P !! pc\<^sub>1) (pc\<^sub>1, s\<^sub>1)) step" by simp
    hence tmp4: "WHILE_complexity P (pc\<^sub>1, s\<^sub>1) (1 + step) = 1 + ?single_rt + 5 * pc\<^sub>1  + WHILE_complexity P (iexec (P !! pc\<^sub>1) (pc\<^sub>1, s\<^sub>1)) step" using tmp3 by auto
    have pre7: "s ''pc'' \<noteq> 0" using pre1 step1.prems(1) by auto
    have pre8: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> ?single_rt + s ''pc'' * 5 \<^esup> s\<^sub>1'" using GOTO_Prog_to_WHILE_IF_correctness_complexity[of s P ?single_rt, OF aux7 aux8 tmp1] by blast
    have pre9: "((WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s\<^sub>1') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t)" using def_t by blast
    have "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 1 + (?single_rt + s ''pc'' * 5) + WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" 
      using WhileTrue[of s "''pc''" "GOTO_Prog_to_WHILE_IF P" "?single_rt + s ''pc'' * 5" s\<^sub>1' "WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step" t, OF pre7 pre8 pre9] by simp
    thus ?thesis 
      by (smt (verit) \<open>WHILE_complexity P (pc\<^sub>1, s\<^sub>1) (1 + step) = 1 + 5 * pc\<^sub>1 + (case P !! pc\<^sub>1 of HALT \<Rightarrow> 2 | GOTO i \<Rightarrow> 2 | IF x\<noteq>0 THEN GOTO i \<Rightarrow> 3 | _ \<Rightarrow> 4) + WHILE_complexity P (iexec (P !! pc\<^sub>1) (pc\<^sub>1, s\<^sub>1)) step\<close> add.assoc add.commute aux2 mult.commute pre1 tmp3)
  next
    case (ADD x v)
    let ?single_rt = 4
    have pre3: "well_defined_instr (x += v)" by (metis ADD step1.prems(1) step1.prems(2) step1.prems(3) well_defined_prog_def)
    have pre4: "iexec (x += v) (pc\<^sub>1, s\<^sub>1) = (pc\<^sub>2, s\<^sub>2)" using ADD aux2 by fastforce
    have "\<exists>s\<^sub>1'. ((GOTO_Instr_to_WHILE (x += v), s) \<Rightarrow>\<^bsup> ?single_rt \<^esup> s\<^sub>1' \<and> s\<^sub>1' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x))" 
      using instr_add[OF pre3 pre4, of s, OF pre1 pre2] by blast
    then obtain s\<^sub>1' where def_s\<^sub>1': "((GOTO_Instr_to_WHILE (x += v), s) \<Rightarrow>\<^bsup> ?single_rt \<^esup> s\<^sub>1' \<and> s\<^sub>1' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x))" by blast

    have tmp1: "((GOTO_Instr_to_WHILE (P !! s ''pc''), s) \<Rightarrow>\<^bsup> ?single_rt \<^esup> s\<^sub>1')" using def_s\<^sub>1' ADD pre1 by auto
    have tmp2: "s\<^sub>1' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x)" using def_s\<^sub>1' by blast
    have pre5: "s\<^sub>1' ''pc'' = pc\<^sub>2" using tmp2 by blast
    have pre6: "\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x" using tmp2 by blast
    have "\<exists>t. ((WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s\<^sub>1') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t)" 
      using step1(4)[OF aux5 aux6 step1(7), of s\<^sub>1', OF pre5 pre6] by blast
    then obtain t where def_t: "((WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s\<^sub>1') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t)" by blast

    have tmp3: "?var = ?single_rt" by (simp add: ADD)
    have "WHILE_complexity P (pc\<^sub>1, s\<^sub>1) (1 + step) = 1 + 5 * pc\<^sub>1 + ?var + WHILE_complexity P (iexec (P !! pc\<^sub>1) (pc\<^sub>1, s\<^sub>1)) step" by simp
    hence tmp4: "WHILE_complexity P (pc\<^sub>1, s\<^sub>1) (1 + step) = 1 + ?single_rt + 5 * pc\<^sub>1  + WHILE_complexity P (iexec (P !! pc\<^sub>1) (pc\<^sub>1, s\<^sub>1)) step" using tmp3 by auto
    have pre7: "s ''pc'' \<noteq> 0" using pre1 step1.prems(1) by auto
    have pre8: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> ?single_rt + s ''pc'' * 5 \<^esup> s\<^sub>1'" using GOTO_Prog_to_WHILE_IF_correctness_complexity[of s P ?single_rt, OF aux7 aux8 tmp1] by blast
    have pre9: "((WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s\<^sub>1') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t)" using def_t by blast
    have "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 1 + (?single_rt + s ''pc'' * 5) + WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" 
      using WhileTrue[of s "''pc''" "GOTO_Prog_to_WHILE_IF P" "?single_rt + s ''pc'' * 5" s\<^sub>1' "WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step" t, OF pre7 pre8 pre9] by simp
    thus ?thesis
      by (smt (verit) ADD tmp4 add.commute group_cancel.add2 mult.commute pre1 pre4 tmp3)
  next
    case (SUB x v)
    let ?single_rt = 4
    have pre3: "well_defined_instr (x -= v)" by (metis SUB step1.prems(1) step1.prems(2) step1.prems(3) well_defined_prog_def)
    have pre4: "iexec (x -= v) (pc\<^sub>1, s\<^sub>1) = (pc\<^sub>2, s\<^sub>2)" using SUB aux2 by fastforce
    have "\<exists>s\<^sub>1'. ((GOTO_Instr_to_WHILE (x -= v), s) \<Rightarrow>\<^bsup> ?single_rt \<^esup> s\<^sub>1' \<and> s\<^sub>1' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x))" 
      using instr_sub[OF pre3 pre4, of s, OF pre1 pre2] by blast
    then obtain s\<^sub>1' where def_s\<^sub>1': "((GOTO_Instr_to_WHILE (x -= v), s) \<Rightarrow>\<^bsup> ?single_rt \<^esup> s\<^sub>1' \<and> s\<^sub>1' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x))" by blast

    have tmp1: "((GOTO_Instr_to_WHILE (P !! s ''pc''), s) \<Rightarrow>\<^bsup> ?single_rt \<^esup> s\<^sub>1')" using def_s\<^sub>1' SUB pre1 by auto
    have tmp2: "s\<^sub>1' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x)" using def_s\<^sub>1' by blast
    have pre5: "s\<^sub>1' ''pc'' = pc\<^sub>2" using tmp2 by blast
    have pre6: "\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x" using tmp2 by blast
    have "\<exists>t. ((WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s\<^sub>1') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t)" 
      using step1(4)[OF aux5 aux6 step1(7), of s\<^sub>1', OF pre5 pre6] by blast
    then obtain t where def_t: "((WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s\<^sub>1') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t)" by blast

    have tmp3: "?var = ?single_rt" by (simp add: SUB)
    have "WHILE_complexity P (pc\<^sub>1, s\<^sub>1) (1 + step) = 1 + 5 * pc\<^sub>1 + ?var + WHILE_complexity P (iexec (P !! pc\<^sub>1) (pc\<^sub>1, s\<^sub>1)) step" by simp
    hence tmp4: "WHILE_complexity P (pc\<^sub>1, s\<^sub>1) (1 + step) = 1 + ?single_rt + 5 * pc\<^sub>1  + WHILE_complexity P (iexec (P !! pc\<^sub>1) (pc\<^sub>1, s\<^sub>1)) step" using tmp3 by auto
    have pre7: "s ''pc'' \<noteq> 0" using pre1 step1.prems(1) by auto
    have pre8: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> ?single_rt + s ''pc'' * 5 \<^esup> s\<^sub>1'" using GOTO_Prog_to_WHILE_IF_correctness_complexity[of s P ?single_rt, OF aux7 aux8 tmp1] by blast
    have pre9: "((WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s\<^sub>1') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t)" using def_t by blast
    have "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 1 + (?single_rt + s ''pc'' * 5) + WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" 
      using WhileTrue[of s "''pc''" "GOTO_Prog_to_WHILE_IF P" "?single_rt + s ''pc'' * 5" s\<^sub>1' "WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step" t, OF pre7 pre8 pre9] by simp
    thus ?thesis
      by (smt (verit) SUB tmp4 add.commute group_cancel.add2 mult.commute pre1 pre4 tmp3)
  next
    case (RSH x)
    let ?single_rt = 4
    have pre3: "well_defined_instr (x \<bind>1)" by (metis RSH step1.prems(1) step1.prems(2) step1.prems(3) well_defined_prog_def)
    have pre4: "iexec (x \<bind>1) (pc\<^sub>1, s\<^sub>1) = (pc\<^sub>2, s\<^sub>2)" using RSH aux2 by fastforce
    have "\<exists>s\<^sub>1'. ((GOTO_Instr_to_WHILE (x \<bind>1), s) \<Rightarrow>\<^bsup> ?single_rt \<^esup> s\<^sub>1' \<and> s\<^sub>1' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x))" 
      using instr_right_shift[OF pre3 pre4, of s, OF pre1 pre2] by blast
    then obtain s\<^sub>1' where def_s\<^sub>1': "((GOTO_Instr_to_WHILE (x \<bind>1), s) \<Rightarrow>\<^bsup> ?single_rt \<^esup> s\<^sub>1' \<and> s\<^sub>1' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x))" by blast

    have tmp1: "((GOTO_Instr_to_WHILE (P !! s ''pc''), s) \<Rightarrow>\<^bsup> ?single_rt \<^esup> s\<^sub>1')" using def_s\<^sub>1' RSH pre1 by auto
    have tmp2: "s\<^sub>1' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x)" using def_s\<^sub>1' by blast
    have pre5: "s\<^sub>1' ''pc'' = pc\<^sub>2" using tmp2 by blast
    have pre6: "\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x" using tmp2 by blast
    have "\<exists>t. ((WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s\<^sub>1') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t)" 
      using step1(4)[OF aux5 aux6 step1(7), of s\<^sub>1', OF pre5 pre6] by blast
    then obtain t where def_t: "((WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s\<^sub>1') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t)" by blast

    have tmp3: "?var = ?single_rt" by (simp add: RSH)
    have "WHILE_complexity P (pc\<^sub>1, s\<^sub>1) (1 + step) = 1 + 5 * pc\<^sub>1 + ?var + WHILE_complexity P (iexec (P !! pc\<^sub>1) (pc\<^sub>1, s\<^sub>1)) step" by simp
    hence tmp4: "WHILE_complexity P (pc\<^sub>1, s\<^sub>1) (1 + step) = 1 + ?single_rt + 5 * pc\<^sub>1  + WHILE_complexity P (iexec (P !! pc\<^sub>1) (pc\<^sub>1, s\<^sub>1)) step" using tmp3 by auto
    have pre7: "s ''pc'' \<noteq> 0" using pre1 step1.prems(1) by auto
    have pre8: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> ?single_rt + s ''pc'' * 5 \<^esup> s\<^sub>1'" using GOTO_Prog_to_WHILE_IF_correctness_complexity[of s P ?single_rt, OF aux7 aux8 tmp1] by blast
    have pre9: "((WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s\<^sub>1') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t)" using def_t by blast
    have "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 1 + (?single_rt + s ''pc'' * 5) + WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" 
      using WhileTrue[of s "''pc''" "GOTO_Prog_to_WHILE_IF P" "?single_rt + s ''pc'' * 5" s\<^sub>1' "WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step" t, OF pre7 pre8 pre9] by simp
    thus ?thesis
      by (smt (verit) RSH tmp4 add.commute group_cancel.add2 mult.commute pre1 pre4 tmp3)
  next
    case (MOD x)
    let ?single_rt = 4
    have pre3: "well_defined_instr (x %=2)" by (metis MOD step1.prems(1) step1.prems(2) step1.prems(3) well_defined_prog_def)
    have pre4: "iexec (x %=2) (pc\<^sub>1, s\<^sub>1) = (pc\<^sub>2, s\<^sub>2)" using MOD aux2 by fastforce
    have "\<exists>s\<^sub>1'. ((GOTO_Instr_to_WHILE (x %=2), s) \<Rightarrow>\<^bsup> ?single_rt \<^esup> s\<^sub>1' \<and> s\<^sub>1' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x))" 
      using instr_left_shift[OF pre3 pre4, of s, OF pre1 pre2] by blast
    then obtain s\<^sub>1' where def_s\<^sub>1': "((GOTO_Instr_to_WHILE (x %=2), s) \<Rightarrow>\<^bsup> ?single_rt \<^esup> s\<^sub>1' \<and> s\<^sub>1' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x))" by blast

    have tmp1: "((GOTO_Instr_to_WHILE (P !! s ''pc''), s) \<Rightarrow>\<^bsup> ?single_rt \<^esup> s\<^sub>1')" using def_s\<^sub>1' MOD pre1 by auto
    have tmp2: "s\<^sub>1' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x)" using def_s\<^sub>1' by blast
    have pre5: "s\<^sub>1' ''pc'' = pc\<^sub>2" using tmp2 by blast
    have pre6: "\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x" using tmp2 by blast
    have "\<exists>t. ((WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s\<^sub>1') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t)" 
      using step1(4)[OF aux5 aux6 step1(7), of s\<^sub>1', OF pre5 pre6] by blast
    then obtain t where def_t: "((WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s\<^sub>1') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t)" by blast

    have tmp3: "?var = ?single_rt" by (simp add: MOD)
    have "WHILE_complexity P (pc\<^sub>1, s\<^sub>1) (1 + step) = 1 + 5 * pc\<^sub>1 + ?var + WHILE_complexity P (iexec (P !! pc\<^sub>1) (pc\<^sub>1, s\<^sub>1)) step" by simp
    hence tmp4: "WHILE_complexity P (pc\<^sub>1, s\<^sub>1) (1 + step) = 1 + ?single_rt + 5 * pc\<^sub>1  + WHILE_complexity P (iexec (P !! pc\<^sub>1) (pc\<^sub>1, s\<^sub>1)) step" using tmp3 by auto
    have pre7: "s ''pc'' \<noteq> 0" using pre1 step1.prems(1) by auto
    have pre8: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> ?single_rt + s ''pc'' * 5 \<^esup> s\<^sub>1'" using GOTO_Prog_to_WHILE_IF_correctness_complexity[of s P ?single_rt, OF aux7 aux8 tmp1] by blast
    have pre9: "((WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s\<^sub>1') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t)" using def_t by blast
    have "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 1 + (?single_rt + s ''pc'' * 5) + WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" 
      using WhileTrue[of s "''pc''" "GOTO_Prog_to_WHILE_IF P" "?single_rt + s ''pc'' * 5" s\<^sub>1' "WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step" t, OF pre7 pre8 pre9] by simp
    thus ?thesis
      by (smt (verit) MOD tmp4 add.commute group_cancel.add2 mult.commute pre1 pre4 tmp3)
  next
    case (JMP i)
    let ?single_rt = 2
    have pre3: "well_defined_instr (GOTO i)" by (metis JMP step1.prems(1) step1.prems(2) step1.prems(3) well_defined_prog_def)
    have pre4: "iexec (GOTO i) (pc\<^sub>1, s\<^sub>1) = (pc\<^sub>2, s\<^sub>2)" using JMP aux2 by fastforce
    have "\<exists>s\<^sub>1'. ((GOTO_Instr_to_WHILE (GOTO i), s) \<Rightarrow>\<^bsup> ?single_rt \<^esup> s\<^sub>1' \<and> s\<^sub>1' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x))" 
      using instr_jump[OF pre3 pre4, of s, OF pre1 pre2] by blast
    then obtain s\<^sub>1' where def_s\<^sub>1': "((GOTO_Instr_to_WHILE (GOTO i), s) \<Rightarrow>\<^bsup> ?single_rt \<^esup> s\<^sub>1' \<and> s\<^sub>1' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x))" by blast

    have tmp1: "((GOTO_Instr_to_WHILE (P !! s ''pc''), s) \<Rightarrow>\<^bsup> ?single_rt \<^esup> s\<^sub>1')" using def_s\<^sub>1' JMP pre1 by auto
    have tmp2: "s\<^sub>1' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x)" using def_s\<^sub>1' by blast
    have pre5: "s\<^sub>1' ''pc'' = pc\<^sub>2" using tmp2 by blast
    have pre6: "\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x" using tmp2 by blast
    have "\<exists>t. ((WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s\<^sub>1') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t)" 
      using step1(4)[OF aux5 aux6 step1(7), of s\<^sub>1', OF pre5 pre6] by blast
    then obtain t where def_t: "((WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s\<^sub>1') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t)" by blast

    have tmp3: "?var = ?single_rt" by (simp add: JMP)
    have "WHILE_complexity P (pc\<^sub>1, s\<^sub>1) (1 + step) = 1 + 5 * pc\<^sub>1 + ?var + WHILE_complexity P (iexec (P !! pc\<^sub>1) (pc\<^sub>1, s\<^sub>1)) step" by simp
    hence tmp4: "WHILE_complexity P (pc\<^sub>1, s\<^sub>1) (1 + step) = 1 + ?single_rt + 5 * pc\<^sub>1  + WHILE_complexity P (iexec (P !! pc\<^sub>1) (pc\<^sub>1, s\<^sub>1)) step" using tmp3 by auto
    have pre7: "s ''pc'' \<noteq> 0" using pre1 step1.prems(1) by auto
    have pre8: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> ?single_rt + s ''pc'' * 5 \<^esup> s\<^sub>1'" using GOTO_Prog_to_WHILE_IF_correctness_complexity[of s P ?single_rt, OF aux7 aux8 tmp1] by blast
    have pre9: "((WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s\<^sub>1') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t)" using def_t by blast
    have "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 1 + (?single_rt + s ''pc'' * 5) + WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" 
      using WhileTrue[of s "''pc''" "GOTO_Prog_to_WHILE_IF P" "?single_rt + s ''pc'' * 5" s\<^sub>1' "WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step" t, OF pre7 pre8 pre9] by simp
    thus ?thesis
      by (smt (verit) JMP tmp4 add.commute group_cancel.add2 mult.commute pre1 pre4 tmp3)
  next
    case (CONDJMP x i)
    let ?single_rt = 3
    have pre3: "well_defined_instr (IF x\<noteq>0 THEN GOTO i)" by (metis CONDJMP step1.prems(1) step1.prems(2) step1.prems(3) well_defined_prog_def)
    have pre4: "iexec (IF x\<noteq>0 THEN GOTO i) (pc\<^sub>1, s\<^sub>1) = (pc\<^sub>2, s\<^sub>2)" using CONDJMP aux2 by fastforce
    have "\<exists>s\<^sub>1'. ((GOTO_Instr_to_WHILE (IF x\<noteq>0 THEN GOTO i), s) \<Rightarrow>\<^bsup> ?single_rt \<^esup> s\<^sub>1' \<and> s\<^sub>1' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x))" 
      using instr_cond_jump[OF pre3 pre4, of s, OF pre1 pre2] by blast
    then obtain s\<^sub>1' where def_s\<^sub>1': "((GOTO_Instr_to_WHILE (IF x\<noteq>0 THEN GOTO i), s) \<Rightarrow>\<^bsup> ?single_rt \<^esup> s\<^sub>1' \<and> s\<^sub>1' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x))" by blast

    have tmp1: "((GOTO_Instr_to_WHILE (P !! s ''pc''), s) \<Rightarrow>\<^bsup> ?single_rt \<^esup> s\<^sub>1')" using def_s\<^sub>1' CONDJMP pre1 by auto
    have tmp2: "s\<^sub>1' ''pc'' = pc\<^sub>2 \<and> (\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x)" using def_s\<^sub>1' by blast
    have pre5: "s\<^sub>1' ''pc'' = pc\<^sub>2" using tmp2 by blast
    have pre6: "\<forall>x. x \<noteq> ''pc'' \<longrightarrow> s\<^sub>1' x = s\<^sub>2 x" using tmp2 by blast
    have "\<exists>t. ((WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s\<^sub>1') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t)" 
      using step1(4)[OF aux5 aux6 step1(7), of s\<^sub>1', OF pre5 pre6] by blast
    then obtain t where def_t: "((WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s\<^sub>1') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t)" by blast

    have tmp3: "?var = ?single_rt" by (simp add: CONDJMP)
    have "WHILE_complexity P (pc\<^sub>1, s\<^sub>1) (1 + step) = 1 + 5 * pc\<^sub>1 + ?var + WHILE_complexity P (iexec (P !! pc\<^sub>1) (pc\<^sub>1, s\<^sub>1)) step" by simp
    hence tmp4: "WHILE_complexity P (pc\<^sub>1, s\<^sub>1) (1 + step) = 1 + ?single_rt + 5 * pc\<^sub>1  + WHILE_complexity P (iexec (P !! pc\<^sub>1) (pc\<^sub>1, s\<^sub>1)) step" using tmp3 by auto
    have pre7: "s ''pc'' \<noteq> 0" using pre1 step1.prems(1) by auto
    have pre8: "(GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> ?single_rt + s ''pc'' * 5 \<^esup> s\<^sub>1'" using GOTO_Prog_to_WHILE_IF_correctness_complexity[of s P ?single_rt, OF aux7 aux8 tmp1] by blast
    have pre9: "((WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s\<^sub>1') \<Rightarrow>\<^bsup> WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t)" using def_t by blast
    have "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF P, s) \<Rightarrow>\<^bsup> 1 + (?single_rt + s ''pc'' * 5) + WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step \<^esup> t" 
      using WhileTrue[of s "''pc''" "GOTO_Prog_to_WHILE_IF P" "?single_rt + s ''pc'' * 5" s\<^sub>1' "WHILE_complexity P (pc\<^sub>2, s\<^sub>2) step" t, OF pre7 pre8 pre9] by simp
    thus ?thesis
      by (smt (verit) CONDJMP tmp4 add.commute group_cancel.add2 mult.commute pre1 pre4 tmp3)
  qed
qed

text \<open>This lemma proves that: \<close>
text \<open>Under the assumption that GOTO program and WHILE program starts from the same program counter and state,\<close>
text \<open>If a GOTO instruction ends with program counter pc' and state t'\<close>
text \<open>If the transformed WHILE program ends with program counter pc and state t\<close>
text \<open>All the variable in state t and t' should have the same value\<close>
lemma prog_var_consist:
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
    using prog_while_var_consist[of prog pc s' k pc' t' ?s t, OF assms(1) aux1 aux2 aux3 assms(3) aux4 aux5] by blast
qed

text \<open>This lemma proves that: \<close>
text \<open>Under the assumption that GOTO program and WHILE program starts from the same program counter and state,\<close>
text \<open>If a GOTO instruction ends with program counter pc' and state t'\<close>
text \<open>If the transformed WHILE program ends with program counter pc and state t\<close>
text \<open>The two program counter should be the same\<close>
lemma prog_pc_consist:
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
    using prog_while_pc_consist[of prog pc s' k pc' t' ?s t, OF assms(1) aux1 aux2 aux3 assms(3) aux4 aux5] by blast
qed

text \<open>This theorem proves the existence of the transformed WHILE program\<close>
lemma prog_complexity_existence:
  assumes "prog \<turnstile> (pc, s') \<rightarrow>\<^bsup> k \<^esup> (pc', t')"
    and "well_defined_prog prog" and "pc = 1"
    and "\<forall>x \<noteq> ''pc''. s x = s' x"
  shows "\<exists>t. (GOTO_Prog_to_WHILE prog, s) \<Rightarrow>\<^bsup> 2 + (WHILE_complexity prog (pc, s') k) \<^esup> t" using assms
proof -
  have aux1: "(''pc'' ::= A (atomExp.N 1), s) \<Rightarrow>\<^bsup> 2 \<^esup> s(''pc'' := 1)" by (simp add: assign_t_simp numeral_2_eq_2)
  let ?s = "s(''pc'' := 1)"
  have aux2: "1 \<le> pc" by (simp add: assms(3))
  have aux3: "pc \<le> length prog" using assms(2) assms(3) well_defined_prog_def by blast
  have aux4: "?s ''pc'' = pc" by (simp add: assms(3))
  have aux5: "\<forall>x \<noteq> ''pc''. ?s x = s' x" by (simp add: assms(4))
  have "\<exists>t. (WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF prog, ?s) \<Rightarrow>\<^bsup> (WHILE_complexity prog (pc, s') k) \<^esup> t" 
    using prog_while_complexity_existence[of prog pc s' k pc' t' ?s, OF assms(1) aux2 aux3 assms(2) aux4 aux5] by blast
  then obtain t where def_t: "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF prog, ?s) \<Rightarrow>\<^bsup> (WHILE_complexity prog (pc, s') k) \<^esup> t" by blast
  hence "(GOTO_Prog_to_WHILE prog, s) \<Rightarrow>\<^bsup> 2 + (WHILE_complexity prog (pc, s') k) \<^esup> t" using aux1 by (metis GOTO_Prog_to_WHILE_def Seq_tE_While_init)
  thus "\<exists>t. (GOTO_Prog_to_WHILE prog, s) \<Rightarrow>\<^bsup> 2 + (WHILE_complexity prog (pc, s') k) \<^esup> t" by blast
qed

text \<open>The final goal of this submodule\<close>
theorem while_prog_valid:
  assumes "prog \<turnstile> (pc, s') \<rightarrow>\<^bsup> k \<^esup> (pc', t')"
    and "well_defined_prog prog" and "pc = 1"
    and "\<forall>x \<noteq> ''pc''. s x = s' x"
  shows "\<exists>t. (GOTO_Prog_to_WHILE prog, s) \<Rightarrow>\<^bsup> 2 + (WHILE_complexity prog (pc, s') k) \<^esup> t \<and> t ''pc'' = pc' \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using assms
proof -
  have goal1: "\<exists>t. (GOTO_Prog_to_WHILE prog, s) \<Rightarrow>\<^bsup> 2 + (WHILE_complexity prog (pc, s') k) \<^esup> t" using prog_complexity_existence assms by blast
  then obtain t where def_t: "(GOTO_Prog_to_WHILE prog, s) \<Rightarrow>\<^bsup> 2 + (WHILE_complexity prog (pc, s') k) \<^esup> t" by blast
  have goal2: "t ''pc'' = pc'" using prog_pc_consist[of prog pc s' k pc' t' s t, OF assms(1) def_t assms(2) assms(3) assms(4)] by blast
  have goal3: "\<forall>x \<noteq> ''pc''. t x = t' x" using prog_var_consist[of prog pc s' k pc' t' s t, OF assms(1) def_t assms(2) assms(3) assms(4)] by blast
  show "\<exists>t. (GOTO_Prog_to_WHILE prog, s) \<Rightarrow>\<^bsup> 2 + (WHILE_complexity prog (pc, s') k) \<^esup> t \<and> t ''pc'' = pc' \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using def_t goal2 goal3 by blast
qed
end