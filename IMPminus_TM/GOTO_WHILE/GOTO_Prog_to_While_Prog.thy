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

fun GOTO_Prog_to_WHILE_single' :: "GOTO_Prog \<Rightarrow> nat \<Rightarrow> com" where 
  "GOTO_Prog_to_WHILE_single' prog 0 = SKIP" | 
  "GOTO_Prog_to_WHILE_single' prog pc = if_neq ''pc'' (length prog + 1 - pc) 
    (GOTO_Prog_to_WHILE_single' prog (pc - 1)) (GOTO_Instr_to_WHILE (prog !! (length prog + 1 - pc)))"

definition GOTO_Prog_to_WHILE_single :: "GOTO_Prog \<Rightarrow> com" where 
  "GOTO_Prog_to_WHILE_single prog = GOTO_Prog_to_WHILE_single' prog (length prog)"

value "GOTO_Prog_to_WHILE_single [''x'' ::= N 3, ''y'' ::= N 4, ''z'' ::= V ''x'', ''z'' += V ''y'', HALT]"

lemma 
  assumes "1 \<le> s ''pc''" and "s ''pc'' \<le> pc" and "pc \<le> length prog" and "length prog + 1 - pc \<le> s ''pc''"
    and "(GOTO_Instr_to_WHILE (prog !! (s ''pc'')), s) \<Rightarrow>\<^bsup> i \<^esup> t"
  shows "(GOTO_Prog_to_WHILE_single' prog pc, s) \<Rightarrow>\<^bsup> j \<^esup> t" using assms
proof (induction pc arbitrary: i j)
  case 0
  then show ?case by linarith
next
  case (Suc pc)
  consider (c1) "s ''pc'' = Suc pc" | (c2) "s ''pc'' \<le> pc" using Suc.prems(2) le_SucE by blast
  then show ?case
  proof cases
    case c1
    have "s ''pc'' \<ge> length prog - pc" using Suc.prems(4) by force
    show ?thesis using c1 Suc sorry
  next
    case c2
    have simplify: "GOTO_Prog_to_WHILE_single' prog (Suc pc) = if_neq ''pc'' (length prog - pc) 
    (GOTO_Prog_to_WHILE_single' prog pc) (GOTO_Instr_to_WHILE (prog !! (length prog - pc)))" by simp
    consider (c21) "s ''pc'' = length prog - pc" | (c22) "s ''pc'' > length prog - pc" using Suc.prems(4) by fastforce
    then show ?thesis
    proof cases
      case c21
      have "(GOTO_Prog_to_WHILE_single' prog (Suc pc), s) \<Rightarrow>\<^bsup> i + 5 \<^esup> t" using Suc(6) c21 if_neq_trans_ins_2_out_eq by auto
      show ?thesis using c21 c2 Suc sorry
    next
      case c22
      have "(GOTO_Prog_to_WHILE_single' prog pc, s) \<Rightarrow>\<^bsup> j \<^esup> t" using Suc.IH Suc.prems(3) Suc.prems(5) c2 c22 by force
      hence "(GOTO_Prog_to_WHILE_single' prog (Suc pc), s) \<Rightarrow>\<^bsup> j + 5 \<^esup> t" by (simp add: c22 if_neq_trans_ins_2_out_gt)
      show ?thesis using c22 c2 Suc sorry
    qed
  qed
qed

function (sequential) GOTO_Prog_to_WHILE_IF' :: "GOTO_Prog \<Rightarrow> nat \<Rightarrow> com" where 
  "GOTO_Prog_to_WHILE_IF' prog t = (if t > length prog then SKIP else if_neq ''pc'' t 
    (GOTO_Prog_to_WHILE_IF' prog (Suc t)) (GOTO_Instr_to_WHILE (prog !! t)))"
  apply pat_completeness apply auto done
termination apply (relation "measure (\<lambda>(prog, t) . length prog + 1 - t)") apply auto[] apply auto[] done

definition GOTO_Prog_to_WHILE_IF :: "GOTO_Prog \<Rightarrow> com" where 
  "GOTO_Prog_to_WHILE_IF prog = GOTO_Prog_to_WHILE_IF' prog 1"

value "GOTO_Prog_to_WHILE_IF [''x'' ::= N 3, ''y'' ::= N 4, ''z'' ::= V ''x'', ''z'' += V ''y'', HALT]"

lemma 
  assumes "1 \<le> min_pc" and "min_pc \<le> pc" and "pc \<le> length prog" and "s ''pc'' = pc"
    and "(GOTO_Instr_to_WHILE (prog !! pc), s) \<Rightarrow>\<^bsup> i \<^esup> t"
  shows "(GOTO_Prog_to_WHILE_IF' prog min_pc, s) \<Rightarrow>\<^bsup> j \<^esup> t" using assms
proof (induction prog min_pc arbitrary: rule: GOTO_Prog_to_WHILE_IF'.induct)
  case (1 prog min_pc)
  consider (c1) "min_pc = pc" | (c2) "min_pc < pc" using "1.prems"(2) by linarith
  then show ?case using 1 
  proof cases
    case c1
    then show ?thesis sorry
  next
    case c2
    then show ?thesis sorry
  qed
qed
end