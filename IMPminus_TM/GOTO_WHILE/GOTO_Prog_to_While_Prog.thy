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

value "GOTO_Prog_to_WHILE_IF [''x'' ::= N 3, ''y'' ::= N 4, ''z'' ::= V ''x'', ''z'' += V ''y'', HALT]"

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

definition GOTO_Prog_to_WHILE :: "GOTO_Prog \<Rightarrow> com" where
  "GOTO_Prog_to_WHILE prog = ''pc'' ::= A (atomExp.N 1) ;; WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF prog"

definition well_defined_prog :: "GOTO_Prog \<Rightarrow> bool" where
  "well_defined_prog prog = (\<forall>i. (1 \<le> i \<and> i \<le> length prog) \<longrightarrow> (well_defined_instr (prog !! i)))"

(*
definition well_defined_prog :: "GOTO_Prog \<Rightarrow> bool" where
  "well_defined_prog prog = (\<forall>i. (1 \<le> i \<and> i \<le> length prog) \<longrightarrow> 
    (well_defined_instr (prog !! i) \<and> (case prog !! i of GOTO j \<Rightarrow> j \<le> length prog | _ \<Rightarrow> True)))"
*)

lemma prog_pc_consist:
  assumes "prog \<turnstile> (pc, s') \<rightarrow>* (pc', t')" 
    and "well_defined_prog prog"
    and "(WHILE ''pc''\<noteq>0 DO GOTO_Prog_to_WHILE_IF prog, s) \<Rightarrow>\<^bsup> k \<^esup> t"
    and "s ''pc'' = pc" and "\<forall>x \<noteq> ''pc''. s x = s' x"
  shows "t ''pc'' = pc'" using assms 
proof (induction "exec1 prog" pc s' pc t rule: star_induct) sorry
end