theory GOTO_Instr_to_While_Prog
  imports "IMPminus_TM-Def.GOTO" "IMP_Minus.Com" "IMP_Minus.Big_StepT"
begin

fun well_defined_instr :: "instr \<Rightarrow> bool" where
  "well_defined_instr HALT = True" | 
  "well_defined_instr (x ;;= t) = (x \<noteq> ''pc''\<and> (case t of N c \<Rightarrow> True | V y \<Rightarrow> y \<noteq> ''pc''))" |
  "well_defined_instr (x += t) = (x \<noteq> ''pc''\<and> (case t of N c \<Rightarrow> True | V y \<Rightarrow> y \<noteq> ''pc''))" |
  "well_defined_instr (x -= t) = (x \<noteq> ''pc'' \<and> (case t of N c \<Rightarrow> True | V y \<Rightarrow> y \<noteq> ''pc''))" |
  "well_defined_instr (x \<bind>1) = (x \<noteq> ''pc'')" |
  "well_defined_instr (x %=2) = (x \<noteq> ''pc'')" |
  "well_defined_instr (GOTO i) = (i > 0)" |
  "well_defined_instr (IF x\<noteq>0 THEN GOTO i) = (x \<noteq> ''pc'' \<and> i > 0)"

fun GOTO_Instr_to_WHILE :: "instr \<Rightarrow> com" where
  "GOTO_Instr_to_WHILE HALT = ''pc'' ::= A (atomExp.N 0)" | 
  "GOTO_Instr_to_WHILE (x ;;= t) = 
    (case t of operi.N c \<Rightarrow> x ::= A (atomExp.N c) | operi.V y \<Rightarrow> x ::= A (atomExp.V y)) ;; 
    ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)" | 
  "GOTO_Instr_to_WHILE (x += t) = 
    (case t of operi.N c \<Rightarrow> x ::= (atomExp.V x \<oplus> atomExp.N c) | operi.V y \<Rightarrow> x ::= (atomExp.V x \<oplus> atomExp.V y)) ;; 
    ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)" |
  "GOTO_Instr_to_WHILE (x -= t) = 
    (case t of operi.N c \<Rightarrow> x ::= (atomExp.V x \<ominus> atomExp.N c) | operi.V y \<Rightarrow> x ::= (atomExp.V x \<ominus> atomExp.V y)) ;; 
    ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)" | 
  "GOTO_Instr_to_WHILE (x \<bind>1) = 
    x ::= (atomExp.V x \<then>) ;; 
    ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)" | 
  "GOTO_Instr_to_WHILE (x %=2) = 
    x ::= (atomExp.V x \<doteq>1) ;; 
    ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)" | 
  "GOTO_Instr_to_WHILE (GOTO i) = ''pc'' ::= A (atomExp.N i)" | 
  "GOTO_Instr_to_WHILE (IF x\<noteq>0 THEN GOTO i) = IF x\<noteq>0 THEN ''pc'' ::= A (atomExp.N i) ELSE ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)"

lemma instr_halt_complexity:
  "\<exists>t. (GOTO_Instr_to_WHILE HALT, s) \<Rightarrow>\<^bsup> 2 \<^esup> t"
  by (metis AssignI' GOTO_Instr_to_WHILE.simps(1))

lemma instr_assign_complexity:
  "\<exists>t. (GOTO_Instr_to_WHILE (x ;;= c), s) \<Rightarrow>\<^bsup> 4 \<^esup> t"
  apply (cases c)
  apply fastforce
  by fastforce

lemma instr_add_complexity:
  "\<exists>t. (GOTO_Instr_to_WHILE (x += c), s) \<Rightarrow>\<^bsup> 4 \<^esup> t"
  apply (cases c)
  apply fastforce
  by fastforce

lemma instr_sub_complexity:
  "\<exists>t. (GOTO_Instr_to_WHILE (x -= c), s) \<Rightarrow>\<^bsup> 4 \<^esup> t"
  apply (cases c)
  apply fastforce
  by fastforce

lemma instr_right_shift_complexity:
  "\<exists>t. (GOTO_Instr_to_WHILE (x \<bind>1), s) \<Rightarrow>\<^bsup> 4 \<^esup> t"
  by fastforce

lemma instr_left_shift_complexity:
  "\<exists>t. (GOTO_Instr_to_WHILE (x %=2), s) \<Rightarrow>\<^bsup> 4 \<^esup> t"
  by fastforce

lemma instr_jump_complexity:
  "\<exists>t. (GOTO_Instr_to_WHILE (GOTO i), s) \<Rightarrow>\<^bsup> 2 \<^esup> t"
  by (metis AssignI'' GOTO_Instr_to_WHILE.simps(7))

lemma instr_cond_jump_complexity:
  "\<exists>t. (GOTO_Instr_to_WHILE (IF x\<noteq>0 THEN GOTO i), s) \<Rightarrow>\<^bsup> 3 \<^esup> t"
  apply (cases "s x")
  apply fastforce
  by fastforce

lemma instr_pc_consist:
  assumes "well_defined_instr instr"
    and "(GOTO_Instr_to_WHILE instr, s) \<Rightarrow>\<^bsup> k \<^esup> t"
    and "iexec instr (pc, s') = (pc', t')" 
    and "s ''pc'' = pc" and "\<forall>x \<noteq> ''pc''. s x = s' x"
  shows "t ''pc'' = pc'"
proof (cases instr)
  case HALT
  have "(''pc'' ::= A (atomExp.N 0), s) \<Rightarrow>\<^bsup> k \<^esup> t" using HALT assms(2) by auto
  hence "s(''pc'' := aval (A (atomExp.N 0)) s) = t" by blast
  hence aux1: "t ''pc'' = 0" by force

  have "iexec HALT (pc, s') = (0, s')" by simp
  hence aux2: "pc' = 0" using HALT assms(3) by force

  show ?thesis using aux1 aux2 by simp
next
  case (ASSIGN x tmp)
  then show ?thesis
  proof (cases tmp)
    case (N c)
    let ?inter = "s(x := c)"
    let ?final = "?inter(''pc'' := ?inter ''pc'' + 1)"
    let ?w_com = "x ::= A (atomExp.N c) ;; ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)"
    have aux1: "(x ::= A (atomExp.N c), s) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter" by (simp add: AssignI')
    have aux2: "(''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1), ?inter) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" by (simp add: AssignI')
    have "(?w_com, s) \<Rightarrow>\<^bsup> 4 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" using aux1 aux2 by (simp add: Seq)
    hence "t = ?inter(''pc'' := ?inter ''pc'' + 1)" using ASSIGN N assms(2) by auto
    hence aux3: "t ''pc'' = pc + 1" using ASSIGN assms(1) assms(4) by auto

    have "iexec (x ;;= tmp) (pc, s') = (pc + 1, s'(x := c))" by (simp add: N)
    hence aux4: "pc' = pc + 1" using ASSIGN assms(3) by auto

    show ?thesis using aux3 aux4 by blast
  next
    case (V y)
    let ?inter = "s(x := s y)"
    let ?final = "?inter(''pc'' := ?inter ''pc'' + 1)"
    let ?w_com = "x ::= A (atomExp.V y) ;; ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)"
    have aux1: "(x ::= A (atomExp.V y), s) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter" by (simp add: AssignI')
    have aux2: "(''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1), ?inter) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" by (simp add: AssignI')
    have "(?w_com, s) \<Rightarrow>\<^bsup> 4 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" using aux1 aux2 by (simp add: Seq)
    hence "t = ?inter(''pc'' := ?inter ''pc'' + 1)" using ASSIGN V assms(2) by auto
    hence aux3: "t ''pc'' = pc + 1" using ASSIGN assms(1) assms(4) by auto

    have "iexec (x ;;= tmp) (pc, s') = (pc + 1, s'(x := s' y))" by (simp add: V)
    hence aux4: "pc' = pc + 1" using ASSIGN assms(3) by auto

    show ?thesis using aux3 aux4 by blast
  qed
next
  case (ADD x tmp)
  then show ?thesis
  proof (cases tmp)
    case (N c)
    let ?inter = "s(x := s x + c)"
    let ?final = "?inter(''pc'' := ?inter ''pc'' + 1)"
    let ?w_com = "x ::= (atomExp.V x \<oplus> atomExp.N c) ;; ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)"
    have aux1: "(x ::= (atomExp.V x \<oplus> atomExp.N c), s) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter" by (simp add: AssignI')
    have aux2: "(''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1), ?inter) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" by (simp add: AssignI')
    have "(?w_com, s) \<Rightarrow>\<^bsup> 4 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" using aux1 aux2 by (simp add: Seq)
    hence "t = ?inter(''pc'' := ?inter ''pc'' + 1)" using ADD N assms(2) by auto
    hence aux3: "t ''pc'' = pc + 1" using ADD assms(1) assms(4) by auto

    have "iexec (x += tmp) (pc, s') = (pc + 1, s'(x :=  s' x + c))" by (simp add: N)
    hence aux4: "pc' = pc + 1" using ADD assms(3) by auto

    show ?thesis using aux3 aux4 by blast
  next
    case (V y)
    let ?inter = "s(x := s x + s y)"
    let ?final = "?inter(''pc'' := ?inter ''pc'' + 1)"
    let ?w_com = "x ::= (atomExp.V x \<oplus> atomExp.V y) ;; ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)"
    have aux1: "(x ::= (atomExp.V x \<oplus> atomExp.V y), s) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter" by (simp add: AssignI')
    have aux2: "(''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1), ?inter) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" by (simp add: AssignI')
    have "(?w_com, s) \<Rightarrow>\<^bsup> 4 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" using aux1 aux2 by (simp add: Seq)
    hence "t = ?inter(''pc'' := ?inter ''pc'' + 1)" using ADD V assms(2) by auto
    hence aux3: "t ''pc'' = pc + 1" using ADD assms(1) assms(4) by auto

    have "iexec (x += tmp) (pc, s') = (pc + 1, s'(x :=  s' x + s' y))" by (simp add: V)
    hence aux4: "pc' = pc + 1" using ADD assms(3) by auto

    show ?thesis using aux3 aux4 by blast
  qed
next
  case (SUB x tmp)
  then show ?thesis
  proof (cases tmp)
    case (N c)
    let ?inter = "s(x := s x - c)"
    let ?final = "?inter(''pc'' := ?inter ''pc'' + 1)"
    let ?w_com = "x ::= (atomExp.V x \<ominus> atomExp.N c) ;; ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)"
    have aux1: "(x ::= (atomExp.V x \<ominus> atomExp.N c), s) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter" by (simp add: AssignI')
    have aux2: "(''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1), ?inter) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" by (simp add: AssignI')
    have "(?w_com, s) \<Rightarrow>\<^bsup> 4 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" using aux1 aux2 by (simp add: Seq)
    hence "t = ?inter(''pc'' := ?inter ''pc'' + 1)" using SUB N assms(2) by auto
    hence aux3: "t ''pc'' = pc + 1" using SUB assms(1) assms(4) by auto

    have "iexec (x -= tmp) (pc, s') = (pc + 1, s'(x :=  s' x - c))" by (simp add: N)
    hence aux4: "pc' = pc + 1" using SUB assms(3) by auto

    show ?thesis using aux3 aux4 by blast
  next
    case (V y)
    let ?inter = "s(x := s x - s y)"
    let ?final = "?inter(''pc'' := ?inter ''pc'' + 1)"
    let ?w_com = "x ::= (atomExp.V x \<ominus> atomExp.V y) ;; ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)"
    have aux1: "(x ::= (atomExp.V x \<ominus> atomExp.V y), s) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter" by (simp add: AssignI')
    have aux2: "(''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1), ?inter) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" by (simp add: AssignI')
    have "(?w_com, s) \<Rightarrow>\<^bsup> 4 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" using aux1 aux2 by (simp add: Seq)
    hence "t = ?inter(''pc'' := ?inter ''pc'' + 1)" using SUB V assms(2) by auto
    hence aux3: "t ''pc'' = pc + 1" using SUB assms(1) assms(4) by auto

    have "iexec (x -= tmp) (pc, s') = (pc + 1, s'(x :=  s' x - s' y))" by (simp add: V)
    hence aux4: "pc' = pc + 1" using SUB assms(3) by auto

    show ?thesis using aux3 aux4 by blast
  qed
next
  case (RSH x)
  let ?inter = "s(x := s x div 2)"
  let ?final = "?inter(''pc'' := ?inter ''pc'' + 1)"
  let ?w_com = "x ::= (atomExp.V x \<then>) ;; ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)"
  have aux1: "(x ::= (atomExp.V x \<then>), s) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter" by (simp add: AssignI')
  have aux2: "(''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1), ?inter) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" by (simp add: AssignI')
  have "(?w_com, s) \<Rightarrow>\<^bsup> 4 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" using aux1 aux2 by (simp add: Seq)
  hence "t = ?inter(''pc'' := ?inter ''pc'' + 1)" using RSH assms(2) by auto
  hence aux3: "t ''pc'' = pc + 1" using RSH assms(1) assms(4) by auto

  have "iexec (x \<bind>1) (pc, s') = (pc + 1, s'(x :=  s' x div 2))" by simp
  hence aux4: "pc' = pc + 1" using RSH assms(3) by auto
  
  show ?thesis using aux3 aux4 by blast
next
  case (MOD x)
  let ?inter = "s(x := s x mod 2)"
  let ?final = "?inter(''pc'' := ?inter ''pc'' + 1)"
  let ?w_com = "x ::= (atomExp.V x \<doteq>1) ;; ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)"
  have aux1: "(x ::= (atomExp.V x \<doteq>1), s) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter" by (simp add: AssignI')
  have aux2: "(''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1), ?inter) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" by (simp add: AssignI')
  have "(?w_com, s) \<Rightarrow>\<^bsup> 4 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" using aux1 aux2 by (simp add: Seq)
  hence "t = ?inter(''pc'' := ?inter ''pc'' + 1)" using MOD assms(2) by auto
  hence aux3: "t ''pc'' = pc + 1" using MOD assms(1) assms(4) by auto

  have "iexec (x %=2) (pc, s') = (pc + 1, s'(x :=  s' x mod 2))" by simp
  hence aux4: "pc' = pc + 1" using MOD assms(3) by auto
  
  show ?thesis using aux3 aux4 by blast
next
  case (JMP i)
  have "(''pc'' ::= A (atomExp.N i), s) \<Rightarrow>\<^bsup> 2 \<^esup> s(''pc'' := i)" by (simp add: AssignI')
  hence aux1: "t ''pc'' = i" using JMP assms(2) by auto

  have "iexec (GOTO i) (pc, s') = (i, s')" by simp
  hence aux2: "pc' = i" using JMP assms(3) by auto

  show ?thesis using aux1 aux2 by blast
next
  case (CONDJMP x i)
  let ?w_com = "IF x\<noteq>0 THEN ''pc'' ::= A (atomExp.N i) ELSE ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)"
  consider (c1) "s x = 0" | (c2) "s x > 0" by auto
  then show ?thesis
  proof cases
    case c1
    have "(''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1), s) \<Rightarrow>\<^bsup> 2 \<^esup> s(''pc'' := s ''pc'' + 1)" by (simp add: AssignI')
    hence "(?w_com, s) \<Rightarrow>\<^bsup> 3 \<^esup> s(''pc'' := s ''pc'' + 1)" by (simp add: big_step_t.IfFalse c1)
    hence "t = s(''pc'' := s ''pc'' + 1)" using CONDJMP assms(2) by auto
    hence aux1: "t ''pc'' = pc + 1" using CONDJMP assms(1) assms(4) by auto

    have "iexec (IF x\<noteq>0 THEN GOTO i) (pc, s') = (pc + 1, s')" using c1 CONDJMP assms(1) assms(5) by auto
    hence aux2: "pc' = pc + 1" using CONDJMP assms(3) by auto

    show ?thesis using aux1 aux2 by blast
  next
    case c2
    have "(''pc'' ::= A (atomExp.N i), s) \<Rightarrow>\<^bsup> 2 \<^esup> s(''pc'' := i)" by (simp add: AssignI')
    hence "(?w_com, s) \<Rightarrow>\<^bsup> 3 \<^esup> s(''pc'' := i)" by (simp add: big_step_t.IfTrue c2)
    hence aux1: "t ''pc'' = i" using CONDJMP assms(2) fun_upd_eqD by fastforce

    have "iexec (IF x\<noteq>0 THEN GOTO i) (pc, s') = (i, s')" using CONDJMP assms(1) assms(5) c2 by auto
    hence aux2: "pc' = i" using CONDJMP assms(3) by auto

    show ?thesis using aux1 aux2 by blast
  qed
qed

lemma aux_lemma1: "\<forall>x \<noteq> t. s x = s' x \<Longrightarrow> y \<noteq> t \<Longrightarrow> z \<noteq> t \<Longrightarrow> (s(x := s y)) z = (s'(x := s' y)) z" by simp

lemma instr_var_consist:
  assumes "well_defined_instr instr"
    and "(GOTO_Instr_to_WHILE instr, s) \<Rightarrow>\<^bsup> k \<^esup> t"
    and "iexec instr (pc, s') = (pc', t')" 
    and "s ''pc'' = pc" and "\<forall>x \<noteq> ''pc''. s x = s' x"
  shows "\<forall>z \<noteq> ''pc''. t z = t' z"
proof (cases instr)
  case HALT
  have "(''pc'' ::= A (atomExp.N 0), s) \<Rightarrow>\<^bsup> k \<^esup> t" using HALT assms(2) by auto
  hence "t = s(''pc'' := aval (A (atomExp.N 0)) s)" by blast
  thus ?thesis using HALT assms(3) assms(5) by auto
next
  case (ASSIGN x tmp)
  then show ?thesis
  proof (cases tmp)
    case (N c)
    let ?inter = "s(x := c)"
    let ?final = "?inter(''pc'' := ?inter ''pc'' + 1)"
    let ?w_com = "x ::= A (atomExp.N c) ;; ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)"
    have aux1: "(x ::= A (atomExp.N c), s) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter" by (simp add: AssignI')
    have aux2: "(''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1), ?inter) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" by (simp add: AssignI')
    have "(?w_com, s) \<Rightarrow>\<^bsup> 4 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" using aux1 aux2 by (simp add: Seq)
    hence aux3: "t = ?inter(''pc'' := ?inter ''pc'' + 1)" using ASSIGN N assms(2) by auto

    have "iexec (x ;;= tmp) (pc, s') = (pc + 1, s'(x := c))" by (simp add: N)
    hence aux4: "t' = s'(x := c)" using ASSIGN assms(3) by auto

    show ?thesis using aux3 aux4 by (simp add: assms(5))
  next
    case (V y)
    let ?inter = "s(x := s y)"
    let ?final = "?inter(''pc'' := ?inter ''pc'' + 1)"
    let ?w_com = "x ::= A (atomExp.V y) ;; ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)"
    have aux1: "(x ::= A (atomExp.V y), s) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter" by (simp add: AssignI')
    have aux2: "(''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1), ?inter) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" by (simp add: AssignI')
    have "(?w_com, s) \<Rightarrow>\<^bsup> 4 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" using aux1 aux2 by (simp add: Seq)
    hence aux3: "t = ?inter(''pc'' := ?inter ''pc'' + 1)" using ASSIGN V assms(2) by auto

    have "iexec (x ;;= tmp) (pc, s') = (pc + 1, s'(x := s' y))" by (simp add: V)
    hence aux4: "t' = s'(x := s' y)" using ASSIGN assms(3) by auto

    let ?inter' = "s'(x := s' y)"
    have "\<forall>z \<noteq> ''pc''. ?inter z = ?inter' z" using ASSIGN V assms(1) assms(5) by auto
    thus ?thesis using aux3 aux4 by simp
  qed
next
  case (ADD x tmp)
  then show ?thesis
  proof (cases tmp)
    case (N c)
    let ?inter = "s(x := s x + c)"
    let ?final = "?inter(''pc'' := ?inter ''pc'' + 1)"
    let ?w_com = "x ::= (atomExp.V x \<oplus> atomExp.N c) ;; ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)"
    have aux1: "(x ::= (atomExp.V x \<oplus> atomExp.N c), s) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter" by (simp add: AssignI')
    have aux2: "(''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1), ?inter) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" by (simp add: AssignI')
    have "(?w_com, s) \<Rightarrow>\<^bsup> 4 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" using aux1 aux2 by (simp add: Seq)
    hence aux3: "t = ?inter(''pc'' := ?inter ''pc'' + 1)" using ADD N assms(2) by auto

    have "iexec (x += tmp) (pc, s') = (pc + 1, s'(x :=  s' x + c))" by (simp add: N)
    hence aux4: "t' = s'(x :=  s' x + c)" using ADD assms(3) by auto
    
    show ?thesis using aux3 aux4 by (simp add: assms(5))
  next
    case (V y)
    let ?inter = "s(x := s x + s y)"
    let ?final = "?inter(''pc'' := ?inter ''pc'' + 1)"
    let ?w_com = "x ::= (atomExp.V x \<oplus> atomExp.V y) ;; ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)"
    have aux1: "(x ::= (atomExp.V x \<oplus> atomExp.V y), s) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter" by (simp add: AssignI')
    have aux2: "(''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1), ?inter) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" by (simp add: AssignI')
    have "(?w_com, s) \<Rightarrow>\<^bsup> 4 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" using aux1 aux2 by (simp add: Seq)
    hence aux3: "t = ?inter(''pc'' := ?inter ''pc'' + 1)" using ADD V assms(2) by auto

    have "iexec (x += tmp) (pc, s') = (pc + 1, s'(x :=  s' x + s' y))" by (simp add: V)
    hence aux4: "t' = s'(x :=  s' x + s' y)" using ADD assms(3) by auto

    let ?inter' = "s'(x := s' x + s' y)"
    have "\<forall>z \<noteq> ''pc''. ?inter z = ?inter' z" using ADD V assms(1) assms(5) by auto
    thus ?thesis using aux3 aux4 by simp
  qed
next
  case (SUB x tmp)
  then show ?thesis
  proof (cases tmp)
    case (N c)
    let ?inter = "s(x := s x - c)"
    let ?final = "?inter(''pc'' := ?inter ''pc'' + 1)"
    let ?w_com = "x ::= (atomExp.V x \<ominus> atomExp.N c) ;; ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)"
    have aux1: "(x ::= (atomExp.V x \<ominus> atomExp.N c), s) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter" by (simp add: AssignI')
    have aux2: "(''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1), ?inter) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" by (simp add: AssignI')
    have "(?w_com, s) \<Rightarrow>\<^bsup> 4 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" using aux1 aux2 by (simp add: Seq)
    hence aux3: "t = ?inter(''pc'' := ?inter ''pc'' + 1)" using SUB N assms(2) by auto

    have "iexec (x -= tmp) (pc, s') = (pc + 1, s'(x :=  s' x - c))" by (simp add: N)
    hence aux4: "t' = s'(x :=  s' x - c)" using SUB assms(3) by auto

    show ?thesis using aux3 aux4 by (simp add: assms(5))
  next
    case (V y)
    let ?inter = "s(x := s x - s y)"
    let ?final = "?inter(''pc'' := ?inter ''pc'' + 1)"
    let ?w_com = "x ::= (atomExp.V x \<ominus> atomExp.V y) ;; ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)"
    have aux1: "(x ::= (atomExp.V x \<ominus> atomExp.V y), s) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter" by (simp add: AssignI')
    have aux2: "(''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1), ?inter) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" by (simp add: AssignI')
    have "(?w_com, s) \<Rightarrow>\<^bsup> 4 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" using aux1 aux2 by (simp add: Seq)
    hence aux3: "t = ?inter(''pc'' := ?inter ''pc'' + 1)" using SUB V assms(2) by auto

    have "iexec (x -= tmp) (pc, s') = (pc + 1, s'(x :=  s' x - s' y))" by (simp add: V)
    hence aux4: "t' = s'(x :=  s' x - s' y)" using SUB assms(3) by auto
    
    let ?inter' = "s'(x := s' x - s' y)"
    have "\<forall>z \<noteq> ''pc''. ?inter z = ?inter' z" using SUB V assms(1) assms(5) by auto
    thus ?thesis using aux3 aux4 by simp
  qed
next
  case (RSH x)
  let ?inter = "s(x := s x div 2)"
  let ?final = "?inter(''pc'' := ?inter ''pc'' + 1)"
  let ?w_com = "x ::= (atomExp.V x \<then>) ;; ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)"
  have aux1: "(x ::= (atomExp.V x \<then>), s) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter" by (simp add: AssignI')
  have aux2: "(''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1), ?inter) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" by (simp add: AssignI')
  have "(?w_com, s) \<Rightarrow>\<^bsup> 4 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" using aux1 aux2 by (simp add: Seq)
  hence aux3: "t = ?inter(''pc'' := ?inter ''pc'' + 1)" using RSH assms(2) by auto

  have "iexec (x \<bind>1) (pc, s') = (pc + 1, s'(x :=  s' x div 2))" by simp
  hence aux4: "t' = s'(x :=  s' x div 2)" using RSH assms(3) by auto
  
  show ?thesis using aux3 aux4 by (simp add: assms(5))
next
  case (MOD x)
  let ?inter = "s(x := s x mod 2)"
  let ?final = "?inter(''pc'' := ?inter ''pc'' + 1)"
  let ?w_com = "x ::= (atomExp.V x \<doteq>1) ;; ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)"
  have aux1: "(x ::= (atomExp.V x \<doteq>1), s) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter" by (simp add: AssignI')
  have aux2: "(''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1), ?inter) \<Rightarrow>\<^bsup> 2 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" by (simp add: AssignI')
  have "(?w_com, s) \<Rightarrow>\<^bsup> 4 \<^esup> ?inter(''pc'' := ?inter ''pc'' + 1)" using aux1 aux2 by (simp add: Seq)
  hence aux3: "t = ?inter(''pc'' := ?inter ''pc'' + 1)" using MOD assms(2) by auto

  have "iexec (x %=2) (pc, s') = (pc + 1, s'(x :=  s' x mod 2))" by simp
  hence aux4: "t' = s'(x :=  s' x mod 2)" using MOD assms(3) by auto
  
  show ?thesis using aux3 aux4 by (simp add: assms(5))
next
  case (JMP i)
  have "(''pc'' ::= A (atomExp.N i), s) \<Rightarrow>\<^bsup> 2 \<^esup> s(''pc'' := i)" by (simp add: AssignI')
  hence aux1: "t = s(''pc'' := i)" using JMP assms(2) by auto

  have "iexec (GOTO i) (pc, s') = (i, s')" by simp
  hence aux2: "t' = s'" using JMP assms(3) by auto

  show ?thesis using aux1 aux2 by (simp add: assms(5))
next
  case (CONDJMP x i)
  let ?w_com = "IF x\<noteq>0 THEN ''pc'' ::= A (atomExp.N i) ELSE ''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1)"
  consider (c1) "s x = 0" | (c2) "s x > 0" by auto
  then show ?thesis
  proof (cases)
    case c1
    have "(''pc'' ::= (atomExp.V ''pc'' \<oplus> atomExp.N 1), s) \<Rightarrow>\<^bsup> 2 \<^esup> s(''pc'' := s ''pc'' + 1)" by (simp add: AssignI')
    hence "(?w_com, s) \<Rightarrow>\<^bsup> 3 \<^esup> s(''pc'' := s ''pc'' + 1)" by (simp add: big_step_t.IfFalse c1)
    hence aux1: "t = s(''pc'' := s ''pc'' + 1)" using CONDJMP assms(2) by auto

    have "iexec (IF x\<noteq>0 THEN GOTO i) (pc, s') = (pc + 1, s')" using c1 CONDJMP assms(1) assms(5) by auto
    hence aux2: "t' = s'" using CONDJMP assms(3) by auto

    show ?thesis using aux1 aux2 by (simp add: assms(5))
  next
    case c2
    have "(''pc'' ::= A (atomExp.N i), s) \<Rightarrow>\<^bsup> 2 \<^esup> s(''pc'' := i)" by (simp add: AssignI')
    hence "(?w_com, s) \<Rightarrow>\<^bsup> 3 \<^esup> s(''pc'' := i)" by (simp add: big_step_t.IfTrue c2)
    hence aux1: "t = s(''pc'' := i)" using CONDJMP assms(2) fun_upd_eqD by fastforce

    have "iexec (IF x\<noteq>0 THEN GOTO i) (pc, s') = (i, s')" using CONDJMP assms(1) assms(5) c2 by auto
    hence aux2: "t' = s'" using CONDJMP assms(3) by auto

    show ?thesis using aux1 aux2 by (simp add: assms(5))
  qed
qed

theorem single_instr_consist: 
  assumes "well_defined_instr instr"
    and "(GOTO_Instr_to_WHILE instr, s) \<Rightarrow>\<^bsup> k \<^esup> t"
    and "iexec instr (pc, s') = (pc', t')" 
    and "s ''pc'' = pc" and "\<forall>x \<noteq> ''pc''. s x = s' x"
  shows "t ''pc'' = pc'" and "\<forall>x \<noteq> ''pc''. t x = t' x" 
  using assms(1) assms(2) assms(3) assms(4) assms(5) instr_pc_consist apply auto[1]
  using assms(1) assms(2) assms(3) assms(4) assms(5) instr_var_consist by presburger

lemma "(GOTO_Instr_to_WHILE HALT, s) \<Rightarrow>\<^bsup> 2 \<^esup> t" using instr_halt_complexity sorry

theorem instr_halt:
  assumes "well_defined_instr HALT"
  and "iexec HALT (pc, s') = (pc', t')"
  and "s ''pc'' = pc" and "\<forall>x \<noteq> ''pc''. s x = s' x"
  shows "\<exists>t. ((GOTO_Instr_to_WHILE HALT, s) \<Rightarrow>\<^bsup> 2 \<^esup> t) \<and> (t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using assms
proof -
  have "\<exists>t. (GOTO_Instr_to_WHILE HALT, s) \<Rightarrow>\<^bsup> 2 \<^esup> t" using instr_halt_complexity by blast
  then obtain t where aux: "(GOTO_Instr_to_WHILE HALT, s) \<Rightarrow>\<^bsup> 2 \<^esup> t" by blast
  hence "(t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using assms by (meson instr_pc_consist instr_var_consist) 
  thus "\<exists>t. ((GOTO_Instr_to_WHILE HALT, s) \<Rightarrow>\<^bsup> 2 \<^esup> t) \<and> (t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using aux by blast
qed

lemma instr_complexity_halt':
  "(GOTO_Instr_to_WHILE HALT, s) \<Rightarrow>\<^bsup> k \<^esup> t \<Longrightarrow> k = 2" by (meson bigstep_det instr_halt_complexity)

theorem instr_assign:
  assumes "well_defined_instr (x ;;= c)"
  and "iexec (x ;;= c) (pc, s') = (pc', t')"
  and "s ''pc'' = pc" and "\<forall>x \<noteq> ''pc''. s x = s' x"
  shows "\<exists>t. ((GOTO_Instr_to_WHILE (x ;;= c), s) \<Rightarrow>\<^bsup> 4 \<^esup> t) \<and> (t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using assms
proof -
  have "\<exists>t. (GOTO_Instr_to_WHILE (x ;;= c), s) \<Rightarrow>\<^bsup> 4 \<^esup> t" using instr_assign_complexity by blast
  then obtain t where aux: "(GOTO_Instr_to_WHILE (x ;;= c), s) \<Rightarrow>\<^bsup> 4 \<^esup> t" by blast
  hence "(t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using assms by (meson instr_pc_consist instr_var_consist) 
  thus "\<exists>t. ((GOTO_Instr_to_WHILE (x ;;= c), s) \<Rightarrow>\<^bsup> 4 \<^esup> t) \<and> (t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using aux by blast
qed

lemma instr_complexity_assign':
  "(GOTO_Instr_to_WHILE (x ;;= c), s) \<Rightarrow>\<^bsup> k \<^esup> t \<Longrightarrow> k = 4" by (meson bigstep_det instr_assign_complexity)

theorem instr_add:
  assumes "well_defined_instr (x += c)"
  and "iexec (x += c) (pc, s') = (pc', t')"
  and "s ''pc'' = pc" and "\<forall>x \<noteq> ''pc''. s x = s' x"
  shows "\<exists>t. ((GOTO_Instr_to_WHILE (x += c), s) \<Rightarrow>\<^bsup> 4 \<^esup> t) \<and> (t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using assms
proof -
  have "\<exists>t. (GOTO_Instr_to_WHILE (x += c), s) \<Rightarrow>\<^bsup> 4 \<^esup> t" using instr_add_complexity by blast
  then obtain t where aux: "(GOTO_Instr_to_WHILE (x += c), s) \<Rightarrow>\<^bsup> 4 \<^esup> t" by blast
  hence "(t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using assms by (meson instr_pc_consist instr_var_consist) 
  thus "\<exists>t. ((GOTO_Instr_to_WHILE (x += c), s) \<Rightarrow>\<^bsup> 4 \<^esup> t) \<and> (t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using aux by blast
qed

lemma instr_complexity_add':
  "(GOTO_Instr_to_WHILE (x += c), s) \<Rightarrow>\<^bsup> k \<^esup> t \<Longrightarrow> k = 4" by (meson bigstep_det instr_add_complexity)

theorem instr_sub:
  assumes "well_defined_instr (x -= c)"
  and "iexec (x -= c) (pc, s') = (pc', t')"
  and "s ''pc'' = pc" and "\<forall>x \<noteq> ''pc''. s x = s' x"
  shows "\<exists>t. ((GOTO_Instr_to_WHILE (x -= c), s) \<Rightarrow>\<^bsup> 4 \<^esup> t) \<and> (t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using assms
proof -
  have "\<exists>t. (GOTO_Instr_to_WHILE (x -= c), s) \<Rightarrow>\<^bsup> 4 \<^esup> t" using instr_sub_complexity by blast
  then obtain t where aux: "(GOTO_Instr_to_WHILE (x -= c), s) \<Rightarrow>\<^bsup> 4 \<^esup> t" by blast
  hence "(t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using assms by (meson instr_pc_consist instr_var_consist) 
  thus "\<exists>t. ((GOTO_Instr_to_WHILE (x -= c), s) \<Rightarrow>\<^bsup> 4 \<^esup> t) \<and> (t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using aux by blast
qed

lemma instr_complexity_sub':
  "(GOTO_Instr_to_WHILE (x -= c), s) \<Rightarrow>\<^bsup> k \<^esup> t \<Longrightarrow> k = 4" by (meson bigstep_det instr_sub_complexity)

theorem instr_right_shift:
  assumes "well_defined_instr (x \<bind>1)"
  and "iexec (x \<bind>1) (pc, s') = (pc', t')"
  and "s ''pc'' = pc" and "\<forall>x \<noteq> ''pc''. s x = s' x"
  shows "\<exists>t. ((GOTO_Instr_to_WHILE (x \<bind>1), s) \<Rightarrow>\<^bsup> 4 \<^esup> t) \<and> (t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using assms
proof -
  have "\<exists>t. (GOTO_Instr_to_WHILE (x \<bind>1), s) \<Rightarrow>\<^bsup> 4 \<^esup> t" using instr_right_shift_complexity by blast
  then obtain t where aux: "(GOTO_Instr_to_WHILE (x \<bind>1), s) \<Rightarrow>\<^bsup> 4 \<^esup> t" by blast
  hence "(t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using assms by (meson instr_pc_consist instr_var_consist) 
  thus "\<exists>t. ((GOTO_Instr_to_WHILE (x \<bind>1), s) \<Rightarrow>\<^bsup> 4 \<^esup> t) \<and> (t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using aux by blast
qed

lemma instr_complexity_right_shift':
  "(GOTO_Instr_to_WHILE (x \<bind>1), s) \<Rightarrow>\<^bsup> k \<^esup> t \<Longrightarrow> k = 4" by (meson bigstep_det instr_right_shift_complexity)

theorem instr_left_shift:
  assumes "well_defined_instr (x %=2)"
  and "iexec (x %=2) (pc, s') = (pc', t')"
  and "s ''pc'' = pc" and "\<forall>x \<noteq> ''pc''. s x = s' x"
  shows "\<exists>t. ((GOTO_Instr_to_WHILE (x %=2), s) \<Rightarrow>\<^bsup> 4 \<^esup> t) \<and> (t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using assms
proof -
  have "\<exists>t. (GOTO_Instr_to_WHILE (x %=2), s) \<Rightarrow>\<^bsup> 4 \<^esup> t" using instr_left_shift_complexity by blast
  then obtain t where aux: "(GOTO_Instr_to_WHILE (x %=2), s) \<Rightarrow>\<^bsup> 4 \<^esup> t" by blast
  hence "(t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using assms by (meson instr_pc_consist instr_var_consist) 
  thus "\<exists>t. ((GOTO_Instr_to_WHILE (x %=2), s) \<Rightarrow>\<^bsup> 4 \<^esup> t) \<and> (t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using aux by blast
qed

lemma instr_complexity_left_shift':
  "(GOTO_Instr_to_WHILE (x %=2), s) \<Rightarrow>\<^bsup> k \<^esup> t \<Longrightarrow> k = 4" by (meson bigstep_det instr_left_shift_complexity)

theorem instr_jump:
  assumes "well_defined_instr (GOTO i)"
  and "iexec (GOTO i) (pc, s') = (pc', t')"
  and "s ''pc'' = pc" and "\<forall>x \<noteq> ''pc''. s x = s' x"
  shows "\<exists>t. ((GOTO_Instr_to_WHILE (GOTO i), s) \<Rightarrow>\<^bsup> 2 \<^esup> t) \<and> (t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using assms
proof -
  have "\<exists>t. (GOTO_Instr_to_WHILE (GOTO i), s) \<Rightarrow>\<^bsup> 2 \<^esup> t" using instr_jump_complexity by blast
  then obtain t where aux: "(GOTO_Instr_to_WHILE (GOTO i), s) \<Rightarrow>\<^bsup> 2 \<^esup> t" by blast
  hence "(t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using assms by (meson instr_pc_consist instr_var_consist) 
  thus "\<exists>t. ((GOTO_Instr_to_WHILE (GOTO i), s) \<Rightarrow>\<^bsup> 2 \<^esup> t) \<and> (t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using aux by blast
qed

lemma instr_complexity_jump':
  "(GOTO_Instr_to_WHILE (GOTO i), s) \<Rightarrow>\<^bsup> k \<^esup> t \<Longrightarrow> k = 2" by (meson bigstep_det instr_jump_complexity)

theorem instr_cond_jump:
  assumes "well_defined_instr (IF x\<noteq>0 THEN GOTO i)"
  and "iexec (IF x\<noteq>0 THEN GOTO i) (pc, s') = (pc', t')"
  and "s ''pc'' = pc" and "\<forall>x \<noteq> ''pc''. s x = s' x"
  shows "\<exists>t. ((GOTO_Instr_to_WHILE (IF x\<noteq>0 THEN GOTO i), s) \<Rightarrow>\<^bsup> 3 \<^esup> t) \<and> (t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using assms
proof -
  have "\<exists>t. (GOTO_Instr_to_WHILE (IF x\<noteq>0 THEN GOTO i), s) \<Rightarrow>\<^bsup> 3 \<^esup> t" using instr_cond_jump_complexity by blast
  then obtain t where aux: "(GOTO_Instr_to_WHILE (IF x\<noteq>0 THEN GOTO i), s) \<Rightarrow>\<^bsup> 3 \<^esup> t" by blast
  hence "(t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using assms by (meson instr_pc_consist instr_var_consist) 
  thus "\<exists>t. ((GOTO_Instr_to_WHILE (IF x\<noteq>0 THEN GOTO i), s) \<Rightarrow>\<^bsup> 3 \<^esup> t) \<and> (t ''pc'' = pc') \<and> (\<forall>x \<noteq> ''pc''. t x = t' x)" using aux by blast
qed

lemma instr_complexity_cond_jump':
  "(GOTO_Instr_to_WHILE (IF x\<noteq>0 THEN GOTO i), s) \<Rightarrow>\<^bsup> k \<^esup> t \<Longrightarrow> k = 3" by (meson bigstep_det instr_cond_jump_complexity)

end