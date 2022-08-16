
(* Name is wrong, we do not have time here. 
  But I should probably add it...
*)

theory Big_StepT_Ex
  imports Big_StepT "~~/src/HOL/Library/Simps_Case_Conv"
begin
function (sequential, domintros) big_step_function :: "(com \<times> state) \<Rightarrow> state" where
  "big_step_function (SKIP,s) = s" |
  "big_step_function (x ::= a,s) = s(x := aval a s)" |
  "big_step_function (c1;;c2, s1) = big_step_function (c2, big_step_function (c1,s1))" |
  "big_step_function (IF b \<noteq>0 THEN c1 ELSE c2, s) = (if s b \<noteq> 0 then big_step_function (c1,s) else big_step_function (c2,s))" |
  "big_step_function (WHILE b \<noteq>0 DO c,s) = (if s b \<noteq> 0 then big_step_function (c;; WHILE b \<noteq>0 DO c, s) else s)" 
  by pat_completeness auto

print_theorems
(* Soundness and partial termination *)
lemma "(c,s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> big_step_function_dom (c,s) \<and> big_step_function (c,s) = s'"
  by (induction s t s' rule: big_step_t_induct) 
    (auto simp add: big_step_function.domintros big_step_function.psimps)

(* Partial completeness? *)
  
(* Total termination not possible (WHILE b\<noteq>0 DO b ::= b+1). Therefore sadly no code equations *)

(* Instead, explicitly partial function: *)

partial_function (option) big_step_ex :: "(com\<times> state) \<Rightarrow> state option" where
  "big_step_ex cs = (case cs of (SKIP,s) \<Rightarrow> Some s | (x ::= a,s) \<Rightarrow> Some (s(x := aval a s))
    | (c1;;c2, s1) \<Rightarrow> Option.bind (big_step_ex (c1,s1)) (\<lambda>s. big_step_ex (c2, s))
    | (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow> (if s b \<noteq> 0 then big_step_ex (c1,s) else big_step_ex (c2,s))
    | (WHILE b \<noteq>0 DO c,s) \<Rightarrow> (if s b \<noteq> 0 then big_step_ex (c;; WHILE b \<noteq>0 DO c, s) else Some s))"

thm big_step_ex.simps
simps_of_case big_step_ex_simps[simp,code]: big_step_ex.simps

lemma big_step_ex_sound:"(c,s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> big_step_ex (c,s) = Some s'"
  by (induction s t s' rule: big_step_t_induct) auto

(* Horrible completeness proof *)

lemma WhileTrue': "\<lbrakk> s1 b \<noteq> 0; (c;; WHILE b \<noteq>0 DO c, s1) \<Rightarrow>\<^bsup> y \<^esup> s3; 1+y=z  \<rbrakk> 
    \<Longrightarrow> (WHILE b \<noteq>0 DO c, s1) \<Rightarrow>\<^bsup> z \<^esup> s3" by auto
lemma WhileFalse': "\<lbrakk> s b = 0; s=s' \<rbrakk> \<Longrightarrow> (WHILE b \<noteq>0 DO c,s) \<Rightarrow>\<^bsup> Suc (Suc 0) \<^esup> s'"
  by auto

lemma assumes"big_step_ex (c,s) = Some s'" shows "\<exists>t . (c,s) \<Rightarrow>\<^bsup>t\<^esup> s'"
proof (induction arbitrary: t rule: big_step_ex.raw_induct[OF _ assms])
  case (1 big_step_ex cs csa)
  obtain c s where cs[simp]: "cs = (c,s)" by force

  consider "c = SKIP" "s = csa" 
    | x a where "c = (x ::= a)" "csa = (s(x := aval a s))"
    | c1 c2 where "c = (c1;; c2)" "Some csa = Option.bind (big_step_ex (c1, s)) (\<lambda>s. big_step_ex (c2, s))"
    | b c1 c2 where "c = (IF b\<noteq>0 THEN c1 ELSE c2)" 
      "Some csa = (if s b \<noteq> 0 then big_step_ex (c1, s) else big_step_ex (c2, s))"
    | b cb where  "c = (WHILE b\<noteq>0 DO cb)" 
        "Some csa = (if s b \<noteq> 0 then big_step_ex (cb;; WHILE b\<noteq>0 DO cb, s) else Some s)"
    using 1(2) 
    by (smt (verit, del_insts) case_prod_conv com.exhaust com.simps(25) com.simps(26) com.simps(27) com.simps(28) com.simps(29) cs option.inject)

  then show ?case
  proof(cases)
    case 1
    then show ?thesis by simp
  next
    case 2
    show ?thesis 
      apply (subst cs) apply (subst 2(1)) apply (subst 2(2)) apply (rule exI) 
      by (rule big_step_t.Assign)
  next
    case 3
    obtain s' where step: "big_step_ex (c1, s) = Some s'" "big_step_ex (c2, s') = Some csa"
      using "3"(2) by fastforce
    show ?thesis 
      apply (rule exI) apply (subst cs) apply (subst 3(1))
      apply (rule Seq'[of _  _ _ s'])
      using 1(1)[OF step(1)] apply (rule exE_some) apply simp
      using 1(1)[OF step(2)] apply (rule exE_some) apply simp
      done
  next
    case 4
    have t: "big_step_ex (c1, s) = Some csa" if "s b \<noteq> 0"
      by (simp add: "4"(2) that)
    have f: "big_step_ex (c2, s) = Some csa" if "s b = 0"
      by (simp add: "4"(2) that)
    show ?thesis 
    proof(subst cs, subst 4(1), cases "s b \<noteq> 0")
      case True
      show "\<exists>t. (IF b\<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> t \<^esup> csa" 
        apply (rule exI) apply (rule big_step_t.IfTrue)
          apply (fact True)
        using 1(1)[OF t, OF True] apply (rule exE_some) apply simp
        by simp
    next
      case False
      hence F: "s b = 0" by simp
      show "\<exists>t. (IF b\<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> t \<^esup> csa" 
        apply (rule exI) apply (rule big_step_t.IfFalse)
          apply (fact F)
        using 1(1)[OF f, OF F] apply (rule exE_some) apply simp
        by simp
    qed
  next
    case 5
    then show ?thesis
    proof(cases "s b \<noteq> 0")
      case True
      hence u: "big_step_ex (cb;; WHILE b\<noteq>0 DO cb, s) = Some csa"
        using "5"(2) by force
      show ?thesis apply (rule exI) apply (subst cs) apply (subst 5)
        apply (rule WhileTrue')
          apply (fact True)
        using 1(1)[OF u] apply (rule exE_some) apply simp
        by simp
    next
      case False
      hence False: "s b = 0" by simp
      show ?thesis apply (rule exI) apply (subst cs) apply (subst 5)
         apply (rule WhileFalse')
         apply (fact False)
        using "5"(2)
        by (metis False option.inject)
    
    qed
  qed
qed

end