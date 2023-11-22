
theory Big_StepT_Ex
  imports Big_StepT "~~/src/HOL/Library/Simps_Case_Conv"
begin

function (sequential, domintros) big_step_function :: "(com \<times> state) \<Rightarrow> (nat \<times> state)" where
  "big_step_function (SKIP,s) = (1, s)" |
  "big_step_function (x ::= a,s) = (2, s(x := aval a s))" |
  "big_step_function (c1;;c2, s) =
    (let (n1, s1) = big_step_function (c1, s);
        (n2, s2) = big_step_function (c2, s1)
    in (n1+n2, s2))" |
  "big_step_function (IF b \<noteq>0 THEN c1 ELSE c2, s) = 
    apfst Suc (if s b \<noteq> 0 then big_step_function (c1,s) else big_step_function (c2,s))" |
  "big_step_function (WHILE b \<noteq>0 DO c,s) = (if s b \<noteq> 0 then apfst Suc (big_step_function (c;; WHILE b \<noteq>0 DO c, s)) else (2, s))" 
  by pat_completeness auto

print_theorems
(* Soundness and partial termination *)
lemma "(c,s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> big_step_function_dom (c,s) \<and> big_step_function (c,s) = (t, s')"
proof (induction s t s' rule: big_step_t_induct)
  case (Seq c1 s1 x s2 c2 y s3 z)
  then show ?case 
      apply (subst big_step_function.psimps)
     apply (auto intro: big_step_function.domintros simp add: Let_def big_step_function.domintros big_step_function.psimps)
    done (* ? ? ? *)
next
  case (WhileTrue s1 b c x s2 y s3 z)
  show ?case
    apply (rule conjI)
    using WhileTrue.IH(1) WhileTrue.IH(2) big_step_function.domintros(3) big_step_function.domintros(5) apply fastforce
    apply (subst big_step_function.psimps)
    using WhileTrue.IH(1) WhileTrue.IH(2) big_step_function.domintros(3) big_step_function.domintros(5) apply force
    apply (split if_split)
    apply safe
      apply (subst big_step_function.psimps)
       apply (rule big_step_function.domintros)
    using WhileTrue.IH(1) apply blast
    apply (simp add: WhileTrue.IH(1) WhileTrue.IH(2))
      apply (unfold Let_def)
    using WhileTrue.IH(1) WhileTrue.IH(2) WhileTrue.hyps(4) 
      apply (auto split: prod.splits)[]
    using WhileTrue.hyps(1) apply blast+
    done (* TODO: Do properly *)
qed (auto intro: big_step_function.domintros simp add: Let_def big_step_function.domintros big_step_function.psimps)

(* Partial completeness? *)
  
(* Total termination not possible (WHILE b\<noteq>0 DO b ::= b+1). Therefore sadly no code equations *)

(* Instead, explicitly partial function: . Bunch of stupid mono rules as I cannot be bothered
  to understand what exactly the problem is*)


lemma mono1[partial_function_mono]: "monotone option.le_fun option_ord
          (\<lambda>big_step_ex. map_option (apfst ((+) aa)) (big_step_ex (x32, ba)))" 
  by (smt (verit, best) flat_ord_def fun_ord_def monotoneI option.map_disc_iff)
lemma "monotone option.le_fun option_ord
          (\<lambda>big_step_ex.
              map_option (apfst Suc)
               (if b x41 \<noteq> 0 then big_step_ex (x42, b) else big_step_ex (x43, b)))"
  by (smt (verit, best) flat_ord_def fun_ord_def monotoneI option.map_disc_iff)
lemma mono2[partial_function_mono]:"
         monotone option.le_fun option_ord
          (\<lambda>f. map_option (apfst Suc) (f (x52;; WHILE x51\<noteq>0 DO x52, b)))"
  by (smt (verit, best) flat_ord_def fun_ord_def monotoneI option.map_disc_iff)
lemma mono3[partial_function_mono]:"
  (\<And>x a b x41 x42 x43.
      monotone option.le_fun option_ord
       (\<lambda>big_step_ex.
           map_option (apfst Suc)
            (if b x41 \<noteq> 0 then big_step_ex (x42, b) else big_step_ex (x43, b)))) \<Longrightarrow>
  (\<And>x a b x51 x52.
      monotone option.le_fun option_ord
       (\<lambda>f. map_option (apfst Suc) (f (x52;; WHILE x51\<noteq>0 DO x52, b)))) \<Longrightarrow>
  (\<And>x. monotone option.le_fun option_ord
         (\<lambda>big_step_ex.
             case x of (SKIP, s) \<Rightarrow> Some (1, s) | (x ::= a, s) \<Rightarrow> Some (2, s(x := aval a s))
             | (c1;; c2, s) \<Rightarrow>
                 Option.bind (big_step_ex (c1, s))
                  (\<lambda>(n, s). map_option (apfst ((+) n)) (big_step_ex (c2, s)))
             | (IF b\<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>
                 map_option (apfst Suc)
                  (if s b \<noteq> 0 then big_step_ex (c1, s) else big_step_ex (c2, s))
             | (WHILE b\<noteq>0 DO c, s) \<Rightarrow>
                 if s b \<noteq> 0 then map_option (apfst Suc) (big_step_ex (c;; WHILE b\<noteq>0 DO c, s))
                 else Some (2, s)))"
  apply (auto split: prod.splits com.splits option.splits simp add: flat_ord_def fun_ord_def monotone_def)
  apply (smt (verit) bind.bind_lunit bind_eq_None_conv old.prod.case option.collapse option.map_disc_iff split_cong)
  apply (smt (verit) bind.bind_lunit bind_eq_None_conv old.prod.case option.collapse option.map_disc_iff split_cong)
  apply (smt (verit) bind.bind_lunit bind_eq_None_conv old.prod.case option.collapse option.map_disc_iff split_cong)
  apply (smt (verit) bind.bind_lunit bind_eq_None_conv old.prod.case option.collapse option.map_disc_iff split_cong)
  done
lemma mono4[partial_function_mono]: "monotone option.le_fun option_ord
          (\<lambda>big_step_ex.
              map_option (apfst Suc)
               (if b x41 \<noteq> 0 then big_step_ex (x42, b) else big_step_ex (x43, b)))"
  by (smt (verit, best) flat_ord_def fun_ord_def monotoneI option.map_disc_iff)

partial_function (option) big_step_ex :: "(com\<times> state) \<Rightarrow> (nat \<times> state) option" where
  "big_step_ex cs = (case cs of (SKIP,s) \<Rightarrow> Some (1, s) | (x ::= a,s) \<Rightarrow> Some (2, s(x := aval a s))
    | (c1;;c2, s1) \<Rightarrow> Option.bind (big_step_ex (c1,s1)) (\<lambda>(n, s). map_option (apfst (\<lambda>n'. n+n')) (big_step_ex (c2, s)))
    | (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow> map_option (apfst Suc) (if s b \<noteq> 0 then big_step_ex (c1,s) else big_step_ex (c2,s))
    | (WHILE b \<noteq>0 DO c,s) \<Rightarrow> (if s b \<noteq> 0 then map_option (apfst Suc) (big_step_ex (c;; WHILE b \<noteq>0 DO c, s)) else Some (2, s)))"
    
thm big_step_ex.simps
simps_of_case big_step_ex_simps[simp,code]: big_step_ex.simps

lemma big_step_ex_sound:"(c,s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> big_step_ex (c,s) = Some (t, s')"
  by (induction s t s' rule: big_step_t_induct) auto

end