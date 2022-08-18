theory Utilities
  imports
    IMP_Minus.Call_By_Prefixes
    IMP_Minus.Com
begin


lemma Seq_E:
  "\<lbrakk>(c1;; c2, s1) \<Rightarrow>\<^bsup> p \<^esup> s3; \<And>x s2 y. \<lbrakk>(c1, s1) \<Rightarrow>\<^bsup> x \<^esup> s2; (c2, s2) \<Rightarrow>\<^bsup> y \<^esup> s3\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by blast
thm If_tE[where ?x=y]

lemma If_E:
  "\<lbrakk>(IF b\<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> y \<^esup> t; \<And>x. \<lbrakk>0 < s b; (c1, s) \<Rightarrow>\<^bsup> x \<^esup> t\<rbrakk> \<Longrightarrow> P;
    \<And>x. \<lbrakk>s b = 0; (c2, s) \<Rightarrow>\<^bsup> x \<^esup> t\<rbrakk> \<Longrightarrow> P\<rbrakk>
  \<Longrightarrow> P"
  by blast


method fastforce_sorted_premises uses simp =
  (match premises in
    var_doesnt_change[thin]: "\<And>x. x \<in>  _ \<Longrightarrow> _ (_ x) = _ (_ x)"(multi)
    \<Rightarrow> \<open>match premises in
        subroutine_results[thin]: "_ (add_prefix (add_prefix p _) _) = _" (multi) for p
          \<Rightarrow> \<open>match premises in
            assignments[thin]: "((add_prefix p1 _) ::= _, _) \<Rightarrow>\<^bsup> _ \<^esup> _" (multi) for p1
              \<Rightarrow> \<open>match premises in
                while_cond[thin]: "_ < _ (add_prefix p2 _)" (multi) for p2
                  \<Rightarrow> \<open>match premises in
                    invoke[thin]: "(invoke_subprogram p3 _, _) \<Rightarrow>\<^bsup> _ \<^esup> _" (multi) for p3
                      \<Rightarrow> \<open>match premises in
                        remaining[thin]: "_" (multi)
                          \<Rightarrow> \<open>insert var_doesnt_change subroutine_results while_cond invoke,
                             (fastforce simp add: assignments[THEN AssignD, simplified]
                                remaining simp)\<close>\<close>\<close>\<close>\<close>\<close>)

method fastforce_sorted_premises2 uses simp =
  (((drule AssignD)+, (erule conjE)+)?,
    (match premises in
      var_doesnt_change[thin]:"\<And>v. v \<in>  _ \<Longrightarrow> _ (add_prefix p1 v) = _ (add_prefix p1 v)"(multi) for p1
      \<Rightarrow> \<open>match premises in
              subroutine_results[thin]: "_ (add_prefix (add_prefix p _) _) = _" (multi) for p
                \<Rightarrow> \<open>match premises in
                    assignments[thin]: "_ = _(_ :=_)" (multi)
                      \<Rightarrow> \<open>match premises in
                          cond[thin]: "_ < _ " (multi)
                            \<Rightarrow> \<open>match premises in
                                invoke[thin]: "(invoke_subprogram p3 _, _) \<Rightarrow>\<^bsup> _ \<^esup> _" (multi) for p3
                                  \<Rightarrow> \<open>match premises in
                                      remaining[thin]: "_" (multi)
                                        \<Rightarrow> \<open>insert var_doesnt_change subroutine_results cond invoke
                                            remaining, fastforce simp: assignments simp\<close>\<close>
                                \<bar>remaining[thin]: "_" (multi)
                                  \<Rightarrow> \<open>insert var_doesnt_change subroutine_results cond remaining,
                                      fastforce simp: assignments simp\<close>\<close>
                          \<bar>invoke[thin]: "(invoke_subprogram p3 _, _) \<Rightarrow>\<^bsup> _ \<^esup> _" (multi) for p3
                            \<Rightarrow> \<open>match premises in
                                remaining[thin]:"_" (multi)
                                  \<Rightarrow> \<open>insert var_doesnt_change subroutine_results invoke remaining,
                                      fastforce simp: assignments simp\<close>\<close>
                          \<bar>remaining[thin]:"_" (multi)
                                    \<Rightarrow> \<open>insert var_doesnt_change subroutine_results remaining,
                                        fastforce simp: assignments simp\<close>\<close>\<close>\<close>))

method force_sorted_premises uses simp =
  (match premises in
    var_doesnt_change[thin]: "\<And>x. x \<in>  _ \<Longrightarrow> _ (_ x) = _ (_ x)"(multi)
    \<Rightarrow> \<open>match premises in
        subroutine_results[thin]: "_ (add_prefix (add_prefix p _) _) = _" (multi) for p
          \<Rightarrow> \<open>match premises in
            assignments[thin]: "((add_prefix p1 _) ::= _, _) \<Rightarrow>\<^bsup> _ \<^esup> _" (multi) for p1
              \<Rightarrow> \<open>match premises in
                while_cond[thin]: "_ < _ (add_prefix p2 _)" (multi) for p2
                  \<Rightarrow> \<open>match premises in
                    invoke[thin]: "(invoke_subprogram p3 _, _) \<Rightarrow>\<^bsup> _ \<^esup> _" (multi) for p3
                      \<Rightarrow> \<open>match premises in
                        remaining[thin]: "_" (multi)
                          \<Rightarrow> \<open>insert var_doesnt_change subroutine_results while_cond invoke,
                             (force simp add: assignments[THEN AssignD, simplified]
                                remaining simp)\<close>\<close>\<close>\<close>\<close>\<close>)

method sort_premises =
  (match premises in
    var_doesnt_change[thin]: "\<And>x. x \<in>  _ \<Longrightarrow> _ (_ x) = _ (_ x)"(multi)
    \<Rightarrow> \<open>match premises in
        subroutine_results[thin]: "_ (add_prefix (add_prefix p _) _) = _" (multi) for p
          \<Rightarrow> \<open>match premises in
            assignments[thin]: "((add_prefix p1 _) ::= _, _) \<Rightarrow>\<^bsup> _ \<^esup> _" (multi) for p1
              \<Rightarrow> \<open>match premises in
                while_cond[thin]: "_ < _ (add_prefix p2 _)" (multi) for p2
                  \<Rightarrow> \<open>match premises in
                    invoke[thin]: "(invoke_subprogram p3 _, _) \<Rightarrow>\<^bsup> _ \<^esup> _" (multi) for p3
                      \<Rightarrow> \<open>match premises in
                    remaining[thin]: "_" (multi)
                      \<Rightarrow> \<open>insert var_doesnt_change subroutine_results while_cond invoke assignments
                          remaining\<close>\<close>\<close>\<close>\<close>\<close>)


definition "While' = Com.com.While"

notation While' ("(WHILEdummy _/\<noteq>0 DO _)"  [0, 61] 61)

lemma While_E_dummy:
  "\<lbrakk>(WHILE b\<noteq>0 DO c, s) \<Rightarrow>\<^bsup> x \<^esup> t;
    \<lbrakk>t = s; s b = 0\<rbrakk> \<Longrightarrow> P;
    \<And>x' s2 y. \<lbrakk>0 < s b; (c, s) \<Rightarrow>\<^bsup> x' \<^esup> s2;
               (WHILEdummy b\<noteq>0 DO c, s2) \<Rightarrow>\<^bsup> y \<^esup> t\<rbrakk> \<Longrightarrow> P\<rbrakk>
  \<Longrightarrow> P"
  by (auto simp: While'_def)

lemma While_tE_dummy:
  "\<lbrakk>(WHILE b\<noteq>0 DO c, s) \<Rightarrow>\<^bsup> x \<^esup> t;
  \<lbrakk>x = Suc (Suc 0); t = s; s b = 0\<rbrakk> \<Longrightarrow> P;
  \<And>x' s2 y. \<lbrakk>0 < s b; (c, s) \<Rightarrow>\<^bsup> x' \<^esup> s2;
             (WHILEdummy b\<noteq>0 DO c, s2) \<Rightarrow>\<^bsup> y \<^esup> t; x = Suc (x' + y)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: While'_def)

method while_step = (erule While_E_dummy, print_fact While_E_dummy)
method while_step_time = (erule While_tE_dummy, print_fact While_tE_dummy)
method seqt_step = (erule Seq_tE, print_fact Seq_tE)
method seq_step = (erule Seq_E, print_fact Seq_E)
method ift_step = (erule If_tE, print_fact If_tE)
method if_step = (erule If_E, print_fact If_E)
method assign_step = (drule AssignD, elim conjE, print_fact AssignD)

definition "dest_com_gen = 0"

lemma dest_com_gen: "dest_com_gen = dest_com_gen"
  by simp

named_theorems functional_correctness

method subroutine_step for vars::"char list set" =
  (match premises in foo[thin]:
    "(invoke_subprogram (add_prefix _ _) subprog, _) \<Rightarrow>\<^bsup> _ \<^esup> _" for subprog
    \<Rightarrow> \<open>match functional_correctness in invokeE[thin]:
          "\<And>(vars:: char list set). \<lbrakk>(invoke_subprogram (add_prefix _ _) subprog, _) \<Rightarrow>\<^bsup> _ \<^esup> _;
           _; _\<rbrakk> \<Longrightarrow> ?P"
            \<Rightarrow> \<open>insert foo; elim invokeE[where ?vars=vars]\<close>\<close>,
    match premises in prem: "_ \<in> vars" \<Rightarrow> \<open>insert prem, fastforce\<close>)

definition "subroutine_step = 0"

lemma subroutine_step: "subroutine_step = subroutine_step"
  by auto

method dest_com_gen' =
  (erule compose_programs_1[where ?c2.0 = "(While' _ _)"], assumption,
    erule compose_programs_2[where ?c1.0 = "(_;; While' _ _)"], assumption,
    (match premises in a[thin]:
      "(init_while_cond;;
        WHILEdummy _ \<noteq>0 DO (
          loop_body;;
          init_while_cond);;
        after_loop, _) \<Rightarrow>\<^bsup>_\<^esup> _" for init_while_cond loop_body after_loop  \<Rightarrow>
      \<open>match premises in b[thin]: "\<lbrakk>loop_cond; state_upd; _\<rbrakk> \<Longrightarrow> P"
        for loop_cond state_upd P \<Rightarrow> \<open>subst b[OF _ _ a[unfolded While'_def]]\<close>\<close>))

method dest_com_gen_time' =
  (erule compose_programs_1[where ?c2.0 = "(While' _ _)"], assumption,
    erule compose_programs_2[where ?c1.0 = "(_;; While' _ _)"], assumption,
    (match premises
      in a[thin]:
      "(init_while_cond;;
                WHILEdummy _ \<noteq>0 DO (loop_body;; init_while_cond);;
                after_loop, _) \<Rightarrow>\<^bsup>_\<^esup> _"
    for init_while_cond loop_body after_loop  \<Rightarrow>
      \<open>match premises in b[thin]: "\<lbrakk>loop_cond; state_upd; _\<rbrakk> \<Longrightarrow> P"
       for loop_cond state_upd P \<Rightarrow> \<open>subst b[OF _ _ a[unfolded While'_def], simplified add.assoc]\<close>\<close>))

method vcg for vars::"char list set" =
  (((subroutine_step vars, print_fact subroutine_step); (vcg vars)?) |
    (while_step ; (vcg vars)?) |
    ((dest_com_gen', print_fact dest_com_gen) ; (vcg vars)?) |
    (if_step ; (vcg vars)?) |
    (seq_step ; (vcg vars)?))

method vcg_time for vars::"char list set" =
  (((subroutine_step vars, print_fact subroutine_step); (vcg_time vars)?) |
    (while_step_time; (vcg_time vars)?) |
    ((dest_com_gen_time', print_fact dest_com_gen); (vcg_time vars)?) |
    (ift_step; (vcg_time vars)?) |
    (seqt_step; (vcg_time vars)?))

end