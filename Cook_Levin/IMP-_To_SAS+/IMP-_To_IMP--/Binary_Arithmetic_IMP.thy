theory Binary_Arithmetic_IMP 
  imports Primitives_IMP_Minus  Binary_Arithmetic_Nat IMP_Minus.Com
begin

subsection \<open>N-th bit of Natural Number\<close>

fun nth_bit_of_num_nat' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nth_bit_of_num_nat' x n  = (if x \<noteq> 0 then 
                              (if n \<noteq> 0 then
                                nth_bit_of_num_nat' (tl_nat x) (n-1)
                               else
                                (if hd_nat x \<noteq> 0 then
                                   1 \<comment> \<open>x \<noteq> 0 \<and> n = 0 \<and> hd_nat x \<noteq> 0\<close>
                                 else
                                   0 \<comment> \<open>x \<noteq> 0 \<and> n = 0 \<and> hd_nat x = 0\<close>))
                            else
                              (if n \<noteq> 0 then
                                 0 \<comment> \<open>x = 0 \<and> n \<noteq> 0\<close>
                               else
                                 1 \<comment> \<open>x = 0 \<and> n = 0\<close>)
                              )"

lemma nth_bit_of_num_nat'_correct:
  "(nth_bit_of_num_nat' x n) = (nth_bit_of_num_nat x n)"
proof (induction x n rule: nth_bit_of_num_nat.induct)
  case (1 s)
  then show ?case
    apply(subst nth_bit_of_num_nat.simps)
    apply(subst nth_bit_of_num_nat'.simps)
    by (auto simp: Let_def split: if_splits)
qed 

record nth_bit_of_num_state = nth_bit_of_num_x::nat nth_bit_of_num_n::nat nth_bit_of_num_ret::nat

abbreviation "nth_bit_of_num_prefix \<equiv> ''nth_bit_of_num.''"
abbreviation "nth_bit_of_num_x_str \<equiv> ''x''"
abbreviation "nth_bit_of_num_n_str \<equiv> ''n''"
abbreviation "nth_bit_of_num_ret_str \<equiv> ''ret''"

definition "nth_bit_of_num_state_upd s \<equiv>
      let
        tl_xs' = nth_bit_of_num_x s;
        tl_ret' = 0;
        tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
        tl_ret_state = tl_imp tl_state;
        nth_bit_of_num_x' = tl_ret tl_ret_state;
        nth_bit_of_num_n' = nth_bit_of_num_n s - 1;
        ret = \<lparr>nth_bit_of_num_x = nth_bit_of_num_x', nth_bit_of_num_n = nth_bit_of_num_n', nth_bit_of_num_ret = nth_bit_of_num_ret s\<rparr>
      in
        ret
"

definition 
  "nth_bit_of_num_imp_compute_loop_condition s \<equiv>
  (let
     AND_neq_zero_a' = nth_bit_of_num_x s;
     AND_neq_zero_b' = nth_bit_of_num_n s;
     AND_neq_zero_ret' = 0;
     AND_neq_zero_state = \<lparr>AND_neq_zero_a = AND_neq_zero_a', AND_neq_zero_b = AND_neq_zero_b', AND_neq_zero_ret = AND_neq_zero_ret'\<rparr>;
     AND_neq_zero_state_ret = AND_neq_zero_imp AND_neq_zero_state;
     condition = AND_neq_zero_ret (AND_neq_zero_state_ret)
  in
     condition)"

definition 
  "nth_bit_of_num_imp_after_loop s \<equiv>
       (let
          hd_xs' = nth_bit_of_num_x s;
          hd_ret' = 0;
          hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
          hd_state_ret = hd_imp hd_state;
          hd_x = hd_ret hd_state_ret;
          nth_bit_of_num_ret' = 
                           (if nth_bit_of_num_x s \<noteq> 0 then 
                              ((if hd_x \<noteq> 0 then
                                   1 \<comment> \<open>x \<noteq> 0 \<and> n = 0 \<and> hd_nat x \<noteq> 0\<close>
                                 else
                                   0 \<comment> \<open>x \<noteq> 0 \<and> n = 0 \<and> hd_nat x = 0\<close>))
                            else
                              (if nth_bit_of_num_n s \<noteq> 0 then
                                 0 \<comment> \<open>x = 0 \<and> n \<noteq> 0\<close>
                               else
                                 1 \<comment> \<open>x = 0 \<and> n = 0\<close>)
                              );
          ret = \<lparr>nth_bit_of_num_x = nth_bit_of_num_x s, nth_bit_of_num_n = nth_bit_of_num_n s,
                 nth_bit_of_num_ret = nth_bit_of_num_ret'\<rparr>
        in
          ret)"


function nth_bit_of_num_imp:: "nth_bit_of_num_state \<Rightarrow> nth_bit_of_num_state" where
  "nth_bit_of_num_imp s = 
  (
    (if nth_bit_of_num_imp_compute_loop_condition s \<noteq> 0 then \<comment> \<open>While xs \<noteq> 0\<close>
      (
        let
          next_iteration = nth_bit_of_num_imp (nth_bit_of_num_state_upd s)
        in
          next_iteration
      )
    else
      (
        let
          ret = nth_bit_of_num_imp_after_loop s
        in
          ret
      )
    )
)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>s. nth_bit_of_num_n s)")
    (auto simp: nth_bit_of_num_imp_compute_loop_condition_def AND_neq_zero_imp_correct tl_imp_correct nth_bit_of_num_state_upd_def Let_def split: if_splits)

lemmas nth_bit_of_num_imp_subprogram_simps = 
  nth_bit_of_num_imp_after_loop_def nth_bit_of_num_state_upd_def
  nth_bit_of_num_imp_compute_loop_condition_def 

declare nth_bit_of_num_imp.simps [simp del]

lemma nth_bit_of_num_imp_correct:
  "nth_bit_of_num_ret (nth_bit_of_num_imp s) = nth_bit_of_num_nat (nth_bit_of_num_x s) (nth_bit_of_num_n s)"
proof (induction s rule: nth_bit_of_num_imp.induct)
  case (1 s)
  then show ?case
    apply(subst nth_bit_of_num_imp.simps)
    apply(subst nth_bit_of_num_nat.simps)
    by (auto simp del: nth_bit_of_num_nat.simps
        simp add: nth_bit_of_num_imp_after_loop_def 
        nth_bit_of_num_imp_compute_loop_condition_def
        tl_imp_correct hd_imp_correct AND_neq_zero_imp_correct
        nth_bit_of_num_state_upd_def Let_def
        split: if_splits)
qed 


definition "nth_bit_of_num_state_upd_time t s \<equiv>
      let
        tl_xs' = nth_bit_of_num_x s;
        t = t + 2;
        tl_ret' = 0;
        t = t + 2;
        tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
        tl_ret_state = tl_imp tl_state;
        t = t + tl_imp_time 0 tl_state;
        nth_bit_of_num_x' = tl_ret tl_ret_state;
        t = t + 2;
        nth_bit_of_num_n' = nth_bit_of_num_n s - 1;
        t = t + 2;
        ret = t
      in
        ret
"

definition 
  "nth_bit_of_num_imp_compute_loop_condition_time t s \<equiv>
  (let
     AND_neq_zero_a' = nth_bit_of_num_x s;
     t = t + 2;
     AND_neq_zero_b' = nth_bit_of_num_n s;
     t = t + 2;
     AND_neq_zero_ret' = 0;
     t = t + 2;
     AND_neq_zero_state = \<lparr>AND_neq_zero_a = AND_neq_zero_a', AND_neq_zero_b = AND_neq_zero_b', AND_neq_zero_ret = AND_neq_zero_ret'\<rparr>;
     AND_neq_zero_state_ret = AND_neq_zero_imp AND_neq_zero_state;
     t = t + AND_neq_zero_imp_time 0 AND_neq_zero_state;
     condition = AND_neq_zero_ret AND_neq_zero_state_ret;
     t = t + 2;
     ret = t
  in
     t)"

definition 
  "nth_bit_of_num_imp_after_loop_time t s \<equiv>
       (let
          hd_xs' = nth_bit_of_num_x s;
          t = t + 2;
          hd_ret' = 0;
          t = t + 2;
          hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
          hd_state_ret = hd_imp hd_state;
          t = t + hd_imp_time 0 hd_state;
          hd_x = hd_ret hd_state_ret;
          t = t + 2;
          nth_bit_of_num_ret'::nat = 
                           (if nth_bit_of_num_x s \<noteq> 0 then 
                              ((if hd_x \<noteq> 0 then
                                   1 \<comment> \<open>x \<noteq> 0 \<and> n = 0 \<and> hd_nat x \<noteq> 0\<close>
                                 else
                                   0 \<comment> \<open>x \<noteq> 0 \<and> n = 0 \<and> hd_nat x = 0\<close>))
                            else
                              (if nth_bit_of_num_n s \<noteq> 0 then
                                 0 \<comment> \<open>x = 0 \<and> n \<noteq> 0\<close>
                               else
                                 1 \<comment> \<open>x = 0 \<and> n = 0\<close>)
                              );
          t = t + 1 +
                           (if nth_bit_of_num_x s \<noteq> 0 then 
                              (1 +
                               (if hd_x \<noteq> 0 then
                                  2 \<comment> \<open>x \<noteq> 0 \<and> n = 0 \<and> hd_nat x \<noteq> 0\<close>
                                else
                                  2 \<comment> \<open>x \<noteq> 0 \<and> n = 0 \<and> hd_nat x = 0\<close>))
                            else
                              1 + 
                              (if nth_bit_of_num_n s \<noteq> 0 then
                                 2 \<comment> \<open>x = 0 \<and> n \<noteq> 0\<close>
                               else
                                 2 \<comment> \<open>x = 0 \<and> n = 0\<close>)
                              );
          ret = t
        in
          ret
)"


function nth_bit_of_num_imp_time:: "nat \<Rightarrow> nth_bit_of_num_state \<Rightarrow> nat" where
  "nth_bit_of_num_imp_time t s = 
  nth_bit_of_num_imp_compute_loop_condition_time 0 s+
   (
    (if nth_bit_of_num_imp_compute_loop_condition s \<noteq> 0 then \<comment> \<open>While xs \<noteq> 0\<close>
      (
        let
          t = t + 1; \<comment> \<open>While condition true\<close>
          next_iteration = 
           nth_bit_of_num_imp_time (t + 
                                    nth_bit_of_num_state_upd_time 0 s) (nth_bit_of_num_state_upd s)
        in
          next_iteration
      )
    else
      (
        let
          t = t + 2; \<comment> \<open>skipping while loop as it is false\<close>
          ret = t + nth_bit_of_num_imp_after_loop_time 0 s
        in
          ret
      )
    )
)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(t, s). nth_bit_of_num_n s)")
    (auto simp: nth_bit_of_num_imp_compute_loop_condition_def
      AND_neq_zero_imp_correct tl_imp_correct
      nth_bit_of_num_state_upd_def Let_def
      split: if_splits)


lemmas nth_bit_of_num_imp_subprogram_time_simps = nth_bit_of_num_imp_subprogram_simps
  nth_bit_of_num_imp_after_loop_time_def nth_bit_of_num_state_upd_time_def
  nth_bit_of_num_imp_compute_loop_condition_time_def 


lemmas [simp del] = nth_bit_of_num_imp_time.simps

lemma nth_bit_of_num_imp_time_acc: "(nth_bit_of_num_imp_time (Suc t) s) = Suc (nth_bit_of_num_imp_time t s)"
  apply (induction t s arbitrary:  rule: nth_bit_of_num_imp_time.induct)
  apply(subst nth_bit_of_num_imp_time.simps)
  apply(subst (2) nth_bit_of_num_imp_time.simps)
  apply (auto simp add: nth_bit_of_num_imp_compute_loop_condition_time_def
      nth_bit_of_num_imp_after_loop_time_def
      nth_bit_of_num_state_upd_time_def
      nth_bit_of_num_state_upd_def Let_def eval_nat_numeral 
      split: if_splits)
  done

lemma nth_bit_of_num_imp_time_acc_2: "(nth_bit_of_num_imp_time x s) = x + (nth_bit_of_num_imp_time 0 s)"
  by (induction x arbitrary: s)
    (auto simp add: nth_bit_of_num_imp_time_acc nth_bit_of_num_state_upd_def Let_def eval_nat_numeral split: if_splits)

lemma nth_bit_of_num_imp_time_acc_2_simp: 
  "(nth_bit_of_num_imp_time (nth_bit_of_num_state_upd_time 0 s) s') =
   (nth_bit_of_num_state_upd_time 0 s) + (nth_bit_of_num_imp_time 0 s')"
  by (rule nth_bit_of_num_imp_time_acc_2)

\<comment> \<open>The following separation is due to parsing time, whic grows exponentially in the length of IMP-
    programs.\<close>

abbreviation "nth_bit_of_num_while_cond \<equiv> ''condition''"

definition "nth_bit_of_num_IMP_init_while_cond \<equiv>
     \<comment> \<open>AND_neq_zero_a' = nth_bit_of_num_x s;\<close>
     (AND_neq_zero_prefix @ AND_neq_zero_a_str) ::= (A (V nth_bit_of_num_x_str));;
     \<comment> \<open>AND_neq_zero_b' = nth_bit_of_num_n s;\<close>
     (AND_neq_zero_prefix @ AND_neq_zero_b_str) ::= (A (V nth_bit_of_num_n_str));;
     \<comment> \<open>AND_neq_zero_ret' = 0;\<close>
     (AND_neq_zero_prefix @ AND_neq_zero_ret_str) ::= (A (N 0));;
     \<comment> \<open>AND_neq_zero_state = \<lparr>AND_neq_zero_a = AND_neq_zero_a', AND_neq_zero_b = AND_neq_zero_b', AND_neq_zero_ret = AND_neq_zero_ret'\<rparr>;\<close>
     \<comment> \<open>AND_neq_zero_state_ret = AND_neq_zero_imp AND_neq_zero_state;\<close>
     invoke_subprogram AND_neq_zero_prefix AND_neq_zero_IMP_Minus;;
     \<comment> \<open>condition = AND_neq_zero_ret (AND_neq_zero_state_ret)\<close>
     (nth_bit_of_num_while_cond) ::= (A (V (AND_neq_zero_prefix @ AND_neq_zero_ret_str)))
"

definition "nth_bit_of_num_IMP_loop_body \<equiv>
      \<comment> \<open>(\<close>
        \<comment> \<open>let\<close>
          \<comment> \<open>tl_xs' = nth_bit_of_num_x s;\<close>
          (tl_prefix @ tl_xs_str) ::= (A (V nth_bit_of_num_x_str));;
          \<comment> \<open>tl_ret' = 0;\<close>
          (tl_prefix @ tl_ret_str) ::= (A (N 0));;
          \<comment> \<open>tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;\<close>
          \<comment> \<open>tl_ret_state = tl_imp tl_state;\<close>
          invoke_subprogram tl_prefix tl_IMP_Minus;;
          \<comment> \<open>nth_bit_of_num_x' = tl_ret tl_ret_state;\<close>
          (nth_bit_of_num_x_str ::= (A (V (tl_prefix @ tl_ret_str))));;
          \<comment> \<open>nth_bit_of_num_n' = nth_bit_of_num_n s - 1;\<close>
          (nth_bit_of_num_n_str ::= ((V nth_bit_of_num_n_str \<ominus> (N 1))))
          \<comment> \<open>next_iteration = nth_bit_of_num_imp (nth_bit_of_num_state_upd s)\<close>
        \<comment> \<open>in\<close>
          \<comment> \<open>next_iteration\<close>
      \<comment> \<open>)\<close>
"

abbreviation "hd_x \<equiv> ''hd_x''"

definition "nth_bit_of_num_IMP_after_loop \<equiv>
          \<comment> \<open>hd_xs' = nth_bit_of_num_x s;\<close>
          (hd_prefix @ hd_xs_str) ::= (A (V nth_bit_of_num_x_str));;
          \<comment> \<open>hd_ret' = 0;\<close>
          (hd_prefix @ hd_ret_str) ::= (A (N 0));;
          \<comment> \<open>hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;\<close>
          \<comment> \<open>hd_state_ret = hd_imp hd_state;\<close>
          \<comment> \<open>hd_x = hd_ret hd_state_ret;\<close>
          invoke_subprogram hd_prefix hd_IMP_Minus;;
          (hd_x) ::= (A (V (hd_prefix @ hd_ret_str)));;
          \<comment> \<open>nth_bit_of_num_ret' = \<close>
                           \<comment> \<open>(if nth_bit_of_num_x s \<noteq> 0 then \<close>
                           IF nth_bit_of_num_x_str \<noteq>0 THEN
                              \<comment> \<open>((if hd_ret hd_state_ret \<noteq> 0 then\<close>
                              IF hd_x \<noteq>0 THEN
                                   \<comment> \<open>1 \<comment> \<open>x \<noteq> 0 \<and> n = 0 \<and> hd_nat x \<noteq> 0\<close>\<close>
                                   nth_bit_of_num_ret_str ::= (A (N 1))
                                 \<comment> \<open>else\<close>
                                 ELSE
                                   \<comment> \<open>0 \<comment> \<open>x \<noteq> 0 \<and> n = 0 \<and> hd_nat x = 0\<close>))\<close>
                                   nth_bit_of_num_ret_str ::= (A (N 0))
                            \<comment> \<open>else\<close>
                            ELSE
                              \<comment> \<open>(if nth_bit_of_num_n s \<noteq> 0 then\<close>
                              IF nth_bit_of_num_n_str \<noteq>0 THEN
                                 \<comment> \<open>0 \<comment> \<open>x = 0 \<and> n \<noteq> 0\<close>\<close>
                                 nth_bit_of_num_ret_str ::= (A (N 0))
                               \<comment> \<open>else\<close>
                               ELSE
                                 \<comment> \<open>1 \<comment> \<open>x = 0 \<and> n = 0\<close>)\<close>
                                 nth_bit_of_num_ret_str ::= (A (N 1))
                              \<comment> \<open>);\<close>
"

definition nth_bit_of_num_IMP_Minus where
  "nth_bit_of_num_IMP_Minus \<equiv>
  nth_bit_of_num_IMP_init_while_cond;;
  \<comment> \<open>in\<close>
    \<comment> \<open>(if condition \<noteq> 0 then \<comment> \<open>While xs \<noteq> 0\<close>\<close>
      WHILE nth_bit_of_num_while_cond \<noteq>0 DO(
        nth_bit_of_num_IMP_loop_body;;
        nth_bit_of_num_IMP_init_while_cond
      );;
    \<comment> \<open>else\<close>
      \<comment> \<open>(\<close>
        \<comment> \<open>let\<close>
        nth_bit_of_num_IMP_after_loop
          \<comment> \<open>ret = \<lparr>nth_bit_of_num_x = nth_bit_of_num_x s, nth_bit_of_num_n = nth_bit_of_num_n s,\<close>
                 \<comment> \<open>nth_bit_of_num_ret = nth_bit_of_num_ret'\<rparr>\<close>
        \<comment> \<open>in\<close>
          \<comment> \<open>ret\<close>
      \<comment> \<open>)\<close>
    \<comment> \<open>)\<close>
"

abbreviation 
  "nth_bit_of_num_IMP_vars \<equiv>
  {nth_bit_of_num_x_str, nth_bit_of_num_n_str, nth_bit_of_num_ret_str}"

lemmas nth_bit_of_num_IMP_subprogram_simps = 
  nth_bit_of_num_IMP_init_while_cond_def nth_bit_of_num_IMP_loop_body_def nth_bit_of_num_IMP_after_loop_def

definition "nth_bit_of_num_imp_to_HOL_state p s =
  \<lparr>nth_bit_of_num_x = (s (add_prefix p nth_bit_of_num_x_str)), 
   nth_bit_of_num_n = (s (add_prefix p nth_bit_of_num_n_str)),
   nth_bit_of_num_ret = (s (add_prefix p nth_bit_of_num_ret_str))\<rparr>"

lemmas nth_bit_of_num_state_translators = tl_imp_to_HOL_state_def hd_imp_to_HOL_state_def
  AND_neq_zero_imp_to_HOL_state_def
  nth_bit_of_num_imp_to_HOL_state_def

lemmas nth_bit_of_num_complete_simps =
  nth_bit_of_num_IMP_subprogram_simps nth_bit_of_num_imp_subprogram_simps
  nth_bit_of_num_state_translators

lemmas functional_correctness_lemmas = functional_correctness

definition "While' = Com.com.While"

notation While' ("(WHILEdummy _/\<noteq>0 DO _)"  [0, 61] 61)

lemma While_tE_dummy:
"(WHILE b\<noteq>0 DO c, s) \<Rightarrow>\<^bsup> x \<^esup> t \<Longrightarrow>
(x = Suc (Suc 0) \<Longrightarrow> t = s \<Longrightarrow> s b = 0 \<Longrightarrow> P) \<Longrightarrow>
(\<And>x' s2 y. 0 < s b \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup> x' \<^esup> s2 \<Longrightarrow> (WHILEdummy b\<noteq>0 DO c, s2) \<Rightarrow>\<^bsup> y \<^esup> t \<Longrightarrow> Suc (x' + y) = x \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: While'_def)

method while_step = (erule While_tE_dummy, print_fact While_tE)
method seq_step = (erule Seq_tE, print_fact Seq_tE)
method if_step = (erule If_tE, print_fact If_tE)
method assign_step = (drule AssignD, elim conjE, print_fact AssignD)

definition "dest_com_gen = 0"

lemma dest_com_gen: "dest_com_gen = dest_com_gen"
  by auto

method subroutine_step for vars::"char list set" =
  (erule functional_correctness_lemmas[where vars = vars],
     (match premises
        in prem[thin]:
          "_ \<in> vars" \<Rightarrow>
                      \<open>match premises
                          in c[thin]: "_" (multi) \<Rightarrow>
                              \<open>insert prem, (auto)[1]\<close>\<close>))

definition "subroutine_step = 0"

lemma subroutine_step: "subroutine_step = subroutine_step"
  by auto

method dest_com_gen' = 
  (erule compose_programs_1[where ?c2.0 = "(While' _ _)"], assumption,
    erule compose_programs_2[where ?c1.0 = "(_;; While' _ _)"], assumption,
    (match premises
      in a[thin]: 
      "(init_while_cond;; 
                WHILEdummy _ \<noteq>0 DO (loop_body;; init_while_cond);;
                after_loop, _) \<Rightarrow>\<^bsup>_\<^esup> _"
    for init_while_cond loop_body after_loop  \<Rightarrow> 
      \<open>match premises in b[thin]: "\<lbrakk>loop_cond; state_upd; _\<rbrakk> \<Longrightarrow> P"
       for loop_cond state_upd P \<Rightarrow> \<open>subst b[OF _ _ a[unfolded While'_def]]\<close>\<close>))

method vcg for vars::"char list set" = (*subroutine_step vars*)
  (((subroutine_step vars, print_fact subroutine_step); (vcg vars)?) | (while_step ; (vcg vars)?) | ((dest_com_gen', print_fact dest_com_gen) ; (vcg vars)?) | (if_step ; (vcg vars)?) | (seq_step ; (vcg vars)?) | (assign_step; (vcg vars)?))

lemma nth_bit_of_num_IMP_Minus_correct_function: 
  "(invoke_subprogram p nth_bit_of_num_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p nth_bit_of_num_ret_str) = nth_bit_of_num_ret (nth_bit_of_num_imp (nth_bit_of_num_imp_to_HOL_state p s))"
  apply(induction "nth_bit_of_num_imp_to_HOL_state p s" arbitrary: s s' t rule: nth_bit_of_num_imp.induct)
  apply(subst nth_bit_of_num_imp.simps)
  apply(simp only: nth_bit_of_num_IMP_Minus_def prefix_simps)
  apply(vcg nth_bit_of_num_IMP_vars)
   apply(simp only: nth_bit_of_num_IMP_subprogram_simps prefix_simps)
  apply(vcg nth_bit_of_num_IMP_vars)

   apply(simp add: nth_bit_of_num_imp_subprogram_simps nth_bit_of_num_imp_time_acc
      nth_bit_of_num_state_translators Let_def,
      force)
     apply(simp add: nth_bit_of_num_imp_subprogram_simps nth_bit_of_num_imp_time_acc
      nth_bit_of_num_state_translators Let_def,
      force)
     apply(simp add: nth_bit_of_num_imp_subprogram_simps nth_bit_of_num_imp_time_acc
      nth_bit_of_num_state_translators Let_def,
      force)
     apply(simp add: nth_bit_of_num_imp_subprogram_simps nth_bit_of_num_imp_time_acc
      nth_bit_of_num_state_translators Let_def,
      force)

   apply(simp_all only: nth_bit_of_num_IMP_init_while_cond_def nth_bit_of_num_IMP_loop_body_def prefix_simps)

    apply(vcg nth_bit_of_num_IMP_vars)
   apply(simp only: nth_bit_of_num_imp_subprogram_simps nth_bit_of_num_imp_time_acc
      nth_bit_of_num_state_translators Let_def;
      force)

  apply(vcg nth_bit_of_num_IMP_vars)
   apply(simp only: nth_bit_of_num_imp_subprogram_simps nth_bit_of_num_imp_time_acc
      nth_bit_of_num_state_translators Let_def;
      force)

    apply(vcg nth_bit_of_num_IMP_vars)
   apply(simp only: nth_bit_of_num_imp_subprogram_simps nth_bit_of_num_imp_time_acc
      nth_bit_of_num_state_translators Let_def;
      force)
  done

(*lemma nth_bit_of_num_IMP_Minus_correct_function:
  "(invoke_subprogram p nth_bit_of_num_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p nth_bit_of_num_ret_str) = nth_bit_of_num_ret (nth_bit_of_num_imp (nth_bit_of_num_imp_to_HOL_state p s))"
  apply(induction "nth_bit_of_num_imp_to_HOL_state p s" arbitrary: s s' t rule: nth_bit_of_num_imp.induct)
  apply(subst nth_bit_of_num_imp.simps)
  apply(simp only: nth_bit_of_num_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule While_tE)
   apply(simp only: nth_bit_of_num_IMP_subprogram_simps prefix_simps)
   apply(erule Seq_tE)+
   apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "nth_bit_of_num_IMP_vars"])
    apply auto [1]
   apply(erule If_tE)
    apply(erule If_tE)
     apply(drule AssignD)+
     apply(elim conjE)
     apply(erule hd_IMP_Minus_correct[where vars = "nth_bit_of_num_IMP_vars"])
      apply auto [1]
     apply(simp add: nth_bit_of_num_imp_subprogram_simps nth_bit_of_num_imp_time_acc
      nth_bit_of_num_state_translators Let_def,
      force)
    apply(erule hd_IMP_Minus_correct[where vars = "nth_bit_of_num_IMP_vars"])
     apply auto [1]
    apply(simp add: nth_bit_of_num_imp_subprogram_simps nth_bit_of_num_imp_time_acc
      nth_bit_of_num_state_translators Let_def,
      force)
   apply(erule hd_IMP_Minus_correct[where vars = "nth_bit_of_num_IMP_vars"])
    apply auto [1]
   apply(simp add: nth_bit_of_num_imp_subprogram_simps nth_bit_of_num_imp_time_acc
      nth_bit_of_num_state_translators Let_def,
      force)

  apply(erule Seq_tE)+
  apply(dest_com_gen)
    apply(simp only: nth_bit_of_num_IMP_init_while_cond_def prefix_simps)
    apply(erule Seq_tE)+
    apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "nth_bit_of_num_IMP_vars"])
     apply auto [1]
    apply(simp add: nth_bit_of_num_complete_simps Let_def, force)

   apply(simp only: nth_bit_of_num_IMP_init_while_cond_def nth_bit_of_num_IMP_loop_body_def prefix_simps)
   apply(erule Seq_tE)+
   apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "nth_bit_of_num_IMP_vars"])
    apply auto [1]
   apply(erule tl_IMP_Minus_correct[where vars = "nth_bit_of_num_IMP_vars"])
    apply force [1]
   apply(simp add: nth_bit_of_num_complete_simps Let_def, force)

  apply(simp only: nth_bit_of_num_IMP_init_while_cond_def nth_bit_of_num_IMP_loop_body_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "nth_bit_of_num_IMP_vars"])
   apply auto [1]
  apply(erule tl_IMP_Minus_correct[where vars = "nth_bit_of_num_IMP_vars"])
   apply force [1]
  apply(simp add: nth_bit_of_num_complete_simps Let_def, force)
  done*)



text \<open>Debugging lemma\<close>

lemma nth_bit_of_num_IMP_Minus_correct_time_loop_condition:
  "(invoke_subprogram p nth_bit_of_num_IMP_init_while_cond, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = nth_bit_of_num_imp_compute_loop_condition_time 0 (nth_bit_of_num_imp_to_HOL_state p s)"
  apply(subst nth_bit_of_num_imp_compute_loop_condition_time_def)
  apply(simp only: nth_bit_of_num_IMP_init_while_cond_def prefix_simps)
  apply(erule Seq_tE)+
  apply(drule AssignD)+
  apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "nth_bit_of_num_IMP_vars"])
   apply auto [1]
  apply(elim conjE)
  apply(simp add: nth_bit_of_num_imp_subprogram_simps nth_bit_of_num_imp_time_acc
      nth_bit_of_num_state_translators Let_def)
  done

lemmas nth_bit_of_num_complete_time_simps =
  nth_bit_of_num_imp_subprogram_time_simps
  nth_bit_of_num_imp_time_acc
  nth_bit_of_num_imp_time_acc_2_simp

lemma While_tE_time_dummy:
"(WHILE b\<noteq>0 DO c, s) \<Rightarrow>\<^bsup> x \<^esup> t \<Longrightarrow>
  (x = Suc (Suc 0) \<Longrightarrow> t = s \<Longrightarrow> s b = 0 \<Longrightarrow> P) \<Longrightarrow>
  (\<And>x' s2 y. 0 < s b \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup> x' \<^esup> s2 \<Longrightarrow> (WHILEdummy b\<noteq>0 DO c, s2) \<Rightarrow>\<^bsup> y \<^esup> t \<Longrightarrow> x = Suc (x' + y) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: While'_def)

method while_step_time = (erule While_tE_time_dummy, print_fact While_tE)

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


method vcg_time for vars::"char list set" = (*subroutine_step vars*)
  ((subroutine_step vars, print_fact subroutine_step) |
   while_step_time | (dest_com_gen_time', print_fact dest_com_gen) | if_step | seq_step | assign_step)


lemma nth_bit_of_num_IMP_Minus_correct_time:
  "(invoke_subprogram p nth_bit_of_num_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = nth_bit_of_num_imp_time 0 (nth_bit_of_num_imp_to_HOL_state p s)"
  apply(induction "nth_bit_of_num_imp_to_HOL_state p s" arbitrary: s s' t rule: nth_bit_of_num_imp.induct)
  apply(subst nth_bit_of_num_imp_time.simps)
  apply(simp only: nth_bit_of_num_IMP_Minus_def prefix_simps)
  apply(vcg_time nth_bit_of_num_IMP_vars)+
   apply(simp only: nth_bit_of_num_IMP_subprogram_simps prefix_simps)
  apply(vcg_time nth_bit_of_num_IMP_vars)+
     apply(simp add: nth_bit_of_num_imp_subprogram_time_simps nth_bit_of_num_imp_time_acc
      nth_bit_of_num_state_translators Let_def,
      force)
  apply(vcg_time nth_bit_of_num_IMP_vars)+
     apply(simp add: nth_bit_of_num_imp_subprogram_time_simps nth_bit_of_num_imp_time_acc
      nth_bit_of_num_state_translators Let_def,
      force)
  apply(vcg_time nth_bit_of_num_IMP_vars)+
     apply(simp add: nth_bit_of_num_imp_subprogram_time_simps nth_bit_of_num_imp_time_acc
      nth_bit_of_num_state_translators Let_def,
      force)
  apply(vcg_time nth_bit_of_num_IMP_vars)+
     apply(simp add: nth_bit_of_num_imp_subprogram_time_simps nth_bit_of_num_imp_time_acc
      nth_bit_of_num_state_translators Let_def,
      force)

  apply(vcg_time nth_bit_of_num_IMP_vars)+
  apply(simp add: add.assoc)

    apply(simp only: nth_bit_of_num_IMP_init_while_cond_def prefix_simps)
  apply(vcg_time nth_bit_of_num_IMP_vars)+
    apply(simp add: nth_bit_of_num_complete_simps Let_def; force)

   apply(simp only: nth_bit_of_num_IMP_init_while_cond_def nth_bit_of_num_IMP_loop_body_def prefix_simps)
  apply(vcg_time nth_bit_of_num_IMP_vars)+
   apply(simp add: nth_bit_of_num_complete_simps Let_def; force)

  apply(simp only: nth_bit_of_num_IMP_init_while_cond_def nth_bit_of_num_IMP_loop_body_def prefix_simps)
  apply(vcg_time nth_bit_of_num_IMP_vars)+
  apply(simp add: nth_bit_of_num_imp_time_acc_2[where x = "tl_imp_time t s" for t s]
      nth_bit_of_num_complete_time_simps nth_bit_of_num_complete_simps Let_def;
      force)
  done


end 