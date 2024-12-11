theory Binary_Arithmetic_IMP_Minus
  imports
    Primitives_IMP_Minus
    "IMP-_To_SAS+_Nat.Binary_Arithmetic_Nat"
    IMP_Minus.Com
    Utilities
begin

unbundle no IMP_Minus_Minus_Com.com_syntax

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
  by (induction x n rule: nth_bit_of_num_nat.induct) simp

record nth_bit_of_num_state =
  nth_bit_of_num_x::nat
  nth_bit_of_num_n::nat
  nth_bit_of_num_ret::nat

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
        ret = \<lparr>nth_bit_of_num_x = nth_bit_of_num_x',
               nth_bit_of_num_n = nth_bit_of_num_n',
               nth_bit_of_num_ret = nth_bit_of_num_ret s\<rparr>
      in
        ret
"

definition
  "nth_bit_of_num_imp_compute_loop_condition s \<equiv>
  (let
     AND_neq_zero_a' = nth_bit_of_num_x s;
     AND_neq_zero_b' = nth_bit_of_num_n s;
     AND_neq_zero_ret' = 0;
     AND_neq_zero_state = \<lparr>AND_neq_zero_a = AND_neq_zero_a',
                           AND_neq_zero_b = AND_neq_zero_b',
                           AND_neq_zero_ret = AND_neq_zero_ret'\<rparr>;
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


lemmas nth_bit_of_num_imp_subprogram_simps =
  nth_bit_of_num_imp_after_loop_def
  nth_bit_of_num_state_upd_def
  nth_bit_of_num_imp_compute_loop_condition_def


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
  by simp+
termination
  by (relation "measure nth_bit_of_num_n")
    (simp add: nth_bit_of_num_imp_subprogram_simps AND_neq_zero_imp_correct tl_imp_correct
      Let_def split: if_splits)+

declare nth_bit_of_num_imp.simps [simp del]
declare
  arg_cong3[where f=nth_bit_of_num_state.make, state_congs]
  arg_cong[where f=nth_bit_of_num_ret, state_congs]
  arg_cong[where f=nth_bit_of_num_imp, state_congs]

lemma nth_bit_of_num_imp_correct[let_function_correctness]:
  "nth_bit_of_num_ret (nth_bit_of_num_imp s) =
    nth_bit_of_num_nat (nth_bit_of_num_x s) (nth_bit_of_num_n s)"
  apply (induction s rule: nth_bit_of_num_imp.induct)
  apply (subst nth_bit_of_num_imp.simps)
  apply (subst nth_bit_of_num_nat.simps)
  by (simp del: nth_bit_of_num_nat.simps add: nth_bit_of_num_imp_subprogram_simps tl_imp_correct
      hd_imp_correct AND_neq_zero_imp_correct Let_def split: if_splits)

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
     AND_neq_zero_state = \<lparr>AND_neq_zero_a = AND_neq_zero_a',
                           AND_neq_zero_b = AND_neq_zero_b',
                           AND_neq_zero_ret = AND_neq_zero_ret'\<rparr>;
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

lemmas nth_bit_of_num_imp_subprogram_time_simps =
  nth_bit_of_num_imp_subprogram_simps
  nth_bit_of_num_imp_after_loop_time_def nth_bit_of_num_state_upd_time_def
  nth_bit_of_num_imp_compute_loop_condition_time_def

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
  by (relation "measure (nth_bit_of_num_n \<circ> snd)")
    (simp add: nth_bit_of_num_imp_subprogram_time_simps AND_neq_zero_imp_correct tl_imp_correct
      Let_def split: if_splits)+

declare nth_bit_of_num_imp_time.simps [simp del]

lemma nth_bit_of_num_imp_time_acc: "(nth_bit_of_num_imp_time (Suc t) s) =
  Suc (nth_bit_of_num_imp_time t s)"
  by (induction t s rule: nth_bit_of_num_imp_time.induct)
    ((subst (1 2) nth_bit_of_num_imp_time.simps);
      (simp add: nth_bit_of_num_state_upd_def))

lemma nth_bit_of_num_imp_time_acc_2_aux:
  "(nth_bit_of_num_imp_time t s) =
    t + (nth_bit_of_num_imp_time 0 s)"
  by (induction t arbitrary: s)
    (simp add: nth_bit_of_num_imp_time_acc)+

lemma nth_bit_of_num_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (nth_bit_of_num_imp_time t s) =
    t + (nth_bit_of_num_imp_time 0 s)"
  by (rule nth_bit_of_num_imp_time_acc_2_aux)

lemma nth_bit_of_num_imp_time_acc_3:
  "(nth_bit_of_num_imp_time (a + b) s) =
    a + (nth_bit_of_num_imp_time b s)"
  by (induction a arbitrary: b s)
    (simp add: nth_bit_of_num_imp_time_acc)+

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
          invoke_subprogram hd_prefix hd_IMP_Minus;;
          \<comment> \<open>hd_x = hd_ret hd_state_ret;\<close>
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
  nth_bit_of_num_IMP_init_while_cond_def
  nth_bit_of_num_IMP_loop_body_def
  nth_bit_of_num_IMP_after_loop_def

definition "nth_bit_of_num_imp_to_HOL_state p s =
  \<lparr>nth_bit_of_num_x = (s (add_prefix p nth_bit_of_num_x_str)),
   nth_bit_of_num_n = (s (add_prefix p nth_bit_of_num_n_str)),
   nth_bit_of_num_ret = (s (add_prefix p nth_bit_of_num_ret_str))\<rparr>"

lemmas nth_bit_of_num_state_translators =
  tl_imp_to_HOL_state_def
  hd_imp_to_HOL_state_def
  AND_neq_zero_imp_to_HOL_state_def
  nth_bit_of_num_imp_to_HOL_state_def

thm
  nth_bit_of_num_IMP_subprogram_simps (* TODO *)

lemmas nth_bit_of_num_complete_simps =
  nth_bit_of_num_imp_subprogram_simps
  nth_bit_of_num_state_translators

lemma nth_bit_of_num_IMP_Minus_correct_function:
  "(invoke_subprogram p nth_bit_of_num_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
    s' (add_prefix p nth_bit_of_num_ret_str) =
      nth_bit_of_num_ret (nth_bit_of_num_imp (nth_bit_of_num_imp_to_HOL_state p s))"
  apply(induction "nth_bit_of_num_imp_to_HOL_state p s" arbitrary: s s' t
      rule: nth_bit_of_num_imp.induct)
  apply(subst nth_bit_of_num_imp.simps)
  apply(simp only: nth_bit_of_num_IMP_Minus_def prefix_simps)
  apply(vcg nth_bit_of_num_IMP_vars)

  subgoal
    apply(subst (asm) (3) nth_bit_of_num_IMP_init_while_cond_def)
    apply(subst (asm) (2) nth_bit_of_num_IMP_after_loop_def)
    apply(simp only: prefix_simps)
    apply(vcg nth_bit_of_num_IMP_vars)
    by (fastforce simp: nth_bit_of_num_complete_simps)+

  subgoal
    apply(subst (asm) (1) nth_bit_of_num_IMP_init_while_cond_def)
    apply(simp only: prefix_simps)
    apply(vcg nth_bit_of_num_IMP_vars)
    by (fastforce_sorted_premises simp: nth_bit_of_num_complete_simps)

  subgoal
    apply(subst (asm) nth_bit_of_num_IMP_init_while_cond_def)
    apply(subst (asm) nth_bit_of_num_IMP_loop_body_def)
    apply(simp only: prefix_simps)
    apply(vcg nth_bit_of_num_IMP_vars)
    by (fastforce_sorted_premises simp: Let_def
        nth_bit_of_num_complete_simps)

  subgoal
    apply(subst (asm) (1) nth_bit_of_num_IMP_init_while_cond_def)
    apply(subst (asm) (1) nth_bit_of_num_IMP_loop_body_def)
    apply(simp only: prefix_simps)
    apply(vcg nth_bit_of_num_IMP_vars)
    by (fastforce_sorted_premises simp: Let_def
        nth_bit_of_num_complete_simps)
  done

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
  nth_bit_of_num_imp_time_acc_2
  nth_bit_of_num_imp_time_acc_3
  nth_bit_of_num_state_translators

lemma nth_bit_of_num_IMP_Minus_correct_time:
  "(invoke_subprogram p nth_bit_of_num_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = nth_bit_of_num_imp_time 0 (nth_bit_of_num_imp_to_HOL_state p s)"
  apply(induction "nth_bit_of_num_imp_to_HOL_state p s"
      arbitrary: s s' t rule: nth_bit_of_num_imp.induct)
  apply(subst nth_bit_of_num_imp_time.simps)
  apply(simp only: nth_bit_of_num_IMP_Minus_def prefix_simps)

  apply(vcg_time nth_bit_of_num_IMP_vars)

  subgoal
    apply(subst (asm) (3) nth_bit_of_num_IMP_init_while_cond_def)
    apply(subst (asm) (2) nth_bit_of_num_IMP_after_loop_def)
    apply(simp only: prefix_simps)
    apply(vcg_time nth_bit_of_num_IMP_vars)
    by (force simp: nth_bit_of_num_imp_subprogram_time_simps
        nth_bit_of_num_state_translators)+

  apply(simp add: add.assoc)
  apply(vcg_time nth_bit_of_num_IMP_vars)

  subgoal
    apply(subst (asm) (1) nth_bit_of_num_IMP_init_while_cond_def)
    apply(simp only: prefix_simps)
    apply(vcg_time nth_bit_of_num_IMP_vars)
    by (fastforce simp add: nth_bit_of_num_complete_simps)

  subgoal
    apply(subst (asm) (1) nth_bit_of_num_IMP_init_while_cond_def)
    apply(subst (asm) (1) nth_bit_of_num_IMP_loop_body_def)
    apply(simp only: prefix_simps)
    apply(vcg_time nth_bit_of_num_IMP_vars)
    by (fastforce_sorted_premises simp: Let_def
        nth_bit_of_num_complete_time_simps)

  subgoal
    apply(subst (asm) (1) nth_bit_of_num_IMP_init_while_cond_def)
    apply(subst (asm) (1) nth_bit_of_num_IMP_loop_body_def)
    apply(simp only: prefix_simps)
    apply(vcg_time nth_bit_of_num_IMP_vars)
    by (fastforce_sorted_premises simp: Let_def nth_bit_of_num_complete_time_simps)
  done


subsection \<open>nth_bit_tail\<close>

fun nth_bit_tail':: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nth_bit_tail' acc n =
  (if n \<noteq> 0
   then nth_bit_tail' (acc div 2) (n - 1)
   else acc mod 2
  )"

lemma nth_bit_tail'_correct:"nth_bit_tail acc n = nth_bit_tail' acc n"
  by(induction acc n rule: nth_bit_tail.induct) simp+

record nth_bit_tail_state =
  nth_bit_tail_acc::nat
  nth_bit_tail_n::nat
  nth_bit_tail_ret::nat

abbreviation "nth_bit_tail_prefix \<equiv> ''nth_bit_tail.''"
abbreviation "nth_bit_tail_acc_str \<equiv> ''acc''"
abbreviation "nth_bit_tail_n_str \<equiv> ''n''"
abbreviation "nth_bit_tail_ret_str \<equiv> ''ret''"

definition "nth_bit_tail_state_upd s \<equiv>
  let
    nth_bit_tail_acc' = nth_bit_tail_acc s div 2;
    nth_bit_tail_n' = nth_bit_tail_n s - 1;
    nth_bit_tail_ret' = nth_bit_tail_ret s;
    ret = \<lparr>nth_bit_tail_acc = nth_bit_tail_acc',
           nth_bit_tail_n = nth_bit_tail_n',
           nth_bit_tail_ret = nth_bit_tail_ret'\<rparr>
  in ret
"

definition "nth_bit_tail_imp_compute_loop_condition s \<equiv>
  let
    condition = nth_bit_tail_n s
  in condition
"

definition "nth_bit_tail_imp_after_loop s \<equiv>
  let
    nth_bit_tail_acc' = nth_bit_tail_acc s;
    nth_bit_tail_n' = nth_bit_tail_n s;
    nth_bit_tail_ret' = nth_bit_tail_acc s mod 2;
    ret = \<lparr>nth_bit_tail_acc = nth_bit_tail_acc',
           nth_bit_tail_n = nth_bit_tail_n',
           nth_bit_tail_ret = nth_bit_tail_ret'\<rparr>
  in ret
"

lemmas nth_bit_tail_imp_subprogram_simps =
  nth_bit_tail_state_upd_def
  nth_bit_tail_imp_compute_loop_condition_def
  nth_bit_tail_imp_after_loop_def

function nth_bit_tail_imp::
  "nth_bit_tail_state \<Rightarrow> nth_bit_tail_state" where
  "nth_bit_tail_imp s =
  (if nth_bit_tail_imp_compute_loop_condition s \<noteq> 0
   then
    let next_iteration = nth_bit_tail_imp (nth_bit_tail_state_upd s)
    in next_iteration
   else
    let ret = nth_bit_tail_imp_after_loop s
    in ret
  )"
  by simp+
termination
  by (relation "measure nth_bit_tail_n")
    (simp add: nth_bit_tail_imp_subprogram_simps)+

declare nth_bit_tail_imp.simps [simp del]
declare
  arg_cong3[where f=nth_bit_tail_state.make, state_congs]
  arg_cong[where f=nth_bit_tail_ret, state_congs]
  arg_cong[where f=nth_bit_tail_imp, state_congs]
  arg_cong2[where f=nth_bit_tail', let_lemmas]
  nth_bit_tail_state.simps[state_simps]

lemma nth_bit_tail_imp_correct[let_function_correctness]:
  "nth_bit_tail_ret (nth_bit_tail_imp s) =
    nth_bit_tail' (nth_bit_tail_acc s) (nth_bit_tail_n s)"
  apply (induction s rule: nth_bit_tail_imp.induct)
  apply (subst nth_bit_tail_imp.simps)
  apply (subst nth_bit_tail'.simps)
  by (simp del: nth_bit_tail.simps add: nth_bit_tail_imp_subprogram_simps Let_def)

definition "nth_bit_tail_state_upd_time t s \<equiv>
  let
    nth_bit_tail_acc' = nth_bit_tail_acc s div 2;
    t = t + 2;
    nth_bit_tail_n' = nth_bit_tail_n s - 1;
    t = t + 2;
    nth_bit_tail_ret' = nth_bit_tail_ret s;
    t = t + 2;
    ret = t
  in
    ret
"

definition "nth_bit_tail_imp_compute_loop_condition_time t s \<equiv>
  let
    condition = nth_bit_tail_n s;
    ret = t + 2
  in
    ret
"

definition "nth_bit_tail_imp_after_loop_time t s \<equiv>
  let
    nth_bit_tail_acc' = nth_bit_tail_acc s;
    t = t + 2;
    nth_bit_tail_n' = nth_bit_tail_n s;
    t = t + 2;
    nth_bit_tail_ret' = nth_bit_tail_acc s mod 2;
    t = t + 2;
    ret = t
  in
    ret
"

lemmas nth_bit_tail_imp_subprogram_time_simps =
  nth_bit_tail_state_upd_time_def
  nth_bit_tail_imp_compute_loop_condition_time_def
  nth_bit_tail_imp_after_loop_time_def
  nth_bit_tail_imp_subprogram_simps

function nth_bit_tail_imp_time::
  "nat \<Rightarrow> nth_bit_tail_state \<Rightarrow> nat" where
  "nth_bit_tail_imp_time t s =
  nth_bit_tail_imp_compute_loop_condition_time 0 s +
  (if nth_bit_tail_imp_compute_loop_condition s \<noteq> 0
    then
      (let
        t = t + 1;
        next_iteration =
          nth_bit_tail_imp_time (t + nth_bit_tail_state_upd_time 0 s)
                         (nth_bit_tail_state_upd s)
       in next_iteration)
    else
      (let
        t = t + 2;
        ret = t + nth_bit_tail_imp_after_loop_time 0 s
       in ret)
  )"
  by auto
termination
  by (relation "measure (nth_bit_tail_n \<circ> snd)")
    (simp add: nth_bit_tail_imp_subprogram_time_simps)+

declare nth_bit_tail_imp_time.simps [simp del]

lemma nth_bit_tail_imp_time_acc:
  "(nth_bit_tail_imp_time (Suc t) s) = Suc (nth_bit_tail_imp_time t s)"
  by (induction t s rule: nth_bit_tail_imp_time.induct)
    ((subst (1 2) nth_bit_tail_imp_time.simps);
      (simp add: nth_bit_tail_state_upd_def))

lemma nth_bit_tail_imp_time_acc_2_aux:
  "(nth_bit_tail_imp_time t s) = t + (nth_bit_tail_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: nth_bit_tail_imp_time_acc)+

lemma nth_bit_tail_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (nth_bit_tail_imp_time t s) = t + (nth_bit_tail_imp_time 0 s)"
  by (rule nth_bit_tail_imp_time_acc_2_aux)

lemma nth_bit_tail_imp_time_acc_3:
  "(nth_bit_tail_imp_time (a + b) s) = a + (nth_bit_tail_imp_time b s)"
  by (induction a arbitrary: b s)
    (simp add: nth_bit_tail_imp_time_acc)+

abbreviation "nth_bit_tail_while_cond \<equiv> ''condition''"

definition "nth_bit_tail_IMP_loop_body \<equiv>
  \<comment> \<open>nth_bit_tail_acc' = nth_bit_tail_acc s div 2;\<close>
  nth_bit_tail_acc_str ::= ((V nth_bit_tail_acc_str)\<then>);;
  \<comment> \<open>nth_bit_tail_n' = nth_bit_tail_n s - 1;\<close>
  nth_bit_tail_n_str ::= ((V nth_bit_tail_n_str) \<ominus> (N 1));;
  \<comment> \<open>nth_bit_tail_ret' = nth_bit_tail_ret s;\<close>
  nth_bit_tail_ret_str ::= (A (V nth_bit_tail_ret_str))
  \<comment> \<open>ret = \<lparr>nth_bit_tail_acc = nth_bit_tail_acc',\<close>
  \<comment> \<open>       nth_bit_tail_n = nth_bit_tail_n',\<close>
  \<comment> \<open>       nth_bit_tail_ret = nth_bit_tail_ret'\<rparr>\<close>
"

definition "nth_bit_tail_IMP_init_while_cond \<equiv>
  \<comment> \<open>condition = nth_bit_tail_n s\<close>
  nth_bit_tail_while_cond ::= (A (V nth_bit_tail_n_str))
"

definition "nth_bit_tail_IMP_after_loop \<equiv>
  \<comment> \<open>nth_bit_tail_acc' = nth_bit_tail_acc s;\<close>
  nth_bit_tail_acc_str ::= (A (V nth_bit_tail_acc_str));;
  \<comment> \<open>nth_bit_tail_n' = nth_bit_tail_n s;\<close>
  nth_bit_tail_n_str ::= (A (V nth_bit_tail_n_str));;
  \<comment> \<open>nth_bit_tail_ret' = nth_bit_tail_acc s mod 2;\<close>
  nth_bit_tail_ret_str ::= ((V nth_bit_tail_acc_str) \<doteq>1)
  \<comment> \<open>ret = \<lparr>nth_bit_tail_acc = nth_bit_tail_acc',\<close>
  \<comment> \<open>       nth_bit_tail_n = nth_bit_tail_n',\<close>
  \<comment> \<open>       nth_bit_tail_ret = nth_bit_tail_ret'\<rparr>\<close>
"

definition nth_bit_tail_IMP_Minus where
  "nth_bit_tail_IMP_Minus \<equiv>
  nth_bit_tail_IMP_init_while_cond;;
  WHILE nth_bit_tail_while_cond \<noteq>0 DO (
    nth_bit_tail_IMP_loop_body;;
    nth_bit_tail_IMP_init_while_cond
  );;
  nth_bit_tail_IMP_after_loop"

abbreviation
  "nth_bit_tail_IMP_vars \<equiv>
  {nth_bit_tail_acc_str, nth_bit_tail_n_str, nth_bit_tail_ret_str}"

lemmas nth_bit_tail_IMP_subprogram_simps =
  nth_bit_tail_IMP_init_while_cond_def
  nth_bit_tail_IMP_loop_body_def
  nth_bit_tail_IMP_after_loop_def

definition "nth_bit_tail_imp_to_HOL_state p s =
  \<lparr>nth_bit_tail_acc = (s (add_prefix p nth_bit_tail_acc_str)),
   nth_bit_tail_n = (s (add_prefix p nth_bit_tail_n_str)),
   nth_bit_tail_ret = (s (add_prefix p nth_bit_tail_ret_str))\<rparr>"

lemmas nth_bit_tail_state_translators =
  nth_bit_tail_imp_to_HOL_state_def

lemmas nth_bit_tail_complete_simps =
  nth_bit_tail_IMP_subprogram_simps
  nth_bit_tail_imp_subprogram_simps
  nth_bit_tail_state_translators

lemma nth_bit_tail_IMP_Minus_correct_function:
  "(invoke_subprogram p nth_bit_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p nth_bit_tail_ret_str) =
      nth_bit_tail_ret (nth_bit_tail_imp (nth_bit_tail_imp_to_HOL_state p s))"
  apply(induction "nth_bit_tail_imp_to_HOL_state p s" arbitrary: s s' t
      rule: nth_bit_tail_imp.induct)
  apply(subst nth_bit_tail_imp.simps)
  apply(simp only: nth_bit_tail_IMP_Minus_def prefix_simps)
  apply(vcg nth_bit_tail_IMP_vars)

  subgoal
    apply(subst (asm) (3) nth_bit_tail_IMP_init_while_cond_def)
    apply(subst (asm) (2) nth_bit_tail_IMP_after_loop_def)
    apply(simp only: prefix_simps)
    apply(vcg nth_bit_tail_IMP_vars)
    by (fastforce simp: nth_bit_tail_complete_simps)

  subgoal
    apply(subst (asm) (1) nth_bit_tail_IMP_init_while_cond_def)
    apply(simp only: prefix_simps)
    by (fastforce simp add: nth_bit_tail_complete_simps)

  subgoal
    apply(subst (asm) nth_bit_tail_IMP_init_while_cond_def)
    apply(subst (asm) nth_bit_tail_IMP_loop_body_def)
    apply(simp only: prefix_simps)
    by (fastforce simp add: Let_def nth_bit_tail_complete_simps)

  subgoal
    apply(subst (asm) (1) nth_bit_tail_IMP_init_while_cond_def)
    apply(subst (asm) (1) nth_bit_tail_IMP_loop_body_def)
    apply(simp only: prefix_simps)
    by (fastforce simp add: Let_def nth_bit_tail_complete_simps)
  done

lemma nth_bit_tail_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ nth_bit_tail_pref) nth_bit_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix nth_bit_tail_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemmas nth_bit_tail_complete_time_simps =
  nth_bit_tail_imp_subprogram_time_simps
  nth_bit_tail_IMP_subprogram_simps
  nth_bit_tail_imp_time_acc_2
  nth_bit_tail_imp_time_acc_3
  nth_bit_tail_state_translators

lemma nth_bit_tail_IMP_Minus_correct_time:
  "(invoke_subprogram p nth_bit_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = nth_bit_tail_imp_time 0 (nth_bit_tail_imp_to_HOL_state p s)"
  apply(induction "nth_bit_tail_imp_to_HOL_state p s" arbitrary: s s' t
      rule: nth_bit_tail_imp.induct)
  apply(subst nth_bit_tail_imp_time.simps)
  apply(simp only: nth_bit_tail_IMP_Minus_def prefix_simps)

  apply(vcg_time nth_bit_tail_IMP_vars)

  subgoal
    apply(subst (asm) (3) nth_bit_tail_IMP_init_while_cond_def)
    apply(subst (asm) (2) nth_bit_tail_IMP_after_loop_def)
    apply(simp only: prefix_simps)
    apply(vcg_time nth_bit_tail_IMP_vars)
    by (force simp add: nth_bit_tail_IMP_subprogram_simps nth_bit_tail_imp_subprogram_time_simps
        nth_bit_tail_state_translators)

  apply(simp add: add.assoc)
  apply(vcg_time nth_bit_tail_IMP_vars)

  subgoal
    apply(subst (asm) (1) nth_bit_tail_IMP_init_while_cond_def)
    apply(simp only: prefix_simps)
    by (fastforce simp add: nth_bit_tail_complete_simps)

  subgoal
    apply(subst (asm) (1) nth_bit_tail_IMP_init_while_cond_def)
    apply(subst (asm) (1) nth_bit_tail_IMP_loop_body_def)
    apply(simp only: prefix_simps)
    by (fastforce simp add: Let_def nth_bit_tail_complete_time_simps)

  subgoal
    apply(subst (asm) (1) nth_bit_tail_IMP_init_while_cond_def)
    apply(subst (asm) (1) nth_bit_tail_IMP_loop_body_def)
    apply(simp only: prefix_simps)
    by (fastforce simp add: Let_def nth_bit_tail_complete_time_simps)
  done

lemma nth_bit_tail_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) nth_bit_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
    \<lbrakk>t = (nth_bit_tail_imp_time 0 (nth_bit_tail_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) nth_bit_tail_ret_str) =
          nth_bit_tail_ret (nth_bit_tail_imp
                                        (nth_bit_tail_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using nth_bit_tail_IMP_Minus_correct_function
  by (auto simp: nth_bit_tail_IMP_Minus_correct_time)
    (meson nth_bit_tail_IMP_Minus_correct_effects set_mono_prefix)

subsection \<open>bit_length\<close>

subsubsection \<open>bit_length_acc\<close>

record bit_length_acc_state =
  bit_length_acc_acc::nat
  bit_length_acc_n::nat
  bit_length_acc_ret::nat

abbreviation "bit_length_acc_prefix \<equiv> ''bit_length_acc.''"
abbreviation "bit_length_acc_acc_str \<equiv> ''acc''"
abbreviation "bit_length_acc_n_str \<equiv> ''n''"
abbreviation "bit_length_acc_ret_str \<equiv> ''ret''"

definition "bit_length_acc_state_upd s \<equiv>
  (let
      bit_length_acc_acc' = bit_length_acc_acc s + 1;
      bit_length_acc_n' = bit_length_acc_n s div 2;
      ret = \<lparr>bit_length_acc_acc = bit_length_acc_acc',
             bit_length_acc_n = bit_length_acc_n',
             bit_length_acc_ret = bit_length_acc_ret s\<rparr>
  in
      ret
)"

definition "bit_length_acc_imp_compute_loop_condition s \<equiv>
  (let
      LESS_EQUAL_neq_zero_a' = 2;
      LESS_EQUAL_neq_zero_b' = bit_length_acc_n s;
      LESS_EQUAL_neq_zero_ret' = 0;
      LESS_EQUAL_neq_zero_state = \<lparr>LESS_EQUAL_neq_zero_a = LESS_EQUAL_neq_zero_a',
                                   LESS_EQUAL_neq_zero_b = LESS_EQUAL_neq_zero_b',
                                   LESS_EQUAL_neq_zero_ret = LESS_EQUAL_neq_zero_ret'\<rparr>;
      LESS_EQUAL_neq_zero_ret_state = LESS_EQUAL_neq_zero_imp LESS_EQUAL_neq_zero_state;
      condition = LESS_EQUAL_neq_zero_ret LESS_EQUAL_neq_zero_ret_state
  in
      condition
)"

definition "bit_length_acc_imp_after_loop s \<equiv>
  (let
      bit_length_acc_ret' = bit_length_acc_acc s;
      ret = \<lparr>bit_length_acc_acc = bit_length_acc_acc s,
             bit_length_acc_n = bit_length_acc_n s,
             bit_length_acc_ret = bit_length_acc_ret'\<rparr>
  in
      ret
)"

lemmas bit_length_acc_imp_subprogram_simps =
  bit_length_acc_state_upd_def
  bit_length_acc_imp_compute_loop_condition_def
  bit_length_acc_imp_after_loop_def

function bit_length_acc_imp::
  "bit_length_acc_state \<Rightarrow> bit_length_acc_state" where
  "bit_length_acc_imp s =
  (if bit_length_acc_imp_compute_loop_condition s \<noteq> 0
   then let next_iteration = bit_length_acc_imp (bit_length_acc_state_upd s)
        in next_iteration
   else let ret = bit_length_acc_imp_after_loop s
        in ret
  )"
  by simp+
termination
  apply (relation "measure bit_length_acc_n")
  apply (simp add: bit_length_acc_imp_subprogram_simps LESS_EQUAL_neq_zero_imp_correct)+
  by presburger

declare bit_length_acc_imp.simps [simp del]

lemma bit_length_acc_imp_correct[let_function_correctness]:
  "bit_length_acc_ret (bit_length_acc_imp s) =
    bit_length_acc (bit_length_acc_acc s) (bit_length_acc_n s)"
  apply (induction s rule: bit_length_acc_imp.induct)
  apply (subst bit_length_acc_imp.simps)
  apply (subst bit_length_acc.simps)
  apply (simp del: bit_length_acc.simps add: bit_length_acc_imp_subprogram_simps Let_def
    LESS_EQUAL_neq_zero_imp_correct)
  done

definition "bit_length_acc_state_upd_time t s \<equiv>
  (let
      bit_length_acc_acc' = bit_length_acc_acc s + 1;
      t = t + 2;
      bit_length_acc_n' = bit_length_acc_n s div 2;
      t = t + 2;
      ret = \<lparr>bit_length_acc_acc = bit_length_acc_acc',
             bit_length_acc_n = bit_length_acc_n',
             bit_length_acc_ret = bit_length_acc_ret s\<rparr>
  in
      t
)"

definition "bit_length_acc_imp_compute_loop_condition_time t s \<equiv>
  (let
      LESS_EQUAL_neq_zero_a' = 2;
      t = t + 2;
      LESS_EQUAL_neq_zero_b' = bit_length_acc_n s;
      t = t + 2;
      LESS_EQUAL_neq_zero_ret' = 0;
      t = t + 2;
      LESS_EQUAL_neq_zero_state = \<lparr>LESS_EQUAL_neq_zero_a = LESS_EQUAL_neq_zero_a',
                                   LESS_EQUAL_neq_zero_b = LESS_EQUAL_neq_zero_b',
                                   LESS_EQUAL_neq_zero_ret = LESS_EQUAL_neq_zero_ret'\<rparr>;
      LESS_EQUAL_neq_zero_ret_state = LESS_EQUAL_neq_zero_imp LESS_EQUAL_neq_zero_state;
      t = t + LESS_EQUAL_neq_zero_imp_time 0 LESS_EQUAL_neq_zero_state;
      condition = LESS_EQUAL_neq_zero_ret LESS_EQUAL_neq_zero_ret_state;
      t = t + 2
  in
      t
)"

definition "bit_length_acc_imp_after_loop_time t s \<equiv>
  (let
      bit_length_acc_ret' = bit_length_acc_acc s;
      t = t + 2;
      ret = \<lparr>bit_length_acc_acc = bit_length_acc_acc s,
             bit_length_acc_n = bit_length_acc_n s,
             bit_length_acc_ret = bit_length_acc_ret'\<rparr>
  in
      t
)"

lemmas bit_length_acc_imp_subprogram_time_simps =
  bit_length_acc_state_upd_time_def
  bit_length_acc_imp_compute_loop_condition_time_def
  bit_length_acc_imp_after_loop_time_def
  bit_length_acc_imp_subprogram_simps

function bit_length_acc_imp_time::
  "nat \<Rightarrow> bit_length_acc_state \<Rightarrow> nat" where
  "bit_length_acc_imp_time t s =
  bit_length_acc_imp_compute_loop_condition_time 0 s +
  (if bit_length_acc_imp_compute_loop_condition s \<noteq> 0
    then
      (let
        t = t + 1;
        next_iteration =
          bit_length_acc_imp_time (t + bit_length_acc_state_upd_time 0 s)
                         (bit_length_acc_state_upd s)
       in next_iteration)
    else
      (let
        t = t + 2;
        ret = t + bit_length_acc_imp_after_loop_time 0 s
       in ret)
  )"
  by auto
termination
  apply (relation "measure (bit_length_acc_n \<circ> snd)")
  apply (simp add: bit_length_acc_imp_subprogram_time_simps LESS_EQUAL_neq_zero_imp_correct)+
  by presburger

declare bit_length_acc_imp_time.simps [simp del]

lemma bit_length_acc_imp_time_acc:
  "(bit_length_acc_imp_time (Suc t) s) = Suc (bit_length_acc_imp_time t s)"
  by (induction t s rule: bit_length_acc_imp_time.induct)
    ((subst (1 2) bit_length_acc_imp_time.simps);
      (simp add: bit_length_acc_state_upd_def))

lemma bit_length_acc_imp_time_acc_2_aux:
  "(bit_length_acc_imp_time t s) = t + (bit_length_acc_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: bit_length_acc_imp_time_acc)+

lemma bit_length_acc_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (bit_length_acc_imp_time t s) = t + (bit_length_acc_imp_time 0 s)"
  by (rule bit_length_acc_imp_time_acc_2_aux)

lemma bit_length_acc_imp_time_acc_3:
  "(bit_length_acc_imp_time (a + b) s) = a + (bit_length_acc_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: bit_length_acc_imp_time_acc)+

abbreviation "bit_length_acc_while_cond \<equiv> ''condition''"

definition "bit_length_acc_IMP_init_while_cond \<equiv>
  \<comment> \<open>  LESS_EQUAL_neq_zero_a' = 2;\<close>
  (LESS_EQUAL_neq_zero_prefix @ LESS_EQUAL_neq_zero_a_str) ::= (A (N 2));;
  \<comment> \<open>  LESS_EQUAL_neq_zero_b' = bit_length_acc_n s;\<close>
  (LESS_EQUAL_neq_zero_prefix @ LESS_EQUAL_neq_zero_b_str) ::= (A (V bit_length_acc_n_str));;
  \<comment> \<open>  LESS_EQUAL_neq_zero_ret' = 0;\<close>
  (LESS_EQUAL_neq_zero_prefix @ LESS_EQUAL_neq_zero_ret_str) ::= (A (N 0));;
  \<comment> \<open>  LESS_EQUAL_neq_zero_state = \<lparr>LESS_EQUAL_neq_zero_a = LESS_EQUAL_neq_zero_a',\<close>
  \<comment> \<open>                               LESS_EQUAL_neq_zero_b = LESS_EQUAL_neq_zero_b',\<close>
  \<comment> \<open>                               LESS_EQUAL_neq_zero_ret = LESS_EQUAL_neq_zero_ret'\<rparr>;\<close>
  \<comment> \<open>  LESS_EQUAL_neq_zero_ret_state = LESS_EQUAL_neq_zero_imp LESS_EQUAL_neq_zero_state;\<close>
  (invoke_subprogram LESS_EQUAL_neq_zero_prefix LESS_EQUAL_neq_zero_IMP_Minus);;
  \<comment> \<open>  condition = LESS_EQUAL_neq_zero_ret LESS_EQUAL_neq_zero_ret_state\<close>
  (bit_length_acc_while_cond) ::= (A (V (LESS_EQUAL_neq_zero_prefix @ LESS_EQUAL_neq_zero_ret_str)))
"

definition "bit_length_acc_IMP_loop_body \<equiv>
  \<comment> \<open>  bit_length_acc_acc' = bit_length_acc_acc s + 1;\<close>
  (bit_length_acc_acc_str) ::= (Plus (V bit_length_acc_acc_str) (N 1));;
  \<comment> \<open>  bit_length_acc_n' = bit_length_acc_n s div 2;\<close>
  (bit_length_acc_n_str) ::= (RightShift (V bit_length_acc_n_str))
  \<comment> \<open>  ret = \<lparr>bit_length_acc_acc = bit_length_acc_acc',\<close>
  \<comment> \<open>         bit_length_acc_n = bit_length_acc_n',\<close>
  \<comment> \<open>         bit_length_acc_ret = bit_length_acc_ret s\<rparr>\<close>
"

definition "bit_length_acc_IMP_after_loop \<equiv>
  \<comment> \<open>  bit_length_acc_ret' = bit_length_acc_acc s;\<close>
  (bit_length_acc_ret_str) ::= (A (V bit_length_acc_acc_str))
  \<comment> \<open>  ret = \<lparr>bit_length_acc_acc = bit_length_acc_acc s,\<close>
  \<comment> \<open>         bit_length_acc_n = bit_length_acc_n s,\<close>
  \<comment> \<open>         bit_length_acc_ret = bit_length_acc_ret'\<rparr>\<close>
"

definition bit_length_acc_IMP_Minus where
  "bit_length_acc_IMP_Minus \<equiv>
  bit_length_acc_IMP_init_while_cond;;
  WHILE bit_length_acc_while_cond \<noteq>0 DO (
    bit_length_acc_IMP_loop_body;;
    bit_length_acc_IMP_init_while_cond
  );;
  bit_length_acc_IMP_after_loop"

abbreviation "bit_length_acc_IMP_vars\<equiv>
  {bit_length_acc_acc_str, bit_length_acc_n_str, bit_length_acc_ret_str}"

lemmas bit_length_acc_IMP_subprogram_simps =
  bit_length_acc_IMP_init_while_cond_def
  bit_length_acc_IMP_loop_body_def
  bit_length_acc_IMP_after_loop_def

definition "bit_length_acc_imp_to_HOL_state p s =
  \<lparr>bit_length_acc_acc = (s (add_prefix p bit_length_acc_acc_str)),
   bit_length_acc_n = (s (add_prefix p bit_length_acc_n_str)),
   bit_length_acc_ret = (s (add_prefix p bit_length_acc_ret_str))\<rparr>"

lemmas bit_length_acc_state_translators =
  bit_length_acc_imp_to_HOL_state_def
  LESS_EQUAL_neq_zero_imp_to_HOL_state_def

lemmas bit_length_acc_complete_simps =
  bit_length_acc_IMP_subprogram_simps
  bit_length_acc_imp_subprogram_simps
  bit_length_acc_state_translators

lemma bit_length_acc_IMP_Minus_correct_function:
  "(invoke_subprogram p bit_length_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p bit_length_acc_ret_str)
      = bit_length_acc_ret
          (bit_length_acc_imp (bit_length_acc_imp_to_HOL_state p s))"
  apply(induction "bit_length_acc_imp_to_HOL_state p s" arbitrary: s s' t
    rule: bit_length_acc_imp.induct)
  apply(subst bit_length_acc_imp.simps)
  apply(simp only: bit_length_acc_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule While_tE)

  subgoal
    apply(simp only: bit_length_acc_IMP_subprogram_simps prefix_simps)
    apply(erule Seq_E)+
    apply(erule LESS_EQUAL_neq_zero_IMP_Minus_correct[where vars = "bit_length_acc_IMP_vars"])
    subgoal premises p using p(10) by fastforce
    by(fastforce simp: bit_length_acc_IMP_subprogram_simps
        bit_length_acc_imp_subprogram_simps
        bit_length_acc_state_translators)

  apply(erule Seq_E)+
  apply(dest_com_gen)

  subgoal
      apply(simp only: bit_length_acc_IMP_init_while_cond_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule LESS_EQUAL_neq_zero_IMP_Minus_correct[where vars = "bit_length_acc_IMP_vars"])
      subgoal premises p using p(14) by fastforce
      by(fastforce simp add: bit_length_acc_complete_simps)

  subgoal
      apply(subst (asm) bit_length_acc_IMP_init_while_cond_def)
      apply(simp only: bit_length_acc_IMP_loop_body_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule LESS_EQUAL_neq_zero_IMP_Minus_correct[where vars = "bit_length_acc_IMP_vars"])
      subgoal premises p using p(11) by fastforce
      by (simp only: bit_length_acc_imp_subprogram_simps
          bit_length_acc_state_translators Let_def, force)

  subgoal
      apply(simp only: bit_length_acc_IMP_init_while_cond_def prefix_simps
          bit_length_acc_IMP_loop_body_def)
      apply(erule Seq_E)+
      apply(erule LESS_EQUAL_neq_zero_IMP_Minus_correct[where vars = "bit_length_acc_IMP_vars"])
      subgoal premises p using p(15) by fastforce
      by (simp only: bit_length_acc_imp_subprogram_simps
          bit_length_acc_state_translators Let_def, force)
  done

lemma bit_length_acc_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ bit_length_acc_pref) bit_length_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix bit_length_acc_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemmas bit_length_acc_complete_time_simps =
  bit_length_acc_imp_subprogram_time_simps
  bit_length_acc_imp_time_acc
  bit_length_acc_imp_time_acc_2
  bit_length_acc_imp_time_acc_3
  bit_length_acc_state_translators

lemma bit_length_acc_IMP_Minus_correct_time:
  "(invoke_subprogram p bit_length_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = bit_length_acc_imp_time 0 (bit_length_acc_imp_to_HOL_state p s)"
  apply(induction "bit_length_acc_imp_to_HOL_state p s" arbitrary: s s' t
      rule: bit_length_acc_imp.induct)
  apply(subst bit_length_acc_imp_time.simps)
  apply(simp only: bit_length_acc_IMP_Minus_def prefix_simps)

  apply(erule Seq_tE)+
  apply(erule While_tE_time)

  subgoal
    apply(simp only: bit_length_acc_IMP_subprogram_simps prefix_simps)
    apply(erule Seq_tE)+
    apply(erule LESS_EQUAL_neq_zero_IMP_Minus_correct[where vars = "bit_length_acc_IMP_vars"])
    subgoal premises p using p(16) by fastforce
    by (force simp: bit_length_acc_IMP_subprogram_simps
        bit_length_acc_imp_subprogram_time_simps bit_length_acc_state_translators)

  apply(erule Seq_tE)+
  apply(simp add: add.assoc)
  apply(dest_com_gen_time)

  subgoal
    apply(simp only: bit_length_acc_IMP_init_while_cond_def prefix_simps)
    apply(erule Seq_tE)+
    apply(erule LESS_EQUAL_neq_zero_IMP_Minus_correct[where vars = "bit_length_acc_IMP_vars"])
    subgoal premises p using p(25) by fastforce
    by(fastforce simp add: bit_length_acc_complete_simps)

  subgoal
    apply(subst (asm) bit_length_acc_IMP_init_while_cond_def)
    apply(simp only: bit_length_acc_IMP_loop_body_def prefix_simps)
    apply(erule Seq_tE)+
    apply(erule LESS_EQUAL_neq_zero_IMP_Minus_correct[where vars = "bit_length_acc_IMP_vars"])
    subgoal premises p using p(19) by fastforce
    by (simp only: bit_length_acc_imp_subprogram_time_simps
        bit_length_acc_state_translators Let_def, force)

  subgoal
    apply(simp only: prefix_simps bit_length_acc_IMP_init_while_cond_def
        bit_length_acc_IMP_loop_body_def)
    apply(erule Seq_tE)+
    apply(erule LESS_EQUAL_neq_zero_IMP_Minus_correct[where vars = "bit_length_acc_IMP_vars"])
    subgoal premises p using p(27) by fastforce
    apply(simp only: bit_length_acc_complete_time_simps Let_def)
    by force

  done

lemma bit_length_acc_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) bit_length_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (bit_length_acc_imp_time 0 (bit_length_acc_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) bit_length_acc_ret_str) =
          bit_length_acc_ret (bit_length_acc_imp
                                        (bit_length_acc_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using bit_length_acc_IMP_Minus_correct_function
    bit_length_acc_IMP_Minus_correct_time
    bit_length_acc_IMP_Minus_correct_effects
  by (meson set_mono_prefix)

subsubsection \<open>bit_length_tail\<close>

record bit_length_tail_state =
  bit_length_tail_n::nat
  bit_length_tail_ret::nat

abbreviation "bit_length_tail_prefix \<equiv> ''bit_length_tail.''"
abbreviation "bit_length_tail_n_str \<equiv> ''n''"
abbreviation "bit_length_tail_ret_str \<equiv> ''ret''"

definition "bit_length_tail_state_upd s =
  (let
      bit_length_acc_acc' = 1;
      bit_length_acc_n' = bit_length_tail_n s;
      bit_length_acc_ret' = 0;
      bit_length_acc_state = \<lparr>bit_length_acc_acc = bit_length_acc_acc',
                              bit_length_acc_n = bit_length_acc_n',
                              bit_length_acc_ret = bit_length_acc_ret'\<rparr>;
      bit_length_acc_ret_state = bit_length_acc_imp bit_length_acc_state;
      bit_length_tail_ret' = bit_length_acc_ret bit_length_acc_ret_state;
      ret = \<lparr>bit_length_tail_n = bit_length_tail_n s,
             bit_length_tail_ret = bit_length_tail_ret'\<rparr>
  in
      ret
)"

function bit_length_tail_imp ::
  "bit_length_tail_state \<Rightarrow> bit_length_tail_state" where
  "bit_length_tail_imp s =
  (let
      ret = bit_length_tail_state_upd s
    in
      ret
  )"
  by simp+
termination
  by (relation "measure bit_length_tail_n") simp

declare bit_length_tail_imp.simps [simp del]

lemma bit_length_tail_imp_correct[let_function_correctness]:
  "bit_length_tail_ret (bit_length_tail_imp s) =
    bit_length_tail (bit_length_tail_n s)"
  apply (simp only: bit_length_tail_imp.simps Let_def bit_length_tail_state_upd_def
    bit_length_acc_imp_correct bit_length_tail_def)
  by simp

function bit_length_tail_imp_time ::
  "nat \<Rightarrow> bit_length_tail_state \<Rightarrow> nat" where
  "bit_length_tail_imp_time t s =
  (let
      bit_length_acc_acc' = 1;
      t = t + 2;
      bit_length_acc_n' = bit_length_tail_n s;
      t = t + 2;
      bit_length_acc_ret' = 0;
      t = t + 2;
      bit_length_acc_state = \<lparr>bit_length_acc_acc = bit_length_acc_acc',
                              bit_length_acc_n = bit_length_acc_n',
                              bit_length_acc_ret = bit_length_acc_ret'\<rparr>;
      bit_length_acc_ret_state = bit_length_acc_imp bit_length_acc_state;
      t = t + bit_length_acc_imp_time 0 bit_length_acc_state;
      bit_length_tail_ret' = bit_length_acc_ret bit_length_acc_ret_state;
      t = t + 2;
      ret = \<lparr>bit_length_tail_n = bit_length_tail_n s,
             bit_length_tail_ret = bit_length_tail_ret'\<rparr>
  in
      t
  )"
  by auto
termination
  by (relation "measure (bit_length_tail_n \<circ> snd)") simp

declare bit_length_tail_imp_time.simps [simp del]

lemma bit_length_tail_imp_time_acc:
  "(bit_length_tail_imp_time (Suc t) s) = Suc (bit_length_tail_imp_time t s)"
  by (induction t s rule: bit_length_tail_imp_time.induct)
    ((subst (1 2) bit_length_tail_imp_time.simps);
      (simp add: bit_length_tail_state_upd_def Let_def))

lemma bit_length_tail_imp_time_acc_2_aux:
  "(bit_length_tail_imp_time t s) = t + (bit_length_tail_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: bit_length_tail_imp_time_acc)+

lemma bit_length_tail_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (bit_length_tail_imp_time t s) = t + (bit_length_tail_imp_time 0 s)"
  by (rule bit_length_tail_imp_time_acc_2_aux)

lemma bit_length_tail_imp_time_acc_3:
  "(bit_length_tail_imp_time (a + b) s) = a + (bit_length_tail_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: bit_length_tail_imp_time_acc)+

definition bit_length_tail_IMP_Minus where
  "bit_length_tail_IMP_Minus \<equiv>
  \<comment> \<open>  bit_length_acc_acc' = 1;\<close>
  (bit_length_acc_prefix @ bit_length_acc_acc_str) ::= (A (N 1));;
  \<comment> \<open>  bit_length_acc_n' = bit_length_tail_n s;\<close>
  (bit_length_acc_prefix @ bit_length_acc_n_str) ::= (A (V bit_length_tail_n_str));;
  \<comment> \<open>  bit_length_acc_ret' = 0;\<close>
  (bit_length_acc_prefix @ bit_length_acc_ret_str) ::= (A (N 0));;
  \<comment> \<open>  bit_length_acc_state = \<lparr>bit_length_acc_acc = bit_length_acc_acc',\<close>
  \<comment> \<open>                          bit_length_acc_n = bit_length_acc_n',\<close>
  \<comment> \<open>                          bit_length_acc_ret = bit_length_acc_ret'\<rparr>;\<close>
  \<comment> \<open>  bit_length_acc_ret_state = bit_length_acc_imp bit_length_acc_state;\<close>
  (invoke_subprogram bit_length_acc_prefix bit_length_acc_IMP_Minus);;
  \<comment> \<open>  bit_length_tail_ret' = bit_length_acc_ret bit_length_acc_ret_state;\<close>
  (bit_length_tail_ret_str) ::= (A (V (bit_length_acc_prefix @ bit_length_acc_ret_str)))
  \<comment> \<open>  ret = \<lparr>bit_length_tail_n = bit_length_tail_n s,\<close>
  \<comment> \<open>         bit_length_tail_ret = bit_length_tail_ret'\<rparr>\<close>
"

abbreviation "bit_length_tail_IMP_vars \<equiv>
  {bit_length_tail_n_str, bit_length_tail_ret_str}"

definition "bit_length_tail_imp_to_HOL_state p s =
  \<lparr>bit_length_tail_n = (s (add_prefix p bit_length_tail_n_str)),
   bit_length_tail_ret = (s (add_prefix p bit_length_tail_ret_str))\<rparr>"

lemmas bit_length_tail_state_translators =
  bit_length_tail_imp_to_HOL_state_def
  bit_length_acc_imp_to_HOL_state_def

lemma bit_length_tail_IMP_Minus_correct_function:
  "(invoke_subprogram p bit_length_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p bit_length_tail_ret_str)
      = bit_length_tail_ret
          (bit_length_tail_imp (bit_length_tail_imp_to_HOL_state p s))"
  apply(subst bit_length_tail_imp.simps)
  apply(simp only: bit_length_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule bit_length_acc_IMP_Minus_correct[where vars = "bit_length_tail_IMP_vars"])
  subgoal premises p using p(5) by fastforce
  by(fastforce simp: bit_length_tail_state_translators
    bit_length_tail_state_upd_def)

lemma bit_length_tail_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ bit_length_tail_pref) bit_length_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix bit_length_tail_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma bit_length_tail_IMP_Minus_correct_time:
  "(invoke_subprogram p bit_length_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = bit_length_tail_imp_time 0 (bit_length_tail_imp_to_HOL_state p s)"
  apply(subst bit_length_tail_imp_time.simps)
  apply(simp only: bit_length_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule bit_length_acc_IMP_Minus_correct[where vars = "bit_length_tail_IMP_vars"])
  subgoal premises p using p(9) by fastforce
  by(fastforce simp add: Let_def bit_length_tail_state_translators)

lemma bit_length_tail_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) bit_length_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (bit_length_tail_imp_time 0 (bit_length_tail_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) bit_length_tail_ret_str) =
          bit_length_tail_ret (bit_length_tail_imp
                                        (bit_length_tail_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using bit_length_tail_IMP_Minus_correct_function
    bit_length_tail_IMP_Minus_correct_time
    bit_length_tail_IMP_Minus_correct_effects
  by (meson set_mono_prefix)

end
