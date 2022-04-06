theory IMP_Minus_To_IMP_Minus_Minus_State_Translations_IMP
  imports
    Primitives_IMP_Minus
    IMP_Minus_To_IMP_Minus_Minus_State_Translations_nat
    IMP_Minus.Com
begin

unbundle IMP_Minus_Minus_Com.no_com_syntax


abbreviation "hash_as_nat \<equiv> 35"
lemma hash_encode_val: "encode_char (CHR ''#'') = hash_as_nat"
  by (simp add: encode_char_def)

record dropWhile_char_state =
  dropWhile_char_n::nat
  dropWhile_char_ret::nat

abbreviation "dropWhile_char_prefix \<equiv> ''dropWhile_char.''"
abbreviation "dropWhile_char_n_str \<equiv> ''n''"
abbreviation "dropWhile_char_ret_str \<equiv> ''ret''"

fun dropWhile_char':: "nat \<Rightarrow> nat" where
  "dropWhile_char' n =
    (if n \<noteq> 0 \<and> hd_nat n = encode_char (CHR ''#'')
     then dropWhile_char' (tl_nat n)
     else n
    )"

lemma dropWhile_char'_correct: "dropWhile_char n = dropWhile_char' n"
  by (induction n rule: dropWhile_char.induct) (simp)

definition "dropWhile_char_state_upd s \<equiv>
      let
        tl_xs' = dropWhile_char_n s;
        tl_ret' = 0;
        tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
        tl_ret_state = tl_imp tl_state;
        dropWhile_char_n' = tl_ret tl_ret_state;
        dropWhile_char_ret' = dropWhile_char_ret s;
        ret = \<lparr>dropWhile_char_n = dropWhile_char_n',
               dropWhile_char_ret = dropWhile_char_ret'\<rparr>
      in
        ret"

definition "dropWhile_char_imp_compute_loop_condition s \<equiv>
  (let NOTEQUAL_neq_zero_a' = dropWhile_char_n s;
       NOTEQUAL_neq_zero_b' = 0;
       NOTEQUAL_neq_zero_ret' = 0;
       NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                                  NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                                  NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
       NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
       hd_xs' = dropWhile_char_n s;
       hd_ret' = 0;
       hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
       hd_ret_state = hd_imp hd_state;
       EQUAL_neq_zero_a' = hd_ret hd_ret_state;
       EQUAL_neq_zero_b' = hash_as_nat;
       EQUAL_neq_zero_ret' = 0;
       EQUAL_neq_zero_state = \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
                               EQUAL_neq_zero_b = EQUAL_neq_zero_b',
                               EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
       EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
       AND_neq_zero_a' = NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state;
       AND_neq_zero_b' = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;
       AND_neq_zero_ret' = 0;
       AND_neq_zero_state = \<lparr>AND_neq_zero_a = AND_neq_zero_a',
                             AND_neq_zero_b = AND_neq_zero_b',
                             AND_neq_zero_ret = AND_neq_zero_ret'\<rparr>;
       AND_neq_zero_ret_state = AND_neq_zero_imp AND_neq_zero_state;
       condition = AND_neq_zero_ret AND_neq_zero_ret_state
   in condition
  )"

definition "dropWhile_char_imp_after_loop s \<equiv>
  (let
    dropWhile_char_n' = dropWhile_char_n s;
    dropWhile_char_ret' = dropWhile_char_n s;
    ret = \<lparr>dropWhile_char_n = dropWhile_char_n',
           dropWhile_char_ret = dropWhile_char_ret'\<rparr>
   in ret
  )"

lemmas dropWhile_char_imp_subprogram_simps =
  dropWhile_char_imp_after_loop_def
  dropWhile_char_state_upd_def
  dropWhile_char_imp_compute_loop_condition_def

function dropWhile_char_imp:: "dropWhile_char_state \<Rightarrow> dropWhile_char_state" where
  "dropWhile_char_imp s =
  (if dropWhile_char_imp_compute_loop_condition s \<noteq> 0
   then
    (let next_iteration = dropWhile_char_imp (dropWhile_char_state_upd s)
      in next_iteration)
  else
    (let ret = dropWhile_char_imp_after_loop s in ret)
  )"
    by simp+
termination
  by (relation "measure dropWhile_char_n", simp)
    (simp add: dropWhile_char_imp_subprogram_simps tl_imp_correct AND_neq_zero_imp_correct
      NOTEQUAL_neq_zero_imp_correct split:if_splits)+

declare dropWhile_char_imp.simps [simp del]

lemma dropWhile_char_imp_correct:
  "dropWhile_char_ret (dropWhile_char_imp s) = dropWhile_char' (dropWhile_char_n s)"
  by (induction "dropWhile_char_n s" arbitrary: s rule: dropWhile_char'.induct)
    (subst dropWhile_char_imp.simps, simp add: dropWhile_char_imp_subprogram_simps tl_imp_correct 
    hd_imp_correct AND_neq_zero_imp_correct EQUAL_neq_zero_imp_correct NOTEQUAL_neq_zero_imp_correct
    hash_encode_val)

definition "dropWhile_char_state_upd_time t s \<equiv>
      let
        tl_xs' = dropWhile_char_n s;
        t = t + 2;
        tl_ret' = 0;
        t = t + 2;
        tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
        tl_ret_state = tl_imp tl_state;
        t = t + tl_imp_time 0 tl_state;
        dropWhile_char_n' = tl_ret tl_ret_state;
        t = t + 2;
        dropWhile_char_ret' = dropWhile_char_ret s;
        t = t + 2;
        ret = t
      in
        ret"

definition "dropWhile_char_imp_compute_loop_condition_time t s \<equiv>
  (let NOTEQUAL_neq_zero_a' = dropWhile_char_n s;
       t = t + 2;
       NOTEQUAL_neq_zero_b' = 0;
       t = t + 2;
       NOTEQUAL_neq_zero_ret' = 0;
       t = t + 2;
       NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                                  NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                                  NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
       NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
       t = t + NOTEQUAL_neq_zero_imp_time 0 NOTEQUAL_neq_zero_state;
       hd_xs' = dropWhile_char_n s;
       t = t + 2;
       hd_ret' = 0;
       t = t + 2;
       hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
       hd_ret_state = hd_imp hd_state;
       t = t + hd_imp_time 0 hd_state;
       EQUAL_neq_zero_a' = hd_ret hd_ret_state;
       t = t + 2;
       EQUAL_neq_zero_b' = hash_as_nat;
       t = t + 2;
       EQUAL_neq_zero_ret' = 0;
       t = t + 2;
       EQUAL_neq_zero_state = \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
                               EQUAL_neq_zero_b = EQUAL_neq_zero_b',
                               EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
       EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
       t = t + EQUAL_neq_zero_imp_time 0 EQUAL_neq_zero_state;
       AND_neq_zero_a' = NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state;
       t = t + 2;
       AND_neq_zero_b' = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;
       t = t + 2;
       AND_neq_zero_ret' = 0;
       t = t + 2;
       AND_neq_zero_state = \<lparr>AND_neq_zero_a = AND_neq_zero_a',
                             AND_neq_zero_b = AND_neq_zero_b',
                             AND_neq_zero_ret = AND_neq_zero_ret'\<rparr>;
       AND_neq_zero_ret_state = AND_neq_zero_imp AND_neq_zero_state;
       t = t + AND_neq_zero_imp_time 0 AND_neq_zero_state;
       ret = t
   in ret
  )"

definition "dropWhile_char_imp_after_loop_time (t::nat) (s::dropWhile_char_state) \<equiv>
  (let
    dropWhile_char_n' = dropWhile_char_n s;
    t = t + 2;
    dropWhile_char_ret' = dropWhile_char_n s;
    t = t + 2;
    ret = t
   in ret
  )"

lemmas dropWhile_char_imp_subprogram_simps_time =
  dropWhile_char_imp_after_loop_time_def
  dropWhile_char_state_upd_time_def
  dropWhile_char_imp_compute_loop_condition_time_def

function dropWhile_char_imp_time:: "nat \<Rightarrow> dropWhile_char_state \<Rightarrow> nat" where
  "dropWhile_char_imp_time t s =
   dropWhile_char_imp_compute_loop_condition_time 0 s +
  (if dropWhile_char_imp_compute_loop_condition s \<noteq> 0
   then
    (let
        t = t + 1;
        next_iteration
          = dropWhile_char_imp_time (t + dropWhile_char_state_upd_time 0 s)
                                    (dropWhile_char_state_upd s)
     in next_iteration)
  else
    (let
        t = t + 2;
        ret = t + dropWhile_char_imp_after_loop_time 0 s
     in ret)
  )"
  by auto
termination
  by (relation "measure (dropWhile_char_n \<circ> snd)", simp)
    (simp add: dropWhile_char_imp_compute_loop_condition_def tl_imp_correct
      dropWhile_char_state_upd_def AND_neq_zero_imp_correct NOTEQUAL_neq_zero_imp_correct
      split: if_splits)

declare dropWhile_char_imp_time.simps [simp del]

lemmas dropWhile_char_imp_subprogram_time_simps =
  dropWhile_char_imp_subprogram_simps
  dropWhile_char_imp_after_loop_time_def
  dropWhile_char_state_upd_time_def
  dropWhile_char_imp_compute_loop_condition_time_def

lemma dropWhile_char_imp_time_acc:
  "(dropWhile_char_imp_time (Suc t) s) = Suc (dropWhile_char_imp_time t s)"
  by (induction t s rule: dropWhile_char_imp_time.induct) (simp add: dropWhile_char_imp_time.simps)

lemma dropWhile_char_imp_time_acc_2:
  "(dropWhile_char_imp_time x s) = x + (dropWhile_char_imp_time 0 s)"
  by (induction x arbitrary: s) (simp add: dropWhile_char_imp_time_acc)+

lemma dropWhile_char_imp_time_acc_2_simp:
  "(dropWhile_char_imp_time (n_hashes_state_upd_time 0 s) s') =
   (n_hashes_state_upd_time 0 s) + (dropWhile_char_imp_time 0 s')"
  by (rule dropWhile_char_imp_time_acc_2)

abbreviation "dropWhile_char_while_cond \<equiv> ''condition''"

definition "dropWhile_char_IMP_init_while_cond \<equiv>
  \<comment> \<open>(NOTEQUAL_neq_zero_a' = dropWhile_char_n s;\<close>
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_a_str) ::= (A (V dropWhile_char_n_str));;
  \<comment> \<open>(NOTEQUAL_neq_zero_b' = 0;\<close>
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_b_str) ::= (A (N 0));;
  \<comment> \<open>(NOTEQUAL_neq_zero_ret' = 0;\<close>
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str) ::= (A (N 0));;
  \<comment> \<open>(NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',\<close>
  \<comment> \<open>(                          NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',\<close>
  \<comment> \<open>(                          NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;\<close>
  \<comment> \<open>(NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;\<close>
  invoke_subprogram NOTEQUAL_neq_zero_prefix NOTEQUAL_neq_zero_IMP_Minus;;
  \<comment> \<open>(hd_xs' = dropWhile_char_n s;\<close>
  (hd_prefix @ hd_xs_str) ::= (A (V dropWhile_char_n_str));;
  \<comment> \<open>(hd_ret' = 0;\<close>
  (hd_prefix @ hd_ret_str) ::= (A (N 0));;
  \<comment> \<open>(hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;\<close>
  \<comment> \<open>(hd_ret_state = hd_imp hd_state;\<close>
  invoke_subprogram hd_prefix hd_IMP_Minus;;
  \<comment> \<open>(EQUAL_neq_zero_a' = hd_ret hd_ret_state;\<close>
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_a_str) ::= (A (V (hd_prefix @ hd_ret_str)));;
  \<comment> \<open>(EQUAL_neq_zero_b' = hash_as_nat;\<close>
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_b_str) ::= (A (N hash_as_nat));;
  \<comment> \<open>(EQUAL_neq_zero_ret' = 0;\<close>
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str) ::= (A (N 0));;
  \<comment> \<open>(EQUAL_neq_zero_state = \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',\<close>
  \<comment> \<open>(                       EQUAL_neq_zero_b = EQUAL_neq_zero_b',\<close>
  \<comment> \<open>(                       EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;\<close>
  \<comment> \<open>(EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;\<close>
  invoke_subprogram EQUAL_neq_zero_prefix EQUAL_neq_zero_IMP_Minus;;
  \<comment> \<open>(AND_neq_zero_a' = NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state;\<close>
  (AND_neq_zero_prefix @ AND_neq_zero_a_str) ::=
    (A (V (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str)));;
  \<comment> \<open>(AND_neq_zero_b' = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;\<close>
  (AND_neq_zero_prefix @ AND_neq_zero_b_str) ::=
    (A (V (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str)));;
  \<comment> \<open>(AND_neq_zero_ret' = 0;\<close>
  (AND_neq_zero_prefix @ AND_neq_zero_ret_str) ::= (A (N 0));;
  \<comment> \<open>(AND_neq_zero_state = \<lparr>AND_neq_zero_a = AND_neq_zero_a',\<close>
  \<comment> \<open>(                     AND_neq_zero_b = AND_neq_zero_b',\<close>
  \<comment> \<open>(                     AND_neq_zero_ret = AND_neq_zero_ret'\<rparr>;\<close>
  \<comment> \<open>(AND_neq_zero_ret_state = AND_neq_zero_imp AND_neq_zero_state;\<close>
  invoke_subprogram AND_neq_zero_prefix AND_neq_zero_IMP_Minus;;
  \<comment> \<open>(condition = AND_neq_zero_ret AND_neq_zero_ret_state\<close>
  dropWhile_char_while_cond ::= (A (V (AND_neq_zero_prefix @ AND_neq_zero_ret_str)))
  "

definition "dropWhile_char_IMP_loop_body \<equiv>
  \<comment> \<open>tl_xs' = dropWhile_char_n s;\<close>
  (tl_prefix @ tl_xs_str) ::= (A (V dropWhile_char_n_str));;
  \<comment> \<open>tl_ret' = 0;\<close>
  (tl_prefix @ tl_ret_str) ::= (A (N 0));;
  \<comment> \<open>tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;\<close>
  \<comment> \<open>tl_ret_state = tl_imp tl_state;\<close>
  invoke_subprogram tl_prefix tl_IMP_Minus;;
  \<comment> \<open>dropWhile_char_n' = tl_ret tl_ret_state;\<close>
  dropWhile_char_n_str ::= (A (V (tl_prefix @ tl_ret_str)));;
  \<comment> \<open>dropWhile_char_ret' = dropWhile_char_ret s;\<close>
  dropWhile_char_ret_str ::= (A (V dropWhile_char_ret_str))
  \<comment> \<open>ret = \<lparr>dropWhile_char_n = dropWhile_char_n',\<close>
  \<comment> \<open>       dropWhile_char_ret = dropWhile_char_ret'\<rparr>\<close>
  "


definition "dropWhile_char_IMP_after_loop \<equiv>
  \<comment> \<open>  dropWhile_char_n' = dropWhile_char_n s;\<close>
  dropWhile_char_n_str ::= (A (V dropWhile_char_n_str));;
  \<comment> \<open>  dropWhile_char_ret' = dropWhile_char_n s;\<close>
  dropWhile_char_ret_str ::= (A (V dropWhile_char_n_str))
  \<comment> \<open>  ret = \<lparr>dropWhile_char_n = dropWhile_char_n',\<close>
  \<comment> \<open>         dropWhile_char_ret = dropWhile_char_ret'\<rparr>\<close>
  "

definition dropWhile_char_IMP_Minus where
  "dropWhile_char_IMP_Minus \<equiv>
  dropWhile_char_IMP_init_while_cond;;
  WHILE dropWhile_char_while_cond \<noteq>0 DO (
    dropWhile_char_IMP_loop_body;;
    dropWhile_char_IMP_init_while_cond
  );;
  dropWhile_char_IMP_after_loop"

abbreviation
  "dropWhile_char_IMP_vars \<equiv>
  {dropWhile_char_n_str, dropWhile_char_ret_str}"

lemmas dropWhile_char_IMP_subprogram_simps =
  dropWhile_char_IMP_init_while_cond_def
  dropWhile_char_IMP_loop_body_def
  dropWhile_char_IMP_after_loop_def

definition "dropWhile_char_imp_to_HOL_state p s =
  \<lparr>dropWhile_char_n = (s (add_prefix p dropWhile_char_n_str)),
   dropWhile_char_ret = (s (add_prefix p dropWhile_char_ret_str))\<rparr>"

lemmas dropWhile_char_state_translators =
  hd_imp_to_HOL_state_def
  tl_imp_to_HOL_state_def
  dropWhile_char_imp_to_HOL_state_def
  AND_neq_zero_imp_to_HOL_state_def
  EQUAL_neq_zero_imp_to_HOL_state_def
  NOTEQUAL_neq_zero_imp_to_HOL_state_def

lemmas dropWhile_char_complete_simps =
  dropWhile_char_IMP_subprogram_simps
  dropWhile_char_imp_subprogram_simps
  dropWhile_char_state_translators

abbreviation
  "dropWhile_char_IMP_subprogram_prefixes \<equiv>
  {NOTEQUAL_neq_zero_prefix, EQUAL_neq_zero_prefix, AND_neq_zero_prefix, hd_prefix, tl_prefix}"

lemma dropWhile_char_IMP_subprogram_prefixes_aux:
  "v \<in> dropWhile_char_IMP_vars
    \<Longrightarrow> \<forall> prfx \<in> dropWhile_char_IMP_subprogram_prefixes. \<not> set prfx \<subseteq> set v"
  by fastforce

lemma dropWhile_char_IMP_Minus_correct_function:
  "(invoke_subprogram p dropWhile_char_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p dropWhile_char_ret_str)
      = dropWhile_char_ret (dropWhile_char_imp (dropWhile_char_imp_to_HOL_state p s))"
  apply(induction "dropWhile_char_imp_to_HOL_state p s" arbitrary: s s' t
      rule: dropWhile_char_imp.induct)


  apply(subst dropWhile_char_imp.simps)
  apply(simp only: dropWhile_char_IMP_Minus_def prefix_simps )
  apply(erule Seq_tE)+
  apply(erule While_tE)
  subgoal for s0 result t1 t2 after_loop t_after t_cond_init fst_loop t3

    apply(simp only: dropWhile_char_IMP_init_while_cond_def prefix_simps)
    apply(erule Seq_tE)+

    apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(38) by fastforce
    apply(erule hd_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(40) by fastforce
    apply(erule EQUAL_neq_zero_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(42) by fastforce
    apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(44) by fastforce


    apply(drule AssignD)+
    apply(elim conjE)
    subgoal premises p
      
      thm p
      using p(1, 3, 56) apply -

    
    apply(simp add: dropWhile_char_imp_subprogram_simps
         dropWhile_char_imp_time_acc
      dropWhile_char_state_translators Let_def)
      sorry
    sorry

  apply(erule Seq_tE)+
  apply(dest_com_gen)
  
  subgoal for s result t1 t2 after_loop t_after t_cond_init fst_loop t3 t4 fst_loop_end t5 t_body
    fst_loop_after t_cond

 

    apply(simp only: dropWhile_char_IMP_init_while_cond_def prefix_simps)
    apply(erule Seq_tE)+

    apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(69) by fastforce
    apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(71) by fastforce
    apply(erule EQUAL_neq_zero_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(73) by fastforce
    apply(erule EQUAL_neq_zero_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(75) by fastforce
    apply(erule hd_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(77) by fastforce
    apply(erule hd_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(79) by fastforce
    apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(81) by fastforce
    apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(83) by fastforce

    
    (* apply(simp add: dropWhile_char_complete_simps Let_def)
    apply force *)


    sorry

  subgoal for s result t1 t2 after_loop t_after t_cond_init fst_loop t3 t4 fst_loop_end t5 t_body
    fst_loop_after t_cond

    apply(simp only: dropWhile_char_IMP_init_while_cond_def dropWhile_char_IMP_loop_body_def
        prefix_simps)
    apply(erule Seq_tE)+

    apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(77) by fastforce
    apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(79) by fastforce
    apply(erule hd_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(81) by fastforce
    apply(erule hd_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(83) by fastforce
    apply(erule EQUAL_neq_zero_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(85) by fastforce
    apply(erule EQUAL_neq_zero_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(87) by fastforce
    apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(89) by fastforce
    apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(91) by fastforce
    apply(erule tl_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(93) by fastforce



(*     apply (simp add: dropWhile_char_complete_simps Let_def)
 *)



    sorry

  subgoal for s result t1 t2 after_loop t_after t_cond_init fst_loop t3 t4 fst_loop_end t5 t_body

    apply(simp only: dropWhile_char_IMP_init_while_cond_def dropWhile_char_IMP_loop_body_def
        prefix_simps)
    apply(erule Seq_tE)+

    apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(77) by fastforce
    apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(79) by fastforce
    apply(erule hd_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(81) by fastforce
    apply(erule hd_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(83) by fastforce
    apply(erule EQUAL_neq_zero_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(85) by fastforce
    apply(erule EQUAL_neq_zero_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(87) by fastforce
    apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(89) by fastforce
    apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(91) by fastforce
    apply(erule tl_IMP_Minus_correct[where vars = "dropWhile_char_IMP_vars"])
    subgoal premises p using p(93) by fastforce

(*   apply (simp add: dropWhile_char_complete_simps Let_def)
 *)
    sorry
  done

record n_hashes_acc_state =
  n_hashes_acc_acc::nat
  n_hashes_acc_n::nat
  n_hashes_acc_ret::nat

abbreviation "n_hashes_acc_prefix \<equiv> ''n_hashes_acc.''"
abbreviation "n_hashes_acc_acc_str \<equiv> ''acc''"
abbreviation "n_hashes_acc_n_str \<equiv> ''n''"
abbreviation "n_hashes_acc_ret_str \<equiv> ''ret''"

definition "n_hashes_acc_state_upd s \<equiv>
      let
        cons_h' = hash_as_nat;
        cons_t' = n_hashes_acc_acc s;
        cons_ret' = 0;
        cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
        cons_ret_state = cons_imp cons_state;
        n_hashes_acc_acc' = cons_ret cons_ret_state;
        n_hashes_acc_n' = n_hashes_acc_n s - 1;
        ret = \<lparr>n_hashes_acc_acc = n_hashes_acc_acc',
               n_hashes_acc_n = n_hashes_acc_n',
               n_hashes_acc_ret = n_hashes_acc_ret s\<rparr>
      in
        ret
"

definition "n_hashes_acc_imp_compute_loop_condition s \<equiv>
  (let
    condition = n_hashes_acc_n s
   in condition
  )"

definition "n_hashes_acc_imp_after_loop s \<equiv>
  (let
    ret = \<lparr>n_hashes_acc_acc = n_hashes_acc_acc s,
           n_hashes_acc_n = n_hashes_acc_n s,
           n_hashes_acc_ret = n_hashes_acc_acc s\<rparr>
   in ret
  )"

lemmas n_hashes_acc_imp_subprogram_simps =
  n_hashes_acc_imp_after_loop_def
  n_hashes_acc_state_upd_def
  n_hashes_acc_imp_compute_loop_condition_def

function n_hashes_acc_imp:: "n_hashes_acc_state \<Rightarrow> n_hashes_acc_state" where
  "n_hashes_acc_imp s =
  (if n_hashes_acc_imp_compute_loop_condition s \<noteq> 0
   then
    (let next_iteration = n_hashes_acc_imp (n_hashes_acc_state_upd s)
      in next_iteration)
  else
    (let ret = n_hashes_acc_imp_after_loop s in ret)
  )"
  by simp+
termination by (relation "measure (\<lambda>s. n_hashes_acc_n s)")
    (simp add: n_hashes_acc_imp_subprogram_simps)+

declare n_hashes_acc_imp.simps [simp del]

lemma n_hashes_acc_imp_correct:
  "n_hashes_acc_ret (n_hashes_acc_imp s) = n_hashes_acc (n_hashes_acc_acc s) (n_hashes_acc_n s)"
  apply(induction s rule: n_hashes_acc_imp.induct)
  apply(subst n_hashes_acc_imp.simps)
  apply(simp add: n_hashes_acc_imp_subprogram_simps cons_imp_correct hash_encode_val Suc_diff_Suc)
  by (metis Suc_pred hash_encode_val n_hashes_acc.simps(2))

definition "n_hashes_acc_state_upd_time t s \<equiv>
      let
        cons_h' = hash_as_nat;
        t = t + 2;
        cons_t' = n_hashes_acc_acc s;
        t = t + 2;
        cons_ret' = 0;
        t = t + 2;
        cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
        cons_ret_state = cons_imp cons_state;
        t = t + cons_imp_time 0 cons_state;
        n_hashes_acc_acc' = cons_ret cons_ret_state;
        t = t + 2;
        n_hashes_acc_n' = n_hashes_acc_n s - 1;
        t = t + 2;
        ret = t
      in
        ret
"

definition "n_hashes_acc_imp_compute_loop_condition_time t s \<equiv>
  (let
    condition = n_hashes_acc_n s;
    t = t + 2;
    ret = t
   in ret
  )"

definition "n_hashes_acc_imp_after_loop_time t s \<equiv>
  (let
    t = t + 2;
    ret = t
   in ret
  )"

function n_hashes_acc_imp_time:: "nat \<Rightarrow> n_hashes_acc_state \<Rightarrow> nat" where
  "n_hashes_acc_imp_time t s =
  n_hashes_acc_imp_compute_loop_condition_time 0 s +
  (if n_hashes_acc_imp_compute_loop_condition s \<noteq> 0
   then
    (let
        t = t + 1;
        next_iteration
          = n_hashes_acc_imp_time (t + n_hashes_acc_state_upd_time 0 s) (n_hashes_acc_state_upd s)
     in next_iteration)
  else
    (let
        t = t + 2;
        ret = t + n_hashes_acc_imp_after_loop_time 0 s
     in ret)
  )"
  by auto
termination
  by (relation "measure (\<lambda>(t,s). n_hashes_acc_n s)")
    (simp add: n_hashes_acc_imp_subprogram_simps)+

lemmas n_hashes_acc_imp_subprogram_time_simps =
  n_hashes_acc_imp_subprogram_simps
  n_hashes_acc_imp_after_loop_time_def
  n_hashes_acc_state_upd_time_def
  n_hashes_acc_imp_compute_loop_condition_time_def

lemmas [simp del] = n_hashes_acc_imp_time.simps

lemma n_hashes_acc_imp_time_acc:
  "(n_hashes_acc_imp_time (Suc t) s) = Suc (n_hashes_acc_imp_time t s)"
  by (induction t s rule: n_hashes_acc_imp_time.induct)
    ((subst (1 2) n_hashes_acc_imp_time.simps); (simp add: n_hashes_acc_state_upd_def))

lemma n_hashes_acc_imp_time_acc_2:
  "(n_hashes_acc_imp_time x s) = x + (n_hashes_acc_imp_time 0 s)"
  by (induction x arbitrary: s) (simp add: n_hashes_acc_imp_time_acc)+

lemma n_hashes_acc_imp_time_acc_2_simp:
  "(n_hashes_acc_imp_time (n_hashes_state_upd_time 0 s) s') =
   (n_hashes_state_upd_time 0 s) + (n_hashes_acc_imp_time 0 s')"
  by (rule n_hashes_acc_imp_time_acc_2)

abbreviation "n_hashes_acc_while_cond \<equiv> ''condition''"

definition "n_hashes_acc_IMP_init_while_cond \<equiv>
  \<comment> \<open>condition = n_hashes_n s\<close>
  n_hashes_acc_while_cond ::= (A (V n_hashes_acc_n_str))"

definition "n_hashes_acc_IMP_loop_body \<equiv>
  \<comment> \<open>cons_h' = hash_as_nat;\<close>
  ((cons_prefix @ cons_h_str) ::= (A (N 35)));;
  \<comment> \<open>cons_t' = n_hashes_acc_acc s;\<close>
  ((cons_prefix @ cons_t_str) ::= (A (V n_hashes_acc_acc_str)));;
  \<comment> \<open>cons_ret' = 0;\<close>
  ((cons_prefix @ cons_ret_str) ::= (A (N 0)));;
  \<comment> \<open>cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>n_hashes_acc_acc' = cons_ret cons_ret_state;\<close>
  ((n_hashes_acc_acc_str) ::= (A (V (cons_prefix @ cons_ret_str))));;
  \<comment> \<open>n_hashes_acc_n' = n_hashes_acc_n s - 1\<close>
  ((n_hashes_acc_n_str) ::= (Sub (V n_hashes_acc_n_str) (N 1)))"


definition "n_hashes_acc_IMP_after_loop \<equiv>
  \<comment> \<open>ret = s\<close>
  ((n_hashes_acc_ret_str) ::= (A (V n_hashes_acc_acc_str)))"

definition n_hashes_acc_IMP_Minus where
  "n_hashes_acc_IMP_Minus \<equiv>
  n_hashes_acc_IMP_init_while_cond;;
  WHILE n_hashes_acc_while_cond \<noteq>0 DO (
    n_hashes_acc_IMP_loop_body;;
    n_hashes_acc_IMP_init_while_cond
  );;
  n_hashes_acc_IMP_after_loop"

abbreviation
  "n_hashes_acc_IMP_vars \<equiv>
  {n_hashes_acc_acc_str, n_hashes_acc_n_str, n_hashes_acc_ret_str}"

lemmas n_hashes_acc_IMP_subprogram_simps =
  n_hashes_acc_IMP_init_while_cond_def
  n_hashes_acc_IMP_loop_body_def
  n_hashes_acc_IMP_after_loop_def

definition "n_hashes_acc_imp_to_HOL_state p s =
  \<lparr>n_hashes_acc_acc = (s (add_prefix p n_hashes_acc_acc_str)),
   n_hashes_acc_n = (s (add_prefix p n_hashes_acc_n_str)),
   n_hashes_acc_ret = (s (add_prefix p n_hashes_acc_ret_str))\<rparr>"

lemmas n_hashes_acc_state_translators =
  cons_imp_to_HOL_state_def
  n_hashes_acc_imp_to_HOL_state_def

lemmas n_hashes_acc_complete_simps =
  n_hashes_acc_IMP_subprogram_simps
  n_hashes_acc_imp_subprogram_simps
  n_hashes_acc_state_translators

lemma n_hashes_acc_IMP_Minus_correct_function:
  "(invoke_subprogram p n_hashes_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p n_hashes_acc_ret_str)
      = n_hashes_acc_ret (n_hashes_acc_imp (n_hashes_acc_imp_to_HOL_state p s))"
  apply(induction "n_hashes_acc_imp_to_HOL_state p s" arbitrary: s s' t
      rule: n_hashes_acc_imp.induct)
  apply(subst n_hashes_acc_imp.simps)
  apply(clarsimp simp: n_hashes_acc_IMP_Minus_def)
  apply(erule While_tE)
   apply(clarsimp simp: n_hashes_acc_IMP_subprogram_simps n_hashes_acc_imp_subprogram_simps
      n_hashes_acc_state_translators)
  apply(erule Seq_tE)+
  apply(dest_com_gen)

    apply(simp only: n_hashes_acc_IMP_init_while_cond_def prefix_simps)
    apply(force simp: n_hashes_acc_imp_subprogram_simps n_hashes_acc_state_translators)

   apply(clarsimp simp: n_hashes_acc_IMP_subprogram_simps invoke_subprogram_append)
   apply(erule cons_IMP_Minus_correct[where vars = "n_hashes_acc_IMP_vars"], fastforce)
   apply (fastforce simp: n_hashes_acc_imp_subprogram_simps n_hashes_acc_state_translators)

  apply(clarsimp simp: n_hashes_acc_IMP_subprogram_simps invoke_subprogram_append)
  apply(erule cons_IMP_Minus_correct[where vars = "n_hashes_acc_IMP_vars"], fastforce)
  apply (fastforce simp: n_hashes_acc_imp_subprogram_simps n_hashes_acc_state_translators)
  done

lemma n_hashes_acc_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ n_hashes_acc_pref) n_hashes_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix n_hashes_acc_pref v)\<rbrakk>
  \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma n_hashes_acc_IMP_Minus_correct_time_loop_condition:
  "(invoke_subprogram p n_hashes_acc_IMP_init_while_cond, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = n_hashes_acc_imp_compute_loop_condition_time 0 (n_hashes_acc_imp_to_HOL_state p s)"
  by (subst n_hashes_acc_imp_compute_loop_condition_time_def)
    (auto simp: n_hashes_acc_IMP_init_while_cond_def)

lemmas n_hashes_acc_complete_time_simps =
  n_hashes_acc_imp_subprogram_time_simps
  n_hashes_acc_imp_time_acc
  n_hashes_acc_imp_time_acc_2_simp

lemma n_hashes_acc_IMP_Minus_correct_time:
  "(invoke_subprogram p n_hashes_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = n_hashes_acc_imp_time 0 (n_hashes_acc_imp_to_HOL_state p s)"
  apply(induction "n_hashes_acc_imp_to_HOL_state p s" arbitrary: s s' t
      rule: n_hashes_acc_imp.induct)
  apply(subst n_hashes_acc_imp_time.simps)
  apply(clarsimp simp: n_hashes_acc_IMP_Minus_def)
  apply(erule While_tE_time)
   apply(clarsimp simp: n_hashes_acc_IMP_subprogram_simps n_hashes_acc_state_translators
      n_hashes_acc_imp_subprogram_time_simps)
  apply(clarsimp simp: add.assoc)
  apply(dest_com_gen_time)

    apply(force simp: n_hashes_acc_IMP_init_while_cond_def n_hashes_acc_imp_subprogram_time_simps
      n_hashes_acc_state_translators)

   apply(clarsimp simp: n_hashes_acc_IMP_loop_body_def invoke_subprogram_append)
   apply(erule cons_IMP_Minus_correct[where vars = "n_hashes_acc_IMP_vars"], fastforce)
   apply (force simp: n_hashes_acc_complete_simps)

  apply(clarsimp simp: n_hashes_acc_IMP_init_while_cond_def n_hashes_acc_IMP_loop_body_def
      invoke_subprogram_append)
  apply(erule cons_IMP_Minus_correct[where vars = "n_hashes_acc_IMP_vars"], fastforce)
  apply(force simp: n_hashes_acc_complete_time_simps n_hashes_acc_state_translators)
  done

lemma n_hashes_acc_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) n_hashes_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
     \<lbrakk>t = (n_hashes_acc_imp_time 0 (n_hashes_acc_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) n_hashes_acc_ret_str) =
        n_hashes_acc_ret (n_hashes_acc_imp (n_hashes_acc_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using n_hashes_acc_IMP_Minus_correct_function
  by (auto simp: n_hashes_acc_IMP_Minus_correct_time)
    (meson n_hashes_acc_IMP_Minus_correct_effects set_mono_prefix)

record n_hashes_tail_state =
  n_hashes_tail_n::nat
  n_hashes_tail_ret::nat

abbreviation "n_hashes_tail_prefix \<equiv> ''n_hashes_tail.''"
abbreviation "n_hashes_tail_n_str \<equiv> ''n''"
abbreviation "n_hashes_tail_ret_str \<equiv> ''ret''"

definition "n_hashes_tail_state_upd s =
  (let
      n_hashes_acc_acc' = 0;
      n_hashes_acc_n' = n_hashes_tail_n s;
      n_hashes_acc_ret' = 0;
      n_hashes_acc_state = \<lparr>n_hashes_acc_acc = n_hashes_acc_acc',
                            n_hashes_acc_n = n_hashes_acc_n',
                            n_hashes_acc_ret = n_hashes_acc_ret'\<rparr>;
      n_hashes_acc_ret_state = n_hashes_acc_imp n_hashes_acc_state;
      reverse_nat_n' = n_hashes_acc_ret n_hashes_acc_ret_state;
      reverse_nat_ret' = 0;
      reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n',
                             reverse_nat_ret = reverse_nat_ret'\<rparr>;
      reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;
      n_hashes_tail_ret' = reverse_nat_ret reverse_nat_ret_state;
      n_hashes_tail_n' = n_hashes_tail_n s;
      ret = \<lparr>n_hashes_tail_n = n_hashes_tail_n',
             n_hashes_tail_ret = n_hashes_tail_ret'\<rparr>
    in
      ret
  )"

function n_hashes_tail_imp:: "n_hashes_tail_state \<Rightarrow> n_hashes_tail_state" where
  "n_hashes_tail_imp s =
  (let
      ret = n_hashes_tail_state_upd s
    in
      ret
  )"
  by simp+
termination
  by (relation "measure (\<lambda>s. n_hashes_tail_n s)") simp

declare n_hashes_tail_imp.simps [simp del]

lemma n_hashes_tail_imp_correct:
  "n_hashes_tail_ret (n_hashes_tail_imp s) = n_hashes_tail (n_hashes_tail_n s)"
  by (simp add: n_hashes_acc_imp_correct n_hashes_tail_def n_hashes_tail_imp.simps
      n_hashes_tail_state_upd_def reverse_nat_imp_correct)

function n_hashes_tail_imp_time:: "nat \<Rightarrow> n_hashes_tail_state \<Rightarrow> nat" where
  "n_hashes_tail_imp_time t s =
  (let
      n_hashes_acc_acc' = 0;
      t = t + 2;
      n_hashes_acc_n' = n_hashes_tail_n s;
      t = t + 2;
      n_hashes_acc_ret' = 0;
      t = t + 2;
      n_hashes_acc_state = \<lparr>n_hashes_acc_acc = n_hashes_acc_acc',
                            n_hashes_acc_n = n_hashes_acc_n',
                            n_hashes_acc_ret = n_hashes_acc_ret'\<rparr>;
      n_hashes_acc_ret_state = n_hashes_acc_imp n_hashes_acc_state;
      t = t + n_hashes_acc_imp_time 0 n_hashes_acc_state;
      reverse_nat_n' = n_hashes_acc_ret n_hashes_acc_ret_state;
      t = t + 2;
      reverse_nat_ret' = 0;
      t = t + 2;
      reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n',
                             reverse_nat_ret = reverse_nat_ret'\<rparr>;
      reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;
      t = t + reverse_nat_imp_time 0 reverse_nat_state;
      n_hashes_tail_ret' = reverse_nat_ret reverse_nat_ret_state;
      t = t + 2;
      ret = t
    in
      ret
  )"
  by auto
termination
  by (relation "measure (\<lambda>(t, s). n_hashes_tail_n s)") simp

lemmas [simp del] = n_hashes_tail_imp_time.simps

lemma n_hashes_tail_imp_time_acc:
  "(n_hashes_tail_imp_time (Suc t) s) = Suc (n_hashes_tail_imp_time t s)"
  by (simp add: n_hashes_tail_imp_time.simps Let_def)

lemma n_hashes_tail_imp_time_acc_2:
  "(n_hashes_tail_imp_time x s) = x + (n_hashes_tail_imp_time 0 s)"
  by (simp add: n_hashes_tail_imp_time.simps Let_def)

definition n_hashes_tail_IMP_Minus where
  "n_hashes_tail_IMP_Minus \<equiv>
    \<comment> \<open>n_hashes_acc_acc' = 0;\<close>
    (n_hashes_acc_prefix @ n_hashes_acc_acc_str) ::= (A (N 0));;
    \<comment> \<open>n_hashes_acc_n' = n_hashes_tail_n s;\<close>
    (n_hashes_acc_prefix @ n_hashes_acc_n_str) ::= (A (V n_hashes_tail_n_str));;
    \<comment> \<open>n_hashes_acc_ret' = 0;\<close>
    (n_hashes_acc_prefix @ n_hashes_acc_ret_str) ::= (A (N 0));;
    \<comment> \<open>n_hashes_acc_state = \<lparr>n_hashes_acc_acc = n_hashes_acc_acc',\<close>
    \<comment> \<open>                      n_hashes_acc_n = n_hashes_acc_n',\<close>
    \<comment> \<open>                      n_hashes_acc_ret = n_hashes_acc_ret'\<rparr>;\<close>
    \<comment> \<open>n_hashes_acc_ret_state = n_hashes_acc_imp n_hashes_acc_state;\<close>
    invoke_subprogram n_hashes_acc_prefix n_hashes_acc_IMP_Minus;;
    \<comment> \<open>reverse_nat_n' = n_hashes_acc_ret n_hashes_acc_ret_state;\<close>
    (reverse_nat_prefix @ reverse_nat_n_str)
      ::= (A (V (n_hashes_acc_prefix @ n_hashes_acc_ret_str)));;
    \<comment> \<open>reverse_nat_ret' = 0;\<close>
    (reverse_nat_prefix @ reverse_nat_ret_str) ::= (A (N 0));;
    \<comment> \<open>reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n',\<close>
    \<comment> \<open>                       reverse_nat_ret = reverse_nat_ret'\<rparr>;\<close>
    \<comment> \<open>reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;\<close>
    invoke_subprogram reverse_nat_prefix reverse_nat_IMP_Minus;;
    \<comment> \<open>n_hashes_tail_ret' = reverse_nat_ret reverse_nat_ret_state;\<close>
    n_hashes_tail_ret_str ::= (A (V (reverse_nat_prefix @ reverse_nat_ret_str)))
"

abbreviation
  "n_hashes_tail_IMP_vars \<equiv>
  {n_hashes_tail_n_str, n_hashes_tail_ret_str}"

definition "n_hashes_tail_imp_to_HOL_state p s =
  \<lparr>n_hashes_tail_n = (s (add_prefix p n_hashes_tail_n_str)),
   n_hashes_tail_ret = (s (add_prefix p n_hashes_tail_ret_str))\<rparr>"

lemmas n_hashes_tail_state_translators =
  n_hashes_acc_imp_to_HOL_state_def
  reverse_nat_imp_to_HOL_state_def
  n_hashes_tail_imp_to_HOL_state_def

lemma n_hashes_tail_IMP_Minus_correct_function:
  "(invoke_subprogram p n_hashes_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p n_hashes_tail_ret_str)
      = n_hashes_tail_ret (n_hashes_tail_imp (n_hashes_tail_imp_to_HOL_state p s))"
  by (fastforce elim: reverse_nat_IMP_Minus_correct n_hashes_acc_IMP_Minus_correct
      simp: n_hashes_tail_state_translators n_hashes_tail_state_upd_def
      n_hashes_tail_IMP_Minus_def invoke_subprogram_append n_hashes_tail_imp.simps)

lemma n_hashes_tail_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ n_hashes_tail_pref) n_hashes_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix n_hashes_tail_pref v)\<rbrakk>
  \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma n_hashes_tail_IMP_Minus_correct_time:
  "(invoke_subprogram p n_hashes_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = n_hashes_tail_imp_time 0 (n_hashes_tail_imp_to_HOL_state p s)"
  by (fastforce elim: n_hashes_acc_IMP_Minus_correct reverse_nat_IMP_Minus_correct
      simp: n_hashes_tail_imp_time.simps n_hashes_tail_imp_time_acc n_hashes_tail_imp_time_acc_2
      n_hashes_tail_state_translators Let_def n_hashes_tail_IMP_Minus_def invoke_subprogram_append)

lemma n_hashes_tail_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) n_hashes_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
     \<lbrakk>t = (n_hashes_tail_imp_time 0 (n_hashes_tail_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) n_hashes_tail_ret_str) =
        n_hashes_tail_ret (n_hashes_tail_imp (n_hashes_tail_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using n_hashes_tail_IMP_Minus_correct_time n_hashes_tail_IMP_Minus_correct_function
    n_hashes_tail_IMP_Minus_correct_effects
  by (meson set_mono_prefix)

end