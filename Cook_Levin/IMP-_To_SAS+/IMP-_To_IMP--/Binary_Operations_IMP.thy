theory Binary_Operations_IMP
  imports
    Primitives_IMP_Minus
    Binary_Arithmetic_IMP
    IMP_Minus_To_IMP_Minus_Minus_State_Translations_IMP
    Binary_Operations_Nat
    IMP_Minus.Com
    Utilities
begin

unbundle IMP_Minus_Minus_Com.no_com_syntax

subsection \<open>com_list_to_seq\<close>

subsubsection \<open>com_list_to_seq_acc\<close>

record com_list_to_seq_acc_state =
  com_list_to_seq_acc_acc::nat
  com_list_to_seq_acc_n::nat
  com_list_to_seq_acc_ret::nat

abbreviation "com_list_to_seq_acc_prefix \<equiv> ''com_list_to_seq_acc.''"
abbreviation "com_list_to_seq_acc_acc_str \<equiv> ''acc''"
abbreviation "com_list_to_seq_acc_n_str \<equiv> ''n''"
abbreviation "com_list_to_seq_acc_ret_str \<equiv> ''ret''"

definition "com_list_to_seq_acc_state_upd s \<equiv>
  (let
      cons_h' = com_list_to_seq_acc_acc s;
      cons_t' = 0;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      hd_xs' = com_list_to_seq_acc_n s;
      hd_ret' = 0;
      hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
      hd_ret_state = hd_imp hd_state;
      cons_h' = hd_ret hd_ret_state;
      cons_t' = cons_ret cons_ret_state;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_h' = 2;
      cons_t' = cons_ret cons_ret_state;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      com_list_to_seq_acc_acc' = cons_ret cons_ret_state;
      tl_xs' = com_list_to_seq_acc_n s;
      tl_ret' = 0;
      tl_state = \<lparr>tl_xs = tl_xs',
                  tl_ret = tl_ret'\<rparr>;
      tl_ret_state = tl_imp tl_state;
      com_list_to_seq_acc_n' = tl_ret tl_ret_state;
      ret = \<lparr>com_list_to_seq_acc_acc = com_list_to_seq_acc_acc',
             com_list_to_seq_acc_n = com_list_to_seq_acc_n',
             com_list_to_seq_acc_ret = com_list_to_seq_acc_ret s\<rparr>
  in
      ret
)"

definition "com_list_to_seq_acc_imp_compute_loop_condition s \<equiv>
  (let
      condition = com_list_to_seq_acc_n s
  in
      condition
)"

definition "com_list_to_seq_acc_imp_after_loop s \<equiv>
  (let
      com_list_to_seq_acc_ret' = com_list_to_seq_acc_acc s;
      ret = \<lparr>com_list_to_seq_acc_acc = com_list_to_seq_acc_acc s,
             com_list_to_seq_acc_n = com_list_to_seq_acc_n s,
             com_list_to_seq_acc_ret = com_list_to_seq_acc_ret'\<rparr>
  in
      ret
)"

lemmas com_list_to_seq_acc_imp_subprogram_simps = 
  com_list_to_seq_acc_state_upd_def
  com_list_to_seq_acc_imp_compute_loop_condition_def
  com_list_to_seq_acc_imp_after_loop_def

function com_list_to_seq_acc_imp::
  "com_list_to_seq_acc_state \<Rightarrow> com_list_to_seq_acc_state" where
  "com_list_to_seq_acc_imp s =
  (if com_list_to_seq_acc_imp_compute_loop_condition s \<noteq> 0
   then let next_iteration = com_list_to_seq_acc_imp (com_list_to_seq_acc_state_upd s)
        in next_iteration
   else let ret = com_list_to_seq_acc_imp_after_loop s
        in ret
  )"
  by simp+
termination
  apply (relation "measure com_list_to_seq_acc_n")
  apply (simp add: com_list_to_seq_acc_imp_subprogram_simps tl_imp_correct)+
  done

declare com_list_to_seq_acc_imp.simps [simp del]

lemma com_list_to_seq_acc_imp_correct[let_function_correctness]:
  "com_list_to_seq_acc_ret (com_list_to_seq_acc_imp s) =
    com_list_to_seq_acc (com_list_to_seq_acc_acc s) (com_list_to_seq_acc_n s)"
  apply (induction s rule: com_list_to_seq_acc_imp.induct)
  apply (subst com_list_to_seq_acc_imp.simps)
  apply (subst com_list_to_seq_acc.simps)
  apply (simp del: com_list_to_seq_acc.simps add: com_list_to_seq_acc_imp_subprogram_simps Let_def
  cons_imp_correct hd_imp_correct tl_imp_correct)
  done 

definition "com_list_to_seq_acc_state_upd_time t s \<equiv>
  (let
      cons_h' = com_list_to_seq_acc_acc s;
      t = t + 2;
      cons_t' = 0;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      hd_xs' = com_list_to_seq_acc_n s;
      t = t + 2;
      hd_ret' = 0;
      t = t + 2;
      hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
      hd_ret_state = hd_imp hd_state;
      t = t + hd_imp_time 0 hd_state;
      cons_h' = hd_ret hd_ret_state;
      t = t + 2;
      cons_t' = cons_ret cons_ret_state;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_h' = 2;
      t = t + 2;
      cons_t' = cons_ret cons_ret_state;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      com_list_to_seq_acc_acc' = cons_ret cons_ret_state;
      t = t + 2;
      tl_xs' = com_list_to_seq_acc_n s;
      t = t + 2;
      tl_ret' = 0;
      t = t + 2;
      tl_state = \<lparr>tl_xs = tl_xs',
                  tl_ret = tl_ret'\<rparr>;
      tl_ret_state = tl_imp tl_state;
      t = t + tl_imp_time 0 tl_state;
      com_list_to_seq_acc_n' = tl_ret tl_ret_state;
      t = t + 2;
      ret = \<lparr>com_list_to_seq_acc_acc = com_list_to_seq_acc_acc',
             com_list_to_seq_acc_n = com_list_to_seq_acc_n',
             com_list_to_seq_acc_ret = com_list_to_seq_acc_ret s\<rparr>
  in
      t
)"

definition "com_list_to_seq_acc_imp_compute_loop_condition_time t s \<equiv>
  (let
      condition = com_list_to_seq_acc_n s;
      t = t + 2
  in
      t
)"

definition "com_list_to_seq_acc_imp_after_loop_time t s \<equiv>
  (let
      com_list_to_seq_acc_ret' = com_list_to_seq_acc_acc s;
      t = t + 2;
      ret = \<lparr>com_list_to_seq_acc_acc = com_list_to_seq_acc_acc s,
             com_list_to_seq_acc_n = com_list_to_seq_acc_n s,
             com_list_to_seq_acc_ret = com_list_to_seq_acc_ret'\<rparr>
  in
      t
)"

lemmas com_list_to_seq_acc_imp_subprogram_time_simps = 
  com_list_to_seq_acc_state_upd_time_def
  com_list_to_seq_acc_imp_compute_loop_condition_time_def
  com_list_to_seq_acc_imp_after_loop_time_def
  com_list_to_seq_acc_imp_subprogram_simps

function com_list_to_seq_acc_imp_time::
  "nat \<Rightarrow> com_list_to_seq_acc_state \<Rightarrow> nat" where
  "com_list_to_seq_acc_imp_time t s =
  com_list_to_seq_acc_imp_compute_loop_condition_time 0 s +
  (if com_list_to_seq_acc_imp_compute_loop_condition s \<noteq> 0
    then
      (let
        t = t + 1;
        next_iteration =
          com_list_to_seq_acc_imp_time (t + com_list_to_seq_acc_state_upd_time 0 s)
                         (com_list_to_seq_acc_state_upd s)
       in next_iteration)
    else
      (let
        t = t + 2;
        ret = t + com_list_to_seq_acc_imp_after_loop_time 0 s
       in ret)
  )"
  by auto
termination
  apply (relation "measure (com_list_to_seq_acc_n \<circ> snd)")
  by (simp add: com_list_to_seq_acc_imp_subprogram_time_simps tl_imp_correct)+

declare com_list_to_seq_acc_imp_time.simps [simp del]

lemma com_list_to_seq_acc_imp_time_acc:
  "(com_list_to_seq_acc_imp_time (Suc t) s) = Suc (com_list_to_seq_acc_imp_time t s)"
  by (induction t s rule: com_list_to_seq_acc_imp_time.induct)
    ((subst (1 2) com_list_to_seq_acc_imp_time.simps);
      (simp add: com_list_to_seq_acc_state_upd_def))            

lemma com_list_to_seq_acc_imp_time_acc_2_aux:
  "(com_list_to_seq_acc_imp_time t s) = t + (com_list_to_seq_acc_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: com_list_to_seq_acc_imp_time_acc)+            

lemma com_list_to_seq_acc_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (com_list_to_seq_acc_imp_time t s) = t + (com_list_to_seq_acc_imp_time 0 s)"
  by (rule com_list_to_seq_acc_imp_time_acc_2_aux)            

lemma com_list_to_seq_acc_imp_time_acc_3:
  "(com_list_to_seq_acc_imp_time (a + b) s) = a + (com_list_to_seq_acc_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: com_list_to_seq_acc_imp_time_acc)+  

abbreviation "com_list_to_seq_acc_while_cond \<equiv> ''condition''"

definition "com_list_to_seq_acc_IMP_init_while_cond \<equiv>
  \<comment> \<open>  condition = com_list_to_seq_acc_n s\<close>
  (com_list_to_seq_acc_while_cond) ::= (A (V com_list_to_seq_acc_n_str))
"

definition "com_list_to_seq_acc_IMP_loop_body \<equiv>
  \<comment> \<open>  cons_h' = com_list_to_seq_acc_acc s;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V com_list_to_seq_acc_acc_str));;
  \<comment> \<open>  cons_t' = 0;\<close>
  (cons_prefix @ cons_t_str) ::= (A (N 0));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  hd_xs' = com_list_to_seq_acc_n s;\<close>
  (hd_prefix @ hd_xs_str) ::= (A (V com_list_to_seq_acc_n_str));;
  \<comment> \<open>  hd_ret' = 0;\<close>
  (hd_prefix @ hd_ret_str) ::= (A (N 0));;
  \<comment> \<open>  hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;\<close>
  \<comment> \<open>  hd_ret_state = hd_imp hd_state;\<close>
  (invoke_subprogram hd_prefix hd_IMP_Minus);;
  \<comment> \<open>  cons_h' = hd_ret hd_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (hd_prefix @ hd_ret_str)));;
  \<comment> \<open>  cons_t' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_h' = 2;\<close>
  (cons_prefix @ cons_h_str) ::= (A (N 2));;
  \<comment> \<open>  cons_t' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  com_list_to_seq_acc_acc' = cons_ret cons_ret_state;\<close>
  (com_list_to_seq_acc_acc_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  tl_xs' = com_list_to_seq_acc_n s;\<close>
  (tl_prefix @ tl_xs_str) ::= (A (V com_list_to_seq_acc_n_str));;
  \<comment> \<open>  tl_ret' = 0;\<close>
  (tl_prefix @ tl_ret_str) ::= (A (N 0));;
  \<comment> \<open>  tl_state = \<lparr>tl_xs = tl_xs',\<close>
  \<comment> \<open>              tl_ret = tl_ret'\<rparr>;\<close>
  \<comment> \<open>  tl_ret_state = tl_imp tl_state;\<close>
  (invoke_subprogram tl_prefix tl_IMP_Minus);;
  \<comment> \<open>  com_list_to_seq_acc_n' = tl_ret tl_ret_state;\<close>
  (com_list_to_seq_acc_n_str) ::= (A (V (tl_prefix @ tl_ret_str)))
  \<comment> \<open>  ret = \<lparr>com_list_to_seq_acc_acc = com_list_to_seq_acc_acc',\<close>
  \<comment> \<open>         com_list_to_seq_acc_n = com_list_to_seq_acc_n',\<close>
  \<comment> \<open>         com_list_to_seq_acc_ret = com_list_to_seq_acc_ret s\<rparr>\<close>
"

definition "com_list_to_seq_acc_IMP_after_loop \<equiv>
  \<comment> \<open>  com_list_to_seq_acc_ret' = com_list_to_seq_acc_acc s;\<close>
  (com_list_to_seq_acc_ret_str) ::= (A (V com_list_to_seq_acc_acc_str))
  \<comment> \<open>  ret = \<lparr>com_list_to_seq_acc_acc = com_list_to_seq_acc_acc s,\<close>
  \<comment> \<open>         com_list_to_seq_acc_n = com_list_to_seq_acc_n s,\<close>
  \<comment> \<open>         com_list_to_seq_acc_ret = com_list_to_seq_acc_ret'\<rparr>\<close>
"

definition com_list_to_seq_acc_IMP_Minus where
  "com_list_to_seq_acc_IMP_Minus \<equiv>
  com_list_to_seq_acc_IMP_init_while_cond;;
  WHILE com_list_to_seq_acc_while_cond \<noteq>0 DO (
    com_list_to_seq_acc_IMP_loop_body;;
    com_list_to_seq_acc_IMP_init_while_cond
  );;
  com_list_to_seq_acc_IMP_after_loop"

abbreviation "com_list_to_seq_acc_IMP_vars \<equiv>
  {com_list_to_seq_acc_acc_str, com_list_to_seq_acc_n_str, com_list_to_seq_acc_ret_str}"

lemmas com_list_to_seq_acc_IMP_subprogram_simps =
  com_list_to_seq_acc_IMP_init_while_cond_def
  com_list_to_seq_acc_IMP_loop_body_def
  com_list_to_seq_acc_IMP_after_loop_def

definition "com_list_to_seq_acc_imp_to_HOL_state p s =
  \<lparr>com_list_to_seq_acc_acc = (s (add_prefix p com_list_to_seq_acc_acc_str)),
   com_list_to_seq_acc_n = (s (add_prefix p com_list_to_seq_acc_n_str)),
   com_list_to_seq_acc_ret = (s (add_prefix p com_list_to_seq_acc_ret_str))\<rparr>"

lemmas com_list_to_seq_acc_state_translators =
  com_list_to_seq_acc_imp_to_HOL_state_def
  hd_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  tl_imp_to_HOL_state_def

lemmas com_list_to_seq_acc_complete_simps =
  com_list_to_seq_acc_IMP_subprogram_simps
  com_list_to_seq_acc_imp_subprogram_simps
  com_list_to_seq_acc_state_translators

lemma com_list_to_seq_acc_IMP_Minus_correct_function:
  "(invoke_subprogram p com_list_to_seq_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p com_list_to_seq_acc_ret_str)
      = com_list_to_seq_acc_ret
          (com_list_to_seq_acc_imp (com_list_to_seq_acc_imp_to_HOL_state p s))"
  apply(induction "com_list_to_seq_acc_imp_to_HOL_state p s" arbitrary: s s' t
    rule: com_list_to_seq_acc_imp.induct)
  apply(subst com_list_to_seq_acc_imp.simps)
  apply(simp only: com_list_to_seq_acc_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule While_tE)

  subgoal
    apply(simp only: com_list_to_seq_acc_IMP_subprogram_simps prefix_simps)
    by(fastforce simp: com_list_to_seq_acc_IMP_subprogram_simps
        com_list_to_seq_acc_imp_subprogram_simps
        com_list_to_seq_acc_state_translators)

  apply(erule Seq_E)+
  apply(dest_com_gen)

  subgoal
      apply(simp only: com_list_to_seq_acc_IMP_init_while_cond_def prefix_simps)
      by(fastforce simp add: com_list_to_seq_acc_complete_simps)

  subgoal
      apply(subst (asm) com_list_to_seq_acc_IMP_init_while_cond_def)
      apply(simp only: com_list_to_seq_acc_IMP_loop_body_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule cons_IMP_Minus_correct[where vars = "com_list_to_seq_acc_IMP_vars"])
      subgoal premises p using p(25) by fastforce
      apply(erule hd_IMP_Minus_correct[where 
            vars = "insert (cons_prefix @ cons_ret_str) com_list_to_seq_acc_IMP_vars"])
      subgoal premises p using p(27) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "com_list_to_seq_acc_IMP_vars"])
      subgoal premises p using p(29) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "com_list_to_seq_acc_IMP_vars"])
      subgoal premises p using p(31) by fastforce
      apply(erule tl_IMP_Minus_correct[where vars = "com_list_to_seq_acc_IMP_vars"])
      subgoal premises p using p(33) by fastforce
      by (simp only: com_list_to_seq_acc_imp_subprogram_simps
          com_list_to_seq_acc_state_translators Let_def, force)

  subgoal
      apply(simp only: com_list_to_seq_acc_IMP_init_while_cond_def prefix_simps
          com_list_to_seq_acc_IMP_loop_body_def)
      apply(erule Seq_E)+
      apply(erule cons_IMP_Minus_correct[where vars = "com_list_to_seq_acc_IMP_vars"])
      subgoal premises p using p(25) by fastforce
      apply(erule hd_IMP_Minus_correct[where 
            vars = "insert (cons_prefix @ cons_ret_str) com_list_to_seq_acc_IMP_vars"])
      subgoal premises p using p(27) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "com_list_to_seq_acc_IMP_vars"])
      subgoal premises p using p(29) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "com_list_to_seq_acc_IMP_vars"])
      subgoal premises p using p(31) by fastforce
      apply(erule tl_IMP_Minus_correct[where vars = "com_list_to_seq_acc_IMP_vars"])
      subgoal premises p using p(33) by fastforce
      by (fastforce_sorted_premises2 simp: com_list_to_seq_acc_imp_subprogram_simps
          com_list_to_seq_acc_state_translators Let_def)
  done  

lemma com_list_to_seq_acc_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ com_list_to_seq_acc_pref) com_list_to_seq_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix com_list_to_seq_acc_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast     

lemmas com_list_to_seq_acc_complete_time_simps =
  com_list_to_seq_acc_imp_subprogram_time_simps
  com_list_to_seq_acc_imp_time_acc
  com_list_to_seq_acc_imp_time_acc_2
  com_list_to_seq_acc_imp_time_acc_3
  com_list_to_seq_acc_state_translators

lemma com_list_to_seq_acc_IMP_Minus_correct_time:
  "(invoke_subprogram p com_list_to_seq_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = com_list_to_seq_acc_imp_time 0 (com_list_to_seq_acc_imp_to_HOL_state p s)"
  apply(induction "com_list_to_seq_acc_imp_to_HOL_state p s" arbitrary: s s' t
      rule: com_list_to_seq_acc_imp.induct)
  apply(subst com_list_to_seq_acc_imp_time.simps)
  apply(simp only: com_list_to_seq_acc_IMP_Minus_def prefix_simps)

  apply(erule Seq_tE)+
  apply(erule While_tE_time)

  subgoal
    apply(simp only: com_list_to_seq_acc_IMP_subprogram_simps prefix_simps)
    by (force simp: com_list_to_seq_acc_IMP_subprogram_simps
        com_list_to_seq_acc_imp_subprogram_time_simps com_list_to_seq_acc_state_translators)

  apply(erule Seq_tE)+
  apply(simp add: add.assoc)
  apply(dest_com_gen_time)

  subgoal
    apply(simp only: com_list_to_seq_acc_IMP_init_while_cond_def prefix_simps)
    by(fastforce simp add: com_list_to_seq_acc_complete_simps)

  subgoal
    apply(subst (asm) com_list_to_seq_acc_IMP_init_while_cond_def)
    apply(simp only: com_list_to_seq_acc_IMP_loop_body_def prefix_simps)
    apply(erule Seq_tE)+
    apply(erule cons_IMP_Minus_correct[where vars = "com_list_to_seq_acc_IMP_vars"])
    subgoal premises p using p(47) by fastforce
    apply(erule hd_IMP_Minus_correct[where 
          vars = "insert (cons_prefix @ cons_ret_str) com_list_to_seq_acc_IMP_vars"])
    subgoal premises p using p(49) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "com_list_to_seq_acc_IMP_vars"])
    subgoal premises p using p(51) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "com_list_to_seq_acc_IMP_vars"])
    subgoal premises p using p(53) by fastforce
    apply(erule tl_IMP_Minus_correct[where vars = "com_list_to_seq_acc_IMP_vars"])
    subgoal premises p using p(55) by fastforce
    by (simp only: com_list_to_seq_acc_imp_subprogram_time_simps
        com_list_to_seq_acc_state_translators Let_def, force)

  subgoal
    apply(simp only: prefix_simps com_list_to_seq_acc_IMP_init_while_cond_def
        com_list_to_seq_acc_IMP_loop_body_def)
    apply(erule Seq_tE)+
    apply(erule cons_IMP_Minus_correct[where vars = "com_list_to_seq_acc_IMP_vars"])
    subgoal premises p using p(47) by fastforce
    apply(erule hd_IMP_Minus_correct[where 
          vars = "insert (cons_prefix @ cons_ret_str) com_list_to_seq_acc_IMP_vars"])
    subgoal premises p using p(49) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "com_list_to_seq_acc_IMP_vars"])
    subgoal premises p using p(51) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "com_list_to_seq_acc_IMP_vars"])
    subgoal premises p using p(53) by fastforce
    apply(erule tl_IMP_Minus_correct[where vars = "com_list_to_seq_acc_IMP_vars"])
    subgoal premises p using p(55) by fastforce
    apply(simp only: com_list_to_seq_acc_complete_time_simps Let_def)
    by (fastforce_sorted_premises simp: Let_def com_list_to_seq_acc_complete_time_simps)
  done 

lemma com_list_to_seq_acc_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) com_list_to_seq_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (com_list_to_seq_acc_imp_time 0 (com_list_to_seq_acc_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) com_list_to_seq_acc_ret_str) =
          com_list_to_seq_acc_ret (com_list_to_seq_acc_imp
                                        (com_list_to_seq_acc_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using com_list_to_seq_acc_IMP_Minus_correct_function
    com_list_to_seq_acc_IMP_Minus_correct_time
    com_list_to_seq_acc_IMP_Minus_correct_effects
  by (meson set_mono_prefix)

subsubsection \<open>com_list_to_seq_tail\<close>

record com_list_to_seq_tail_state =
  com_list_to_seq_tail_ys::nat
  com_list_to_seq_tail_ret::nat

abbreviation "com_list_to_seq_tail_prefix \<equiv> ''com_list_to_seq_tail.''"
abbreviation "com_list_to_seq_tail_ys_str \<equiv> ''ys''"
abbreviation "com_list_to_seq_tail_ret_str \<equiv> ''ret''"

definition "com_list_to_seq_tail_state_upd s =
  (let
      cons_h' = 0;
      cons_t' = 0;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_result = cons_ret cons_ret_state;
      reverse_nat_n' = com_list_to_seq_tail_ys s;
      reverse_nat_ret' = 0;
      reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n', reverse_nat_ret = reverse_nat_ret'\<rparr>;
      reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;
      com_list_to_seq_acc_acc' = cons_result;
      com_list_to_seq_acc_n' = reverse_nat_ret reverse_nat_ret_state;
      com_list_to_seq_acc_ret' = 0;
      com_list_to_seq_acc_state = \<lparr>com_list_to_seq_acc_acc = com_list_to_seq_acc_acc',
                                   com_list_to_seq_acc_n = com_list_to_seq_acc_n',
                                   com_list_to_seq_acc_ret = com_list_to_seq_acc_ret'\<rparr>;
      com_list_to_seq_acc_ret_state = com_list_to_seq_acc_imp com_list_to_seq_acc_state;
      com_list_to_seq_tail_ret' = com_list_to_seq_acc_ret com_list_to_seq_acc_ret_state;
      ret = \<lparr>com_list_to_seq_tail_ys = com_list_to_seq_tail_ys s,
             com_list_to_seq_tail_ret = com_list_to_seq_tail_ret'\<rparr>
  in
      ret
)"

function com_list_to_seq_tail_imp ::
  "com_list_to_seq_tail_state \<Rightarrow> com_list_to_seq_tail_state" where
  "com_list_to_seq_tail_imp s =
  (let 
      ret = com_list_to_seq_tail_state_upd s
    in 
      ret
  )"
  by simp+
termination
  by (relation "measure com_list_to_seq_tail_ys") simp

declare com_list_to_seq_tail_imp.simps [simp del]

lemma com_list_to_seq_tail_imp_correct[let_function_correctness]:
  "com_list_to_seq_tail_ret (com_list_to_seq_tail_imp s) =
    com_list_to_seq_tail (com_list_to_seq_tail_ys s)"
  apply (simp only: com_list_to_seq_tail_imp.simps Let_def com_list_to_seq_tail_state_upd_def
  cons_imp_correct reverse_nat_imp_correct com_list_to_seq_acc_imp_correct com_list_to_seq_tail_def)
  by simp    

function com_list_to_seq_tail_imp_time ::
  "nat \<Rightarrow> com_list_to_seq_tail_state \<Rightarrow> nat" where
  "com_list_to_seq_tail_imp_time t s =
  (let
      cons_h' = 0;
      t = t + 2;
      cons_t' = 0;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_result = cons_ret cons_ret_state;
      t = t + 2;
      reverse_nat_n' = com_list_to_seq_tail_ys s;
      t = t + 2;
      reverse_nat_ret' = 0;
      t = t + 2;
      reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n', reverse_nat_ret = reverse_nat_ret'\<rparr>;
      reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;
      t = t + reverse_nat_imp_time 0 reverse_nat_state;
      com_list_to_seq_acc_acc' = cons_result;
      t = t + 2;
      com_list_to_seq_acc_n' = reverse_nat_ret reverse_nat_ret_state;
      t = t + 2;
      com_list_to_seq_acc_ret' = 0;
      t = t + 2;
      com_list_to_seq_acc_state = \<lparr>com_list_to_seq_acc_acc = com_list_to_seq_acc_acc',
                                   com_list_to_seq_acc_n = com_list_to_seq_acc_n',
                                   com_list_to_seq_acc_ret = com_list_to_seq_acc_ret'\<rparr>;
      com_list_to_seq_acc_ret_state = com_list_to_seq_acc_imp com_list_to_seq_acc_state;
      t = t + com_list_to_seq_acc_imp_time 0 com_list_to_seq_acc_state;
      com_list_to_seq_tail_ret' = com_list_to_seq_acc_ret com_list_to_seq_acc_ret_state;
      t = t + 2;
      ret = \<lparr>com_list_to_seq_tail_ys = com_list_to_seq_tail_ys s,
             com_list_to_seq_tail_ret = com_list_to_seq_tail_ret'\<rparr>
  in
      t
  )"
  by auto
termination
  by (relation "measure (com_list_to_seq_tail_ys \<circ> snd)") simp

declare com_list_to_seq_tail_imp_time.simps [simp del]

lemma com_list_to_seq_tail_imp_time_acc:
  "(com_list_to_seq_tail_imp_time (Suc t) s) = Suc (com_list_to_seq_tail_imp_time t s)"
  by (induction t s rule: com_list_to_seq_tail_imp_time.induct)
    ((subst (1 2) com_list_to_seq_tail_imp_time.simps);
      (simp add: com_list_to_seq_tail_state_upd_def Let_def))            

lemma com_list_to_seq_tail_imp_time_acc_2_aux:
  "(com_list_to_seq_tail_imp_time t s) = t + (com_list_to_seq_tail_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: com_list_to_seq_tail_imp_time_acc)+            

lemma com_list_to_seq_tail_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (com_list_to_seq_tail_imp_time t s) = t + (com_list_to_seq_tail_imp_time 0 s)"
  by (rule com_list_to_seq_tail_imp_time_acc_2_aux)            

lemma com_list_to_seq_tail_imp_time_acc_3:
  "(com_list_to_seq_tail_imp_time (a + b) s) = a + (com_list_to_seq_tail_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: com_list_to_seq_tail_imp_time_acc)+ 

abbreviation "com_list_to_seq_tail_cons_result \<equiv> ''cons_result''"

definition com_list_to_seq_tail_IMP_Minus where
  "com_list_to_seq_tail_IMP_Minus \<equiv>
  \<comment> \<open>  cons_h' = 0;\<close>
  (cons_prefix @ cons_h_str) ::= (A (N 0));;
  \<comment> \<open>  cons_t' = 0;\<close>
  (cons_prefix @ cons_t_str) ::= (A (N 0));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_result = cons_ret cons_ret_state;\<close>
  (com_list_to_seq_tail_cons_result) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  reverse_nat_n' = com_list_to_seq_tail_ys s;\<close>
  (reverse_nat_prefix @ reverse_nat_n_str) ::= (A (V com_list_to_seq_tail_ys_str));;
  \<comment> \<open>  reverse_nat_ret' = 0;\<close>
  (reverse_nat_prefix @ reverse_nat_ret_str) ::= (A (N 0));;
  \<comment> \<open>  reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n', reverse_nat_ret = reverse_nat_ret'\<rparr>;\<close>
  \<comment> \<open>  reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;\<close>
  (invoke_subprogram reverse_nat_prefix reverse_nat_IMP_Minus);;
  \<comment> \<open>  com_list_to_seq_acc_acc' = cons_result;\<close>
  (com_list_to_seq_acc_prefix @ com_list_to_seq_acc_acc_str) ::= (A (V com_list_to_seq_tail_cons_result));;
  \<comment> \<open>  com_list_to_seq_acc_n' = reverse_nat_ret reverse_nat_ret_state;\<close>
  (com_list_to_seq_acc_prefix @ com_list_to_seq_acc_n_str) ::= (A (V (reverse_nat_prefix @ reverse_nat_ret_str)));;
  \<comment> \<open>  com_list_to_seq_acc_ret' = 0;\<close>
  (com_list_to_seq_acc_prefix @ com_list_to_seq_acc_ret_str) ::= (A (N 0));;
  \<comment> \<open>  com_list_to_seq_acc_state = \<lparr>com_list_to_seq_acc_acc = com_list_to_seq_acc_acc',\<close>
  \<comment> \<open>                               com_list_to_seq_acc_n = com_list_to_seq_acc_n',\<close>
  \<comment> \<open>                               com_list_to_seq_acc_ret = com_list_to_seq_acc_ret'\<rparr>;\<close>
  \<comment> \<open>  com_list_to_seq_acc_ret_state = com_list_to_seq_acc_imp com_list_to_seq_acc_state;\<close>
  (invoke_subprogram com_list_to_seq_acc_prefix com_list_to_seq_acc_IMP_Minus);;
  \<comment> \<open>  com_list_to_seq_tail_ret' = com_list_to_seq_acc_ret com_list_to_seq_acc_ret_state;\<close>
  (com_list_to_seq_tail_ret_str) ::= (A (V (com_list_to_seq_acc_prefix @ com_list_to_seq_acc_ret_str)))
  \<comment> \<open>  ret = \<lparr>com_list_to_seq_tail_ys = com_list_to_seq_tail_ys s,\<close>
  \<comment> \<open>         com_list_to_seq_tail_ret = com_list_to_seq_tail_ret'\<rparr>\<close>
"

abbreviation "com_list_to_seq_tail_IMP_vars \<equiv>
  {com_list_to_seq_tail_ys_str, com_list_to_seq_tail_ret_str, com_list_to_seq_tail_cons_result}"

definition "com_list_to_seq_tail_imp_to_HOL_state p s =
  \<lparr>com_list_to_seq_tail_ys = (s (add_prefix p com_list_to_seq_tail_ys_str)),
   com_list_to_seq_tail_ret = (s (add_prefix p com_list_to_seq_tail_ret_str))\<rparr>"

lemmas com_list_to_seq_tail_state_translators =
  com_list_to_seq_tail_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  reverse_nat_imp_to_HOL_state_def
  com_list_to_seq_acc_imp_to_HOL_state_def

lemma com_list_to_seq_tail_IMP_Minus_correct_function:
  "(invoke_subprogram p com_list_to_seq_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p com_list_to_seq_tail_ret_str)
      = com_list_to_seq_tail_ret
          (com_list_to_seq_tail_imp (com_list_to_seq_tail_imp_to_HOL_state p s))"
  apply(subst com_list_to_seq_tail_imp.simps)
  apply(simp only: com_list_to_seq_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule cons_IMP_Minus_correct[where vars = "com_list_to_seq_tail_IMP_vars"])
  subgoal premises p using p(13) by fastforce
  apply(erule reverse_nat_IMP_Minus_correct[where vars = "com_list_to_seq_tail_IMP_vars"])
  subgoal premises p using p(15) by fastforce
  apply(erule com_list_to_seq_acc_IMP_Minus_correct[where vars = "com_list_to_seq_tail_IMP_vars"])
  subgoal premises p using p(17) by fastforce
  by(fastforce simp: com_list_to_seq_tail_state_translators
    com_list_to_seq_tail_state_upd_def)     

lemma com_list_to_seq_tail_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ com_list_to_seq_tail_pref) com_list_to_seq_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix com_list_to_seq_tail_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast 

lemma com_list_to_seq_tail_IMP_Minus_correct_time:
  "(invoke_subprogram p com_list_to_seq_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = com_list_to_seq_tail_imp_time 0 (com_list_to_seq_tail_imp_to_HOL_state p s)"
  apply(subst com_list_to_seq_tail_imp_time.simps)
  apply(simp only: com_list_to_seq_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule cons_IMP_Minus_correct[where vars = "com_list_to_seq_tail_IMP_vars"])
  subgoal premises p using p(25) by fastforce
  apply(erule reverse_nat_IMP_Minus_correct[where vars = "com_list_to_seq_tail_IMP_vars"])
  subgoal premises p using p(27) by fastforce
  apply(erule com_list_to_seq_acc_IMP_Minus_correct[where vars = "com_list_to_seq_tail_IMP_vars"])
  subgoal premises p using p(29) by fastforce
  by(fastforce simp add: Let_def com_list_to_seq_tail_state_translators)   

lemma com_list_to_seq_tail_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) com_list_to_seq_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (com_list_to_seq_tail_imp_time 0 (com_list_to_seq_tail_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) com_list_to_seq_tail_ret_str) =
          com_list_to_seq_tail_ret (com_list_to_seq_tail_imp
                                        (com_list_to_seq_tail_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using com_list_to_seq_tail_IMP_Minus_correct_function
    com_list_to_seq_tail_IMP_Minus_correct_time
    com_list_to_seq_tail_IMP_Minus_correct_effects
  by (meson set_mono_prefix)


subsection \<open>binary_assign_constant\<close>

subsubsection \<open>binary_assign_constant_acc_aux\<close>

fun binary_assign_constant_acc_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "binary_assign_constant_acc_aux diff n v x = 
    (cons (var_bit_to_var_tail(prod_encode (v,n-diff))) (cons (nth_bit_tail x (n-diff)) 0))"

record binary_assign_constant_acc_aux_state =
  binary_assign_constant_acc_aux_diff::nat
  binary_assign_constant_acc_aux_n::nat
  binary_assign_constant_acc_aux_v::nat
  binary_assign_constant_acc_aux_x::nat
  binary_assign_constant_acc_aux_ret::nat

abbreviation "binary_assign_constant_acc_aux_prefix \<equiv> ''binary_assign_constant_acc_aux.''"
abbreviation "binary_assign_constant_acc_aux_diff_str \<equiv> ''diff''"
abbreviation "binary_assign_constant_acc_aux_n_str \<equiv> ''n''"
abbreviation "binary_assign_constant_acc_aux_v_str \<equiv> ''v''"
abbreviation "binary_assign_constant_acc_aux_x_str \<equiv> ''x''"
abbreviation "binary_assign_constant_acc_aux_ret_str \<equiv> ''ret''"

definition "binary_assign_constant_acc_aux_state_upd s \<equiv>
  (let
      prod_encode_a' = binary_assign_constant_acc_aux_v s;
      prod_encode_b' = binary_assign_constant_acc_aux_n s - binary_assign_constant_acc_aux_diff s;
      prod_encode_ret' = 0;
      prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                           prod_encode_b = prod_encode_b',
                           prod_encode_ret = prod_encode_ret'\<rparr>;
      prod_encode_ret_state = prod_encode_imp prod_encode_state;
      var_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
      var_bit_to_var_tail_ret' = 0;
      var_bit_to_var_tail_state = \<lparr>var_bit_to_var_tail_n = var_bit_to_var_tail_n',
                                   var_bit_to_var_tail_ret = var_bit_to_var_tail_ret'\<rparr>;
      var_bit_to_var_tail_ret_state = var_bit_to_var_tail_imp var_bit_to_var_tail_state;
      var_bit_to_var_tail_result = var_bit_to_var_tail_ret var_bit_to_var_tail_ret_state;
      nth_bit_tail_acc' = binary_assign_constant_acc_aux_x s;
      nth_bit_tail_n' = binary_assign_constant_acc_aux_n s - binary_assign_constant_acc_aux_diff s;
      nth_bit_tail_ret' = 0;
      nth_bit_tail_state = \<lparr>nth_bit_tail_acc = nth_bit_tail_acc',
                            nth_bit_tail_n = nth_bit_tail_n',
                            nth_bit_tail_ret = nth_bit_tail_ret'\<rparr>;
      nth_bit_tail_ret_state = nth_bit_tail_imp nth_bit_tail_state;
      cons_h' = nth_bit_tail_ret nth_bit_tail_ret_state;
      cons_t' = 0;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_h' = var_bit_to_var_tail_result;
      cons_t' = cons_ret cons_ret_state;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      binary_assign_constant_acc_aux_ret' = cons_ret cons_ret_state;
      ret = \<lparr>binary_assign_constant_acc_aux_diff = binary_assign_constant_acc_aux_diff s,
             binary_assign_constant_acc_aux_n = binary_assign_constant_acc_aux_n s,
             binary_assign_constant_acc_aux_v = binary_assign_constant_acc_aux_v s,
             binary_assign_constant_acc_aux_x = binary_assign_constant_acc_aux_x s,
             binary_assign_constant_acc_aux_ret = binary_assign_constant_acc_aux_ret'\<rparr>
  in
      ret
)"

function binary_assign_constant_acc_aux_imp ::
  "binary_assign_constant_acc_aux_state \<Rightarrow> binary_assign_constant_acc_aux_state" where
  "binary_assign_constant_acc_aux_imp s =
  (let 
      ret = binary_assign_constant_acc_aux_state_upd s
    in 
      ret
  )"
  by simp+
termination
  by (relation "measure binary_assign_constant_acc_aux_diff") simp

declare binary_assign_constant_acc_aux_imp.simps [simp del]

lemma binary_assign_constant_acc_aux_imp_correct[let_function_correctness]:
  "binary_assign_constant_acc_aux_ret (binary_assign_constant_acc_aux_imp s) =
    binary_assign_constant_acc_aux (binary_assign_constant_acc_aux_diff s) (binary_assign_constant_acc_aux_n s)
      (binary_assign_constant_acc_aux_v s) (binary_assign_constant_acc_aux_x s)"
  apply (simp only: binary_assign_constant_acc_aux_imp.simps Let_def binary_assign_constant_acc_aux_state_upd_def
  prod_encode_imp_correct var_bit_to_var_tail_imp_correct nth_bit_tail_imp_correct cons_imp_correct)
  by (simp add: nth_bit_tail'_correct)    

function binary_assign_constant_acc_aux_imp_time ::
  "nat \<Rightarrow> binary_assign_constant_acc_aux_state \<Rightarrow> nat" where
  "binary_assign_constant_acc_aux_imp_time t s =
  (let
      prod_encode_a' = binary_assign_constant_acc_aux_v s;
      t = t + 2;
      prod_encode_b' = binary_assign_constant_acc_aux_n s - binary_assign_constant_acc_aux_diff s;
      t = t + 2;
      prod_encode_ret' = 0;
      t = t + 2;
      prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                           prod_encode_b = prod_encode_b',
                           prod_encode_ret = prod_encode_ret'\<rparr>;
      prod_encode_ret_state = prod_encode_imp prod_encode_state;
      t = t + prod_encode_imp_time 0 prod_encode_state;
      var_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
      t = t + 2;
      var_bit_to_var_tail_ret' = 0;
      t = t + 2;
      var_bit_to_var_tail_state = \<lparr>var_bit_to_var_tail_n = var_bit_to_var_tail_n',
                                   var_bit_to_var_tail_ret = var_bit_to_var_tail_ret'\<rparr>;
      var_bit_to_var_tail_ret_state = var_bit_to_var_tail_imp var_bit_to_var_tail_state;
      t = t + var_bit_to_var_tail_imp_time 0 var_bit_to_var_tail_state;
      var_bit_to_var_tail_result = var_bit_to_var_tail_ret var_bit_to_var_tail_ret_state;
      t = t + 2;
      nth_bit_tail_acc' = binary_assign_constant_acc_aux_x s;
      t = t + 2;
      nth_bit_tail_n' = binary_assign_constant_acc_aux_n s - binary_assign_constant_acc_aux_diff s;
      t = t + 2;
      nth_bit_tail_ret' = 0;
      t = t + 2;
      nth_bit_tail_state = \<lparr>nth_bit_tail_acc = nth_bit_tail_acc',
                            nth_bit_tail_n = nth_bit_tail_n',
                            nth_bit_tail_ret = nth_bit_tail_ret'\<rparr>;
      nth_bit_tail_ret_state = nth_bit_tail_imp nth_bit_tail_state;
      t = t + nth_bit_tail_imp_time 0 nth_bit_tail_state;
      cons_h' = nth_bit_tail_ret nth_bit_tail_ret_state;
      t = t + 2;
      cons_t' = 0;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_h' = var_bit_to_var_tail_result;
      t = t + 2;
      cons_t' = cons_ret cons_ret_state;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      binary_assign_constant_acc_aux_ret' = cons_ret cons_ret_state;
      t = t + 2;
      ret = \<lparr>binary_assign_constant_acc_aux_diff = binary_assign_constant_acc_aux_diff s,
             binary_assign_constant_acc_aux_n = binary_assign_constant_acc_aux_n s,
             binary_assign_constant_acc_aux_v = binary_assign_constant_acc_aux_v s,
             binary_assign_constant_acc_aux_x = binary_assign_constant_acc_aux_x s,
             binary_assign_constant_acc_aux_ret = binary_assign_constant_acc_aux_ret'\<rparr>
  in
      t
  )"
  by auto
termination
  by (relation "measure (binary_assign_constant_acc_aux_diff \<circ> snd)") simp

declare binary_assign_constant_acc_aux_imp_time.simps [simp del]

lemma binary_assign_constant_acc_aux_imp_time_acc:
  "(binary_assign_constant_acc_aux_imp_time (Suc t) s) = Suc (binary_assign_constant_acc_aux_imp_time t s)"
  by (induction t s rule: binary_assign_constant_acc_aux_imp_time.induct)
    ((subst (1 2) binary_assign_constant_acc_aux_imp_time.simps);
      (simp add: binary_assign_constant_acc_aux_state_upd_def Let_def))            

lemma binary_assign_constant_acc_aux_imp_time_acc_2_aux:
  "(binary_assign_constant_acc_aux_imp_time t s) = t + (binary_assign_constant_acc_aux_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: binary_assign_constant_acc_aux_imp_time_acc)+            

lemma binary_assign_constant_acc_aux_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (binary_assign_constant_acc_aux_imp_time t s) = t + (binary_assign_constant_acc_aux_imp_time 0 s)"
  by (rule binary_assign_constant_acc_aux_imp_time_acc_2_aux)            

lemma binary_assign_constant_acc_aux_imp_time_acc_3:
  "(binary_assign_constant_acc_aux_imp_time (a + b) s) = a + (binary_assign_constant_acc_aux_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: binary_assign_constant_acc_aux_imp_time_acc)+ 

abbreviation "binary_assign_constant_acc_aux_var_bit_to_var_tail_result \<equiv> ''var_bit_to_var_tail_result''"

definition binary_assign_constant_acc_aux_IMP_Minus where
  "binary_assign_constant_acc_aux_IMP_Minus \<equiv>
  \<comment> \<open>  prod_encode_a' = binary_assign_constant_acc_aux_v s;\<close>
  (prod_encode_prefix @ prod_encode_a_str) ::= (A (V binary_assign_constant_acc_aux_v_str));;
  \<comment> \<open>  prod_encode_b' = binary_assign_constant_acc_aux_n s - binary_assign_constant_acc_aux_diff s;\<close>
  (prod_encode_prefix @ prod_encode_b_str) ::= (Sub (V binary_assign_constant_acc_aux_n_str) (V binary_assign_constant_acc_aux_diff_str));;
  \<comment> \<open>  prod_encode_ret' = 0;\<close>
  (prod_encode_prefix @ prod_encode_ret_str) ::= (A (N 0));;
  \<comment> \<open>  prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',\<close>
  \<comment> \<open>                       prod_encode_b = prod_encode_b',\<close>
  \<comment> \<open>                       prod_encode_ret = prod_encode_ret'\<rparr>;\<close>
  \<comment> \<open>  prod_encode_ret_state = prod_encode_imp prod_encode_state;\<close>
  (invoke_subprogram prod_encode_prefix prod_encode_IMP_Minus);;
  \<comment> \<open>  var_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;\<close>
  (var_bit_to_var_tail_prefix @ var_bit_to_var_tail_n_str) ::= (A (V (prod_encode_prefix @ prod_encode_ret_str)));;
  \<comment> \<open>  var_bit_to_var_tail_ret' = 0;\<close>
  (var_bit_to_var_tail_prefix @ var_bit_to_var_tail_ret_str) ::= (A (N 0));;
  \<comment> \<open>  var_bit_to_var_tail_state = \<lparr>var_bit_to_var_tail_n = var_bit_to_var_tail_n',\<close>
  \<comment> \<open>                               var_bit_to_var_tail_ret = var_bit_to_var_tail_ret'\<rparr>;\<close>
  \<comment> \<open>  var_bit_to_var_tail_ret_state = var_bit_to_var_tail_imp var_bit_to_var_tail_state;\<close>
  (invoke_subprogram var_bit_to_var_tail_prefix var_bit_to_var_tail_IMP_Minus);;
  \<comment> \<open>  var_bit_to_var_tail_result = var_bit_to_var_tail_ret var_bit_to_var_tail_ret_state;\<close>
  (binary_assign_constant_acc_aux_var_bit_to_var_tail_result) ::= (A (V (var_bit_to_var_tail_prefix @ var_bit_to_var_tail_ret_str)));;
  \<comment> \<open>  nth_bit_tail_acc' = binary_assign_constant_acc_aux_x s;\<close>
  (nth_bit_tail_prefix @ nth_bit_tail_acc_str) ::= (A (V binary_assign_constant_acc_aux_x_str));;
  \<comment> \<open>  nth_bit_tail_n' = binary_assign_constant_acc_aux_n s - binary_assign_constant_acc_aux_diff s;\<close>
  (nth_bit_tail_prefix @ nth_bit_tail_n_str) ::= (Sub (V binary_assign_constant_acc_aux_n_str) (V binary_assign_constant_acc_aux_diff_str));;
  \<comment> \<open>  nth_bit_tail_ret' = 0;\<close>
  (nth_bit_tail_prefix @ nth_bit_tail_ret_str) ::= (A (N 0));;
  \<comment> \<open>  nth_bit_tail_state = \<lparr>nth_bit_tail_acc = nth_bit_tail_acc',\<close>
  \<comment> \<open>                        nth_bit_tail_n = nth_bit_tail_n',\<close>
  \<comment> \<open>                        nth_bit_tail_ret = nth_bit_tail_ret'\<rparr>;\<close>
  \<comment> \<open>  nth_bit_tail_ret_state = nth_bit_tail_imp nth_bit_tail_state;\<close>
  (invoke_subprogram nth_bit_tail_prefix nth_bit_tail_IMP_Minus);;
  \<comment> \<open>  cons_h' = nth_bit_tail_ret nth_bit_tail_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (nth_bit_tail_prefix @ nth_bit_tail_ret_str)));;
  \<comment> \<open>  cons_t' = 0;\<close>
  (cons_prefix @ cons_t_str) ::= (A (N 0));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_h' = var_bit_to_var_tail_result;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V binary_assign_constant_acc_aux_var_bit_to_var_tail_result));;
  \<comment> \<open>  cons_t' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  binary_assign_constant_acc_aux_ret' = cons_ret cons_ret_state;\<close>
  (binary_assign_constant_acc_aux_ret_str) ::= (A (V (cons_prefix @ cons_ret_str)))
  \<comment> \<open>  ret = \<lparr>binary_assign_constant_acc_aux_diff = binary_assign_constant_acc_aux_diff s,\<close>
  \<comment> \<open>         binary_assign_constant_acc_aux_n = binary_assign_constant_acc_aux_n s,\<close>
  \<comment> \<open>         binary_assign_constant_acc_aux_v = binary_assign_constant_acc_aux_v s,\<close>
  \<comment> \<open>         binary_assign_constant_acc_aux_x = binary_assign_constant_acc_aux_x s,\<close>
  \<comment> \<open>         binary_assign_constant_acc_aux_ret = binary_assign_constant_acc_aux_ret'\<rparr>\<close>
"

abbreviation "binary_assign_constant_acc_aux_IMP_vars \<equiv>
  {binary_assign_constant_acc_aux_diff_str, binary_assign_constant_acc_aux_n_str, binary_assign_constant_acc_aux_v_str,
  binary_assign_constant_acc_aux_x_str, binary_assign_constant_acc_aux_ret_str,
  binary_assign_constant_acc_aux_var_bit_to_var_tail_result}"

definition "binary_assign_constant_acc_aux_imp_to_HOL_state p s =
  \<lparr>binary_assign_constant_acc_aux_diff = (s (add_prefix p binary_assign_constant_acc_aux_diff_str)),
   binary_assign_constant_acc_aux_n = (s (add_prefix p binary_assign_constant_acc_aux_n_str)),
   binary_assign_constant_acc_aux_v = (s (add_prefix p binary_assign_constant_acc_aux_v_str)),
   binary_assign_constant_acc_aux_x = (s (add_prefix p binary_assign_constant_acc_aux_x_str)),
   binary_assign_constant_acc_aux_ret = (s (add_prefix p binary_assign_constant_acc_aux_ret_str))\<rparr>"

lemmas binary_assign_constant_acc_aux_state_translators =
  binary_assign_constant_acc_aux_imp_to_HOL_state_def
  prod_encode_imp_to_HOL_state_def
  var_bit_to_var_tail_imp_to_HOL_state_def
  nth_bit_tail_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def

lemma binary_assign_constant_acc_aux_IMP_Minus_correct_function:
  "(invoke_subprogram p binary_assign_constant_acc_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p binary_assign_constant_acc_aux_ret_str)
      = binary_assign_constant_acc_aux_ret
          (binary_assign_constant_acc_aux_imp (binary_assign_constant_acc_aux_imp_to_HOL_state p s))"
  apply(subst binary_assign_constant_acc_aux_imp.simps)
  apply(simp only: binary_assign_constant_acc_aux_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule prod_encode_IMP_Minus_correct[where vars = "binary_assign_constant_acc_aux_IMP_vars"])
  subgoal premises p using p(21) by fastforce
  apply(erule var_bit_to_var_tail_IMP_Minus_correct[where vars = "binary_assign_constant_acc_aux_IMP_vars"])
  subgoal premises p using p(23) by fastforce
  apply(erule nth_bit_tail_IMP_Minus_correct[where vars = "binary_assign_constant_acc_aux_IMP_vars"])
  subgoal premises p using p(25) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_acc_aux_IMP_vars"])
  subgoal premises p using p(27) by fastforce      
  apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_acc_aux_IMP_vars"])
  subgoal premises p using p(29) by fastforce
  by(fastforce_sorted_premises2 simp: binary_assign_constant_acc_aux_state_translators Let_def
    binary_assign_constant_acc_aux_state_upd_def)        

lemma binary_assign_constant_acc_aux_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ binary_assign_constant_acc_aux_pref) binary_assign_constant_acc_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix binary_assign_constant_acc_aux_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast 

lemma binary_assign_constant_acc_aux_IMP_Minus_correct_time:
  "(invoke_subprogram p binary_assign_constant_acc_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = binary_assign_constant_acc_aux_imp_time 0 (binary_assign_constant_acc_aux_imp_to_HOL_state p s)"
  apply(subst binary_assign_constant_acc_aux_imp_time.simps)
  apply(simp only: binary_assign_constant_acc_aux_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule prod_encode_IMP_Minus_correct[where vars = "binary_assign_constant_acc_aux_IMP_vars"])
  subgoal premises p using p(41) by fastforce
  apply(erule var_bit_to_var_tail_IMP_Minus_correct[where vars = "binary_assign_constant_acc_aux_IMP_vars"])
  subgoal premises p using p(43) by fastforce
  apply(erule nth_bit_tail_IMP_Minus_correct[where vars = "binary_assign_constant_acc_aux_IMP_vars"])
  subgoal premises p using p(45) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_acc_aux_IMP_vars"])
  subgoal premises p using p(47) by fastforce      
  apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_acc_aux_IMP_vars"])
  subgoal premises p using p(49) by fastforce
  by(force simp: Let_def binary_assign_constant_acc_aux_state_translators)

lemma binary_assign_constant_acc_aux_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) binary_assign_constant_acc_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (binary_assign_constant_acc_aux_imp_time 0 (binary_assign_constant_acc_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) binary_assign_constant_acc_aux_ret_str) =
          binary_assign_constant_acc_aux_ret (binary_assign_constant_acc_aux_imp
                                        (binary_assign_constant_acc_aux_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using binary_assign_constant_acc_aux_IMP_Minus_correct_function
    binary_assign_constant_acc_aux_IMP_Minus_correct_time
    binary_assign_constant_acc_aux_IMP_Minus_correct_effects
  by (meson set_mono_prefix)

subsubsection \<open>binary_assign_constant_acc\<close>

fun binary_assign_constant_acc' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "binary_assign_constant_acc' acc diff n v x = (if diff = 0 then acc else
    binary_assign_constant_acc' (cons 2 (cons (cons 1 
      (binary_assign_constant_acc_aux diff n v x))
      (cons acc 0) )) (diff-1) n v x )"

lemma binary_assign_constant_acc'_correct:
  "binary_assign_constant_acc acc diff n v x = binary_assign_constant_acc' acc diff n v x"
  by (induction acc diff n v x rule: binary_assign_constant_acc.induct) simp

record binary_assign_constant_acc_state =
  binary_assign_constant_acc_acc::nat
  binary_assign_constant_acc_diff::nat
  binary_assign_constant_acc_n::nat
  binary_assign_constant_acc_v::nat
  binary_assign_constant_acc_x::nat
  binary_assign_constant_acc_ret::nat

abbreviation "binary_assign_constant_acc_prefix \<equiv> ''binary_assign_constant_acc.''"
abbreviation "binary_assign_constant_acc_acc_str \<equiv> ''acc''"
abbreviation "binary_assign_constant_acc_diff_str \<equiv> ''diff''"
abbreviation "binary_assign_constant_acc_n_str \<equiv> ''n''"
abbreviation "binary_assign_constant_acc_v_str \<equiv> ''v''"
abbreviation "binary_assign_constant_acc_x_str \<equiv> ''x''"
abbreviation "binary_assign_constant_acc_ret_str \<equiv> ''ret''"

definition "binary_assign_constant_acc_state_upd s \<equiv>
  (let
      binary_assign_constant_acc_aux_diff' = binary_assign_constant_acc_diff s;
      binary_assign_constant_acc_aux_n' = binary_assign_constant_acc_n s;
      binary_assign_constant_acc_aux_v' = binary_assign_constant_acc_v s;
      binary_assign_constant_acc_aux_x' = binary_assign_constant_acc_x s;
      binary_assign_constant_acc_aux_ret' = 0;
      binary_assign_constant_acc_aux_state = \<lparr>binary_assign_constant_acc_aux_diff = binary_assign_constant_acc_aux_diff',
                                              binary_assign_constant_acc_aux_n = binary_assign_constant_acc_aux_n',
                                              binary_assign_constant_acc_aux_v = binary_assign_constant_acc_aux_v',
                                              binary_assign_constant_acc_aux_x = binary_assign_constant_acc_aux_x',
                                              binary_assign_constant_acc_aux_ret = binary_assign_constant_acc_aux_ret'\<rparr>;
      binary_assign_constant_acc_aux_ret_state = binary_assign_constant_acc_aux_imp binary_assign_constant_acc_aux_state;
      cons_h' = 1;
      cons_t' = binary_assign_constant_acc_aux_ret binary_assign_constant_acc_aux_ret_state;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_result = cons_ret cons_ret_state;
      cons_h' = binary_assign_constant_acc_acc s;
      cons_t' = 0;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_h' = cons_result;
      cons_t' = cons_ret cons_ret_state;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_h' = 2;
      cons_t' = cons_ret cons_ret_state;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      binary_assign_constant_acc_acc' = cons_ret cons_ret_state;
      binary_assign_constant_acc_diff' = binary_assign_constant_acc_diff s - 1;
      ret = \<lparr>binary_assign_constant_acc_acc = binary_assign_constant_acc_acc',
             binary_assign_constant_acc_diff = binary_assign_constant_acc_diff',
             binary_assign_constant_acc_n = binary_assign_constant_acc_n s,
             binary_assign_constant_acc_v = binary_assign_constant_acc_v s,
             binary_assign_constant_acc_x = binary_assign_constant_acc_x s,
             binary_assign_constant_acc_ret = binary_assign_constant_acc_ret s\<rparr>
  in
      ret
)"

definition "binary_assign_constant_acc_imp_compute_loop_condition s \<equiv>
  (let
      condition = binary_assign_constant_acc_diff s
  in
      condition
)"

definition "binary_assign_constant_acc_imp_after_loop s \<equiv>
  (let
      binary_assign_constant_acc_ret' = binary_assign_constant_acc_acc s;
      ret = \<lparr>binary_assign_constant_acc_acc = binary_assign_constant_acc_acc s,
             binary_assign_constant_acc_diff = binary_assign_constant_acc_diff s,
             binary_assign_constant_acc_n = binary_assign_constant_acc_n s,
             binary_assign_constant_acc_v = binary_assign_constant_acc_v s,
             binary_assign_constant_acc_x = binary_assign_constant_acc_x s,
             binary_assign_constant_acc_ret = binary_assign_constant_acc_ret'\<rparr>
  in
      ret
)"

lemmas binary_assign_constant_acc_imp_subprogram_simps = 
  binary_assign_constant_acc_state_upd_def
  binary_assign_constant_acc_imp_compute_loop_condition_def
  binary_assign_constant_acc_imp_after_loop_def

function binary_assign_constant_acc_imp::
  "binary_assign_constant_acc_state \<Rightarrow> binary_assign_constant_acc_state" where
  "binary_assign_constant_acc_imp s =
  (if binary_assign_constant_acc_imp_compute_loop_condition s \<noteq> 0
   then let next_iteration = binary_assign_constant_acc_imp (binary_assign_constant_acc_state_upd s)
        in next_iteration
   else let ret = binary_assign_constant_acc_imp_after_loop s
        in ret
  )"
  by simp+
termination
  apply (relation "measure binary_assign_constant_acc_diff")
  apply (simp add: binary_assign_constant_acc_imp_subprogram_simps)+
  done

declare binary_assign_constant_acc_imp.simps [simp del]

lemma binary_assign_constant_acc_imp_correct[let_function_correctness]:
  "binary_assign_constant_acc_ret (binary_assign_constant_acc_imp s) =
    binary_assign_constant_acc (binary_assign_constant_acc_acc s) (binary_assign_constant_acc_diff s)
      (binary_assign_constant_acc_n s) (binary_assign_constant_acc_v s) (binary_assign_constant_acc_x s)"
  apply (induction s rule: binary_assign_constant_acc_imp.induct)
  apply (subst binary_assign_constant_acc_imp.simps)
  apply (subst binary_assign_constant_acc.simps)
  apply (simp del: binary_assign_constant_acc.simps add: binary_assign_constant_acc_imp_subprogram_simps Let_def
    binary_assign_constant_acc_aux_imp_correct cons_imp_correct)
  done 

definition "binary_assign_constant_acc_state_upd_time t s \<equiv>
  (let
      binary_assign_constant_acc_aux_diff' = binary_assign_constant_acc_diff s;
      t = t + 2;
      binary_assign_constant_acc_aux_n' = binary_assign_constant_acc_n s;
      t = t + 2;
      binary_assign_constant_acc_aux_v' = binary_assign_constant_acc_v s;
      t = t + 2;
      binary_assign_constant_acc_aux_x' = binary_assign_constant_acc_x s;
      t = t + 2;
      binary_assign_constant_acc_aux_ret' = 0;
      t = t + 2;
      binary_assign_constant_acc_aux_state = \<lparr>binary_assign_constant_acc_aux_diff = binary_assign_constant_acc_aux_diff',
                                              binary_assign_constant_acc_aux_n = binary_assign_constant_acc_aux_n',
                                              binary_assign_constant_acc_aux_v = binary_assign_constant_acc_aux_v',
                                              binary_assign_constant_acc_aux_x = binary_assign_constant_acc_aux_x',
                                              binary_assign_constant_acc_aux_ret = binary_assign_constant_acc_aux_ret'\<rparr>;
      binary_assign_constant_acc_aux_ret_state = binary_assign_constant_acc_aux_imp binary_assign_constant_acc_aux_state;
      t = t + binary_assign_constant_acc_aux_imp_time 0 binary_assign_constant_acc_aux_state;
      cons_h' = 1;
      t = t + 2;
      cons_t' = binary_assign_constant_acc_aux_ret binary_assign_constant_acc_aux_ret_state;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_result = cons_ret cons_ret_state;
      t = t + 2;
      cons_h' = binary_assign_constant_acc_acc s;
      t = t + 2;
      cons_t' = 0;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_h' = cons_result;
      t = t + 2;
      cons_t' = cons_ret cons_ret_state;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_h' = 2;
      t = t + 2;
      cons_t' = cons_ret cons_ret_state;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      binary_assign_constant_acc_acc' = cons_ret cons_ret_state;
      t = t + 2;
      binary_assign_constant_acc_diff' = binary_assign_constant_acc_diff s - 1;
      t = t + 2;
      ret = \<lparr>binary_assign_constant_acc_acc = binary_assign_constant_acc_acc',
             binary_assign_constant_acc_diff = binary_assign_constant_acc_diff',
             binary_assign_constant_acc_n = binary_assign_constant_acc_n s,
             binary_assign_constant_acc_v = binary_assign_constant_acc_v s,
             binary_assign_constant_acc_x = binary_assign_constant_acc_x s,
             binary_assign_constant_acc_ret = binary_assign_constant_acc_ret s\<rparr>
  in
      t
)"

definition "binary_assign_constant_acc_imp_compute_loop_condition_time t s \<equiv>
  (let
      condition = binary_assign_constant_acc_diff s;
      t = t + 2
  in
      t
)"

definition "binary_assign_constant_acc_imp_after_loop_time t s \<equiv>
  (let
      binary_assign_constant_acc_ret' = binary_assign_constant_acc_acc s;
      t = t + 2;
      ret = \<lparr>binary_assign_constant_acc_acc = binary_assign_constant_acc_acc s,
             binary_assign_constant_acc_diff = binary_assign_constant_acc_diff s,
             binary_assign_constant_acc_n = binary_assign_constant_acc_n s,
             binary_assign_constant_acc_v = binary_assign_constant_acc_v s,
             binary_assign_constant_acc_x = binary_assign_constant_acc_x s,
             binary_assign_constant_acc_ret = binary_assign_constant_acc_ret'\<rparr>
  in
      t
)"

lemmas binary_assign_constant_acc_imp_subprogram_time_simps = 
  binary_assign_constant_acc_state_upd_time_def
  binary_assign_constant_acc_imp_compute_loop_condition_time_def
  binary_assign_constant_acc_imp_after_loop_time_def
  binary_assign_constant_acc_imp_subprogram_simps

function binary_assign_constant_acc_imp_time::
  "nat \<Rightarrow> binary_assign_constant_acc_state \<Rightarrow> nat" where
  "binary_assign_constant_acc_imp_time t s =
  binary_assign_constant_acc_imp_compute_loop_condition_time 0 s +
  (if binary_assign_constant_acc_imp_compute_loop_condition s \<noteq> 0
    then
      (let
        t = t + 1;
        next_iteration =
          binary_assign_constant_acc_imp_time (t + binary_assign_constant_acc_state_upd_time 0 s)
                         (binary_assign_constant_acc_state_upd s)
       in next_iteration)
    else
      (let
        t = t + 2;
        ret = t + binary_assign_constant_acc_imp_after_loop_time 0 s
       in ret)
  )"
  by auto
termination
  apply (relation "measure (binary_assign_constant_acc_diff \<circ> snd)")
  by (simp add: binary_assign_constant_acc_imp_subprogram_time_simps)+

declare binary_assign_constant_acc_imp_time.simps [simp del]   

lemma binary_assign_constant_acc_imp_time_acc:
  "(binary_assign_constant_acc_imp_time (Suc t) s) = Suc (binary_assign_constant_acc_imp_time t s)"
  by (induction t s rule: binary_assign_constant_acc_imp_time.induct)
    ((subst (1 2) binary_assign_constant_acc_imp_time.simps);
      (simp add: binary_assign_constant_acc_state_upd_def))            

lemma binary_assign_constant_acc_imp_time_acc_2_aux:
  "(binary_assign_constant_acc_imp_time t s) = t + (binary_assign_constant_acc_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: binary_assign_constant_acc_imp_time_acc)+            

lemma binary_assign_constant_acc_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (binary_assign_constant_acc_imp_time t s) = t + (binary_assign_constant_acc_imp_time 0 s)"
  by (rule binary_assign_constant_acc_imp_time_acc_2_aux)            

lemma binary_assign_constant_acc_imp_time_acc_3:
  "(binary_assign_constant_acc_imp_time (a + b) s) = a + (binary_assign_constant_acc_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: binary_assign_constant_acc_imp_time_acc)+            

abbreviation "binary_assign_constant_acc_while_cond \<equiv> ''condition''"
abbreviation "binary_assign_constant_acc_cons_result \<equiv> ''cons_result''"

definition "binary_assign_constant_acc_IMP_init_while_cond \<equiv>
  \<comment> \<open>  condition = binary_assign_constant_acc_diff s\<close>
  (binary_assign_constant_acc_while_cond) ::= (A (V binary_assign_constant_acc_diff_str))
"

definition "binary_assign_constant_acc_IMP_loop_body \<equiv>
  \<comment> \<open>  binary_assign_constant_acc_aux_diff' = binary_assign_constant_acc_diff s;\<close>
  (binary_assign_constant_acc_aux_prefix @ binary_assign_constant_acc_aux_diff_str) ::= (A (V binary_assign_constant_acc_diff_str));;
  \<comment> \<open>  binary_assign_constant_acc_aux_n' = binary_assign_constant_acc_n s;\<close>
  (binary_assign_constant_acc_aux_prefix @ binary_assign_constant_acc_aux_n_str) ::= (A (V binary_assign_constant_acc_n_str));;
  \<comment> \<open>  binary_assign_constant_acc_aux_v' = binary_assign_constant_acc_v s;\<close>
  (binary_assign_constant_acc_aux_prefix @ binary_assign_constant_acc_aux_v_str) ::= (A (V binary_assign_constant_acc_v_str));;
  \<comment> \<open>  binary_assign_constant_acc_aux_x' = binary_assign_constant_acc_x s;\<close>
  (binary_assign_constant_acc_aux_prefix @ binary_assign_constant_acc_aux_x_str) ::= (A (V binary_assign_constant_acc_x_str));;
  \<comment> \<open>  binary_assign_constant_acc_aux_ret' = 0;\<close>
  (binary_assign_constant_acc_aux_prefix @ binary_assign_constant_acc_aux_ret_str) ::= (A (N 0));;
  \<comment> \<open>  binary_assign_constant_acc_aux_state = \<lparr>binary_assign_constant_acc_aux_diff = binary_assign_constant_acc_aux_diff',\<close>
  \<comment> \<open>                                          binary_assign_constant_acc_aux_n = binary_assign_constant_acc_aux_n',\<close>
  \<comment> \<open>                                          binary_assign_constant_acc_aux_v = binary_assign_constant_acc_aux_v',\<close>
  \<comment> \<open>                                          binary_assign_constant_acc_aux_x = binary_assign_constant_acc_aux_x',\<close>
  \<comment> \<open>                                          binary_assign_constant_acc_aux_ret = binary_assign_constant_acc_aux_ret'\<rparr>;\<close>
  \<comment> \<open>  binary_assign_constant_acc_aux_ret_state = binary_assign_constant_acc_aux_imp binary_assign_constant_acc_aux_state;\<close>
  (invoke_subprogram binary_assign_constant_acc_aux_prefix binary_assign_constant_acc_aux_IMP_Minus);;
  \<comment> \<open>  cons_h' = 1;\<close>
  (cons_prefix @ cons_h_str) ::= (A (N 1));;
  \<comment> \<open>  cons_t' = binary_assign_constant_acc_aux_ret binary_assign_constant_acc_aux_ret_state;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V (binary_assign_constant_acc_aux_prefix @ binary_assign_constant_acc_aux_ret_str)));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_result = cons_ret cons_ret_state;\<close>
  (binary_assign_constant_acc_cons_result) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_h' = binary_assign_constant_acc_acc s;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V binary_assign_constant_acc_acc_str));;
  \<comment> \<open>  cons_t' = 0;\<close>
  (cons_prefix @ cons_t_str) ::= (A (N 0));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_h' = cons_result;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V binary_assign_constant_acc_cons_result));;
  \<comment> \<open>  cons_t' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_h' = 2;\<close>
  (cons_prefix @ cons_h_str) ::= (A (N 2));;
  \<comment> \<open>  cons_t' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  binary_assign_constant_acc_acc' = cons_ret cons_ret_state;\<close>
  (binary_assign_constant_acc_acc_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  binary_assign_constant_acc_diff' = binary_assign_constant_acc_diff s - 1;\<close>
  (binary_assign_constant_acc_diff_str) ::= (Sub (V binary_assign_constant_acc_diff_str) (N 1))
  \<comment> \<open>  ret = \<lparr>binary_assign_constant_acc_acc = binary_assign_constant_acc_acc',\<close>
  \<comment> \<open>         binary_assign_constant_acc_diff = binary_assign_constant_acc_diff',\<close>
  \<comment> \<open>         binary_assign_constant_acc_n = binary_assign_constant_acc_n s,\<close>
  \<comment> \<open>         binary_assign_constant_acc_v = binary_assign_constant_acc_v s,\<close>
  \<comment> \<open>         binary_assign_constant_acc_x = binary_assign_constant_acc_x s,\<close>
  \<comment> \<open>         binary_assign_constant_acc_ret = binary_assign_constant_acc_ret s\<rparr>\<close>
"

definition "binary_assign_constant_acc_IMP_after_loop \<equiv>
  \<comment> \<open>  binary_assign_constant_acc_ret' = binary_assign_constant_acc_acc s;\<close>
  (binary_assign_constant_acc_ret_str) ::= (A (V binary_assign_constant_acc_acc_str))
  \<comment> \<open>  ret = \<lparr>binary_assign_constant_acc_acc = binary_assign_constant_acc_acc s,\<close>
  \<comment> \<open>         binary_assign_constant_acc_diff = binary_assign_constant_acc_diff s,\<close>
  \<comment> \<open>         binary_assign_constant_acc_n = binary_assign_constant_acc_n s,\<close>
  \<comment> \<open>         binary_assign_constant_acc_v = binary_assign_constant_acc_v s,\<close>
  \<comment> \<open>         binary_assign_constant_acc_x = binary_assign_constant_acc_x s,\<close>
  \<comment> \<open>         binary_assign_constant_acc_ret = binary_assign_constant_acc_ret'\<rparr>\<close>
"

definition binary_assign_constant_acc_IMP_Minus where
  "binary_assign_constant_acc_IMP_Minus \<equiv>
  binary_assign_constant_acc_IMP_init_while_cond;;
  WHILE binary_assign_constant_acc_while_cond \<noteq>0 DO (
    binary_assign_constant_acc_IMP_loop_body;;
    binary_assign_constant_acc_IMP_init_while_cond
  );;
  binary_assign_constant_acc_IMP_after_loop"

abbreviation "binary_assign_constant_acc_IMP_vars\<equiv>
  {binary_assign_constant_acc_acc_str, binary_assign_constant_acc_diff_str, binary_assign_constant_acc_n_str,
  binary_assign_constant_acc_v_str, binary_assign_constant_acc_x_str, binary_assign_constant_acc_ret_str,
  binary_assign_constant_acc_cons_result}"

lemmas binary_assign_constant_acc_IMP_subprogram_simps =
  binary_assign_constant_acc_IMP_init_while_cond_def
  binary_assign_constant_acc_IMP_loop_body_def
  binary_assign_constant_acc_IMP_after_loop_def

definition "binary_assign_constant_acc_imp_to_HOL_state p s =
  \<lparr>binary_assign_constant_acc_acc = (s (add_prefix p binary_assign_constant_acc_acc_str)),
   binary_assign_constant_acc_diff = (s (add_prefix p binary_assign_constant_acc_diff_str)),
   binary_assign_constant_acc_n = (s (add_prefix p binary_assign_constant_acc_n_str)),
   binary_assign_constant_acc_v = (s (add_prefix p binary_assign_constant_acc_v_str)),
   binary_assign_constant_acc_x = (s (add_prefix p binary_assign_constant_acc_x_str)),
   binary_assign_constant_acc_ret = (s (add_prefix p binary_assign_constant_acc_ret_str))\<rparr>"

lemmas binary_assign_constant_acc_state_translators =
  binary_assign_constant_acc_imp_to_HOL_state_def
  binary_assign_constant_acc_aux_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def

lemmas binary_assign_constant_acc_complete_simps =
  binary_assign_constant_acc_IMP_subprogram_simps
  binary_assign_constant_acc_imp_subprogram_simps
  binary_assign_constant_acc_state_translators

lemma binary_assign_constant_acc_IMP_Minus_correct_function:
  "(invoke_subprogram p binary_assign_constant_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p binary_assign_constant_acc_ret_str)
      = binary_assign_constant_acc_ret
          (binary_assign_constant_acc_imp (binary_assign_constant_acc_imp_to_HOL_state p s))"
  apply(induction "binary_assign_constant_acc_imp_to_HOL_state p s" arbitrary: s s' t
    rule: binary_assign_constant_acc_imp.induct)
  apply(subst binary_assign_constant_acc_imp.simps)
  apply(simp only: binary_assign_constant_acc_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule While_tE)

  subgoal
    apply(simp only: binary_assign_constant_acc_IMP_subprogram_simps prefix_simps)
    by(fastforce simp: binary_assign_constant_acc_IMP_subprogram_simps
        binary_assign_constant_acc_imp_subprogram_simps
        binary_assign_constant_acc_state_translators)

  apply(erule Seq_E)+
  apply(dest_com_gen)

  subgoal
      apply(simp only: binary_assign_constant_acc_IMP_init_while_cond_def prefix_simps)
      by(fastforce simp add: binary_assign_constant_acc_complete_simps)

  subgoal
      apply(subst (asm) binary_assign_constant_acc_IMP_init_while_cond_def)
      apply(simp only: binary_assign_constant_acc_IMP_loop_body_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule binary_assign_constant_acc_aux_IMP_Minus_correct[where vars = "binary_assign_constant_acc_IMP_vars"])
      subgoal premises p using p(30) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_acc_IMP_vars"])
      subgoal premises p using p(32) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_acc_IMP_vars"])
      subgoal premises p using p(34) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_acc_IMP_vars"])
      subgoal premises p using p(36) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_acc_IMP_vars"])
      subgoal premises p using p(38) by fastforce
      by (fastforce_sorted_premises simp: binary_assign_constant_acc_imp_subprogram_simps
          binary_assign_constant_acc_state_translators Let_def)

  subgoal
      apply(simp only: binary_assign_constant_acc_IMP_init_while_cond_def prefix_simps
          binary_assign_constant_acc_IMP_loop_body_def)
      apply(erule Seq_E)+
      apply(erule binary_assign_constant_acc_aux_IMP_Minus_correct[where vars = "binary_assign_constant_acc_IMP_vars"])
      subgoal premises p using p(30) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_acc_IMP_vars"])
      subgoal premises p using p(32) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_acc_IMP_vars"])
      subgoal premises p using p(34) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_acc_IMP_vars"])
      subgoal premises p using p(36) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_acc_IMP_vars"])
      subgoal premises p using p(38) by fastforce
      by (fastforce_sorted_premises simp: binary_assign_constant_acc_imp_subprogram_simps
          binary_assign_constant_acc_state_translators Let_def)
    done  

lemma binary_assign_constant_acc_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ binary_assign_constant_acc_pref) binary_assign_constant_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix binary_assign_constant_acc_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast   

lemmas binary_assign_constant_acc_complete_time_simps =
  binary_assign_constant_acc_imp_subprogram_time_simps
  binary_assign_constant_acc_imp_time_acc
  binary_assign_constant_acc_imp_time_acc_2
  binary_assign_constant_acc_imp_time_acc_3
  binary_assign_constant_acc_state_translators

lemma binary_assign_constant_acc_IMP_Minus_correct_time:
  "(invoke_subprogram p binary_assign_constant_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = binary_assign_constant_acc_imp_time 0 (binary_assign_constant_acc_imp_to_HOL_state p s)"
  apply(induction "binary_assign_constant_acc_imp_to_HOL_state p s" arbitrary: s s' t
      rule: binary_assign_constant_acc_imp.induct)
  apply(subst binary_assign_constant_acc_imp_time.simps)
  apply(simp only: binary_assign_constant_acc_IMP_Minus_def prefix_simps)

  apply(erule Seq_tE)+
  apply(erule While_tE_time)

  subgoal
    apply(simp only: binary_assign_constant_acc_IMP_subprogram_simps prefix_simps)
    by (force simp: binary_assign_constant_acc_IMP_subprogram_simps
        binary_assign_constant_acc_imp_subprogram_time_simps binary_assign_constant_acc_state_translators)

  apply(erule Seq_tE)+
  apply(simp add: add.assoc)
  apply(dest_com_gen_time)

  subgoal
    apply(simp only: binary_assign_constant_acc_IMP_init_while_cond_def prefix_simps)
    by(fastforce simp add: binary_assign_constant_acc_complete_simps)

  subgoal
    apply(subst (asm) binary_assign_constant_acc_IMP_init_while_cond_def)
    apply(simp only: binary_assign_constant_acc_IMP_loop_body_def prefix_simps)
    apply(erule Seq_tE)+
    apply(erule binary_assign_constant_acc_aux_IMP_Minus_correct[where vars = "binary_assign_constant_acc_IMP_vars"])
    subgoal premises p using p(57) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_acc_IMP_vars"])
    subgoal premises p using p(59) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_acc_IMP_vars"])
    subgoal premises p using p(61) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_acc_IMP_vars"])
    subgoal premises p using p(63) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_acc_IMP_vars"])
    subgoal premises p using p(65) by fastforce
    by (fastforce_sorted_premises simp: binary_assign_constant_acc_imp_subprogram_time_simps
        binary_assign_constant_acc_state_translators Let_def)

  subgoal
    apply(simp only: prefix_simps binary_assign_constant_acc_IMP_init_while_cond_def
        binary_assign_constant_acc_IMP_loop_body_def)
    apply(erule Seq_tE)+
    apply(erule binary_assign_constant_acc_aux_IMP_Minus_correct[where vars = "binary_assign_constant_acc_IMP_vars"])
    subgoal premises p using p(57) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_acc_IMP_vars"])
    subgoal premises p using p(59) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_acc_IMP_vars"])
    subgoal premises p using p(61) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_acc_IMP_vars"])
    subgoal premises p using p(63) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_acc_IMP_vars"])
    subgoal premises p using p(65) by fastforce
    apply(simp only: binary_assign_constant_acc_complete_time_simps Let_def)
    by(force simp: Let_def binary_assign_constant_acc_state_translators)

  done   

lemma binary_assign_constant_acc_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) binary_assign_constant_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (binary_assign_constant_acc_imp_time 0 (binary_assign_constant_acc_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) binary_assign_constant_acc_ret_str) =
          binary_assign_constant_acc_ret (binary_assign_constant_acc_imp
                                        (binary_assign_constant_acc_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using binary_assign_constant_acc_IMP_Minus_correct_function
  by (auto simp: binary_assign_constant_acc_IMP_Minus_correct_time)
    (meson binary_assign_constant_acc_IMP_Minus_correct_effects set_mono_prefix)

subsubsection \<open>binary_assign_constant_tail\<close>

record binary_assign_constant_tail_state =
  binary_assign_constant_tail_n::nat
  binary_assign_constant_tail_v::nat
  binary_assign_constant_tail_x::nat
  binary_assign_constant_tail_ret::nat

abbreviation "binary_assign_constant_tail_prefix \<equiv> ''binary_assign_constant_tail.''"
abbreviation "binary_assign_constant_tail_n_str \<equiv> ''n''"
abbreviation "binary_assign_constant_tail_v_str \<equiv> ''v''"
abbreviation "binary_assign_constant_tail_x_str \<equiv> ''x''"
abbreviation "binary_assign_constant_tail_ret_str \<equiv> ''ret''"

definition "binary_assign_constant_tail_state_upd s =
  (let
      cons_h' = 0;
      cons_t' = 0;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      binary_assign_constant_acc_acc' = cons_ret cons_ret_state;
      binary_assign_constant_acc_diff' = binary_assign_constant_tail_n s;
      binary_assign_constant_acc_n' = binary_assign_constant_tail_n s;
      binary_assign_constant_acc_v' = binary_assign_constant_tail_v s;
      binary_assign_constant_acc_x' = binary_assign_constant_tail_x s;
      binary_assign_constant_acc_ret' = 0;
      binary_assign_constant_acc_state = \<lparr>binary_assign_constant_acc_acc = binary_assign_constant_acc_acc',
                                          binary_assign_constant_acc_diff = binary_assign_constant_acc_diff',
                                          binary_assign_constant_acc_n = binary_assign_constant_acc_n',
                                          binary_assign_constant_acc_v = binary_assign_constant_acc_v',
                                          binary_assign_constant_acc_x = binary_assign_constant_acc_x',
                                          binary_assign_constant_acc_ret = binary_assign_constant_acc_ret'\<rparr>;
      binary_assign_constant_acc_ret_state = binary_assign_constant_acc_imp binary_assign_constant_acc_state;
      binary_assign_constant_tail_ret' = binary_assign_constant_acc_ret binary_assign_constant_acc_ret_state;
      ret = \<lparr>binary_assign_constant_tail_n = binary_assign_constant_tail_n s,
             binary_assign_constant_tail_v = binary_assign_constant_tail_v s,
             binary_assign_constant_tail_x = binary_assign_constant_tail_x s,
             binary_assign_constant_tail_ret = binary_assign_constant_tail_ret'\<rparr>
  in
      ret
)"

function binary_assign_constant_tail_imp ::
  "binary_assign_constant_tail_state \<Rightarrow> binary_assign_constant_tail_state" where
  "binary_assign_constant_tail_imp s =
  (let 
      ret = binary_assign_constant_tail_state_upd s
    in 
      ret
  )"
  by simp+
termination
  by (relation "measure binary_assign_constant_tail_n") simp

declare binary_assign_constant_tail_imp.simps [simp del]

lemma binary_assign_constant_tail_imp_correct[let_function_correctness]:
  "binary_assign_constant_tail_ret (binary_assign_constant_tail_imp s) =
    binary_assign_constant_tail (binary_assign_constant_tail_n s) (binary_assign_constant_tail_v s)
      (binary_assign_constant_tail_x s)"
  by (simp add: binary_assign_constant_tail_imp.simps Let_def binary_assign_constant_tail_state_upd_def
    cons_imp_correct binary_assign_constant_acc_imp_correct binary_assign_constant_tail_def)

function binary_assign_constant_tail_imp_time ::
  "nat \<Rightarrow> binary_assign_constant_tail_state \<Rightarrow> nat" where
  "binary_assign_constant_tail_imp_time t s =
  (let
      cons_h' = 0;
      t = t + 2;
      cons_t' = 0;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      binary_assign_constant_acc_acc' = cons_ret cons_ret_state;
      t = t + 2;
      binary_assign_constant_acc_diff' = binary_assign_constant_tail_n s;
      t = t + 2;
      binary_assign_constant_acc_n' = binary_assign_constant_tail_n s;
      t = t + 2;
      binary_assign_constant_acc_v' = binary_assign_constant_tail_v s;
      t = t + 2;
      binary_assign_constant_acc_x' = binary_assign_constant_tail_x s;
      t = t + 2;
      binary_assign_constant_acc_ret' = 0;
      t = t + 2;
      binary_assign_constant_acc_state = \<lparr>binary_assign_constant_acc_acc = binary_assign_constant_acc_acc',
                                          binary_assign_constant_acc_diff = binary_assign_constant_acc_diff',
                                          binary_assign_constant_acc_n = binary_assign_constant_acc_n',
                                          binary_assign_constant_acc_v = binary_assign_constant_acc_v',
                                          binary_assign_constant_acc_x = binary_assign_constant_acc_x',
                                          binary_assign_constant_acc_ret = binary_assign_constant_acc_ret'\<rparr>;
      binary_assign_constant_acc_ret_state = binary_assign_constant_acc_imp binary_assign_constant_acc_state;
      t = t + binary_assign_constant_acc_imp_time 0 binary_assign_constant_acc_state;
      binary_assign_constant_tail_ret' = binary_assign_constant_acc_ret binary_assign_constant_acc_ret_state;
      t = t + 2;
      ret = \<lparr>binary_assign_constant_tail_n = binary_assign_constant_tail_n s,
             binary_assign_constant_tail_v = binary_assign_constant_tail_v s,
             binary_assign_constant_tail_x = binary_assign_constant_tail_x s,
             binary_assign_constant_tail_ret = binary_assign_constant_tail_ret'\<rparr>
  in
      t
  )"
  by auto
termination
  by (relation "measure (binary_assign_constant_tail_n \<circ> snd)") simp

declare binary_assign_constant_tail_imp_time.simps [simp del]

lemma binary_assign_constant_tail_imp_time_acc:
  "(binary_assign_constant_tail_imp_time (Suc t) s) = Suc (binary_assign_constant_tail_imp_time t s)"
  by (induction t s rule: binary_assign_constant_tail_imp_time.induct)
    ((subst (1 2) binary_assign_constant_tail_imp_time.simps);
      (simp add: binary_assign_constant_tail_state_upd_def Let_def))            

lemma binary_assign_constant_tail_imp_time_acc_2_aux:
  "(binary_assign_constant_tail_imp_time t s) = t + (binary_assign_constant_tail_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: binary_assign_constant_tail_imp_time_acc)+            

lemma binary_assign_constant_tail_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (binary_assign_constant_tail_imp_time t s) = t + (binary_assign_constant_tail_imp_time 0 s)"
  by (rule binary_assign_constant_tail_imp_time_acc_2_aux)            

lemma binary_assign_constant_tail_imp_time_acc_3:
  "(binary_assign_constant_tail_imp_time (a + b) s) = a + (binary_assign_constant_tail_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: binary_assign_constant_tail_imp_time_acc)+    

definition binary_assign_constant_tail_IMP_Minus where
  "binary_assign_constant_tail_IMP_Minus \<equiv>
  \<comment> \<open>  cons_h' = 0;\<close>
  (cons_prefix @ cons_h_str) ::= (A (N 0));;
  \<comment> \<open>  cons_t' = 0;\<close>
  (cons_prefix @ cons_t_str) ::= (A (N 0));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  binary_assign_constant_acc_acc' = cons_ret cons_ret_state;\<close>
  (binary_assign_constant_acc_prefix @ binary_assign_constant_acc_acc_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  binary_assign_constant_acc_diff' = binary_assign_constant_tail_n s;\<close>
  (binary_assign_constant_acc_prefix @ binary_assign_constant_acc_diff_str) ::= (A (V binary_assign_constant_tail_n_str));;
  \<comment> \<open>  binary_assign_constant_acc_n' = binary_assign_constant_tail_n s;\<close>
  (binary_assign_constant_acc_prefix @ binary_assign_constant_acc_n_str) ::= (A (V binary_assign_constant_tail_n_str));;
  \<comment> \<open>  binary_assign_constant_acc_v' = binary_assign_constant_tail_v s;\<close>
  (binary_assign_constant_acc_prefix @ binary_assign_constant_acc_v_str) ::= (A (V binary_assign_constant_tail_v_str));;
  \<comment> \<open>  binary_assign_constant_acc_x' = binary_assign_constant_tail_x s;\<close>
  (binary_assign_constant_acc_prefix @ binary_assign_constant_acc_x_str) ::= (A (V binary_assign_constant_tail_x_str));;
  \<comment> \<open>  binary_assign_constant_acc_ret' = 0;\<close>
  (binary_assign_constant_acc_prefix @ binary_assign_constant_acc_ret_str) ::= (A (N 0));;
  \<comment> \<open>  binary_assign_constant_acc_state = \<lparr>binary_assign_constant_acc_acc = binary_assign_constant_acc_acc',\<close>
  \<comment> \<open>                                      binary_assign_constant_acc_diff = binary_assign_constant_acc_diff',\<close>
  \<comment> \<open>                                      binary_assign_constant_acc_n = binary_assign_constant_acc_n',\<close>
  \<comment> \<open>                                      binary_assign_constant_acc_v = binary_assign_constant_acc_v',\<close>
  \<comment> \<open>                                      binary_assign_constant_acc_x = binary_assign_constant_acc_x',\<close>
  \<comment> \<open>                                      binary_assign_constant_acc_ret = binary_assign_constant_acc_ret'\<rparr>;\<close>
  \<comment> \<open>  binary_assign_constant_acc_ret_state = binary_assign_constant_acc_imp binary_assign_constant_acc_state;\<close>
  (invoke_subprogram binary_assign_constant_acc_prefix binary_assign_constant_acc_IMP_Minus);;
  \<comment> \<open>  binary_assign_constant_tail_ret' = binary_assign_constant_acc_ret binary_assign_constant_acc_ret_state;\<close>
  (binary_assign_constant_tail_ret_str) ::= (A (V (binary_assign_constant_acc_prefix @ binary_assign_constant_acc_ret_str)))
  \<comment> \<open>  ret = \<lparr>binary_assign_constant_tail_n = binary_assign_constant_tail_n s,\<close>
  \<comment> \<open>         binary_assign_constant_tail_v = binary_assign_constant_tail_v s,\<close>
  \<comment> \<open>         binary_assign_constant_tail_x = binary_assign_constant_tail_x s,\<close>
  \<comment> \<open>         binary_assign_constant_tail_ret = binary_assign_constant_tail_ret'\<rparr>\<close>
"

abbreviation "binary_assign_constant_tail_IMP_vars \<equiv>
  {binary_assign_constant_tail_n_str, binary_assign_constant_tail_v_str, binary_assign_constant_tail_x_str,
  binary_assign_constant_tail_ret_str}"

definition "binary_assign_constant_tail_imp_to_HOL_state p s =
  \<lparr>binary_assign_constant_tail_n = (s (add_prefix p binary_assign_constant_tail_n_str)),
   binary_assign_constant_tail_v = (s (add_prefix p binary_assign_constant_tail_v_str)),
   binary_assign_constant_tail_x = (s (add_prefix p binary_assign_constant_tail_x_str)),
   binary_assign_constant_tail_ret = (s (add_prefix p binary_assign_constant_tail_ret_str))\<rparr>"

lemmas binary_assign_constant_tail_state_translators =
  binary_assign_constant_tail_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  binary_assign_constant_acc_imp_to_HOL_state_def

lemma binary_assign_constant_tail_IMP_Minus_correct_function:
  "(invoke_subprogram p binary_assign_constant_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p binary_assign_constant_tail_ret_str)
      = binary_assign_constant_tail_ret
          (binary_assign_constant_tail_imp (binary_assign_constant_tail_imp_to_HOL_state p s))"
  apply(subst binary_assign_constant_tail_imp.simps)
  apply(simp only: binary_assign_constant_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_tail_IMP_vars"])
  subgoal premises p using p(12) by fastforce
  apply(erule binary_assign_constant_acc_IMP_Minus_correct[where vars = "binary_assign_constant_tail_IMP_vars"])
  subgoal premises p using p(14) by fastforce
  by(fastforce simp: binary_assign_constant_tail_state_translators
    binary_assign_constant_tail_state_upd_def) 

lemma binary_assign_constant_tail_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ binary_assign_constant_tail_pref) binary_assign_constant_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix binary_assign_constant_tail_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast  

lemma binary_assign_constant_tail_IMP_Minus_correct_time:
  "(invoke_subprogram p binary_assign_constant_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = binary_assign_constant_tail_imp_time 0 (binary_assign_constant_tail_imp_to_HOL_state p s)"
  apply(subst binary_assign_constant_tail_imp_time.simps)
  apply(simp only: binary_assign_constant_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule cons_IMP_Minus_correct[where vars = "binary_assign_constant_tail_IMP_vars"])
  subgoal premises p using p(23) by fastforce
  apply(erule binary_assign_constant_acc_IMP_Minus_correct[where vars = "binary_assign_constant_tail_IMP_vars"])
  subgoal premises p using p(25) by fastforce
  by(fastforce simp add: Let_def binary_assign_constant_tail_state_translators) 

lemma binary_assign_constant_tail_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) binary_assign_constant_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (binary_assign_constant_tail_imp_time 0 (binary_assign_constant_tail_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) binary_assign_constant_tail_ret_str) =
          binary_assign_constant_tail_ret (binary_assign_constant_tail_imp
                                        (binary_assign_constant_tail_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using binary_assign_constant_tail_IMP_Minus_correct_function
    binary_assign_constant_tail_IMP_Minus_correct_time
    binary_assign_constant_tail_IMP_Minus_correct_effects
  by (meson set_mono_prefix)


subsection copy_var_to_operand

subsubsection copy_var_to_operand_aux1

record copy_var_to_operand_aux1_state=
copy_var_to_operand_aux1_op::nat
copy_var_to_operand_aux1_diff::nat
copy_var_to_operand_aux1_ret::nat

abbreviation "copy_var_to_operand_aux1_prefix \<equiv> ''copy_var_to_operand_aux1_op.''"
abbreviation "copy_var_to_operand_aux1_op_str \<equiv> ''op''"
abbreviation "copy_var_to_operand_aux1_diff_str \<equiv> ''diff''"
abbreviation "copy_var_to_operand_aux1_ret_str \<equiv> ''ret''"

definition "copy_var_to_operand_aux1_imp_state_upd s \<equiv> 
 (let
   prod_encode_a' = copy_var_to_operand_aux1_op s;
   prod_encode_b' = copy_var_to_operand_aux1_diff s;
   prod_encode_ret' = 0;
   prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                       prod_encode_b = prod_encode_b',
                       prod_encode_ret = prod_encode_ret'\<rparr>;
   prod_encode_ret_state = prod_encode_imp prod_encode_state;
   var_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
   var_bit_to_var_tail_ret' = 0;
   var_bit_to_var_tail_state = \<lparr>var_bit_to_var_tail_n = var_bit_to_var_tail_n',
                               var_bit_to_var_tail_ret = var_bit_to_var_tail_ret'\<rparr>;
   var_bit_to_var_tail_ret_state = var_bit_to_var_tail_imp var_bit_to_var_tail_state;

   cons_h' = var_bit_to_var_tail_ret var_bit_to_var_tail_ret_state;
   cons_t' = 0;
   cons_ret' = 0;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;

   copy_var_to_operand_aux1_ret' = cons_ret cons_ret_state;
   ret = \<lparr>copy_var_to_operand_aux1_op = copy_var_to_operand_aux1_op s,
         copy_var_to_operand_aux1_diff = copy_var_to_operand_aux1_diff s,
         copy_var_to_operand_aux1_ret = copy_var_to_operand_aux1_ret'\<rparr>
  in
   ret)"

function copy_var_to_operand_aux1_imp 
 :: "copy_var_to_operand_aux1_state \<Rightarrow> copy_var_to_operand_aux1_state" where 
"copy_var_to_operand_aux1_imp s = 
  (let
     ret = copy_var_to_operand_aux1_imp_state_upd s
   in
    ret)" by simp+
termination 
  by (relation "measure copy_var_to_operand_aux1_op", simp)

declare copy_var_to_operand_aux1_imp.simps[simp del]

lemma copy_var_to_operand_aux1_imp_correct[let_function_correctness]:
  "copy_var_to_operand_aux1_ret (copy_var_to_operand_aux1_imp s)
    = ((var_bit_to_var_tail (prod_encode (
        (copy_var_to_operand_aux1_op s), (copy_var_to_operand_aux1_diff s)))) ## 0)"
apply (subst copy_var_to_operand_aux1_imp.simps copy_var_to_operand_aux1_imp_state_upd_def)+
apply (auto simp add: Let_def var_bit_to_var_tail_imp_correct 
  cons_imp_correct prod_encode_imp_correct)
done 

definition "copy_var_to_operand_aux1_imp_state_upd_time t s \<equiv> 
 (let
   prod_encode_a' = copy_var_to_operand_aux1_op s;
   t = t + 2;
   prod_encode_b' = copy_var_to_operand_aux1_diff s;
   t = t + 2;
   prod_encode_ret' = 0;
   t = t + 2;
   prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                       prod_encode_b = prod_encode_b',
                       prod_encode_ret = prod_encode_ret'\<rparr>;
   prod_encode_ret_state = prod_encode_imp prod_encode_state;
   t = t + prod_encode_imp_time 0 prod_encode_state;

   var_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
   t = t + 2;
   var_bit_to_var_tail_ret' = 0;
   t = t + 2;
   var_bit_to_var_tail_state = \<lparr>var_bit_to_var_tail_n = var_bit_to_var_tail_n',
                               var_bit_to_var_tail_ret = var_bit_to_var_tail_ret'\<rparr>;
   var_bit_to_var_tail_ret_state = var_bit_to_var_tail_imp var_bit_to_var_tail_state;
   t = t + var_bit_to_var_tail_imp_time 0 var_bit_to_var_tail_state;

   cons_h' = var_bit_to_var_tail_ret var_bit_to_var_tail_ret_state;
   t = t + 2;
   cons_t' = 0;
   t = t + 2;
   cons_ret' = 0;
   t = t + 2;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

   copy_var_to_operand_aux1_ret' = cons_ret cons_ret_state;
   t = t + 2;
   ret = \<lparr>copy_var_to_operand_aux1_op = copy_var_to_operand_aux1_op s,
         copy_var_to_operand_aux1_diff = copy_var_to_operand_aux1_diff s,
         copy_var_to_operand_aux1_ret = copy_var_to_operand_aux1_ret'\<rparr>
  in
   t)"

function copy_var_to_operand_aux1_imp_time 
 :: "nat \<Rightarrow> copy_var_to_operand_aux1_state \<Rightarrow> nat" where 
"copy_var_to_operand_aux1_imp_time t s = 
  (let
     ret = copy_var_to_operand_aux1_imp_state_upd s;
     t = t + copy_var_to_operand_aux1_imp_state_upd_time 0 s
   in
    t)" by auto
termination 
  by (relation "measure (copy_var_to_operand_aux1_op \<circ> snd)", simp)

definition "copy_var_to_operand_aux1_IMP_Minus \<equiv> 
  (prod_encode_prefix @ prod_encode_a_str) ::= A (V copy_var_to_operand_aux1_op_str);;
  (prod_encode_prefix @ prod_encode_b_str) ::= A (V copy_var_to_operand_aux1_diff_str);;
  (prod_encode_prefix @ prod_encode_ret_str) ::= A (N 0);;
  invoke_subprogram prod_encode_prefix prod_encode_IMP_Minus;;
  
  (var_bit_to_var_tail_prefix @ var_bit_to_var_tail_n_str) ::= A (V (prod_encode_prefix @ prod_encode_ret_str));;
  (var_bit_to_var_tail_prefix @ var_bit_to_var_tail_ret_str) ::= A (N 0);;
  invoke_subprogram var_bit_to_var_tail_prefix var_bit_to_var_tail_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (var_bit_to_var_tail_prefix @ var_bit_to_var_tail_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  copy_var_to_operand_aux1_ret_str ::= A (V (cons_prefix @ cons_ret_str))"

abbreviation "copy_var_to_operand_aux1_IMP_vars \<equiv> 
  {copy_var_to_operand_aux1_op_str, copy_var_to_operand_aux1_diff_str, copy_var_to_operand_aux1_ret_str}"

definition "copy_var_to_operand_aux1_imp_to_HOL_state p s \<equiv> 
  \<lparr>copy_var_to_operand_aux1_op = s (add_prefix p copy_var_to_operand_aux1_op_str),
  copy_var_to_operand_aux1_diff = s (add_prefix p copy_var_to_operand_aux1_diff_str),
  copy_var_to_operand_aux1_ret = s (add_prefix p copy_var_to_operand_aux1_ret_str)\<rparr>"

lemmas copy_var_to_operand_aux1_state_translators =
  copy_var_to_operand_aux1_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  var_bit_to_var_tail_imp_to_HOL_state_def 
  prod_encode_imp_to_HOL_state_def

lemma copy_var_to_operand_aux1_IMP_Minus_correct_function:
  "(invoke_subprogram p copy_var_to_operand_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_var_to_operand_aux1_ret_str)
      = copy_var_to_operand_aux1_ret (copy_var_to_operand_aux1_imp (copy_var_to_operand_aux1_imp_to_HOL_state p s))"
  apply (simp only: copy_var_to_operand_aux1_imp.simps copy_var_to_operand_aux1_imp_state_upd_def)
  apply (simp only: copy_var_to_operand_aux1_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule prod_encode_IMP_Minus_correct[where vars=copy_var_to_operand_aux1_IMP_vars])
  subgoal premises p using p(12) by fastforce
  apply (erule var_bit_to_var_tail_IMP_Minus_correct[where vars=copy_var_to_operand_aux1_IMP_vars])
  subgoal premises p using p(14) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux1_IMP_vars])
  subgoal premises p using p(16) by fastforce
  apply (force simp add: copy_var_to_operand_aux1_state_translators Let_def)
  done 

lemma copy_var_to_operand_aux1_IMP_Minus_correct_time:
  "(invoke_subprogram p copy_var_to_operand_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = copy_var_to_operand_aux1_imp_time 0 (copy_var_to_operand_aux1_imp_to_HOL_state p s)"
  apply (simp only: copy_var_to_operand_aux1_imp_time.simps copy_var_to_operand_aux1_imp_state_upd_time_def)
  apply (simp only: copy_var_to_operand_aux1_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule prod_encode_IMP_Minus_correct[where vars=copy_var_to_operand_aux1_IMP_vars])
  subgoal premises p using p(23) by fastforce
  apply (erule var_bit_to_var_tail_IMP_Minus_correct[where vars=copy_var_to_operand_aux1_IMP_vars])
  subgoal premises p using p(25) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux1_IMP_vars])
  subgoal premises p using p(27) by fastforce
  apply (force simp add: copy_var_to_operand_aux1_state_translators Let_def)
  done 

lemma copy_var_to_operand_aux1_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_var_to_operand_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
     \<lbrakk>t = (copy_var_to_operand_aux1_imp_time 0 (copy_var_to_operand_aux1_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) copy_var_to_operand_aux1_ret_str) =
        copy_var_to_operand_aux1_ret
          (copy_var_to_operand_aux1_imp (copy_var_to_operand_aux1_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_var_to_operand_aux1_IMP_Minus_correct_function 
      copy_var_to_operand_aux1_IMP_Minus_correct_time
       set_mono_prefix
  by (smt (verit, ccfv_SIG) com_add_prefix_valid_subset com_only_vars)

subsubsection copy_var_to_operand_aux2

record copy_var_to_operand_aux2_state=
copy_var_to_operand_aux2_op::nat
copy_var_to_operand_aux2_diff::nat
copy_var_to_operand_aux2_ret::nat

abbreviation "copy_var_to_operand_aux2_prefix \<equiv> ''copy_var_to_operand_aux2_op.''"
abbreviation "copy_var_to_operand_aux2_op_str \<equiv> ''op''"
abbreviation "copy_var_to_operand_aux2_diff_str \<equiv> ''diff''"
abbreviation "copy_var_to_operand_aux2_ret_str \<equiv> ''ret''"

definition "copy_var_to_operand_aux2_imp_state_upd s \<equiv> 
 (let
   prod_encode_a' = copy_var_to_operand_aux2_op s;
   prod_encode_b' = copy_var_to_operand_aux2_diff s;
   prod_encode_ret' = 0;
   prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                       prod_encode_b = prod_encode_b',
                       prod_encode_ret = prod_encode_ret'\<rparr>;
   prod_encode_ret_state = prod_encode_imp prod_encode_state;
   operand_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
   operand_bit_to_var_tail_ret' = 0;
   operand_bit_to_var_tail_state = \<lparr>operand_bit_to_var_tail_n = operand_bit_to_var_tail_n',
                               operand_bit_to_var_tail_ret = operand_bit_to_var_tail_ret'\<rparr>;
   operand_bit_to_var_tail_ret_state = operand_bit_to_var_tail_imp operand_bit_to_var_tail_state;

   cons_h' = 1;
   cons_t' = 0;
   cons_ret' = 0;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;

   cons_h' = operand_bit_to_var_tail_ret operand_bit_to_var_tail_ret_state;
   cons_t' = cons_ret cons_ret_state;
   cons_ret' = 0;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;

   cons_h' = 1;
   cons_t' = cons_ret cons_ret_state;
   cons_ret' = 0;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;

   copy_var_to_operand_aux2_ret' = cons_ret cons_ret_state;
   ret = \<lparr>copy_var_to_operand_aux2_op = copy_var_to_operand_aux2_op s,
         copy_var_to_operand_aux2_diff = copy_var_to_operand_aux2_diff s,
         copy_var_to_operand_aux2_ret = copy_var_to_operand_aux2_ret'\<rparr>
  in
   ret)"

function copy_var_to_operand_aux2_imp 
 :: "copy_var_to_operand_aux2_state \<Rightarrow> copy_var_to_operand_aux2_state" where 
"copy_var_to_operand_aux2_imp s = 
  (let
     ret = copy_var_to_operand_aux2_imp_state_upd s
   in
    ret)" by simp+
termination 
  by (relation "measure copy_var_to_operand_aux2_op", simp)

declare copy_var_to_operand_aux2_imp.simps[simp del]

lemma copy_var_to_operand_aux2_imp_correct[let_function_correctness]:
  "copy_var_to_operand_aux2_ret (copy_var_to_operand_aux2_imp s)
    = (1 ## (operand_bit_to_var_tail (prod_encode (
        (copy_var_to_operand_aux2_op s), (copy_var_to_operand_aux2_diff s)))) ## 1 ## 0)"
apply (subst copy_var_to_operand_aux2_imp.simps copy_var_to_operand_aux2_imp_state_upd_def)+
apply (auto simp add: Let_def operand_bit_to_var_tail_imp_correct 
  cons_imp_correct prod_encode_imp_correct)
done 

definition "copy_var_to_operand_aux2_imp_state_upd_time t s \<equiv> 
 (let
   prod_encode_a' = copy_var_to_operand_aux2_op s;
   t = t + 2;
   prod_encode_b' = copy_var_to_operand_aux2_diff s;
   t = t + 2;
   prod_encode_ret' = 0;
   t = t + 2;
   prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                       prod_encode_b = prod_encode_b',
                       prod_encode_ret = prod_encode_ret'\<rparr>;
   prod_encode_ret_state = prod_encode_imp prod_encode_state;
   t = t + prod_encode_imp_time 0 prod_encode_state;

   operand_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
   t = t + 2;
   operand_bit_to_var_tail_ret' = 0;
   t = t + 2;
   operand_bit_to_var_tail_state = \<lparr>operand_bit_to_var_tail_n = operand_bit_to_var_tail_n',
                               operand_bit_to_var_tail_ret = operand_bit_to_var_tail_ret'\<rparr>;
   operand_bit_to_var_tail_ret_state = operand_bit_to_var_tail_imp operand_bit_to_var_tail_state;
   t = t + operand_bit_to_var_tail_imp_time 0 operand_bit_to_var_tail_state;

   cons_h' = 1;
   t = t + 2;
   cons_t' = 0;
   t = t + 2;
   cons_ret' = 0;
   t = t + 2;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

   cons_h' = operand_bit_to_var_tail_ret operand_bit_to_var_tail_ret_state;
   t = t + 2;
   cons_t' = cons_ret cons_ret_state;
   t = t + 2;
   cons_ret' = 0;
   t = t + 2;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

   cons_h' = 1;
   t = t + 2;
   cons_t' = cons_ret cons_ret_state;
   t = t + 2;
   cons_ret' = 0;
   t = t + 2;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

   copy_var_to_operand_aux2_ret' = cons_ret cons_ret_state;
   t = t + 2;
   ret = \<lparr>copy_var_to_operand_aux2_op = copy_var_to_operand_aux2_op s,
         copy_var_to_operand_aux2_diff = copy_var_to_operand_aux2_diff s,
         copy_var_to_operand_aux2_ret = copy_var_to_operand_aux2_ret'\<rparr>
  in
   t)"

function copy_var_to_operand_aux2_imp_time 
 :: "nat \<Rightarrow> copy_var_to_operand_aux2_state \<Rightarrow> nat" where 
"copy_var_to_operand_aux2_imp_time t s = 
  (let
     ret = copy_var_to_operand_aux2_imp_state_upd s;
     t = t + copy_var_to_operand_aux2_imp_state_upd_time 0 s
   in
    t)" by auto
termination 
  by (relation "measure (copy_var_to_operand_aux2_op \<circ> snd)", simp)

definition "copy_var_to_operand_aux2_IMP_Minus \<equiv> 
  (prod_encode_prefix @ prod_encode_a_str) ::= A (V copy_var_to_operand_aux2_op_str);;
  (prod_encode_prefix @ prod_encode_b_str) ::= A (V copy_var_to_operand_aux2_diff_str);;
  (prod_encode_prefix @ prod_encode_ret_str) ::= A (N 0);;
  invoke_subprogram prod_encode_prefix prod_encode_IMP_Minus;;
  
  (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_n_str) ::= A (V (prod_encode_prefix @ prod_encode_ret_str));;
  (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str) ::= A (N 0);;
  invoke_subprogram operand_bit_to_var_tail_prefix operand_bit_to_var_tail_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (N 1);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (N 1);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  copy_var_to_operand_aux2_ret_str ::= A (V (cons_prefix @ cons_ret_str))"

abbreviation "copy_var_to_operand_aux2_IMP_vars \<equiv> 
  {copy_var_to_operand_aux2_op_str, copy_var_to_operand_aux2_diff_str, copy_var_to_operand_aux2_ret_str}"

definition "copy_var_to_operand_aux2_imp_to_HOL_state p s \<equiv> 
  \<lparr>copy_var_to_operand_aux2_op = s (add_prefix p copy_var_to_operand_aux2_op_str),
  copy_var_to_operand_aux2_diff = s (add_prefix p copy_var_to_operand_aux2_diff_str),
  copy_var_to_operand_aux2_ret = s (add_prefix p copy_var_to_operand_aux2_ret_str)\<rparr>"

lemmas copy_var_to_operand_aux2_state_translators =
  copy_var_to_operand_aux2_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  operand_bit_to_var_tail_imp_to_HOL_state_def 
  prod_encode_imp_to_HOL_state_def

lemma copy_var_to_operand_aux2_IMP_Minus_correct_function:
  "(invoke_subprogram p copy_var_to_operand_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_var_to_operand_aux2_ret_str)
      = copy_var_to_operand_aux2_ret (copy_var_to_operand_aux2_imp (copy_var_to_operand_aux2_imp_to_HOL_state p s))"
  apply (simp only: copy_var_to_operand_aux2_imp.simps copy_var_to_operand_aux2_imp_state_upd_def)
  apply (simp only: copy_var_to_operand_aux2_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule prod_encode_IMP_Minus_correct[where vars=copy_var_to_operand_aux2_IMP_vars])
  subgoal premises p using p(20) by fastforce
  apply (erule operand_bit_to_var_tail_IMP_Minus_correct[where vars=copy_var_to_operand_aux2_IMP_vars])
  subgoal premises p using p(22) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux2_IMP_vars])
  subgoal premises p using p(24) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux2_IMP_vars])
  subgoal premises p using p(26) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars="copy_var_to_operand_aux2_IMP_vars 
    \<union> {operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str}"])
  subgoal premises p using p(28) by fastforce
  apply (force simp: copy_var_to_operand_aux2_state_translators Let_def) 
  done 

lemma copy_var_to_operand_aux2_IMP_Minus_correct_time:
  "(invoke_subprogram p copy_var_to_operand_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = copy_var_to_operand_aux2_imp_time 0 (copy_var_to_operand_aux2_imp_to_HOL_state p s)"
  apply (simp only: copy_var_to_operand_aux2_imp_time.simps copy_var_to_operand_aux2_imp_state_upd_time_def)
  apply (simp only: copy_var_to_operand_aux2_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule prod_encode_IMP_Minus_correct[where vars=copy_var_to_operand_aux2_IMP_vars])
  subgoal premises p using p(39) by fastforce
  apply (erule operand_bit_to_var_tail_IMP_Minus_correct[where vars=copy_var_to_operand_aux2_IMP_vars])
  subgoal premises p using p(41) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux2_IMP_vars])
  subgoal premises p using p(43) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux2_IMP_vars])
  subgoal premises p using p(45) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars="copy_var_to_operand_aux2_IMP_vars 
    \<union> {operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str}"])
  subgoal premises p using p(47) by fastforce
  apply (force simp: copy_var_to_operand_aux2_state_translators Let_def) 
  done 

lemma copy_var_to_operand_aux2_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_var_to_operand_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
     \<lbrakk>t = (copy_var_to_operand_aux2_imp_time 0 (copy_var_to_operand_aux2_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) copy_var_to_operand_aux2_ret_str) =
        copy_var_to_operand_aux2_ret
          (copy_var_to_operand_aux2_imp (copy_var_to_operand_aux2_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_var_to_operand_aux2_IMP_Minus_correct_function 
      copy_var_to_operand_aux2_IMP_Minus_correct_time
       set_mono_prefix
  by (smt (verit, ccfv_SIG) com_add_prefix_valid_subset com_only_vars)

subsubsection copy_var_to_operand_aux3

record copy_var_to_operand_aux3_state=
copy_var_to_operand_aux3_op::nat
copy_var_to_operand_aux3_diff::nat
copy_var_to_operand_aux3_ret::nat

abbreviation "copy_var_to_operand_aux3_prefix \<equiv> ''copy_var_to_operand_aux3_op.''"
abbreviation "copy_var_to_operand_aux3_op_str \<equiv> ''op''"
abbreviation "copy_var_to_operand_aux3_diff_str \<equiv> ''diff''"
abbreviation "copy_var_to_operand_aux3_ret_str \<equiv> ''ret''"

definition "copy_var_to_operand_aux3_imp_state_upd s \<equiv> 
 (let
   prod_encode_a' = copy_var_to_operand_aux3_op s;
   prod_encode_b' = copy_var_to_operand_aux3_diff s;
   prod_encode_ret' = 0;
   prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                       prod_encode_b = prod_encode_b',
                       prod_encode_ret = prod_encode_ret'\<rparr>;
   prod_encode_ret_state = prod_encode_imp prod_encode_state;
   operand_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
   operand_bit_to_var_tail_ret' = 0;
   operand_bit_to_var_tail_state = \<lparr>operand_bit_to_var_tail_n = operand_bit_to_var_tail_n',
                               operand_bit_to_var_tail_ret = operand_bit_to_var_tail_ret'\<rparr>;
   operand_bit_to_var_tail_ret_state = operand_bit_to_var_tail_imp operand_bit_to_var_tail_state;

   cons_h' = 0;
   cons_t' = 0;
   cons_ret' = 0;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;

   cons_h' = operand_bit_to_var_tail_ret operand_bit_to_var_tail_ret_state;
   cons_t' = cons_ret cons_ret_state;
   cons_ret' = 0;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;

   cons_h' = 1;
   cons_t' = cons_ret cons_ret_state;
   cons_ret' = 0;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;

   copy_var_to_operand_aux3_ret' = cons_ret cons_ret_state;
   ret = \<lparr>copy_var_to_operand_aux3_op = copy_var_to_operand_aux3_op s,
         copy_var_to_operand_aux3_diff = copy_var_to_operand_aux3_diff s,
         copy_var_to_operand_aux3_ret = copy_var_to_operand_aux3_ret'\<rparr>
  in
   ret)"

function copy_var_to_operand_aux3_imp 
 :: "copy_var_to_operand_aux3_state \<Rightarrow> copy_var_to_operand_aux3_state" where 
"copy_var_to_operand_aux3_imp s = 
  (let
     ret = copy_var_to_operand_aux3_imp_state_upd s
   in
    ret)" by simp+
termination 
  by (relation "measure copy_var_to_operand_aux3_op", simp)

declare copy_var_to_operand_aux3_imp.simps[simp del]

lemma copy_var_to_operand_aux3_imp_correct[let_function_correctness]:
  "copy_var_to_operand_aux3_ret (copy_var_to_operand_aux3_imp s)
    = (1 ## (operand_bit_to_var_tail (prod_encode (
        (copy_var_to_operand_aux3_op s), (copy_var_to_operand_aux3_diff s)))) ## 0 ## 0)"
apply (subst copy_var_to_operand_aux3_imp.simps copy_var_to_operand_aux3_imp_state_upd_def)+
apply (auto simp add: Let_def operand_bit_to_var_tail_imp_correct 
  cons_imp_correct prod_encode_imp_correct)
done 

definition "copy_var_to_operand_aux3_imp_state_upd_time t s \<equiv> 
 (let
   prod_encode_a' = copy_var_to_operand_aux3_op s;
   t = t + 2;
   prod_encode_b' = copy_var_to_operand_aux3_diff s;
   t = t + 2;
   prod_encode_ret' = 0;
   t = t + 2;
   prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                       prod_encode_b = prod_encode_b',
                       prod_encode_ret = prod_encode_ret'\<rparr>;
   prod_encode_ret_state = prod_encode_imp prod_encode_state;
   t = t + prod_encode_imp_time 0 prod_encode_state;

   operand_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
   t = t + 2;
   operand_bit_to_var_tail_ret' = 0;
   t = t + 2;
   operand_bit_to_var_tail_state = \<lparr>operand_bit_to_var_tail_n = operand_bit_to_var_tail_n',
                               operand_bit_to_var_tail_ret = operand_bit_to_var_tail_ret'\<rparr>;
   operand_bit_to_var_tail_ret_state = operand_bit_to_var_tail_imp operand_bit_to_var_tail_state;
   t = t + operand_bit_to_var_tail_imp_time 0 operand_bit_to_var_tail_state;

   cons_h' = 0;
   t = t + 2;
   cons_t' = 0;
   t = t + 2;
   cons_ret' = 0;
   t = t + 2;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

   cons_h' = operand_bit_to_var_tail_ret operand_bit_to_var_tail_ret_state;
   t = t + 2;
   cons_t' = cons_ret cons_ret_state;
   t = t + 2;
   cons_ret' = 0;
   t = t + 2;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

   cons_h' = 1;
   t = t + 2;
   cons_t' = cons_ret cons_ret_state;
   t = t + 2;
   cons_ret' = 0;
   t = t + 2;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

   copy_var_to_operand_aux3_ret' = cons_ret cons_ret_state;
   t = t + 2;
   ret = \<lparr>copy_var_to_operand_aux3_op = copy_var_to_operand_aux3_op s,
         copy_var_to_operand_aux3_diff = copy_var_to_operand_aux3_diff s,
         copy_var_to_operand_aux3_ret = copy_var_to_operand_aux3_ret'\<rparr>
  in
   t)"

function copy_var_to_operand_aux3_imp_time 
 :: "nat \<Rightarrow> copy_var_to_operand_aux3_state \<Rightarrow> nat" where 
"copy_var_to_operand_aux3_imp_time t s = 
  (let
     ret = copy_var_to_operand_aux3_imp_state_upd s;
     t = t + copy_var_to_operand_aux3_imp_state_upd_time 0 s
   in
    t)" by auto
termination 
  by (relation "measure (copy_var_to_operand_aux3_op \<circ> snd)", simp)

definition "copy_var_to_operand_aux3_IMP_Minus \<equiv> 
  (prod_encode_prefix @ prod_encode_a_str) ::= A (V copy_var_to_operand_aux3_op_str);;
  (prod_encode_prefix @ prod_encode_b_str) ::= A (V copy_var_to_operand_aux3_diff_str);;
  (prod_encode_prefix @ prod_encode_ret_str) ::= A (N 0);;
  invoke_subprogram prod_encode_prefix prod_encode_IMP_Minus;;
  
  (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_n_str) ::= A (V (prod_encode_prefix @ prod_encode_ret_str));;
  (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str) ::= A (N 0);;
  invoke_subprogram operand_bit_to_var_tail_prefix operand_bit_to_var_tail_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (N 0);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (N 1);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  copy_var_to_operand_aux3_ret_str ::= A (V (cons_prefix @ cons_ret_str))"

abbreviation "copy_var_to_operand_aux3_IMP_vars \<equiv> 
  {copy_var_to_operand_aux3_op_str, copy_var_to_operand_aux3_diff_str, copy_var_to_operand_aux3_ret_str}"

definition "copy_var_to_operand_aux3_imp_to_HOL_state p s \<equiv> 
  \<lparr>copy_var_to_operand_aux3_op = s (add_prefix p copy_var_to_operand_aux3_op_str),
  copy_var_to_operand_aux3_diff = s (add_prefix p copy_var_to_operand_aux3_diff_str),
  copy_var_to_operand_aux3_ret = s (add_prefix p copy_var_to_operand_aux3_ret_str)\<rparr>"

lemmas copy_var_to_operand_aux3_state_translators =
  copy_var_to_operand_aux3_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  operand_bit_to_var_tail_imp_to_HOL_state_def 
  prod_encode_imp_to_HOL_state_def

lemma copy_var_to_operand_aux3_IMP_Minus_correct_function:
  "(invoke_subprogram p copy_var_to_operand_aux3_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_var_to_operand_aux3_ret_str)
      = copy_var_to_operand_aux3_ret (copy_var_to_operand_aux3_imp (copy_var_to_operand_aux3_imp_to_HOL_state p s))"
  apply (simp only: copy_var_to_operand_aux3_imp.simps copy_var_to_operand_aux3_imp_state_upd_def)
  apply (simp only: copy_var_to_operand_aux3_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule prod_encode_IMP_Minus_correct[where vars=copy_var_to_operand_aux3_IMP_vars])
  subgoal premises p using p(20) by fastforce
  apply (erule operand_bit_to_var_tail_IMP_Minus_correct[where vars=copy_var_to_operand_aux3_IMP_vars])
  subgoal premises p using p(22) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux3_IMP_vars])
  subgoal premises p using p(24) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux3_IMP_vars])
  subgoal premises p using p(26) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars="copy_var_to_operand_aux3_IMP_vars 
    \<union> {operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str}"])
  subgoal premises p using p(28) by fastforce
  apply (force simp: copy_var_to_operand_aux3_state_translators Let_def) 
  done 

lemma copy_var_to_operand_aux3_IMP_Minus_correct_time:
  "(invoke_subprogram p copy_var_to_operand_aux3_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = copy_var_to_operand_aux3_imp_time 0 (copy_var_to_operand_aux3_imp_to_HOL_state p s)"
  apply (simp only: copy_var_to_operand_aux3_imp_time.simps copy_var_to_operand_aux3_imp_state_upd_time_def)
  apply (simp only: copy_var_to_operand_aux3_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule prod_encode_IMP_Minus_correct[where vars=copy_var_to_operand_aux3_IMP_vars])
  subgoal premises p using p(39) by fastforce
  apply (erule operand_bit_to_var_tail_IMP_Minus_correct[where vars=copy_var_to_operand_aux3_IMP_vars])
  subgoal premises p using p(41) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux3_IMP_vars])
  subgoal premises p using p(43) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux3_IMP_vars])
  subgoal premises p using p(45) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars="copy_var_to_operand_aux3_IMP_vars 
    \<union> {operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str}"])
  subgoal premises p using p(47) by fastforce
  apply (force simp: copy_var_to_operand_aux3_state_translators Let_def) 
  done 

lemma copy_var_to_operand_aux3_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_var_to_operand_aux3_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
     \<lbrakk>t = (copy_var_to_operand_aux3_imp_time 0 (copy_var_to_operand_aux3_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) copy_var_to_operand_aux3_ret_str) =
        copy_var_to_operand_aux3_ret
          (copy_var_to_operand_aux3_imp (copy_var_to_operand_aux3_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_var_to_operand_aux3_IMP_Minus_correct_function 
      copy_var_to_operand_aux3_IMP_Minus_correct_time
       set_mono_prefix
  by (smt (verit, ccfv_SIG) com_add_prefix_valid_subset com_only_vars)

subsubsection copy_var_to_operand_aux4

record copy_var_to_operand_aux4_state=
  copy_var_to_operand_aux4_diff::nat
  copy_var_to_operand_aux4_i::nat
  copy_var_to_operand_aux4_op::nat
  copy_var_to_operand_aux4_v::nat 
  copy_var_to_operand_aux4_ret::nat

abbreviation "copy_var_to_operand_aux4_prefix \<equiv> ''copy_var_to_operand_aux4_prefix.''"
abbreviation "copy_var_to_operand_aux4_diff_str \<equiv> ''diff''"
abbreviation "copy_var_to_operand_aux4_i_str \<equiv> ''i''"
abbreviation "copy_var_to_operand_aux4_op_str \<equiv> ''op''"
abbreviation "copy_var_to_operand_aux4_v_str \<equiv> ''v''"
abbreviation "copy_var_to_operand_aux4_ret_str \<equiv> ''ret''"

definition "copy_var_to_operand_aux4_state_upd s \<equiv> 
 (let
   copy_var_to_operand_aux3_op' = copy_var_to_operand_aux4_op s;
   copy_var_to_operand_aux3_diff' = copy_var_to_operand_aux4_i s - copy_var_to_operand_aux4_diff s;
   copy_var_to_operand_aux3_ret' = 0;
   copy_var_to_operand_aux3_state = \<lparr>copy_var_to_operand_aux3_op = copy_var_to_operand_aux3_op',
                                    copy_var_to_operand_aux3_diff = copy_var_to_operand_aux3_diff',
                                    copy_var_to_operand_aux3_ret = copy_var_to_operand_aux3_ret'\<rparr>;
   copy_var_to_operand_aux3_ret_state = copy_var_to_operand_aux3_imp copy_var_to_operand_aux3_state;

   cons_h' = copy_var_to_operand_aux3_ret copy_var_to_operand_aux3_ret_state;
   cons_t' = 0;
   cons_ret' = 0;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;

   copy_var_to_operand_aux2_op' = copy_var_to_operand_aux4_op s;
   copy_var_to_operand_aux2_diff' = copy_var_to_operand_aux4_i s - copy_var_to_operand_aux4_diff s;
   copy_var_to_operand_aux2_ret' = 0;
   copy_var_to_operand_aux2_state = \<lparr>copy_var_to_operand_aux2_op = copy_var_to_operand_aux2_op',
                                    copy_var_to_operand_aux2_diff = copy_var_to_operand_aux2_diff',
                                    copy_var_to_operand_aux2_ret = copy_var_to_operand_aux2_ret'\<rparr>;
   copy_var_to_operand_aux2_ret_state = copy_var_to_operand_aux2_imp copy_var_to_operand_aux2_state;

   cons_h' = copy_var_to_operand_aux2_ret copy_var_to_operand_aux2_ret_state;
   cons_t' = cons_ret cons_ret_state;
   cons_ret' = 0;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;

   copy_var_to_operand_aux1_op' = copy_var_to_operand_aux4_v s;
   copy_var_to_operand_aux1_diff' = copy_var_to_operand_aux4_i s - copy_var_to_operand_aux4_diff s;
   copy_var_to_operand_aux1_ret' = 0;
   copy_var_to_operand_aux1_state = \<lparr>copy_var_to_operand_aux1_op = copy_var_to_operand_aux1_op',
                                    copy_var_to_operand_aux1_diff = copy_var_to_operand_aux1_diff',
                                    copy_var_to_operand_aux1_ret = copy_var_to_operand_aux1_ret'\<rparr>;
  copy_var_to_operand_aux1_ret_state = copy_var_to_operand_aux1_imp copy_var_to_operand_aux1_state;

 cons_h' = copy_var_to_operand_aux1_ret copy_var_to_operand_aux1_ret_state;
 cons_t' = cons_ret cons_ret_state; 
 cons_ret' = 0;
 cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
 cons_ret_state = cons_imp cons_state;

 cons_h' = 3;
 cons_t' = cons_ret cons_ret_state; 
 cons_ret' = 0;
 cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
 cons_ret_state = cons_imp cons_state;

 copy_var_to_operand_aux4_ret' = cons_ret cons_ret_state;
 ret = \<lparr>copy_var_to_operand_aux4_diff = copy_var_to_operand_aux4_diff s,
       copy_var_to_operand_aux4_i = copy_var_to_operand_aux4_i s,
       copy_var_to_operand_aux4_op = copy_var_to_operand_aux4_op s,
       copy_var_to_operand_aux4_v = copy_var_to_operand_aux4_v s,
       copy_var_to_operand_aux4_ret = copy_var_to_operand_aux4_ret'\<rparr>
 in
  ret)"

function copy_var_to_operand_aux4_imp 
  :: "copy_var_to_operand_aux4_state \<Rightarrow> copy_var_to_operand_aux4_state" where
"copy_var_to_operand_aux4_imp s = 
  (let
    ret = copy_var_to_operand_aux4_state_upd s
   in
    ret)" by simp+
termination 
 by (relation "measure copy_var_to_operand_aux4_diff", simp)

declare copy_var_to_operand_aux4_imp.simps[simp del]

lemma copy_var_to_operand_aux4_imp_correct:
  "copy_var_to_operand_aux4_ret (copy_var_to_operand_aux4_imp s) = 
    (3 ## ((var_bit_to_var_tail (prod_encode ((copy_var_to_operand_aux4_v s), 
      (copy_var_to_operand_aux4_i s) - (copy_var_to_operand_aux4_diff s)))) ## 0)
    ## (1 ## (operand_bit_to_var_tail (prod_encode ((copy_var_to_operand_aux4_op s), 
       (copy_var_to_operand_aux4_i s) - (copy_var_to_operand_aux4_diff s)))) ## 1 ## 0)
    ## (1 ## (operand_bit_to_var_tail (prod_encode ((copy_var_to_operand_aux4_op s), 
      (copy_var_to_operand_aux4_i s) - (copy_var_to_operand_aux4_diff s)))) ## 0 ## 0)
    ## 0)"
  apply (simp only: copy_var_to_operand_aux4_imp.simps copy_var_to_operand_aux4_state_upd_def)
  apply (auto simp add: cons_imp_correct Let_def 
    copy_var_to_operand_aux1_imp_correct copy_var_to_operand_aux3_imp_correct
    copy_var_to_operand_aux2_imp_correct)
  done 

definition "copy_var_to_operand_aux4_state_upd_time t s \<equiv> 
 (let
   copy_var_to_operand_aux3_op' = copy_var_to_operand_aux4_op s;
   t = t + 2;
   copy_var_to_operand_aux3_diff' = copy_var_to_operand_aux4_i s - copy_var_to_operand_aux4_diff s;
   t = t + 2;
   copy_var_to_operand_aux3_ret' = 0;
   t = t + 2;
   copy_var_to_operand_aux3_state = \<lparr>copy_var_to_operand_aux3_op = copy_var_to_operand_aux3_op',
                                    copy_var_to_operand_aux3_diff = copy_var_to_operand_aux3_diff',
                                    copy_var_to_operand_aux3_ret = copy_var_to_operand_aux3_ret'\<rparr>;
   copy_var_to_operand_aux3_ret_state = copy_var_to_operand_aux3_imp copy_var_to_operand_aux3_state;
   t = t + copy_var_to_operand_aux3_imp_time 0 copy_var_to_operand_aux3_state;

   cons_h' = copy_var_to_operand_aux3_ret copy_var_to_operand_aux3_ret_state;
   t = t + 2;
   cons_t' = 0;
   t = t + 2;
   cons_ret' = 0;
   t = t + 2;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

   copy_var_to_operand_aux2_op' = copy_var_to_operand_aux4_op s;
   t = t + 2;
   copy_var_to_operand_aux2_diff' = copy_var_to_operand_aux4_i s - copy_var_to_operand_aux4_diff s;
   t = t + 2;
   copy_var_to_operand_aux2_ret' = 0;
   t = t + 2;
   copy_var_to_operand_aux2_state = \<lparr>copy_var_to_operand_aux2_op = copy_var_to_operand_aux2_op',
                                    copy_var_to_operand_aux2_diff = copy_var_to_operand_aux2_diff',
                                    copy_var_to_operand_aux2_ret = copy_var_to_operand_aux2_ret'\<rparr>;
   copy_var_to_operand_aux2_ret_state = copy_var_to_operand_aux2_imp copy_var_to_operand_aux2_state;
   t = t + copy_var_to_operand_aux2_imp_time 0 copy_var_to_operand_aux2_state;

   cons_h' = copy_var_to_operand_aux2_ret copy_var_to_operand_aux2_ret_state;
   t = t + 2;
   cons_t' = cons_ret cons_ret_state;
   t = t + 2;
   cons_ret' = 0;
   t = t + 2;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

   copy_var_to_operand_aux1_op' = copy_var_to_operand_aux4_v s;
   t = t + 2;
   copy_var_to_operand_aux1_diff' = copy_var_to_operand_aux4_i s - copy_var_to_operand_aux4_diff s;
   t = t + 2;
   copy_var_to_operand_aux1_ret' = 0;
   t = t + 2;
   copy_var_to_operand_aux1_state = \<lparr>copy_var_to_operand_aux1_op = copy_var_to_operand_aux1_op',
                                    copy_var_to_operand_aux1_diff = copy_var_to_operand_aux1_diff',
                                    copy_var_to_operand_aux1_ret = copy_var_to_operand_aux1_ret'\<rparr>;
  copy_var_to_operand_aux1_ret_state = copy_var_to_operand_aux1_imp copy_var_to_operand_aux1_state;
   t = t + copy_var_to_operand_aux1_imp_time 0 copy_var_to_operand_aux1_state;

 cons_h' = copy_var_to_operand_aux1_ret copy_var_to_operand_aux1_ret_state;
   t = t + 2;
 cons_t' = cons_ret cons_ret_state; 
   t = t + 2;
 cons_ret' = 0;
   t = t + 2;
 cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
 cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

 cons_h' = 3;
   t = t + 2;
 cons_t' = cons_ret cons_ret_state; 
   t = t + 2;
 cons_ret' = 0;
   t = t + 2;
 cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
 cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

 copy_var_to_operand_aux4_ret' = cons_ret cons_ret_state;
   t = t + 2;
 ret = \<lparr>copy_var_to_operand_aux4_diff = copy_var_to_operand_aux4_diff s,
       copy_var_to_operand_aux4_i = copy_var_to_operand_aux4_i s,
       copy_var_to_operand_aux4_op = copy_var_to_operand_aux4_op s,
       copy_var_to_operand_aux4_v = copy_var_to_operand_aux4_v s,
       copy_var_to_operand_aux4_ret = copy_var_to_operand_aux4_ret'\<rparr>
 in
  t)"


function copy_var_to_operand_aux4_imp_time 
  :: "nat \<Rightarrow> copy_var_to_operand_aux4_state \<Rightarrow> nat" where
"copy_var_to_operand_aux4_imp_time t s = 
  (let
    ret = copy_var_to_operand_aux4_state_upd s;
    t = t + copy_var_to_operand_aux4_state_upd_time 0 s
   in
    t)" by auto
termination 
 by (relation "measure (copy_var_to_operand_aux4_diff \<circ> snd)", simp)

declare copy_var_to_operand_aux4_imp_time.simps[simp del]

definition "copy_var_to_operand_aux4_IMP_Minus \<equiv> 
  (copy_var_to_operand_aux3_prefix @ copy_var_to_operand_aux3_op_str)
    ::= A (V copy_var_to_operand_aux4_op_str);;
  (copy_var_to_operand_aux3_prefix @ copy_var_to_operand_aux3_diff_str)
    ::= Sub (V copy_var_to_operand_aux4_i_str) ((V copy_var_to_operand_aux4_diff_str));;
  (copy_var_to_operand_aux3_prefix @ copy_var_to_operand_aux3_ret_str)
    ::= A (N 0);;
  invoke_subprogram copy_var_to_operand_aux3_prefix copy_var_to_operand_aux3_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (copy_var_to_operand_aux3_prefix @ copy_var_to_operand_aux3_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (copy_var_to_operand_aux2_prefix @ copy_var_to_operand_aux2_op_str)
    ::= A (V copy_var_to_operand_aux4_op_str);;
  (copy_var_to_operand_aux2_prefix @ copy_var_to_operand_aux2_diff_str)
    ::= Sub (V copy_var_to_operand_aux4_i_str) ((V copy_var_to_operand_aux4_diff_str));;
  (copy_var_to_operand_aux2_prefix @ copy_var_to_operand_aux2_ret_str)
    ::= A (N 0);;
  invoke_subprogram copy_var_to_operand_aux2_prefix copy_var_to_operand_aux2_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (copy_var_to_operand_aux2_prefix @ copy_var_to_operand_aux2_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (copy_var_to_operand_aux1_prefix @ copy_var_to_operand_aux1_op_str)
    ::= A (V copy_var_to_operand_aux4_v_str);;
  (copy_var_to_operand_aux1_prefix @ copy_var_to_operand_aux1_diff_str)
    ::= Sub (V copy_var_to_operand_aux4_i_str) ((V copy_var_to_operand_aux4_diff_str));;
  (copy_var_to_operand_aux1_prefix @ copy_var_to_operand_aux1_ret_str)
    ::= A (N 0);;
  invoke_subprogram copy_var_to_operand_aux1_prefix copy_var_to_operand_aux1_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (V (copy_var_to_operand_aux1_prefix @ copy_var_to_operand_aux1_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (cons_prefix @ cons_h_str) ::= A (N 3);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  copy_var_to_operand_aux4_ret_str ::= A (V (cons_prefix @ cons_ret_str))"

abbreviation "copy_var_to_operand_aux4_IMP_vars \<equiv> 
 {copy_var_to_operand_aux4_diff_str, copy_var_to_operand_aux4_i_str,
 copy_var_to_operand_aux4_op_str, copy_var_to_operand_aux4_v_str}"

definition "copy_var_to_operand_aux4_imp_to_HOL_state p s = 
  \<lparr>copy_var_to_operand_aux4_diff = s (add_prefix p copy_var_to_operand_aux4_diff_str),
  copy_var_to_operand_aux4_i = s (add_prefix p copy_var_to_operand_aux4_i_str),
  copy_var_to_operand_aux4_op = s (add_prefix p copy_var_to_operand_aux4_op_str),
  copy_var_to_operand_aux4_v = s (add_prefix p copy_var_to_operand_aux4_v_str),
  copy_var_to_operand_aux4_ret = s (add_prefix p copy_var_to_operand_aux4_ret_str)\<rparr>"

lemmas copy_var_to_operand_aux4_state_translators = 
  copy_var_to_operand_aux4_imp_to_HOL_state_def
  copy_var_to_operand_aux3_imp_to_HOL_state_def
  copy_var_to_operand_aux2_imp_to_HOL_state_def 
  copy_var_to_operand_aux1_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
    
lemma copy_var_to_operand_aux4_IMP_Minus_correct_function:
 "(invoke_subprogram p copy_var_to_operand_aux4_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_var_to_operand_aux4_ret_str)
      = copy_var_to_operand_aux4_ret (copy_var_to_operand_aux4_imp (copy_var_to_operand_aux4_imp_to_HOL_state p s))" 
  apply (simp only: copy_var_to_operand_aux4_imp.simps copy_var_to_operand_aux4_state_upd_def)
  apply (simp only: copy_var_to_operand_aux4_IMP_Minus_def prefix_simps)  
  apply (erule Seq_E)+
  apply (erule copy_var_to_operand_aux3_IMP_Minus_correct[where vars=copy_var_to_operand_aux4_IMP_vars])
  subgoal premises p using p(29) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux4_IMP_vars])
  subgoal premises p using p(31) by fastforce
  apply (erule copy_var_to_operand_aux2_IMP_Minus_correct[where vars="copy_var_to_operand_aux4_IMP_vars \<union> {(cons_prefix @ cons_ret_str)}"])
  subgoal premises p using p(33) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux4_IMP_vars])
  subgoal premises p using p(35) by fastforce
  apply (erule copy_var_to_operand_aux1_IMP_Minus_correct[where vars="copy_var_to_operand_aux4_IMP_vars \<union> {(cons_prefix @ cons_ret_str)}"])
  subgoal premises p using p(37) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux4_IMP_vars])
  subgoal premises p using p(39) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux4_IMP_vars])
  subgoal premises p using p(41) by fastforce
  apply (force simp: copy_var_to_operand_aux4_state_translators Let_def)
  done

lemma copy_var_to_operand_aux4_IMP_Minus_correct_time:
 "(invoke_subprogram p copy_var_to_operand_aux4_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = copy_var_to_operand_aux4_imp_time 0 (copy_var_to_operand_aux4_imp_to_HOL_state p s)" 
  apply (simp only: copy_var_to_operand_aux4_imp_time.simps copy_var_to_operand_aux4_state_upd_time_def)
  apply (simp only: copy_var_to_operand_aux4_IMP_Minus_def prefix_simps)  
  apply (erule Seq_tE)+
  apply (erule copy_var_to_operand_aux3_IMP_Minus_correct[where vars=copy_var_to_operand_aux4_IMP_vars])
  subgoal premises p using p(57) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux4_IMP_vars])
  subgoal premises p using p(59) by fastforce
  apply (erule copy_var_to_operand_aux2_IMP_Minus_correct[where vars="copy_var_to_operand_aux4_IMP_vars \<union> {(cons_prefix @ cons_ret_str)}"])
  subgoal premises p using p(61) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux4_IMP_vars])
  subgoal premises p using p(63) by fastforce
  apply (erule copy_var_to_operand_aux1_IMP_Minus_correct[where vars="copy_var_to_operand_aux4_IMP_vars \<union> {(cons_prefix @ cons_ret_str)}"])
  subgoal premises p using p(65) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux4_IMP_vars])
  subgoal premises p using p(67) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux4_IMP_vars])
  subgoal premises p using p(69) by fastforce
  apply (force simp: copy_var_to_operand_aux4_state_translators Let_def)
  done

lemma copy_var_to_operand_aux4_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_var_to_operand_aux4_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
     \<lbrakk>t = (copy_var_to_operand_aux4_imp_time 0 (copy_var_to_operand_aux4_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) copy_var_to_operand_aux4_ret_str) =
        copy_var_to_operand_aux4_ret
          (copy_var_to_operand_aux4_imp (copy_var_to_operand_aux4_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_var_to_operand_aux4_IMP_Minus_correct_function 
      copy_var_to_operand_aux4_IMP_Minus_correct_time
       set_mono_prefix
  by (smt (verit, ccfv_SIG) com_add_prefix_valid_subset com_only_vars)

subsubsection copy_var_to_operand_aux5

record copy_var_to_operand_aux5_state = 
  copy_var_to_operand_aux5_acc::nat
  copy_var_to_operand_aux5_diff::nat
  copy_var_to_operand_aux5_i::nat
  copy_var_to_operand_aux5_op::nat
  copy_var_to_operand_aux5_v::nat 
  copy_var_to_operand_aux5_ret::nat

abbreviation "copy_var_to_operand_aux5_prefix \<equiv> ''copy_var_to_operand_aux5.''"
abbreviation "copy_var_to_operand_aux5_acc_str \<equiv> ''acc''"
abbreviation "copy_var_to_operand_aux5_diff_str \<equiv> ''diff''"
abbreviation "copy_var_to_operand_aux5_i_str \<equiv> ''i''"
abbreviation "copy_var_to_operand_aux5_op_str \<equiv> ''op''"
abbreviation "copy_var_to_operand_aux5_v_str \<equiv> ''v''"
abbreviation "copy_var_to_operand_aux5_ret_str \<equiv> ''ret''"

definition "copy_var_to_operand_aux5_state_upd s \<equiv>
  (let
   cons_h' = copy_var_to_operand_aux5_acc s;
   cons_t' = 0;
   cons_ret' = 0;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;

   copy_var_to_operand_aux4_diff' = copy_var_to_operand_aux5_diff s;
   copy_var_to_operand_aux4_i' = copy_var_to_operand_aux5_i s;
   copy_var_to_operand_aux4_op' = copy_var_to_operand_aux5_op s;
   copy_var_to_operand_aux4_v' = copy_var_to_operand_aux5_v s;
   copy_var_to_operand_aux4_ret' = 0;
   copy_var_to_operand_aux4_state = 
    \<lparr>copy_var_to_operand_aux4_diff = copy_var_to_operand_aux4_diff',
    copy_var_to_operand_aux4_i = copy_var_to_operand_aux4_i',
    copy_var_to_operand_aux4_op = copy_var_to_operand_aux4_op',
    copy_var_to_operand_aux4_v = copy_var_to_operand_aux4_v',
    copy_var_to_operand_aux4_ret = copy_var_to_operand_aux4_ret'\<rparr>;
  copy_var_to_operand_aux4_ret_state = copy_var_to_operand_aux4_imp copy_var_to_operand_aux4_state;

  cons_h' = copy_var_to_operand_aux4_ret copy_var_to_operand_aux4_ret_state;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = 2;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  copy_var_to_operand_aux5_ret' = cons_ret cons_ret_state;
  ret = \<lparr>copy_var_to_operand_aux5_acc = copy_var_to_operand_aux5_acc s,
        copy_var_to_operand_aux5_diff = copy_var_to_operand_aux5_diff s,
        copy_var_to_operand_aux5_i = copy_var_to_operand_aux5_i s,
        copy_var_to_operand_aux5_op = copy_var_to_operand_aux5_op s,
        copy_var_to_operand_aux5_v = copy_var_to_operand_aux5_v s,
        copy_var_to_operand_aux5_ret = copy_var_to_operand_aux5_ret'\<rparr>
  in
   ret)"

function copy_var_to_operand_aux5_imp :: 
  "copy_var_to_operand_aux5_state \<Rightarrow> copy_var_to_operand_aux5_state" where
"copy_var_to_operand_aux5_imp s = 
  (let
   ret =copy_var_to_operand_aux5_state_upd s
  in
   ret)" by simp+
  termination 
   by (relation "measure copy_var_to_operand_aux5_diff", simp)

declare copy_var_to_operand_aux5_imp.simps[simp del]

fun copy_var_to_operand_aux5 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"copy_var_to_operand_aux5 acc diff i op v = 
  (2 ## 
      (3 ## ((var_bit_to_var_tail (prod_encode (v, i - diff))) ## 0)
          ## (1 ## (operand_bit_to_var_tail (prod_encode (op, i - diff))) ## 1 ## 0)
          ## (1 ## (operand_bit_to_var_tail (prod_encode (op, i - diff))) ## 0 ## 0)
          ## 0)
        ## acc
        ## 0)"

lemma copy_var_to_operand_aux5_imp_correct:
  "copy_var_to_operand_aux5_ret (copy_var_to_operand_aux5_imp s) = 
    copy_var_to_operand_aux5 (copy_var_to_operand_aux5_acc s) (copy_var_to_operand_aux5_diff s)
     (copy_var_to_operand_aux5_i s) (copy_var_to_operand_aux5_op s) (copy_var_to_operand_aux5_v s)"
apply (subst copy_var_to_operand_aux5_imp.simps copy_var_to_operand_aux5_state_upd_def)+
apply (auto simp add: copy_var_to_operand_aux4_imp_correct cons_imp_correct Let_def)
done 

definition "copy_var_to_operand_aux5_state_upd_time t s \<equiv>
  (let
   cons_h' = copy_var_to_operand_aux5_acc s;
   t = t + 2;
   cons_t' = 0;
   t = t + 2;
   cons_ret' = 0;
   t = t + 2;
   cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
   cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

   copy_var_to_operand_aux4_diff' = copy_var_to_operand_aux5_diff s;
   t = t + 2;
   copy_var_to_operand_aux4_i' = copy_var_to_operand_aux5_i s;
   t = t + 2;
   copy_var_to_operand_aux4_op' = copy_var_to_operand_aux5_op s;
   t = t + 2;
   copy_var_to_operand_aux4_v' = copy_var_to_operand_aux5_v s;
   t = t + 2;
   copy_var_to_operand_aux4_ret' = 0;
   t = t + 2;
   copy_var_to_operand_aux4_state = 
    \<lparr>copy_var_to_operand_aux4_diff = copy_var_to_operand_aux4_diff',
    copy_var_to_operand_aux4_i = copy_var_to_operand_aux4_i',
    copy_var_to_operand_aux4_op = copy_var_to_operand_aux4_op',
    copy_var_to_operand_aux4_v = copy_var_to_operand_aux4_v',
    copy_var_to_operand_aux4_ret = copy_var_to_operand_aux4_ret'\<rparr>;
  copy_var_to_operand_aux4_ret_state = copy_var_to_operand_aux4_imp copy_var_to_operand_aux4_state;
   t = t + copy_var_to_operand_aux4_imp_time 0 copy_var_to_operand_aux4_state;

  cons_h' = copy_var_to_operand_aux4_ret copy_var_to_operand_aux4_ret_state;
   t = t + 2;
  cons_t' = cons_ret cons_ret_state;
   t = t + 2;
  cons_ret' = 0;
   t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

  cons_h' = 2;
   t = t + 2;
  cons_t' = cons_ret cons_ret_state;
   t = t + 2;
  cons_ret' = 0;
   t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
   t = t + cons_imp_time 0 cons_state;

  copy_var_to_operand_aux5_ret' = cons_ret cons_ret_state;
   t = t + 2;
  ret = \<lparr>copy_var_to_operand_aux5_acc = copy_var_to_operand_aux5_acc s,
        copy_var_to_operand_aux5_diff = copy_var_to_operand_aux5_diff s,
        copy_var_to_operand_aux5_i = copy_var_to_operand_aux5_i s,
        copy_var_to_operand_aux5_op = copy_var_to_operand_aux5_op s,
        copy_var_to_operand_aux5_v = copy_var_to_operand_aux5_v s,
        copy_var_to_operand_aux5_ret = copy_var_to_operand_aux5_ret'\<rparr>
  in
   t)"

function copy_var_to_operand_aux5_imp_time :: 
  "nat \<Rightarrow> copy_var_to_operand_aux5_state \<Rightarrow> nat" where
"copy_var_to_operand_aux5_imp_time t s = 
  (let
   ret =copy_var_to_operand_aux5_state_upd s;
   t = t + copy_var_to_operand_aux5_state_upd_time 0 s
  in
   t)" by auto
  termination 
   by (relation "measure (copy_var_to_operand_aux5_diff \<circ> snd)", simp)

declare copy_var_to_operand_aux5_imp_time.simps[simp del]

definition "copy_var_to_operand_aux5_IMP_Minus \<equiv>
  (cons_prefix @ cons_h_str) ::= A (V copy_var_to_operand_aux5_acc_str);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (copy_var_to_operand_aux4_prefix @ copy_var_to_operand_aux4_diff_str) 
    ::= A (V (copy_var_to_operand_aux5_diff_str));;
  (copy_var_to_operand_aux4_prefix @ copy_var_to_operand_aux4_i_str) 
    ::= A (V copy_var_to_operand_aux5_i_str);;
  (copy_var_to_operand_aux4_prefix @ copy_var_to_operand_aux4_op_str) 
    ::= A (V copy_var_to_operand_aux5_op_str);;
  (copy_var_to_operand_aux4_prefix @ copy_var_to_operand_aux4_v_str) 
    ::= A (V copy_var_to_operand_aux5_v_str);;
  (copy_var_to_operand_aux4_prefix @ copy_var_to_operand_aux4_ret_str) 
    ::= A (N 0);;
  invoke_subprogram copy_var_to_operand_aux4_prefix copy_var_to_operand_aux4_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (copy_var_to_operand_aux4_prefix @ copy_var_to_operand_aux4_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (N 2);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  copy_var_to_operand_aux5_ret_str ::= A (V (cons_prefix @ cons_ret_str))
"

abbreviation "copy_var_to_operand_aux5_IMP_vars\<equiv>
  {copy_var_to_operand_aux5_acc_str, copy_var_to_operand_aux5_diff_str,
  copy_var_to_operand_aux5_i_str, copy_var_to_operand_aux5_op_str,
  copy_var_to_operand_aux5_v_str, copy_var_to_operand_aux5_ret_str}"


definition "copy_var_to_operand_aux5_imp_to_HOL_state p s =
  \<lparr>copy_var_to_operand_aux5_acc = (s (add_prefix p copy_var_to_operand_aux5_acc_str)),
  copy_var_to_operand_aux5_diff = (s (add_prefix p copy_var_to_operand_aux5_diff_str)),
  copy_var_to_operand_aux5_i = (s (add_prefix p copy_var_to_operand_aux5_i_str)),
  copy_var_to_operand_aux5_op = (s (add_prefix p copy_var_to_operand_aux5_op_str)),
  copy_var_to_operand_aux5_v = (s (add_prefix p copy_var_to_operand_aux5_v_str)),
  copy_var_to_operand_aux5_ret = (s (add_prefix p copy_var_to_operand_aux5_ret_str))\<rparr>"

lemmas copy_var_to_operand_aux5_state_translators =
  copy_var_to_operand_aux5_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  copy_var_to_operand_aux4_imp_to_HOL_state_def

lemma copy_var_to_operand_aux5_IMP_Minus_correct_function:
  "(invoke_subprogram p copy_var_to_operand_aux5_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_var_to_operand_aux5_ret_str)
      = copy_var_to_operand_aux5_ret
          (copy_var_to_operand_aux5_imp (copy_var_to_operand_aux5_imp_to_HOL_state p s))"
  apply (simp only: copy_var_to_operand_aux5_imp.simps copy_var_to_operand_aux5_state_upd_def)
  apply (simp only: copy_var_to_operand_aux5_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux5_IMP_vars])
  subgoal premises p using p(19) by fastforce
  apply (erule copy_var_to_operand_aux4_IMP_Minus_correct[where 
         vars="copy_var_to_operand_aux5_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
  subgoal premises p using p(21) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux5_IMP_vars])
  subgoal premises p using p(23) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux5_IMP_vars])
  subgoal premises p using p(25) by fastforce
  apply (force simp: Let_def copy_var_to_operand_aux5_state_translators)
  done 

lemma copy_var_to_operand_aux5_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ copy_var_to_operand_aux5_pref) copy_var_to_operand_aux5_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix copy_var_to_operand_aux5_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemma copy_var_to_operand_aux5_IMP_Minus_correct_time:
  "(invoke_subprogram p copy_var_to_operand_aux5_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = copy_var_to_operand_aux5_imp_time 0 (copy_var_to_operand_aux5_imp_to_HOL_state p s)"
  apply (simp only: copy_var_to_operand_aux5_imp_time.simps copy_var_to_operand_aux5_state_upd_time_def)
  apply (simp only: copy_var_to_operand_aux5_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux5_IMP_vars])
  subgoal premises p using p(37) by fastforce
  apply (erule copy_var_to_operand_aux4_IMP_Minus_correct[where 
         vars="copy_var_to_operand_aux5_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
  subgoal premises p using p(39) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux5_IMP_vars])
  subgoal premises p using p(41) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_aux5_IMP_vars])
  subgoal premises p using p(43) by fastforce
  apply (force simp: Let_def copy_var_to_operand_aux5_state_translators)
  done 

lemma copy_var_to_operand_aux5_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_var_to_operand_aux5_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (copy_var_to_operand_aux5_imp_time 0 (copy_var_to_operand_aux5_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) copy_var_to_operand_aux5_ret_str) =
          copy_var_to_operand_aux5_ret (copy_var_to_operand_aux5_imp
                                        (copy_var_to_operand_aux5_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_var_to_operand_aux5_IMP_Minus_correct_function
  by (auto simp: copy_var_to_operand_aux5_IMP_Minus_correct_time)
    (meson copy_var_to_operand_aux5_IMP_Minus_correct_effects set_mono_prefix)

subsubsection copy_var_to_operand_acc

record copy_var_to_operand_acc_state =
  copy_var_to_operand_acc_acc::nat
  copy_var_to_operand_acc_diff::nat
  copy_var_to_operand_acc_i::nat
  copy_var_to_operand_acc_op::nat
  copy_var_to_operand_acc_v::nat 
  copy_var_to_operand_acc_ret::nat

abbreviation "copy_var_to_operand_acc_prefix \<equiv> ''copy_var_to_operand_acc.''"
abbreviation "copy_var_to_operand_acc_acc_str \<equiv> ''acc''"
abbreviation "copy_var_to_operand_acc_diff_str \<equiv> ''diff''"
abbreviation "copy_var_to_operand_acc_i_str \<equiv> ''i''"
abbreviation "copy_var_to_operand_acc_op_str \<equiv> ''op''"
abbreviation "copy_var_to_operand_acc_v_str \<equiv> ''v''"
abbreviation "copy_var_to_operand_acc_ret_str \<equiv> ''ret''"

definition "copy_var_to_operand_acc_state_upd s \<equiv>
  (let 
   copy_var_to_operand_aux5_acc' = copy_var_to_operand_acc_acc s;
   copy_var_to_operand_aux5_diff' = copy_var_to_operand_acc_diff s;
   copy_var_to_operand_aux5_i' = copy_var_to_operand_acc_i s;
   copy_var_to_operand_aux5_op' = copy_var_to_operand_acc_op s;
   copy_var_to_operand_aux5_v' = copy_var_to_operand_acc_v s;
   copy_var_to_operand_aux5_ret' = 0;
   copy_var_to_operand_aux5_state = 
    \<lparr>copy_var_to_operand_aux5_acc = copy_var_to_operand_aux5_acc',
    copy_var_to_operand_aux5_diff = copy_var_to_operand_aux5_diff',
    copy_var_to_operand_aux5_i = copy_var_to_operand_aux5_i',
    copy_var_to_operand_aux5_op = copy_var_to_operand_aux5_op',
    copy_var_to_operand_aux5_v = copy_var_to_operand_aux5_v',
    copy_var_to_operand_aux5_ret = copy_var_to_operand_aux5_ret'\<rparr>;
  copy_var_to_operand_aux5_ret_state = copy_var_to_operand_aux5_imp copy_var_to_operand_aux5_state;

  copy_var_to_operand_acc_acc' = copy_var_to_operand_aux5_ret copy_var_to_operand_aux5_ret_state;
  copy_var_to_operand_acc_diff' = copy_var_to_operand_acc_diff s - 1;
  ret = \<lparr>copy_var_to_operand_acc_acc = copy_var_to_operand_acc_acc',
        copy_var_to_operand_acc_diff = copy_var_to_operand_acc_diff',
        copy_var_to_operand_acc_i = copy_var_to_operand_acc_i s,
        copy_var_to_operand_acc_op = copy_var_to_operand_acc_op s,
        copy_var_to_operand_acc_v = copy_var_to_operand_acc_v s,
        copy_var_to_operand_acc_ret = copy_var_to_operand_acc_ret s\<rparr>
  in
   ret)"


definition "copy_var_to_operand_acc_imp_compute_loop_condition s \<equiv> 
 (let
  condition = copy_var_to_operand_acc_diff s
 in 
  condition)"

definition "copy_var_to_operand_acc_imp_after_loop s \<equiv> 
 (let 
  copy_var_to_operand_acc_ret' = copy_var_to_operand_acc_acc s;
  ret = \<lparr>copy_var_to_operand_acc_acc = copy_var_to_operand_acc_acc s,
        copy_var_to_operand_acc_diff = copy_var_to_operand_acc_diff s,
        copy_var_to_operand_acc_i = copy_var_to_operand_acc_i s,
        copy_var_to_operand_acc_op = copy_var_to_operand_acc_op s,
        copy_var_to_operand_acc_v = copy_var_to_operand_acc_v s,
        copy_var_to_operand_acc_ret = copy_var_to_operand_acc_ret'\<rparr>
 in
  ret)"

lemmas copy_var_to_operand_acc_imp_subprogram_simps = 
  copy_var_to_operand_acc_state_upd_def
  copy_var_to_operand_acc_imp_compute_loop_condition_def
  copy_var_to_operand_acc_imp_after_loop_def

function copy_var_to_operand_acc_imp::
  "copy_var_to_operand_acc_state \<Rightarrow> copy_var_to_operand_acc_state" where
  "copy_var_to_operand_acc_imp s =
  (if copy_var_to_operand_acc_imp_compute_loop_condition s \<noteq> 0
   then
    let next_iteration = copy_var_to_operand_acc_imp (copy_var_to_operand_acc_state_upd s)
    in next_iteration
   else
    let ret = copy_var_to_operand_acc_imp_after_loop s
    in ret
  )"
  by simp+
termination
  apply (relation "measure copy_var_to_operand_acc_diff")
  apply (simp add: copy_var_to_operand_acc_imp_subprogram_simps)+
  done

declare copy_var_to_operand_acc_imp.simps [simp del]

lemma copy_var_to_operand_acc_imp_correct:
  "copy_var_to_operand_acc_ret (copy_var_to_operand_acc_imp s) =
    copy_var_to_operand_acc (copy_var_to_operand_acc_acc s) 
    (copy_var_to_operand_acc_diff s) (copy_var_to_operand_acc_i s)
    (copy_var_to_operand_acc_op s) (copy_var_to_operand_acc_v s)"
  apply (induction s rule: copy_var_to_operand_acc_imp.induct)
  apply (subst copy_var_to_operand_acc_imp.simps)
  apply (subst copy_var_to_operand_acc.simps)
  apply (auto simp del: copy_var_to_operand_acc.simps simp add: 
  copy_var_to_operand_acc_imp_subprogram_simps Let_def
  copy_var_to_operand_aux5_imp_correct)
  done            


definition "copy_var_to_operand_acc_state_upd_time t s \<equiv>
  (let
   copy_var_to_operand_aux5_acc' = copy_var_to_operand_acc_acc s;
   t = t + 2;
   copy_var_to_operand_aux5_diff' = copy_var_to_operand_acc_diff s;
   t = t + 2;
   copy_var_to_operand_aux5_i' = copy_var_to_operand_acc_i s;
   t = t + 2;
   copy_var_to_operand_aux5_op' = copy_var_to_operand_acc_op s;
   t = t + 2;
   copy_var_to_operand_aux5_v' = copy_var_to_operand_acc_v s;
   t = t + 2;
   copy_var_to_operand_aux5_ret' = 0;
   t = t + 2;
   copy_var_to_operand_aux5_state = 
    \<lparr>copy_var_to_operand_aux5_acc = copy_var_to_operand_aux5_acc',
    copy_var_to_operand_aux5_diff = copy_var_to_operand_aux5_diff',
    copy_var_to_operand_aux5_i = copy_var_to_operand_aux5_i',
    copy_var_to_operand_aux5_op = copy_var_to_operand_aux5_op',
    copy_var_to_operand_aux5_v = copy_var_to_operand_aux5_v',
    copy_var_to_operand_aux5_ret = copy_var_to_operand_aux5_ret'\<rparr>;
  copy_var_to_operand_aux5_ret_state = copy_var_to_operand_aux5_imp copy_var_to_operand_aux5_state;
   t = t + copy_var_to_operand_aux5_imp_time 0 copy_var_to_operand_aux5_state;

  copy_var_to_operand_acc_acc' = copy_var_to_operand_aux5_ret copy_var_to_operand_aux5_ret_state;
  t = t + 2;
  copy_var_to_operand_acc_diff' = copy_var_to_operand_acc_diff s - 1;
    t = t + 2;
  ret = \<lparr>copy_var_to_operand_acc_acc = copy_var_to_operand_acc_acc',
        copy_var_to_operand_acc_diff = copy_var_to_operand_acc_diff',
        copy_var_to_operand_acc_i = copy_var_to_operand_acc_i s,
        copy_var_to_operand_acc_op = copy_var_to_operand_acc_op s,
        copy_var_to_operand_acc_v = copy_var_to_operand_acc_v s,
        copy_var_to_operand_acc_ret = copy_var_to_operand_acc_ret s\<rparr>
  in
   t)"

definition "copy_var_to_operand_acc_imp_compute_loop_condition_time t s \<equiv>
  let
  condition = copy_var_to_operand_acc_diff s;
  t = t + 2
  in
    t
"

definition "copy_var_to_operand_acc_imp_after_loop_time t s \<equiv>
  (let
    copy_var_to_operand_acc_ret' = copy_var_to_operand_acc_acc s;
    t = t + 2;
    ret = \<lparr>copy_var_to_operand_acc_acc = copy_var_to_operand_acc_acc s,
        copy_var_to_operand_acc_diff = copy_var_to_operand_acc_diff s,
        copy_var_to_operand_acc_i = copy_var_to_operand_acc_i s,
        copy_var_to_operand_acc_op = copy_var_to_operand_acc_op s,
        copy_var_to_operand_acc_v = copy_var_to_operand_acc_v s,
        copy_var_to_operand_acc_ret = copy_var_to_operand_acc_ret'\<rparr>
  in
    t)
"

lemmas copy_var_to_operand_acc_imp_subprogram_time_simps = 
  copy_var_to_operand_acc_state_upd_time_def
  copy_var_to_operand_acc_imp_compute_loop_condition_time_def
  copy_var_to_operand_acc_imp_after_loop_time_def
  copy_var_to_operand_acc_imp_subprogram_simps

function copy_var_to_operand_acc_imp_time::
  "nat \<Rightarrow> copy_var_to_operand_acc_state \<Rightarrow> nat" where
  "copy_var_to_operand_acc_imp_time t s =
  copy_var_to_operand_acc_imp_compute_loop_condition_time 0 s +
  (if copy_var_to_operand_acc_imp_compute_loop_condition s \<noteq> 0
    then
      (let
        t = t + 1;
        next_iteration =
          copy_var_to_operand_acc_imp_time (t + copy_var_to_operand_acc_state_upd_time 0 s)
                         (copy_var_to_operand_acc_state_upd s)
       in next_iteration)
    else
      (let
        t = t + 2;
        ret = t + copy_var_to_operand_acc_imp_after_loop_time 0 s
       in ret)
  )"
  by auto
termination
  apply (relation "measure (copy_var_to_operand_acc_diff \<circ> snd)")
  by (simp add: copy_var_to_operand_acc_imp_subprogram_time_simps)+

declare copy_var_to_operand_acc_imp_time.simps [simp del]            

lemma copy_var_to_operand_acc_imp_time_acc:
  "(copy_var_to_operand_acc_imp_time (Suc t) s) = Suc (copy_var_to_operand_acc_imp_time t s)"
  by (induction t s rule: copy_var_to_operand_acc_imp_time.induct)
    ((subst (1 2) copy_var_to_operand_acc_imp_time.simps);
      (simp add: copy_var_to_operand_acc_state_upd_def))            

lemma copy_var_to_operand_acc_imp_time_acc_2_aux:
  "(copy_var_to_operand_acc_imp_time t s) = t + (copy_var_to_operand_acc_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: copy_var_to_operand_acc_imp_time_acc)+            

lemma copy_var_to_operand_acc_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (copy_var_to_operand_acc_imp_time t s) = t + (copy_var_to_operand_acc_imp_time 0 s)"
  by (rule copy_var_to_operand_acc_imp_time_acc_2_aux)            

lemma copy_var_to_operand_acc_imp_time_acc_3:
  "(copy_var_to_operand_acc_imp_time (a + b) s) = a + (copy_var_to_operand_acc_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: copy_var_to_operand_acc_imp_time_acc)+            

abbreviation "copy_var_to_operand_acc_while_cond \<equiv> ''condition''"

definition "copy_var_to_operand_acc_IMP_init_while_cond \<equiv>
  copy_var_to_operand_acc_while_cond ::= A (V copy_var_to_operand_acc_diff_str)
"

definition "copy_var_to_operand_acc_IMP_loop_body \<equiv>
  (copy_var_to_operand_aux5_prefix @ copy_var_to_operand_aux5_acc_str) 
    ::= A (V (copy_var_to_operand_acc_acc_str));;
  (copy_var_to_operand_aux5_prefix @ copy_var_to_operand_aux5_diff_str) 
    ::= A (V (copy_var_to_operand_acc_diff_str));;
  (copy_var_to_operand_aux5_prefix @ copy_var_to_operand_aux5_i_str) 
    ::= A (V copy_var_to_operand_acc_i_str);;
  (copy_var_to_operand_aux5_prefix @ copy_var_to_operand_aux5_op_str) 
    ::= A (V copy_var_to_operand_acc_op_str);;
  (copy_var_to_operand_aux5_prefix @ copy_var_to_operand_aux5_v_str) 
    ::= A (V copy_var_to_operand_acc_v_str);;
  (copy_var_to_operand_aux5_prefix @ copy_var_to_operand_aux5_ret_str) 
    ::= A (N 0);;
  invoke_subprogram copy_var_to_operand_aux5_prefix copy_var_to_operand_aux5_IMP_Minus;;

  copy_var_to_operand_acc_acc_str ::= A (V (copy_var_to_operand_aux5_prefix @ copy_var_to_operand_aux5_ret_str) );;
  copy_var_to_operand_acc_diff_str ::= Sub (V copy_var_to_operand_acc_diff_str) (N 1)
"

definition "copy_var_to_operand_acc_IMP_after_loop \<equiv>
  copy_var_to_operand_acc_ret_str ::= A (V copy_var_to_operand_acc_acc_str)
"

definition copy_var_to_operand_acc_IMP_Minus where
  "copy_var_to_operand_acc_IMP_Minus \<equiv>
  copy_var_to_operand_acc_IMP_init_while_cond;;
  WHILE copy_var_to_operand_acc_while_cond \<noteq>0 DO (
    copy_var_to_operand_acc_IMP_loop_body;;
    copy_var_to_operand_acc_IMP_init_while_cond
  );;
  copy_var_to_operand_acc_IMP_after_loop"

abbreviation "copy_var_to_operand_acc_IMP_vars\<equiv>
  {copy_var_to_operand_acc_acc_str, copy_var_to_operand_acc_diff_str,
  copy_var_to_operand_acc_i_str, copy_var_to_operand_acc_op_str,
  copy_var_to_operand_acc_v_str, copy_var_to_operand_acc_ret_str,
  copy_var_to_operand_acc_while_cond}"

lemmas copy_var_to_operand_acc_IMP_subprogram_simps =
  copy_var_to_operand_acc_IMP_init_while_cond_def
  copy_var_to_operand_acc_IMP_loop_body_def
  copy_var_to_operand_acc_IMP_after_loop_def

definition "copy_var_to_operand_acc_imp_to_HOL_state p s =
  \<lparr>copy_var_to_operand_acc_acc = (s (add_prefix p copy_var_to_operand_acc_acc_str)),
  copy_var_to_operand_acc_diff = (s (add_prefix p copy_var_to_operand_acc_diff_str)),
  copy_var_to_operand_acc_i = (s (add_prefix p copy_var_to_operand_acc_i_str)),
  copy_var_to_operand_acc_op = (s (add_prefix p copy_var_to_operand_acc_op_str)),
  copy_var_to_operand_acc_v = (s (add_prefix p copy_var_to_operand_acc_v_str)),
  copy_var_to_operand_acc_ret = (s (add_prefix p copy_var_to_operand_acc_ret_str))\<rparr>"

lemmas copy_var_to_operand_acc_state_translators =
  copy_var_to_operand_acc_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  copy_var_to_operand_aux5_imp_to_HOL_state_def

lemmas copy_var_to_operand_acc_complete_simps =
  copy_var_to_operand_acc_IMP_subprogram_simps
  copy_var_to_operand_acc_imp_subprogram_simps
  copy_var_to_operand_acc_state_translators

lemma copy_var_to_operand_acc_IMP_Minus_correct_function:
  "(invoke_subprogram p copy_var_to_operand_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_var_to_operand_acc_ret_str)
      = copy_var_to_operand_acc_ret
          (copy_var_to_operand_acc_imp (copy_var_to_operand_acc_imp_to_HOL_state p s))"
  apply(induction "copy_var_to_operand_acc_imp_to_HOL_state p s" arbitrary: s s' t
    rule: copy_var_to_operand_acc_imp.induct)
  apply(subst copy_var_to_operand_acc_imp.simps)
  apply(simp only: copy_var_to_operand_acc_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule While_tE)

  subgoal
    apply(simp only: copy_var_to_operand_acc_IMP_subprogram_simps prefix_simps)
    by(fastforce simp: copy_var_to_operand_acc_IMP_subprogram_simps
        copy_var_to_operand_acc_imp_subprogram_simps
        copy_var_to_operand_acc_state_translators)

  apply(erule Seq_E)+
  apply(dest_com_gen)

  subgoal
      apply(simp only: copy_var_to_operand_acc_IMP_init_while_cond_def prefix_simps)
      by(fastforce simp add: copy_var_to_operand_acc_complete_simps)

  subgoal
      apply(subst (asm) copy_var_to_operand_acc_IMP_init_while_cond_def)
      apply(simp only: copy_var_to_operand_acc_IMP_loop_body_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule copy_var_to_operand_aux5_IMP_Minus_correct[where vars = copy_var_to_operand_acc_IMP_vars])
      subgoal premises p using p(14) by fastforce
      by (force simp: copy_var_to_operand_acc_imp_subprogram_simps
          copy_var_to_operand_acc_state_translators Let_def)

  subgoal
      apply(simp only: copy_var_to_operand_acc_IMP_init_while_cond_def prefix_simps
          copy_var_to_operand_acc_IMP_loop_body_def)
      apply(erule Seq_E)+
      apply(erule copy_var_to_operand_aux5_IMP_Minus_correct[where vars = copy_var_to_operand_acc_IMP_vars])
      subgoal premises p using p(14) by fastforce
      by (force simp: copy_var_to_operand_acc_imp_subprogram_simps
          copy_var_to_operand_acc_state_translators Let_def)
  done        

lemma copy_var_to_operand_acc_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ copy_var_to_operand_acc_pref) copy_var_to_operand_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix copy_var_to_operand_acc_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemmas copy_var_to_operand_acc_complete_time_simps =
  copy_var_to_operand_acc_imp_subprogram_time_simps
  copy_var_to_operand_acc_imp_time_acc_2
  copy_var_to_operand_acc_imp_time_acc_3
  copy_var_to_operand_acc_state_translators

lemma copy_var_to_operand_acc_IMP_Minus_correct_time:
  "(invoke_subprogram p copy_var_to_operand_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = copy_var_to_operand_acc_imp_time 0 (copy_var_to_operand_acc_imp_to_HOL_state p s)"
  apply(induction "copy_var_to_operand_acc_imp_to_HOL_state p s" arbitrary: s s' t
      rule: copy_var_to_operand_acc_imp.induct)
  apply(subst copy_var_to_operand_acc_imp_time.simps)
  apply(simp only: copy_var_to_operand_acc_IMP_Minus_def prefix_simps)

  apply(erule Seq_tE)+
  apply(erule While_tE_time)

  subgoal
    apply(simp only: copy_var_to_operand_acc_IMP_subprogram_simps prefix_simps)
    by (force simp: copy_var_to_operand_acc_IMP_subprogram_simps
        copy_var_to_operand_acc_imp_subprogram_time_simps copy_var_to_operand_acc_state_translators)

  apply(erule Seq_tE)+
  apply(simp add: add.assoc)
  apply(dest_com_gen_time)

  subgoal
    apply(simp only: copy_var_to_operand_acc_IMP_init_while_cond_def prefix_simps)
    by(fastforce simp add: copy_var_to_operand_acc_complete_simps)

  subgoal
    apply(subst (asm) copy_var_to_operand_acc_IMP_init_while_cond_def)
    apply(simp only: copy_var_to_operand_acc_IMP_loop_body_def prefix_simps)
    apply(erule Seq_tE)+
    apply(erule copy_var_to_operand_aux5_IMP_Minus_correct[where vars = copy_var_to_operand_acc_IMP_vars])
    subgoal premises p using p(25) by fastforce
    by (force simp: copy_var_to_operand_acc_imp_subprogram_simps
          copy_var_to_operand_acc_state_translators Let_def)

  subgoal
    apply(simp only: prefix_simps copy_var_to_operand_acc_IMP_init_while_cond_def
        copy_var_to_operand_acc_IMP_loop_body_def)
    apply(erule Seq_tE)+
    apply(erule copy_var_to_operand_aux5_IMP_Minus_correct[where vars = copy_var_to_operand_acc_IMP_vars])
    subgoal premises p using p(25) by fastforce
    apply (force simp: copy_var_to_operand_acc_complete_time_simps Let_def)
    done      
  done        

lemma copy_var_to_operand_acc_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_var_to_operand_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (copy_var_to_operand_acc_imp_time 0 (copy_var_to_operand_acc_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) copy_var_to_operand_acc_ret_str) =
          copy_var_to_operand_acc_ret (copy_var_to_operand_acc_imp
                                        (copy_var_to_operand_acc_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_var_to_operand_acc_IMP_Minus_correct_function
  by (auto simp: copy_var_to_operand_acc_IMP_Minus_correct_time)
    (meson copy_var_to_operand_acc_IMP_Minus_correct_effects set_mono_prefix) 

subsubsection copy_var_to_operand_tail 

record copy_var_to_operand_tail_state =
  copy_var_to_operand_tail_i::nat
  copy_var_to_operand_tail_op::nat 
  copy_var_to_operand_tail_v::nat
  copy_var_to_operand_tail_ret::nat

abbreviation "copy_var_to_operand_tail_prefix \<equiv> ''copy_var_to_operand_tail.''"
abbreviation "copy_var_to_operand_tail_i_str \<equiv> ''i''"
abbreviation "copy_var_to_operand_tail_op_str \<equiv> ''op''"
abbreviation "copy_var_to_operand_tail_v_str \<equiv> ''v''"
abbreviation "copy_var_to_operand_tail_ret_str \<equiv> ''ret''"

definition "copy_var_to_operand_tail_state_upd s \<equiv> 
(let
  cons_h' = 0;
  cons_t' = 0;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  copy_var_to_operand_acc_acc' = cons_ret cons_ret_state;
  copy_var_to_operand_acc_diff' = copy_var_to_operand_tail_i s;
  copy_var_to_operand_acc_i' = copy_var_to_operand_tail_i s;
  copy_var_to_operand_acc_op' = copy_var_to_operand_tail_op s;
  copy_var_to_operand_acc_v' = copy_var_to_operand_tail_v s;
  copy_var_to_operand_acc_ret' = 0;
  copy_var_to_operand_acc_state = 
    \<lparr>copy_var_to_operand_acc_acc = copy_var_to_operand_acc_acc',
    copy_var_to_operand_acc_diff = copy_var_to_operand_acc_diff',
    copy_var_to_operand_acc_i = copy_var_to_operand_acc_i',
    copy_var_to_operand_acc_op = copy_var_to_operand_acc_op',
    copy_var_to_operand_acc_v = copy_var_to_operand_acc_v',
    copy_var_to_operand_acc_ret = copy_var_to_operand_acc_ret'\<rparr>;
  copy_var_to_operand_acc_ret_state = copy_var_to_operand_acc_imp copy_var_to_operand_acc_state;

  copy_var_to_operand_tail_ret' = copy_var_to_operand_acc_ret copy_var_to_operand_acc_ret_state;
  ret = 
    \<lparr>copy_var_to_operand_tail_i = copy_var_to_operand_tail_i s,
    copy_var_to_operand_tail_op = copy_var_to_operand_tail_op s,
    copy_var_to_operand_tail_v = copy_var_to_operand_tail_v s,
    copy_var_to_operand_tail_ret = copy_var_to_operand_tail_ret'\<rparr>
  in 
   ret)"

function copy_var_to_operand_tail_imp 
 :: "copy_var_to_operand_tail_state \<Rightarrow> copy_var_to_operand_tail_state" where 
"copy_var_to_operand_tail_imp s = 
 (let
   ret = copy_var_to_operand_tail_state_upd s
  in
   ret)" by simp+
  termination by (relation "measure copy_var_to_operand_tail_i", simp)

declare copy_var_to_operand_tail_imp.simps[simp del]

lemma copy_var_to_operand_tail_imp_correct:
  "copy_var_to_operand_tail_ret (copy_var_to_operand_tail_imp s) =
    copy_var_to_operand_tail (copy_var_to_operand_tail_i s) 
     (copy_var_to_operand_tail_op s) (copy_var_to_operand_tail_v s)"
apply (simp only: copy_var_to_operand_tail_imp.simps copy_var_to_operand_tail_state_upd_def)
apply (simp add: copy_var_to_operand_acc_imp_correct cons_imp_correct 
      Let_def copy_var_to_operand_tail_def)
done 

definition "copy_var_to_operand_tail_state_upd_time t s \<equiv> 
(let
  cons_h' = 0;
  t = t + 2;
  cons_t' = 0;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  copy_var_to_operand_acc_acc' = cons_ret cons_ret_state;
  t = t + 2;
  t = t + 2;
  copy_var_to_operand_acc_diff' = copy_var_to_operand_tail_i s;
  copy_var_to_operand_acc_i' = copy_var_to_operand_tail_i s;
  t = t + 2;
  copy_var_to_operand_acc_op' = copy_var_to_operand_tail_op s;
  t = t + 2;
  copy_var_to_operand_acc_v' = copy_var_to_operand_tail_v s;
  t = t + 2;
  copy_var_to_operand_acc_ret' = 0;
  t = t + 2;
  copy_var_to_operand_acc_state = 
    \<lparr>copy_var_to_operand_acc_acc = copy_var_to_operand_acc_acc',
    copy_var_to_operand_acc_diff = copy_var_to_operand_acc_diff',
    copy_var_to_operand_acc_i = copy_var_to_operand_acc_i',
    copy_var_to_operand_acc_op = copy_var_to_operand_acc_op',
    copy_var_to_operand_acc_v = copy_var_to_operand_acc_v',
    copy_var_to_operand_acc_ret = copy_var_to_operand_acc_ret'\<rparr>;
  copy_var_to_operand_acc_ret_state = copy_var_to_operand_acc_imp copy_var_to_operand_acc_state;
  t = t + copy_var_to_operand_acc_imp_time 0 copy_var_to_operand_acc_state;

  copy_var_to_operand_tail_ret' = copy_var_to_operand_acc_ret copy_var_to_operand_acc_ret_state;
  t = t + 2;
  ret = 
    \<lparr>copy_var_to_operand_tail_i = copy_var_to_operand_tail_i s,
    copy_var_to_operand_tail_op = copy_var_to_operand_tail_op s,
    copy_var_to_operand_tail_v = copy_var_to_operand_tail_v s,
    copy_var_to_operand_tail_ret = copy_var_to_operand_tail_ret'\<rparr>
  in 
   t)"

function copy_var_to_operand_tail_imp_time 
 :: "nat \<Rightarrow> copy_var_to_operand_tail_state \<Rightarrow> nat" where 
"copy_var_to_operand_tail_imp_time t s = 
 (let
   ret = copy_var_to_operand_tail_state_upd s;
   t = t + copy_var_to_operand_tail_state_upd_time 0 s
  in
   t)" by auto
  termination by (relation "measure (copy_var_to_operand_tail_i \<circ> snd)", simp)

declare copy_var_to_operand_tail_imp_time.simps[simp del]

abbreviation "copy_var_to_operand_tail_IMP_vars \<equiv> 
  {copy_var_to_operand_tail_i_str, copy_var_to_operand_tail_op_str, 
  copy_var_to_operand_tail_v_str, copy_var_to_operand_tail_ret_str}"

definition "copy_var_to_operand_tail_imp_to_HOL_state p s \<equiv>
  \<lparr>copy_var_to_operand_tail_i = s (add_prefix p copy_var_to_operand_tail_i_str),
  copy_var_to_operand_tail_op = s (add_prefix p copy_var_to_operand_tail_op_str),
  copy_var_to_operand_tail_v = s (add_prefix p copy_var_to_operand_tail_v_str),
  copy_var_to_operand_tail_ret = s (add_prefix p copy_var_to_operand_tail_ret_str)\<rparr>"

definition "copy_var_to_operand_tail_IMP_Minus \<equiv> 
  (cons_prefix @ cons_h_str) ::= A (N 0);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (copy_var_to_operand_acc_prefix @ copy_var_to_operand_acc_acc_str)
    ::= A (V (cons_prefix @ cons_ret_str));;
  (copy_var_to_operand_acc_prefix @ copy_var_to_operand_acc_diff_str)
    ::= A (V copy_var_to_operand_tail_i_str);;
  (copy_var_to_operand_acc_prefix @ copy_var_to_operand_acc_i_str)
    ::= A (V copy_var_to_operand_tail_i_str);;
  (copy_var_to_operand_acc_prefix @ copy_var_to_operand_acc_op_str)
    ::= A (V copy_var_to_operand_tail_op_str);;
  (copy_var_to_operand_acc_prefix @ copy_var_to_operand_acc_v_str)
    ::= A (V copy_var_to_operand_tail_v_str);;
  (copy_var_to_operand_acc_prefix @ copy_var_to_operand_acc_ret_str)
    ::= A (N 0);;
  invoke_subprogram  copy_var_to_operand_acc_prefix  copy_var_to_operand_acc_IMP_Minus;;
  
  copy_var_to_operand_tail_ret_str 
    ::= A (V (copy_var_to_operand_acc_prefix @ copy_var_to_operand_acc_ret_str))
    
  "

lemmas copy_var_to_operand_tail_state_translators=
  copy_var_to_operand_tail_imp_to_HOL_state_def
  copy_var_to_operand_acc_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def

lemma copy_var_to_operand_tail_IMP_Minus_correct_function:
  "(invoke_subprogram p copy_var_to_operand_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_var_to_operand_tail_ret_str)
      = copy_var_to_operand_tail_ret
          (copy_var_to_operand_tail_imp (copy_var_to_operand_tail_imp_to_HOL_state p s))"
apply (simp only: copy_var_to_operand_tail_imp.simps copy_var_to_operand_tail_state_upd_def)
apply (simp only: copy_var_to_operand_tail_IMP_Minus_def prefix_simps)
apply (erule Seq_E)+
apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_tail_IMP_vars])
subgoal premises p using p(12) by fastforce
apply (erule copy_var_to_operand_acc_IMP_Minus_correct[where vars=copy_var_to_operand_tail_IMP_vars])
subgoal premises p using p(14) by fastforce
apply (force simp add: copy_var_to_operand_tail_state_translators Let_def)
done 

lemma copy_var_to_operand_tail_IMP_Minus_correct_time:
  "(invoke_subprogram p copy_var_to_operand_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (copy_var_to_operand_tail_imp_time 0 (copy_var_to_operand_tail_imp_to_HOL_state p s))"
apply (simp only: copy_var_to_operand_tail_imp_time.simps copy_var_to_operand_tail_state_upd_time_def)
apply (simp only: copy_var_to_operand_tail_IMP_Minus_def prefix_simps)
apply (erule Seq_tE)+
apply (erule cons_IMP_Minus_correct[where vars=copy_var_to_operand_tail_IMP_vars])
subgoal premises p using p(23) by fastforce
apply (erule copy_var_to_operand_acc_IMP_Minus_correct[where vars=copy_var_to_operand_tail_IMP_vars])
subgoal premises p using p(25) by fastforce
apply (force simp add: copy_var_to_operand_tail_state_translators Let_def)
done 

lemma copy_var_to_operand_tail_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ copy_var_to_operand_tail_pref) copy_var_to_operand_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix copy_var_to_operand_tail_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma copy_var_to_operand_tail_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_var_to_operand_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (copy_var_to_operand_tail_imp_time 0 (copy_var_to_operand_tail_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) copy_var_to_operand_tail_ret_str) =
          copy_var_to_operand_tail_ret (copy_var_to_operand_tail_imp
                                        (copy_var_to_operand_tail_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_var_to_operand_tail_IMP_Minus_correct_function
  by (auto simp: copy_var_to_operand_tail_IMP_Minus_correct_time)
    (meson copy_var_to_operand_tail_IMP_Minus_correct_effects set_mono_prefix) 

subsection copy_const_to_operand

subsubsection copy_const_to_operand_aux1

record copy_const_to_operand_aux1_state =
  copy_const_to_operand_aux1_x::nat
  copy_const_to_operand_aux1_diff::nat
  copy_const_to_operand_aux1_op::nat
  copy_const_to_operand_aux1_ret::nat

abbreviation "copy_const_to_operand_aux1_prefix \<equiv> ''copy_const_to_operand_aux1.''"
abbreviation "copy_const_to_operand_aux1_x_str \<equiv> ''x''"
abbreviation "copy_const_to_operand_aux1_diff_str \<equiv> ''diff''"
abbreviation "copy_const_to_operand_aux1_op_str \<equiv> ''op''"
abbreviation "copy_const_to_operand_aux1_ret_str \<equiv> ''ret''"

definition "copy_const_to_operand_aux1_imp s \<equiv> 
(let
  nth_bit_tail_acc' = copy_const_to_operand_aux1_x s;
  nth_bit_tail_n' = copy_const_to_operand_aux1_diff s;
  nth_bit_tail_ret' = 0;
  nth_bit_tail_state = \<lparr>nth_bit_tail_acc = nth_bit_tail_acc',
                        nth_bit_tail_n = nth_bit_tail_n',
                        nth_bit_tail_ret = nth_bit_tail_ret'\<rparr>;
  nth_bit_tail_ret_state = nth_bit_tail_imp nth_bit_tail_state;

  cons_h' = nth_bit_tail_ret nth_bit_tail_ret_state;
  cons_t' = 0;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  prod_encode_a' = copy_const_to_operand_aux1_op s;
  prod_encode_b' = copy_const_to_operand_aux1_diff s;
  prod_encode_ret' = 0;
  prod_encode_state = \<lparr>prod_encode_a = prod_encode_a', 
                       prod_encode_b = prod_encode_b',
                       prod_encode_ret = prod_encode_ret'\<rparr>;
  prod_encode_ret_state = prod_encode_imp prod_encode_state;

  operand_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
  operand_bit_to_var_tail_ret' = 0;
  operand_bit_to_var_tail_state = 
    \<lparr>operand_bit_to_var_tail_n = operand_bit_to_var_tail_n',
    operand_bit_to_var_tail_ret = operand_bit_to_var_tail_ret'\<rparr>;
  operand_bit_to_var_tail_ret_state 
    = operand_bit_to_var_tail_imp operand_bit_to_var_tail_state;

  cons_h' = operand_bit_to_var_tail_ret operand_bit_to_var_tail_ret_state;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp  cons_state;

  cons_h' = 1;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp  cons_state;

  copy_const_to_operand_aux1_ret' = cons_ret cons_ret_state;
  ret = \<lparr>copy_const_to_operand_aux1_x = copy_const_to_operand_aux1_x s,
        copy_const_to_operand_aux1_diff = copy_const_to_operand_aux1_diff s,
        copy_const_to_operand_aux1_op = copy_const_to_operand_aux1_op s,
        copy_const_to_operand_aux1_ret = copy_const_to_operand_aux1_ret'\<rparr>
in
 ret)"

lemma copy_const_to_operand_aux1_imp_correct:
  "copy_const_to_operand_aux1_ret (copy_const_to_operand_aux1_imp s) 
  = (1 ## (operand_bit_to_var_tail (prod_encode 
    (copy_const_to_operand_aux1_op s,copy_const_to_operand_aux1_diff s))) 
## (nth_bit_tail (copy_const_to_operand_aux1_x s) (copy_const_to_operand_aux1_diff s)) 
## 0)"
apply (simp only: copy_const_to_operand_aux1_imp_def)
apply (simp add: Let_def cons_imp_correct nth_bit_tail_imp_correct
   operand_bit_to_var_tail_imp_correct prod_encode_imp_correct nth_bit_tail'_correct)
done 

definition "copy_const_to_operand_aux1_imp_time t s \<equiv> 
(let
  nth_bit_tail_acc' = copy_const_to_operand_aux1_x s;
  t = t + 2;
  nth_bit_tail_n' = copy_const_to_operand_aux1_diff s;
  t = t + 2;
  nth_bit_tail_ret' = 0;
  t = t + 2;
  nth_bit_tail_state = \<lparr>nth_bit_tail_acc = nth_bit_tail_acc',
                        nth_bit_tail_n = nth_bit_tail_n',
                        nth_bit_tail_ret = nth_bit_tail_ret'\<rparr>;
  nth_bit_tail_ret_state = nth_bit_tail_imp nth_bit_tail_state;
  t = t + nth_bit_tail_imp_time 0 nth_bit_tail_state;

  cons_h' = nth_bit_tail_ret nth_bit_tail_ret_state;
  t = t + 2;
  cons_t' = 0;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  prod_encode_a' = copy_const_to_operand_aux1_op s;
  t = t + 2;
  prod_encode_b' = copy_const_to_operand_aux1_diff s;
  t = t + 2;
  prod_encode_ret' = 0;
  t = t + 2;
  prod_encode_state = \<lparr>prod_encode_a = prod_encode_a', 
                       prod_encode_b = prod_encode_b',
                       prod_encode_ret = prod_encode_ret'\<rparr>;
  prod_encode_ret_state = prod_encode_imp prod_encode_state;
  t = t + prod_encode_imp_time 0 prod_encode_state;

  operand_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
  t = t + 2;
  operand_bit_to_var_tail_ret' = 0;
  t = t + 2;
  operand_bit_to_var_tail_state = 
    \<lparr>operand_bit_to_var_tail_n = operand_bit_to_var_tail_n',
    operand_bit_to_var_tail_ret = operand_bit_to_var_tail_ret'\<rparr>;
  operand_bit_to_var_tail_ret_state 
    = operand_bit_to_var_tail_imp operand_bit_to_var_tail_state;
  t = t + operand_bit_to_var_tail_imp_time 0 operand_bit_to_var_tail_state;

  cons_h' = operand_bit_to_var_tail_ret operand_bit_to_var_tail_ret_state;
  t = t + 2;
  cons_t' = cons_ret cons_ret_state;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp  cons_state;
  t = t + cons_imp_time 0 cons_state;

  cons_h' = 1;
  t = t + 2;
  cons_t' = cons_ret cons_ret_state;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp  cons_state;
  t = t + cons_imp_time 0 cons_state;

  copy_const_to_operand_aux1_ret' = cons_ret cons_ret_state;
  t = t + 2;
  ret = \<lparr>copy_const_to_operand_aux1_x = copy_const_to_operand_aux1_x s,
        copy_const_to_operand_aux1_diff = copy_const_to_operand_aux1_diff s,
        copy_const_to_operand_aux1_op = copy_const_to_operand_aux1_op s,
        copy_const_to_operand_aux1_ret = copy_const_to_operand_aux1_ret'\<rparr>
in
 t)"

abbreviation "copy_const_to_operand_aux1_IMP_vars \<equiv>
  {copy_const_to_operand_aux1_op_str, copy_const_to_operand_aux1_diff_str,
  copy_const_to_operand_aux1_x_str, copy_const_to_operand_aux1_ret_str}"

definition "copy_const_to_operand_aux1_imp_to_HOL_state p s\<equiv> 
  \<lparr>copy_const_to_operand_aux1_x = s (add_prefix p copy_const_to_operand_aux1_x_str),
  copy_const_to_operand_aux1_diff = s (add_prefix p copy_const_to_operand_aux1_diff_str),
  copy_const_to_operand_aux1_op = s (add_prefix p copy_const_to_operand_aux1_op_str),
  copy_const_to_operand_aux1_ret = s (add_prefix p copy_const_to_operand_aux1_ret_str)\<rparr>"

lemmas copy_const_to_operand_aux1_state_translators=
copy_const_to_operand_aux1_imp_to_HOL_state_def
cons_imp_to_HOL_state_def
prod_encode_imp_to_HOL_state_def
operand_bit_to_var_tail_imp_to_HOL_state_def
nth_bit_tail_imp_to_HOL_state_def

definition "copy_const_to_operand_aux1_IMP_Minus \<equiv> 
   (nth_bit_tail_prefix @ nth_bit_tail_acc_str) 
     ::= A (V copy_const_to_operand_aux1_x_str);;
   (nth_bit_tail_prefix @ nth_bit_tail_n_str) 
     ::= A (V copy_const_to_operand_aux1_diff_str);;
   (nth_bit_tail_prefix @ nth_bit_tail_ret_str) 
     ::= A (N 0);;
   invoke_subprogram nth_bit_tail_prefix nth_bit_tail_IMP_Minus;;

   (cons_prefix @ cons_h_str) ::= A (V (nth_bit_tail_prefix @ nth_bit_tail_ret_str));;
   (cons_prefix @ cons_t_str) ::= A (N 0);;
   (cons_prefix @ cons_ret_str) ::= A (N 0);;
   invoke_subprogram cons_prefix cons_IMP_Minus;;

   (prod_encode_prefix @ prod_encode_a_str) ::= A (V copy_const_to_operand_aux1_op_str);;
   (prod_encode_prefix @ prod_encode_b_str) ::= A (V copy_const_to_operand_aux1_diff_str);;
   (prod_encode_prefix @ prod_encode_ret_str) ::= A (N 0);;
   invoke_subprogram prod_encode_prefix prod_encode_IMP_Minus;;

   (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_n_str)
     ::= A (V (prod_encode_prefix @ prod_encode_ret_str));;
   (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str)
     ::= A (N 0);;
    invoke_subprogram operand_bit_to_var_tail_prefix operand_bit_to_var_tail_IMP_Minus;;

   (cons_prefix @ cons_h_str) 
     ::= A (V (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str));;
   (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
   (cons_prefix @ cons_ret_str) ::= A (N 0);;
   invoke_subprogram cons_prefix cons_IMP_Minus;;

   (cons_prefix @ cons_h_str) ::= A (N 1);;
   (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
   (cons_prefix @ cons_ret_str) ::= A (N 0);;
   invoke_subprogram cons_prefix cons_IMP_Minus;;

   copy_const_to_operand_aux1_ret_str ::= A (V (cons_prefix @ cons_ret_str))
  "

lemma copy_const_to_operand_aux1_IMP_Minus_correct_function:
  "(invoke_subprogram p copy_const_to_operand_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_const_to_operand_aux1_ret_str)
      = copy_const_to_operand_aux1_ret
          (copy_const_to_operand_aux1_imp (copy_const_to_operand_aux1_imp_to_HOL_state p s))"
  apply (simp only: copy_const_to_operand_aux1_imp_def)
  apply (simp only: copy_const_to_operand_aux1_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule nth_bit_tail_IMP_Minus_correct[where vars=copy_const_to_operand_aux1_IMP_vars])
  subgoal premises p using p(24) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_const_to_operand_aux1_IMP_vars])
  subgoal premises p using p(26) by fastforce
  apply (erule prod_encode_IMP_Minus_correct[where vars="copy_const_to_operand_aux1_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
  subgoal premises p using p(28) by fastforce
  apply (erule operand_bit_to_var_tail_IMP_Minus_correct[where vars="copy_const_to_operand_aux1_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
  subgoal premises p using p(30) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_const_to_operand_aux1_IMP_vars])
  subgoal premises p using p(32) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_const_to_operand_aux1_IMP_vars])
  subgoal premises p using p(34) by fastforce
  apply (force simp: Let_def copy_const_to_operand_aux1_state_translators)
  done 

lemma copy_const_to_operand_aux1_IMP_Minus_correct_time:
  "(invoke_subprogram p copy_const_to_operand_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
    t =  (copy_const_to_operand_aux1_imp_time 0 (copy_const_to_operand_aux1_imp_to_HOL_state p s))"
  apply (simp only: copy_const_to_operand_aux1_imp_time_def)
  apply (simp only: copy_const_to_operand_aux1_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule nth_bit_tail_IMP_Minus_correct[where vars=copy_const_to_operand_aux1_IMP_vars])
  subgoal premises p using p(47) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_const_to_operand_aux1_IMP_vars])
  subgoal premises p using p(49) by fastforce
  apply (erule prod_encode_IMP_Minus_correct[where vars="copy_const_to_operand_aux1_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
  subgoal premises p using p(51) by fastforce
  apply (erule operand_bit_to_var_tail_IMP_Minus_correct[where vars="copy_const_to_operand_aux1_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
  subgoal premises p using p(53) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_const_to_operand_aux1_IMP_vars])
  subgoal premises p using p(55) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=copy_const_to_operand_aux1_IMP_vars])
  subgoal premises p using p(57) by fastforce
  apply (force simp: Let_def copy_const_to_operand_aux1_state_translators)
  done 

lemma copy_const_to_operand_aux1_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ copy_const_to_operand_aux1_pref) copy_const_to_operand_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix copy_const_to_operand_aux1_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma copy_const_to_operand_aux1_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_const_to_operand_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (copy_const_to_operand_aux1_imp_time 0 (copy_const_to_operand_aux1_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) copy_const_to_operand_aux1_ret_str) =
          copy_const_to_operand_aux1_ret (copy_const_to_operand_aux1_imp
                                        (copy_const_to_operand_aux1_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_const_to_operand_aux1_IMP_Minus_correct_function
  by (auto simp: copy_const_to_operand_aux1_IMP_Minus_correct_time)
    (meson copy_const_to_operand_aux1_IMP_Minus_correct_effects set_mono_prefix) 


subsubsection copy_const_to_operand_acc

record copy_const_to_operand_acc_state = 
  copy_const_to_operand_acc_acc::nat
  copy_const_to_operand_acc_diff::nat 
  copy_const_to_operand_acc_i::nat
  copy_const_to_operand_acc_op::nat
  copy_const_to_operand_acc_x::nat
  copy_const_to_operand_acc_ret::nat

abbreviation "copy_const_to_operand_acc_prefix \<equiv> ''copy_const_to_operand_acc.''"
abbreviation "copy_const_to_operand_acc_acc_str \<equiv> ''acc''"
abbreviation "copy_const_to_operand_acc_diff_str \<equiv> ''diff''"
abbreviation "copy_const_to_operand_acc_i_str \<equiv> ''i''"
abbreviation "copy_const_to_operand_acc_op_str \<equiv> ''op''"
abbreviation "copy_const_to_operand_acc_x_str \<equiv> ''x''"
abbreviation "copy_const_to_operand_acc_ret_str \<equiv> ''ret''"

definition "copy_const_to_operand_acc_state_upd s \<equiv> 
 (let
  cons_h' = copy_const_to_operand_acc_acc s;
  cons_t' = 0;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  copy_const_to_operand_aux1_x' = copy_const_to_operand_acc_x s;
  copy_const_to_operand_aux1_diff' = copy_const_to_operand_acc_i s - copy_const_to_operand_acc_diff s;
  copy_const_to_operand_aux1_op'= copy_const_to_operand_acc_op s;
  copy_const_to_operand_aux1_ret' = 0;
  copy_const_to_operand_aux1_state = 
    \<lparr>copy_const_to_operand_aux1_x = copy_const_to_operand_aux1_x',
    copy_const_to_operand_aux1_diff = copy_const_to_operand_aux1_diff',
    copy_const_to_operand_aux1_op = copy_const_to_operand_aux1_op',
    copy_const_to_operand_aux1_ret = copy_const_to_operand_aux1_ret'\<rparr>;
  copy_const_to_operand_aux1_ret_state = copy_const_to_operand_aux1_imp copy_const_to_operand_aux1_state;

  cons_h' = copy_const_to_operand_aux1_ret copy_const_to_operand_aux1_ret_state;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = 2;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  copy_const_to_operand_acc_acc' = cons_ret cons_ret_state;
  copy_const_to_operand_acc_diff' = copy_const_to_operand_acc_diff s - 1;
  ret = 
   \<lparr>copy_const_to_operand_acc_acc = copy_const_to_operand_acc_acc',
   copy_const_to_operand_acc_diff = copy_const_to_operand_acc_diff',
   copy_const_to_operand_acc_i = copy_const_to_operand_acc_i s,
   copy_const_to_operand_acc_op = copy_const_to_operand_acc_op s,
   copy_const_to_operand_acc_x = copy_const_to_operand_acc_x s,
   copy_const_to_operand_acc_ret = copy_const_to_operand_acc_ret s\<rparr>
 in
  ret)"

definition "copy_const_to_operand_acc_imp_compute_loop_condition s \<equiv> 
  (let 
    cond = copy_const_to_operand_acc_diff s
   in 
    cond)"

definition "copy_const_to_operand_acc_imp_after_loop s \<equiv> 
(let
  copy_const_to_operand_acc_ret' = copy_const_to_operand_acc_acc s;
  ret = 
   \<lparr>copy_const_to_operand_acc_acc = copy_const_to_operand_acc_acc s,
   copy_const_to_operand_acc_diff = copy_const_to_operand_acc_diff s,
   copy_const_to_operand_acc_i = copy_const_to_operand_acc_i s,
   copy_const_to_operand_acc_op = copy_const_to_operand_acc_op s,
   copy_const_to_operand_acc_x = copy_const_to_operand_acc_x s,
   copy_const_to_operand_acc_ret = copy_const_to_operand_acc_ret'\<rparr>
in 
   ret)"

lemmas copy_const_to_operand_acc_imp_subprogram_simps = 
  copy_const_to_operand_acc_state_upd_def
  copy_const_to_operand_acc_imp_compute_loop_condition_def
  copy_const_to_operand_acc_imp_after_loop_def

function copy_const_to_operand_acc_imp::
  "copy_const_to_operand_acc_state \<Rightarrow> copy_const_to_operand_acc_state" where
  "copy_const_to_operand_acc_imp s =
  (if copy_const_to_operand_acc_imp_compute_loop_condition s \<noteq> 0
   then
    let next_iteration = copy_const_to_operand_acc_imp (copy_const_to_operand_acc_state_upd s)
    in next_iteration
   else
    let ret = copy_const_to_operand_acc_imp_after_loop s
    in ret
  )"
  by simp+
termination
  apply (relation "measure copy_const_to_operand_acc_diff")
  apply (simp add: copy_const_to_operand_acc_imp_subprogram_simps
    cons_imp_correct copy_const_to_operand_aux1_imp_correct Let_def)+
  done

declare copy_const_to_operand_acc_imp.simps [simp del]

lemma copy_const_to_operand_acc_imp_correct:
  "copy_const_to_operand_acc_ret (copy_const_to_operand_acc_imp s) =
    copy_const_to_operand_acc (copy_const_to_operand_acc_acc s) (copy_const_to_operand_acc_diff s)
    (copy_const_to_operand_acc_i s) (copy_const_to_operand_acc_op s) (copy_const_to_operand_acc_x s)"
  apply (induction s rule: copy_const_to_operand_acc_imp.induct)
  apply (subst copy_const_to_operand_acc_imp.simps)
  apply (subst copy_const_to_operand_acc.simps)
  apply (auto simp del: copy_const_to_operand_acc.simps 
  simp add: copy_const_to_operand_acc_imp_subprogram_simps Let_def
  cons_imp_correct copy_const_to_operand_aux1_imp_correct)
  done  

definition "copy_const_to_operand_acc_state_upd_time t s \<equiv> 
 (let
  cons_h' = copy_const_to_operand_acc_acc s;
  t = t + 2;
  cons_t' = 0;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  copy_const_to_operand_aux1_x' = copy_const_to_operand_acc_x s;
  t = t + 2;
  copy_const_to_operand_aux1_diff' = copy_const_to_operand_acc_i s - copy_const_to_operand_acc_diff s;
  t = t + 2;
  copy_const_to_operand_aux1_op'= copy_const_to_operand_acc_op s;
  t = t + 2;
  copy_const_to_operand_aux1_ret' = 0;
  t = t + 2;
  copy_const_to_operand_aux1_state = 
    \<lparr>copy_const_to_operand_aux1_x = copy_const_to_operand_aux1_x',
    copy_const_to_operand_aux1_diff = copy_const_to_operand_aux1_diff',
    copy_const_to_operand_aux1_op = copy_const_to_operand_aux1_op',
    copy_const_to_operand_aux1_ret = copy_const_to_operand_aux1_ret'\<rparr>;
  copy_const_to_operand_aux1_ret_state = copy_const_to_operand_aux1_imp copy_const_to_operand_aux1_state;
  t = t + copy_const_to_operand_aux1_imp_time 0 copy_const_to_operand_aux1_state;

  cons_h' = copy_const_to_operand_aux1_ret copy_const_to_operand_aux1_ret_state;
  t = t + 2;
  cons_t' = cons_ret cons_ret_state;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  cons_h' = 2;
  t = t + 2;
  cons_t' = cons_ret cons_ret_state;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  copy_const_to_operand_acc_acc' = cons_ret cons_ret_state;
  t = t + 2;
  copy_const_to_operand_acc_diff' = copy_const_to_operand_acc_diff s - 1;
  t = t + 2;
  ret = 
   \<lparr>copy_const_to_operand_acc_acc = copy_const_to_operand_acc_acc',
   copy_const_to_operand_acc_diff = copy_const_to_operand_acc_diff',
   copy_const_to_operand_acc_i = copy_const_to_operand_acc_i s,
   copy_const_to_operand_acc_op = copy_const_to_operand_acc_op s,
   copy_const_to_operand_acc_x = copy_const_to_operand_acc_x s,
   copy_const_to_operand_acc_ret = copy_const_to_operand_acc_ret s\<rparr>
 in
  t)"

definition "copy_const_to_operand_acc_imp_compute_loop_condition_time t s \<equiv> 
  (let 
    cond = copy_const_to_operand_acc_diff s;
    t = t + 2
   in 
    t)"

definition "copy_const_to_operand_acc_imp_after_loop_time t s \<equiv> 
(let
  copy_const_to_operand_acc_ret' = copy_const_to_operand_acc_acc s;
  t = t + 2;
  ret = 
   \<lparr>copy_const_to_operand_acc_acc = copy_const_to_operand_acc_acc s,
   copy_const_to_operand_acc_diff = copy_const_to_operand_acc_diff s,
   copy_const_to_operand_acc_i = copy_const_to_operand_acc_i s,
   copy_const_to_operand_acc_op = copy_const_to_operand_acc_op s,
   copy_const_to_operand_acc_x = copy_const_to_operand_acc_x s,
   copy_const_to_operand_acc_ret = copy_const_to_operand_acc_ret'\<rparr>
in 
   t)"

lemmas copy_const_to_operand_acc_imp_subprogram_time_simps = 
  copy_const_to_operand_acc_state_upd_time_def
  copy_const_to_operand_acc_imp_compute_loop_condition_time_def
  copy_const_to_operand_acc_imp_after_loop_time_def
  copy_const_to_operand_acc_imp_subprogram_simps

function copy_const_to_operand_acc_imp_time::
  "nat \<Rightarrow> copy_const_to_operand_acc_state \<Rightarrow> nat" where
  "copy_const_to_operand_acc_imp_time t s =
  copy_const_to_operand_acc_imp_compute_loop_condition_time 0 s +
  (if copy_const_to_operand_acc_imp_compute_loop_condition s \<noteq> 0
    then
      (let
        t = t + 1;
        next_iteration =
          copy_const_to_operand_acc_imp_time (t + copy_const_to_operand_acc_state_upd_time 0 s)
                         (copy_const_to_operand_acc_state_upd s)
       in next_iteration)
    else
      (let
        t = t + 2;
        ret = t + copy_const_to_operand_acc_imp_after_loop_time 0 s
       in ret)
  )"
  by auto
termination
  apply (relation "measure (copy_const_to_operand_acc_diff \<circ> snd)")
  by (simp add: copy_const_to_operand_acc_imp_subprogram_time_simps 
  copy_const_to_operand_aux1_imp_correct cons_imp_correct Let_def)+


declare copy_const_to_operand_acc_imp_time.simps [simp del]            

lemma copy_const_to_operand_acc_imp_time_acc:
  "(copy_const_to_operand_acc_imp_time (Suc t) s) = Suc (copy_const_to_operand_acc_imp_time t s)"
  by (induction t s rule: copy_const_to_operand_acc_imp_time.induct)
    ((subst (1 2) copy_const_to_operand_acc_imp_time.simps);
      (simp add: copy_const_to_operand_acc_state_upd_def))            

lemma copy_const_to_operand_acc_imp_time_acc_2_aux:
  "(copy_const_to_operand_acc_imp_time t s) = t + (copy_const_to_operand_acc_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: copy_const_to_operand_acc_imp_time_acc)+            

lemma copy_const_to_operand_acc_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (copy_const_to_operand_acc_imp_time t s) = t + (copy_const_to_operand_acc_imp_time 0 s)"
  by (rule copy_const_to_operand_acc_imp_time_acc_2_aux)            

lemma copy_const_to_operand_acc_imp_time_acc_3:
  "(copy_const_to_operand_acc_imp_time (a + b) s) = a + (copy_const_to_operand_acc_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: copy_const_to_operand_acc_imp_time_acc)+            

abbreviation "copy_const_to_operand_acc_while_cond \<equiv> ''condition''"

definition "copy_const_to_operand_acc_IMP_init_while_cond \<equiv>
  copy_const_to_operand_acc_while_cond ::= A (V copy_const_to_operand_acc_diff_str)
"

definition "copy_const_to_operand_acc_IMP_loop_body \<equiv> 
(cons_prefix @ cons_h_str) ::= A (V copy_const_to_operand_acc_acc_str);;
(cons_prefix @ cons_t_str) ::= A (N 0);;
(cons_prefix @ cons_ret_str) ::= A (N 0);;
invoke_subprogram cons_prefix cons_IMP_Minus;;

(copy_const_to_operand_aux1_prefix @ copy_const_to_operand_aux1_x_str)
  ::= A (V copy_const_to_operand_acc_x_str);;
(copy_const_to_operand_aux1_prefix @ copy_const_to_operand_aux1_diff_str)
  ::= Sub (V copy_const_to_operand_acc_i_str) (V copy_const_to_operand_acc_diff_str);;
(copy_const_to_operand_aux1_prefix @ copy_const_to_operand_aux1_op_str)
  ::= A (V copy_const_to_operand_acc_op_str);;
  (copy_const_to_operand_aux1_prefix @ copy_const_to_operand_aux1_ret_str)
  ::= A (N 0);;
invoke_subprogram copy_const_to_operand_aux1_prefix copy_const_to_operand_aux1_IMP_Minus;;
 
(cons_prefix @ cons_h_str) 
  ::= A (V (copy_const_to_operand_aux1_prefix @ copy_const_to_operand_aux1_ret_str));;
(cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
(cons_prefix @ cons_ret_str) ::= A (N 0);;
invoke_subprogram cons_prefix cons_IMP_Minus;;

(cons_prefix @ cons_h_str) ::= A (N 2);;
(cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
(cons_prefix @ cons_ret_str) ::= A (N 0);;
invoke_subprogram cons_prefix cons_IMP_Minus;;

copy_const_to_operand_acc_acc_str ::= A (V (cons_prefix @ cons_ret_str));;
copy_const_to_operand_acc_diff_str ::= Sub (V copy_const_to_operand_acc_diff_str) (N 1)"

definition "copy_const_to_operand_acc_IMP_after_loop \<equiv>
copy_const_to_operand_acc_ret_str ::= A (V copy_const_to_operand_acc_acc_str)
"

definition copy_const_to_operand_acc_IMP_Minus where
  "copy_const_to_operand_acc_IMP_Minus \<equiv>
  copy_const_to_operand_acc_IMP_init_while_cond;;
  WHILE copy_const_to_operand_acc_while_cond \<noteq>0 DO (
    copy_const_to_operand_acc_IMP_loop_body;;
    copy_const_to_operand_acc_IMP_init_while_cond
  );;
  copy_const_to_operand_acc_IMP_after_loop"

abbreviation "copy_const_to_operand_acc_IMP_vars\<equiv>
  {copy_const_to_operand_acc_ret_str, copy_const_to_operand_acc_acc_str,
  copy_const_to_operand_acc_i_str, copy_const_to_operand_acc_diff_str,
  copy_const_to_operand_acc_op_str, copy_const_to_operand_acc_x_str,
  copy_const_to_operand_acc_while_cond}"

lemmas copy_const_to_operand_acc_IMP_subprogram_simps =
  copy_const_to_operand_acc_IMP_init_while_cond_def
  copy_const_to_operand_acc_IMP_loop_body_def
  copy_const_to_operand_acc_IMP_after_loop_def

definition "copy_const_to_operand_acc_imp_to_HOL_state p s =
  \<lparr>copy_const_to_operand_acc_acc = (s (add_prefix p copy_const_to_operand_acc_acc_str)),
   copy_const_to_operand_acc_diff = (s (add_prefix p copy_const_to_operand_acc_diff_str)),
   copy_const_to_operand_acc_i = (s (add_prefix p copy_const_to_operand_acc_i_str)),
   copy_const_to_operand_acc_op = (s (add_prefix p copy_const_to_operand_acc_op_str)),
   copy_const_to_operand_acc_x = (s (add_prefix p copy_const_to_operand_acc_x_str)),
   copy_const_to_operand_acc_ret = (s (add_prefix p copy_const_to_operand_acc_ret_str))\<rparr>"

lemmas copy_const_to_operand_acc_state_translators =
  copy_const_to_operand_acc_imp_to_HOL_state_def
  copy_const_to_operand_aux1_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def

lemmas copy_const_to_operand_acc_complete_simps =
  copy_const_to_operand_acc_IMP_subprogram_simps
  copy_const_to_operand_acc_imp_subprogram_simps
  copy_const_to_operand_acc_state_translators

lemma copy_const_to_operand_acc_IMP_Minus_correct_function:
  "(invoke_subprogram p copy_const_to_operand_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_const_to_operand_acc_ret_str)
      = copy_const_to_operand_acc_ret
          (copy_const_to_operand_acc_imp (copy_const_to_operand_acc_imp_to_HOL_state p s))"
  apply(induction "copy_const_to_operand_acc_imp_to_HOL_state p s" arbitrary: s s' t
    rule: copy_const_to_operand_acc_imp.induct)
  apply(subst copy_const_to_operand_acc_imp.simps)
  apply(simp only: copy_const_to_operand_acc_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule While_tE)

  subgoal
    apply(simp only: copy_const_to_operand_acc_IMP_subprogram_simps prefix_simps)
    by(fastforce simp: copy_const_to_operand_acc_IMP_subprogram_simps
        copy_const_to_operand_acc_imp_subprogram_simps
        copy_const_to_operand_acc_state_translators)

  apply(erule Seq_E)+
  apply(dest_com_gen)

  subgoal
      apply(simp only: copy_const_to_operand_acc_IMP_init_while_cond_def prefix_simps)
      by(fastforce simp add: copy_const_to_operand_acc_complete_simps)

  subgoal
      apply(subst (asm) copy_const_to_operand_acc_IMP_init_while_cond_def)
      apply(simp only: copy_const_to_operand_acc_IMP_loop_body_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
      subgoal premises p using p(24) by fastforce
      apply(erule copy_const_to_operand_aux1_IMP_Minus_correct[where 
        vars = "copy_const_to_operand_acc_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
      subgoal premises p using p(26) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
      subgoal premises p using p(28) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
      subgoal premises p using p(30) by fastforce
      by (force simp: copy_const_to_operand_acc_imp_subprogram_simps
          copy_const_to_operand_acc_state_translators Let_def)

  subgoal
      apply(simp only: copy_const_to_operand_acc_IMP_init_while_cond_def prefix_simps
          copy_const_to_operand_acc_IMP_loop_body_def)
      apply(erule Seq_E)+
      apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
      subgoal premises p using p(24) by fastforce
      apply(erule copy_const_to_operand_aux1_IMP_Minus_correct[where 
        vars = "copy_const_to_operand_acc_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
      subgoal premises p using p(26) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
      subgoal premises p using p(28) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
      subgoal premises p using p(30) by fastforce
      by (force simp: copy_const_to_operand_acc_imp_subprogram_simps
          copy_const_to_operand_acc_state_translators Let_def)
  done        

lemma copy_const_to_operand_acc_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ copy_const_to_operand_acc_pref) copy_const_to_operand_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix copy_const_to_operand_acc_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemmas copy_const_to_operand_acc_complete_time_simps =
  copy_const_to_operand_acc_imp_subprogram_time_simps
  copy_const_to_operand_acc_imp_time_acc_2
  copy_const_to_operand_acc_imp_time_acc_3
  copy_const_to_operand_acc_state_translators

lemma copy_const_to_operand_acc_IMP_Minus_correct_time:
  "(invoke_subprogram p copy_const_to_operand_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = copy_const_to_operand_acc_imp_time 0 (copy_const_to_operand_acc_imp_to_HOL_state p s)"
  apply(induction "copy_const_to_operand_acc_imp_to_HOL_state p s" arbitrary: s s' t
      rule: copy_const_to_operand_acc_imp.induct)
  apply(subst copy_const_to_operand_acc_imp_time.simps)
  apply(simp only: copy_const_to_operand_acc_IMP_Minus_def prefix_simps)

  apply(erule Seq_tE)+
  apply(erule While_tE_time)

  subgoal
    apply(simp only: copy_const_to_operand_acc_IMP_subprogram_simps prefix_simps)
    by (force simp: copy_const_to_operand_acc_IMP_subprogram_simps
        copy_const_to_operand_acc_imp_subprogram_time_simps copy_const_to_operand_acc_state_translators)

  apply(erule Seq_tE)+
  apply(simp add: add.assoc)
  apply(dest_com_gen_time)

  subgoal
    apply(simp only: copy_const_to_operand_acc_IMP_init_while_cond_def prefix_simps)
    by(fastforce simp add: copy_const_to_operand_acc_complete_simps)

  subgoal
    apply(subst (asm) copy_const_to_operand_acc_IMP_init_while_cond_def)
    apply(simp only: copy_const_to_operand_acc_IMP_loop_body_def prefix_simps)
    apply(erule Seq_E)+
    apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
    subgoal premises p using p(27) by fastforce
    apply(erule copy_const_to_operand_aux1_IMP_Minus_correct[where 
      vars = "copy_const_to_operand_acc_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
    subgoal premises p using p(29) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
    subgoal premises p using p(31) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
    subgoal premises p using p(33) by fastforce
    by (force simp: copy_const_to_operand_acc_imp_subprogram_simps
        copy_const_to_operand_acc_state_translators Let_def)
  
  subgoal
    apply(simp only: prefix_simps copy_const_to_operand_acc_IMP_init_while_cond_def
        copy_const_to_operand_acc_IMP_loop_body_def)
    apply(erule Seq_tE)+
    apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
    subgoal premises p using p(45) by fastforce
    apply(erule copy_const_to_operand_aux1_IMP_Minus_correct[where 
      vars = "copy_const_to_operand_acc_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
    subgoal premises p using p(47) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
    subgoal premises p using p(49) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "copy_const_to_operand_acc_IMP_vars"])
    subgoal premises p using p(51) by fastforce
    by(force simp: copy_const_to_operand_acc_complete_time_simps Let_def)
 done      

lemma copy_const_to_operand_acc_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_const_to_operand_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (copy_const_to_operand_acc_imp_time 0 (copy_const_to_operand_acc_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) copy_const_to_operand_acc_ret_str) =
          copy_const_to_operand_acc_ret (copy_const_to_operand_acc_imp
                                        (copy_const_to_operand_acc_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_const_to_operand_acc_IMP_Minus_correct_function
  by (auto simp: copy_const_to_operand_acc_IMP_Minus_correct_time)
    (meson copy_const_to_operand_acc_IMP_Minus_correct_effects set_mono_prefix)

subsubsection copy_const_to_operand_tail

record copy_const_to_operand_tail_state = 
  copy_const_to_operand_tail_i::nat
  copy_const_to_operand_tail_op::nat
  copy_const_to_operand_tail_x::nat
  copy_const_to_operand_tail_ret::nat

abbreviation "copy_const_to_operand_tail_prefix \<equiv> ''copy_const_to_operand_tail.''"
abbreviation "copy_const_to_operand_tail_i_str \<equiv> ''i''"
abbreviation "copy_const_to_operand_tail_op_str \<equiv> ''op''"
abbreviation "copy_const_to_operand_tail_x_str \<equiv> ''x''"
abbreviation "copy_const_to_operand_tail_ret_str \<equiv> ''ret''"

function copy_const_to_operand_tail_imp 
  :: "copy_const_to_operand_tail_state \<Rightarrow> copy_const_to_operand_tail_state" where 
"copy_const_to_operand_tail_imp s = 
  (let
    cons_h' = 0;
    cons_t' = 0;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    copy_const_to_operand_acc_acc' = cons_ret cons_ret_state;
    copy_const_to_operand_acc_diff' = copy_const_to_operand_tail_i s;
    copy_const_to_operand_acc_i' = copy_const_to_operand_tail_i s;
    copy_const_to_operand_acc_op' = copy_const_to_operand_tail_op s;
    copy_const_to_operand_acc_x' = copy_const_to_operand_tail_x s;
    copy_const_to_operand_acc_ret' = 0;
    copy_const_to_operand_acc_state = 
      \<lparr>copy_const_to_operand_acc_acc = copy_const_to_operand_acc_acc',
      copy_const_to_operand_acc_diff = copy_const_to_operand_acc_diff',
      copy_const_to_operand_acc_i = copy_const_to_operand_acc_i',
      copy_const_to_operand_acc_op = copy_const_to_operand_acc_op',
      copy_const_to_operand_acc_x = copy_const_to_operand_acc_x',
      copy_const_to_operand_acc_ret = copy_const_to_operand_acc_ret'\<rparr>;
    copy_const_to_operand_acc_ret_state
      = copy_const_to_operand_acc_imp copy_const_to_operand_acc_state;
    copy_const_to_operand_tail_ret' = 
      copy_const_to_operand_acc_ret copy_const_to_operand_acc_ret_state;
    ret =
      \<lparr>copy_const_to_operand_tail_i = copy_const_to_operand_tail_i s,
      copy_const_to_operand_tail_op = copy_const_to_operand_tail_op s,
      copy_const_to_operand_tail_x = copy_const_to_operand_tail_x s,
      copy_const_to_operand_tail_ret = copy_const_to_operand_tail_ret'\<rparr>
  in 
   ret)" by simp+
  termination 
  by (relation "measure copy_const_to_operand_tail_i", simp)

declare copy_const_to_operand_tail_imp.simps[simp del]

lemma copy_const_to_operand_tail_imp_correct:
  "copy_const_to_operand_tail_ret (copy_const_to_operand_tail_imp s)
    = copy_const_to_operand_tail (copy_const_to_operand_tail_i s) 
      (copy_const_to_operand_tail_op s) (copy_const_to_operand_tail_x s)"
apply (simp only: copy_const_to_operand_tail_imp.simps)
apply (auto simp add: copy_const_to_operand_acc_imp_correct cons_imp_correct Let_def
  copy_const_to_operand_tail_def)
done 

function copy_const_to_operand_tail_imp_time 
  :: "nat \<Rightarrow> copy_const_to_operand_tail_state \<Rightarrow> nat" where 
"copy_const_to_operand_tail_imp_time t s = 
  (let
    cons_h' = 0;
    t = t + 2;
    cons_t' = 0;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    copy_const_to_operand_acc_acc' = cons_ret cons_ret_state;
    t = t + 2;
    copy_const_to_operand_acc_diff' = copy_const_to_operand_tail_i s;
    t = t + 2;
    copy_const_to_operand_acc_i' = copy_const_to_operand_tail_i s;
    t = t + 2;
    copy_const_to_operand_acc_op' = copy_const_to_operand_tail_op s;
    t = t + 2;
    copy_const_to_operand_acc_x' = copy_const_to_operand_tail_x s;
    t = t + 2;
    copy_const_to_operand_acc_ret' = 0;
    t = t + 2;
    copy_const_to_operand_acc_state = 
      \<lparr>copy_const_to_operand_acc_acc = copy_const_to_operand_acc_acc',
      copy_const_to_operand_acc_diff = copy_const_to_operand_acc_diff',
      copy_const_to_operand_acc_i = copy_const_to_operand_acc_i',
      copy_const_to_operand_acc_op = copy_const_to_operand_acc_op',
      copy_const_to_operand_acc_x = copy_const_to_operand_acc_x',
      copy_const_to_operand_acc_ret = copy_const_to_operand_acc_ret'\<rparr>;
    copy_const_to_operand_acc_ret_state
      = copy_const_to_operand_acc_imp copy_const_to_operand_acc_state;
    t = t + copy_const_to_operand_acc_imp_time 0 copy_const_to_operand_acc_state;

    copy_const_to_operand_tail_ret' = 
      copy_const_to_operand_acc_ret copy_const_to_operand_acc_ret_state;
    t = t + 2;
    ret =
      \<lparr>copy_const_to_operand_tail_i = copy_const_to_operand_tail_i s,
      copy_const_to_operand_tail_op = copy_const_to_operand_tail_op s,
      copy_const_to_operand_tail_x = copy_const_to_operand_tail_x s,
      copy_const_to_operand_tail_ret = copy_const_to_operand_tail_ret'\<rparr>
  in 
   t)" by auto
  termination 
  by (relation "measure (copy_const_to_operand_tail_i \<circ> snd)", simp)

abbreviation "copy_const_to_operand_tail_IMP_vars \<equiv> 
  {copy_const_to_operand_tail_i_str, copy_const_to_operand_tail_op_str,
  copy_const_to_operand_tail_x_str, copy_const_to_operand_tail_ret_str}"

definition "copy_const_to_operand_tail_imp_to_HOL_state p s \<equiv> 
   \<lparr>copy_const_to_operand_tail_i = s (add_prefix p copy_const_to_operand_tail_i_str),
    copy_const_to_operand_tail_op = s (add_prefix p copy_const_to_operand_tail_op_str),
    copy_const_to_operand_tail_x = s (add_prefix p copy_const_to_operand_tail_x_str),
    copy_const_to_operand_tail_ret = s (add_prefix p copy_const_to_operand_tail_ret_str)\<rparr>"

lemmas copy_const_to_operand_tail_state_translators=
  copy_const_to_operand_tail_imp_to_HOL_state_def
  copy_const_to_operand_acc_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def

definition "copy_const_to_operand_tail_IMP_Minus \<equiv> 
  (cons_prefix @ cons_h_str) ::= A (N 0);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  
  (copy_const_to_operand_acc_prefix @ copy_const_to_operand_acc_acc_str)
    ::= A (V (cons_prefix @ cons_ret_str));;
  (copy_const_to_operand_acc_prefix @ copy_const_to_operand_acc_diff_str)
    ::= A (V copy_const_to_operand_tail_i_str);;
  (copy_const_to_operand_acc_prefix @ copy_const_to_operand_acc_i_str)
    ::= A (V copy_const_to_operand_tail_i_str);;
  (copy_const_to_operand_acc_prefix @ copy_const_to_operand_acc_op_str)
    ::= A (V copy_const_to_operand_tail_op_str);;
  (copy_const_to_operand_acc_prefix @ copy_const_to_operand_acc_x_str)
    ::= A (V copy_const_to_operand_tail_x_str);;
  (copy_const_to_operand_acc_prefix @ copy_const_to_operand_acc_ret_str)
    ::= A (N 0);;
  invoke_subprogram copy_const_to_operand_acc_prefix copy_const_to_operand_acc_IMP_Minus;;
  copy_const_to_operand_tail_ret_str 
    ::= A (V (copy_const_to_operand_acc_prefix @ copy_const_to_operand_acc_ret_str))"

lemma copy_const_to_operand_tail_IMP_Minus_correct_function:
  "(invoke_subprogram p copy_const_to_operand_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_const_to_operand_tail_ret_str)
      = copy_const_to_operand_tail_ret
          (copy_const_to_operand_tail_imp (copy_const_to_operand_tail_imp_to_HOL_state p s))"
  apply (simp only: copy_const_to_operand_tail_imp.simps)
  apply (simp only: copy_const_to_operand_tail_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule cons_IMP_Minus_correct[where vars = copy_const_to_operand_tail_IMP_vars])
  subgoal premises p using p(12) by fastforce
  apply (erule copy_const_to_operand_acc_IMP_Minus_correct[where vars = copy_const_to_operand_tail_IMP_vars])
  subgoal premises p using p(14) by fastforce
  apply (force simp: copy_const_to_operand_tail_state_translators Let_def)
  done 

lemma copy_const_to_operand_tail_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ copy_const_to_operand_acc_pref) copy_const_to_operand_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix copy_const_to_operand_acc_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemma copy_const_to_operand_tail_IMP_Minus_correct_time:
  "(invoke_subprogram p copy_const_to_operand_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = copy_const_to_operand_tail_imp_time 0 (copy_const_to_operand_tail_imp_to_HOL_state p s)"
  apply (simp only: copy_const_to_operand_tail_imp_time.simps)
  apply (simp only: copy_const_to_operand_tail_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule cons_IMP_Minus_correct[where vars = copy_const_to_operand_tail_IMP_vars])
  subgoal premises p using p(23) by fastforce
  apply (erule copy_const_to_operand_acc_IMP_Minus_correct[where vars = copy_const_to_operand_tail_IMP_vars])
  subgoal premises p using p(25) by fastforce
  apply (force simp: copy_const_to_operand_tail_state_translators Let_def)
  done 

lemma copy_const_to_operand_tail_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_const_to_operand_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (copy_const_to_operand_tail_imp_time 0 (copy_const_to_operand_tail_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) copy_const_to_operand_tail_ret_str) =
          copy_const_to_operand_tail_ret (copy_const_to_operand_tail_imp
                                        (copy_const_to_operand_tail_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_const_to_operand_tail_IMP_Minus_correct_function 
      copy_const_to_operand_tail_IMP_Minus_correct_time
       set_mono_prefix
  by (smt (verit, ccfv_SIG) com_add_prefix_valid_subset com_only_vars)

subsection copy_atom_to_operand_tail

record copy_atom_to_operand_tail_state = 
  copy_atom_to_operand_tail_n::nat
  copy_atom_to_operand_tail_op::nat
  copy_atom_to_operand_tail_a::nat
  copy_atom_to_operand_tail_ret::nat

abbreviation "copy_atom_to_operand_tail_prefix \<equiv> ''copy_atom_to_operand_tail.''"
abbreviation "copy_atom_to_operand_tail_n_str \<equiv> ''n''"
abbreviation "copy_atom_to_operand_tail_op_str \<equiv> ''op''"
abbreviation "copy_atom_to_operand_tail_a_str \<equiv> ''a''"
abbreviation "copy_atom_to_operand_tail_ret_str \<equiv> ''ret''"
abbreviation "copy_atom_to_operand_tail_cond \<equiv> ''cond''"

function copy_atom_to_operand_tail_imp 
  :: "copy_atom_to_operand_tail_state \<Rightarrow> copy_atom_to_operand_tail_state"
where 
"copy_atom_to_operand_tail_imp s = 
(let
  fst'_state_p' = copy_atom_to_operand_tail_a s;
  fst'_state = \<lparr>fst'_state_p = fst'_state_p'\<rparr>;
  fst'_ret_state = fst'_imp fst'_state;
  cond = fst'_state_p fst'_ret_state
in
  (if cond \<noteq> 0 
  then (let
         snd'_state_p' = copy_atom_to_operand_tail_a s;
         snd'_state = \<lparr>snd'_state_p = snd'_state_p'\<rparr>;
         snd'_ret_state = snd'_imp snd'_state;
         
         copy_const_to_operand_tail_i' = copy_atom_to_operand_tail_n s;
         copy_const_to_operand_tail_op' = copy_atom_to_operand_tail_op s;
         copy_const_to_operand_tail_x' = snd'_state_p snd'_ret_state;
         copy_const_to_operand_tail_ret' = 0;
         copy_const_to_operand_tail_state 
           = \<lparr>copy_const_to_operand_tail_i = copy_const_to_operand_tail_i',
             copy_const_to_operand_tail_op = copy_const_to_operand_tail_op',
             copy_const_to_operand_tail_x = copy_const_to_operand_tail_x',
             copy_const_to_operand_tail_ret = copy_const_to_operand_tail_ret'\<rparr>;
         copy_const_to_operand_tail_ret_state = 
            copy_const_to_operand_tail_imp copy_const_to_operand_tail_state;
         copy_atom_to_operand_tail_ret' 
            = copy_const_to_operand_tail_ret copy_const_to_operand_tail_ret_state;
         ret =
           \<lparr>copy_atom_to_operand_tail_n = copy_atom_to_operand_tail_n s,
            copy_atom_to_operand_tail_op = copy_atom_to_operand_tail_op s,
            copy_atom_to_operand_tail_a = copy_atom_to_operand_tail_a s,
            copy_atom_to_operand_tail_ret = copy_atom_to_operand_tail_ret'\<rparr>
        in
         ret)
  else (let
         snd'_state_p' = copy_atom_to_operand_tail_a s;
         snd'_state = \<lparr>snd'_state_p = snd'_state_p'\<rparr>;
         snd'_ret_state = snd'_imp snd'_state;
         
         copy_var_to_operand_tail_i' = copy_atom_to_operand_tail_n s;
         copy_var_to_operand_tail_op' = copy_atom_to_operand_tail_op s;
         copy_var_to_operand_tail_v' = snd'_state_p snd'_ret_state;
         copy_var_to_operand_tail_ret' = 0;
         copy_var_to_operand_tail_state 
           = \<lparr>copy_var_to_operand_tail_i = copy_var_to_operand_tail_i',
             copy_var_to_operand_tail_op = copy_var_to_operand_tail_op',
             copy_var_to_operand_tail_v = copy_var_to_operand_tail_v',
             copy_var_to_operand_tail_ret = copy_var_to_operand_tail_ret'\<rparr>;
         copy_var_to_operand_tail_ret_state = 
            copy_var_to_operand_tail_imp copy_var_to_operand_tail_state;
         copy_atom_to_operand_tail_ret' 
            = copy_var_to_operand_tail_ret copy_var_to_operand_tail_ret_state;
         ret =
           \<lparr>copy_atom_to_operand_tail_n = copy_atom_to_operand_tail_n s,
            copy_atom_to_operand_tail_op = copy_atom_to_operand_tail_op s,
            copy_atom_to_operand_tail_a = copy_atom_to_operand_tail_a s,
            copy_atom_to_operand_tail_ret = copy_atom_to_operand_tail_ret'\<rparr>
        in
         ret)
  ))" by simp+
termination by (relation "measure copy_atom_to_operand_tail_n", simp)

declare copy_atom_to_operand_tail_imp.simps[simp del]

lemma copy_atom_to_operand_tail_imp_correct[let_function_correctness]:
  "copy_atom_to_operand_tail_ret (copy_atom_to_operand_tail_imp s) = 
    copy_atom_to_operand_tail (copy_atom_to_operand_tail_n s)
      (copy_atom_to_operand_tail_op s) (copy_atom_to_operand_tail_a s)"
apply (simp only: copy_atom_to_operand_tail_imp.simps)
apply (simp add: copy_var_to_operand_tail_imp_correct
copy_const_to_operand_tail_imp_correct fst'_imp_correct snd'_imp_correct Let_def
copy_atom_to_operand_tail_def fst_nat_fst'_nat snd_nat_snd'_nat)
done 

function copy_atom_to_operand_tail_imp_time 
  :: "nat \<Rightarrow> copy_atom_to_operand_tail_state \<Rightarrow> nat"
where 
"copy_atom_to_operand_tail_imp_time t s = 
(let
  fst'_state_p' = copy_atom_to_operand_tail_a s;
  t = t + 2;
  fst'_state = \<lparr>fst'_state_p = fst'_state_p'\<rparr>;
  fst'_ret_state = fst'_imp fst'_state;
  t = t + fst'_imp_time 0 fst'_state;
  cond = fst'_state_p fst'_ret_state;
  t = t + 2
in
  (if cond \<noteq> 0 
  then (let
         t = t + 1;
         snd'_state_p' = copy_atom_to_operand_tail_a s;
         t = t + 2;
         snd'_state = \<lparr>snd'_state_p = snd'_state_p'\<rparr>;
         snd'_ret_state = snd'_imp snd'_state;
         t = t + snd'_imp_time 0 snd'_state;
         
         copy_const_to_operand_tail_i' = copy_atom_to_operand_tail_n s;
         t = t + 2;
         copy_const_to_operand_tail_op' = copy_atom_to_operand_tail_op s;
         t = t + 2;
         copy_const_to_operand_tail_x' = snd'_state_p snd'_ret_state;
         t = t + 2;
         copy_const_to_operand_tail_ret' = 0;
         t = t + 2;
         copy_const_to_operand_tail_state 
           = \<lparr>copy_const_to_operand_tail_i = copy_const_to_operand_tail_i',
             copy_const_to_operand_tail_op = copy_const_to_operand_tail_op',
             copy_const_to_operand_tail_x = copy_const_to_operand_tail_x',
             copy_const_to_operand_tail_ret = copy_const_to_operand_tail_ret'\<rparr>;
         copy_const_to_operand_tail_ret_state = 
            copy_const_to_operand_tail_imp copy_const_to_operand_tail_state;
         t = t + copy_const_to_operand_tail_imp_time 0 copy_const_to_operand_tail_state;
         copy_atom_to_operand_tail_ret' 
            = copy_const_to_operand_tail_ret copy_const_to_operand_tail_ret_state;
         t = t + 2;
         ret =
           \<lparr>copy_atom_to_operand_tail_n = copy_atom_to_operand_tail_n s,
            copy_atom_to_operand_tail_op = copy_atom_to_operand_tail_op s,
            copy_atom_to_operand_tail_a = copy_atom_to_operand_tail_a s,
            copy_atom_to_operand_tail_ret = copy_atom_to_operand_tail_ret'\<rparr>
        in
         t)
  else (let
         t = t + 1;
         snd'_state_p' = copy_atom_to_operand_tail_a s;
         t = t + 2;
         snd'_state = \<lparr>snd'_state_p = snd'_state_p'\<rparr>;
         snd'_ret_state = snd'_imp snd'_state;
         t = t + snd'_imp_time 0 snd'_state;
         
         copy_var_to_operand_tail_i' = copy_atom_to_operand_tail_n s;
         t = t + 2;
         copy_var_to_operand_tail_op' = copy_atom_to_operand_tail_op s;
         t = t + 2;
         copy_var_to_operand_tail_v' = snd'_state_p snd'_ret_state;
         t = t + 2;
         copy_var_to_operand_tail_ret' = 0;
         t = t + 2;
         copy_var_to_operand_tail_state 
           = \<lparr>copy_var_to_operand_tail_i = copy_var_to_operand_tail_i',
             copy_var_to_operand_tail_op = copy_var_to_operand_tail_op',
             copy_var_to_operand_tail_v = copy_var_to_operand_tail_v',
             copy_var_to_operand_tail_ret = copy_var_to_operand_tail_ret'\<rparr>;
         copy_var_to_operand_tail_ret_state = 
            copy_var_to_operand_tail_imp copy_var_to_operand_tail_state;
         t = t + copy_var_to_operand_tail_imp_time 0 copy_var_to_operand_tail_state;
         copy_atom_to_operand_tail_ret' 
            = copy_var_to_operand_tail_ret copy_var_to_operand_tail_ret_state;
         t = t + 2;
         ret =
           \<lparr>copy_atom_to_operand_tail_n = copy_atom_to_operand_tail_n s,
            copy_atom_to_operand_tail_op = copy_atom_to_operand_tail_op s,
            copy_atom_to_operand_tail_a = copy_atom_to_operand_tail_a s,
            copy_atom_to_operand_tail_ret = copy_atom_to_operand_tail_ret'\<rparr>
        in
         t)
  ))" by auto
termination by (relation "measure (copy_atom_to_operand_tail_n \<circ> snd)", simp)

declare copy_atom_to_operand_tail_imp_time.simps[simp del]

abbreviation "copy_atom_to_operand_tail_IMP_vars \<equiv> 
 {copy_atom_to_operand_tail_ret_str, copy_atom_to_operand_tail_n_str,
 copy_atom_to_operand_tail_op_str, copy_atom_to_operand_tail_a_str,
 copy_atom_to_operand_tail_cond}"

definition "copy_atom_to_operand_tail_imp_to_HOL_state p s\<equiv> 
\<lparr>copy_atom_to_operand_tail_n = s (add_prefix p copy_atom_to_operand_tail_n_str),
copy_atom_to_operand_tail_op = s (add_prefix p copy_atom_to_operand_tail_op_str),
copy_atom_to_operand_tail_a = s (add_prefix p copy_atom_to_operand_tail_a_str),
copy_atom_to_operand_tail_ret = s (add_prefix p copy_atom_to_operand_tail_ret_str)\<rparr>"

lemmas copy_atom_to_operand_tail_state_translators=
  copy_atom_to_operand_tail_imp_to_HOL_state_def
  copy_var_to_operand_tail_imp_to_HOL_state_def
  copy_const_to_operand_tail_imp_to_HOL_state_def
  fst'_imp_to_HOL_state_def snd'_imp_to_HOL_state_def

definition "copy_atom_to_operand_tail_IMP_Minus \<equiv> 
  (fst'_prefix @ fst'_p_str) ::= A (V copy_atom_to_operand_tail_a_str);;
  invoke_subprogram fst'_prefix fst'_IMP_Minus;;
  copy_atom_to_operand_tail_cond ::= A (V (fst'_prefix @ fst'_p_str));;
  IF copy_atom_to_operand_tail_cond\<noteq>0 
  THEN 
    (
    (snd'_prefix @ snd'_p_str) ::= A (V copy_atom_to_operand_tail_a_str);;
    invoke_subprogram snd'_prefix snd'_IMP_Minus;;

    (copy_const_to_operand_tail_prefix @ copy_const_to_operand_tail_i_str)
      ::= A (V copy_atom_to_operand_tail_n_str);;
    (copy_const_to_operand_tail_prefix @ copy_const_to_operand_tail_op_str)
      ::= A (V copy_atom_to_operand_tail_op_str);;
    (copy_const_to_operand_tail_prefix @ copy_const_to_operand_tail_x_str)
      ::= A (V (snd'_prefix @ snd'_p_str));;
    (copy_const_to_operand_tail_prefix @ copy_const_to_operand_tail_ret_str)
      ::= A (N 0);;
    invoke_subprogram copy_const_to_operand_tail_prefix copy_const_to_operand_tail_IMP_Minus;;

    (copy_atom_to_operand_tail_ret_str) ::=
      A (V (copy_const_to_operand_tail_prefix @ copy_const_to_operand_tail_ret_str))
    )
  ELSE 
    (
    (snd'_prefix @ snd'_p_str) ::= A (V copy_atom_to_operand_tail_a_str);;
    invoke_subprogram snd'_prefix snd'_IMP_Minus;;

    (copy_var_to_operand_tail_prefix @ copy_var_to_operand_tail_i_str)
      ::= A (V copy_atom_to_operand_tail_n_str);;
    (copy_var_to_operand_tail_prefix @ copy_var_to_operand_tail_op_str)
      ::= A (V copy_atom_to_operand_tail_op_str);;
    (copy_var_to_operand_tail_prefix @ copy_var_to_operand_tail_v_str)
      ::= A (V (snd'_prefix @ snd'_p_str));;
    (copy_var_to_operand_tail_prefix @ copy_var_to_operand_tail_ret_str)
      ::= A (N 0);;
    invoke_subprogram copy_var_to_operand_tail_prefix copy_var_to_operand_tail_IMP_Minus;;

    (copy_atom_to_operand_tail_ret_str) ::=
      A (V (copy_var_to_operand_tail_prefix @ copy_var_to_operand_tail_ret_str))
    )
  "

lemma copy_atom_to_operand_tail_IMP_Minus_correct_function:
  "(invoke_subprogram p copy_atom_to_operand_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p copy_atom_to_operand_tail_ret_str)
      = copy_atom_to_operand_tail_ret
          (copy_atom_to_operand_tail_imp (copy_atom_to_operand_tail_imp_to_HOL_state p s))"
  apply (simp only: copy_atom_to_operand_tail_imp.simps)
  apply (simp only: copy_atom_to_operand_tail_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule fst'_IMP_Minus_correct[where vars = copy_atom_to_operand_tail_IMP_vars])
  subgoal premises p using p(4) by fastforce
  apply (erule If_E)
    subgoal 
      apply (erule Seq_E)+
      apply (erule snd'_IMP_Minus_correct[where vars = copy_atom_to_operand_tail_IMP_vars])
      subgoal premises p using p (14) by fastforce
      apply (erule copy_const_to_operand_tail_IMP_Minus_correct[where vars = copy_atom_to_operand_tail_IMP_vars])
      subgoal premises p using p (16) by fastforce
      apply (force simp: copy_atom_to_operand_tail_state_translators Let_def)
    done 

    subgoal 
      apply (erule Seq_E)+
      apply (erule snd'_IMP_Minus_correct[where vars = copy_atom_to_operand_tail_IMP_vars])
      subgoal premises p using p (14) by fastforce
      apply (erule copy_var_to_operand_tail_IMP_Minus_correct[where vars = copy_atom_to_operand_tail_IMP_vars])
      subgoal premises p using p (16) by fastforce
      apply (force simp: copy_atom_to_operand_tail_state_translators Let_def)
    done 
  done 

lemma copy_atom_to_operand_tail_IMP_Minus_correct_time:
  "(invoke_subprogram p copy_atom_to_operand_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
    t = (copy_atom_to_operand_tail_imp_time 0 (copy_atom_to_operand_tail_imp_to_HOL_state p s))"
  apply (simp only: copy_atom_to_operand_tail_imp_time.simps)
  apply (simp only: copy_atom_to_operand_tail_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule fst'_IMP_Minus_correct[where vars = copy_atom_to_operand_tail_IMP_vars])
  subgoal premises p using p(7) by fastforce
  apply (erule If_tE)
    subgoal 
      apply (erule Seq_tE)+
      apply (erule snd'_IMP_Minus_correct[where vars = copy_atom_to_operand_tail_IMP_vars])
      subgoal premises p using p (25) by fastforce
      apply (erule copy_const_to_operand_tail_IMP_Minus_correct[where vars = copy_atom_to_operand_tail_IMP_vars])
      subgoal premises p using p (27) by fastforce
      apply (force simp: copy_atom_to_operand_tail_state_translators Let_def)
    done 

    subgoal 
      apply (erule Seq_tE)+
      apply (erule snd'_IMP_Minus_correct[where vars = copy_atom_to_operand_tail_IMP_vars])
      subgoal premises p using p (25) by fastforce
      apply (erule copy_var_to_operand_tail_IMP_Minus_correct[where vars = copy_atom_to_operand_tail_IMP_vars])
      subgoal premises p using p (27) by fastforce
      apply (force simp: copy_atom_to_operand_tail_state_translators Let_def)
    done 
  done 

lemma copy_atom_to_operand_tail_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) copy_atom_to_operand_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (copy_atom_to_operand_tail_imp_time 0 (copy_atom_to_operand_tail_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) copy_atom_to_operand_tail_ret_str) =
          copy_atom_to_operand_tail_ret (copy_atom_to_operand_tail_imp
                                        (copy_atom_to_operand_tail_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using copy_atom_to_operand_tail_IMP_Minus_correct_function 
      copy_atom_to_operand_tail_IMP_Minus_correct_time
       set_mono_prefix
  by (smt (verit, ccfv_SIG) com_add_prefix_valid_subset com_only_vars)

subsection \<open>assign_var_carry\<close>

subsubsection \<open>assign_var_carry_tail_aux1\<close>

fun assign_var_carry_tail_aux1 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "assign_var_carry_tail_aux1 i v a b c =
    (var_bit_to_var_tail(prod_encode (v, i))) ##
    (if a + b + c = 1 \<or> a + b + c = 3 then 1 else 0) ## 0"

record assign_var_carry_tail_aux1_state =
  assign_var_carry_tail_aux1_i::nat
  assign_var_carry_tail_aux1_v::nat
  assign_var_carry_tail_aux1_a::nat
  assign_var_carry_tail_aux1_b::nat
  assign_var_carry_tail_aux1_c::nat
  assign_var_carry_tail_aux1_ret::nat

abbreviation "assign_var_carry_tail_aux1_prefix \<equiv> ''assign_var_carry_tail_aux1.''"
abbreviation "assign_var_carry_tail_aux1_i_str \<equiv> ''i''"
abbreviation "assign_var_carry_tail_aux1_v_str \<equiv> ''v''"
abbreviation "assign_var_carry_tail_aux1_a_str \<equiv> ''a''"
abbreviation "assign_var_carry_tail_aux1_b_str \<equiv> ''b''"
abbreviation "assign_var_carry_tail_aux1_c_str \<equiv> ''c''"
abbreviation "assign_var_carry_tail_aux1_ret_str \<equiv> ''ret''"

definition "assign_var_carry_tail_aux1_state_upd s =
  (let
      EQUAL_neq_zero_a' = assign_var_carry_tail_aux1_a s + assign_var_carry_tail_aux1_b s;
      EQUAL_neq_zero_a' = EQUAL_neq_zero_a' + assign_var_carry_tail_aux1_c s;
      EQUAL_neq_zero_b' = 1;
      EQUAL_neq_zero_ret' = 0;
      EQUAL_neq_zero_state = \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
                              EQUAL_neq_zero_b = EQUAL_neq_zero_b',
                              EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
      EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
      EQUAL_neq_zero_result = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;
      EQUAL_neq_zero_a' = assign_var_carry_tail_aux1_a s + assign_var_carry_tail_aux1_b s;
      EQUAL_neq_zero_a' = EQUAL_neq_zero_a' + assign_var_carry_tail_aux1_c s;
      EQUAL_neq_zero_b' = 3;
      EQUAL_neq_zero_ret' = 0;
      EQUAL_neq_zero_state = \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
                              EQUAL_neq_zero_b = EQUAL_neq_zero_b',
                              EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
      EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
      OR_neq_zero_a' = EQUAL_neq_zero_result;
      OR_neq_zero_b' = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;
      OR_neq_zero_ret' = 0;
      OR_neq_zero_state = \<lparr>OR_neq_zero_a = OR_neq_zero_a',
                           OR_neq_zero_b = OR_neq_zero_b',
                           OR_neq_zero_ret = OR_neq_zero_ret'\<rparr>;
      OR_neq_zero_ret_state = OR_neq_zero_imp OR_neq_zero_state;
      cons_h' = OR_neq_zero_ret OR_neq_zero_ret_state;
      cons_t' = 0;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_result = cons_ret cons_ret_state;
      prod_encode_a' = assign_var_carry_tail_aux1_v s;
      prod_encode_b' = assign_var_carry_tail_aux1_i s;
      prod_encode_ret' = 0;
      prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                           prod_encode_b = prod_encode_b',
                           prod_encode_ret = prod_encode_ret'\<rparr>;
      prod_encode_ret_state = prod_encode_imp prod_encode_state;
      var_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
      var_bit_to_var_tail_ret' = 0;
      var_bit_to_var_tail_state = \<lparr>var_bit_to_var_tail_n = var_bit_to_var_tail_n',
                                   var_bit_to_var_tail_ret = var_bit_to_var_tail_ret'\<rparr>;
      var_bit_to_var_tail_ret_state = var_bit_to_var_tail_imp var_bit_to_var_tail_state;
      cons_h' = var_bit_to_var_tail_ret var_bit_to_var_tail_ret_state;
      cons_t' = cons_result;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      assign_var_carry_tail_aux1_ret' = cons_ret cons_ret_state;
      ret = \<lparr>assign_var_carry_tail_aux1_i = assign_var_carry_tail_aux1_i s,
             assign_var_carry_tail_aux1_v = assign_var_carry_tail_aux1_v s,
             assign_var_carry_tail_aux1_a = assign_var_carry_tail_aux1_a s,
             assign_var_carry_tail_aux1_b = assign_var_carry_tail_aux1_b s,
             assign_var_carry_tail_aux1_c = assign_var_carry_tail_aux1_c s,
             assign_var_carry_tail_aux1_ret = assign_var_carry_tail_aux1_ret'\<rparr>
  in
      ret
)"

function assign_var_carry_tail_aux1_imp ::
  "assign_var_carry_tail_aux1_state \<Rightarrow> assign_var_carry_tail_aux1_state" where
  "assign_var_carry_tail_aux1_imp s =
  (let 
      ret = assign_var_carry_tail_aux1_state_upd s
    in 
      ret
  )"
  by simp+
termination
  by (relation "measure assign_var_carry_tail_aux1_i") simp

declare assign_var_carry_tail_aux1_imp.simps [simp del]

lemma assign_var_carry_tail_aux1_imp_correct[let_function_correctness]:
  "assign_var_carry_tail_aux1_ret (assign_var_carry_tail_aux1_imp s) =
    assign_var_carry_tail_aux1 (assign_var_carry_tail_aux1_i s) (assign_var_carry_tail_aux1_v s)
      (assign_var_carry_tail_aux1_a s) (assign_var_carry_tail_aux1_b s) (assign_var_carry_tail_aux1_c s)"
  apply (simp only: assign_var_carry_tail_aux1_imp.simps Let_def assign_var_carry_tail_aux1_state_upd_def
    EQUAL_neq_zero_imp_correct OR_neq_zero_imp_correct cons_imp_correct prod_encode_imp_correct
    var_bit_to_var_tail_imp_correct)
  by simp   

function assign_var_carry_tail_aux1_imp_time ::
  "nat \<Rightarrow> assign_var_carry_tail_aux1_state \<Rightarrow> nat" where
  "assign_var_carry_tail_aux1_imp_time t s =
  (let
      EQUAL_neq_zero_a' = assign_var_carry_tail_aux1_a s + assign_var_carry_tail_aux1_b s;
      t = t + 2;
      EQUAL_neq_zero_a' = EQUAL_neq_zero_a' + assign_var_carry_tail_aux1_c s;
      t = t + 2;
      EQUAL_neq_zero_b' = 1;
      t = t + 2;
      EQUAL_neq_zero_ret' = 0;
      t = t + 2;
      EQUAL_neq_zero_state = \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
                              EQUAL_neq_zero_b = EQUAL_neq_zero_b',
                              EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
      EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
      t = t + EQUAL_neq_zero_imp_time 0 EQUAL_neq_zero_state;
      EQUAL_neq_zero_result = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;
      t = t + 2;
      EQUAL_neq_zero_a' = assign_var_carry_tail_aux1_a s + assign_var_carry_tail_aux1_b s;
      t = t + 2;
      EQUAL_neq_zero_a' = EQUAL_neq_zero_a' + assign_var_carry_tail_aux1_c s;
      t = t + 2;
      EQUAL_neq_zero_b' = 3;
      t = t + 2;
      EQUAL_neq_zero_ret' = 0;
      t = t + 2;
      EQUAL_neq_zero_state = \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
                              EQUAL_neq_zero_b = EQUAL_neq_zero_b',
                              EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
      EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
      t = t + EQUAL_neq_zero_imp_time 0 EQUAL_neq_zero_state;
      OR_neq_zero_a' = EQUAL_neq_zero_result;
      t = t + 2;
      OR_neq_zero_b' = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;
      t = t + 2;
      OR_neq_zero_ret' = 0;
      t = t + 2;
      OR_neq_zero_state = \<lparr>OR_neq_zero_a = OR_neq_zero_a',
                           OR_neq_zero_b = OR_neq_zero_b',
                           OR_neq_zero_ret = OR_neq_zero_ret'\<rparr>;
      OR_neq_zero_ret_state = OR_neq_zero_imp OR_neq_zero_state;
      t = t + OR_neq_zero_imp_time 0 OR_neq_zero_state;
      cons_h' = OR_neq_zero_ret OR_neq_zero_ret_state;
      t = t + 2;
      cons_t' = 0;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_result = cons_ret cons_ret_state;
      t = t + 2;
      prod_encode_a' = assign_var_carry_tail_aux1_v s;
      t = t + 2;
      prod_encode_b' = assign_var_carry_tail_aux1_i s;
      t = t + 2;
      prod_encode_ret' = 0;
      t = t + 2;
      prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                           prod_encode_b = prod_encode_b',
                           prod_encode_ret = prod_encode_ret'\<rparr>;
      prod_encode_ret_state = prod_encode_imp prod_encode_state;
      t = t + prod_encode_imp_time 0 prod_encode_state;
      var_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
      t = t + 2;
      var_bit_to_var_tail_ret' = 0;
      t = t + 2;
      var_bit_to_var_tail_state = \<lparr>var_bit_to_var_tail_n = var_bit_to_var_tail_n',
                                   var_bit_to_var_tail_ret = var_bit_to_var_tail_ret'\<rparr>;
      var_bit_to_var_tail_ret_state = var_bit_to_var_tail_imp var_bit_to_var_tail_state;
      t = t + var_bit_to_var_tail_imp_time 0 var_bit_to_var_tail_state;
      cons_h' = var_bit_to_var_tail_ret var_bit_to_var_tail_ret_state;
      t = t + 2;
      cons_t' = cons_result;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      assign_var_carry_tail_aux1_ret' = cons_ret cons_ret_state;
      t = t + 2;
      ret = \<lparr>assign_var_carry_tail_aux1_i = assign_var_carry_tail_aux1_i s,
             assign_var_carry_tail_aux1_v = assign_var_carry_tail_aux1_v s,
             assign_var_carry_tail_aux1_a = assign_var_carry_tail_aux1_a s,
             assign_var_carry_tail_aux1_b = assign_var_carry_tail_aux1_b s,
             assign_var_carry_tail_aux1_c = assign_var_carry_tail_aux1_c s,
             assign_var_carry_tail_aux1_ret = assign_var_carry_tail_aux1_ret'\<rparr>
  in
      t
  )"
  by auto
termination
  by (relation "measure (assign_var_carry_tail_aux1_i \<circ> snd)") simp

declare assign_var_carry_tail_aux1_imp_time.simps [simp del]

lemma assign_var_carry_tail_aux1_imp_time_acc:
  "(assign_var_carry_tail_aux1_imp_time (Suc t) s) = Suc (assign_var_carry_tail_aux1_imp_time t s)"
  by (induction t s rule: assign_var_carry_tail_aux1_imp_time.induct)
    ((subst (1 2) assign_var_carry_tail_aux1_imp_time.simps);
      (simp add: assign_var_carry_tail_aux1_state_upd_def Let_def))            

lemma assign_var_carry_tail_aux1_imp_time_acc_2_aux:
  "(assign_var_carry_tail_aux1_imp_time t s) = t + (assign_var_carry_tail_aux1_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: assign_var_carry_tail_aux1_imp_time_acc)+            

lemma assign_var_carry_tail_aux1_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (assign_var_carry_tail_aux1_imp_time t s) = t + (assign_var_carry_tail_aux1_imp_time 0 s)"
  by (rule assign_var_carry_tail_aux1_imp_time_acc_2_aux)            

lemma assign_var_carry_tail_aux1_imp_time_acc_3:
  "(assign_var_carry_tail_aux1_imp_time (a + b) s) = a + (assign_var_carry_tail_aux1_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: assign_var_carry_tail_aux1_imp_time_acc)+            

abbreviation "assign_var_carry_tail_aux1_EQUAL_neq_zero_result \<equiv> ''EQUAL_neq_zero_result''"
abbreviation "assign_var_carry_tail_aux1_cons_result \<equiv> ''cons_result''"

definition assign_var_carry_tail_aux1_IMP_Minus where
  "assign_var_carry_tail_aux1_IMP_Minus \<equiv>
  \<comment> \<open>  EQUAL_neq_zero_a' = assign_var_carry_tail_aux1_a s + assign_var_carry_tail_aux1_b s;\<close>
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_a_str) ::= (Plus (V assign_var_carry_tail_aux1_a_str) (V assign_var_carry_tail_aux1_b_str));;
  \<comment> \<open>  EQUAL_neq_zero_a' = EQUAL_neq_zero_a' + assign_var_carry_tail_aux1_c s;\<close>
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_a_str) ::=
    (Plus (V (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_a_str)) (V assign_var_carry_tail_aux1_c_str));;
  \<comment> \<open>  EQUAL_neq_zero_b' = 1;\<close>
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_b_str) ::= (A (N 1));;
  \<comment> \<open>  EQUAL_neq_zero_ret' = 0;\<close>
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str) ::= (A (N 0));;
  \<comment> \<open>  EQUAL_neq_zero_state = \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',\<close>
  \<comment> \<open>                          EQUAL_neq_zero_b = EQUAL_neq_zero_b',\<close>
  \<comment> \<open>                          EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;\<close>
  \<comment> \<open>  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;\<close>
  (invoke_subprogram EQUAL_neq_zero_prefix EQUAL_neq_zero_IMP_Minus);;
  \<comment> \<open>  EQUAL_neq_zero_result = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;\<close>
  (assign_var_carry_tail_aux1_EQUAL_neq_zero_result) ::= (A (V (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str)));;
  \<comment> \<open>  EQUAL_neq_zero_a' = assign_var_carry_tail_aux1_a s + assign_var_carry_tail_aux1_b s;\<close>
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_a_str) ::= (Plus (V assign_var_carry_tail_aux1_a_str) (V assign_var_carry_tail_aux1_b_str));;
  \<comment> \<open>  EQUAL_neq_zero_a' = EQUAL_neq_zero_a' + assign_var_carry_tail_aux1_c s;\<close>
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_a_str) ::=
    (Plus (V (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_a_str)) (V assign_var_carry_tail_aux1_c_str));;
  \<comment> \<open>  EQUAL_neq_zero_b' = 3;\<close>
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_b_str) ::= (A (N 3));;
  \<comment> \<open>  EQUAL_neq_zero_ret' = 0;\<close>
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str) ::= (A (N 0));;
  \<comment> \<open>  EQUAL_neq_zero_state = \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',\<close>
  \<comment> \<open>                          EQUAL_neq_zero_b = EQUAL_neq_zero_b',\<close>
  \<comment> \<open>                          EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;\<close>
  \<comment> \<open>  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;\<close>
  (invoke_subprogram EQUAL_neq_zero_prefix EQUAL_neq_zero_IMP_Minus);;
  \<comment> \<open>  OR_neq_zero_a' = EQUAL_neq_zero_result;\<close>
  (OR_neq_zero_prefix @ OR_neq_zero_a_str) ::= (A (V assign_var_carry_tail_aux1_EQUAL_neq_zero_result));;
  \<comment> \<open>  OR_neq_zero_b' = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;\<close>
  (OR_neq_zero_prefix @ OR_neq_zero_b_str) ::= (A (V (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str)));;
  \<comment> \<open>  OR_neq_zero_ret' = 0;\<close>
  (OR_neq_zero_prefix @ OR_neq_zero_ret_str) ::= (A (N 0));;
  \<comment> \<open>  OR_neq_zero_state = \<lparr>OR_neq_zero_a = OR_neq_zero_a',\<close>
  \<comment> \<open>                       OR_neq_zero_b = OR_neq_zero_b',\<close>
  \<comment> \<open>                       OR_neq_zero_ret = OR_neq_zero_ret'\<rparr>;\<close>
  \<comment> \<open>  OR_neq_zero_ret_state = OR_neq_zero_imp OR_neq_zero_state;\<close>
  (invoke_subprogram OR_neq_zero_prefix OR_neq_zero_IMP_Minus);;
  \<comment> \<open>  cons_h' = OR_neq_zero_ret OR_neq_zero_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (OR_neq_zero_prefix @ OR_neq_zero_ret_str)));;
  \<comment> \<open>  cons_t' = 0;\<close>
  (cons_prefix @ cons_t_str) ::= (A (N 0));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_result = cons_ret cons_ret_state;\<close>
  (assign_var_carry_tail_aux1_cons_result) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  prod_encode_a' = assign_var_carry_tail_aux1_v s;\<close>
  (prod_encode_prefix @ prod_encode_a_str) ::= (A (V assign_var_carry_tail_aux1_v_str));;
  \<comment> \<open>  prod_encode_b' = assign_var_carry_tail_aux1_i s;\<close>
  (prod_encode_prefix @ prod_encode_b_str) ::= (A (V assign_var_carry_tail_aux1_i_str));;
  \<comment> \<open>  prod_encode_ret' = 0;\<close>
  (prod_encode_prefix @ prod_encode_ret_str) ::= (A (N 0));;
  \<comment> \<open>  prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',\<close>
  \<comment> \<open>                       prod_encode_b = prod_encode_b',\<close>
  \<comment> \<open>                       prod_encode_ret = prod_encode_ret'\<rparr>;\<close>
  \<comment> \<open>  prod_encode_ret_state = prod_encode_imp prod_encode_state;\<close>
  (invoke_subprogram prod_encode_prefix prod_encode_IMP_Minus);;
  \<comment> \<open>  var_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;\<close>
  (var_bit_to_var_tail_prefix @ var_bit_to_var_tail_n_str) ::= (A (V (prod_encode_prefix @ prod_encode_ret_str)));;
  \<comment> \<open>  var_bit_to_var_tail_ret' = 0;\<close>
  (var_bit_to_var_tail_prefix @ var_bit_to_var_tail_ret_str) ::= (A (N 0));;
  \<comment> \<open>  var_bit_to_var_tail_state = \<lparr>var_bit_to_var_tail_n = var_bit_to_var_tail_n',\<close>
  \<comment> \<open>                               var_bit_to_var_tail_ret = var_bit_to_var_tail_ret'\<rparr>;\<close>
  \<comment> \<open>  var_bit_to_var_tail_ret_state = var_bit_to_var_tail_imp var_bit_to_var_tail_state;\<close>
  (invoke_subprogram var_bit_to_var_tail_prefix var_bit_to_var_tail_IMP_Minus);;
  \<comment> \<open>  cons_h' = var_bit_to_var_tail_ret var_bit_to_var_tail_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (var_bit_to_var_tail_prefix @ var_bit_to_var_tail_ret_str)));;
  \<comment> \<open>  cons_t' = cons_result;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V assign_var_carry_tail_aux1_cons_result));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  assign_var_carry_tail_aux1_ret' = cons_ret cons_ret_state;\<close>
  (assign_var_carry_tail_aux1_ret_str) ::= (A (V (cons_prefix @ cons_ret_str)))
  \<comment> \<open>  ret = \<lparr>assign_var_carry_tail_aux1_i = assign_var_carry_tail_aux1_i s,\<close>
  \<comment> \<open>         assign_var_carry_tail_aux1_v = assign_var_carry_tail_aux1_v s,\<close>
  \<comment> \<open>         assign_var_carry_tail_aux1_a = assign_var_carry_tail_aux1_a s,\<close>
  \<comment> \<open>         assign_var_carry_tail_aux1_b = assign_var_carry_tail_aux1_b s,\<close>
  \<comment> \<open>         assign_var_carry_tail_aux1_c = assign_var_carry_tail_aux1_c s,\<close>
  \<comment> \<open>         assign_var_carry_tail_aux1_ret = assign_var_carry_tail_aux1_ret'\<rparr>\<close>
"

abbreviation "assign_var_carry_tail_aux1_IMP_vars\<equiv>
  {assign_var_carry_tail_aux1_i_str, assign_var_carry_tail_aux1_v_str, assign_var_carry_tail_aux1_a_str,
  assign_var_carry_tail_aux1_b_str, assign_var_carry_tail_aux1_c_str, assign_var_carry_tail_aux1_ret_str,
  assign_var_carry_tail_aux1_EQUAL_neq_zero_result, assign_var_carry_tail_aux1_cons_result}"

definition "assign_var_carry_tail_aux1_imp_to_HOL_state p s =
  \<lparr>assign_var_carry_tail_aux1_i = (s (add_prefix p assign_var_carry_tail_aux1_i_str)),
   assign_var_carry_tail_aux1_v = (s (add_prefix p assign_var_carry_tail_aux1_v_str)),
   assign_var_carry_tail_aux1_a = (s (add_prefix p assign_var_carry_tail_aux1_a_str)),
   assign_var_carry_tail_aux1_b = (s (add_prefix p assign_var_carry_tail_aux1_b_str)),
   assign_var_carry_tail_aux1_c = (s (add_prefix p assign_var_carry_tail_aux1_c_str)),
   assign_var_carry_tail_aux1_ret = (s (add_prefix p assign_var_carry_tail_aux1_ret_str))\<rparr>"

lemmas assign_var_carry_tail_aux1_state_translators =
  assign_var_carry_tail_aux1_imp_to_HOL_state_def
  EQUAL_neq_zero_imp_to_HOL_state_def
  OR_neq_zero_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  prod_encode_imp_to_HOL_state_def
  var_bit_to_var_tail_imp_to_HOL_state_def

lemma assign_var_carry_tail_aux1_IMP_Minus_correct_function:
  "(invoke_subprogram p assign_var_carry_tail_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p assign_var_carry_tail_aux1_ret_str)
      = assign_var_carry_tail_aux1_ret
          (assign_var_carry_tail_aux1_imp (assign_var_carry_tail_aux1_imp_to_HOL_state p s))"
  apply(subst assign_var_carry_tail_aux1_imp.simps)
  apply(simp only: assign_var_carry_tail_aux1_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule EQUAL_neq_zero_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux1_IMP_vars"])
  subgoal premises p using p(32) by fastforce
  apply(erule EQUAL_neq_zero_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux1_IMP_vars"])
  subgoal premises p using p(34) by fastforce
  apply(erule OR_neq_zero_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux1_IMP_vars"])
  subgoal premises p using p(36) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux1_IMP_vars"])
  subgoal premises p using p(38) by fastforce
  apply(erule prod_encode_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux1_IMP_vars"])
  subgoal premises p using p(40) by fastforce
  apply(erule var_bit_to_var_tail_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux1_IMP_vars"])
  subgoal premises p using p(42) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux1_IMP_vars"])
  subgoal premises p using p(44) by fastforce
  by(force simp: assign_var_carry_tail_aux1_state_translators
    assign_var_carry_tail_aux1_state_upd_def)

lemma assign_var_carry_tail_aux1_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ assign_var_carry_tail_aux1_pref) assign_var_carry_tail_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix assign_var_carry_tail_aux1_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast 

lemma assign_var_carry_tail_aux1_IMP_Minus_correct_time:
  "(invoke_subprogram p assign_var_carry_tail_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = assign_var_carry_tail_aux1_imp_time 0 (assign_var_carry_tail_aux1_imp_to_HOL_state p s)"
  apply(subst assign_var_carry_tail_aux1_imp_time.simps)
  apply(simp only: assign_var_carry_tail_aux1_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule EQUAL_neq_zero_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux1_IMP_vars"])
  subgoal premises p using p(63) by fastforce
  apply(erule EQUAL_neq_zero_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux1_IMP_vars"])
  subgoal premises p using p(65) by fastforce
  apply(erule OR_neq_zero_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux1_IMP_vars"])
  subgoal premises p using p(67) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux1_IMP_vars"])
  subgoal premises p using p(69) by fastforce
  apply(erule prod_encode_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux1_IMP_vars"])
  subgoal premises p using p(71) by fastforce
  apply(erule var_bit_to_var_tail_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux1_IMP_vars"])
  subgoal premises p using p(73) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux1_IMP_vars"])
  subgoal premises p using p(75) by fastforce
  by(force simp add: Let_def assign_var_carry_tail_aux1_state_translators)   

lemma assign_var_carry_tail_aux1_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) assign_var_carry_tail_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (assign_var_carry_tail_aux1_imp_time 0 (assign_var_carry_tail_aux1_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) assign_var_carry_tail_aux1_ret_str) =
          assign_var_carry_tail_aux1_ret (assign_var_carry_tail_aux1_imp
                                        (assign_var_carry_tail_aux1_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using assign_var_carry_tail_aux1_IMP_Minus_correct_function
    assign_var_carry_tail_aux1_IMP_Minus_correct_time
    assign_var_carry_tail_aux1_IMP_Minus_correct_effects
  by (meson set_mono_prefix) 

subsubsection \<open>assign_var_carry_tail_aux2\<close>

fun assign_var_carry_tail_aux2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "assign_var_carry_tail_aux2 a b c = 
    (1 ## (vname_encode ''carry'') ## (if a + b + c \<ge> 2 then 1 else 0) ## 0) ## 0"

record assign_var_carry_tail_aux2_state =
  assign_var_carry_tail_aux2_a::nat
  assign_var_carry_tail_aux2_b::nat
  assign_var_carry_tail_aux2_c::nat
  assign_var_carry_tail_aux2_ret::nat

abbreviation "assign_var_carry_tail_aux2_prefix \<equiv> ''assign_var_carry_tail_aux2.''"
abbreviation "assign_var_carry_tail_aux2_a_str \<equiv> ''a''"
abbreviation "assign_var_carry_tail_aux2_b_str \<equiv> ''b''"
abbreviation "assign_var_carry_tail_aux2_c_str \<equiv> ''c''"
abbreviation "assign_var_carry_tail_aux2_ret_str \<equiv> ''ret''"

definition "assign_var_carry_tail_aux2_state_upd s =
  (let
      LESS_EQUAL_neq_zero_a' = 2;
      LESS_EQUAL_neq_zero_b' = assign_var_carry_tail_aux2_a s + assign_var_carry_tail_aux2_b s;
      LESS_EQUAL_neq_zero_b' = LESS_EQUAL_neq_zero_b' + assign_var_carry_tail_aux2_c s;
      LESS_EQUAL_neq_zero_ret' = 0;
      LESS_EQUAL_neq_zero_state = \<lparr>LESS_EQUAL_neq_zero_a = LESS_EQUAL_neq_zero_a',
                                   LESS_EQUAL_neq_zero_b = LESS_EQUAL_neq_zero_b',
                                   LESS_EQUAL_neq_zero_ret = LESS_EQUAL_neq_zero_ret'\<rparr>;
      LESS_EQUAL_neq_zero_ret_state = LESS_EQUAL_neq_zero_imp LESS_EQUAL_neq_zero_state;
      cons_h' = LESS_EQUAL_neq_zero_ret LESS_EQUAL_neq_zero_ret_state;
      cons_t' = 0;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_h' = carry_vname_encode_as_nat;
      cons_t' = cons_ret cons_ret_state;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_h' = 1;
      cons_t' = cons_ret cons_ret_state;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_h' = cons_ret cons_ret_state;
      cons_t' = 0;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      assign_var_carry_tail_aux2_ret' = cons_ret cons_ret_state;
      ret = \<lparr>assign_var_carry_tail_aux2_a = assign_var_carry_tail_aux2_a s,
             assign_var_carry_tail_aux2_b = assign_var_carry_tail_aux2_b s,
             assign_var_carry_tail_aux2_c = assign_var_carry_tail_aux2_c s,
             assign_var_carry_tail_aux2_ret = assign_var_carry_tail_aux2_ret'\<rparr>
  in
      ret
)"

function assign_var_carry_tail_aux2_imp ::
  "assign_var_carry_tail_aux2_state \<Rightarrow> assign_var_carry_tail_aux2_state" where
  "assign_var_carry_tail_aux2_imp s =
  (let 
      ret = assign_var_carry_tail_aux2_state_upd s
    in 
      ret
  )"
  by simp+
termination
  by (relation "measure assign_var_carry_tail_aux2_a") simp

declare assign_var_carry_tail_aux2_imp.simps [simp del]

lemma assign_var_carry_tail_aux2_imp_correct[let_function_correctness]:
  "assign_var_carry_tail_aux2_ret (assign_var_carry_tail_aux2_imp s) =
    assign_var_carry_tail_aux2 (assign_var_carry_tail_aux2_a s) (assign_var_carry_tail_aux2_b s)
      (assign_var_carry_tail_aux2_c s)"
  by (simp add: assign_var_carry_tail_aux2_imp.simps Let_def assign_var_carry_tail_aux2_state_upd_def
    LESS_EQUAL_neq_zero_imp_correct cons_imp_correct carry_vname_encode_val)

function assign_var_carry_tail_aux2_imp_time ::
  "nat \<Rightarrow> assign_var_carry_tail_aux2_state \<Rightarrow> nat" where
  "assign_var_carry_tail_aux2_imp_time t s =
  (let
      LESS_EQUAL_neq_zero_a' = 2;
      t = t + 2;
      LESS_EQUAL_neq_zero_b' = assign_var_carry_tail_aux2_a s + assign_var_carry_tail_aux2_b s;
      t = t + 2;
      LESS_EQUAL_neq_zero_b' = LESS_EQUAL_neq_zero_b' + assign_var_carry_tail_aux2_c s;
      t = t + 2;
      LESS_EQUAL_neq_zero_ret' = 0;
      t = t + 2;
      LESS_EQUAL_neq_zero_state = \<lparr>LESS_EQUAL_neq_zero_a = LESS_EQUAL_neq_zero_a',
                                   LESS_EQUAL_neq_zero_b = LESS_EQUAL_neq_zero_b',
                                   LESS_EQUAL_neq_zero_ret = LESS_EQUAL_neq_zero_ret'\<rparr>;
      LESS_EQUAL_neq_zero_ret_state = LESS_EQUAL_neq_zero_imp LESS_EQUAL_neq_zero_state;
      t = t + LESS_EQUAL_neq_zero_imp_time 0 LESS_EQUAL_neq_zero_state;
      cons_h' = LESS_EQUAL_neq_zero_ret LESS_EQUAL_neq_zero_ret_state;
      t = t + 2;
      cons_t' = 0;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_h' = carry_vname_encode_as_nat;
      t = t + 2;
      cons_t' = cons_ret cons_ret_state;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_h' = 1;
      t = t + 2;
      cons_t' = cons_ret cons_ret_state;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_h' = cons_ret cons_ret_state;
      t = t + 2;
      cons_t' = 0;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      assign_var_carry_tail_aux2_ret' = cons_ret cons_ret_state;
      t = t + 2;
      ret = \<lparr>assign_var_carry_tail_aux2_a = assign_var_carry_tail_aux2_a s,
             assign_var_carry_tail_aux2_b = assign_var_carry_tail_aux2_b s,
             assign_var_carry_tail_aux2_c = assign_var_carry_tail_aux2_c s,
             assign_var_carry_tail_aux2_ret = assign_var_carry_tail_aux2_ret'\<rparr>
  in
      t
  )"
  by auto
termination
  by (relation "measure (assign_var_carry_tail_aux2_a \<circ> snd)") simp

declare assign_var_carry_tail_aux2_imp_time.simps [simp del]

lemma assign_var_carry_tail_aux2_imp_time_acc:
  "(assign_var_carry_tail_aux2_imp_time (Suc t) s) = Suc (assign_var_carry_tail_aux2_imp_time t s)"
  by (induction t s rule: assign_var_carry_tail_aux2_imp_time.induct)
    ((subst (1 2) assign_var_carry_tail_aux2_imp_time.simps);
      (simp add: assign_var_carry_tail_aux2_state_upd_def Let_def))            

lemma assign_var_carry_tail_aux2_imp_time_acc_2_aux:
  "(assign_var_carry_tail_aux2_imp_time t s) = t + (assign_var_carry_tail_aux2_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: assign_var_carry_tail_aux2_imp_time_acc)+            

lemma assign_var_carry_tail_aux2_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (assign_var_carry_tail_aux2_imp_time t s) = t + (assign_var_carry_tail_aux2_imp_time 0 s)"
  by (rule assign_var_carry_tail_aux2_imp_time_acc_2_aux)            

lemma assign_var_carry_tail_aux2_imp_time_acc_3:
  "(assign_var_carry_tail_aux2_imp_time (a + b) s) = a + (assign_var_carry_tail_aux2_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: assign_var_carry_tail_aux2_imp_time_acc)+   

definition assign_var_carry_tail_aux2_IMP_Minus where
  "assign_var_carry_tail_aux2_IMP_Minus \<equiv>
  \<comment> \<open>  LESS_EQUAL_neq_zero_a' = 2;\<close>
  (LESS_EQUAL_neq_zero_prefix @ LESS_EQUAL_neq_zero_a_str) ::= (A (N 2));;
  \<comment> \<open>  LESS_EQUAL_neq_zero_b' = assign_var_carry_tail_aux2_a s + assign_var_carry_tail_aux2_b s;\<close>
  (LESS_EQUAL_neq_zero_prefix @ LESS_EQUAL_neq_zero_b_str) ::= (Plus (V assign_var_carry_tail_aux2_a_str) (V assign_var_carry_tail_aux2_b_str));;
  \<comment> \<open>  LESS_EQUAL_neq_zero_b' = LESS_EQUAL_neq_zero_b' + assign_var_carry_tail_aux2_c s;\<close>
  (LESS_EQUAL_neq_zero_prefix @ LESS_EQUAL_neq_zero_b_str) ::= 
    (Plus (V (LESS_EQUAL_neq_zero_prefix @ LESS_EQUAL_neq_zero_b_str)) (V assign_var_carry_tail_aux2_c_str));;
  \<comment> \<open>  LESS_EQUAL_neq_zero_ret' = 0;\<close>
  (LESS_EQUAL_neq_zero_prefix @ LESS_EQUAL_neq_zero_ret_str) ::= (A (N 0));;
  \<comment> \<open>  LESS_EQUAL_neq_zero_state = \<lparr>LESS_EQUAL_neq_zero_a = LESS_EQUAL_neq_zero_a',\<close>
  \<comment> \<open>                               LESS_EQUAL_neq_zero_b = LESS_EQUAL_neq_zero_b',\<close>
  \<comment> \<open>                               LESS_EQUAL_neq_zero_ret = LESS_EQUAL_neq_zero_ret'\<rparr>;\<close>
  \<comment> \<open>  LESS_EQUAL_neq_zero_ret_state = LESS_EQUAL_neq_zero_imp LESS_EQUAL_neq_zero_state;\<close>
  (invoke_subprogram LESS_EQUAL_neq_zero_prefix LESS_EQUAL_neq_zero_IMP_Minus);;
  \<comment> \<open>  cons_h' = LESS_EQUAL_neq_zero_ret LESS_EQUAL_neq_zero_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (LESS_EQUAL_neq_zero_prefix @ LESS_EQUAL_neq_zero_ret_str)));;
  \<comment> \<open>  cons_t' = 0;\<close>
  (cons_prefix @ cons_t_str) ::= (A (N 0));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_h' = carry_vname_encode_as_nat;\<close>
  (cons_prefix @ cons_h_str) ::= (A (N carry_vname_encode_as_nat));;
  \<comment> \<open>  cons_t' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_h' = 1;\<close>
  (cons_prefix @ cons_h_str) ::= (A (N 1));;
  \<comment> \<open>  cons_t' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_h' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_t' = 0;\<close>
  (cons_prefix @ cons_t_str) ::= (A (N 0));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  assign_var_carry_tail_aux2_ret' = cons_ret cons_ret_state;\<close>
  (assign_var_carry_tail_aux2_ret_str) ::= (A (V (cons_prefix @ cons_ret_str)))
  \<comment> \<open>  ret = \<lparr>assign_var_carry_tail_aux2_a = assign_var_carry_tail_aux2_a s,\<close>
  \<comment> \<open>         assign_var_carry_tail_aux2_b = assign_var_carry_tail_aux2_b s,\<close>
  \<comment> \<open>         assign_var_carry_tail_aux2_c = assign_var_carry_tail_aux2_c s,\<close>
  \<comment> \<open>         assign_var_carry_tail_aux2_ret = assign_var_carry_tail_aux2_ret'\<rparr>\<close>
"

abbreviation "assign_var_carry_tail_aux2_IMP_vars\<equiv>
  {assign_var_carry_tail_aux2_a_str, assign_var_carry_tail_aux2_b_str, assign_var_carry_tail_aux2_c_str,
  assign_var_carry_tail_aux2_ret_str}"

definition "assign_var_carry_tail_aux2_imp_to_HOL_state p s =
  \<lparr>assign_var_carry_tail_aux2_a = (s (add_prefix p assign_var_carry_tail_aux2_a_str)),
   assign_var_carry_tail_aux2_b = (s (add_prefix p assign_var_carry_tail_aux2_b_str)),
   assign_var_carry_tail_aux2_c = (s (add_prefix p assign_var_carry_tail_aux2_c_str)),
   assign_var_carry_tail_aux2_ret = (s (add_prefix p assign_var_carry_tail_aux2_ret_str))\<rparr>"

lemmas assign_var_carry_tail_aux2_state_translators =
  assign_var_carry_tail_aux2_imp_to_HOL_state_def
  LESS_EQUAL_neq_zero_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def

lemma assign_var_carry_tail_aux2_IMP_Minus_correct_function:
  "(invoke_subprogram p assign_var_carry_tail_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p assign_var_carry_tail_aux2_ret_str)
      = assign_var_carry_tail_aux2_ret
          (assign_var_carry_tail_aux2_imp (assign_var_carry_tail_aux2_imp_to_HOL_state p s))"
  apply(subst assign_var_carry_tail_aux2_imp.simps)
  apply(simp only: assign_var_carry_tail_aux2_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule LESS_EQUAL_neq_zero_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux2_IMP_vars"])
  subgoal premises p using p(22) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux2_IMP_vars"])
  subgoal premises p using p(24) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux2_IMP_vars"])
  subgoal premises p using p(26) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux2_IMP_vars"])
  subgoal premises p using p(28) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux2_IMP_vars"])
  subgoal premises p using p(30) by fastforce
  by(force simp: assign_var_carry_tail_aux2_state_translators
    assign_var_carry_tail_aux2_state_upd_def)   

lemma assign_var_carry_tail_aux2_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ assign_var_carry_tail_aux2_pref) assign_var_carry_tail_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix assign_var_carry_tail_aux2_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast   

lemma assign_var_carry_tail_aux2_IMP_Minus_correct_time:
  "(invoke_subprogram p assign_var_carry_tail_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = assign_var_carry_tail_aux2_imp_time 0 (assign_var_carry_tail_aux2_imp_to_HOL_state p s)"
  apply(subst assign_var_carry_tail_aux2_imp_time.simps)
  apply(simp only: assign_var_carry_tail_aux2_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule LESS_EQUAL_neq_zero_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux2_IMP_vars"])
  subgoal premises p using p(43) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux2_IMP_vars"])
  subgoal premises p using p(45) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux2_IMP_vars"])
  subgoal premises p using p(47) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux2_IMP_vars"])
  subgoal premises p using p(49) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "assign_var_carry_tail_aux2_IMP_vars"])
  subgoal premises p using p(51) by fastforce
  by(force simp add: Let_def assign_var_carry_tail_aux2_state_translators) 

lemma assign_var_carry_tail_aux2_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) assign_var_carry_tail_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (assign_var_carry_tail_aux2_imp_time 0 (assign_var_carry_tail_aux2_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) assign_var_carry_tail_aux2_ret_str) =
          assign_var_carry_tail_aux2_ret (assign_var_carry_tail_aux2_imp
                                        (assign_var_carry_tail_aux2_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using assign_var_carry_tail_aux2_IMP_Minus_correct_function
    assign_var_carry_tail_aux2_IMP_Minus_correct_time
    assign_var_carry_tail_aux2_IMP_Minus_correct_effects
  by (meson set_mono_prefix)

subsubsection \<open>assign_var_carry_tail\<close>

fun assign_var_carry_tail' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "assign_var_carry_tail' i v a b c = 
    2 ## (1 ## (assign_var_carry_tail_aux1 i v a b c)) ## (assign_var_carry_tail_aux2 a b c)"

lemma assign_var_carry_tail'_correct:
  "assign_var_carry_tail i v a b c = assign_var_carry_tail' i v a b c"
  unfolding assign_var_carry_tail_def
  by (simp only: assign_var_carry_tail'.simps
    assign_var_carry_tail_aux1.simps
    assign_var_carry_tail_aux2.simps)

record assign_var_carry_tail_state =
  assign_var_carry_tail_i::nat
  assign_var_carry_tail_v::nat
  assign_var_carry_tail_a::nat
  assign_var_carry_tail_b::nat
  assign_var_carry_tail_c::nat
  assign_var_carry_tail_ret::nat

abbreviation "assign_var_carry_tail_prefix \<equiv> ''assign_var_carry_tail.''"
abbreviation "assign_var_carry_tail_i_str \<equiv> ''i''"
abbreviation "assign_var_carry_tail_v_str \<equiv> ''v''"
abbreviation "assign_var_carry_tail_a_str \<equiv> ''a''"
abbreviation "assign_var_carry_tail_b_str \<equiv> ''b''"
abbreviation "assign_var_carry_tail_c_str \<equiv> ''c''"
abbreviation "assign_var_carry_tail_ret_str \<equiv> ''ret''"

definition "assign_var_carry_tail_state_upd s =
  (let
      assign_var_carry_tail_aux1_i' = assign_var_carry_tail_i s;
      assign_var_carry_tail_aux1_v' = assign_var_carry_tail_v s;
      assign_var_carry_tail_aux1_a' = assign_var_carry_tail_a s;
      assign_var_carry_tail_aux1_b' = assign_var_carry_tail_b s;
      assign_var_carry_tail_aux1_c' = assign_var_carry_tail_c s;
      assign_var_carry_tail_aux1_ret' = 0;
      assign_var_carry_tail_aux1_state = \<lparr>assign_var_carry_tail_aux1_i = assign_var_carry_tail_aux1_i',
                                          assign_var_carry_tail_aux1_v = assign_var_carry_tail_aux1_v',
                                          assign_var_carry_tail_aux1_a = assign_var_carry_tail_aux1_a',
                                          assign_var_carry_tail_aux1_b = assign_var_carry_tail_aux1_b',
                                          assign_var_carry_tail_aux1_c = assign_var_carry_tail_aux1_c',
                                          assign_var_carry_tail_aux1_ret = assign_var_carry_tail_aux1_ret'\<rparr>;
      assign_var_carry_tail_aux1_ret_state = assign_var_carry_tail_aux1_imp assign_var_carry_tail_aux1_state;
      cons_h' = 1;
      cons_t' = assign_var_carry_tail_aux1_ret assign_var_carry_tail_aux1_ret_state;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_result = cons_ret cons_ret_state;
      assign_var_carry_tail_aux2_a' = assign_var_carry_tail_a s;
      assign_var_carry_tail_aux2_b' = assign_var_carry_tail_b s;
      assign_var_carry_tail_aux2_c' = assign_var_carry_tail_c s;
      assign_var_carry_tail_aux2_ret' = 0;
      assign_var_carry_tail_aux2_state = \<lparr>assign_var_carry_tail_aux2_a = assign_var_carry_tail_aux2_a',
                                          assign_var_carry_tail_aux2_b = assign_var_carry_tail_aux2_b',
                                          assign_var_carry_tail_aux2_c = assign_var_carry_tail_aux2_c',
                                          assign_var_carry_tail_aux2_ret = assign_var_carry_tail_aux2_ret'\<rparr>;
      assign_var_carry_tail_aux2_ret_state = assign_var_carry_tail_aux2_imp assign_var_carry_tail_aux2_state;
      cons_h' = cons_result;
      cons_t' = assign_var_carry_tail_aux2_ret assign_var_carry_tail_aux2_ret_state;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_h' = 2;
      cons_t' = cons_ret cons_ret_state;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      assign_var_carry_tail_ret' = cons_ret cons_ret_state;
      ret = \<lparr>assign_var_carry_tail_i = assign_var_carry_tail_i s,
             assign_var_carry_tail_v = assign_var_carry_tail_v s,
             assign_var_carry_tail_a = assign_var_carry_tail_a s,
             assign_var_carry_tail_b = assign_var_carry_tail_b s,
             assign_var_carry_tail_c = assign_var_carry_tail_c s,
             assign_var_carry_tail_ret = assign_var_carry_tail_ret'\<rparr>
  in
      ret
)"

function assign_var_carry_tail_imp ::
  "assign_var_carry_tail_state \<Rightarrow> assign_var_carry_tail_state" where
  "assign_var_carry_tail_imp s =
  (let 
      ret = assign_var_carry_tail_state_upd s
    in 
      ret
  )"
  by simp+
termination
  by (relation "measure assign_var_carry_tail_i") simp

declare assign_var_carry_tail_imp.simps [simp del]

lemma assign_var_carry_tail_imp_correct[let_function_correctness]:
  "assign_var_carry_tail_ret (assign_var_carry_tail_imp s) =
    assign_var_carry_tail (assign_var_carry_tail_i s) (assign_var_carry_tail_v s) (assign_var_carry_tail_a s)
      (assign_var_carry_tail_b s) (assign_var_carry_tail_c s)"
  apply (simp only: assign_var_carry_tail_imp.simps Let_def assign_var_carry_tail_state_upd_def
    assign_var_carry_tail'_correct assign_var_carry_tail_aux1_imp_correct cons_imp_correct
    assign_var_carry_tail_aux2_imp_correct)
  by simp    

function assign_var_carry_tail_imp_time ::
  "nat \<Rightarrow> assign_var_carry_tail_state \<Rightarrow> nat" where
  "assign_var_carry_tail_imp_time t s =
  (let
      assign_var_carry_tail_aux1_i' = assign_var_carry_tail_i s;
      t = t + 2;
      assign_var_carry_tail_aux1_v' = assign_var_carry_tail_v s;
      t = t + 2;
      assign_var_carry_tail_aux1_a' = assign_var_carry_tail_a s;
      t = t + 2;
      assign_var_carry_tail_aux1_b' = assign_var_carry_tail_b s;
      t = t + 2;
      assign_var_carry_tail_aux1_c' = assign_var_carry_tail_c s;
      t = t + 2;
      assign_var_carry_tail_aux1_ret' = 0;
      t = t + 2;
      assign_var_carry_tail_aux1_state = \<lparr>assign_var_carry_tail_aux1_i = assign_var_carry_tail_aux1_i',
                                          assign_var_carry_tail_aux1_v = assign_var_carry_tail_aux1_v',
                                          assign_var_carry_tail_aux1_a = assign_var_carry_tail_aux1_a',
                                          assign_var_carry_tail_aux1_b = assign_var_carry_tail_aux1_b',
                                          assign_var_carry_tail_aux1_c = assign_var_carry_tail_aux1_c',
                                          assign_var_carry_tail_aux1_ret = assign_var_carry_tail_aux1_ret'\<rparr>;
      assign_var_carry_tail_aux1_ret_state = assign_var_carry_tail_aux1_imp assign_var_carry_tail_aux1_state;
      t = t + assign_var_carry_tail_aux1_imp_time 0 assign_var_carry_tail_aux1_state;
      cons_h' = 1;
      t = t + 2;
      cons_t' = assign_var_carry_tail_aux1_ret assign_var_carry_tail_aux1_ret_state;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_result = cons_ret cons_ret_state;
      t = t + 2;
      assign_var_carry_tail_aux2_a' = assign_var_carry_tail_a s;
      t = t + 2;
      assign_var_carry_tail_aux2_b' = assign_var_carry_tail_b s;
      t = t + 2;
      assign_var_carry_tail_aux2_c' = assign_var_carry_tail_c s;
      t = t + 2;
      assign_var_carry_tail_aux2_ret' = 0;
      t = t + 2;
      assign_var_carry_tail_aux2_state = \<lparr>assign_var_carry_tail_aux2_a = assign_var_carry_tail_aux2_a',
                                          assign_var_carry_tail_aux2_b = assign_var_carry_tail_aux2_b',
                                          assign_var_carry_tail_aux2_c = assign_var_carry_tail_aux2_c',
                                          assign_var_carry_tail_aux2_ret = assign_var_carry_tail_aux2_ret'\<rparr>;
      assign_var_carry_tail_aux2_ret_state = assign_var_carry_tail_aux2_imp assign_var_carry_tail_aux2_state;
      t = t + assign_var_carry_tail_aux2_imp_time 0 assign_var_carry_tail_aux2_state;
      cons_h' = cons_result;
      t = t + 2;
      cons_t' = assign_var_carry_tail_aux2_ret assign_var_carry_tail_aux2_ret_state;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_h' = 2;
      t = t + 2;
      cons_t' = cons_ret cons_ret_state;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      assign_var_carry_tail_ret' = cons_ret cons_ret_state;
      t = t + 2;
      ret = \<lparr>assign_var_carry_tail_i = assign_var_carry_tail_i s,
             assign_var_carry_tail_v = assign_var_carry_tail_v s,
             assign_var_carry_tail_a = assign_var_carry_tail_a s,
             assign_var_carry_tail_b = assign_var_carry_tail_b s,
             assign_var_carry_tail_c = assign_var_carry_tail_c s,
             assign_var_carry_tail_ret = assign_var_carry_tail_ret'\<rparr>
  in
      t
  )"
  by auto
termination
  by (relation "measure (assign_var_carry_tail_i \<circ> snd)") simp

declare assign_var_carry_tail_imp_time.simps [simp del]

lemma assign_var_carry_tail_imp_time_acc:
  "(assign_var_carry_tail_imp_time (Suc t) s) = Suc (assign_var_carry_tail_imp_time t s)"
  by (induction t s rule: assign_var_carry_tail_imp_time.induct)
    ((subst (1 2) assign_var_carry_tail_imp_time.simps);
      (simp add: assign_var_carry_tail_state_upd_def Let_def))            

lemma assign_var_carry_tail_imp_time_acc_2_aux:
  "(assign_var_carry_tail_imp_time t s) = t + (assign_var_carry_tail_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: assign_var_carry_tail_imp_time_acc)+            

lemma assign_var_carry_tail_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (assign_var_carry_tail_imp_time t s) = t + (assign_var_carry_tail_imp_time 0 s)"
  by (rule assign_var_carry_tail_imp_time_acc_2_aux)            

lemma assign_var_carry_tail_imp_time_acc_3:
  "(assign_var_carry_tail_imp_time (a + b) s) = a + (assign_var_carry_tail_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: assign_var_carry_tail_imp_time_acc)+  

abbreviation "assign_var_carry_tail_cons_result \<equiv> ''cons_result''"

definition assign_var_carry_tail_IMP_Minus where
  "assign_var_carry_tail_IMP_Minus \<equiv>
  \<comment> \<open>  assign_var_carry_tail_aux1_i' = assign_var_carry_tail_i s;\<close>
  (assign_var_carry_tail_aux1_prefix @ assign_var_carry_tail_aux1_i_str) ::= (A (V assign_var_carry_tail_i_str));;
  \<comment> \<open>  assign_var_carry_tail_aux1_v' = assign_var_carry_tail_v s;\<close>
  (assign_var_carry_tail_aux1_prefix @ assign_var_carry_tail_aux1_v_str) ::= (A (V assign_var_carry_tail_v_str));;
  \<comment> \<open>  assign_var_carry_tail_aux1_a' = assign_var_carry_tail_a s;\<close>
  (assign_var_carry_tail_aux1_prefix @ assign_var_carry_tail_aux1_a_str) ::= (A (V assign_var_carry_tail_a_str));;
  \<comment> \<open>  assign_var_carry_tail_aux1_b' = assign_var_carry_tail_b s;\<close>
  (assign_var_carry_tail_aux1_prefix @ assign_var_carry_tail_aux1_b_str) ::= (A (V assign_var_carry_tail_b_str));;
  \<comment> \<open>  assign_var_carry_tail_aux1_c' = assign_var_carry_tail_c s;\<close>
  (assign_var_carry_tail_aux1_prefix @ assign_var_carry_tail_aux1_c_str) ::= (A (V assign_var_carry_tail_c_str));;
  \<comment> \<open>  assign_var_carry_tail_aux1_ret' = 0;\<close>
  (assign_var_carry_tail_aux1_prefix @ assign_var_carry_tail_aux1_ret_str) ::= (A (N 0));;
  \<comment> \<open>  assign_var_carry_tail_aux1_state = \<lparr>assign_var_carry_tail_aux1_i = assign_var_carry_tail_aux1_i',\<close>
  \<comment> \<open>                                      assign_var_carry_tail_aux1_v = assign_var_carry_tail_aux1_v',\<close>
  \<comment> \<open>                                      assign_var_carry_tail_aux1_a = assign_var_carry_tail_aux1_a',\<close>
  \<comment> \<open>                                      assign_var_carry_tail_aux1_b = assign_var_carry_tail_aux1_b',\<close>
  \<comment> \<open>                                      assign_var_carry_tail_aux1_c = assign_var_carry_tail_aux1_c',\<close>
  \<comment> \<open>                                      assign_var_carry_tail_aux1_ret = assign_var_carry_tail_aux1_ret'\<rparr>;\<close>
  \<comment> \<open>  assign_var_carry_tail_aux1_ret_state = assign_var_carry_tail_aux1_imp assign_var_carry_tail_aux1_state;\<close>
  (invoke_subprogram assign_var_carry_tail_aux1_prefix assign_var_carry_tail_aux1_IMP_Minus);;
  \<comment> \<open>  cons_h' = 1;\<close>
  (cons_prefix @ cons_h_str) ::= (A (N 1));;
  \<comment> \<open>  cons_t' = assign_var_carry_tail_aux1_ret assign_var_carry_tail_aux1_ret_state;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V (assign_var_carry_tail_aux1_prefix @ assign_var_carry_tail_aux1_ret_str)));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_result = cons_ret cons_ret_state;\<close>
  (assign_var_carry_tail_cons_result) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  assign_var_carry_tail_aux2_a' = assign_var_carry_tail_a s;\<close>
  (assign_var_carry_tail_aux2_prefix @ assign_var_carry_tail_aux2_a_str) ::= (A (V assign_var_carry_tail_a_str));;
  \<comment> \<open>  assign_var_carry_tail_aux2_b' = assign_var_carry_tail_b s;\<close>
  (assign_var_carry_tail_aux2_prefix @ assign_var_carry_tail_aux2_b_str) ::= (A (V assign_var_carry_tail_b_str));;
  \<comment> \<open>  assign_var_carry_tail_aux2_c' = assign_var_carry_tail_c s;\<close>
  (assign_var_carry_tail_aux2_prefix @ assign_var_carry_tail_aux2_c_str) ::= (A (V assign_var_carry_tail_c_str));;
  \<comment> \<open>  assign_var_carry_tail_aux2_ret' = 0;\<close>
  (assign_var_carry_tail_aux2_prefix @ assign_var_carry_tail_aux2_ret_str) ::= (A (N 0));;
  \<comment> \<open>  assign_var_carry_tail_aux2_state = \<lparr>assign_var_carry_tail_aux2_a = assign_var_carry_tail_aux2_a',\<close>
  \<comment> \<open>                                      assign_var_carry_tail_aux2_b = assign_var_carry_tail_aux2_b',\<close>
  \<comment> \<open>                                      assign_var_carry_tail_aux2_c = assign_var_carry_tail_aux2_c',\<close>
  \<comment> \<open>                                      assign_var_carry_tail_aux2_ret = assign_var_carry_tail_aux2_ret'\<rparr>;\<close>
  \<comment> \<open>  assign_var_carry_tail_aux2_ret_state = assign_var_carry_tail_aux2_imp assign_var_carry_tail_aux2_state;\<close>
  (invoke_subprogram assign_var_carry_tail_aux2_prefix assign_var_carry_tail_aux2_IMP_Minus);;
  \<comment> \<open>  cons_h' = cons_result;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V assign_var_carry_tail_cons_result));;
  \<comment> \<open>  cons_t' = assign_var_carry_tail_aux2_ret assign_var_carry_tail_aux2_ret_state;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V (assign_var_carry_tail_aux2_prefix @ assign_var_carry_tail_aux2_ret_str)));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_h' = 2;\<close>
  (cons_prefix @ cons_h_str) ::= (A (N 2));;
  \<comment> \<open>  cons_t' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  assign_var_carry_tail_ret' = cons_ret cons_ret_state;\<close>
  (assign_var_carry_tail_ret_str) ::= (A (V (cons_prefix @ cons_ret_str)))
  \<comment> \<open>  ret = \<lparr>assign_var_carry_tail_i = assign_var_carry_tail_i s,\<close>
  \<comment> \<open>         assign_var_carry_tail_v = assign_var_carry_tail_v s,\<close>
  \<comment> \<open>         assign_var_carry_tail_a = assign_var_carry_tail_a s,\<close>
  \<comment> \<open>         assign_var_carry_tail_b = assign_var_carry_tail_b s,\<close>
  \<comment> \<open>         assign_var_carry_tail_c = assign_var_carry_tail_c s,\<close>
  \<comment> \<open>         assign_var_carry_tail_ret = assign_var_carry_tail_ret'\<rparr>\<close>
"

abbreviation "assign_var_carry_tail_IMP_vars\<equiv>
  {assign_var_carry_tail_i_str, assign_var_carry_tail_v_str, assign_var_carry_tail_a_str,
  assign_var_carry_tail_b_str, assign_var_carry_tail_c_str, assign_var_carry_tail_ret_str,
  assign_var_carry_tail_cons_result}"

definition "assign_var_carry_tail_imp_to_HOL_state p s =
  \<lparr>assign_var_carry_tail_i = (s (add_prefix p assign_var_carry_tail_i_str)),
   assign_var_carry_tail_v = (s (add_prefix p assign_var_carry_tail_v_str)),
   assign_var_carry_tail_a = (s (add_prefix p assign_var_carry_tail_a_str)),
   assign_var_carry_tail_b = (s (add_prefix p assign_var_carry_tail_b_str)),
   assign_var_carry_tail_c = (s (add_prefix p assign_var_carry_tail_c_str)),
   assign_var_carry_tail_ret = (s (add_prefix p assign_var_carry_tail_ret_str))\<rparr>"

lemmas assign_var_carry_tail_state_translators =
  assign_var_carry_tail_imp_to_HOL_state_def
  assign_var_carry_tail_aux1_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  assign_var_carry_tail_aux2_imp_to_HOL_state_def

lemma assign_var_carry_tail_IMP_Minus_correct_function:
  "(invoke_subprogram p assign_var_carry_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p assign_var_carry_tail_ret_str)
      = assign_var_carry_tail_ret
          (assign_var_carry_tail_imp (assign_var_carry_tail_imp_to_HOL_state p s))"
  apply(subst assign_var_carry_tail_imp.simps)
  apply(simp only: assign_var_carry_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule assign_var_carry_tail_aux1_IMP_Minus_correct[where vars = "assign_var_carry_tail_IMP_vars"])
  subgoal premises p using p(26) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "assign_var_carry_tail_IMP_vars"])
  subgoal premises p using p(28) by fastforce
  apply(erule assign_var_carry_tail_aux2_IMP_Minus_correct[where vars = "assign_var_carry_tail_IMP_vars"])
  subgoal premises p using p(30) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "assign_var_carry_tail_IMP_vars"])
  subgoal premises p using p(32) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "assign_var_carry_tail_IMP_vars"])
  subgoal premises p using p(34) by fastforce
  by(force simp: assign_var_carry_tail_state_translators
    assign_var_carry_tail_state_upd_def)  

lemma assign_var_carry_tail_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ assign_var_carry_tail_pref) assign_var_carry_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix assign_var_carry_tail_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast  

lemma assign_var_carry_tail_IMP_Minus_correct_time:
  "(invoke_subprogram p assign_var_carry_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = assign_var_carry_tail_imp_time 0 (assign_var_carry_tail_imp_to_HOL_state p s)"
  apply(subst assign_var_carry_tail_imp_time.simps)
  apply(simp only: assign_var_carry_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule assign_var_carry_tail_aux1_IMP_Minus_correct[where vars = "assign_var_carry_tail_IMP_vars"])
  subgoal premises p using p(51) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "assign_var_carry_tail_IMP_vars"])
  subgoal premises p using p(53) by fastforce
  apply(erule assign_var_carry_tail_aux2_IMP_Minus_correct[where vars = "assign_var_carry_tail_IMP_vars"])
  subgoal premises p using p(55) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "assign_var_carry_tail_IMP_vars"])
  subgoal premises p using p(57) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "assign_var_carry_tail_IMP_vars"])
  subgoal premises p using p(59) by fastforce
  by(force simp add: Let_def assign_var_carry_tail_state_translators)  

lemma assign_var_carry_tail_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) assign_var_carry_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (assign_var_carry_tail_imp_time 0 (assign_var_carry_tail_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) assign_var_carry_tail_ret_str) =
          assign_var_carry_tail_ret (assign_var_carry_tail_imp
                                        (assign_var_carry_tail_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using assign_var_carry_tail_IMP_Minus_correct_function
    assign_var_carry_tail_IMP_Minus_correct_time
    assign_var_carry_tail_IMP_Minus_correct_effects
  by (meson set_mono_prefix)

subsection \<open>full_adder\<close>

subsubsection \<open>full_adder_tail_aux1\<close>

fun full_adder_tail_aux1 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "full_adder_tail_aux1 op_b i v a b = 
    (3 ## (op_b ## 0) ## (assign_var_carry_tail i v a b 1) ## (assign_var_carry_tail i v a b 0) ## 0)"

record full_adder_tail_aux1_state =
  full_adder_tail_aux1_op_b::nat
  full_adder_tail_aux1_i::nat
  full_adder_tail_aux1_v::nat
  full_adder_tail_aux1_a::nat
  full_adder_tail_aux1_b::nat
  full_adder_tail_aux1_ret::nat

abbreviation "full_adder_tail_aux1_prefix \<equiv> ''full_adder_tail_aux1.''"
abbreviation "full_adder_tail_aux1_op_b_str \<equiv> ''op_b''"
abbreviation "full_adder_tail_aux1_i_str \<equiv> ''i''"
abbreviation "full_adder_tail_aux1_v_str \<equiv> ''v''"
abbreviation "full_adder_tail_aux1_a_str \<equiv> ''a''"
abbreviation "full_adder_tail_aux1_b_str \<equiv> ''b''"
abbreviation "full_adder_tail_aux1_ret_str \<equiv> ''ret''"

definition "full_adder_tail_aux1_state_upd s =
  (let
      assign_var_carry_tail_i' = full_adder_tail_aux1_i s;
      assign_var_carry_tail_v' = full_adder_tail_aux1_v s;
      assign_var_carry_tail_a' = full_adder_tail_aux1_a s;
      assign_var_carry_tail_b' = full_adder_tail_aux1_b s;
      assign_var_carry_tail_c' = 0;
      assign_var_carry_tail_ret' = 0;
      assign_var_carry_tail_state = \<lparr>assign_var_carry_tail_i = assign_var_carry_tail_i',
                                     assign_var_carry_tail_v = assign_var_carry_tail_v',
                                     assign_var_carry_tail_a = assign_var_carry_tail_a',
                                     assign_var_carry_tail_b = assign_var_carry_tail_b',
                                     assign_var_carry_tail_c = assign_var_carry_tail_c',
                                     assign_var_carry_tail_ret = assign_var_carry_tail_ret'\<rparr>;
      assign_var_carry_tail_ret_state = assign_var_carry_tail_imp assign_var_carry_tail_state;
      cons_h' = assign_var_carry_tail_ret assign_var_carry_tail_ret_state;
      cons_t' = 0;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_result = cons_ret cons_ret_state;
      assign_var_carry_tail_i' = full_adder_tail_aux1_i s;
      assign_var_carry_tail_v' = full_adder_tail_aux1_v s;
      assign_var_carry_tail_a' = full_adder_tail_aux1_a s;
      assign_var_carry_tail_b' = full_adder_tail_aux1_b s;
      assign_var_carry_tail_c' = 1;
      assign_var_carry_tail_ret' = 0;
      assign_var_carry_tail_state = \<lparr>assign_var_carry_tail_i = assign_var_carry_tail_i',
                                     assign_var_carry_tail_v = assign_var_carry_tail_v',
                                     assign_var_carry_tail_a = assign_var_carry_tail_a',
                                     assign_var_carry_tail_b = assign_var_carry_tail_b',
                                     assign_var_carry_tail_c = assign_var_carry_tail_c',
                                     assign_var_carry_tail_ret = assign_var_carry_tail_ret'\<rparr>;
      assign_var_carry_tail_ret_state = assign_var_carry_tail_imp assign_var_carry_tail_state;
      cons_h' = assign_var_carry_tail_ret assign_var_carry_tail_ret_state;
      cons_t' = cons_result;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;      
      cons_result = cons_ret cons_ret_state;
      cons_h' = full_adder_tail_aux1_op_b s;
      cons_t' = 0;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_h' = cons_ret cons_ret_state;
      cons_t' = cons_result;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_h' = 3;
      cons_t' = cons_ret cons_ret_state;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      full_adder_tail_aux1_ret' = cons_ret cons_ret_state;
      ret = \<lparr>full_adder_tail_aux1_op_b = full_adder_tail_aux1_op_b s,
             full_adder_tail_aux1_i = full_adder_tail_aux1_i s,
             full_adder_tail_aux1_v = full_adder_tail_aux1_v s,
             full_adder_tail_aux1_a = full_adder_tail_aux1_a s,
             full_adder_tail_aux1_b = full_adder_tail_aux1_b s,
             full_adder_tail_aux1_ret = full_adder_tail_aux1_ret'\<rparr>
  in
      ret
)"

function full_adder_tail_aux1_imp ::
  "full_adder_tail_aux1_state \<Rightarrow> full_adder_tail_aux1_state" where
  "full_adder_tail_aux1_imp s =
  (let 
      ret = full_adder_tail_aux1_state_upd s
    in 
      ret
  )"
  by simp+
termination
  by (relation "measure full_adder_tail_aux1_op_b") simp

declare full_adder_tail_aux1_imp.simps [simp del]

lemma full_adder_tail_aux1_imp_correct[let_function_correctness]:
  "full_adder_tail_aux1_ret (full_adder_tail_aux1_imp s) =
    full_adder_tail_aux1 (full_adder_tail_aux1_op_b s) (full_adder_tail_aux1_i s) (full_adder_tail_aux1_v s)
      (full_adder_tail_aux1_a s) (full_adder_tail_aux1_b s)"
  apply (simp only: full_adder_tail_aux1_imp.simps Let_def full_adder_tail_aux1_state_upd_def
    assign_var_carry_tail_imp_correct cons_imp_correct)
  by simp  

function full_adder_tail_aux1_imp_time ::
  "nat \<Rightarrow> full_adder_tail_aux1_state \<Rightarrow> nat" where
  "full_adder_tail_aux1_imp_time t s =
  (let
      assign_var_carry_tail_i' = full_adder_tail_aux1_i s;
      t = t + 2;
      assign_var_carry_tail_v' = full_adder_tail_aux1_v s;
      t = t + 2;
      assign_var_carry_tail_a' = full_adder_tail_aux1_a s;
      t = t + 2;
      assign_var_carry_tail_b' = full_adder_tail_aux1_b s;
      t = t + 2;
      assign_var_carry_tail_c' = 0;
      t = t + 2;
      assign_var_carry_tail_ret' = 0;
      t = t + 2;
      assign_var_carry_tail_state = \<lparr>assign_var_carry_tail_i = assign_var_carry_tail_i',
                                     assign_var_carry_tail_v = assign_var_carry_tail_v',
                                     assign_var_carry_tail_a = assign_var_carry_tail_a',
                                     assign_var_carry_tail_b = assign_var_carry_tail_b',
                                     assign_var_carry_tail_c = assign_var_carry_tail_c',
                                     assign_var_carry_tail_ret = assign_var_carry_tail_ret'\<rparr>;
      assign_var_carry_tail_ret_state = assign_var_carry_tail_imp assign_var_carry_tail_state;
      t = t + assign_var_carry_tail_imp_time 0 assign_var_carry_tail_state;
      cons_h' = assign_var_carry_tail_ret assign_var_carry_tail_ret_state;
      t = t + 2;
      cons_t' = 0;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_result = cons_ret cons_ret_state;
      t = t + 2;
      assign_var_carry_tail_i' = full_adder_tail_aux1_i s;
      t = t + 2;
      assign_var_carry_tail_v' = full_adder_tail_aux1_v s;
      t = t + 2;
      assign_var_carry_tail_a' = full_adder_tail_aux1_a s;
      t = t + 2;
      assign_var_carry_tail_b' = full_adder_tail_aux1_b s;
      t = t + 2;
      assign_var_carry_tail_c' = 1;
      t = t + 2;
      assign_var_carry_tail_ret' = 0;
      t = t + 2;
      assign_var_carry_tail_state = \<lparr>assign_var_carry_tail_i = assign_var_carry_tail_i',
                                     assign_var_carry_tail_v = assign_var_carry_tail_v',
                                     assign_var_carry_tail_a = assign_var_carry_tail_a',
                                     assign_var_carry_tail_b = assign_var_carry_tail_b',
                                     assign_var_carry_tail_c = assign_var_carry_tail_c',
                                     assign_var_carry_tail_ret = assign_var_carry_tail_ret'\<rparr>;
      assign_var_carry_tail_ret_state = assign_var_carry_tail_imp assign_var_carry_tail_state;
      t = t + assign_var_carry_tail_imp_time 0 assign_var_carry_tail_state;
      cons_h' = assign_var_carry_tail_ret assign_var_carry_tail_ret_state;
      t = t + 2;
      cons_t' = cons_result;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_result = cons_ret cons_ret_state;
      t = t + 2;
      cons_h' = full_adder_tail_aux1_op_b s;
      t = t + 2;
      cons_t' = 0;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_h' = cons_ret cons_ret_state;
      t = t + 2;
      cons_t' = cons_result;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_h' = 3;
      t = t + 2;
      cons_t' = cons_ret cons_ret_state;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      full_adder_tail_aux1_ret' = cons_ret cons_ret_state;
      t = t + 2;
      ret = \<lparr>full_adder_tail_aux1_op_b = full_adder_tail_aux1_op_b s,
             full_adder_tail_aux1_i = full_adder_tail_aux1_i s,
             full_adder_tail_aux1_v = full_adder_tail_aux1_v s,
             full_adder_tail_aux1_a = full_adder_tail_aux1_a s,
             full_adder_tail_aux1_b = full_adder_tail_aux1_b s,
             full_adder_tail_aux1_ret = full_adder_tail_aux1_ret'\<rparr>
  in
      t
  )"
  by auto
termination
  by (relation "measure (full_adder_tail_aux1_op_b \<circ> snd)") simp

declare full_adder_tail_aux1_imp_time.simps [simp del]

lemma full_adder_tail_aux1_imp_time_acc:
  "(full_adder_tail_aux1_imp_time (Suc t) s) = Suc (full_adder_tail_aux1_imp_time t s)"
  by (induction t s rule: full_adder_tail_aux1_imp_time.induct)
    ((subst (1 2) full_adder_tail_aux1_imp_time.simps);
      (simp add: full_adder_tail_aux1_state_upd_def Let_def))            

lemma full_adder_tail_aux1_imp_time_acc_2_aux:
  "(full_adder_tail_aux1_imp_time t s) = t + (full_adder_tail_aux1_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: full_adder_tail_aux1_imp_time_acc)+            

lemma full_adder_tail_aux1_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (full_adder_tail_aux1_imp_time t s) = t + (full_adder_tail_aux1_imp_time 0 s)"
  by (rule full_adder_tail_aux1_imp_time_acc_2_aux)            

lemma full_adder_tail_aux1_imp_time_acc_3:
  "(full_adder_tail_aux1_imp_time (a + b) s) = a + (full_adder_tail_aux1_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: full_adder_tail_aux1_imp_time_acc)+   

abbreviation "full_adder_tail_aux1_cons_result \<equiv> ''cons_result''"

definition full_adder_tail_aux1_IMP_Minus where
  "full_adder_tail_aux1_IMP_Minus \<equiv>
  \<comment> \<open>  assign_var_carry_tail_i' = full_adder_tail_aux1_i s;\<close>
  (assign_var_carry_tail_prefix @ assign_var_carry_tail_i_str) ::= (A (V full_adder_tail_aux1_i_str));;
  \<comment> \<open>  assign_var_carry_tail_v' = full_adder_tail_aux1_v s;\<close>
  (assign_var_carry_tail_prefix @ assign_var_carry_tail_v_str) ::= (A (V full_adder_tail_aux1_v_str));;
  \<comment> \<open>  assign_var_carry_tail_a' = full_adder_tail_aux1_a s;\<close>
  (assign_var_carry_tail_prefix @ assign_var_carry_tail_a_str) ::= (A (V full_adder_tail_aux1_a_str));;
  \<comment> \<open>  assign_var_carry_tail_b' = full_adder_tail_aux1_b s;\<close>
  (assign_var_carry_tail_prefix @ assign_var_carry_tail_b_str) ::= (A (V full_adder_tail_aux1_b_str));;
  \<comment> \<open>  assign_var_carry_tail_c' = 0;\<close>
  (assign_var_carry_tail_prefix @ assign_var_carry_tail_c_str) ::= (A (N 0));;
  \<comment> \<open>  assign_var_carry_tail_ret' = 0;\<close>
  (assign_var_carry_tail_prefix @ assign_var_carry_tail_ret_str) ::= (A (N 0));;
  \<comment> \<open>  assign_var_carry_tail_state = \<lparr>assign_var_carry_tail_i = assign_var_carry_tail_i',\<close>
  \<comment> \<open>                                 assign_var_carry_tail_v = assign_var_carry_tail_v',\<close>
  \<comment> \<open>                                 assign_var_carry_tail_a = assign_var_carry_tail_a',\<close>
  \<comment> \<open>                                 assign_var_carry_tail_b = assign_var_carry_tail_b',\<close>
  \<comment> \<open>                                 assign_var_carry_tail_c = assign_var_carry_tail_c',\<close>
  \<comment> \<open>                                 assign_var_carry_tail_ret = assign_var_carry_tail_ret'\<rparr>;\<close>
  \<comment> \<open>  assign_var_carry_tail_ret_state = assign_var_carry_tail_imp assign_var_carry_tail_state;\<close>
  (invoke_subprogram assign_var_carry_tail_prefix assign_var_carry_tail_IMP_Minus);;
  \<comment> \<open>  cons_h' = assign_var_carry_tail_ret assign_var_carry_tail_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (assign_var_carry_tail_prefix @ assign_var_carry_tail_ret_str)));;
  \<comment> \<open>  cons_t' = 0;\<close>
  (cons_prefix @ cons_t_str) ::= (A (N 0));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_result = cons_ret cons_ret_state;\<close>
  (full_adder_tail_aux1_cons_result) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  assign_var_carry_tail_i' = full_adder_tail_aux1_i s;\<close>
  (assign_var_carry_tail_prefix @ assign_var_carry_tail_i_str) ::= (A (V full_adder_tail_aux1_i_str));;
  \<comment> \<open>  assign_var_carry_tail_v' = full_adder_tail_aux1_v s;\<close>
  (assign_var_carry_tail_prefix @ assign_var_carry_tail_v_str) ::= (A (V full_adder_tail_aux1_v_str));;
  \<comment> \<open>  assign_var_carry_tail_a' = full_adder_tail_aux1_a s;\<close>
  (assign_var_carry_tail_prefix @ assign_var_carry_tail_a_str) ::= (A (V full_adder_tail_aux1_a_str));;
  \<comment> \<open>  assign_var_carry_tail_b' = full_adder_tail_aux1_b s;\<close>
  (assign_var_carry_tail_prefix @ assign_var_carry_tail_b_str) ::= (A (V full_adder_tail_aux1_b_str));;
  \<comment> \<open>  assign_var_carry_tail_c' = 1;\<close>
  (assign_var_carry_tail_prefix @ assign_var_carry_tail_c_str) ::= (A (N 1));;
  \<comment> \<open>  assign_var_carry_tail_ret' = 0;\<close>
  (assign_var_carry_tail_prefix @ assign_var_carry_tail_ret_str) ::= (A (N 0));;
  \<comment> \<open>  assign_var_carry_tail_state = \<lparr>assign_var_carry_tail_i = assign_var_carry_tail_i',\<close>
  \<comment> \<open>                                 assign_var_carry_tail_v = assign_var_carry_tail_v',\<close>
  \<comment> \<open>                                 assign_var_carry_tail_a = assign_var_carry_tail_a',\<close>
  \<comment> \<open>                                 assign_var_carry_tail_b = assign_var_carry_tail_b',\<close>
  \<comment> \<open>                                 assign_var_carry_tail_c = assign_var_carry_tail_c',\<close>
  \<comment> \<open>                                 assign_var_carry_tail_ret = assign_var_carry_tail_ret'\<rparr>;\<close>
  \<comment> \<open>  assign_var_carry_tail_ret_state = assign_var_carry_tail_imp assign_var_carry_tail_state;\<close>
  (invoke_subprogram assign_var_carry_tail_prefix assign_var_carry_tail_IMP_Minus);;
  \<comment> \<open>  cons_h' = assign_var_carry_tail_ret assign_var_carry_tail_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (assign_var_carry_tail_prefix @ assign_var_carry_tail_ret_str)));;
  \<comment> \<open>  cons_t' = cons_result;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V full_adder_tail_aux1_cons_result));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_result = cons_ret cons_ret_state;\<close>
  (full_adder_tail_aux1_cons_result) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_h' = full_adder_tail_aux1_op_b s;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V full_adder_tail_aux1_op_b_str));;
  \<comment> \<open>  cons_t' = 0;\<close>
  (cons_prefix @ cons_t_str) ::= (A (N 0));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_h' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_t' = cons_result;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V full_adder_tail_aux1_cons_result));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_h' = 3;\<close>
  (cons_prefix @ cons_h_str) ::= (A (N 3));;
  \<comment> \<open>  cons_t' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  full_adder_tail_aux1_ret' = cons_ret cons_ret_state;\<close>
  (full_adder_tail_aux1_ret_str) ::= (A (V (cons_prefix @ cons_ret_str)))
  \<comment> \<open>  ret = \<lparr>full_adder_tail_aux1_op_b = full_adder_tail_aux1_op_b s,\<close>
  \<comment> \<open>         full_adder_tail_aux1_i = full_adder_tail_aux1_i s,\<close>
  \<comment> \<open>         full_adder_tail_aux1_v = full_adder_tail_aux1_v s,\<close>
  \<comment> \<open>         full_adder_tail_aux1_a = full_adder_tail_aux1_a s,\<close>
  \<comment> \<open>         full_adder_tail_aux1_b = full_adder_tail_aux1_b s,\<close>
  \<comment> \<open>         full_adder_tail_aux1_ret = full_adder_tail_aux1_ret'\<rparr>\<close>
"

abbreviation "full_adder_tail_aux1_IMP_vars \<equiv>
  {full_adder_tail_aux1_op_b_str, full_adder_tail_aux1_i_str, full_adder_tail_aux1_v_str,
  full_adder_tail_aux1_a_str, full_adder_tail_aux1_b_str, full_adder_tail_aux1_ret_str,
  full_adder_tail_aux1_cons_result}"

definition "full_adder_tail_aux1_imp_to_HOL_state p s =
  \<lparr>full_adder_tail_aux1_op_b = (s (add_prefix p full_adder_tail_aux1_op_b_str)),
   full_adder_tail_aux1_i = (s (add_prefix p full_adder_tail_aux1_i_str)),
   full_adder_tail_aux1_v = (s (add_prefix p full_adder_tail_aux1_v_str)),
   full_adder_tail_aux1_a = (s (add_prefix p full_adder_tail_aux1_a_str)),
   full_adder_tail_aux1_b = (s (add_prefix p full_adder_tail_aux1_b_str)),
   full_adder_tail_aux1_ret = (s (add_prefix p full_adder_tail_aux1_ret_str))\<rparr>"

lemmas full_adder_tail_aux1_state_translators =
  full_adder_tail_aux1_imp_to_HOL_state_def
  assign_var_carry_tail_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def

lemma full_adder_tail_aux1_IMP_Minus_correct_function:
  "(invoke_subprogram p full_adder_tail_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p full_adder_tail_aux1_ret_str)
      = full_adder_tail_aux1_ret
          (full_adder_tail_aux1_imp (full_adder_tail_aux1_imp_to_HOL_state p s))"
  apply(subst full_adder_tail_aux1_imp.simps)
  apply(simp only: full_adder_tail_aux1_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule assign_var_carry_tail_IMP_Minus_correct[where vars = "full_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(37) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(39) by fastforce
  apply(erule assign_var_carry_tail_IMP_Minus_correct[where vars = "full_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(41) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(43) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(45) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(47) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(49) by fastforce
  by(force simp: full_adder_tail_aux1_state_translators
    full_adder_tail_aux1_state_upd_def)   

lemma full_adder_tail_aux1_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ full_adder_tail_aux1_pref) full_adder_tail_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix full_adder_tail_aux1_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast  

lemma full_adder_tail_aux1_IMP_Minus_correct_time:
  "(invoke_subprogram p full_adder_tail_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = full_adder_tail_aux1_imp_time 0 (full_adder_tail_aux1_imp_to_HOL_state p s)"
  apply(subst full_adder_tail_aux1_imp_time.simps)
  apply(simp only: full_adder_tail_aux1_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule assign_var_carry_tail_IMP_Minus_correct[where vars = "full_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(73) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(75) by fastforce
  apply(erule assign_var_carry_tail_IMP_Minus_correct[where vars = "full_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(77) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(79) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(81) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(83) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(85) by fastforce
  by(force simp add: Let_def full_adder_tail_aux1_state_translators) 

lemma full_adder_tail_aux1_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) full_adder_tail_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (full_adder_tail_aux1_imp_time 0 (full_adder_tail_aux1_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) full_adder_tail_aux1_ret_str) =
          full_adder_tail_aux1_ret (full_adder_tail_aux1_imp
                                        (full_adder_tail_aux1_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using full_adder_tail_aux1_IMP_Minus_correct_function
    full_adder_tail_aux1_IMP_Minus_correct_time
    full_adder_tail_aux1_IMP_Minus_correct_effects
  by (meson set_mono_prefix)

subsubsection \<open>full_adder_tail_aux2\<close>

fun full_adder_tail_aux2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "full_adder_tail_aux2 op_b i v a = 
    (3 ## ((vname_encode ''carry'') ## 0) ## 
    (full_adder_tail_aux1 op_b i v a 1) ##
    (full_adder_tail_aux1 op_b i v a 0) ## 0)"

record full_adder_tail_aux2_state =
  full_adder_tail_aux2_op_b::nat
  full_adder_tail_aux2_i::nat
  full_adder_tail_aux2_v::nat
  full_adder_tail_aux2_a::nat
  full_adder_tail_aux2_ret::nat

abbreviation "full_adder_tail_aux2_prefix \<equiv> ''full_adder_tail_aux2.''"
abbreviation "full_adder_tail_aux2_op_b_str \<equiv> ''op_b''"
abbreviation "full_adder_tail_aux2_i_str \<equiv> ''i''"
abbreviation "full_adder_tail_aux2_v_str \<equiv> ''v''"
abbreviation "full_adder_tail_aux2_a_str \<equiv> ''a''"
abbreviation "full_adder_tail_aux2_ret_str \<equiv> ''ret''"

definition "full_adder_tail_aux2_state_upd s =
  (let
      full_adder_tail_aux1_op_b' = full_adder_tail_aux2_op_b s;
      full_adder_tail_aux1_i' = full_adder_tail_aux2_i s;
      full_adder_tail_aux1_v' = full_adder_tail_aux2_v s;
      full_adder_tail_aux1_a' = full_adder_tail_aux2_a s;
      full_adder_tail_aux1_b' = 0;
      full_adder_tail_aux1_ret' = 0;
      full_adder_tail_aux1_state = \<lparr>full_adder_tail_aux1_op_b = full_adder_tail_aux1_op_b',
                                    full_adder_tail_aux1_i = full_adder_tail_aux1_i',
                                    full_adder_tail_aux1_v = full_adder_tail_aux1_v',
                                    full_adder_tail_aux1_a = full_adder_tail_aux1_a',
                                    full_adder_tail_aux1_b = full_adder_tail_aux1_b',
                                    full_adder_tail_aux1_ret = full_adder_tail_aux1_ret'\<rparr>;
      full_adder_tail_aux1_ret_state = full_adder_tail_aux1_imp full_adder_tail_aux1_state;
      cons_h' = full_adder_tail_aux1_ret full_adder_tail_aux1_ret_state;
      cons_t' = 0;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_result = cons_ret cons_ret_state;
      full_adder_tail_aux1_op_b' = full_adder_tail_aux2_op_b s;
      full_adder_tail_aux1_i' = full_adder_tail_aux2_i s;
      full_adder_tail_aux1_v' = full_adder_tail_aux2_v s;
      full_adder_tail_aux1_a' = full_adder_tail_aux2_a s;
      full_adder_tail_aux1_b' = 1;
      full_adder_tail_aux1_ret' = 0;
      full_adder_tail_aux1_state = \<lparr>full_adder_tail_aux1_op_b = full_adder_tail_aux1_op_b',
                                    full_adder_tail_aux1_i = full_adder_tail_aux1_i',
                                    full_adder_tail_aux1_v = full_adder_tail_aux1_v',
                                    full_adder_tail_aux1_a = full_adder_tail_aux1_a',
                                    full_adder_tail_aux1_b = full_adder_tail_aux1_b',
                                    full_adder_tail_aux1_ret = full_adder_tail_aux1_ret'\<rparr>;
      full_adder_tail_aux1_ret_state = full_adder_tail_aux1_imp full_adder_tail_aux1_state;
      cons_h' = full_adder_tail_aux1_ret full_adder_tail_aux1_ret_state;
      cons_t' = cons_result;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;      
      cons_result = cons_ret cons_ret_state;
      cons_h' = carry_vname_encode_as_nat;
      cons_t' = 0;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_h' = cons_ret cons_ret_state;
      cons_t' = cons_result;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_h' = 3;
      cons_t' = cons_ret cons_ret_state;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      full_adder_tail_aux2_ret' = cons_ret cons_ret_state;
      ret = \<lparr>full_adder_tail_aux2_op_b = full_adder_tail_aux2_op_b s,
             full_adder_tail_aux2_i = full_adder_tail_aux2_i s,
             full_adder_tail_aux2_v = full_adder_tail_aux2_v s,
             full_adder_tail_aux2_a = full_adder_tail_aux2_a s,
             full_adder_tail_aux2_ret = full_adder_tail_aux2_ret'\<rparr>
  in
      ret
)"

function full_adder_tail_aux2_imp ::
  "full_adder_tail_aux2_state \<Rightarrow> full_adder_tail_aux2_state" where
  "full_adder_tail_aux2_imp s =
  (let 
      ret = full_adder_tail_aux2_state_upd s
    in 
      ret
  )"
  by simp+
termination
  by (relation "measure full_adder_tail_aux2_op_b") simp

declare full_adder_tail_aux2_imp.simps [simp del]

lemma full_adder_tail_aux2_imp_correct[let_function_correctness]:
  "full_adder_tail_aux2_ret (full_adder_tail_aux2_imp s) =
    full_adder_tail_aux2 (full_adder_tail_aux2_op_b s) (full_adder_tail_aux2_i s) (full_adder_tail_aux2_v s)
      (full_adder_tail_aux2_a s)"
  apply (simp only: full_adder_tail_aux2_imp.simps Let_def full_adder_tail_aux2_state_upd_def
  full_adder_tail_aux1_imp_correct cons_imp_correct carry_vname_encode_val full_adder_tail_aux2.simps)
  by simp

function full_adder_tail_aux2_imp_time ::
  "nat \<Rightarrow> full_adder_tail_aux2_state \<Rightarrow> nat" where
  "full_adder_tail_aux2_imp_time t s =
  (let
      full_adder_tail_aux1_op_b' = full_adder_tail_aux2_op_b s;
      t = t + 2;
      full_adder_tail_aux1_i' = full_adder_tail_aux2_i s;
      t = t + 2;
      full_adder_tail_aux1_v' = full_adder_tail_aux2_v s;
      t = t + 2;
      full_adder_tail_aux1_a' = full_adder_tail_aux2_a s;
      t = t + 2;
      full_adder_tail_aux1_b' = 0;
      t = t + 2;
      full_adder_tail_aux1_ret' = 0;
      t = t + 2;
      full_adder_tail_aux1_state = \<lparr>full_adder_tail_aux1_op_b = full_adder_tail_aux1_op_b',
                                    full_adder_tail_aux1_i = full_adder_tail_aux1_i',
                                    full_adder_tail_aux1_v = full_adder_tail_aux1_v',
                                    full_adder_tail_aux1_a = full_adder_tail_aux1_a',
                                    full_adder_tail_aux1_b = full_adder_tail_aux1_b',
                                    full_adder_tail_aux1_ret = full_adder_tail_aux1_ret'\<rparr>;
      full_adder_tail_aux1_ret_state = full_adder_tail_aux1_imp full_adder_tail_aux1_state;
      t = t + full_adder_tail_aux1_imp_time 0 full_adder_tail_aux1_state;
      cons_h' = full_adder_tail_aux1_ret full_adder_tail_aux1_ret_state;
      t = t + 2;
      cons_t' = 0;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_result = cons_ret cons_ret_state;
      t = t + 2;
      full_adder_tail_aux1_op_b' = full_adder_tail_aux2_op_b s;
      t = t + 2;
      full_adder_tail_aux1_i' = full_adder_tail_aux2_i s;
      t = t + 2;
      full_adder_tail_aux1_v' = full_adder_tail_aux2_v s;
      t = t + 2;
      full_adder_tail_aux1_a' = full_adder_tail_aux2_a s;
      t = t + 2;
      full_adder_tail_aux1_b' = 1;
      t = t + 2;
      full_adder_tail_aux1_ret' = 0;
      t = t + 2;
      full_adder_tail_aux1_state = \<lparr>full_adder_tail_aux1_op_b = full_adder_tail_aux1_op_b',
                                    full_adder_tail_aux1_i = full_adder_tail_aux1_i',
                                    full_adder_tail_aux1_v = full_adder_tail_aux1_v',
                                    full_adder_tail_aux1_a = full_adder_tail_aux1_a',
                                    full_adder_tail_aux1_b = full_adder_tail_aux1_b',
                                    full_adder_tail_aux1_ret = full_adder_tail_aux1_ret'\<rparr>;
      full_adder_tail_aux1_ret_state = full_adder_tail_aux1_imp full_adder_tail_aux1_state;
      t = t + full_adder_tail_aux1_imp_time 0 full_adder_tail_aux1_state;
      cons_h' = full_adder_tail_aux1_ret full_adder_tail_aux1_ret_state;
      t = t + 2;
      cons_t' = cons_result;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_result = cons_ret cons_ret_state;
      t = t + 2;
      cons_h' = carry_vname_encode_as_nat;
      t = t + 2;
      cons_t' = 0;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_h' = cons_ret cons_ret_state;
      t = t + 2;
      cons_t' = cons_result;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_h' = 3;
      t = t + 2;
      cons_t' = cons_ret cons_ret_state;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      full_adder_tail_aux2_ret' = cons_ret cons_ret_state;
      t = t + 2;
      ret = \<lparr>full_adder_tail_aux2_op_b = full_adder_tail_aux2_op_b s,
             full_adder_tail_aux2_i = full_adder_tail_aux2_i s,
             full_adder_tail_aux2_v = full_adder_tail_aux2_v s,
             full_adder_tail_aux2_a = full_adder_tail_aux2_a s,
             full_adder_tail_aux2_ret = full_adder_tail_aux2_ret'\<rparr>
  in
      t
  )"
  by auto
termination
  by (relation "measure (full_adder_tail_aux2_op_b \<circ> snd)") simp

declare full_adder_tail_aux2_imp_time.simps [simp del]

lemma full_adder_tail_aux2_imp_time_acc:
  "(full_adder_tail_aux2_imp_time (Suc t) s) = Suc (full_adder_tail_aux2_imp_time t s)"
  by (induction t s rule: full_adder_tail_aux2_imp_time.induct)
    ((subst (1 2) full_adder_tail_aux2_imp_time.simps);
      (simp add: full_adder_tail_aux2_state_upd_def Let_def))            

lemma full_adder_tail_aux2_imp_time_acc_2_aux:
  "(full_adder_tail_aux2_imp_time t s) = t + (full_adder_tail_aux2_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: full_adder_tail_aux2_imp_time_acc)+            

lemma full_adder_tail_aux2_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (full_adder_tail_aux2_imp_time t s) = t + (full_adder_tail_aux2_imp_time 0 s)"
  by (rule full_adder_tail_aux2_imp_time_acc_2_aux)            

lemma full_adder_tail_aux2_imp_time_acc_3:
  "(full_adder_tail_aux2_imp_time (a + b) s) = a + (full_adder_tail_aux2_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: full_adder_tail_aux2_imp_time_acc)+

abbreviation "full_adder_tail_aux2_cons_result \<equiv> ''cons_result''"

definition full_adder_tail_aux2_IMP_Minus where
  "full_adder_tail_aux2_IMP_Minus \<equiv>
  \<comment> \<open>  full_adder_tail_aux1_op_b' = full_adder_tail_aux2_op_b s;\<close>
  (full_adder_tail_aux1_prefix @ full_adder_tail_aux1_op_b_str) ::= (A (V full_adder_tail_aux2_op_b_str));;
  \<comment> \<open>  full_adder_tail_aux1_i' = full_adder_tail_aux2_i s;\<close>
  (full_adder_tail_aux1_prefix @ full_adder_tail_aux1_i_str) ::= (A (V full_adder_tail_aux2_i_str));;
  \<comment> \<open>  full_adder_tail_aux1_v' = full_adder_tail_aux2_v s;\<close>
  (full_adder_tail_aux1_prefix @ full_adder_tail_aux1_v_str) ::= (A (V full_adder_tail_aux2_v_str));;
  \<comment> \<open>  full_adder_tail_aux1_a' = full_adder_tail_aux2_a s;\<close>
  (full_adder_tail_aux1_prefix @ full_adder_tail_aux1_a_str) ::= (A (V full_adder_tail_aux2_a_str));;
  \<comment> \<open>  full_adder_tail_aux1_b' = 0;\<close>
  (full_adder_tail_aux1_prefix @ full_adder_tail_aux1_b_str) ::= (A (N 0));;
  \<comment> \<open>  full_adder_tail_aux1_ret' = 0;\<close>
  (full_adder_tail_aux1_prefix @ full_adder_tail_aux1_ret_str) ::= (A (N 0));;
  \<comment> \<open>  full_adder_tail_aux1_state = \<lparr>full_adder_tail_aux1_op_b = full_adder_tail_aux1_op_b',\<close>
  \<comment> \<open>                                full_adder_tail_aux1_i = full_adder_tail_aux1_i',\<close>
  \<comment> \<open>                                full_adder_tail_aux1_v = full_adder_tail_aux1_v',\<close>
  \<comment> \<open>                                full_adder_tail_aux1_a = full_adder_tail_aux1_a',\<close>
  \<comment> \<open>                                full_adder_tail_aux1_b = full_adder_tail_aux1_b',\<close>
  \<comment> \<open>                                full_adder_tail_aux1_ret = full_adder_tail_aux1_ret'\<rparr>;\<close>
  \<comment> \<open>  full_adder_tail_aux1_ret_state = full_adder_tail_aux1_imp full_adder_tail_aux1_state;\<close>
  (invoke_subprogram full_adder_tail_aux1_prefix full_adder_tail_aux1_IMP_Minus);;
  \<comment> \<open>  cons_h' = full_adder_tail_aux1_ret full_adder_tail_aux1_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (full_adder_tail_aux1_prefix @ full_adder_tail_aux1_ret_str)));;
  \<comment> \<open>  cons_t' = 0;\<close>
  (cons_prefix @ cons_t_str) ::= (A (N 0));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_result = cons_ret cons_ret_state;\<close>
  (full_adder_tail_aux2_cons_result) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  full_adder_tail_aux1_op_b' = full_adder_tail_aux2_op_b s;\<close>
  (full_adder_tail_aux1_prefix @ full_adder_tail_aux1_op_b_str) ::= (A (V full_adder_tail_aux2_op_b_str));;
  \<comment> \<open>  full_adder_tail_aux1_i' = full_adder_tail_aux2_i s;\<close>
  (full_adder_tail_aux1_prefix @ full_adder_tail_aux1_i_str) ::= (A (V full_adder_tail_aux2_i_str));;
  \<comment> \<open>  full_adder_tail_aux1_v' = full_adder_tail_aux2_v s;\<close>
  (full_adder_tail_aux1_prefix @ full_adder_tail_aux1_v_str) ::= (A (V full_adder_tail_aux2_v_str));;
  \<comment> \<open>  full_adder_tail_aux1_a' = full_adder_tail_aux2_a s;\<close>
  (full_adder_tail_aux1_prefix @ full_adder_tail_aux1_a_str) ::= (A (V full_adder_tail_aux2_a_str));;
  \<comment> \<open>  full_adder_tail_aux1_b' = 1;\<close>
  (full_adder_tail_aux1_prefix @ full_adder_tail_aux1_b_str) ::= (A (N 1));;
  \<comment> \<open>  full_adder_tail_aux1_ret' = 0;\<close>
  (full_adder_tail_aux1_prefix @ full_adder_tail_aux1_ret_str) ::= (A (N 0));;
  \<comment> \<open>  full_adder_tail_aux1_state = \<lparr>full_adder_tail_aux1_op_b = full_adder_tail_aux1_op_b',\<close>
  \<comment> \<open>                                full_adder_tail_aux1_i = full_adder_tail_aux1_i',\<close>
  \<comment> \<open>                                full_adder_tail_aux1_v = full_adder_tail_aux1_v',\<close>
  \<comment> \<open>                                full_adder_tail_aux1_a = full_adder_tail_aux1_a',\<close>
  \<comment> \<open>                                full_adder_tail_aux1_b = full_adder_tail_aux1_b',\<close>
  \<comment> \<open>                                full_adder_tail_aux1_ret = full_adder_tail_aux1_ret'\<rparr>;\<close>
  \<comment> \<open>  full_adder_tail_aux1_ret_state = full_adder_tail_aux1_imp full_adder_tail_aux1_state;\<close>
  (invoke_subprogram full_adder_tail_aux1_prefix full_adder_tail_aux1_IMP_Minus);;
  \<comment> \<open>  cons_h' = full_adder_tail_aux1_ret full_adder_tail_aux1_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (full_adder_tail_aux1_prefix @ full_adder_tail_aux1_ret_str)));;
  \<comment> \<open>  cons_t' = cons_result;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V full_adder_tail_aux2_cons_result));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_result = cons_ret cons_ret_state;\<close>
  (full_adder_tail_aux2_cons_result) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_h' = carry_vname_encode_as_nat;\<close>
  (cons_prefix @ cons_h_str) ::= (A (N carry_vname_encode_as_nat));;
  \<comment> \<open>  cons_t' = 0;\<close>
  (cons_prefix @ cons_t_str) ::= (A (N 0));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_h' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_t' = cons_result;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V full_adder_tail_aux2_cons_result));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_h' = 3;\<close>
  (cons_prefix @ cons_h_str) ::= (A (N 3));;
  \<comment> \<open>  cons_t' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  full_adder_tail_aux2_ret' = cons_ret cons_ret_state;\<close>
  (full_adder_tail_aux2_ret_str) ::= (A (V (cons_prefix @ cons_ret_str)))
  \<comment> \<open>  ret = \<lparr>full_adder_tail_aux2_op_b = full_adder_tail_aux2_op_b s,\<close>
  \<comment> \<open>         full_adder_tail_aux2_i = full_adder_tail_aux2_i s,\<close>
  \<comment> \<open>         full_adder_tail_aux2_v = full_adder_tail_aux2_v s,\<close>
  \<comment> \<open>         full_adder_tail_aux2_a = full_adder_tail_aux2_a s,\<close>
  \<comment> \<open>         full_adder_tail_aux2_ret = full_adder_tail_aux2_ret'\<rparr>\<close>
"

abbreviation "full_adder_tail_aux2_IMP_vars \<equiv>
  {full_adder_tail_aux2_op_b_str, full_adder_tail_aux2_i_str, full_adder_tail_aux2_v_str,
  full_adder_tail_aux2_a_str, full_adder_tail_aux2_ret_str, full_adder_tail_aux2_cons_result}"

definition "full_adder_tail_aux2_imp_to_HOL_state p s =
  \<lparr>full_adder_tail_aux2_op_b = (s (add_prefix p full_adder_tail_aux2_op_b_str)),
   full_adder_tail_aux2_i = (s (add_prefix p full_adder_tail_aux2_i_str)),
   full_adder_tail_aux2_v = (s (add_prefix p full_adder_tail_aux2_v_str)),
   full_adder_tail_aux2_a = (s (add_prefix p full_adder_tail_aux2_a_str)),
   full_adder_tail_aux2_ret = (s (add_prefix p full_adder_tail_aux2_ret_str))\<rparr>"

lemmas full_adder_tail_aux2_state_translators =
  full_adder_tail_aux2_imp_to_HOL_state_def
  full_adder_tail_aux1_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def

lemma full_adder_tail_aux2_IMP_Minus_correct_function:
  "(invoke_subprogram p full_adder_tail_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p full_adder_tail_aux2_ret_str)
      = full_adder_tail_aux2_ret
          (full_adder_tail_aux2_imp (full_adder_tail_aux2_imp_to_HOL_state p s))"
  apply(subst full_adder_tail_aux2_imp.simps)
  apply(simp only: full_adder_tail_aux2_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule full_adder_tail_aux1_IMP_Minus_correct[where vars = "full_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(37) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(39) by fastforce
  apply(erule full_adder_tail_aux1_IMP_Minus_correct[where vars = "full_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(41) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(43) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(45) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(47) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(49) by fastforce
  by(force simp: full_adder_tail_aux2_state_translators
    full_adder_tail_aux2_state_upd_def)     

lemma full_adder_tail_aux2_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ full_adder_tail_aux2_pref) full_adder_tail_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix full_adder_tail_aux2_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma full_adder_tail_aux2_IMP_Minus_correct_time:
  "(invoke_subprogram p full_adder_tail_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = full_adder_tail_aux2_imp_time 0 (full_adder_tail_aux2_imp_to_HOL_state p s)"
  apply(subst full_adder_tail_aux2_imp_time.simps)
  apply(simp only: full_adder_tail_aux2_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule full_adder_tail_aux1_IMP_Minus_correct[where vars = "full_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(73) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(75) by fastforce
  apply(erule full_adder_tail_aux1_IMP_Minus_correct[where vars = "full_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(77) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(79) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(81) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(83) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(85) by fastforce
  by(force simp add: Let_def full_adder_tail_aux2_state_translators)  

lemma full_adder_tail_aux2_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) full_adder_tail_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (full_adder_tail_aux2_imp_time 0 (full_adder_tail_aux2_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) full_adder_tail_aux2_ret_str) =
          full_adder_tail_aux2_ret (full_adder_tail_aux2_imp
                                        (full_adder_tail_aux2_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using full_adder_tail_aux2_IMP_Minus_correct_function
    full_adder_tail_aux2_IMP_Minus_correct_time
    full_adder_tail_aux2_IMP_Minus_correct_effects
  by (meson set_mono_prefix)

subsubsection \<open>full_adder_tail_aux3\<close>

fun full_adder_tail_aux3 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "full_adder_tail_aux3 op_a op_b i v = 
    (op_a ## 0) ## (full_adder_tail_aux2 op_b i v 1) ## (full_adder_tail_aux2 op_b i v 0) ## 0"

record full_adder_tail_aux3_state =
  full_adder_tail_aux3_op_a::nat
  full_adder_tail_aux3_op_b::nat
  full_adder_tail_aux3_i::nat
  full_adder_tail_aux3_v::nat
  full_adder_tail_aux3_ret::nat

abbreviation "full_adder_tail_aux3_prefix \<equiv> ''full_adder_tail_aux3.''"
abbreviation "full_adder_tail_aux3_op_a_str \<equiv> ''op_a''"
abbreviation "full_adder_tail_aux3_op_b_str \<equiv> ''op_b''"
abbreviation "full_adder_tail_aux3_i_str \<equiv> ''i''"
abbreviation "full_adder_tail_aux3_v_str \<equiv> ''v''"
abbreviation "full_adder_tail_aux3_ret_str \<equiv> ''ret''"

definition "full_adder_tail_aux3_state_upd s =
  (let
      full_adder_tail_aux2_op_b' = full_adder_tail_aux3_op_b s;
      full_adder_tail_aux2_i' = full_adder_tail_aux3_i s;
      full_adder_tail_aux2_v' = full_adder_tail_aux3_v s;
      full_adder_tail_aux2_a' = 0;
      full_adder_tail_aux2_ret' = 0;
      full_adder_tail_aux2_state = \<lparr>full_adder_tail_aux2_op_b = full_adder_tail_aux2_op_b',
                                    full_adder_tail_aux2_i = full_adder_tail_aux2_i',
                                    full_adder_tail_aux2_v = full_adder_tail_aux2_v',
                                    full_adder_tail_aux2_a = full_adder_tail_aux2_a',
                                    full_adder_tail_aux2_ret = full_adder_tail_aux2_ret'\<rparr>;
      full_adder_tail_aux2_ret_state = full_adder_tail_aux2_imp full_adder_tail_aux2_state;
      cons_h' = full_adder_tail_aux2_ret full_adder_tail_aux2_ret_state;
      cons_t' = 0;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_result = cons_ret cons_ret_state;
      full_adder_tail_aux2_op_b' = full_adder_tail_aux3_op_b s;
      full_adder_tail_aux2_i' = full_adder_tail_aux3_i s;
      full_adder_tail_aux2_v' = full_adder_tail_aux3_v s;
      full_adder_tail_aux2_a' = 1;
      full_adder_tail_aux2_ret' = 0;
      full_adder_tail_aux2_state = \<lparr>full_adder_tail_aux2_op_b = full_adder_tail_aux2_op_b',
                                    full_adder_tail_aux2_i = full_adder_tail_aux2_i',
                                    full_adder_tail_aux2_v = full_adder_tail_aux2_v',
                                    full_adder_tail_aux2_a = full_adder_tail_aux2_a',
                                    full_adder_tail_aux2_ret = full_adder_tail_aux2_ret'\<rparr>;
      full_adder_tail_aux2_ret_state = full_adder_tail_aux2_imp full_adder_tail_aux2_state;
      cons_h' = full_adder_tail_aux2_ret full_adder_tail_aux2_ret_state;
      cons_t' = cons_result;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;      
      cons_result = cons_ret cons_ret_state;
      cons_h' = full_adder_tail_aux3_op_a s;
      cons_t' = 0;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_h' = cons_ret cons_ret_state;
      cons_t' = cons_result;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      full_adder_tail_aux3_ret' = cons_ret cons_ret_state;
      ret = \<lparr>full_adder_tail_aux3_op_a = full_adder_tail_aux3_op_a s,
             full_adder_tail_aux3_op_b = full_adder_tail_aux3_op_b s,
             full_adder_tail_aux3_i = full_adder_tail_aux3_i s,
             full_adder_tail_aux3_v = full_adder_tail_aux3_v s,
             full_adder_tail_aux3_ret = full_adder_tail_aux3_ret'\<rparr>
   in
      ret
)"

function full_adder_tail_aux3_imp ::
  "full_adder_tail_aux3_state \<Rightarrow> full_adder_tail_aux3_state" where
  "full_adder_tail_aux3_imp s =
  (let 
      ret = full_adder_tail_aux3_state_upd s
    in 
      ret
  )"
  by simp+
termination
  by (relation "measure full_adder_tail_aux3_op_a") simp

declare full_adder_tail_aux3_imp.simps [simp del]

lemma full_adder_tail_aux3_imp_correct[let_function_correctness]:
  "full_adder_tail_aux3_ret (full_adder_tail_aux3_imp s) =
    full_adder_tail_aux3 (full_adder_tail_aux3_op_a s) (full_adder_tail_aux3_op_b s)
      (full_adder_tail_aux3_i s) (full_adder_tail_aux3_v s)"
  apply (simp only: full_adder_tail_aux3_imp.simps Let_def full_adder_tail_aux3_state_upd_def
    full_adder_tail_aux2_imp_correct cons_imp_correct)
  by simp  

function full_adder_tail_aux3_imp_time ::
  "nat \<Rightarrow> full_adder_tail_aux3_state \<Rightarrow> nat" where
  "full_adder_tail_aux3_imp_time t s =
  (let
      full_adder_tail_aux2_op_b' = full_adder_tail_aux3_op_b s;
      t = t + 2;
      full_adder_tail_aux2_i' = full_adder_tail_aux3_i s;
      t = t + 2;
      full_adder_tail_aux2_v' = full_adder_tail_aux3_v s;
      t = t + 2;
      full_adder_tail_aux2_a' = 0;
      t = t + 2;
      full_adder_tail_aux2_ret' = 0;
      t = t + 2;
      full_adder_tail_aux2_state = \<lparr>full_adder_tail_aux2_op_b = full_adder_tail_aux2_op_b',
                                    full_adder_tail_aux2_i = full_adder_tail_aux2_i',
                                    full_adder_tail_aux2_v = full_adder_tail_aux2_v',
                                    full_adder_tail_aux2_a = full_adder_tail_aux2_a',
                                    full_adder_tail_aux2_ret = full_adder_tail_aux2_ret'\<rparr>;
      full_adder_tail_aux2_ret_state = full_adder_tail_aux2_imp full_adder_tail_aux2_state;
      t = t + full_adder_tail_aux2_imp_time 0 full_adder_tail_aux2_state;
      cons_h' = full_adder_tail_aux2_ret full_adder_tail_aux2_ret_state;
      t = t + 2;
      cons_t' = 0;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_result = cons_ret cons_ret_state;
      t = t + 2;
      full_adder_tail_aux2_op_b' = full_adder_tail_aux3_op_b s;
      t = t + 2;
      full_adder_tail_aux2_i' = full_adder_tail_aux3_i s;
      t = t + 2;
      full_adder_tail_aux2_v' = full_adder_tail_aux3_v s;
      t = t + 2;
      full_adder_tail_aux2_a' = 1;
      t = t + 2;
      full_adder_tail_aux2_ret' = 0;
      t = t + 2;
      full_adder_tail_aux2_state = \<lparr>full_adder_tail_aux2_op_b = full_adder_tail_aux2_op_b',
                                    full_adder_tail_aux2_i = full_adder_tail_aux2_i',
                                    full_adder_tail_aux2_v = full_adder_tail_aux2_v',
                                    full_adder_tail_aux2_a = full_adder_tail_aux2_a',
                                    full_adder_tail_aux2_ret = full_adder_tail_aux2_ret'\<rparr>;
      full_adder_tail_aux2_ret_state = full_adder_tail_aux2_imp full_adder_tail_aux2_state;
      t = t + full_adder_tail_aux2_imp_time 0 full_adder_tail_aux2_state;
      cons_h' = full_adder_tail_aux2_ret full_adder_tail_aux2_ret_state;
      t = t + 2;
      cons_t' = cons_result;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_result = cons_ret cons_ret_state;
      t = t + 2;
      cons_h' = full_adder_tail_aux3_op_a s;
      t = t + 2;
      cons_t' = 0;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_h' = cons_ret cons_ret_state;
      t = t + 2;
      cons_t' = cons_result;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      full_adder_tail_aux3_ret' = cons_ret cons_ret_state;
      t = t + 2;
      ret = \<lparr>full_adder_tail_aux3_op_a = full_adder_tail_aux3_op_a s,
             full_adder_tail_aux3_op_b = full_adder_tail_aux3_op_b s,
             full_adder_tail_aux3_i = full_adder_tail_aux3_i s,
             full_adder_tail_aux3_v = full_adder_tail_aux3_v s,
             full_adder_tail_aux3_ret = full_adder_tail_aux3_ret'\<rparr>
  in
      t
  )"
  by auto
termination
  by (relation "measure (full_adder_tail_aux3_op_a \<circ> snd)") simp

declare full_adder_tail_aux3_imp_time.simps [simp del]

lemma full_adder_tail_aux3_imp_time_acc:
  "(full_adder_tail_aux3_imp_time (Suc t) s) = Suc (full_adder_tail_aux3_imp_time t s)"
  by (induction t s rule: full_adder_tail_aux3_imp_time.induct)
    ((subst (1 2) full_adder_tail_aux3_imp_time.simps);
      (simp add: full_adder_tail_aux3_state_upd_def Let_def))            

lemma full_adder_tail_aux3_imp_time_acc_2_aux:
  "(full_adder_tail_aux3_imp_time t s) = t + (full_adder_tail_aux3_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: full_adder_tail_aux3_imp_time_acc)+            

lemma full_adder_tail_aux3_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (full_adder_tail_aux3_imp_time t s) = t + (full_adder_tail_aux3_imp_time 0 s)"
  by (rule full_adder_tail_aux3_imp_time_acc_2_aux)            

lemma full_adder_tail_aux3_imp_time_acc_3:
  "(full_adder_tail_aux3_imp_time (a + b) s) = a + (full_adder_tail_aux3_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: full_adder_tail_aux3_imp_time_acc)+

abbreviation "full_adder_tail_aux3_cons_result \<equiv> ''cons_result''"

definition full_adder_tail_aux3_IMP_Minus where
  "full_adder_tail_aux3_IMP_Minus \<equiv>
  \<comment> \<open>  full_adder_tail_aux2_op_b' = full_adder_tail_aux3_op_b s;\<close>
  (full_adder_tail_aux2_prefix @ full_adder_tail_aux2_op_b_str) ::= (A (V full_adder_tail_aux3_op_b_str));;
  \<comment> \<open>  full_adder_tail_aux2_i' = full_adder_tail_aux3_i s;\<close>
  (full_adder_tail_aux2_prefix @ full_adder_tail_aux2_i_str) ::= (A (V full_adder_tail_aux3_i_str));;
  \<comment> \<open>  full_adder_tail_aux2_v' = full_adder_tail_aux3_v s;\<close>
  (full_adder_tail_aux2_prefix @ full_adder_tail_aux2_v_str) ::= (A (V full_adder_tail_aux3_v_str));;
  \<comment> \<open>  full_adder_tail_aux2_a' = 0;\<close>
  (full_adder_tail_aux2_prefix @ full_adder_tail_aux2_a_str) ::= (A (N 0));;
  \<comment> \<open>  full_adder_tail_aux2_ret' = 0;\<close>
  (full_adder_tail_aux2_prefix @ full_adder_tail_aux2_ret_str) ::= (A (N 0));;
  \<comment> \<open>  full_adder_tail_aux2_state = \<lparr>full_adder_tail_aux2_op_b = full_adder_tail_aux2_op_b',\<close>
  \<comment> \<open>                                full_adder_tail_aux2_i = full_adder_tail_aux2_i',\<close>
  \<comment> \<open>                                full_adder_tail_aux2_v = full_adder_tail_aux2_v',\<close>
  \<comment> \<open>                                full_adder_tail_aux2_a = full_adder_tail_aux2_a',\<close>
  \<comment> \<open>                                full_adder_tail_aux2_ret = full_adder_tail_aux2_ret'\<rparr>;\<close>
  \<comment> \<open>  full_adder_tail_aux2_ret_state = full_adder_tail_aux2_imp full_adder_tail_aux2_state;\<close>
  (invoke_subprogram full_adder_tail_aux2_prefix full_adder_tail_aux2_IMP_Minus);;
  \<comment> \<open>  cons_h' = full_adder_tail_aux2_ret full_adder_tail_aux2_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (full_adder_tail_aux2_prefix @ full_adder_tail_aux2_ret_str)));;
  \<comment> \<open>  cons_t' = 0;\<close>
  (cons_prefix @ cons_t_str) ::= (A (N 0));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_result = cons_ret cons_ret_state;\<close>
  (full_adder_tail_aux3_cons_result) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  full_adder_tail_aux2_op_b' = full_adder_tail_aux3_op_b s;\<close>
  (full_adder_tail_aux2_prefix @ full_adder_tail_aux2_op_b_str) ::= (A (V full_adder_tail_aux3_op_b_str));;
  \<comment> \<open>  full_adder_tail_aux2_i' = full_adder_tail_aux3_i s;\<close>
  (full_adder_tail_aux2_prefix @ full_adder_tail_aux2_i_str) ::= (A (V full_adder_tail_aux3_i_str));;
  \<comment> \<open>  full_adder_tail_aux2_v' = full_adder_tail_aux3_v s;\<close>
  (full_adder_tail_aux2_prefix @ full_adder_tail_aux2_v_str) ::= (A (V full_adder_tail_aux3_v_str));;
  \<comment> \<open>  full_adder_tail_aux2_a' = 1;\<close>
  (full_adder_tail_aux2_prefix @ full_adder_tail_aux2_a_str) ::= (A (N 1));;
  \<comment> \<open>  full_adder_tail_aux2_ret' = 0;\<close>
  (full_adder_tail_aux2_prefix @ full_adder_tail_aux2_ret_str) ::= (A (N 0));;
  \<comment> \<open>  full_adder_tail_aux2_state = \<lparr>full_adder_tail_aux2_op_b = full_adder_tail_aux2_op_b',\<close>
  \<comment> \<open>                                full_adder_tail_aux2_i = full_adder_tail_aux2_i',\<close>
  \<comment> \<open>                                full_adder_tail_aux2_v = full_adder_tail_aux2_v',\<close>
  \<comment> \<open>                                full_adder_tail_aux2_a = full_adder_tail_aux2_a',\<close>
  \<comment> \<open>                                full_adder_tail_aux2_ret = full_adder_tail_aux2_ret'\<rparr>;\<close>
  \<comment> \<open>  full_adder_tail_aux2_ret_state = full_adder_tail_aux2_imp full_adder_tail_aux2_state;\<close>
  (invoke_subprogram full_adder_tail_aux2_prefix full_adder_tail_aux2_IMP_Minus);;
  \<comment> \<open>  cons_h' = full_adder_tail_aux2_ret full_adder_tail_aux2_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (full_adder_tail_aux2_prefix @ full_adder_tail_aux2_ret_str)));;
  \<comment> \<open>  cons_t' = cons_result;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V full_adder_tail_aux3_cons_result));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_result = cons_ret cons_ret_state;\<close>
  (full_adder_tail_aux3_cons_result) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_h' = full_adder_tail_aux3_op_a s;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V full_adder_tail_aux3_op_a_str));;
  \<comment> \<open>  cons_t' = 0;\<close>
  (cons_prefix @ cons_t_str) ::= (A (N 0));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_h' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_t' = cons_result;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V full_adder_tail_aux3_cons_result));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  full_adder_tail_aux3_ret' = cons_ret cons_ret_state;\<close>
  (full_adder_tail_aux3_ret_str) ::= (A (V (cons_prefix @ cons_ret_str)))
  \<comment> \<open>  ret = \<lparr>full_adder_tail_aux3_op_a = full_adder_tail_aux3_op_a s,\<close>
  \<comment> \<open>         full_adder_tail_aux3_op_b = full_adder_tail_aux3_op_b s,\<close>
  \<comment> \<open>         full_adder_tail_aux3_i = full_adder_tail_aux3_i s,\<close>
  \<comment> \<open>         full_adder_tail_aux3_v = full_adder_tail_aux3_v s,\<close>
  \<comment> \<open>         full_adder_tail_aux3_ret = full_adder_tail_aux3_ret'\<rparr>\<close>
"

abbreviation "full_adder_tail_aux3_IMP_vars \<equiv>
  {full_adder_tail_aux3_op_a_str, full_adder_tail_aux3_op_b_str, full_adder_tail_aux3_i_str,
  full_adder_tail_aux3_v_str, full_adder_tail_aux3_ret_str, full_adder_tail_aux3_cons_result}"

definition "full_adder_tail_aux3_imp_to_HOL_state p s =
  \<lparr>full_adder_tail_aux3_op_a = (s (add_prefix p full_adder_tail_aux3_op_a_str)),
   full_adder_tail_aux3_op_b = (s (add_prefix p full_adder_tail_aux3_op_b_str)),
   full_adder_tail_aux3_i = (s (add_prefix p full_adder_tail_aux3_i_str)),
   full_adder_tail_aux3_v = (s (add_prefix p full_adder_tail_aux3_v_str)),
   full_adder_tail_aux3_ret = (s (add_prefix p full_adder_tail_aux3_ret_str))\<rparr>"

lemmas full_adder_tail_aux3_state_translators =
  full_adder_tail_aux3_imp_to_HOL_state_def
  full_adder_tail_aux2_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def

lemma full_adder_tail_aux3_IMP_Minus_correct_function:
  "(invoke_subprogram p full_adder_tail_aux3_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p full_adder_tail_aux3_ret_str)
      = full_adder_tail_aux3_ret
          (full_adder_tail_aux3_imp (full_adder_tail_aux3_imp_to_HOL_state p s))"
  apply(subst full_adder_tail_aux3_imp.simps)
  apply(simp only: full_adder_tail_aux3_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule full_adder_tail_aux2_IMP_Minus_correct[where vars = "full_adder_tail_aux3_IMP_vars"])
  subgoal premises p using p(31) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux3_IMP_vars"])
  subgoal premises p using p(33) by fastforce
  apply(erule full_adder_tail_aux2_IMP_Minus_correct[where vars = "full_adder_tail_aux3_IMP_vars"])
  subgoal premises p using p(35) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux3_IMP_vars"])
  subgoal premises p using p(37) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux3_IMP_vars"])
  subgoal premises p using p(39) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux3_IMP_vars"])
  subgoal premises p using p(41) by fastforce
  by(force simp: full_adder_tail_aux3_state_translators
    full_adder_tail_aux3_state_upd_def)    

lemma full_adder_tail_aux3_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ full_adder_tail_aux3_pref) full_adder_tail_aux3_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix full_adder_tail_aux3_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast    

lemma full_adder_tail_aux3_IMP_Minus_correct_time:
  "(invoke_subprogram p full_adder_tail_aux3_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = full_adder_tail_aux3_imp_time 0 (full_adder_tail_aux3_imp_to_HOL_state p s)"
  apply(subst full_adder_tail_aux3_imp_time.simps)
  apply(simp only: full_adder_tail_aux3_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule full_adder_tail_aux2_IMP_Minus_correct[where vars = "full_adder_tail_aux3_IMP_vars"])
  subgoal premises p using p(61) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux3_IMP_vars"])
  subgoal premises p using p(63) by fastforce
  apply(erule full_adder_tail_aux2_IMP_Minus_correct[where vars = "full_adder_tail_aux3_IMP_vars"])
  subgoal premises p using p(65) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux3_IMP_vars"])
  subgoal premises p using p(67) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux3_IMP_vars"])
  subgoal premises p using p(69) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_aux3_IMP_vars"])
  subgoal premises p using p(71) by fastforce
  by(force simp add: Let_def full_adder_tail_aux3_state_translators)        

lemma full_adder_tail_aux3_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) full_adder_tail_aux3_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (full_adder_tail_aux3_imp_time 0 (full_adder_tail_aux3_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) full_adder_tail_aux3_ret_str) =
          full_adder_tail_aux3_ret (full_adder_tail_aux3_imp
                                        (full_adder_tail_aux3_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using full_adder_tail_aux3_IMP_Minus_correct_function
    full_adder_tail_aux3_IMP_Minus_correct_time
    full_adder_tail_aux3_IMP_Minus_correct_effects
  by (meson set_mono_prefix) 

subsubsection \<open>full_adder_tail\<close>

fun full_adder_tail' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "full_adder_tail' i v =
    (let op_a = operand_bit_to_var_tail (prod_encode(encode_char (CHR ''a''), i));
         op_b = operand_bit_to_var_tail (prod_encode(encode_char (CHR ''b''), i)) in 
    3 ## (full_adder_tail_aux3 op_a op_b i v)
  )"

lemma full_adder_tail'_correct:
  "full_adder_tail i v = full_adder_tail' i v"
  unfolding full_adder_tail_def
  by (simp only: full_adder_tail'.simps full_adder_tail_aux1.simps full_adder_tail_aux2.simps 
    full_adder_tail_aux3.simps Let_def)

record full_adder_tail_state =
  full_adder_tail_i::nat
  full_adder_tail_v::nat
  full_adder_tail_ret::nat

abbreviation "full_adder_tail_prefix \<equiv> ''full_adder_tail.''"
abbreviation "full_adder_tail_i_str \<equiv> ''i''"
abbreviation "full_adder_tail_v_str \<equiv> ''v''"
abbreviation "full_adder_tail_ret_str \<equiv> ''ret''"

definition "full_adder_tail_state_upd s =
  (let
      prod_encode_a' = a_encode_char_as_nat;
      prod_encode_b' = full_adder_tail_i s;
      prod_encode_ret' = 0;
      prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                           prod_encode_b = prod_encode_b',
                           prod_encode_ret = prod_encode_ret'\<rparr>;
      prod_encode_ret_state = prod_encode_imp prod_encode_state;
      operand_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
      operand_bit_to_var_tail_ret' = 0;
      operand_bit_to_var_tail_state = \<lparr>operand_bit_to_var_tail_n = operand_bit_to_var_tail_n',
                                       operand_bit_to_var_tail_ret = operand_bit_to_var_tail_ret'\<rparr>;
      operand_bit_to_var_tail_ret_state = operand_bit_to_var_tail_imp operand_bit_to_var_tail_state;
      operand_bit_to_var_tail_result = operand_bit_to_var_tail_ret operand_bit_to_var_tail_ret_state;
      prod_encode_a' = b_encode_char_as_nat;
      prod_encode_b' = full_adder_tail_i s;
      prod_encode_ret' = 0;
      prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                           prod_encode_b = prod_encode_b',
                           prod_encode_ret = prod_encode_ret'\<rparr>;
      prod_encode_ret_state = prod_encode_imp prod_encode_state;
      operand_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
      operand_bit_to_var_tail_ret' = 0;
      operand_bit_to_var_tail_state = \<lparr>operand_bit_to_var_tail_n = operand_bit_to_var_tail_n',
                                       operand_bit_to_var_tail_ret = operand_bit_to_var_tail_ret'\<rparr>;
      operand_bit_to_var_tail_ret_state = operand_bit_to_var_tail_imp operand_bit_to_var_tail_state;
      full_adder_tail_aux3_op_a' = operand_bit_to_var_tail_result;
      full_adder_tail_aux3_op_b' = operand_bit_to_var_tail_ret operand_bit_to_var_tail_ret_state;
      full_adder_tail_aux3_i' = full_adder_tail_i s;
      full_adder_tail_aux3_v' = full_adder_tail_v s;
      full_adder_tail_aux3_ret' = 0;
      full_adder_tail_aux3_state = \<lparr>full_adder_tail_aux3_op_a = full_adder_tail_aux3_op_a',
                                    full_adder_tail_aux3_op_b = full_adder_tail_aux3_op_b',
                                    full_adder_tail_aux3_i = full_adder_tail_aux3_i',
                                    full_adder_tail_aux3_v = full_adder_tail_aux3_v',
                                    full_adder_tail_aux3_ret = full_adder_tail_aux3_ret'\<rparr>;
      full_adder_tail_aux3_ret_state = full_adder_tail_aux3_imp full_adder_tail_aux3_state;
      cons_h' = 3;
      cons_t' = full_adder_tail_aux3_ret full_adder_tail_aux3_ret_state;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      full_adder_tail_ret' = cons_ret cons_ret_state;
      ret = \<lparr>full_adder_tail_i = full_adder_tail_i s,
             full_adder_tail_v = full_adder_tail_v s,
             full_adder_tail_ret = full_adder_tail_ret'\<rparr>
  in ret
)"

function full_adder_tail_imp ::
  "full_adder_tail_state \<Rightarrow> full_adder_tail_state" where
  "full_adder_tail_imp s =
  (let 
      ret = full_adder_tail_state_upd s
    in 
      ret
  )"
  by simp+
termination
  by (relation "measure full_adder_tail_i") simp

declare full_adder_tail_imp.simps [simp del]

lemma full_adder_tail_imp_correct[let_function_correctness]:
  "full_adder_tail_ret (full_adder_tail_imp s) =
    full_adder_tail (full_adder_tail_i s) (full_adder_tail_v s)"
  apply (simp only: full_adder_tail_imp.simps Let_def full_adder_tail_state_upd_def
    prod_encode_imp_correct operand_bit_to_var_tail_imp_correct full_adder_tail_aux3_imp_correct
    cons_imp_correct a_encode_char_val b_encode_char_val full_adder_tail'_correct full_adder_tail'.simps)
  by simp

function full_adder_tail_imp_time ::
  "nat \<Rightarrow> full_adder_tail_state \<Rightarrow> nat" where
  "full_adder_tail_imp_time t s =
  (let
      prod_encode_a' = a_encode_char_as_nat;
      t = t + 2;
      prod_encode_b' = full_adder_tail_i s;
      t = t + 2;
      prod_encode_ret' = 0;
      t = t + 2;
      prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                           prod_encode_b = prod_encode_b',
                           prod_encode_ret = prod_encode_ret'\<rparr>;
      prod_encode_ret_state = prod_encode_imp prod_encode_state;
      t = t + prod_encode_imp_time 0 prod_encode_state;
      operand_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
      t = t + 2;
      operand_bit_to_var_tail_ret' = 0;
      t = t + 2;
      operand_bit_to_var_tail_state = \<lparr>operand_bit_to_var_tail_n = operand_bit_to_var_tail_n',
                                       operand_bit_to_var_tail_ret = operand_bit_to_var_tail_ret'\<rparr>;
      operand_bit_to_var_tail_ret_state = operand_bit_to_var_tail_imp operand_bit_to_var_tail_state;
      t = t + operand_bit_to_var_tail_imp_time 0 operand_bit_to_var_tail_state;
      operand_bit_to_var_tail_result = operand_bit_to_var_tail_ret operand_bit_to_var_tail_ret_state;
      t = t + 2;
      prod_encode_a' = b_encode_char_as_nat;
      t = t + 2;
      prod_encode_b' = full_adder_tail_i s;
      t = t + 2;
      prod_encode_ret' = 0;
      t = t + 2;
      prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                           prod_encode_b = prod_encode_b',
                           prod_encode_ret = prod_encode_ret'\<rparr>;
      prod_encode_ret_state = prod_encode_imp prod_encode_state;
      t = t + prod_encode_imp_time 0 prod_encode_state;
      operand_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;
      t = t + 2;
      operand_bit_to_var_tail_ret' = 0;
      t = t + 2;
      operand_bit_to_var_tail_state = \<lparr>operand_bit_to_var_tail_n = operand_bit_to_var_tail_n',
                                       operand_bit_to_var_tail_ret = operand_bit_to_var_tail_ret'\<rparr>;
      operand_bit_to_var_tail_ret_state = operand_bit_to_var_tail_imp operand_bit_to_var_tail_state;
      t = t + operand_bit_to_var_tail_imp_time 0 operand_bit_to_var_tail_state;
      full_adder_tail_aux3_op_a' = operand_bit_to_var_tail_result;
      t = t + 2;
      full_adder_tail_aux3_op_b' = operand_bit_to_var_tail_ret operand_bit_to_var_tail_ret_state;
      t = t + 2;
      full_adder_tail_aux3_i' = full_adder_tail_i s;
      t = t + 2;
      full_adder_tail_aux3_v' = full_adder_tail_v s;
      t = t + 2;
      full_adder_tail_aux3_ret' = 0;
      t = t + 2;
      full_adder_tail_aux3_state = \<lparr>full_adder_tail_aux3_op_a = full_adder_tail_aux3_op_a',
                                    full_adder_tail_aux3_op_b = full_adder_tail_aux3_op_b',
                                    full_adder_tail_aux3_i = full_adder_tail_aux3_i',
                                    full_adder_tail_aux3_v = full_adder_tail_aux3_v',
                                    full_adder_tail_aux3_ret = full_adder_tail_aux3_ret'\<rparr>;
      full_adder_tail_aux3_ret_state = full_adder_tail_aux3_imp full_adder_tail_aux3_state;
      t = t + full_adder_tail_aux3_imp_time 0 full_adder_tail_aux3_state;
      cons_h' = 3;
      t = t + 2;
      cons_t' = full_adder_tail_aux3_ret full_adder_tail_aux3_ret_state;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      full_adder_tail_ret' = cons_ret cons_ret_state;
      t = t + 2;
      ret = \<lparr>full_adder_tail_i = full_adder_tail_i s,
             full_adder_tail_v = full_adder_tail_v s,
             full_adder_tail_ret = full_adder_tail_ret'\<rparr>
  in
      t
  )"
  by auto
termination
  by (relation "measure (full_adder_tail_i \<circ> snd)") simp

declare full_adder_tail_imp_time.simps [simp del]

lemma full_adder_tail_imp_time_acc:
  "(full_adder_tail_imp_time (Suc t) s) = Suc (full_adder_tail_imp_time t s)"
  by (induction t s rule: full_adder_tail_imp_time.induct)
    ((subst (1 2) full_adder_tail_imp_time.simps);
      (simp add: full_adder_tail_state_upd_def Let_def))            

lemma full_adder_tail_imp_time_acc_2_aux:
  "(full_adder_tail_imp_time t s) = t + (full_adder_tail_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: full_adder_tail_imp_time_acc)+            

lemma full_adder_tail_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (full_adder_tail_imp_time t s) = t + (full_adder_tail_imp_time 0 s)"
  by (rule full_adder_tail_imp_time_acc_2_aux)            

lemma full_adder_tail_imp_time_acc_3:
  "(full_adder_tail_imp_time (a + b) s) = a + (full_adder_tail_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: full_adder_tail_imp_time_acc)+ 

abbreviation "full_adder_tail_operand_bit_to_var_tail_result \<equiv> ''operand_bit_to_var_tail_result''"

definition full_adder_tail_IMP_Minus where
  "full_adder_tail_IMP_Minus \<equiv>
  \<comment> \<open>  prod_encode_a' = a_encode_char_as_nat;\<close>
  (prod_encode_prefix @ prod_encode_a_str) ::= (A (N a_encode_char_as_nat));;
  \<comment> \<open>  prod_encode_b' = full_adder_tail_i s;\<close>
  (prod_encode_prefix @ prod_encode_b_str) ::= (A (V full_adder_tail_i_str));;
  \<comment> \<open>  prod_encode_ret' = 0;\<close>
  (prod_encode_prefix @ prod_encode_ret_str) ::= (A (N 0));;
  \<comment> \<open>  prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',\<close>
  \<comment> \<open>                       prod_encode_b = prod_encode_b',\<close>
  \<comment> \<open>                       prod_encode_ret = prod_encode_ret'\<rparr>;\<close>
  \<comment> \<open>  prod_encode_ret_state = prod_encode_imp prod_encode_state;\<close>
  (invoke_subprogram prod_encode_prefix prod_encode_IMP_Minus);;
  \<comment> \<open>  operand_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;\<close>
  (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_n_str) ::= (A (V (prod_encode_prefix @ prod_encode_ret_str)));;
  \<comment> \<open>  operand_bit_to_var_tail_ret' = 0;\<close>
  (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str) ::= (A (N 0));;
  \<comment> \<open>  operand_bit_to_var_tail_state = \<lparr>operand_bit_to_var_tail_n = operand_bit_to_var_tail_n',\<close>
  \<comment> \<open>                                   operand_bit_to_var_tail_ret = operand_bit_to_var_tail_ret'\<rparr>;\<close>
  \<comment> \<open>  operand_bit_to_var_tail_ret_state = operand_bit_to_var_tail_imp operand_bit_to_var_tail_state;\<close>
  (invoke_subprogram operand_bit_to_var_tail_prefix operand_bit_to_var_tail_IMP_Minus);;
  \<comment> \<open>  operand_bit_to_var_tail_result = operand_bit_to_var_tail_ret operand_bit_to_var_tail_ret_state;\<close>
  (full_adder_tail_operand_bit_to_var_tail_result) ::= (A (V (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str)));;
  \<comment> \<open>  prod_encode_a' = b_encode_char_as_nat;\<close>
  (prod_encode_prefix @ prod_encode_a_str) ::= (A (N b_encode_char_as_nat));;
  \<comment> \<open>  prod_encode_b' = full_adder_tail_i s;\<close>
  (prod_encode_prefix @ prod_encode_b_str) ::= (A (V full_adder_tail_i_str));;
  \<comment> \<open>  prod_encode_ret' = 0;\<close>
  (prod_encode_prefix @ prod_encode_ret_str) ::= (A (N 0));;
  \<comment> \<open>  prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',\<close>
  \<comment> \<open>                       prod_encode_b = prod_encode_b',\<close>
  \<comment> \<open>                       prod_encode_ret = prod_encode_ret'\<rparr>;\<close>
  \<comment> \<open>  prod_encode_ret_state = prod_encode_imp prod_encode_state;\<close>
  (invoke_subprogram prod_encode_prefix prod_encode_IMP_Minus);;
  \<comment> \<open>  operand_bit_to_var_tail_n' = prod_encode_ret prod_encode_ret_state;\<close>
  (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_n_str) ::= (A (V (prod_encode_prefix @ prod_encode_ret_str)));;
  \<comment> \<open>  operand_bit_to_var_tail_ret' = 0;\<close>
  (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str) ::= (A (N 0));;
  \<comment> \<open>  operand_bit_to_var_tail_state = \<lparr>operand_bit_to_var_tail_n = operand_bit_to_var_tail_n',\<close>
  \<comment> \<open>                                   operand_bit_to_var_tail_ret = operand_bit_to_var_tail_ret'\<rparr>;\<close>
  \<comment> \<open>  operand_bit_to_var_tail_ret_state = operand_bit_to_var_tail_imp operand_bit_to_var_tail_state;\<close>
  (invoke_subprogram operand_bit_to_var_tail_prefix operand_bit_to_var_tail_IMP_Minus);;
  \<comment> \<open>  full_adder_tail_aux3_op_a' = operand_bit_to_var_tail_result;\<close>
  (full_adder_tail_aux3_prefix @ full_adder_tail_aux3_op_a_str) ::= (A (V full_adder_tail_operand_bit_to_var_tail_result));;
  \<comment> \<open>  full_adder_tail_aux3_op_b' = operand_bit_to_var_tail_ret operand_bit_to_var_tail_ret_state;\<close>
  (full_adder_tail_aux3_prefix @ full_adder_tail_aux3_op_b_str) ::= (A (V (operand_bit_to_var_tail_prefix @ operand_bit_to_var_tail_ret_str)));;
  \<comment> \<open>  full_adder_tail_aux3_i' = full_adder_tail_i s;\<close>
  (full_adder_tail_aux3_prefix @ full_adder_tail_aux3_i_str) ::= (A (V full_adder_tail_i_str));;
  \<comment> \<open>  full_adder_tail_aux3_v' = full_adder_tail_v s;\<close>
  (full_adder_tail_aux3_prefix @ full_adder_tail_aux3_v_str) ::= (A (V full_adder_tail_v_str));;
  \<comment> \<open>  full_adder_tail_aux3_ret' = 0;\<close>
  (full_adder_tail_aux3_prefix @ full_adder_tail_aux3_ret_str) ::= (A (N 0));;
  \<comment> \<open>  full_adder_tail_aux3_state = \<lparr>full_adder_tail_aux3_op_a = full_adder_tail_aux3_op_a',\<close>
  \<comment> \<open>                                full_adder_tail_aux3_op_b = full_adder_tail_aux3_op_b',\<close>
  \<comment> \<open>                                full_adder_tail_aux3_i = full_adder_tail_aux3_i',\<close>
  \<comment> \<open>                                full_adder_tail_aux3_v = full_adder_tail_aux3_v',\<close>
  \<comment> \<open>                                full_adder_tail_aux3_ret = full_adder_tail_aux3_ret'\<rparr>;\<close>
  \<comment> \<open>  full_adder_tail_aux3_ret_state = full_adder_tail_aux3_imp full_adder_tail_aux3_state;\<close>
  (invoke_subprogram full_adder_tail_aux3_prefix full_adder_tail_aux3_IMP_Minus);;
  \<comment> \<open>  cons_h' = 3;\<close>
  (cons_prefix @ cons_h_str) ::= (A (N 3));;
  \<comment> \<open>  cons_t' = full_adder_tail_aux3_ret full_adder_tail_aux3_ret_state;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V (full_adder_tail_aux3_prefix @ full_adder_tail_aux3_ret_str)));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  full_adder_tail_ret' = cons_ret cons_ret_state;\<close>
  (full_adder_tail_ret_str) ::= (A (V (cons_prefix @ cons_ret_str)))
  \<comment> \<open>  ret = \<lparr>full_adder_tail_i = full_adder_tail_i s,\<close>
  \<comment> \<open>         full_adder_tail_v = full_adder_tail_v s,\<close>
  \<comment> \<open>         full_adder_tail_ret = full_adder_tail_ret'\<rparr>\<close>
"

abbreviation "full_adder_tail_IMP_vars \<equiv>
  {full_adder_tail_i_str, full_adder_tail_v_str, full_adder_tail_ret_str, 
  full_adder_tail_operand_bit_to_var_tail_result}"

definition "full_adder_tail_imp_to_HOL_state p s =
  \<lparr>full_adder_tail_i = (s (add_prefix p full_adder_tail_i_str)),
   full_adder_tail_v = (s (add_prefix p full_adder_tail_v_str)),
   full_adder_tail_ret = (s (add_prefix p full_adder_tail_ret_str))\<rparr>"

lemmas full_adder_tail_state_translators =
  full_adder_tail_imp_to_HOL_state_def
  prod_encode_imp_to_HOL_state_def
  operand_bit_to_var_tail_imp_to_HOL_state_def
  full_adder_tail_aux3_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def

lemma full_adder_tail_IMP_Minus_correct_function:
  "(invoke_subprogram p full_adder_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p full_adder_tail_ret_str)
      = full_adder_tail_ret
          (full_adder_tail_imp (full_adder_tail_imp_to_HOL_state p s))"
  apply(subst full_adder_tail_imp.simps)
  apply(simp only: full_adder_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule prod_encode_IMP_Minus_correct[where vars = "full_adder_tail_IMP_vars"])
  subgoal premises p using p(26) by fastforce
  apply(erule operand_bit_to_var_tail_IMP_Minus_correct[where vars = "full_adder_tail_IMP_vars"])
  subgoal premises p using p(28) by fastforce
  apply(erule prod_encode_IMP_Minus_correct[where vars = "full_adder_tail_IMP_vars"])
  subgoal premises p using p(30) by fastforce
  apply(erule operand_bit_to_var_tail_IMP_Minus_correct[where vars = "full_adder_tail_IMP_vars"])
  subgoal premises p using p(32) by fastforce
  apply(erule full_adder_tail_aux3_IMP_Minus_correct[where vars = "full_adder_tail_IMP_vars"])
  subgoal premises p using p(34) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_IMP_vars"])
  subgoal premises p using p(36) by fastforce
  by(force simp: full_adder_tail_state_translators
    full_adder_tail_state_upd_def)        

lemma full_adder_tail_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ full_adder_tail_pref) full_adder_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix full_adder_tail_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemma full_adder_tail_IMP_Minus_correct_time:
  "(invoke_subprogram p full_adder_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = full_adder_tail_imp_time 0 (full_adder_tail_imp_to_HOL_state p s)"
  apply(subst full_adder_tail_imp_time.simps)
  apply(simp only: full_adder_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule prod_encode_IMP_Minus_correct[where vars = "full_adder_tail_IMP_vars"])
  subgoal premises p using p(51) by fastforce
  apply(erule operand_bit_to_var_tail_IMP_Minus_correct[where vars = "full_adder_tail_IMP_vars"])
  subgoal premises p using p(53) by fastforce
  apply(erule prod_encode_IMP_Minus_correct[where vars = "full_adder_tail_IMP_vars"])
  subgoal premises p using p(55) by fastforce
  apply(erule operand_bit_to_var_tail_IMP_Minus_correct[where vars = "full_adder_tail_IMP_vars"])
  subgoal premises p using p(57) by fastforce
  apply(erule full_adder_tail_aux3_IMP_Minus_correct[where vars = "full_adder_tail_IMP_vars"])
  subgoal premises p using p(59) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "full_adder_tail_IMP_vars"])
  subgoal premises p using p(61) by fastforce
  by(force simp add: Let_def full_adder_tail_state_translators)  

lemma full_adder_tail_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) full_adder_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (full_adder_tail_imp_time 0 (full_adder_tail_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) full_adder_tail_ret_str) =
          full_adder_tail_ret (full_adder_tail_imp
                                        (full_adder_tail_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using full_adder_tail_IMP_Minus_correct_function
    full_adder_tail_IMP_Minus_correct_time
    full_adder_tail_IMP_Minus_correct_effects
  by (meson set_mono_prefix)

subsection \<open>map_adder\<close>

subsubsection \<open>map_adder_acc\<close>

record map_adder_acc_state =
  map_adder_acc_acc::nat
  map_adder_acc_v::nat
  map_adder_acc_n::nat
  map_adder_acc_ret::nat

abbreviation "map_adder_acc_prefix \<equiv> ''map_adder_acc.''"
abbreviation "map_adder_acc_acc_str \<equiv> ''acc''"
abbreviation "map_adder_acc_v_str \<equiv> ''v''"
abbreviation "map_adder_acc_n_str \<equiv> ''n''"
abbreviation "map_adder_acc_ret_str \<equiv> ''ret''"

definition "map_adder_acc_state_upd s \<equiv>
  (let
      hd_xs' = map_adder_acc_n s;
      hd_ret' = 0;
      hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
      hd_ret_state = hd_imp hd_state;
      full_adder_tail_i' = hd_ret hd_ret_state;
      full_adder_tail_v' = map_adder_acc_v s;
      full_adder_tail_ret' = 0;
      full_adder_tail_state = \<lparr>full_adder_tail_i = full_adder_tail_i',
                               full_adder_tail_v = full_adder_tail_v',
                               full_adder_tail_ret = full_adder_tail_ret'\<rparr>;
      full_adder_tail_ret_state = full_adder_tail_imp full_adder_tail_state;
      cons_h' = full_adder_tail_ret full_adder_tail_ret_state;
      cons_t' = map_adder_acc_acc s;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      map_adder_acc_acc' = cons_ret cons_ret_state;
      tl_xs' = map_adder_acc_n s;
      tl_ret' = 0;
      tl_state = \<lparr>tl_xs = tl_xs',
                  tl_ret = tl_ret'\<rparr>;
      tl_ret_state = tl_imp tl_state;
      map_adder_acc_n' = tl_ret tl_ret_state;
      ret = \<lparr>map_adder_acc_acc = map_adder_acc_acc',
             map_adder_acc_v = map_adder_acc_v s,
             map_adder_acc_n = map_adder_acc_n',
             map_adder_acc_ret = map_adder_acc_ret s\<rparr>
  in
      ret
)"

definition "map_adder_acc_imp_compute_loop_condition s \<equiv>
  (let
      condition = map_adder_acc_n s
  in
      condition
)"

definition "map_adder_acc_imp_after_loop s \<equiv>
  (let
      map_adder_acc_ret' = map_adder_acc_acc s;
      ret = \<lparr>map_adder_acc_acc = map_adder_acc_acc s,
             map_adder_acc_v = map_adder_acc_v s,
             map_adder_acc_n = map_adder_acc_n s,
             map_adder_acc_ret = map_adder_acc_ret'\<rparr>
  in
      ret
)"

lemmas map_adder_acc_imp_subprogram_simps = 
  map_adder_acc_state_upd_def
  map_adder_acc_imp_compute_loop_condition_def
  map_adder_acc_imp_after_loop_def

function map_adder_acc_imp::
  "map_adder_acc_state \<Rightarrow> map_adder_acc_state" where
  "map_adder_acc_imp s =
  (if map_adder_acc_imp_compute_loop_condition s \<noteq> 0
   then let next_iteration = map_adder_acc_imp (map_adder_acc_state_upd s)
        in next_iteration
   else let ret = map_adder_acc_imp_after_loop s
        in ret
  )"
  by simp+
termination
  apply (relation "measure map_adder_acc_n")
  apply (simp add: map_adder_acc_imp_subprogram_simps tl_imp_correct)+
  done

declare map_adder_acc_imp.simps [simp del]

lemma map_adder_acc_imp_correct:
  "map_adder_acc_ret (map_adder_acc_imp s) =
    map_adder_acc (map_adder_acc_acc s) (map_adder_acc_v s) (map_adder_acc_n s)"
  apply (induction s rule: map_adder_acc_imp.induct)
  apply (subst map_adder_acc_imp.simps)
  apply (subst map_adder_acc.simps)
  apply (simp del: map_adder_acc.simps add: map_adder_acc_imp_subprogram_simps Let_def
    hd_imp_correct full_adder_tail_imp_correct cons_imp_correct tl_imp_correct)
  done    

definition "map_adder_acc_state_upd_time t s \<equiv>
  (let
      hd_xs' = map_adder_acc_n s;
      t = t + 2;
      hd_ret' = 0;
      t = t + 2;
      hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
      hd_ret_state = hd_imp hd_state;
      t = t + hd_imp_time 0 hd_state;
      full_adder_tail_i' = hd_ret hd_ret_state;
      t = t + 2;
      full_adder_tail_v' = map_adder_acc_v s;
      t = t + 2;
      full_adder_tail_ret' = 0;
      t = t + 2;
      full_adder_tail_state = \<lparr>full_adder_tail_i = full_adder_tail_i',
                               full_adder_tail_v = full_adder_tail_v',
                               full_adder_tail_ret = full_adder_tail_ret'\<rparr>;
      full_adder_tail_ret_state = full_adder_tail_imp full_adder_tail_state;
      t = t + full_adder_tail_imp_time 0 full_adder_tail_state;
      cons_h' = full_adder_tail_ret full_adder_tail_ret_state;
      t = t + 2;
      cons_t' = map_adder_acc_acc s;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      map_adder_acc_acc' = cons_ret cons_ret_state;
      t = t + 2;
      tl_xs' = map_adder_acc_n s;
      t = t + 2;
      tl_ret' = 0;
      t = t + 2;
      tl_state = \<lparr>tl_xs = tl_xs',
                  tl_ret = tl_ret'\<rparr>;
      tl_ret_state = tl_imp tl_state;
      t = t + tl_imp_time 0 tl_state;
      map_adder_acc_n' = tl_ret tl_ret_state;
      t = t + 2;
      ret = \<lparr>map_adder_acc_acc = map_adder_acc_acc',
             map_adder_acc_v = map_adder_acc_v s,
             map_adder_acc_n = map_adder_acc_n',
             map_adder_acc_ret = map_adder_acc_ret s\<rparr>
  in
      t
)"

definition "map_adder_acc_imp_compute_loop_condition_time t s \<equiv>
  (let
      condition = map_adder_acc_n s;
      t = t + 2
  in
      t
)"

definition "map_adder_acc_imp_after_loop_time t s \<equiv>
  (let
      map_adder_acc_ret' = map_adder_acc_acc s;
      t = t + 2;
      ret = \<lparr>map_adder_acc_acc = map_adder_acc_acc s,
             map_adder_acc_v = map_adder_acc_v s,
             map_adder_acc_n = map_adder_acc_n s,
             map_adder_acc_ret = map_adder_acc_ret'\<rparr>
  in
      t
)"

lemmas map_adder_acc_imp_subprogram_time_simps = 
  map_adder_acc_state_upd_time_def
  map_adder_acc_imp_compute_loop_condition_time_def
  map_adder_acc_imp_after_loop_time_def
  map_adder_acc_imp_subprogram_simps

function map_adder_acc_imp_time::
  "nat \<Rightarrow> map_adder_acc_state \<Rightarrow> nat" where
  "map_adder_acc_imp_time t s =
  map_adder_acc_imp_compute_loop_condition_time 0 s +
  (if map_adder_acc_imp_compute_loop_condition s \<noteq> 0
    then
      (let
        t = t + 1;
        next_iteration =
          map_adder_acc_imp_time (t + map_adder_acc_state_upd_time 0 s)
                         (map_adder_acc_state_upd s)
       in next_iteration)
    else
      (let
        t = t + 2;
        ret = t + map_adder_acc_imp_after_loop_time 0 s
       in ret)
  )"
  by auto
termination
  apply (relation "measure (map_adder_acc_n \<circ> snd)")
  by (simp add: map_adder_acc_imp_subprogram_time_simps tl_imp_correct)+

declare map_adder_acc_imp_time.simps [simp del]   

lemma map_adder_acc_imp_time_acc:
  "(map_adder_acc_imp_time (Suc t) s) = Suc (map_adder_acc_imp_time t s)"
  by (induction t s rule: map_adder_acc_imp_time.induct)
    ((subst (1 2) map_adder_acc_imp_time.simps);
      (simp add: map_adder_acc_state_upd_def))            

lemma map_adder_acc_imp_time_acc_2_aux:
  "(map_adder_acc_imp_time t s) = t + (map_adder_acc_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: map_adder_acc_imp_time_acc)+            

lemma map_adder_acc_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (map_adder_acc_imp_time t s) = t + (map_adder_acc_imp_time 0 s)"
  by (rule map_adder_acc_imp_time_acc_2_aux)            

lemma map_adder_acc_imp_time_acc_3:
  "(map_adder_acc_imp_time (a + b) s) = a + (map_adder_acc_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: map_adder_acc_imp_time_acc)+  

abbreviation "map_adder_acc_while_cond \<equiv> ''condition''"

definition "map_adder_acc_IMP_init_while_cond \<equiv>
  \<comment> \<open>  condition = map_adder_acc_n s\<close>
  (map_adder_acc_while_cond) ::= (A (V map_adder_acc_n_str))
"

definition "map_adder_acc_IMP_loop_body \<equiv>
  \<comment> \<open>  hd_xs' = map_adder_acc_n s;\<close>
  (hd_prefix @ hd_xs_str) ::= (A (V map_adder_acc_n_str));;
  \<comment> \<open>  hd_ret' = 0;\<close>
  (hd_prefix @ hd_ret_str) ::= (A (N 0));;
  \<comment> \<open>  hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;\<close>
  \<comment> \<open>  hd_ret_state = hd_imp hd_state;\<close>
  (invoke_subprogram hd_prefix hd_IMP_Minus);;
  \<comment> \<open>  full_adder_tail_i' = hd_ret hd_ret_state;\<close>
  (full_adder_tail_prefix @ full_adder_tail_i_str) ::= (A (V (hd_prefix @ hd_ret_str)));;
  \<comment> \<open>  full_adder_tail_v' = map_adder_acc_v s;\<close>
  (full_adder_tail_prefix @ full_adder_tail_v_str) ::= (A (V map_adder_acc_v_str));;
  \<comment> \<open>  full_adder_tail_ret' = 0;\<close>
  (full_adder_tail_prefix @ full_adder_tail_ret_str) ::= (A (N 0));;
  \<comment> \<open>  full_adder_tail_state = \<lparr>full_adder_tail_i = full_adder_tail_i',\<close>
  \<comment> \<open>                           full_adder_tail_v = full_adder_tail_v',\<close>
  \<comment> \<open>                           full_adder_tail_ret = full_adder_tail_ret'\<rparr>;\<close>
  \<comment> \<open>  full_adder_tail_ret_state = full_adder_tail_imp full_adder_tail_state;\<close>
  (invoke_subprogram full_adder_tail_prefix full_adder_tail_IMP_Minus);;
  \<comment> \<open>  cons_h' = full_adder_tail_ret full_adder_tail_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (full_adder_tail_prefix @ full_adder_tail_ret_str)));;
  \<comment> \<open>  cons_t' = map_adder_acc_acc s;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V map_adder_acc_acc_str));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  map_adder_acc_acc' = cons_ret cons_ret_state;\<close>
  (map_adder_acc_acc_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  tl_xs' = map_adder_acc_n s;\<close>
  (tl_prefix @ tl_xs_str) ::= (A (V map_adder_acc_n_str));;
  \<comment> \<open>  tl_ret' = 0;\<close>
  (tl_prefix @ tl_ret_str) ::= (A (N 0));;
  \<comment> \<open>  tl_state = \<lparr>tl_xs = tl_xs',\<close>
  \<comment> \<open>              tl_ret = tl_ret'\<rparr>;\<close>
  \<comment> \<open>  tl_ret_state = tl_imp tl_state;\<close>
  (invoke_subprogram tl_prefix tl_IMP_Minus);;
  \<comment> \<open>  map_adder_acc_n' = tl_ret tl_ret_state;\<close>
  (map_adder_acc_n_str) ::= (A (V (tl_prefix @ tl_ret_str)))
  \<comment> \<open>  ret = \<lparr>map_adder_acc_acc = map_adder_acc_acc',\<close>
  \<comment> \<open>         map_adder_acc_v = map_adder_acc_v s,\<close>
  \<comment> \<open>         map_adder_acc_n = map_adder_acc_n',\<close>
  \<comment> \<open>         map_adder_acc_ret = map_adder_acc_ret s\<rparr>\<close>
"

definition "map_adder_acc_IMP_after_loop \<equiv>
  \<comment> \<open>  map_adder_acc_ret' = map_adder_acc_acc s;\<close>
  (map_adder_acc_ret_str) ::= (A (V map_adder_acc_acc_str))
  \<comment> \<open>  ret = \<lparr>map_adder_acc_acc = map_adder_acc_acc s,\<close>
  \<comment> \<open>         map_adder_acc_v = map_adder_acc_v s,\<close>
  \<comment> \<open>         map_adder_acc_n = map_adder_acc_n s,\<close>
  \<comment> \<open>         map_adder_acc_ret = map_adder_acc_ret'\<rparr>\<close>
"

definition map_adder_acc_IMP_Minus where
  "map_adder_acc_IMP_Minus \<equiv>
  map_adder_acc_IMP_init_while_cond;;
  WHILE map_adder_acc_while_cond \<noteq>0 DO (
    map_adder_acc_IMP_loop_body;;
    map_adder_acc_IMP_init_while_cond
  );;
  map_adder_acc_IMP_after_loop"

abbreviation "map_adder_acc_IMP_vars \<equiv>
  {map_adder_acc_acc_str, map_adder_acc_v_str, map_adder_acc_n_str, map_adder_acc_ret_str}"

lemmas map_adder_acc_IMP_subprogram_simps =
  map_adder_acc_IMP_init_while_cond_def
  map_adder_acc_IMP_loop_body_def
  map_adder_acc_IMP_after_loop_def

definition "map_adder_acc_imp_to_HOL_state p s =
  \<lparr>map_adder_acc_acc = (s (add_prefix p map_adder_acc_acc_str)),
   map_adder_acc_v = (s (add_prefix p map_adder_acc_v_str)),
   map_adder_acc_n = (s (add_prefix p map_adder_acc_n_str)),
   map_adder_acc_ret = (s (add_prefix p map_adder_acc_ret_str))\<rparr>"

lemmas map_adder_acc_state_translators =
  map_adder_acc_imp_to_HOL_state_def
  hd_imp_to_HOL_state_def
  full_adder_tail_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  tl_imp_to_HOL_state_def

lemmas map_adder_acc_complete_simps =
  map_adder_acc_IMP_subprogram_simps
  map_adder_acc_imp_subprogram_simps
  map_adder_acc_state_translators

lemma map_adder_acc_IMP_Minus_correct_function:
  "(invoke_subprogram p map_adder_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p map_adder_acc_ret_str)
      = map_adder_acc_ret
          (map_adder_acc_imp (map_adder_acc_imp_to_HOL_state p s))"
  apply(induction "map_adder_acc_imp_to_HOL_state p s" arbitrary: s s' t
    rule: map_adder_acc_imp.induct)
  apply(subst map_adder_acc_imp.simps)
  apply(simp only: map_adder_acc_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule While_tE)

  subgoal
    apply(simp only: map_adder_acc_IMP_subprogram_simps prefix_simps)
    by(fastforce simp: map_adder_acc_IMP_subprogram_simps
        map_adder_acc_imp_subprogram_simps
        map_adder_acc_state_translators)

  apply(erule Seq_E)+
  apply(dest_com_gen)

  subgoal
      apply(simp only: map_adder_acc_IMP_init_while_cond_def prefix_simps)
      by(fastforce simp add: map_adder_acc_complete_simps)

  subgoal
      apply(subst (asm) map_adder_acc_IMP_init_while_cond_def)
      apply(simp only: map_adder_acc_IMP_loop_body_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule hd_IMP_Minus_correct[where vars = "map_adder_acc_IMP_vars"])
      subgoal premises p using p(21) by fastforce
      apply(erule full_adder_tail_IMP_Minus_correct[where vars = "map_adder_acc_IMP_vars"])
      subgoal premises p using p(23) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "map_adder_acc_IMP_vars"])
      subgoal premises p using p(25) by fastforce
      apply(erule tl_IMP_Minus_correct[where vars = "map_adder_acc_IMP_vars"])
      subgoal premises p using p(27) by fastforce
      by (fastforce_sorted_premises2 simp: map_adder_acc_imp_subprogram_simps
          map_adder_acc_state_translators Let_def)

  subgoal
      apply(simp only: map_adder_acc_IMP_init_while_cond_def prefix_simps
          map_adder_acc_IMP_loop_body_def)
      apply(erule Seq_E)+
      apply(erule hd_IMP_Minus_correct[where vars = "map_adder_acc_IMP_vars"])
      subgoal premises p using p(21) by fastforce
      apply(erule full_adder_tail_IMP_Minus_correct[where vars = "map_adder_acc_IMP_vars"])
      subgoal premises p using p(23) by fastforce
      apply(erule cons_IMP_Minus_correct[where vars = "map_adder_acc_IMP_vars"])
      subgoal premises p using p(25) by fastforce
      apply(erule tl_IMP_Minus_correct[where vars = "map_adder_acc_IMP_vars"])
      subgoal premises p using p(27) by fastforce
      by (fastforce_sorted_premises2 simp: map_adder_acc_imp_subprogram_simps
          map_adder_acc_state_translators Let_def)
  done   

lemma map_adder_acc_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ map_adder_acc_pref) map_adder_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix map_adder_acc_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemmas map_adder_acc_complete_time_simps =
  map_adder_acc_imp_subprogram_time_simps
  map_adder_acc_imp_time_acc
  map_adder_acc_imp_time_acc_2
  map_adder_acc_imp_time_acc_3
  map_adder_acc_state_translators

lemma map_adder_acc_IMP_Minus_correct_time:
  "(invoke_subprogram p map_adder_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = map_adder_acc_imp_time 0 (map_adder_acc_imp_to_HOL_state p s)"
  apply(induction "map_adder_acc_imp_to_HOL_state p s" arbitrary: s s' t
      rule: map_adder_acc_imp.induct)
  apply(subst map_adder_acc_imp_time.simps)
  apply(simp only: map_adder_acc_IMP_Minus_def prefix_simps)

  apply(erule Seq_tE)+
  apply(erule While_tE_time)

  subgoal
    apply(simp only: map_adder_acc_IMP_subprogram_simps prefix_simps)
    by (force simp: map_adder_acc_IMP_subprogram_simps
        map_adder_acc_imp_subprogram_time_simps map_adder_acc_state_translators)

  apply(erule Seq_tE)+
  apply(simp add: add.assoc)
  apply(dest_com_gen_time)

  subgoal
    apply(simp only: map_adder_acc_IMP_init_while_cond_def prefix_simps)
    by(fastforce simp add: map_adder_acc_complete_simps)

  subgoal
    apply(subst (asm) map_adder_acc_IMP_init_while_cond_def)
    apply(simp only: map_adder_acc_IMP_loop_body_def prefix_simps)
    apply(erule Seq_tE)+
    apply(erule hd_IMP_Minus_correct[where vars = "map_adder_acc_IMP_vars"])
    subgoal premises p using p(39) by fastforce
    apply(erule full_adder_tail_IMP_Minus_correct[where vars = "map_adder_acc_IMP_vars"])
    subgoal premises p using p(41) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "map_adder_acc_IMP_vars"])
    subgoal premises p using p(43) by fastforce
    apply(erule tl_IMP_Minus_correct[where vars = "map_adder_acc_IMP_vars"])
    subgoal premises p using p(45) by fastforce
    by (fastforce_sorted_premises2 simp: map_adder_acc_imp_subprogram_simps
        map_adder_acc_state_translators Let_def)

  subgoal
    apply(simp only: prefix_simps map_adder_acc_IMP_init_while_cond_def
        map_adder_acc_IMP_loop_body_def)
    apply(erule Seq_tE)+
    apply(erule hd_IMP_Minus_correct[where vars = "map_adder_acc_IMP_vars"])
    subgoal premises p using p(39) by fastforce
    apply(erule full_adder_tail_IMP_Minus_correct[where vars = "map_adder_acc_IMP_vars"])
    subgoal premises p using p(41) by fastforce
    apply(erule cons_IMP_Minus_correct[where vars = "map_adder_acc_IMP_vars"])
    subgoal premises p using p(43) by fastforce
    apply(erule tl_IMP_Minus_correct[where vars = "map_adder_acc_IMP_vars"])
    subgoal premises p using p(45) by fastforce
    apply(simp only: map_adder_acc_complete_time_simps Let_def)
    by (fastforce_sorted_premises simp: map_adder_acc_complete_time_simps Let_def)
  done   

lemma map_adder_acc_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) map_adder_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (map_adder_acc_imp_time 0 (map_adder_acc_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) map_adder_acc_ret_str) =
          map_adder_acc_ret (map_adder_acc_imp
                                        (map_adder_acc_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using map_adder_acc_IMP_Minus_correct_function
  by (auto simp: map_adder_acc_IMP_Minus_correct_time)
    (meson map_adder_acc_IMP_Minus_correct_effects set_mono_prefix)

subsubsection \<open>map_adder_tail\<close>

record map_adder_tail_state =
  map_adder_tail_v::nat
  map_adder_tail_n::nat
  map_adder_tail_ret::nat

abbreviation "map_adder_tail_prefix \<equiv> ''map_adder_tail.''"
abbreviation "map_adder_tail_v_str \<equiv> ''v''"
abbreviation "map_adder_tail_n_str \<equiv> ''n''"
abbreviation "map_adder_tail_ret_str \<equiv> ''ret''"

definition "map_adder_tail_state_upd s =
  (let
      map_adder_acc_acc' = 0;
      map_adder_acc_v' = map_adder_tail_v s;
      map_adder_acc_n' = map_adder_tail_n s;
      map_adder_acc_ret' = 0;
      map_adder_acc_state = \<lparr>map_adder_acc_acc = map_adder_acc_acc',
                             map_adder_acc_v = map_adder_acc_v',
                             map_adder_acc_n = map_adder_acc_n',
                             map_adder_acc_ret = map_adder_acc_ret'\<rparr>;
      map_adder_acc_ret_state = map_adder_acc_imp map_adder_acc_state;
      reverse_nat_n' = map_adder_acc_ret map_adder_acc_ret_state;
      reverse_nat_ret' = 0;
      reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n',
                           reverse_nat_ret = reverse_nat_ret'\<rparr>;
      reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;
      map_adder_tail_ret' = reverse_nat_ret reverse_nat_ret_state;
      ret = \<lparr>map_adder_tail_v = map_adder_tail_v s,
             map_adder_tail_n = map_adder_tail_n s,
             map_adder_tail_ret = map_adder_tail_ret'\<rparr>
  in
      ret
)"

function map_adder_tail_imp ::
  "map_adder_tail_state \<Rightarrow> map_adder_tail_state" where
  "map_adder_tail_imp s =
  (let 
      ret = map_adder_tail_state_upd s
    in 
      ret
  )"
  by simp+
termination
  by (relation "measure map_adder_tail_v") simp

declare map_adder_tail_imp.simps [simp del]

lemma map_adder_tail_imp_correct[let_function_correctness]:
  "map_adder_tail_ret (map_adder_tail_imp s) =
    map_adder_tail (map_adder_tail_v s) (map_adder_tail_n s)"
  apply (simp only: map_adder_tail_imp.simps Let_def map_adder_tail_state_upd_def
    map_adder_acc_imp_correct reverse_nat_imp_correct map_adder_tail_def)
  by simp  

function map_adder_tail_imp_time ::
  "nat \<Rightarrow> map_adder_tail_state \<Rightarrow> nat" where
  "map_adder_tail_imp_time t s =
  (let
      map_adder_acc_acc' = 0;
      t = t + 2;
      map_adder_acc_v' = map_adder_tail_v s;
      t = t + 2;
      map_adder_acc_n' = map_adder_tail_n s;
      t = t + 2;
      map_adder_acc_ret' = 0;
      t = t + 2;
      map_adder_acc_state = \<lparr>map_adder_acc_acc = map_adder_acc_acc',
                             map_adder_acc_v = map_adder_acc_v',
                             map_adder_acc_n = map_adder_acc_n',
                             map_adder_acc_ret = map_adder_acc_ret'\<rparr>;
      map_adder_acc_ret_state = map_adder_acc_imp map_adder_acc_state;
      t = t + map_adder_acc_imp_time 0 map_adder_acc_state;
      reverse_nat_n' = map_adder_acc_ret map_adder_acc_ret_state;
      t = t + 2;
      reverse_nat_ret' = 0;
      t = t + 2;
      reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n',
                           reverse_nat_ret = reverse_nat_ret'\<rparr>;
      reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;
      t = t + reverse_nat_imp_time 0 reverse_nat_state;
      map_adder_tail_ret' = reverse_nat_ret reverse_nat_ret_state;
      t = t + 2;
      ret = \<lparr>map_adder_tail_v = map_adder_tail_v s,
             map_adder_tail_n = map_adder_tail_n s,
             map_adder_tail_ret = map_adder_tail_ret'\<rparr>
  in
      t
  )"
  by auto
termination
  by (relation "measure (map_adder_tail_v \<circ> snd)") simp

declare map_adder_tail_imp_time.simps [simp del]

lemma map_adder_tail_imp_time_acc:
  "(map_adder_tail_imp_time (Suc t) s) = Suc (map_adder_tail_imp_time t s)"
  by (induction t s rule: map_adder_tail_imp_time.induct)
    ((subst (1 2) map_adder_tail_imp_time.simps);
      (simp add: map_adder_tail_state_upd_def Let_def))            

lemma map_adder_tail_imp_time_acc_2_aux:
  "(map_adder_tail_imp_time t s) = t + (map_adder_tail_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: map_adder_tail_imp_time_acc)+            

lemma map_adder_tail_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (map_adder_tail_imp_time t s) = t + (map_adder_tail_imp_time 0 s)"
  by (rule map_adder_tail_imp_time_acc_2_aux)            

lemma map_adder_tail_imp_time_acc_3:
  "(map_adder_tail_imp_time (a + b) s) = a + (map_adder_tail_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: map_adder_tail_imp_time_acc)+ 

definition map_adder_tail_IMP_Minus where
  "map_adder_tail_IMP_Minus \<equiv>
  \<comment> \<open>  map_adder_acc_acc' = 0;\<close>
  (map_adder_acc_prefix @ map_adder_acc_acc_str) ::= (A (N 0));;
  \<comment> \<open>  map_adder_acc_v' = map_adder_tail_v s;\<close>
  (map_adder_acc_prefix @ map_adder_acc_v_str) ::= (A (V map_adder_tail_v_str));;
  \<comment> \<open>  map_adder_acc_n' = map_adder_tail_n s;\<close>
  (map_adder_acc_prefix @ map_adder_acc_n_str) ::= (A (V map_adder_tail_n_str));;
  \<comment> \<open>  map_adder_acc_ret' = 0;\<close>
  (map_adder_acc_prefix @ map_adder_acc_ret_str) ::= (A (N 0));;
  \<comment> \<open>  map_adder_acc_state = \<lparr>map_adder_acc_acc = map_adder_acc_acc',\<close>
  \<comment> \<open>                         map_adder_acc_v = map_adder_acc_v',\<close>
  \<comment> \<open>                         map_adder_acc_n = map_adder_acc_n',\<close>
  \<comment> \<open>                         map_adder_acc_ret = map_adder_acc_ret'\<rparr>;\<close>
  \<comment> \<open>  map_adder_acc_ret_state = map_adder_acc_imp map_adder_acc_state;\<close>
  (invoke_subprogram map_adder_acc_prefix map_adder_acc_IMP_Minus);;
  \<comment> \<open>  reverse_nat_n' = map_adder_acc_ret map_adder_acc_ret_state;\<close>
  (reverse_nat_prefix @ reverse_nat_n_str) ::= (A (V (map_adder_acc_prefix @ map_adder_acc_ret_str)));;
  \<comment> \<open>  reverse_nat_ret' = 0;\<close>
  (reverse_nat_prefix @ reverse_nat_ret_str) ::= (A (N 0));;
  \<comment> \<open>  reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n',\<close>
  \<comment> \<open>                       reverse_nat_ret = reverse_nat_ret'\<rparr>;\<close>
  \<comment> \<open>  reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;\<close>
  (invoke_subprogram reverse_nat_prefix reverse_nat_IMP_Minus);;
  \<comment> \<open>  map_adder_tail_ret' = reverse_nat_ret reverse_nat_ret_state;\<close>
  (map_adder_tail_ret_str) ::= (A (V  (reverse_nat_prefix @ reverse_nat_ret_str)))
  \<comment> \<open>  ret = \<lparr>map_adder_tail_v = map_adder_tail_v s,\<close>
  \<comment> \<open>         map_adder_tail_n = map_adder_tail_n s,\<close>
  \<comment> \<open>         map_adder_tail_ret = map_adder_tail_ret'\<rparr>\<close>
"

abbreviation "map_adder_tail_IMP_vars \<equiv>
  {map_adder_tail_v_str, map_adder_tail_n_str, map_adder_tail_ret_str}"

definition "map_adder_tail_imp_to_HOL_state p s =
  \<lparr>map_adder_tail_v = (s (add_prefix p map_adder_tail_v_str)),
   map_adder_tail_n = (s (add_prefix p map_adder_tail_n_str)),
   map_adder_tail_ret = (s (add_prefix p map_adder_tail_ret_str))\<rparr>"

lemmas map_adder_tail_state_translators =
  map_adder_tail_imp_to_HOL_state_def
  map_adder_acc_imp_to_HOL_state_def
  reverse_nat_imp_to_HOL_state_def

lemma map_adder_tail_IMP_Minus_correct_function:
  "(invoke_subprogram p map_adder_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p map_adder_tail_ret_str)
      = map_adder_tail_ret
          (map_adder_tail_imp (map_adder_tail_imp_to_HOL_state p s))"
  apply(subst map_adder_tail_imp.simps)
  apply(simp only: map_adder_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule map_adder_acc_IMP_Minus_correct[where vars = "map_adder_tail_IMP_vars"])
  subgoal premises p using p(9) by fastforce
  apply(erule reverse_nat_IMP_Minus_correct[where vars = "map_adder_tail_IMP_vars"])
  subgoal premises p using p(11) by fastforce
  by(fastforce simp: map_adder_tail_state_translators
    map_adder_tail_state_upd_def)        

lemma map_adder_tail_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ map_adder_tail_pref) map_adder_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix map_adder_tail_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast     

lemma map_adder_tail_IMP_Minus_correct_time:
  "(invoke_subprogram p map_adder_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = map_adder_tail_imp_time 0 (map_adder_tail_imp_to_HOL_state p s)"
  apply(subst map_adder_tail_imp_time.simps)
  apply(simp only: map_adder_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule map_adder_acc_IMP_Minus_correct[where vars = "map_adder_tail_IMP_vars"])
  subgoal premises p using p(17) by fastforce
  apply(erule reverse_nat_IMP_Minus_correct[where vars = "map_adder_tail_IMP_vars"])
  subgoal premises p using p(19) by fastforce
  by(fastforce simp add: Let_def map_adder_tail_state_translators)        

lemma map_adder_tail_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) map_adder_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (map_adder_tail_imp_time 0 (map_adder_tail_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) map_adder_tail_ret_str) =
          map_adder_tail_ret (map_adder_tail_imp
                                        (map_adder_tail_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using map_adder_tail_IMP_Minus_correct_function
    map_adder_tail_IMP_Minus_correct_time
    map_adder_tail_IMP_Minus_correct_effects
  by (meson set_mono_prefix) 

subsection \<open>adder_tail\<close>

record adder_tail_state =
  adder_tail_n::nat
  adder_tail_v::nat
  adder_tail_ret::nat

abbreviation "adder_tail_prefix \<equiv> ''adder_tail.''"
abbreviation "adder_tail_n_str \<equiv> ''n''"
abbreviation "adder_tail_v_str \<equiv> ''v''"
abbreviation "adder_tail_ret_str \<equiv> ''ret''"

definition "adder_tail_state_upd s =
  (let
      cons_h' = 0;
      cons_t' = 0;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_h' = carry_vname_encode_as_nat;
      cons_t' = cons_ret cons_ret_state;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_h' = 1;
      cons_t' = cons_ret cons_ret_state;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_h' = cons_ret cons_ret_state;
      cons_t' = 0;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_result = cons_ret cons_ret_state;
      list_less_tail_n' = adder_tail_n s;
      list_less_tail_ret' = 0;
      list_less_tail_state = \<lparr>list_less_tail_n = list_less_tail_n',
                              list_less_tail_ret = list_less_tail_ret'\<rparr>;
      list_less_tail_ret_state = list_less_tail_imp list_less_tail_state;
      map_adder_tail_v' = adder_tail_v s;
      map_adder_tail_n' = list_less_tail_ret list_less_tail_ret_state;
      map_adder_tail_ret' = 0;
      map_adder_tail_state = \<lparr>map_adder_tail_v = map_adder_tail_v',
                              map_adder_tail_n = map_adder_tail_n',
                              map_adder_tail_ret = map_adder_tail_ret'\<rparr>;
      map_adder_tail_ret_state = map_adder_tail_imp map_adder_tail_state;
      com_list_to_seq_tail_ys' = map_adder_tail_ret map_adder_tail_ret_state;
      com_list_to_seq_tail_ret' = 0;
      com_list_to_seq_tail_state = \<lparr>com_list_to_seq_tail_ys = com_list_to_seq_tail_ys',
                                    com_list_to_seq_tail_ret = com_list_to_seq_tail_ret'\<rparr>;
      com_list_to_seq_tail_ret_state = com_list_to_seq_tail_imp com_list_to_seq_tail_state;
      cons_h' = com_list_to_seq_tail_ret com_list_to_seq_tail_ret_state;
      cons_t' = cons_result;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_h' = 2;
      cons_t' = cons_ret cons_ret_state;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      adder_tail_ret' = cons_ret cons_ret_state;
      ret = \<lparr>adder_tail_n = adder_tail_n s,
             adder_tail_v = adder_tail_v s,
             adder_tail_ret = adder_tail_ret'\<rparr>
  in
      ret
)"

function adder_tail_imp ::
  "adder_tail_state \<Rightarrow> adder_tail_state" where
  "adder_tail_imp s =
  (let 
      ret = adder_tail_state_upd s
    in 
      ret
  )"
  by simp+
termination
  by (relation "measure adder_tail_n") simp

declare adder_tail_imp.simps [simp del]

lemma adder_tail_imp_correct[let_function_correctness]:
  "adder_tail_ret (adder_tail_imp s) =
    adder_tail (adder_tail_n s) (adder_tail_v s)"
  by (simp add: adder_tail_imp.simps Let_def adder_tail_state_upd_def cons_imp_correct
    list_less_tail_imp_correct map_adder_tail_imp_correct com_list_to_seq_tail_imp_correct
    carry_vname_encode_val adder_tail_def)

function adder_tail_imp_time ::
  "nat \<Rightarrow> adder_tail_state \<Rightarrow> nat" where
  "adder_tail_imp_time t s =
  (let
      cons_h' = 0;
      t = t + 2;
      cons_t' = 0;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_h' = carry_vname_encode_as_nat;
      t = t + 2;
      cons_t' = cons_ret cons_ret_state;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_h' = 1;
      t = t + 2;
      cons_t' = cons_ret cons_ret_state;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_h' = cons_ret cons_ret_state;
      t = t + 2;
      cons_t' = 0;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_result = cons_ret cons_ret_state;
      t = t + 2;
      list_less_tail_n' = adder_tail_n s;
      t = t + 2;
      list_less_tail_ret' = 0;
      t = t + 2;
      list_less_tail_state = \<lparr>list_less_tail_n = list_less_tail_n',
                              list_less_tail_ret = list_less_tail_ret'\<rparr>;
      list_less_tail_ret_state = list_less_tail_imp list_less_tail_state;
      t = t + list_less_tail_imp_time 0 list_less_tail_state;
      map_adder_tail_v' = adder_tail_v s;
      t = t + 2;
      map_adder_tail_n' = list_less_tail_ret list_less_tail_ret_state;
      t = t + 2;
      map_adder_tail_ret' = 0;
      t = t + 2;
      map_adder_tail_state = \<lparr>map_adder_tail_v = map_adder_tail_v',
                              map_adder_tail_n = map_adder_tail_n',
                              map_adder_tail_ret = map_adder_tail_ret'\<rparr>;
      map_adder_tail_ret_state = map_adder_tail_imp map_adder_tail_state;
      t = t + map_adder_tail_imp_time 0 map_adder_tail_state;
      com_list_to_seq_tail_ys' = map_adder_tail_ret map_adder_tail_ret_state;
      t = t + 2;
      com_list_to_seq_tail_ret' = 0;
      t = t + 2;
      com_list_to_seq_tail_state = \<lparr>com_list_to_seq_tail_ys = com_list_to_seq_tail_ys',
                                    com_list_to_seq_tail_ret = com_list_to_seq_tail_ret'\<rparr>;
      com_list_to_seq_tail_ret_state = com_list_to_seq_tail_imp com_list_to_seq_tail_state;
      t = t + com_list_to_seq_tail_imp_time 0 com_list_to_seq_tail_state;
      cons_h' = com_list_to_seq_tail_ret com_list_to_seq_tail_ret_state;
      t = t + 2;
      cons_t' = cons_result;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_h' = 2;
      t = t + 2;
      cons_t' = cons_ret cons_ret_state;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      adder_tail_ret' = cons_ret cons_ret_state;
      t = t + 2;
      ret = \<lparr>adder_tail_n = adder_tail_n s,
             adder_tail_v = adder_tail_v s,
             adder_tail_ret = adder_tail_ret'\<rparr>
  in
      t
  )"
  by auto
termination
  by (relation "measure (adder_tail_n \<circ> snd)") simp

declare adder_tail_imp_time.simps [simp del]

lemma adder_tail_imp_time_acc:
  "(adder_tail_imp_time (Suc t) s) = Suc (adder_tail_imp_time t s)"
  by (induction t s rule: adder_tail_imp_time.induct)
    ((subst (1 2) adder_tail_imp_time.simps);
      (simp add: adder_tail_state_upd_def Let_def))            

lemma adder_tail_imp_time_acc_2_aux:
  "(adder_tail_imp_time t s) = t + (adder_tail_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: adder_tail_imp_time_acc)+            

lemma adder_tail_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (adder_tail_imp_time t s) = t + (adder_tail_imp_time 0 s)"
  by (rule adder_tail_imp_time_acc_2_aux)            

lemma adder_tail_imp_time_acc_3:
  "(adder_tail_imp_time (a + b) s) = a + (adder_tail_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: adder_tail_imp_time_acc)+   

abbreviation "adder_tail_cons_result \<equiv> ''cons_result''"

definition adder_tail_IMP_Minus where
  "adder_tail_IMP_Minus \<equiv>
  \<comment> \<open>  cons_h' = 0;\<close>
  (cons_prefix @ cons_h_str) ::= (A (N 0));;
  \<comment> \<open>  cons_t' = 0;\<close>
  (cons_prefix @ cons_t_str) ::= (A (N 0));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_h' = carry_vname_encode_as_nat;\<close>
  (cons_prefix @ cons_h_str) ::= (A (N carry_vname_encode_as_nat));;
  \<comment> \<open>  cons_t' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_h' = 1;\<close>
  (cons_prefix @ cons_h_str) ::= (A (N 1));;
  \<comment> \<open>  cons_t' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_h' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_t' = 0;\<close>
  (cons_prefix @ cons_t_str) ::= (A (N 0));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_result = cons_ret cons_ret_state;\<close>
  (adder_tail_cons_result) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  list_less_tail_n' = adder_tail_n s;\<close>
  (list_less_tail_prefix @ list_less_tail_n_str) ::= (A (V adder_tail_n_str));;
  \<comment> \<open>  list_less_tail_ret' = 0;\<close>
  (list_less_tail_prefix @ list_less_tail_ret_str) ::= (A (N 0));;
  \<comment> \<open>  list_less_tail_state = \<lparr>list_less_tail_n = list_less_tail_n',\<close>
  \<comment> \<open>                          list_less_tail_ret = list_less_tail_ret'\<rparr>;\<close>
  \<comment> \<open>  list_less_tail_ret_state = list_less_tail_imp list_less_tail_state;\<close>
  (invoke_subprogram list_less_tail_prefix list_less_tail_IMP_Minus);;
  \<comment> \<open>  map_adder_tail_v' = adder_tail_v s;\<close>
  (map_adder_tail_prefix @ map_adder_tail_v_str) ::= (A (V adder_tail_v_str));;
  \<comment> \<open>  map_adder_tail_n' = list_less_tail_ret list_less_tail_ret_state;\<close>
  (map_adder_tail_prefix @ map_adder_tail_n_str) ::= (A (V (list_less_tail_prefix @ list_less_tail_ret_str)));;
  \<comment> \<open>  map_adder_tail_ret' = 0;\<close>
  (map_adder_tail_prefix @ map_adder_tail_ret_str) ::= (A (N 0));;
  \<comment> \<open>  map_adder_tail_state = \<lparr>map_adder_tail_v = map_adder_tail_v',\<close>
  \<comment> \<open>                          map_adder_tail_n = map_adder_tail_n',\<close>
  \<comment> \<open>                          map_adder_tail_ret = map_adder_tail_ret'\<rparr>;\<close>
  \<comment> \<open>  map_adder_tail_ret_state = map_adder_tail_imp map_adder_tail_state;\<close>
  (invoke_subprogram map_adder_tail_prefix map_adder_tail_IMP_Minus);;
  \<comment> \<open>  com_list_to_seq_tail_ys' = map_adder_tail_ret map_adder_tail_ret_state;\<close>
  (com_list_to_seq_tail_prefix @ com_list_to_seq_tail_ys_str) ::= (A (V (map_adder_tail_prefix @ map_adder_tail_ret_str)));;
  \<comment> \<open>  com_list_to_seq_tail_ret' = 0;\<close>
  (com_list_to_seq_tail_prefix @ com_list_to_seq_tail_ret_str) ::= (A (N 0));;
  \<comment> \<open>  com_list_to_seq_tail_state = \<lparr>com_list_to_seq_tail_ys = com_list_to_seq_tail_ys',\<close>
  \<comment> \<open>                                com_list_to_seq_tail_ret = com_list_to_seq_tail_ret'\<rparr>;\<close>
  \<comment> \<open>  com_list_to_seq_tail_ret_state = com_list_to_seq_tail_imp com_list_to_seq_tail_state;\<close>
  (invoke_subprogram com_list_to_seq_tail_prefix com_list_to_seq_tail_IMP_Minus);;
  \<comment> \<open>  cons_h' = com_list_to_seq_tail_ret com_list_to_seq_tail_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (com_list_to_seq_tail_prefix @ com_list_to_seq_tail_ret_str)));;
  \<comment> \<open>  cons_t' = cons_result;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V adder_tail_cons_result));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_h' = 2;\<close>
  (cons_prefix @ cons_h_str) ::= (A (N 2));;
  \<comment> \<open>  cons_t' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  adder_tail_ret' = cons_ret cons_ret_state;\<close>
  (adder_tail_ret_str) ::= (A (V (cons_prefix @ cons_ret_str)))
  \<comment> \<open>  ret = \<lparr>adder_tail_n = adder_tail_n s,\<close>
  \<comment> \<open>         adder_tail_v = adder_tail_v s,\<close>
  \<comment> \<open>         adder_tail_ret = adder_tail_ret'\<rparr>\<close>
"

abbreviation "adder_tail_IMP_vars \<equiv>
  {adder_tail_n_str, adder_tail_v_str, adder_tail_ret_str, adder_tail_cons_result}"

definition "adder_tail_imp_to_HOL_state p s =
  \<lparr>adder_tail_n = (s (add_prefix p adder_tail_n_str)),
   adder_tail_v = (s (add_prefix p adder_tail_v_str)),
   adder_tail_ret = (s (add_prefix p adder_tail_ret_str))\<rparr>"

lemmas adder_tail_state_translators =
  adder_tail_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  list_less_tail_imp_to_HOL_state_def
  map_adder_tail_imp_to_HOL_state_def
  com_list_to_seq_tail_imp_to_HOL_state_def

lemma adder_tail_IMP_Minus_correct_function:
  "(invoke_subprogram p adder_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p adder_tail_ret_str)
      = adder_tail_ret
          (adder_tail_imp (adder_tail_imp_to_HOL_state p s))"
  apply(subst adder_tail_imp.simps)
  apply(simp only: adder_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule cons_IMP_Minus_correct[where vars = "adder_tail_IMP_vars"])
  subgoal premises p using p(36) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "adder_tail_IMP_vars"])
  subgoal premises p using p(38) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "adder_tail_IMP_vars"])
  subgoal premises p using p(40) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "adder_tail_IMP_vars"])
  subgoal premises p using p(42) by fastforce
  apply(erule list_less_tail_IMP_Minus_correct[where vars = "adder_tail_IMP_vars"])
  subgoal premises p using p(44) by fastforce
  apply(erule map_adder_tail_IMP_Minus_correct[where vars = "adder_tail_IMP_vars"])
  subgoal premises p using p(46) by fastforce
  apply(erule com_list_to_seq_tail_IMP_Minus_correct[where vars = "adder_tail_IMP_vars"])
  subgoal premises p using p(48) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "adder_tail_IMP_vars"])
  subgoal premises p using p(50) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "adder_tail_IMP_vars"])
  subgoal premises p using p(52) by fastforce
  by(force simp: adder_tail_state_translators adder_tail_state_upd_def)  

lemma adder_tail_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ adder_tail_pref) adder_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix adder_tail_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemma adder_tail_IMP_Minus_correct_time:
  "(invoke_subprogram p adder_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = adder_tail_imp_time 0 (adder_tail_imp_to_HOL_state p s)"
  apply(subst adder_tail_imp_time.simps)
  apply(simp only: adder_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule cons_IMP_Minus_correct[where vars = "adder_tail_IMP_vars"])
  subgoal premises p using p(71) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "adder_tail_IMP_vars"])
  subgoal premises p using p(73) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "adder_tail_IMP_vars"])
  subgoal premises p using p(75) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "adder_tail_IMP_vars"])
  subgoal premises p using p(77) by fastforce
  apply(erule list_less_tail_IMP_Minus_correct[where vars = "adder_tail_IMP_vars"])
  subgoal premises p using p(79) by fastforce
  apply(erule map_adder_tail_IMP_Minus_correct[where vars = "adder_tail_IMP_vars"])
  subgoal premises p using p(81) by fastforce
  apply(erule com_list_to_seq_tail_IMP_Minus_correct[where vars = "adder_tail_IMP_vars"])
  subgoal premises p using p(83) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "adder_tail_IMP_vars"])
  subgoal premises p using p(85) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "adder_tail_IMP_vars"])
  subgoal premises p using p(87) by fastforce
  by(force simp add: Let_def adder_tail_state_translators)  

lemma adder_tail_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) adder_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (adder_tail_imp_time 0 (adder_tail_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) adder_tail_ret_str) =
          adder_tail_ret (adder_tail_imp
                                        (adder_tail_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using adder_tail_IMP_Minus_correct_function
    adder_tail_IMP_Minus_correct_time
    adder_tail_IMP_Minus_correct_effects
  by (meson set_mono_prefix)

subsection \<open>binary_adder\<close>

subsubsection \<open>binary_adder_tail_aux1\<close>

fun binary_adder_tail_aux1 :: "nat \<Rightarrow> nat" where
  "binary_adder_tail_aux1 n = 
    (2 ## (copy_atom_to_operand_tail n (encode_char(CHR ''a'')) (prod_encode(1,0))) ## 
    (copy_atom_to_operand_tail n (encode_char(CHR ''b'')) (prod_encode(1,0))) ## 0)"

record binary_adder_tail_aux1_state =
  binary_adder_tail_aux1_n::nat
  binary_adder_tail_aux1_ret::nat

abbreviation "binary_adder_tail_aux1_prefix \<equiv> ''binary_adder_tail_aux1.''"
abbreviation "binary_adder_tail_aux1_n_str \<equiv> ''n''"
abbreviation "binary_adder_tail_aux1_ret_str \<equiv> ''ret''"

definition "binary_adder_tail_aux1_state_upd s =
  (let
      prod_encode_a' = 1;
      prod_encode_b' = 0;
      prod_encode_ret' = 0;
      prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                           prod_encode_b = prod_encode_b',
                           prod_encode_ret = prod_encode_ret'\<rparr>;
      prod_encode_ret_state = prod_encode_imp prod_encode_state;
      copy_atom_to_operand_tail_n' = binary_adder_tail_aux1_n s;
      copy_atom_to_operand_tail_op' = b_encode_char_as_nat;
      copy_atom_to_operand_tail_a' = prod_encode_ret prod_encode_ret_state;
      copy_atom_to_operand_tail_ret' = 0;
      copy_atom_to_operand_tail_state = \<lparr>copy_atom_to_operand_tail_n = copy_atom_to_operand_tail_n',
                                         copy_atom_to_operand_tail_op = copy_atom_to_operand_tail_op',
                                         copy_atom_to_operand_tail_a = copy_atom_to_operand_tail_a',
                                         copy_atom_to_operand_tail_ret = copy_atom_to_operand_tail_ret'\<rparr>;
      copy_atom_to_operand_tail_ret_state = copy_atom_to_operand_tail_imp copy_atom_to_operand_tail_state;
      cons_h' = copy_atom_to_operand_tail_ret copy_atom_to_operand_tail_ret_state;
      cons_t' = 0;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_result = cons_ret cons_ret_state;
      prod_encode_a' = 1;
      prod_encode_b' = 0;
      prod_encode_ret' = 0;
      prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                           prod_encode_b = prod_encode_b',
                           prod_encode_ret = prod_encode_ret'\<rparr>;
      prod_encode_ret_state = prod_encode_imp prod_encode_state;
      copy_atom_to_operand_tail_n' = binary_adder_tail_aux1_n s;
      copy_atom_to_operand_tail_op' = a_encode_char_as_nat;
      copy_atom_to_operand_tail_a' = prod_encode_ret prod_encode_ret_state;
      copy_atom_to_operand_tail_ret' = 0;
      copy_atom_to_operand_tail_state = \<lparr>copy_atom_to_operand_tail_n = copy_atom_to_operand_tail_n',
                                         copy_atom_to_operand_tail_op = copy_atom_to_operand_tail_op',
                                         copy_atom_to_operand_tail_a = copy_atom_to_operand_tail_a',
                                         copy_atom_to_operand_tail_ret = copy_atom_to_operand_tail_ret'\<rparr>;
      copy_atom_to_operand_tail_ret_state = copy_atom_to_operand_tail_imp copy_atom_to_operand_tail_state;
      cons_h' = copy_atom_to_operand_tail_ret copy_atom_to_operand_tail_ret_state;
      cons_t' = cons_result;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_h' = 2;
      cons_t' = cons_ret cons_ret_state;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      binary_adder_tail_aux1_ret' = cons_ret cons_ret_state;
      ret = \<lparr>binary_adder_tail_aux1_n = binary_adder_tail_aux1_n s,
             binary_adder_tail_aux1_ret = binary_adder_tail_aux1_ret'\<rparr>
  in
      ret
)"

function binary_adder_tail_aux1_imp ::
  "binary_adder_tail_aux1_state \<Rightarrow> binary_adder_tail_aux1_state" where
  "binary_adder_tail_aux1_imp s =
  (let 
      ret = binary_adder_tail_aux1_state_upd s
    in 
      ret
  )"
  by simp+
termination
  by (relation "measure binary_adder_tail_aux1_n") simp

declare binary_adder_tail_aux1_imp.simps [simp del]

lemma binary_adder_tail_aux1_imp_correct[let_function_correctness]:
  "binary_adder_tail_aux1_ret (binary_adder_tail_aux1_imp s) =
    binary_adder_tail_aux1 (binary_adder_tail_aux1_n s)"
  apply (simp only: binary_adder_tail_aux1_imp.simps Let_def binary_adder_tail_aux1_state_upd_def
    prod_encode_imp_correct copy_atom_to_operand_tail_imp_correct cons_imp_correct a_encode_char_val
    b_encode_char_val binary_adder_tail_aux1.simps)
  by simp 

function binary_adder_tail_aux1_imp_time ::
  "nat \<Rightarrow> binary_adder_tail_aux1_state \<Rightarrow> nat" where
  "binary_adder_tail_aux1_imp_time t s =
  (let
      prod_encode_a' = 1;
      t = t + 2;
      prod_encode_b' = 0;
      t = t + 2;
      prod_encode_ret' = 0;
      t = t + 2;
      prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                           prod_encode_b = prod_encode_b',
                           prod_encode_ret = prod_encode_ret'\<rparr>;
      prod_encode_ret_state = prod_encode_imp prod_encode_state;
      t = t + prod_encode_imp_time 0 prod_encode_state;
      copy_atom_to_operand_tail_n' = binary_adder_tail_aux1_n s;
      t = t + 2;
      copy_atom_to_operand_tail_op' = b_encode_char_as_nat;
      t = t + 2;
      copy_atom_to_operand_tail_a' = prod_encode_ret prod_encode_ret_state;
      t = t + 2;
      copy_atom_to_operand_tail_ret' = 0;
      t = t + 2;
      copy_atom_to_operand_tail_state = \<lparr>copy_atom_to_operand_tail_n = copy_atom_to_operand_tail_n',
                                         copy_atom_to_operand_tail_op = copy_atom_to_operand_tail_op',
                                         copy_atom_to_operand_tail_a = copy_atom_to_operand_tail_a',
                                         copy_atom_to_operand_tail_ret = copy_atom_to_operand_tail_ret'\<rparr>;
      copy_atom_to_operand_tail_ret_state = copy_atom_to_operand_tail_imp copy_atom_to_operand_tail_state;
      t = t + copy_atom_to_operand_tail_imp_time 0 copy_atom_to_operand_tail_state;
      cons_h' = copy_atom_to_operand_tail_ret copy_atom_to_operand_tail_ret_state;
      t = t + 2;
      cons_t' = 0;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_result = cons_ret cons_ret_state;
      t = t + 2;
      prod_encode_a' = 1;
      t = t + 2;
      prod_encode_b' = 0;
      t = t + 2;
      prod_encode_ret' = 0;
      t = t + 2;
      prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                           prod_encode_b = prod_encode_b',
                           prod_encode_ret = prod_encode_ret'\<rparr>;
      prod_encode_ret_state = prod_encode_imp prod_encode_state;
      t = t + prod_encode_imp_time 0 prod_encode_state;
      copy_atom_to_operand_tail_n' = binary_adder_tail_aux1_n s;
      t = t + 2;
      copy_atom_to_operand_tail_op' = a_encode_char_as_nat;
      t = t + 2;
      copy_atom_to_operand_tail_a' = prod_encode_ret prod_encode_ret_state;
      t = t + 2;
      copy_atom_to_operand_tail_ret' = 0;
      t = t + 2;
      copy_atom_to_operand_tail_state = \<lparr>copy_atom_to_operand_tail_n = copy_atom_to_operand_tail_n',
                                         copy_atom_to_operand_tail_op = copy_atom_to_operand_tail_op',
                                         copy_atom_to_operand_tail_a = copy_atom_to_operand_tail_a',
                                         copy_atom_to_operand_tail_ret = copy_atom_to_operand_tail_ret'\<rparr>;
      copy_atom_to_operand_tail_ret_state = copy_atom_to_operand_tail_imp copy_atom_to_operand_tail_state;
      t = t + copy_atom_to_operand_tail_imp_time 0 copy_atom_to_operand_tail_state;
      cons_h' = copy_atom_to_operand_tail_ret copy_atom_to_operand_tail_ret_state;
      t = t + 2;
      cons_t' = cons_result;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_h' = 2;
      t = t + 2;
      cons_t' = cons_ret cons_ret_state;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      binary_adder_tail_aux1_ret' = cons_ret cons_ret_state;
      t = t + 2;
      ret = \<lparr>binary_adder_tail_aux1_n = binary_adder_tail_aux1_n s,
             binary_adder_tail_aux1_ret = binary_adder_tail_aux1_ret'\<rparr>
  in
      t
  )"
  by auto
termination
  by (relation "measure (binary_adder_tail_aux1_n \<circ> snd)") simp

declare binary_adder_tail_aux1_imp_time.simps [simp del]

lemma binary_adder_tail_aux1_imp_time_acc:
  "(binary_adder_tail_aux1_imp_time (Suc t) s) = Suc (binary_adder_tail_aux1_imp_time t s)"
  by (induction t s rule: binary_adder_tail_aux1_imp_time.induct)
    ((subst (1 2) binary_adder_tail_aux1_imp_time.simps);
      (simp add: binary_adder_tail_aux1_state_upd_def Let_def))            

lemma binary_adder_tail_aux1_imp_time_acc_2_aux:
  "(binary_adder_tail_aux1_imp_time t s) = t + (binary_adder_tail_aux1_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: binary_adder_tail_aux1_imp_time_acc)+            

lemma binary_adder_tail_aux1_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (binary_adder_tail_aux1_imp_time t s) = t + (binary_adder_tail_aux1_imp_time 0 s)"
  by (rule binary_adder_tail_aux1_imp_time_acc_2_aux)            

lemma binary_adder_tail_aux1_imp_time_acc_3:
  "(binary_adder_tail_aux1_imp_time (a + b) s) = a + (binary_adder_tail_aux1_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: binary_adder_tail_aux1_imp_time_acc)+   

abbreviation "binary_adder_tail_aux1_cons_result \<equiv> ''cons_result''"

definition binary_adder_tail_aux1_IMP_Minus where
  "binary_adder_tail_aux1_IMP_Minus \<equiv>
  \<comment> \<open>  prod_encode_a' = 1;\<close>
  (prod_encode_prefix @ prod_encode_a_str) ::= (A (N 1));;
  \<comment> \<open>  prod_encode_b' = 0;\<close>
  (prod_encode_prefix @ prod_encode_b_str) ::= (A (N 0));;
  \<comment> \<open>  prod_encode_ret' = 0;\<close>
  (prod_encode_prefix @ prod_encode_ret_str) ::= (A (N 0));;
  \<comment> \<open>  prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',\<close>
  \<comment> \<open>                       prod_encode_b = prod_encode_b',\<close>
  \<comment> \<open>                       prod_encode_ret = prod_encode_ret'\<rparr>;\<close>
  \<comment> \<open>  prod_encode_ret_state = prod_encode_imp prod_encode_state;\<close>
  (invoke_subprogram prod_encode_prefix prod_encode_IMP_Minus);;
  \<comment> \<open>  copy_atom_to_operand_tail_n' = binary_adder_tail_aux1_n s;\<close>
  (copy_atom_to_operand_tail_prefix @ copy_atom_to_operand_tail_n_str) ::= (A (V binary_adder_tail_aux1_n_str));;
  \<comment> \<open>  copy_atom_to_operand_tail_op' = b_encode_char_as_nat;\<close>
  (copy_atom_to_operand_tail_prefix @ copy_atom_to_operand_tail_op_str) ::= (A (N b_encode_char_as_nat));;
  \<comment> \<open>  copy_atom_to_operand_tail_a' = prod_encode_ret prod_encode_ret_state;\<close>
  (copy_atom_to_operand_tail_prefix @ copy_atom_to_operand_tail_a_str) ::= (A (V (prod_encode_prefix @ prod_encode_ret_str)));;
  \<comment> \<open>  copy_atom_to_operand_tail_ret' = 0;\<close>
  (copy_atom_to_operand_tail_prefix @ copy_atom_to_operand_tail_ret_str) ::= (A (N 0));;
  \<comment> \<open>  copy_atom_to_operand_tail_state = \<lparr>copy_atom_to_operand_tail_n = copy_atom_to_operand_tail_n',\<close>
  \<comment> \<open>                                     copy_atom_to_operand_tail_op = copy_atom_to_operand_tail_op',\<close>
  \<comment> \<open>                                     copy_atom_to_operand_tail_a = copy_atom_to_operand_tail_a',\<close>
  \<comment> \<open>                                     copy_atom_to_operand_tail_ret = copy_atom_to_operand_tail_ret'\<rparr>;\<close>
  \<comment> \<open>  copy_atom_to_operand_tail_ret_state = copy_atom_to_operand_tail_imp copy_atom_to_operand_tail_state;\<close>
  (invoke_subprogram copy_atom_to_operand_tail_prefix copy_atom_to_operand_tail_IMP_Minus);;
  \<comment> \<open>  cons_h' = copy_atom_to_operand_tail_ret copy_atom_to_operand_tail_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (copy_atom_to_operand_tail_prefix @ copy_atom_to_operand_tail_ret_str)));;
  \<comment> \<open>  cons_t' = 0;\<close>
  (cons_prefix @ cons_t_str) ::= (A (N 0));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_result = cons_ret cons_ret_state;\<close>
  (binary_adder_tail_aux1_cons_result) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  prod_encode_a' = 1;\<close>
  (prod_encode_prefix @ prod_encode_a_str) ::= (A (N 1));;
  \<comment> \<open>  prod_encode_b' = 0;\<close>
  (prod_encode_prefix @ prod_encode_b_str) ::= (A (N 0));;
  \<comment> \<open>  prod_encode_ret' = 0;\<close>
  (prod_encode_prefix @ prod_encode_ret_str) ::= (A (N 0));;
  \<comment> \<open>  prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',\<close>
  \<comment> \<open>                       prod_encode_b = prod_encode_b',\<close>
  \<comment> \<open>                       prod_encode_ret = prod_encode_ret'\<rparr>;\<close>
  \<comment> \<open>  prod_encode_ret_state = prod_encode_imp prod_encode_state;\<close>
  (invoke_subprogram prod_encode_prefix prod_encode_IMP_Minus);;
  \<comment> \<open>  copy_atom_to_operand_tail_n' = binary_adder_tail_aux1_n s;\<close>
  (copy_atom_to_operand_tail_prefix @ copy_atom_to_operand_tail_n_str) ::= (A (V binary_adder_tail_aux1_n_str));;
  \<comment> \<open>  copy_atom_to_operand_tail_op' = a_encode_char_as_nat;\<close>
  (copy_atom_to_operand_tail_prefix @ copy_atom_to_operand_tail_op_str) ::= (A (N a_encode_char_as_nat));;
  \<comment> \<open>  copy_atom_to_operand_tail_a' = prod_encode_ret prod_encode_ret_state;\<close>
  (copy_atom_to_operand_tail_prefix @ copy_atom_to_operand_tail_a_str) ::= (A (V (prod_encode_prefix @ prod_encode_ret_str)));;
  \<comment> \<open>  copy_atom_to_operand_tail_ret' = 0;\<close>
  (copy_atom_to_operand_tail_prefix @ copy_atom_to_operand_tail_ret_str) ::= (A (N 0));;
  \<comment> \<open>  copy_atom_to_operand_tail_state = \<lparr>copy_atom_to_operand_tail_n = copy_atom_to_operand_tail_n',\<close>
  \<comment> \<open>                                     copy_atom_to_operand_tail_op = copy_atom_to_operand_tail_op',\<close>
  \<comment> \<open>                                     copy_atom_to_operand_tail_a = copy_atom_to_operand_tail_a',\<close>
  \<comment> \<open>                                     copy_atom_to_operand_tail_ret = copy_atom_to_operand_tail_ret'\<rparr>;\<close>
  \<comment> \<open>  copy_atom_to_operand_tail_ret_state = copy_atom_to_operand_tail_imp copy_atom_to_operand_tail_state;\<close>
  (invoke_subprogram copy_atom_to_operand_tail_prefix copy_atom_to_operand_tail_IMP_Minus);;
  \<comment> \<open>  cons_h' = copy_atom_to_operand_tail_ret copy_atom_to_operand_tail_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (copy_atom_to_operand_tail_prefix @ copy_atom_to_operand_tail_ret_str)));;
  \<comment> \<open>  cons_t' = cons_result;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V binary_adder_tail_aux1_cons_result));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_h' = 2;\<close>
  (cons_prefix @ cons_h_str) ::= (A (N 2));;
  \<comment> \<open>  cons_t' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  binary_adder_tail_aux1_ret' = cons_ret cons_ret_state;\<close>
  (binary_adder_tail_aux1_ret_str) ::= (A (V (cons_prefix @ cons_ret_str)))
  \<comment> \<open>  ret = \<lparr>binary_adder_tail_aux1_n = binary_adder_tail_aux1_n s,\<close>
  \<comment> \<open>         binary_adder_tail_aux1_ret = binary_adder_tail_aux1_ret'\<rparr>\<close>
"

abbreviation "binary_adder_tail_aux1_IMP_vars \<equiv>
  {binary_adder_tail_aux1_n_str, binary_adder_tail_aux1_ret_str, binary_adder_tail_aux1_cons_result}"

definition "binary_adder_tail_aux1_imp_to_HOL_state p s =
  \<lparr>binary_adder_tail_aux1_n = (s (add_prefix p binary_adder_tail_aux1_n_str)),
   binary_adder_tail_aux1_ret = (s (add_prefix p binary_adder_tail_aux1_ret_str))\<rparr>"

lemmas binary_adder_tail_aux1_state_translators =
  binary_adder_tail_aux1_imp_to_HOL_state_def
  prod_encode_imp_to_HOL_state_def
  copy_atom_to_operand_tail_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def

lemma binary_adder_tail_aux1_IMP_Minus_correct_function:
  "(invoke_subprogram p binary_adder_tail_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p binary_adder_tail_aux1_ret_str)
      = binary_adder_tail_aux1_ret
          (binary_adder_tail_aux1_imp (binary_adder_tail_aux1_imp_to_HOL_state p s))"
  apply(subst binary_adder_tail_aux1_imp.simps)
  apply(simp only: binary_adder_tail_aux1_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule prod_encode_IMP_Minus_correct[where vars = "binary_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(32) by fastforce
  apply(erule copy_atom_to_operand_tail_IMP_Minus_correct[where vars = "binary_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(34) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(36) by fastforce
  apply(erule prod_encode_IMP_Minus_correct[where vars = "binary_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(38) by fastforce
  apply(erule copy_atom_to_operand_tail_IMP_Minus_correct[where vars = "binary_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(40) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(42) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(44) by fastforce
  by(force simp: binary_adder_tail_aux1_state_translators
    binary_adder_tail_aux1_state_upd_def) 

lemma binary_adder_tail_aux1_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ binary_adder_tail_aux1_pref) binary_adder_tail_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix binary_adder_tail_aux1_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemma binary_adder_tail_aux1_IMP_Minus_correct_time:
  "(invoke_subprogram p binary_adder_tail_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = binary_adder_tail_aux1_imp_time 0 (binary_adder_tail_aux1_imp_to_HOL_state p s)"
  apply(subst binary_adder_tail_aux1_imp_time.simps)
  apply(simp only: binary_adder_tail_aux1_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule prod_encode_IMP_Minus_correct[where vars = "binary_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(63) by fastforce
  apply(erule copy_atom_to_operand_tail_IMP_Minus_correct[where vars = "binary_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(65) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(67) by fastforce
  apply(erule prod_encode_IMP_Minus_correct[where vars = "binary_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(69) by fastforce
  apply(erule copy_atom_to_operand_tail_IMP_Minus_correct[where vars = "binary_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(71) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(73) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_aux1_IMP_vars"])
  subgoal premises p using p(75) by fastforce
  by(force simp add: Let_def binary_adder_tail_aux1_state_translators)   

lemma binary_adder_tail_aux1_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) binary_adder_tail_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (binary_adder_tail_aux1_imp_time 0 (binary_adder_tail_aux1_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) binary_adder_tail_aux1_ret_str) =
          binary_adder_tail_aux1_ret (binary_adder_tail_aux1_imp
                                        (binary_adder_tail_aux1_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using binary_adder_tail_aux1_IMP_Minus_correct_function
    binary_adder_tail_aux1_IMP_Minus_correct_time
    binary_adder_tail_aux1_IMP_Minus_correct_effects
  by (meson set_mono_prefix) 

subsubsection \<open>binary_adder_tail_aux2\<close>

fun binary_adder_tail_aux2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "binary_adder_tail_aux2 n v b = 
    (copy_atom_to_operand_tail n (encode_char(CHR ''b'')) b) ## 
    (2 ## (adder_tail n v) ## (binary_adder_tail_aux1 n) ## 0) ## 0"

record binary_adder_tail_aux2_state =
  binary_adder_tail_aux2_n::nat
  binary_adder_tail_aux2_v::nat
  binary_adder_tail_aux2_b::nat
  binary_adder_tail_aux2_ret::nat

abbreviation "binary_adder_tail_aux2_prefix \<equiv> ''binary_adder_tail_aux2.''"
abbreviation "binary_adder_tail_aux2_n_str \<equiv> ''n''"
abbreviation "binary_adder_tail_aux2_v_str \<equiv> ''v''"
abbreviation "binary_adder_tail_aux2_b_str \<equiv> ''b''"
abbreviation "binary_adder_tail_aux2_ret_str \<equiv> ''ret''"

definition "binary_adder_tail_aux2_state_upd s =
  (let
      binary_adder_tail_aux1_n' = binary_adder_tail_aux2_n s;
      binary_adder_tail_aux1_ret' = 0;
      binary_adder_tail_aux1_state = \<lparr>binary_adder_tail_aux1_n = binary_adder_tail_aux1_n',
                                      binary_adder_tail_aux1_ret = binary_adder_tail_aux1_ret'\<rparr>;
      binary_adder_tail_aux1_ret_state = binary_adder_tail_aux1_imp binary_adder_tail_aux1_state;
      cons_h' = binary_adder_tail_aux1_ret binary_adder_tail_aux1_ret_state;
      cons_t' = 0;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_result = cons_ret cons_ret_state;
      adder_tail_n' = binary_adder_tail_aux2_n s;
      adder_tail_v' = binary_adder_tail_aux2_v s;
      adder_tail_ret' = 0;
      adder_tail_state = \<lparr>adder_tail_n = adder_tail_n',
                          adder_tail_v = adder_tail_v',
                          adder_tail_ret = adder_tail_ret'\<rparr>;
      adder_tail_ret_state = adder_tail_imp adder_tail_state;
      cons_h' = adder_tail_ret adder_tail_ret_state;
      cons_t' = cons_result;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_h' = 2;
      cons_t' = cons_ret cons_ret_state;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_result = cons_ret cons_ret_state;
      cons_h' = cons_result;
      cons_t' = 0;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_result = cons_ret cons_ret_state;
      copy_atom_to_operand_tail_n' = binary_adder_tail_aux2_n s;
      copy_atom_to_operand_tail_op' = b_encode_char_as_nat;
      copy_atom_to_operand_tail_a' = binary_adder_tail_aux2_b s;
      copy_atom_to_operand_tail_ret' = 0;
      copy_atom_to_operand_tail_state = \<lparr>copy_atom_to_operand_tail_n = copy_atom_to_operand_tail_n',
                                         copy_atom_to_operand_tail_op = copy_atom_to_operand_tail_op',
                                         copy_atom_to_operand_tail_a = copy_atom_to_operand_tail_a',
                                         copy_atom_to_operand_tail_ret = copy_atom_to_operand_tail_ret'\<rparr>;
      copy_atom_to_operand_tail_ret_state = copy_atom_to_operand_tail_imp copy_atom_to_operand_tail_state;
      cons_h' = copy_atom_to_operand_tail_ret copy_atom_to_operand_tail_ret_state;
      cons_t' = cons_result;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      binary_adder_tail_aux2_ret' = cons_ret cons_ret_state;
      ret = \<lparr>binary_adder_tail_aux2_n = binary_adder_tail_aux2_n s,
             binary_adder_tail_aux2_v = binary_adder_tail_aux2_v s,
             binary_adder_tail_aux2_b = binary_adder_tail_aux2_b s,
             binary_adder_tail_aux2_ret = binary_adder_tail_aux2_ret'\<rparr>
  in
      ret
)"

function binary_adder_tail_aux2_imp ::
  "binary_adder_tail_aux2_state \<Rightarrow> binary_adder_tail_aux2_state" where
  "binary_adder_tail_aux2_imp s =
  (let 
      ret = binary_adder_tail_aux2_state_upd s
    in 
      ret
  )"
  by simp+
termination
  by (relation "measure binary_adder_tail_aux2_n") simp

lemma binary_adder_tail_aux2_imp_correct[let_function_correctness]:
  "binary_adder_tail_aux2_ret (binary_adder_tail_aux2_imp s) =
    binary_adder_tail_aux2 (binary_adder_tail_aux2_n s) (binary_adder_tail_aux2_v s)
      (binary_adder_tail_aux2_b s)"
  apply (simp only: binary_adder_tail_aux2_imp.simps Let_def binary_adder_tail_aux2_state_upd_def
    binary_adder_tail_aux1_imp_correct cons_imp_correct adder_tail_imp_correct copy_atom_to_operand_tail_imp_correct
    b_encode_char_val binary_adder_tail_aux2.simps)
  by simp   

declare binary_adder_tail_aux2_imp.simps [simp del]

function binary_adder_tail_aux2_imp_time ::
  "nat \<Rightarrow> binary_adder_tail_aux2_state \<Rightarrow> nat" where
  "binary_adder_tail_aux2_imp_time t s =
  (let
      binary_adder_tail_aux1_n' = binary_adder_tail_aux2_n s;
      t = t + 2;
      binary_adder_tail_aux1_ret' = 0;
      t = t + 2;
      binary_adder_tail_aux1_state = \<lparr>binary_adder_tail_aux1_n = binary_adder_tail_aux1_n',
                                      binary_adder_tail_aux1_ret = binary_adder_tail_aux1_ret'\<rparr>;
      binary_adder_tail_aux1_ret_state = binary_adder_tail_aux1_imp binary_adder_tail_aux1_state;
      t = t + binary_adder_tail_aux1_imp_time 0 binary_adder_tail_aux1_state;
      cons_h' = binary_adder_tail_aux1_ret binary_adder_tail_aux1_ret_state;
      t = t + 2;
      cons_t' = 0;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_result = cons_ret cons_ret_state;
      t = t + 2;
      adder_tail_n' = binary_adder_tail_aux2_n s;
      t = t + 2;
      adder_tail_v' = binary_adder_tail_aux2_v s;
      t = t + 2;
      adder_tail_ret' = 0;
      t = t + 2;
      adder_tail_state = \<lparr>adder_tail_n = adder_tail_n',
                          adder_tail_v = adder_tail_v',
                          adder_tail_ret = adder_tail_ret'\<rparr>;
      adder_tail_ret_state = adder_tail_imp adder_tail_state;
      t = t + adder_tail_imp_time 0 adder_tail_state;
      cons_h' = adder_tail_ret adder_tail_ret_state;
      t = t + 2;
      cons_t' = cons_result;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_h' = 2;
      t = t + 2;
      cons_t' = cons_ret cons_ret_state;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_result = cons_ret cons_ret_state;
      t = t + 2;
      cons_h' = cons_result;
      t = t + 2;
      cons_t' = 0;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_result = cons_ret cons_ret_state;
      t = t + 2;
      copy_atom_to_operand_tail_n' = binary_adder_tail_aux2_n s;
      t = t + 2;
      copy_atom_to_operand_tail_op' = b_encode_char_as_nat;
      t = t + 2;
      copy_atom_to_operand_tail_a' = binary_adder_tail_aux2_b s;
      t = t + 2;
      copy_atom_to_operand_tail_ret' = 0;
      t = t + 2;
      copy_atom_to_operand_tail_state = \<lparr>copy_atom_to_operand_tail_n = copy_atom_to_operand_tail_n',
                                         copy_atom_to_operand_tail_op = copy_atom_to_operand_tail_op',
                                         copy_atom_to_operand_tail_a = copy_atom_to_operand_tail_a',
                                         copy_atom_to_operand_tail_ret = copy_atom_to_operand_tail_ret'\<rparr>;
      copy_atom_to_operand_tail_ret_state = copy_atom_to_operand_tail_imp copy_atom_to_operand_tail_state;
      t = t + copy_atom_to_operand_tail_imp_time 0 copy_atom_to_operand_tail_state;
      cons_h' = copy_atom_to_operand_tail_ret copy_atom_to_operand_tail_ret_state;
      t = t + 2;
      cons_t' = cons_result;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      binary_adder_tail_aux2_ret' = cons_ret cons_ret_state;
      t = t + 2;
      ret = \<lparr>binary_adder_tail_aux2_n = binary_adder_tail_aux2_n s,
             binary_adder_tail_aux2_v = binary_adder_tail_aux2_v s,
             binary_adder_tail_aux2_b = binary_adder_tail_aux2_b s,
             binary_adder_tail_aux2_ret = binary_adder_tail_aux2_ret'\<rparr>
  in
      t
  )"
  by auto
termination
  by (relation "measure (binary_adder_tail_aux2_n \<circ> snd)") simp

declare binary_adder_tail_aux2_imp_time.simps [simp del]

lemma binary_adder_tail_aux2_imp_time_acc:
  "(binary_adder_tail_aux2_imp_time (Suc t) s) = Suc (binary_adder_tail_aux2_imp_time t s)"
  by (induction t s rule: binary_adder_tail_aux2_imp_time.induct)
    ((subst (1 2) binary_adder_tail_aux2_imp_time.simps);
      (simp add: binary_adder_tail_aux2_state_upd_def Let_def))            

lemma binary_adder_tail_aux2_imp_time_acc_2_aux:
  "(binary_adder_tail_aux2_imp_time t s) = t + (binary_adder_tail_aux2_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: binary_adder_tail_aux2_imp_time_acc)+            

lemma binary_adder_tail_aux2_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (binary_adder_tail_aux2_imp_time t s) = t + (binary_adder_tail_aux2_imp_time 0 s)"
  by (rule binary_adder_tail_aux2_imp_time_acc_2_aux)            

lemma binary_adder_tail_aux2_imp_time_acc_3:
  "(binary_adder_tail_aux2_imp_time (a + b) s) = a + (binary_adder_tail_aux2_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: binary_adder_tail_aux2_imp_time_acc)+     

abbreviation "binary_adder_tail_aux2_cons_result \<equiv> ''cons_result''"

definition binary_adder_tail_aux2_IMP_Minus where
  "binary_adder_tail_aux2_IMP_Minus \<equiv>
  \<comment> \<open>  binary_adder_tail_aux1_n' = binary_adder_tail_aux2_n s;\<close>
  (binary_adder_tail_aux1_prefix @ binary_adder_tail_aux1_n_str) ::= (A (V binary_adder_tail_aux2_n_str));;
  \<comment> \<open>  binary_adder_tail_aux1_ret' = 0;\<close>
  (binary_adder_tail_aux1_prefix @ binary_adder_tail_aux1_ret_str) ::= (A (N 0));;
  \<comment> \<open>  binary_adder_tail_aux1_state = \<lparr>binary_adder_tail_aux1_n = binary_adder_tail_aux1_n',\<close>
  \<comment> \<open>                                  binary_adder_tail_aux1_ret = binary_adder_tail_aux1_ret'\<rparr>;\<close>
  \<comment> \<open>  binary_adder_tail_aux1_ret_state = binary_adder_tail_aux1_imp binary_adder_tail_aux1_state;\<close>
  (invoke_subprogram binary_adder_tail_aux1_prefix binary_adder_tail_aux1_IMP_Minus);;
  \<comment> \<open>  cons_h' = binary_adder_tail_aux1_ret binary_adder_tail_aux1_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (binary_adder_tail_aux1_prefix @ binary_adder_tail_aux1_ret_str)));;
  \<comment> \<open>  cons_t' = 0;\<close>
  (cons_prefix @ cons_t_str) ::= (A (N 0));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_result = cons_ret cons_ret_state;\<close>
  (binary_adder_tail_aux2_cons_result) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  adder_tail_n' = binary_adder_tail_aux2_n s;\<close>
  (adder_tail_prefix @ adder_tail_n_str) ::= (A (V binary_adder_tail_aux2_n_str));;
  \<comment> \<open>  adder_tail_v' = binary_adder_tail_aux2_v s;\<close>
  (adder_tail_prefix @ adder_tail_v_str) ::= (A (V binary_adder_tail_aux2_v_str));;
  \<comment> \<open>  adder_tail_ret' = 0;\<close>
  (adder_tail_prefix @ adder_tail_ret_str) ::= (A (N 0));;
  \<comment> \<open>  adder_tail_state = \<lparr>adder_tail_n = adder_tail_n',\<close>
  \<comment> \<open>                      adder_tail_v = adder_tail_v',\<close>
  \<comment> \<open>                      adder_tail_ret = adder_tail_ret'\<rparr>;\<close>
  \<comment> \<open>  adder_tail_ret_state = adder_tail_imp adder_tail_state;\<close>
  (invoke_subprogram adder_tail_prefix adder_tail_IMP_Minus);;
  \<comment> \<open>  cons_h' = adder_tail_ret adder_tail_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (adder_tail_prefix @ adder_tail_ret_str)));;
  \<comment> \<open>  cons_t' = cons_result;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V binary_adder_tail_aux2_cons_result));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_h' = 2;\<close>
  (cons_prefix @ cons_h_str) ::= (A (N 2));;
  \<comment> \<open>  cons_t' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_result = cons_ret cons_ret_state;\<close>
  (binary_adder_tail_aux2_cons_result) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_h' = cons_result;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V binary_adder_tail_aux2_cons_result));;
  \<comment> \<open>  cons_t' = 0;\<close>
  (cons_prefix @ cons_t_str) ::= (A (N 0));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_result = cons_ret cons_ret_state;\<close>
  (binary_adder_tail_aux2_cons_result) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  copy_atom_to_operand_tail_n' = binary_adder_tail_aux2_n s;\<close>
  (copy_atom_to_operand_tail_prefix @ copy_atom_to_operand_tail_n_str) ::= (A (V binary_adder_tail_aux2_n_str));;
  \<comment> \<open>  copy_atom_to_operand_tail_op' = b_encode_char_as_nat;\<close>
  (copy_atom_to_operand_tail_prefix @ copy_atom_to_operand_tail_op_str) ::= (A (N b_encode_char_as_nat));;
  \<comment> \<open>  copy_atom_to_operand_tail_a' = binary_adder_tail_aux2_b s;\<close>
  (copy_atom_to_operand_tail_prefix @ copy_atom_to_operand_tail_a_str) ::= (A (V binary_adder_tail_aux2_b_str));;
  \<comment> \<open>  copy_atom_to_operand_tail_ret' = 0;\<close>
  (copy_atom_to_operand_tail_prefix @ copy_atom_to_operand_tail_ret_str) ::= (A (N 0));;
  \<comment> \<open>  copy_atom_to_operand_tail_state = \<lparr>copy_atom_to_operand_tail_n = copy_atom_to_operand_tail_n',\<close>
  \<comment> \<open>                                     copy_atom_to_operand_tail_op = copy_atom_to_operand_tail_op',\<close>
  \<comment> \<open>                                     copy_atom_to_operand_tail_a = copy_atom_to_operand_tail_a',\<close>
  \<comment> \<open>                                     copy_atom_to_operand_tail_ret = copy_atom_to_operand_tail_ret'\<rparr>;\<close>
  \<comment> \<open>  copy_atom_to_operand_tail_ret_state = copy_atom_to_operand_tail_imp copy_atom_to_operand_tail_state;\<close>
  (invoke_subprogram copy_atom_to_operand_tail_prefix copy_atom_to_operand_tail_IMP_Minus);;
  \<comment> \<open>  cons_h' = copy_atom_to_operand_tail_ret copy_atom_to_operand_tail_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (copy_atom_to_operand_tail_prefix @ copy_atom_to_operand_tail_ret_str)));;
  \<comment> \<open>  cons_t' = cons_result;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V binary_adder_tail_aux2_cons_result));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  binary_adder_tail_aux2_ret' = cons_ret cons_ret_state;\<close>
  (binary_adder_tail_aux2_ret_str) ::= (A (V (cons_prefix @ cons_ret_str)))
  \<comment> \<open>  ret = \<lparr>binary_adder_tail_aux2_n = binary_adder_tail_aux2_n s,\<close>
  \<comment> \<open>         binary_adder_tail_aux2_v = binary_adder_tail_aux2_v s,\<close>
  \<comment> \<open>         binary_adder_tail_aux2_b = binary_adder_tail_aux2_b s,\<close>
  \<comment> \<open>         binary_adder_tail_aux2_ret = binary_adder_tail_aux2_ret'\<rparr>\<close>
"

abbreviation "binary_adder_tail_aux2_IMP_vars \<equiv>
  {binary_adder_tail_aux2_n_str, binary_adder_tail_aux2_v_str, binary_adder_tail_aux2_b_str,
  binary_adder_tail_aux2_ret_str, binary_adder_tail_aux2_cons_result}"

definition "binary_adder_tail_aux2_imp_to_HOL_state p s =
  \<lparr>binary_adder_tail_aux2_n = (s (add_prefix p binary_adder_tail_aux2_n_str)),
   binary_adder_tail_aux2_v = (s (add_prefix p binary_adder_tail_aux2_v_str)),
   binary_adder_tail_aux2_b = (s (add_prefix p binary_adder_tail_aux2_b_str)),
   binary_adder_tail_aux2_ret = (s (add_prefix p binary_adder_tail_aux2_ret_str))\<rparr>"

lemmas binary_adder_tail_aux2_state_translators =
  binary_adder_tail_aux2_imp_to_HOL_state_def
  binary_adder_tail_aux1_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  adder_tail_imp_to_HOL_state_def
  copy_atom_to_operand_tail_imp_to_HOL_state_def

lemma binary_adder_tail_aux2_IMP_Minus_correct_function:
  "(invoke_subprogram p binary_adder_tail_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p binary_adder_tail_aux2_ret_str)
      = binary_adder_tail_aux2_ret
          (binary_adder_tail_aux2_imp (binary_adder_tail_aux2_imp_to_HOL_state p s))"
  apply(subst binary_adder_tail_aux2_imp.simps)
  apply(simp only: binary_adder_tail_aux2_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule binary_adder_tail_aux1_IMP_Minus_correct[where vars = "binary_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(36) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(38) by fastforce
  apply(erule adder_tail_IMP_Minus_correct[where vars = "binary_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(40) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(42) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(44) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(46) by fastforce
  apply(erule copy_atom_to_operand_tail_IMP_Minus_correct[where vars = "binary_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(48) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(50) by fastforce
  by(force simp: binary_adder_tail_aux2_state_translators
    binary_adder_tail_aux2_state_upd_def)   

lemma binary_adder_tail_aux2_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ binary_adder_tail_aux2_pref) binary_adder_tail_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix binary_adder_tail_aux2_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast 

lemma binary_adder_tail_aux2_IMP_Minus_correct_time:
  "(invoke_subprogram p binary_adder_tail_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = binary_adder_tail_aux2_imp_time 0 (binary_adder_tail_aux2_imp_to_HOL_state p s)"
  apply(subst binary_adder_tail_aux2_imp_time.simps)
  apply(simp only: binary_adder_tail_aux2_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule binary_adder_tail_aux1_IMP_Minus_correct[where vars = "binary_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(71) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(73) by fastforce
  apply(erule adder_tail_IMP_Minus_correct[where vars = "binary_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(75) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(77) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(79) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(81) by fastforce
  apply(erule copy_atom_to_operand_tail_IMP_Minus_correct[where vars = "binary_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(83) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_aux2_IMP_vars"])
  subgoal premises p using p(85) by fastforce
  by(force simp add: Let_def binary_adder_tail_aux2_state_translators)   

lemma binary_adder_tail_aux2_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) binary_adder_tail_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (binary_adder_tail_aux2_imp_time 0 (binary_adder_tail_aux2_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) binary_adder_tail_aux2_ret_str) =
          binary_adder_tail_aux2_ret (binary_adder_tail_aux2_imp
                                        (binary_adder_tail_aux2_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using binary_adder_tail_aux2_IMP_Minus_correct_function
    binary_adder_tail_aux2_IMP_Minus_correct_time
    binary_adder_tail_aux2_IMP_Minus_correct_effects
  by (meson set_mono_prefix) 

subsubsection \<open>binary_adder_tail\<close>

fun binary_adder_tail' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "binary_adder_tail' n v a b = 
    2 ## (copy_atom_to_operand_tail n (encode_char(CHR ''a'')) a) ##
    (2 ## (binary_adder_tail_aux2 n v b)) ## 0"

lemma binary_adder_tail'_correct:
  "binary_adder_tail n v a b = binary_adder_tail' n v a b"
  unfolding binary_adder_tail_def
  by (simp only: binary_adder_tail'.simps binary_adder_tail_aux1.simps binary_adder_tail_aux2.simps Let_def)

record binary_adder_tail_state =
  binary_adder_tail_n::nat
  binary_adder_tail_v::nat
  binary_adder_tail_a::nat
  binary_adder_tail_b::nat
  binary_adder_tail_ret::nat

abbreviation "binary_adder_tail_prefix \<equiv> ''binary_adder_tail.''"
abbreviation "binary_adder_tail_n_str \<equiv> ''n''"
abbreviation "binary_adder_tail_v_str \<equiv> ''v''"
abbreviation "binary_adder_tail_a_str \<equiv> ''a''"
abbreviation "binary_adder_tail_b_str \<equiv> ''b''"
abbreviation "binary_adder_tail_ret_str \<equiv> ''ret''"

definition "binary_adder_tail_state_upd s =
  (let
      binary_adder_tail_aux2_n' = binary_adder_tail_n s;
      binary_adder_tail_aux2_v' = binary_adder_tail_v s;
      binary_adder_tail_aux2_b' = binary_adder_tail_b s;
      binary_adder_tail_aux2_ret' = 0;
      binary_adder_tail_aux2_state = \<lparr>binary_adder_tail_aux2_n = binary_adder_tail_aux2_n',
                                      binary_adder_tail_aux2_v = binary_adder_tail_aux2_v',
                                      binary_adder_tail_aux2_b = binary_adder_tail_aux2_b',
                                      binary_adder_tail_aux2_ret = binary_adder_tail_aux2_ret'\<rparr>;
      binary_adder_tail_aux2_ret_state = binary_adder_tail_aux2_imp binary_adder_tail_aux2_state;
      cons_h' = 2;
      cons_t' = binary_adder_tail_aux2_ret binary_adder_tail_aux2_ret_state;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_h' = cons_ret cons_ret_state;
      cons_t' = 0;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_result = cons_ret cons_ret_state;
      copy_atom_to_operand_tail_n' = binary_adder_tail_n s;
      copy_atom_to_operand_tail_op' = a_encode_char_as_nat;
      copy_atom_to_operand_tail_a' = binary_adder_tail_a s;
      copy_atom_to_operand_tail_ret' = 0;
      copy_atom_to_operand_tail_state = \<lparr>copy_atom_to_operand_tail_n = copy_atom_to_operand_tail_n',
                                         copy_atom_to_operand_tail_op = copy_atom_to_operand_tail_op',
                                         copy_atom_to_operand_tail_a = copy_atom_to_operand_tail_a',
                                         copy_atom_to_operand_tail_ret = copy_atom_to_operand_tail_ret'\<rparr>;
      copy_atom_to_operand_tail_ret_state = copy_atom_to_operand_tail_imp copy_atom_to_operand_tail_state;
      cons_h' = copy_atom_to_operand_tail_ret copy_atom_to_operand_tail_ret_state;
      cons_t' = cons_result;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      cons_h' = 2;
      cons_t' = cons_ret cons_ret_state;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      binary_adder_tail_ret' = cons_ret cons_ret_state;
      ret = \<lparr>binary_adder_tail_n = binary_adder_tail_n s,
             binary_adder_tail_v = binary_adder_tail_v s,
             binary_adder_tail_a = binary_adder_tail_a s,
             binary_adder_tail_b = binary_adder_tail_b s,
             binary_adder_tail_ret = binary_adder_tail_ret'\<rparr>
  in
      ret
)"

function binary_adder_tail_imp ::
  "binary_adder_tail_state \<Rightarrow> binary_adder_tail_state" where
  "binary_adder_tail_imp s =
  (let 
      ret = binary_adder_tail_state_upd s
    in 
      ret
  )"
  by simp+
termination
  by (relation "measure binary_adder_tail_n") simp

declare binary_adder_tail_imp.simps [simp del]

lemma binary_adder_tail_imp_correct[let_function_correctness]:
  "binary_adder_tail_ret (binary_adder_tail_imp s) =
    binary_adder_tail (binary_adder_tail_n s) (binary_adder_tail_v s) (binary_adder_tail_a s)
      (binary_adder_tail_b s)"
  apply (simp only: binary_adder_tail_imp.simps Let_def binary_adder_tail_state_upd_def
    binary_adder_tail_aux2_imp_correct cons_imp_correct copy_atom_to_operand_tail_imp_correct
    a_encode_char_val binary_adder_tail'_correct binary_adder_tail'.simps)
  by simp 

function binary_adder_tail_imp_time ::
  "nat \<Rightarrow> binary_adder_tail_state \<Rightarrow> nat" where
  "binary_adder_tail_imp_time t s =
  (let
      binary_adder_tail_aux2_n' = binary_adder_tail_n s;
      t = t + 2;
      binary_adder_tail_aux2_v' = binary_adder_tail_v s;
      t = t + 2;
      binary_adder_tail_aux2_b' = binary_adder_tail_b s;
      t = t + 2;
      binary_adder_tail_aux2_ret' = 0;
      t = t + 2;
      binary_adder_tail_aux2_state = \<lparr>binary_adder_tail_aux2_n = binary_adder_tail_aux2_n',
                                      binary_adder_tail_aux2_v = binary_adder_tail_aux2_v',
                                      binary_adder_tail_aux2_b = binary_adder_tail_aux2_b',
                                      binary_adder_tail_aux2_ret = binary_adder_tail_aux2_ret'\<rparr>;
      binary_adder_tail_aux2_ret_state = binary_adder_tail_aux2_imp binary_adder_tail_aux2_state;
      t = t + binary_adder_tail_aux2_imp_time 0 binary_adder_tail_aux2_state;
      cons_h' = 2;
      t = t + 2;
      cons_t' = binary_adder_tail_aux2_ret binary_adder_tail_aux2_ret_state;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_h' = cons_ret cons_ret_state;
      t = t + 2;
      cons_t' = 0;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_result = cons_ret cons_ret_state;
      t = t + 2;
      copy_atom_to_operand_tail_n' = binary_adder_tail_n s;
      t = t + 2;
      copy_atom_to_operand_tail_op' = a_encode_char_as_nat;
      t = t + 2;
      copy_atom_to_operand_tail_a' = binary_adder_tail_a s;
      t = t + 2;
      copy_atom_to_operand_tail_ret' = 0;
      t = t + 2;
      copy_atom_to_operand_tail_state = \<lparr>copy_atom_to_operand_tail_n = copy_atom_to_operand_tail_n',
                                         copy_atom_to_operand_tail_op = copy_atom_to_operand_tail_op',
                                         copy_atom_to_operand_tail_a = copy_atom_to_operand_tail_a',
                                         copy_atom_to_operand_tail_ret = copy_atom_to_operand_tail_ret'\<rparr>;
      copy_atom_to_operand_tail_ret_state = copy_atom_to_operand_tail_imp copy_atom_to_operand_tail_state;
      t = t + copy_atom_to_operand_tail_imp_time 0 copy_atom_to_operand_tail_state;
      cons_h' = copy_atom_to_operand_tail_ret copy_atom_to_operand_tail_ret_state;
      t = t + 2;
      cons_t' = cons_result;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      cons_h' = 2;
      t = t + 2;
      cons_t' = cons_ret cons_ret_state;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      binary_adder_tail_ret' = cons_ret cons_ret_state;
      t = t + 2;
      ret = \<lparr>binary_adder_tail_n = binary_adder_tail_n s,
             binary_adder_tail_v = binary_adder_tail_v s,
             binary_adder_tail_a = binary_adder_tail_a s,
             binary_adder_tail_b = binary_adder_tail_b s,
             binary_adder_tail_ret = binary_adder_tail_ret'\<rparr>
  in
      t
  )"
  by auto
termination
  by (relation "measure (binary_adder_tail_n \<circ> snd)") simp

declare binary_adder_tail_imp_time.simps [simp del]

lemma binary_adder_tail_imp_time_acc:
  "(binary_adder_tail_imp_time (Suc t) s) = Suc (binary_adder_tail_imp_time t s)"
  by (induction t s rule: binary_adder_tail_imp_time.induct)
    ((subst (1 2) binary_adder_tail_imp_time.simps);
      (simp add: binary_adder_tail_state_upd_def Let_def))            

lemma binary_adder_tail_imp_time_acc_2_aux:
  "(binary_adder_tail_imp_time t s) = t + (binary_adder_tail_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: binary_adder_tail_imp_time_acc)+            

lemma binary_adder_tail_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (binary_adder_tail_imp_time t s) = t + (binary_adder_tail_imp_time 0 s)"
  by (rule binary_adder_tail_imp_time_acc_2_aux)            

lemma binary_adder_tail_imp_time_acc_3:
  "(binary_adder_tail_imp_time (a + b) s) = a + (binary_adder_tail_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: binary_adder_tail_imp_time_acc)+   

abbreviation "binary_adder_tail_cons_result \<equiv> ''cons_result''"

definition binary_adder_tail_IMP_Minus where
  "binary_adder_tail_IMP_Minus \<equiv>
  \<comment> \<open>  binary_adder_tail_aux2_n' = binary_adder_tail_n s;\<close>
  (binary_adder_tail_aux2_prefix @ binary_adder_tail_aux2_n_str) ::= (A (V binary_adder_tail_n_str));;
  \<comment> \<open>  binary_adder_tail_aux2_v' = binary_adder_tail_v s;\<close>
  (binary_adder_tail_aux2_prefix @ binary_adder_tail_aux2_v_str) ::= (A (V binary_adder_tail_v_str));;
  \<comment> \<open>  binary_adder_tail_aux2_b' = binary_adder_tail_b s;\<close>
  (binary_adder_tail_aux2_prefix @ binary_adder_tail_aux2_b_str) ::= (A (V binary_adder_tail_b_str));;
  \<comment> \<open>  binary_adder_tail_aux2_ret' = 0;\<close>
  (binary_adder_tail_aux2_prefix @ binary_adder_tail_aux2_ret_str) ::= (A (N 0));;
  \<comment> \<open>  binary_adder_tail_aux2_state = \<lparr>binary_adder_tail_aux2_n = binary_adder_tail_aux2_n',\<close>
  \<comment> \<open>                                  binary_adder_tail_aux2_v = binary_adder_tail_aux2_v',\<close>
  \<comment> \<open>                                  binary_adder_tail_aux2_b = binary_adder_tail_aux2_b',\<close>
  \<comment> \<open>                                  binary_adder_tail_aux2_ret = binary_adder_tail_aux2_ret'\<rparr>;\<close>
  \<comment> \<open>  binary_adder_tail_aux2_ret_state = binary_adder_tail_aux2_imp binary_adder_tail_aux2_state;\<close>
  (invoke_subprogram binary_adder_tail_aux2_prefix binary_adder_tail_aux2_IMP_Minus);;
  \<comment> \<open>  cons_h' = 2;\<close>
  (cons_prefix @ cons_h_str) ::= (A (N 2));;
  \<comment> \<open>  cons_t' = binary_adder_tail_aux2_ret binary_adder_tail_aux2_ret_state;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V (binary_adder_tail_aux2_prefix @ binary_adder_tail_aux2_ret_str)));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_h' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_t' = 0;\<close>
  (cons_prefix @ cons_t_str) ::= (A (N 0));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_result = cons_ret cons_ret_state;\<close>
  (binary_adder_tail_cons_result) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  copy_atom_to_operand_tail_n' = binary_adder_tail_n s;\<close>
  (copy_atom_to_operand_tail_prefix @ copy_atom_to_operand_tail_n_str) ::= (A (V binary_adder_tail_n_str));;
  \<comment> \<open>  copy_atom_to_operand_tail_op' = a_encode_char_as_nat;\<close>
  (copy_atom_to_operand_tail_prefix @ copy_atom_to_operand_tail_op_str) ::= (A (N a_encode_char_as_nat));;
  \<comment> \<open>  copy_atom_to_operand_tail_a' = binary_adder_tail_a s;\<close>
  (copy_atom_to_operand_tail_prefix @ copy_atom_to_operand_tail_a_str) ::= (A (V binary_adder_tail_a_str));;
  \<comment> \<open>  copy_atom_to_operand_tail_ret' = 0;\<close>
  (copy_atom_to_operand_tail_prefix @ copy_atom_to_operand_tail_ret_str) ::= (A (N 0));;
  \<comment> \<open>  copy_atom_to_operand_tail_state = \<lparr>copy_atom_to_operand_tail_n = copy_atom_to_operand_tail_n',\<close>
  \<comment> \<open>                                     copy_atom_to_operand_tail_op = copy_atom_to_operand_tail_op',\<close>
  \<comment> \<open>                                     copy_atom_to_operand_tail_a = copy_atom_to_operand_tail_a',\<close>
  \<comment> \<open>                                     copy_atom_to_operand_tail_ret = copy_atom_to_operand_tail_ret'\<rparr>;\<close>
  \<comment> \<open>  copy_atom_to_operand_tail_ret_state = copy_atom_to_operand_tail_imp copy_atom_to_operand_tail_state;\<close>
  (invoke_subprogram copy_atom_to_operand_tail_prefix copy_atom_to_operand_tail_IMP_Minus);;
  \<comment> \<open>  cons_h' = copy_atom_to_operand_tail_ret copy_atom_to_operand_tail_ret_state;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (copy_atom_to_operand_tail_prefix @ copy_atom_to_operand_tail_ret_str)));;
  \<comment> \<open>  cons_t' = cons_result;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V binary_adder_tail_cons_result));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  cons_h' = 2;\<close>
  (cons_prefix @ cons_h_str) ::= (A (N 2));;
  \<comment> \<open>  cons_t' = cons_ret cons_ret_state;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  binary_adder_tail_ret' = cons_ret cons_ret_state;\<close>
  (binary_adder_tail_ret_str) ::= (A (V (cons_prefix @ cons_ret_str)))
  \<comment> \<open>  ret = \<lparr>binary_adder_tail_n = binary_adder_tail_n s,\<close>
  \<comment> \<open>         binary_adder_tail_v = binary_adder_tail_v s,\<close>
  \<comment> \<open>         binary_adder_tail_a = binary_adder_tail_a s,\<close>
  \<comment> \<open>         binary_adder_tail_b = binary_adder_tail_b s,\<close>
  \<comment> \<open>         binary_adder_tail_ret = binary_adder_tail_ret'\<rparr>\<close>
"

abbreviation "binary_adder_tail_IMP_vars \<equiv>
  {binary_adder_tail_n_str, binary_adder_tail_v_str, binary_adder_tail_a_str, binary_adder_tail_b_str,
  binary_adder_tail_ret_str, binary_adder_tail_cons_result}"

definition "binary_adder_tail_imp_to_HOL_state p s =
  \<lparr>binary_adder_tail_n = (s (add_prefix p binary_adder_tail_n_str)),
   binary_adder_tail_v = (s (add_prefix p binary_adder_tail_v_str)),
   binary_adder_tail_a = (s (add_prefix p binary_adder_tail_a_str)),
   binary_adder_tail_b = (s (add_prefix p binary_adder_tail_b_str)),
   binary_adder_tail_ret = (s (add_prefix p binary_adder_tail_ret_str))\<rparr>"

lemmas binary_adder_tail_state_translators =
  binary_adder_tail_imp_to_HOL_state_def
  binary_adder_tail_aux2_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  copy_atom_to_operand_tail_imp_to_HOL_state_def

lemma binary_adder_tail_IMP_Minus_correct_function:
  "(invoke_subprogram p binary_adder_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p binary_adder_tail_ret_str)
      = binary_adder_tail_ret
          (binary_adder_tail_imp (binary_adder_tail_imp_to_HOL_state p s))"
  apply(subst binary_adder_tail_imp.simps)
  apply(simp only: binary_adder_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule binary_adder_tail_aux2_IMP_Minus_correct[where vars = "binary_adder_tail_IMP_vars"])
  subgoal premises p using p(28) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_IMP_vars"])
  subgoal premises p using p(30) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_IMP_vars"])
  subgoal premises p using p(32) by fastforce
  apply(erule copy_atom_to_operand_tail_IMP_Minus_correct[where vars = "binary_adder_tail_IMP_vars"])
  subgoal premises p using p(34) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_IMP_vars"])
  subgoal premises p using p(36) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_IMP_vars"])
  subgoal premises p using p(38) by fastforce
  by(force simp: binary_adder_tail_state_translators
    binary_adder_tail_state_upd_def)   

lemma binary_adder_tail_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ binary_adder_tail_pref) binary_adder_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix binary_adder_tail_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemma binary_adder_tail_IMP_Minus_correct_time:
  "(invoke_subprogram p binary_adder_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = binary_adder_tail_imp_time 0 (binary_adder_tail_imp_to_HOL_state p s)"
  apply(subst binary_adder_tail_imp_time.simps)
  apply(simp only: binary_adder_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule binary_adder_tail_aux2_IMP_Minus_correct[where vars = "binary_adder_tail_IMP_vars"])
  subgoal premises p using p(55) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_IMP_vars"])
  subgoal premises p using p(57) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_IMP_vars"])
  subgoal premises p using p(59) by fastforce
  apply(erule copy_atom_to_operand_tail_IMP_Minus_correct[where vars = "binary_adder_tail_IMP_vars"])
  subgoal premises p using p(61) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_IMP_vars"])
  subgoal premises p using p(63) by fastforce
  apply(erule cons_IMP_Minus_correct[where vars = "binary_adder_tail_IMP_vars"])
  subgoal premises p using p(65) by fastforce
  by(force simp add: Let_def binary_adder_tail_state_translators) 

lemma binary_adder_tail_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) binary_adder_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (binary_adder_tail_imp_time 0 (binary_adder_tail_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) binary_adder_tail_ret_str) =
          binary_adder_tail_ret (binary_adder_tail_imp
                                        (binary_adder_tail_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using binary_adder_tail_IMP_Minus_correct_function
    binary_adder_tail_IMP_Minus_correct_time
    binary_adder_tail_IMP_Minus_correct_effects
  by (meson set_mono_prefix) 

end 