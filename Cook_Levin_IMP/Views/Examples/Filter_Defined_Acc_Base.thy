\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Filter_Defined_Acc_Base
  imports
    Cook_Levin_IMP.SAS_Plus_Strips_Nat
    Cook_Levin_IMP.Primitives_IMP_Minus
begin

unbundle IMP_Minus_Minus_Com.no_com_syntax

subsubsection \<open>filter_defined_acc\<close>

record filter_defined_acc_state =
  filter_defined_acc_s :: nat
  filter_defined_acc_acc :: nat
  filter_defined_acc_n :: nat
  filter_defined_acc_ret :: nat

abbreviation "filter_defined_acc_prefix \<equiv> ''filter_defined_acc.''"
abbreviation "filter_defined_acc_s_str \<equiv> ''s''"
abbreviation "filter_defined_acc_acc_str \<equiv> ''acc''"
abbreviation "filter_defined_acc_n_str \<equiv> ''n''"
abbreviation "filter_defined_acc_ret_str \<equiv> ''ret''"

definition "filter_defined_acc_imp_compute_loop_condition s \<equiv>
  (let
    condition = filter_defined_acc_n s
  in condition)"

definition "filter_defined_acc_imp_after_loop s \<equiv>
  (let
    filter_defined_acc_ret' = filter_defined_acc_acc s;
    ret = \<lparr>
      filter_defined_acc_s = filter_defined_acc_s s,
      filter_defined_acc_acc = filter_defined_acc_acc s,
      filter_defined_acc_n = filter_defined_acc_n s,
      filter_defined_acc_ret = filter_defined_acc_ret'
    \<rparr>
  in ret)"

definition "filter_defined_acc_state_upd s \<equiv>
  (let
    hd_xs' = filter_defined_acc_n s;
    hd_ret' = 0;
    hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
    hd_ret_state = hd_imp hd_state;
    map_list_find_aux_xs' = filter_defined_acc_s s;
    map_list_find_aux_a' = hd_ret hd_ret_state;
    map_list_find_aux_ret' = 0;
    map_list_find_aux_state = \<lparr>
      map_list_find_aux_xs = map_list_find_aux_xs',
      map_list_find_aux_a = map_list_find_aux_a',
      map_list_find_aux_ret = map_list_find_aux_ret'
    \<rparr>;
    map_list_find_aux_ret_state = map_list_find_aux_imp map_list_find_aux_state;
    cond = map_list_find_aux_ret map_list_find_aux_ret_state
  in
    (if cond \<noteq> 0
    then
      (let
        filter_defined_acc_s' = filter_defined_acc_s s;
        hd_xs' = filter_defined_acc_n s;
        hd_ret' = 0;
        hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
        hd_ret_state = hd_imp hd_state;
        cons_h' = hd_ret hd_ret_state;
        cons_t' = filter_defined_acc_acc s;
        cons_ret' = 0;
        cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
        cons_ret_state = cons_imp cons_state;
        filter_defined_acc_acc' = cons_ret cons_ret_state;
        tl_xs' = filter_defined_acc_n s;
        tl_ret' = 0;
        tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
        tl_ret_state = tl_imp tl_state;
        filter_defined_acc_n' = tl_ret tl_ret_state;
        filter_defined_acc_ret' = 0;
        ret = \<lparr>
          filter_defined_acc_s = filter_defined_acc_s',
          filter_defined_acc_acc = filter_defined_acc_acc',
          filter_defined_acc_n = filter_defined_acc_n',
          filter_defined_acc_ret = filter_defined_acc_ret'
        \<rparr>
      in ret)
    else
      (let
        filter_defined_acc_s' = filter_defined_acc_s s;
        filter_defined_acc_acc' = filter_defined_acc_acc s;
        tl_xs' = filter_defined_acc_n s;
        tl_ret' = 0;
        tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
        tl_ret_state = tl_imp tl_state;
        filter_defined_acc_n' = tl_ret tl_ret_state;
        filter_defined_acc_ret' = 0;
        ret = \<lparr>
          filter_defined_acc_s = filter_defined_acc_s',
          filter_defined_acc_acc = filter_defined_acc_acc',
          filter_defined_acc_n = filter_defined_acc_n',
          filter_defined_acc_ret = filter_defined_acc_ret'
        \<rparr>
      in ret)))"

lemmas filter_defined_acc_imp_subprogram_simps =
  filter_defined_acc_state_upd_def
  filter_defined_acc_imp_compute_loop_condition_def
  filter_defined_acc_imp_after_loop_def

function filter_defined_acc_imp ::
  "filter_defined_acc_state \<Rightarrow> filter_defined_acc_state" where
  "filter_defined_acc_imp s =
  (if filter_defined_acc_imp_compute_loop_condition s \<noteq> 0
  then
    let next_iteration = filter_defined_acc_imp (filter_defined_acc_state_upd s)
    in next_iteration
  else
    let ret = filter_defined_acc_imp_after_loop s
    in ret
  )"
  by simp+
termination
  apply (relation "measure filter_defined_acc_n")
  apply (simp add: filter_defined_acc_imp_subprogram_simps tl_imp_correct)+
  done

declare filter_defined_acc_imp.simps [simp del]

lemma filter_defined_acc_imp_correct[let_function_correctness]:
  "filter_defined_acc_ret (filter_defined_acc_imp s) =
    filter_defined_acc (filter_defined_acc_s s) (filter_defined_acc_acc s) (filter_defined_acc_n s)"
  apply (induction s rule: filter_defined_acc_imp.induct)
  apply (subst filter_defined_acc_imp.simps)
  apply (subst filter_defined_acc.simps)
  apply (simp del: filter_defined_acc.simps map_list_find_nat.simps
    add: filter_defined_acc_imp_subprogram_simps
    map_list_find_aux_imp_correct cons_imp_correct hd_imp_correct tl_imp_correct)
  done

definition "filter_defined_acc_imp_compute_loop_condition_time t s \<equiv>
  (let
    condition = filter_defined_acc_n s;
    t = t + 2
  in t)"

definition "filter_defined_acc_imp_after_loop_time t s \<equiv>
  (let
    filter_defined_acc_ret' = filter_defined_acc_acc s;
    t = t + 2;
    ret = \<lparr>
      filter_defined_acc_s = filter_defined_acc_s s,
      filter_defined_acc_acc = filter_defined_acc_acc s,
      filter_defined_acc_n = filter_defined_acc_n s,
      filter_defined_acc_ret = filter_defined_acc_ret'
    \<rparr>
  in t)"

definition "filter_defined_acc_state_upd_time t s \<equiv>
  (let
    hd_xs' = filter_defined_acc_n s;
    t = t + 2;
    hd_ret' = 0;
    t = t + 2;
    hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
    hd_ret_state = hd_imp hd_state;
    t = t + hd_imp_time 0 hd_state;
    map_list_find_aux_xs' = filter_defined_acc_s s;
    t = t + 2;
    map_list_find_aux_a' = hd_ret hd_ret_state;
    t = t + 2;
    map_list_find_aux_ret' = 0;
    t = t + 2;
    map_list_find_aux_state = \<lparr>
      map_list_find_aux_xs = map_list_find_aux_xs',
      map_list_find_aux_a = map_list_find_aux_a',
      map_list_find_aux_ret = map_list_find_aux_ret'
    \<rparr>;
    map_list_find_aux_ret_state = map_list_find_aux_imp map_list_find_aux_state;
    t = t + map_list_find_aux_imp_time 0 map_list_find_aux_state;
    map_list_find_aux_xs' = filter_defined_acc_s s;
    t = t + 2;
    cond = map_list_find_aux_ret map_list_find_aux_ret_state;
    t = t + 2
  in
    (if cond \<noteq> 0
    then
      (let
        t = t + 1;
        filter_defined_acc_s' = filter_defined_acc_s s;
        t = t + 2;
        hd_xs' = filter_defined_acc_n s;
        t = t + 2;
        hd_ret' = 0;
        t = t + 2;
        hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
        hd_ret_state = hd_imp hd_state;
        t = t + hd_imp_time 0 hd_state;
        cons_h' = hd_ret hd_ret_state;
        t = t + 2;
        cons_t' = filter_defined_acc_acc s;
        t = t + 2;
        cons_ret' = 0;
        t = t + 2;
        cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
        cons_ret_state = cons_imp cons_state;
        t = t + cons_imp_time 0 cons_state;
        filter_defined_acc_acc' = cons_ret cons_ret_state;
        t = t + 2;
        tl_xs' = filter_defined_acc_n s;
        t = t + 2;
        tl_ret' = 0;
        t = t + 2;
        tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
        tl_ret_state = tl_imp tl_state;
        t = t + tl_imp_time 0 tl_state;
        filter_defined_acc_n' = tl_ret tl_ret_state;
        t = t + 2;
        filter_defined_acc_ret' = 0;
        t = t + 2;
        ret = \<lparr>
          filter_defined_acc_s = filter_defined_acc_s',
          filter_defined_acc_acc = filter_defined_acc_acc',
          filter_defined_acc_n = filter_defined_acc_n',
          filter_defined_acc_ret = filter_defined_acc_ret'
        \<rparr>
      in t)
    else
      (let
        filter_defined_acc_s' = filter_defined_acc_s s;
        t = t + 2;
        filter_defined_acc_acc' = filter_defined_acc_acc s;
        t = t + 2;
        tl_xs' = filter_defined_acc_n s;
        t = t + 2;
        tl_ret' = 0;
        t = t + 2;
        tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
        tl_ret_state = tl_imp tl_state;
        t = t + tl_imp_time 0 tl_state;
        filter_defined_acc_n' = tl_ret tl_ret_state;
        t = t + 2;
        filter_defined_acc_ret' = 0;
        t = t + 2;
        ret = \<lparr>
          filter_defined_acc_s = filter_defined_acc_s',
          filter_defined_acc_acc = filter_defined_acc_acc',
          filter_defined_acc_n = filter_defined_acc_n',
          filter_defined_acc_ret = filter_defined_acc_ret'
        \<rparr>
      in t)))"

lemmas filter_defined_acc_imp_subprogram_time_simps =
  filter_defined_acc_state_upd_time_def
  filter_defined_acc_imp_compute_loop_condition_time_def
  filter_defined_acc_imp_after_loop_time_def
  filter_defined_acc_imp_subprogram_simps

function filter_defined_acc_imp_time ::
  "nat \<Rightarrow> filter_defined_acc_state \<Rightarrow> nat" where
  "filter_defined_acc_imp_time t s =
  filter_defined_acc_imp_compute_loop_condition_time 0 s +
  (if filter_defined_acc_imp_compute_loop_condition s \<noteq> 0
  then
    (let
      t = t + 1;
      next_iteration = filter_defined_acc_imp_time
        (t + filter_defined_acc_state_upd_time 0 s)
        (filter_defined_acc_state_upd s)
    in next_iteration)
  else
    (let
      t = t + 2;
      ret = t + filter_defined_acc_imp_after_loop_time 0 s
    in ret)
  )"
  by auto
termination
  apply (relation "measure (filter_defined_acc_n \<circ> snd)")
  apply (simp add: filter_defined_acc_imp_subprogram_time_simps tl_imp_correct)+
  done

declare filter_defined_acc_imp_time.simps [simp del]

lemma filter_defined_acc_imp_time_acc:
  "(filter_defined_acc_imp_time (Suc t) s) =
    Suc (filter_defined_acc_imp_time t s)"
  by (induction t s rule: filter_defined_acc_imp_time.induct)
    ((subst (1 2) filter_defined_acc_imp_time.simps);
    (simp add: filter_defined_acc_state_upd_def))

abbreviation "filter_defined_acc_while_cond \<equiv> ''condition''"

definition "filter_defined_acc_IMP_init_while_cond \<equiv>
  \<comment> \<open>condition = filter_defined_acc_n s\<close>
  (filter_defined_acc_while_cond) ::= (A (V filter_defined_acc_n_str))
"

definition "filter_defined_acc_IMP_after_loop \<equiv>
  \<comment> \<open>filter_defined_acc_ret' = filter_defined_acc_acc s;\<close>
  (filter_defined_acc_ret_str) ::= (A (V filter_defined_acc_acc_str))
  \<comment> \<open>ret = \<lparr>
      filter_defined_acc_s = filter_defined_acc_s s,
      filter_defined_acc_acc = filter_defined_acc_acc s,
      filter_defined_acc_n = filter_defined_acc_n s,
      filter_defined_acc_ret = filter_defined_acc_ret'
    \<rparr>\<close>"

abbreviation "filter_defined_acc_loop_body_if_cond \<equiv> ''cond''"

definition "filter_defined_acc_IMP_loop_body \<equiv>
  \<comment> \<open>hd_xs' = filter_defined_acc_n s;\<close>
  (hd_prefix @ hd_xs_str) ::= (A (V filter_defined_acc_n_str));;
  \<comment> \<open>hd_ret' = 0;\<close>
  (hd_prefix @ hd_ret_str) ::= (A (N 0));;
  \<comment> \<open>hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
     hd_ret_state = hd_imp hd_state;\<close>
  (invoke_subprogram hd_prefix hd_IMP_Minus);;
  \<comment> \<open>map_list_find_aux_xs' = filter_defined_acc_s s;
     map_list_find_aux_a' = hd_ret hd_ret_state;
     map_list_find_aux_ret' = 0;\<close>
  (map_list_find_aux_prefix @ map_list_find_aux_xs_str) ::= (A (V filter_defined_acc_s_str));;
  (map_list_find_aux_prefix @ map_list_find_aux_a_str) ::= (A (V (hd_prefix @ hd_ret_str)));;
  (map_list_find_aux_prefix @ map_list_find_aux_ret_str) ::= (A (N 0));;
  \<comment> \<open>map_list_find_aux_state = \<lparr>
      map_list_find_aux_xs = map_list_find_aux_xs',
      map_list_find_aux_a = map_list_find_aux_a',
      map_list_find_aux_ret = map_list_find_aux_ret'
    \<rparr>;
    map_list_find_aux_ret_state = map_list_find_aux_imp map_list_find_aux_state;\<close>
  (invoke_subprogram map_list_find_aux_prefix map_list_find_aux_IMP_Minus);;
  filter_defined_acc_loop_body_if_cond ::= (A (V (map_list_find_aux_prefix @ map_list_find_aux_ret_str)));;
  IF filter_defined_acc_loop_body_if_cond\<noteq>0
  THEN ( \<comment> \<open>filter_defined_acc_s' = filter_defined_acc_s s;\<close>
      (filter_defined_acc_s_str) ::= (A (V filter_defined_acc_s_str));;
      \<comment> \<open>hd_xs' = filter_defined_acc_n s;\<close>
      (hd_prefix @ hd_xs_str) ::= (A (V filter_defined_acc_n_str));;
      \<comment> \<open>hd_ret' = 0;\<close>
      (hd_prefix @ hd_ret_str) ::= (A (N 0));;
      \<comment> \<open>hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
         hd_ret_state = hd_imp hd_state;\<close>
      (invoke_subprogram hd_prefix hd_IMP_Minus);;
      \<comment> \<open>cons_h' = hd_ret hd_ret_state;\<close>
      (cons_prefix @ cons_h_str) ::= (A (V (hd_prefix @ hd_ret_str)));;
      \<comment> \<open>cons_t' = filter_defined_acc_acc s;\<close>
      (cons_prefix @ cons_t_str) ::= (A (V filter_defined_acc_acc_str));;
      \<comment>\<open>cons_ret' = 0;\<close>
      (cons_prefix @ cons_ret_str) ::= (A (N 0));;
      \<comment>\<open>cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
      \<comment>\<open>cons_ret_state = cons_imp cons_state;\<close>
      (invoke_subprogram cons_prefix cons_IMP_Minus);;
      \<comment>\<open>filter_defined_acc_acc' = cons_ret cons_ret_state;\<close>
      (filter_defined_acc_acc_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
      \<comment>\<open>tl_xs' = filter_defined_acc_n s;\<close>
      (tl_prefix @ tl_xs_str) ::= (A (V filter_defined_acc_n_str));;
      \<comment>\<open>tl_ret' = 0;\<close>
      (tl_prefix @ tl_ret_str) ::= (A (N 0));;
      \<comment>\<open>tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;\<close>
      \<comment>\<open>tl_ret_state = tl_imp tl_state;\<close>
      (invoke_subprogram tl_prefix tl_IMP_Minus);;
      \<comment>\<open>filter_defined_acc_n' = tl_ret tl_ret_state;\<close>
      (filter_defined_acc_n_str) ::= (A (V (tl_prefix @ tl_ret_str)));;
      \<comment>\<open>filter_defined_acc_ret' = 0;\<close>
      (filter_defined_acc_ret_str) ::= (A (N 0))
    )
  ELSE (
      \<comment> \<open>filter_defined_acc_s' = filter_defined_acc_s s;\<close>
      (filter_defined_acc_s_str) ::= (A (V filter_defined_acc_s_str));;
      \<comment> \<open>filter_defined_acc_acc' = filter_defined_acc_acc s;\<close>
      (filter_defined_acc_acc_str) ::= (A (V filter_defined_acc_acc_str));;
      \<comment> \<open>tl_xs' = filter_defined_acc_n s;\<close>
      (tl_prefix @ tl_xs_str) ::= (A (V filter_defined_acc_n_str));;
      \<comment> \<open>tl_ret' = 0;\<close>
      (tl_prefix @ tl_ret_str) ::= (A (N 0));;
      \<comment> \<open>tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;\<close>
      \<comment> \<open>tl_ret_state = tl_imp tl_state;\<close>
      (invoke_subprogram tl_prefix tl_IMP_Minus);;
      \<comment> \<open>filter_defined_acc_n' = tl_ret tl_ret_state;\<close>
      (filter_defined_acc_n_str) ::= (A (V (tl_prefix @ tl_ret_str)));;
      \<comment> \<open>filter_defined_acc_ret' = 0;\<close>
      (filter_defined_acc_ret_str) ::= (A (N 0))
    )"

definition filter_defined_acc_IMP_Minus where
  "filter_defined_acc_IMP_Minus \<equiv>
  filter_defined_acc_IMP_init_while_cond;;
  WHILE filter_defined_acc_while_cond \<noteq>0 DO (
    filter_defined_acc_IMP_loop_body;;
    filter_defined_acc_IMP_init_while_cond
  );;
  filter_defined_acc_IMP_after_loop"

abbreviation "filter_defined_acc_IMP_vars \<equiv> {
    filter_defined_acc_loop_body_if_cond,
    filter_defined_acc_acc_str, filter_defined_acc_s_str,
    filter_defined_acc_n_str, filter_defined_acc_ret_str
  }"

lemmas filter_defined_acc_IMP_subprogram_simps =
  filter_defined_acc_IMP_init_while_cond_def
  filter_defined_acc_IMP_loop_body_def
  filter_defined_acc_IMP_after_loop_def

definition "filter_defined_acc_imp_to_HOL_state p s = \<lparr>
    filter_defined_acc_s = (s (add_prefix p filter_defined_acc_s_str)),
    filter_defined_acc_acc = (s (add_prefix p filter_defined_acc_acc_str)),
    filter_defined_acc_n = (s (add_prefix p filter_defined_acc_n_str)),
    filter_defined_acc_ret = (s (add_prefix p filter_defined_acc_ret_str))
  \<rparr>"

lemmas filter_defined_acc_state_translators =
  filter_defined_acc_imp_to_HOL_state_def
  hd_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  tl_imp_to_HOL_state_def
  map_list_find_aux_imp_to_HOL_state_def

lemmas filter_defined_acc_complete_simps =
  filter_defined_acc_imp_subprogram_simps
  filter_defined_acc_state_translators


end