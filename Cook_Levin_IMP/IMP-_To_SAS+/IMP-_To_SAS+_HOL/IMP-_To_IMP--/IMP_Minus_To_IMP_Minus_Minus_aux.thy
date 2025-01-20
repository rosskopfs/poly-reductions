theory IMP_Minus_To_IMP_Minus_Minus_aux
  imports
  Primitives_IMP_Minus
    Binary_Arithmetic_IMP
    IMP_Minus_To_IMP_Minus_Minus_State_Translations_IMP
    IMP_Minus_To_IMP_Minus_Minus_nat
    IMP_Minus.Com
  IMP_Minus_To_IMP_Minus_Minus_IMP
  Binary_Operations_IMP

begin

unbundle no IMP_Minus_Minus_Com.com_syntax

subsection IMP_Minus_to_IMP_Minus_Minus_stack

subsubsection IMP_Minus_to_IMP_Minus_Minus_stack_end_recur

record IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_state=
IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s::nat
IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret::nat

abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_prefix \<equiv>
''IMP_Minus_to_IMP_Minus_Minus_stack_end_recur.''"
abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s_str \<equiv> ''s''"
abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret_str \<equiv> ''ret''"
abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_cond \<equiv> ''cond''"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_state_upd s \<equiv>
(let
  cond = IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s s
in
  (if cond = 0 then
  (let
    cons_h' = 0;
    cons_t' = 0;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h',
                  cons_t = cons_t',
                  cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret' = cons_ret cons_ret_state;
    ret =
    \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s = IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s s,
    IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret = IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret'\<rparr>
  in
  ret)
  else
  (let
    hd_xs' = IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s s;
    hd_ret' = 0;
    hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
    hd_ret_state = hd_imp hd_state;
    nth_nat_n' = 1;
    nth_nat_x' = hd_ret hd_ret_state;
    nth_nat_ret' = 0;
    nth_nat_state =
    \<lparr>nth_nat_n = nth_nat_n',
    nth_nat_x = nth_nat_x',
    nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;
    IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret' = nth_nat_ret nth_nat_ret_state;
    ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s = IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s s,
    IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret = IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret'\<rparr>
  in
   ret)
  )
)"

function IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp ::
  "IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_state \<Rightarrow> IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_state" where
  "IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp s =
  (let
      ret = IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_state_upd s
    in
      ret
  )"
  by simp+
termination
  by (relation "measure IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s") simp

declare IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp.simps [simp del]

lemma IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_correct[let_function_correctness]:
  "IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret (IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp s) =
    IMP_Minus_to_IMP_Minus_Minus_stack_end_recur (IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s s)"
  apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp.simps Let_def IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_state_upd_def)
  apply (simp add: nth_nat_imp_correct cons_imp_correct hd_imp_correct IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_def)
  done

function IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time ::
  "nat \<Rightarrow> IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_state \<Rightarrow> nat" where
  "IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time t s =
  (let
  cond = IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s s;
  t = t + 2
  in
  (if cond = 0 then
  (let
    t = t + 1;
    cons_h' = 0;
    t = t + 2;
    cons_t' = 0;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h',
                  cons_t = cons_t',
                  cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;
    IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret' = cons_ret cons_ret_state;
    t = t + 2;
    ret =
    \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s = IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s s,
    IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret = IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret'\<rparr>
  in
  t)
  else
  (let
    t = t + 1;
    hd_xs' = IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s s;
    t = t + 2;
    hd_ret' = 0;
    t = t + 2;
    hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
    hd_ret_state = hd_imp hd_state;
    t = t + hd_imp_time 0 hd_state;

    nth_nat_n' = 1;
    t = t + 2;
    nth_nat_x' = hd_ret hd_ret_state;
    t = t + 2;
    nth_nat_ret' = 0;
    t = t + 2;
    nth_nat_state =
    \<lparr>nth_nat_n = nth_nat_n',
    nth_nat_x = nth_nat_x',
    nth_nat_ret = nth_nat_ret'\<rparr>;
    nth_nat_ret_state = nth_nat_imp nth_nat_state;
    t = t + nth_nat_imp_time 0 nth_nat_state;
    IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret' = nth_nat_ret nth_nat_ret_state;
    t = t + 2;
    ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s = IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s s,
    IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret = IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret'\<rparr>
  in
   t)
  )
  )"
  by auto
termination
  by (relation "measure (IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s \<circ> snd)") simp

declare IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time.simps [simp del]

lemma IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time_acc:
  "(IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time (Suc t) s) = Suc (IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time t s)"
  by (induction t s rule: IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time.induct)
    ((subst (1 2) IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time.simps);
      (simp add: IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_state_upd_def Let_def))

lemma IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time_acc_2_aux:
  "(IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time t s) = t + (IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time_acc)+

lemma IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time t s) = t + (IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time 0 s)"
  by (rule IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time_acc_2_aux)

lemma IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time_acc_3:
  "(IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time (a + b) s) = a + (IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time_acc)+

abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_vars \<equiv>
  {IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s_str}"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_to_HOL_state p s =
  \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s = (s (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s_str)),
   IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret = (s (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret_str))\<rparr>"

lemmas IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_state_translators =
  IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  hd_imp_to_HOL_state_def
  nth_nat_imp_to_HOL_state_def

definition IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_Minus where
  "IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_Minus \<equiv>
  IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_cond
    ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s_str);;
  IF IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_cond \<noteq>0
  THEN
    (
      (hd_prefix @ hd_xs_str)
        ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s_str);;
      (hd_prefix @ hd_ret_str) ::= A (N 0);;
      invoke_subprogram hd_prefix hd_IMP_Minus;;

      (nth_nat_prefix @ nth_nat_n_str) ::= A (N 1);;
      (nth_nat_prefix @ nth_nat_x_str) ::= A (V (hd_prefix @ hd_ret_str));;
      (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
      invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
      IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret_str
        ::= A (V (nth_nat_prefix @ nth_nat_ret_str))
    )
  ELSE
    (
      (cons_prefix @ cons_h_str) ::= A (N 0);;
      (cons_prefix @ cons_t_str) ::= A (N 0);;
      (cons_prefix @ cons_ret_str) ::= A (N 0);;
      invoke_subprogram cons_prefix cons_IMP_Minus;;
      IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret_str
        ::= A (V (cons_prefix @ cons_ret_str))
  )
"

lemma IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp (IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_to_HOL_state p s))"
  apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp.simps)
  apply(simp only: IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply (erule If_E)
    subgoal
    apply (erule Seq_E)+
    apply(erule hd_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_vars"])
    subgoal premises p using p(10) by fastforce
    apply(erule nth_nat_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_vars"])
    subgoal premises p using p(12) by fastforce
    by(fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_state_translators
    IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_state_upd_def)

    subgoal
    apply (erule Seq_E)+
    apply(erule cons_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_vars"])
    subgoal premises p using p(7) by fastforce
    by(fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_state_translators
    IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_state_upd_def)
  done

lemma IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_pref) IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_to_HOL_state p s)"
  apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time.simps)
  apply(simp only: IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_Minus_def prefix_simps)
   apply(erule Seq_tE)+
  apply (erule If_tE)
    subgoal
    apply (erule Seq_tE)+
    apply(erule hd_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_vars"])
    subgoal premises p using p(19) by fastforce
    apply(erule nth_nat_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_vars"])
    subgoal premises p using p(21) by fastforce
    by(fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_state_translators
    Let_def)

    subgoal
    apply (erule Seq_tE)+
    apply(erule cons_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_vars"])
    subgoal premises p using p(13) by fastforce
    by(fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_state_translators
    Let_def)
  done

lemma IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret_str) =
          IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret (IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp
                                        (IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_Minus_correct_function
    IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_Minus_correct_time
    IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_Minus_correct_effects
  by (meson set_mono_prefix)

subsubsection IMP_Minus_to_IMP_Minus_Minus_stack_aux

record IMP_Minus_to_IMP_Minus_Minus_stack_aux_state =
IMP_Minus_to_IMP_Minus_Minus_stack_aux_c::nat
IMP_Minus_to_IMP_Minus_Minus_stack_aux_h::nat
IMP_Minus_to_IMP_Minus_Minus_stack_aux_t::nat
IMP_Minus_to_IMP_Minus_Minus_stack_aux_s::nat
IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret::nat

abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_aux_prefix \<equiv> ''IMP_Minus_to_IMP_Minus_Minus_stack_aux''"
abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_aux_c_str \<equiv> ''c''"
abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str \<equiv> ''h''"
abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_aux_t_str \<equiv> ''t''"
abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_aux_s_str \<equiv> ''s''"
abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str \<equiv> ''ret''"

abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars \<equiv>
 {IMP_Minus_to_IMP_Minus_Minus_stack_aux_c_str, IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str,
 IMP_Minus_to_IMP_Minus_Minus_stack_aux_t_str, IMP_Minus_to_IMP_Minus_Minus_stack_aux_s_str}"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s \<equiv>
  \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = s (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_c_str),
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = s (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str),
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = s (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_t_str),
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = s (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_s_str),
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = s (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str)\<rparr>"

paragraph IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten

abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_nth_result \<equiv> ''ten_res''"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_state_upd s \<equiv>
(let
  nth_nat_n' = 4;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  cons_t' = 0;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  nth_nat_n' = 3;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  nth_nat_result = nth_nat_ret nth_nat_ret_state;

  nth_nat_n' = 1;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;

  var_bit_list_tail_n' = nth_nat_result;
  var_bit_list_tail_v' = nth_nat_ret nth_nat_ret_state;
  var_bit_list_tail_ret' = 0;
  var_bit_list_tail_state =
  \<lparr>var_bit_list_tail_n = var_bit_list_tail_n',
  var_bit_list_tail_v = var_bit_list_tail_v',
  var_bit_list_tail_ret = var_bit_list_tail_ret'\<rparr>;
  var_bit_list_tail_ret_state = var_bit_list_tail_imp var_bit_list_tail_state;

  cons_h' = var_bit_list_tail_ret var_bit_list_tail_ret_state;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = 4;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  add_result_to_stack_nat_c' = cons_ret cons_ret_state;
  add_result_to_stack_nat_s' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s;
  add_result_to_stack_nat_ret' = 0;
  add_result_to_stack_nat_state =
    \<lparr>add_result_to_stack_nat_c = add_result_to_stack_nat_c',
    add_result_to_stack_nat_s = add_result_to_stack_nat_s',
    add_result_to_stack_nat_ret = add_result_to_stack_nat_ret'\<rparr>;
  add_result_to_stack_nat_ret_state = add_result_to_stack_nat_imp add_result_to_stack_nat_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret' = add_result_to_stack_nat_ret add_result_to_stack_nat_ret_state;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>
in
   ret
)"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_state_upd_time t s \<equiv>
(let
  nth_nat_n' = 4;
  t = t + 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  t = t + 2;
  cons_t' = 0;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  nth_nat_n' = 3;
  t = t + 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;
  nth_nat_result = nth_nat_ret nth_nat_ret_state;
  t = t + 2;

  nth_nat_n' = 1;
  t = t + 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;

  var_bit_list_tail_n' = nth_nat_result;
  t = t + 2;
  var_bit_list_tail_v' = nth_nat_ret nth_nat_ret_state;
  t = t + 2;
  var_bit_list_tail_ret' = 0;
  t = t + 2;
  var_bit_list_tail_state =
  \<lparr>var_bit_list_tail_n = var_bit_list_tail_n',
  var_bit_list_tail_v = var_bit_list_tail_v',
  var_bit_list_tail_ret = var_bit_list_tail_ret'\<rparr>;
  var_bit_list_tail_ret_state = var_bit_list_tail_imp var_bit_list_tail_state;
  t = t + var_bit_list_tail_imp_time 0 var_bit_list_tail_state;

  cons_h' = var_bit_list_tail_ret var_bit_list_tail_ret_state;
  t = t + 2;
  cons_t' = cons_ret cons_ret_state;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  cons_h' = 4;
  t = t + 2;
  cons_t' = cons_ret cons_ret_state;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  add_result_to_stack_nat_c' = cons_ret cons_ret_state;
  t = t + 2;
  add_result_to_stack_nat_s' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s;
  t = t + 2;
  add_result_to_stack_nat_ret' = 0;
  t = t + 2;
  add_result_to_stack_nat_state =
    \<lparr>add_result_to_stack_nat_c = add_result_to_stack_nat_c',
    add_result_to_stack_nat_s = add_result_to_stack_nat_s',
    add_result_to_stack_nat_ret = add_result_to_stack_nat_ret'\<rparr>;
  add_result_to_stack_nat_ret_state = add_result_to_stack_nat_imp add_result_to_stack_nat_state;
  t = t + add_result_to_stack_nat_imp_time 0 add_result_to_stack_nat_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'
    = add_result_to_stack_nat_ret add_result_to_stack_nat_ret_state;
  t = t + 2;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>
in
   t
)"

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_imp_correct:
  "IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_state_upd s)
    =
  (add_result_to_stack_nat
  (4 ## (var_bit_list_nat (nth_nat 3 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s))
  (nth_nat 1 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s)))
  ## (nth_nat 4 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s)) ## 0)
  (IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s))"
apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_state_upd_def)
apply (simp add: nth_nat_imp_correct cons_imp_correct var_bit_list_tail_imp_correct
add_result_to_stack_nat_imp_correct)
done

lemmas IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_state_translators =
IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state_def
cons_imp_to_HOL_state_def
nth_nat_imp_to_HOL_state_def
var_bit_list_tail_imp_to_HOL_state_def
add_result_to_stack_nat_imp_to_HOL_state_def

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_IMP_Minus \<equiv>
  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 4);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 3);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_nth_result
    ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 1);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;

  (var_bit_list_tail_prefix @ var_bit_list_tail_n_str)
    ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_nth_result);;
  (var_bit_list_tail_prefix @ var_bit_list_tail_v_str)
    ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (var_bit_list_tail_prefix @ var_bit_list_tail_ret_str)
    ::= A (N 0);;
  invoke_subprogram var_bit_list_tail_prefix var_bit_list_tail_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (var_bit_list_tail_prefix @ var_bit_list_tail_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (N 4);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (add_result_to_stack_nat_prefix @ add_result_to_stack_nat_c_str)
    ::= A (V (cons_prefix @ cons_ret_str));;
  (add_result_to_stack_nat_prefix @ add_result_to_stack_nat_s_str)
    ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_t_str);;
  (add_result_to_stack_nat_prefix @ add_result_to_stack_nat_ret_str)
    ::= A (N 0);;
  invoke_subprogram add_result_to_stack_nat_prefix add_result_to_stack_nat_IMP_Minus;;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str
    ::= A (V (add_result_to_stack_nat_prefix @ add_result_to_stack_nat_ret_str))
  "

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_state_upd (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_state_upd_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_nth_result, cons_prefix @ cons_ret_str}"])
   subgoal premises p using p(34) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {cons_prefix @ cons_ret_str}"])
   subgoal premises p using p(36) by fastforce
   apply (erule var_bit_list_tail_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {cons_prefix @ cons_ret_str}"])
   subgoal premises p using p(38) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(40) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(42) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(44) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(46) by fastforce
   apply (erule add_result_to_stack_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(48) by fastforce
   by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_state_translators)

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_state_upd_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_state_upd_time_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_nth_result, cons_prefix @ cons_ret_str}"])
   subgoal premises p using p(67) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {cons_prefix @ cons_ret_str}"])
   subgoal premises p using p(69) by fastforce
   apply (erule var_bit_list_tail_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {cons_prefix @ cons_ret_str}"])
   subgoal premises p using p(71) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(73) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(75) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(77) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(79) by fastforce
   apply (erule add_result_to_stack_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(81) by fastforce
   by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_state_translators Let_def)

paragraph IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight

abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_nth_result \<equiv> ''eight_res''"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_state_upd s \<equiv>
(let
  nth_nat_n' = 6;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  cons_t' = 0;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  nth_nat_n' = 5;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  nth_nat_n' = 4;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  nth_nat_result = nth_nat_ret nth_nat_ret_state;

  nth_nat_n' = 1;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;

  var_bit_list_tail_n' = nth_nat_result;
  var_bit_list_tail_v' = nth_nat_ret nth_nat_ret_state;
  var_bit_list_tail_ret' = 0;
  var_bit_list_tail_state =
  \<lparr>var_bit_list_tail_n = var_bit_list_tail_n',
  var_bit_list_tail_v = var_bit_list_tail_v',
  var_bit_list_tail_ret = var_bit_list_tail_ret'\<rparr>;
  var_bit_list_tail_ret_state = var_bit_list_tail_imp var_bit_list_tail_state;

  cons_h' = var_bit_list_tail_ret var_bit_list_tail_ret_state;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = 3;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  add_result_to_stack_nat_c' = cons_ret cons_ret_state;
  add_result_to_stack_nat_s' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s;
  add_result_to_stack_nat_ret' = 0;
  add_result_to_stack_nat_state =
    \<lparr>add_result_to_stack_nat_c = add_result_to_stack_nat_c',
    add_result_to_stack_nat_s = add_result_to_stack_nat_s',
    add_result_to_stack_nat_ret = add_result_to_stack_nat_ret'\<rparr>;
  add_result_to_stack_nat_ret_state = add_result_to_stack_nat_imp add_result_to_stack_nat_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret' = add_result_to_stack_nat_ret add_result_to_stack_nat_ret_state;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>
in
   ret
)"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_state_upd_time t s \<equiv>
(let
  nth_nat_n' = 6;
  t = t + 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  t = t + 2;
  cons_t' = 0;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  nth_nat_n' = 5;
  t = t + 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  t = t + 2;
  cons_t' = cons_ret cons_ret_state;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  nth_nat_n' = 4;
  t = t + 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;
  nth_nat_result = nth_nat_ret nth_nat_ret_state;
  t = t + 2;

  nth_nat_n' = 1;
  t = t + 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;

  var_bit_list_tail_n' = nth_nat_result;
  t = t + 2;
  var_bit_list_tail_v' = nth_nat_ret nth_nat_ret_state;
  t = t + 2;
  var_bit_list_tail_ret' = 0;
  t = t + 2;
  var_bit_list_tail_state =
  \<lparr>var_bit_list_tail_n = var_bit_list_tail_n',
  var_bit_list_tail_v = var_bit_list_tail_v',
  var_bit_list_tail_ret = var_bit_list_tail_ret'\<rparr>;
  var_bit_list_tail_ret_state = var_bit_list_tail_imp var_bit_list_tail_state;
  t = t + var_bit_list_tail_imp_time 0 var_bit_list_tail_state;

  cons_h' = var_bit_list_tail_ret var_bit_list_tail_ret_state;
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

  add_result_to_stack_nat_c' = cons_ret cons_ret_state;
  t = t + 2;
  add_result_to_stack_nat_s' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s;
  t = t + 2;
  add_result_to_stack_nat_ret' = 0;
  t = t + 2;
  add_result_to_stack_nat_state =
    \<lparr>add_result_to_stack_nat_c = add_result_to_stack_nat_c',
    add_result_to_stack_nat_s = add_result_to_stack_nat_s',
    add_result_to_stack_nat_ret = add_result_to_stack_nat_ret'\<rparr>;
  add_result_to_stack_nat_ret_state = add_result_to_stack_nat_imp add_result_to_stack_nat_state;
  t = t + add_result_to_stack_nat_imp_time 0 add_result_to_stack_nat_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'
    = add_result_to_stack_nat_ret add_result_to_stack_nat_ret_state;
  t = t + 2;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>
in
   t
)"

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_imp_correct:
  "IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_state_upd s)
    =
  (add_result_to_stack_nat
  (3 ## (var_bit_list_nat (nth_nat 4 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s))
  (nth_nat 1 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s)))
  ## (nth_nat 5 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s))
  ## (nth_nat 6 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s)) ## 0)
  (IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s))"
apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_state_upd_def)
apply (simp add: nth_nat_imp_correct cons_imp_correct var_bit_list_tail_imp_correct
add_result_to_stack_nat_imp_correct)
done

lemmas IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_state_translators =
IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state_def
cons_imp_to_HOL_state_def
nth_nat_imp_to_HOL_state_def
var_bit_list_tail_imp_to_HOL_state_def
add_result_to_stack_nat_imp_to_HOL_state_def

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_IMP_Minus \<equiv>
  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 6);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 5);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 4);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_nth_result
    ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 1);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;

  (var_bit_list_tail_prefix @ var_bit_list_tail_n_str)
    ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_nth_result);;
  (var_bit_list_tail_prefix @ var_bit_list_tail_v_str)
    ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (var_bit_list_tail_prefix @ var_bit_list_tail_ret_str)
    ::= A (N 0);;
  invoke_subprogram var_bit_list_tail_prefix var_bit_list_tail_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (var_bit_list_tail_prefix @ var_bit_list_tail_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (N 3);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (add_result_to_stack_nat_prefix @ add_result_to_stack_nat_c_str)
    ::= A (V (cons_prefix @ cons_ret_str));;
  (add_result_to_stack_nat_prefix @ add_result_to_stack_nat_s_str)
    ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_t_str);;
  (add_result_to_stack_nat_prefix @ add_result_to_stack_nat_ret_str)
    ::= A (N 0);;
  invoke_subprogram add_result_to_stack_nat_prefix add_result_to_stack_nat_IMP_Minus;;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str
    ::= A (V (add_result_to_stack_nat_prefix @ add_result_to_stack_nat_ret_str))
  "

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_state_upd (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_state_upd_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_nth_result, cons_prefix @ cons_ret_str}"])
   subgoal premises p using p(42) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {cons_prefix @ cons_ret_str}"])
   subgoal premises p using p(44) by fastforce
   apply (erule var_bit_list_tail_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {cons_prefix @ cons_ret_str}"])
   subgoal premises p using p(46) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {cons_prefix @ cons_ret_str}"])
   subgoal premises p using p(48) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(50) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(52) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(54) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(56) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(58) by fastforce
   apply (erule add_result_to_stack_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(60) by fastforce
   by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_state_translators)

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_state_upd_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_state_upd_time_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_nth_result, cons_prefix @ cons_ret_str}"])
   subgoal premises p using p(83) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {cons_prefix @ cons_ret_str}"])
   subgoal premises p using p(85) by fastforce
   apply (erule var_bit_list_tail_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {cons_prefix @ cons_ret_str}"])
   subgoal premises p using p(87) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {cons_prefix @ cons_ret_str}"])
   subgoal premises p using p(89) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(91) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(93) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(95) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(97) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(99) by fastforce
   apply (erule add_result_to_stack_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(101) by fastforce
   by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_state_translators Let_def)

paragraph IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_state_upd s \<equiv>
(let
  nth_nat_n' = 5;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  cons_t' = 0;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  nth_nat_n' = 4;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = 2;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  add_result_to_stack_nat_c' = cons_ret cons_ret_state;
  add_result_to_stack_nat_s' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s;
  add_result_to_stack_nat_ret' = 0;
  add_result_to_stack_nat_state =
    \<lparr>add_result_to_stack_nat_c = add_result_to_stack_nat_c',
    add_result_to_stack_nat_s = add_result_to_stack_nat_s',
    add_result_to_stack_nat_ret = add_result_to_stack_nat_ret'\<rparr>;
  add_result_to_stack_nat_ret_state = add_result_to_stack_nat_imp add_result_to_stack_nat_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret' = add_result_to_stack_nat_ret add_result_to_stack_nat_ret_state;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>
in
   ret
)"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_state_upd_time t s \<equiv>
(let
  nth_nat_n' = 5;
  t = t + 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  t = t + 2;
  cons_t' = 0;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  nth_nat_n' = 4;
  t = t + 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
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

  add_result_to_stack_nat_c' = cons_ret cons_ret_state;
  t = t + 2;
  add_result_to_stack_nat_s' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s;
  t = t + 2;
  add_result_to_stack_nat_ret' = 0;
  t = t + 2;
  add_result_to_stack_nat_state =
    \<lparr>add_result_to_stack_nat_c = add_result_to_stack_nat_c',
    add_result_to_stack_nat_s = add_result_to_stack_nat_s',
    add_result_to_stack_nat_ret = add_result_to_stack_nat_ret'\<rparr>;
  add_result_to_stack_nat_ret_state = add_result_to_stack_nat_imp add_result_to_stack_nat_state;
  t = t + add_result_to_stack_nat_imp_time 0 add_result_to_stack_nat_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'
    = add_result_to_stack_nat_ret add_result_to_stack_nat_ret_state;
  t = t + 2;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>
in
   t
)"

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_imp_correct:
  "IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_state_upd s)
    =
  (add_result_to_stack_nat
  (2 ## (nth_nat 4 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s))
  ## (nth_nat 5 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s)) ## 0)
  (IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s))"
apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_state_upd_def)
apply (simp add: nth_nat_imp_correct cons_imp_correct var_bit_list_tail_imp_correct
add_result_to_stack_nat_imp_correct)
done

lemmas IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_state_translators =
IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state_def
cons_imp_to_HOL_state_def
nth_nat_imp_to_HOL_state_def
add_result_to_stack_nat_imp_to_HOL_state_def

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_IMP_Minus \<equiv>
  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 5);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 4);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (N 2);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (add_result_to_stack_nat_prefix @ add_result_to_stack_nat_c_str)
    ::= A (V (cons_prefix @ cons_ret_str));;
  (add_result_to_stack_nat_prefix @ add_result_to_stack_nat_s_str)
    ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_t_str);;
  (add_result_to_stack_nat_prefix @ add_result_to_stack_nat_ret_str)
    ::= A (N 0);;
  invoke_subprogram add_result_to_stack_nat_prefix add_result_to_stack_nat_IMP_Minus;;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str
    ::= A (V (add_result_to_stack_nat_prefix @ add_result_to_stack_nat_ret_str))
  "

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_state_upd (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_state_upd_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {cons_prefix @ cons_ret_str}"])
   subgoal premises p using p(25) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(27) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(29) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(31) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(33) by fastforce
   apply (erule add_result_to_stack_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(35) by fastforce
   by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_state_translators)

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_state_upd_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_state_upd_time_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {cons_prefix @ cons_ret_str}"])
   subgoal premises p using p(49) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(51) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(53) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(55) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(57) by fastforce
   apply (erule add_result_to_stack_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(59) by fastforce
   by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_state_translators Let_def)

paragraph IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_state_upd s \<equiv>
(let
  nth_nat_n' = 3;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  assignment_to_binary_tail_n' = nth_nat_ret nth_nat_ret_state;

  nth_nat_n' = 1;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  nth_nat_result = nth_nat_ret nth_nat_ret_state;
  assignment_to_binary_tail_v' = nth_nat_ret nth_nat_ret_state;

  nth_nat_n' = 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;

  assignment_to_binary_tail_axep' = nth_nat_ret nth_nat_ret_state;
  assignment_to_binary_tail_ret' = 0;
  assignment_to_binary_tail_state =
    \<lparr>assignment_to_binary_tail_n = assignment_to_binary_tail_n',
    assignment_to_binary_tail_v = assignment_to_binary_tail_v',
    assignment_to_binary_tail_aexp = assignment_to_binary_tail_axep',
    assignment_to_binary_tail_ret = assignment_to_binary_tail_ret'\<rparr>;
  assignment_to_binary_tail_ret_state = assignment_to_binary_tail_imp assignment_to_binary_tail_state;

  add_result_to_stack_nat_c' = assignment_to_binary_tail_ret assignment_to_binary_tail_ret_state;
  add_result_to_stack_nat_s' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s;
  add_result_to_stack_nat_ret' = 0;
  add_result_to_stack_nat_state =
    \<lparr>add_result_to_stack_nat_c = add_result_to_stack_nat_c',
    add_result_to_stack_nat_s = add_result_to_stack_nat_s',
    add_result_to_stack_nat_ret = add_result_to_stack_nat_ret'\<rparr>;
  add_result_to_stack_nat_ret_state = add_result_to_stack_nat_imp add_result_to_stack_nat_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret' = add_result_to_stack_nat_ret add_result_to_stack_nat_ret_state;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>
in
   ret
)"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_state_upd_time t s \<equiv>
(let
  nth_nat_n' = 3;
  t = t + 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;
  assignment_to_binary_tail_n' = nth_nat_ret nth_nat_ret_state;
  t = t + 2;

  nth_nat_n' = 1;
  t = t + 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  nth_nat_result = nth_nat_ret nth_nat_ret_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;
  assignment_to_binary_tail_v' = nth_nat_ret nth_nat_ret_state;
  t = t + 2;

  nth_nat_n' = 2;
  t = t + 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;

  assignment_to_binary_tail_axep' = nth_nat_ret nth_nat_ret_state;
  t = t + 2;
  assignment_to_binary_tail_ret' = 0;
  t = t + 2;
  assignment_to_binary_tail_state =
    \<lparr>assignment_to_binary_tail_n = assignment_to_binary_tail_n',
    assignment_to_binary_tail_v = assignment_to_binary_tail_v',
    assignment_to_binary_tail_aexp = assignment_to_binary_tail_axep',
    assignment_to_binary_tail_ret = assignment_to_binary_tail_ret'\<rparr>;
  assignment_to_binary_tail_ret_state = assignment_to_binary_tail_imp assignment_to_binary_tail_state;
  t = t + assignment_to_binary_tail_imp_time 0 assignment_to_binary_tail_state;

  add_result_to_stack_nat_c' = assignment_to_binary_tail_ret assignment_to_binary_tail_ret_state;
  t = t + 2;
  add_result_to_stack_nat_s' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s;
  t = t + 2;
  add_result_to_stack_nat_ret' = 0;
  t = t + 2;
  add_result_to_stack_nat_state =
    \<lparr>add_result_to_stack_nat_c = add_result_to_stack_nat_c',
    add_result_to_stack_nat_s = add_result_to_stack_nat_s',
    add_result_to_stack_nat_ret = add_result_to_stack_nat_ret'\<rparr>;
  add_result_to_stack_nat_ret_state = add_result_to_stack_nat_imp add_result_to_stack_nat_state;
  t = t + add_result_to_stack_nat_imp_time 0 add_result_to_stack_nat_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret' = add_result_to_stack_nat_ret add_result_to_stack_nat_ret_state;
  t = t + 2;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>
in
   t
)"

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_imp_correct:
  "IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_state_upd s)
    =
  (add_result_to_stack_nat
  (assignment_to_binary_nat
  (nth_nat 3 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s))
  (nth_nat 1 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s))
  (nth_nat 2 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s)))
  (IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s))"
apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_state_upd_def)
apply (simp add: nth_nat_imp_correct  add_result_to_stack_nat_imp_correct
assignment_to_binary_tail_imp_correct subtail_assignment_to_binary)
done


lemmas IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_state_translators =
IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state_def
nth_nat_imp_to_HOL_state_def
assignment_to_binary_tail_imp_to_HOL_state_def
add_result_to_stack_nat_imp_to_HOL_state_def

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_IMP_Minus \<equiv>
  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 3);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  (assignment_to_binary_tail_prefix @ assignment_to_binary_tail_n_str)
    ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 1);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  (assignment_to_binary_tail_prefix @ assignment_to_binary_tail_v_str)
    ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 2);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  (assignment_to_binary_tail_prefix @ assignment_to_binary_tail_aexp_str)
    ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;

  (assignment_to_binary_tail_prefix @ assignment_to_binary_tail_ret_str) ::= A (N 0);;
  invoke_subprogram assignment_to_binary_tail_prefix assignment_to_binary_tail_IMP_Minus;;

  (add_result_to_stack_nat_prefix @ add_result_to_stack_nat_c_str)
    ::= A (V (assignment_to_binary_tail_prefix @ assignment_to_binary_tail_ret_str));;
  (add_result_to_stack_nat_prefix @ add_result_to_stack_nat_s_str)
    ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_t_str);;
  (add_result_to_stack_nat_prefix @ add_result_to_stack_nat_ret_str)
    ::= A (N 0);;
  invoke_subprogram add_result_to_stack_nat_prefix add_result_to_stack_nat_IMP_Minus;;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str
    ::= A (V (add_result_to_stack_nat_prefix @ add_result_to_stack_nat_ret_str))
  "

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_state_upd (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_state_upd_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {(assignment_to_binary_tail_prefix @ assignment_to_binary_tail_v_str), (assignment_to_binary_tail_prefix @ assignment_to_binary_tail_n_str)}"])
   subgoal premises p using p(22) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {(assignment_to_binary_tail_prefix @ assignment_to_binary_tail_n_str)}"])
   subgoal premises p using p(24) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(26) by fastforce
   apply (erule assignment_to_binary_tail_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(28) by fastforce
   apply (erule add_result_to_stack_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(30) by fastforce
   by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_state_translators)

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_state_upd_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_state_upd_time_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {(assignment_to_binary_tail_prefix @ assignment_to_binary_tail_v_str), (assignment_to_binary_tail_prefix @ assignment_to_binary_tail_n_str)}"])
   subgoal premises p using p(43) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {(assignment_to_binary_tail_prefix @ assignment_to_binary_tail_n_str)}"])
   subgoal premises p using p(45) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(47) by fastforce
   apply (erule assignment_to_binary_tail_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(49) by fastforce
   apply (erule add_result_to_stack_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(51) by fastforce
   by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_state_translators Let_def)


definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_state_upd s \<equiv>
(let
  cons_h' = 0;
  cons_t' = 0;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  add_result_to_stack_nat_c' = cons_ret cons_ret_state;
  add_result_to_stack_nat_s' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s;
  add_result_to_stack_nat_ret' = 0;
  add_result_to_stack_nat_state =
    \<lparr>add_result_to_stack_nat_c = add_result_to_stack_nat_c',
    add_result_to_stack_nat_s = add_result_to_stack_nat_s',
    add_result_to_stack_nat_ret = add_result_to_stack_nat_ret'\<rparr>;
  add_result_to_stack_nat_ret_state = add_result_to_stack_nat_imp add_result_to_stack_nat_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret' = add_result_to_stack_nat_ret add_result_to_stack_nat_ret_state;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>
in
   ret
)"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_state_upd_time t s \<equiv>
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

  add_result_to_stack_nat_c' = cons_ret cons_ret_state;
  t = t + 2;
  add_result_to_stack_nat_s' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s;
  t = t + 2;
  add_result_to_stack_nat_ret' = 0;
  t = t + 2;
  add_result_to_stack_nat_state =
    \<lparr>add_result_to_stack_nat_c = add_result_to_stack_nat_c',
    add_result_to_stack_nat_s = add_result_to_stack_nat_s',
    add_result_to_stack_nat_ret = add_result_to_stack_nat_ret'\<rparr>;
  add_result_to_stack_nat_ret_state = add_result_to_stack_nat_imp add_result_to_stack_nat_state;
  t = t + add_result_to_stack_nat_imp_time 0 add_result_to_stack_nat_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'
    = add_result_to_stack_nat_ret add_result_to_stack_nat_ret_state;
  t = t + 2;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>
in
   t
)"

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_imp_correct:
  "IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_state_upd s)
    =
  (add_result_to_stack_nat
  (0##0)
  (IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s))"
apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_state_upd_def)
apply (simp add: cons_imp_correct add_result_to_stack_nat_imp_correct)
done

lemmas IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_state_translators =
IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state_def
cons_imp_to_HOL_state_def
add_result_to_stack_nat_imp_to_HOL_state_def

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_IMP_Minus \<equiv>
  (cons_prefix @ cons_h_str) ::= A (N 0);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (add_result_to_stack_nat_prefix @ add_result_to_stack_nat_c_str)
    ::= A (V (cons_prefix @ cons_ret_str));;
  (add_result_to_stack_nat_prefix @ add_result_to_stack_nat_s_str)
    ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_t_str);;
  (add_result_to_stack_nat_prefix @ add_result_to_stack_nat_ret_str)
    ::= A (N 0);;
  invoke_subprogram add_result_to_stack_nat_prefix add_result_to_stack_nat_IMP_Minus;;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str
    ::= A (V (add_result_to_stack_nat_prefix @ add_result_to_stack_nat_ret_str))
  "

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_state_upd (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_state_upd_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(9) by fastforce
   apply (erule add_result_to_stack_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(11) by fastforce
   by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_state_translators)

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_state_upd_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_state_upd_time_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule cons_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(17) by fastforce
   apply (erule add_result_to_stack_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(19) by fastforce
   by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_state_translators Let_def)

paragraph IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_state_upd s \<equiv>
(let
  nth_nat_n' = 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_res_one = nth_nat_ret nth_nat_ret_state;

  nth_nat_n' = 3;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;

  push_on_stack_nat_c' = IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_res_one;
  push_on_stack_nat_n' = nth_nat_ret nth_nat_ret_state;
  push_on_stack_nat_s' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s;
  push_on_stack_nat_ret' = 0;
  push_on_stack_nat_state = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c',
  push_on_stack_nat_n = push_on_stack_nat_n',
  push_on_stack_nat_s = push_on_stack_nat_s',
  push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>;
  push_on_stack_nat_ret_state = push_on_stack_nat_imp push_on_stack_nat_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret' = push_on_stack_nat_ret push_on_stack_nat_ret_state;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>
in
   ret
)"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_state_upd_time t s \<equiv>
(let
  nth_nat_n' = 2;
  t = t + 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;
  IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_res_one = nth_nat_ret nth_nat_ret_state;
  t = t + 2;

  nth_nat_n' = 3;
  t = t + 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;

  push_on_stack_nat_c' = IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_res_one;
  t = t + 2;
  push_on_stack_nat_n' = nth_nat_ret nth_nat_ret_state;
  t = t + 2;
  push_on_stack_nat_s' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s;
  t = t + 2;
  push_on_stack_nat_ret' = 0;
  t = t + 2;
  push_on_stack_nat_state = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c',
  push_on_stack_nat_n = push_on_stack_nat_n',
  push_on_stack_nat_s = push_on_stack_nat_s',
  push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>;
  push_on_stack_nat_ret_state = push_on_stack_nat_imp push_on_stack_nat_state;
  t = t + push_on_stack_nat_imp_time 0 push_on_stack_nat_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret' = push_on_stack_nat_ret push_on_stack_nat_ret_state;
  t = t + 2;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>
in
   t
)"

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_imp_correct:
  "IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_state_upd s)
    =
  (push_on_stack_nat
  (nth_nat 2 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s))
  (nth_nat 3 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s))
  (IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s))"
apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_state_upd_def)
apply (simp add: nth_nat_imp_correct  push_on_stack_nat_imp_correct )
done


lemmas IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_state_translators =
IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state_def
nth_nat_imp_to_HOL_state_def
push_on_stack_nat_imp_to_HOL_state_def

abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_res_one \<equiv> ''res1''"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_IMP_Minus \<equiv>
  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 2);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_res_one
    ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 3);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;

  (push_on_stack_nat_prefix @ push_on_stack_nat_c_str)
    ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_res_one);;
  (push_on_stack_nat_prefix @ push_on_stack_nat_n_str)
    ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (push_on_stack_nat_prefix @ push_on_stack_nat_s_str)
    ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_s_str);;
  (push_on_stack_nat_prefix @ push_on_stack_nat_ret_str)
    ::= A (N 0);;
  invoke_subprogram push_on_stack_nat_prefix push_on_stack_nat_IMP_Minus;;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str
    ::= A (V (push_on_stack_nat_prefix @ push_on_stack_nat_ret_str))
  "

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_state_upd (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_state_upd_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_res_one}"])
   subgoal premises p using p(15) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(17) by fastforce
   apply (erule push_on_stack_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(19) by fastforce
   by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_state_translators)


lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_state_upd_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_state_upd_time_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_res_one}"])
   subgoal premises p using p(29) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(31) by fastforce
   apply (erule push_on_stack_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(33) by fastforce
   by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_state_translators Let_def)

paragraph IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_state_upd s \<equiv>
(let
  nth_nat_n' = 3;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_res_one = nth_nat_ret nth_nat_ret_state;

  nth_nat_n' = 4;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;

  push_on_stack_nat_c' = IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_res_one;
  push_on_stack_nat_n' = nth_nat_ret nth_nat_ret_state;
  push_on_stack_nat_s' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s;
  push_on_stack_nat_ret' = 0;
  push_on_stack_nat_state = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c',
  push_on_stack_nat_n = push_on_stack_nat_n',
  push_on_stack_nat_s = push_on_stack_nat_s',
  push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>;
  push_on_stack_nat_ret_state = push_on_stack_nat_imp push_on_stack_nat_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret' = push_on_stack_nat_ret push_on_stack_nat_ret_state;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>
in
   ret
)"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_state_upd_time t s \<equiv>
(let
  nth_nat_n' = 3;
  t = t + 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;
  IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_res_one = nth_nat_ret nth_nat_ret_state;
  t = t + 2;

  nth_nat_n' = 4;
  t = t + 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;

  push_on_stack_nat_c' = IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_res_one;
  t = t + 2;
  push_on_stack_nat_n' = nth_nat_ret nth_nat_ret_state;
  t = t + 2;
  push_on_stack_nat_s' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s;
  t = t + 2;
  push_on_stack_nat_ret' = 0;
  t = t + 2;
  push_on_stack_nat_state = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c',
  push_on_stack_nat_n = push_on_stack_nat_n',
  push_on_stack_nat_s = push_on_stack_nat_s',
  push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>;
  push_on_stack_nat_ret_state = push_on_stack_nat_imp push_on_stack_nat_state;
  t = t + push_on_stack_nat_imp_time 0 push_on_stack_nat_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret' = push_on_stack_nat_ret push_on_stack_nat_ret_state;
  t = t + 2;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>
in
   t
)"

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_imp_correct:
  "IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_state_upd s)
    =
  (push_on_stack_nat
  (nth_nat 3 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s))
  (nth_nat 4 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s))
  (IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s))"
apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_state_upd_def)
apply (simp add: nth_nat_imp_correct  push_on_stack_nat_imp_correct )
done


lemmas IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_state_translators =
IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state_def
nth_nat_imp_to_HOL_state_def
push_on_stack_nat_imp_to_HOL_state_def

abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_res_one \<equiv> ''res1''"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_IMP_Minus \<equiv>
  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 3);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_res_one
    ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 4);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;

  (push_on_stack_nat_prefix @ push_on_stack_nat_c_str)
    ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_res_one);;
  (push_on_stack_nat_prefix @ push_on_stack_nat_n_str)
    ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (push_on_stack_nat_prefix @ push_on_stack_nat_s_str)
    ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_s_str);;
  (push_on_stack_nat_prefix @ push_on_stack_nat_ret_str)
    ::= A (N 0);;
  invoke_subprogram push_on_stack_nat_prefix push_on_stack_nat_IMP_Minus;;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str
    ::= A (V (push_on_stack_nat_prefix @ push_on_stack_nat_ret_str))
  "

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_state_upd (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_state_upd_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_res_one}"])
   subgoal premises p using p(15) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(17) by fastforce
   apply (erule push_on_stack_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(19) by fastforce
   by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_state_translators)


lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_state_upd_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_state_upd_time_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_res_one}"])
   subgoal premises p using p(29) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(31) by fastforce
   apply (erule push_on_stack_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(33) by fastforce
   by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_state_translators Let_def)

paragraph IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_state_upd s \<equiv>
(let
  nth_nat_n' = 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_res_one = nth_nat_ret nth_nat_ret_state;

  nth_nat_n' = 4;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;

  push_on_stack_nat_c' = IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_res_one;
  push_on_stack_nat_n' = nth_nat_ret nth_nat_ret_state;
  push_on_stack_nat_s' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s;
  push_on_stack_nat_ret' = 0;
  push_on_stack_nat_state = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c',
  push_on_stack_nat_n = push_on_stack_nat_n',
  push_on_stack_nat_s = push_on_stack_nat_s',
  push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>;
  push_on_stack_nat_ret_state = push_on_stack_nat_imp push_on_stack_nat_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret' = push_on_stack_nat_ret push_on_stack_nat_ret_state;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>
in
   ret
)"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_state_upd_time t s \<equiv>
(let
  nth_nat_n' = 2;
  t = t + 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;
  IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_res_one = nth_nat_ret nth_nat_ret_state;
  t = t + 2;

  nth_nat_n' = 4;
  t = t + 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;

  push_on_stack_nat_c' = IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_res_one;
  t = t + 2;
  push_on_stack_nat_n' = nth_nat_ret nth_nat_ret_state;
  t = t + 2;
  push_on_stack_nat_s' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s;
  t = t + 2;
  push_on_stack_nat_ret' = 0;
  t = t + 2;
  push_on_stack_nat_state = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c',
  push_on_stack_nat_n = push_on_stack_nat_n',
  push_on_stack_nat_s = push_on_stack_nat_s',
  push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>;
  push_on_stack_nat_ret_state = push_on_stack_nat_imp push_on_stack_nat_state;
  t = t + push_on_stack_nat_imp_time 0 push_on_stack_nat_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret' = push_on_stack_nat_ret push_on_stack_nat_ret_state;
  t = t + 2;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>
in
   t
)"

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_imp_correct:
  "IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_state_upd s)
    =
  (push_on_stack_nat
  (nth_nat 2 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s))
  (nth_nat 4 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s))
  (IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s))"
apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_state_upd_def)
apply (simp add: nth_nat_imp_correct  push_on_stack_nat_imp_correct )
done


lemmas IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_state_translators =
IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state_def
nth_nat_imp_to_HOL_state_def
push_on_stack_nat_imp_to_HOL_state_def

abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_res_one \<equiv> ''res1''"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_IMP_Minus \<equiv>
  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 2);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_res_one
    ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 4);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;

  (push_on_stack_nat_prefix @ push_on_stack_nat_c_str)
    ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_res_one);;
  (push_on_stack_nat_prefix @ push_on_stack_nat_n_str)
    ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (push_on_stack_nat_prefix @ push_on_stack_nat_s_str)
    ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_s_str);;
  (push_on_stack_nat_prefix @ push_on_stack_nat_ret_str)
    ::= A (N 0);;
  invoke_subprogram push_on_stack_nat_prefix push_on_stack_nat_IMP_Minus;;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str
    ::= A (V (push_on_stack_nat_prefix @ push_on_stack_nat_ret_str))
  "

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_state_upd (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_state_upd_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_res_one}"])
   subgoal premises p using p(15) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(17) by fastforce
   apply (erule push_on_stack_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(19) by fastforce
   by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_state_translators)


lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_state_upd_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_state_upd_time_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_res_one}"])
   subgoal premises p using p(29) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(31) by fastforce
   apply (erule push_on_stack_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(33) by fastforce
   by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_state_translators Let_def)

paragraph IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_state_upd s \<equiv>
(let
  nth_nat_n' = 1;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_res_one = nth_nat_ret nth_nat_ret_state;

  nth_nat_n' = 3;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;

  push_on_stack_nat_c' = IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_res_one;
  push_on_stack_nat_n' = nth_nat_ret nth_nat_ret_state;
  push_on_stack_nat_s' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s;
  push_on_stack_nat_ret' = 0;
  push_on_stack_nat_state = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c',
  push_on_stack_nat_n = push_on_stack_nat_n',
  push_on_stack_nat_s = push_on_stack_nat_s',
  push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>;
  push_on_stack_nat_ret_state = push_on_stack_nat_imp push_on_stack_nat_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret' = push_on_stack_nat_ret push_on_stack_nat_ret_state;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>
in
   ret
)"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_state_upd_time t s \<equiv>
(let
  nth_nat_n' = 1;
  t = t + 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;
  IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_res_one = nth_nat_ret nth_nat_ret_state;
  t = t + 2;

  nth_nat_n' = 3;
  t = t + 2;
  nth_nat_x' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n',
  nth_nat_x = nth_nat_x',
  nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;

  push_on_stack_nat_c' = IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_res_one;
  t = t + 2;
  push_on_stack_nat_n' = nth_nat_ret nth_nat_ret_state;
  t = t + 2;
  push_on_stack_nat_s' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s;
  t = t + 2;
  push_on_stack_nat_ret' = 0;
  t = t + 2;
  push_on_stack_nat_state = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c',
  push_on_stack_nat_n = push_on_stack_nat_n',
  push_on_stack_nat_s = push_on_stack_nat_s',
  push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>;
  push_on_stack_nat_ret_state = push_on_stack_nat_imp push_on_stack_nat_state;
  t = t + push_on_stack_nat_imp_time 0 push_on_stack_nat_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret' = push_on_stack_nat_ret push_on_stack_nat_ret_state;
  t = t + 2;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>
in
   t
)"

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_imp_correct:
  "IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_state_upd s)
    =
  (push_on_stack_nat
  (nth_nat 1 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s))
  (nth_nat 3 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s))
  (IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s))"
apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_state_upd_def)
apply (simp add: nth_nat_imp_correct  push_on_stack_nat_imp_correct )
done


lemmas IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_state_translators =
IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state_def
nth_nat_imp_to_HOL_state_def
push_on_stack_nat_imp_to_HOL_state_def

abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_res_one \<equiv> ''res1''"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_IMP_Minus \<equiv>
  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 1);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_res_one
    ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 3);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;

  (push_on_stack_nat_prefix @ push_on_stack_nat_c_str)
    ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_res_one);;
  (push_on_stack_nat_prefix @ push_on_stack_nat_n_str)
    ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (push_on_stack_nat_prefix @ push_on_stack_nat_s_str)
    ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_s_str);;
  (push_on_stack_nat_prefix @ push_on_stack_nat_ret_str)
    ::= A (N 0);;
  invoke_subprogram push_on_stack_nat_prefix push_on_stack_nat_IMP_Minus;;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str
    ::= A (V (push_on_stack_nat_prefix @ push_on_stack_nat_ret_str))
  "

lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_state_upd (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_state_upd_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_res_one}"])
   subgoal premises p using p(15) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(17) by fastforce
   apply (erule push_on_stack_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(19) by fastforce
   by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_state_translators)


lemma IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_state_upd_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_state_upd_time_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_res_one}"])
   subgoal premises p using p(29) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(31) by fastforce
   apply (erule push_on_stack_nat_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars"])
   subgoal premises p using p(33) by fastforce
   by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_state_translators Let_def)

subsubsection "auxiliary functions"

lemmas IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators=
EQUAL_neq_zero_imp_to_HOL_state_def
IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state_def

abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_aux_cond \<equiv> ''cond''"

paragraph IMP_Minus_to_IMP_Minus_Minus_stack_aux0

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux0_state_upd s \<equiv>
(let
  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s;
  EQUAL_neq_zero_b' = 10;
  EQUAL_neq_zero_ret' = 0;
  EQUAL_neq_zero_state =
    \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
    EQUAL_neq_zero_b = EQUAL_neq_zero_b',
    EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  cond = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state
in
 (if cond \<noteq> 0
 then IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_state_upd s
 else
   (let
     IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret' = 0;
     ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s,
      IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s,
      IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s,
      IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s,
      IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>
   in
    ret)))"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux0_state_upd_time t s \<equiv>
(let
  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s;
  t = t + 2;
  EQUAL_neq_zero_b' = 10;
  t = t + 2;
  EQUAL_neq_zero_ret' = 0;
  t = t + 2;
  EQUAL_neq_zero_state =
    \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
    EQUAL_neq_zero_b = EQUAL_neq_zero_b',
    EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  t = t + EQUAL_neq_zero_imp_time 0 EQUAL_neq_zero_state;
  cond = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;
  t = t + 2
in
 (if cond \<noteq> 0
 then (
  let
   t = t + 1;
   t = t + IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_state_upd_time 0 s
  in
   t)
 else
   (let
     t = t + 1;
     IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret' = 0;
     t = t + 2;
     ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s,
      IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s,
      IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s,
      IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s,
      IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>
   in
    t)))"

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux0_imp_correct:
  "IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_aux0_state_upd s)
    = IMP_Minus_to_IMP_Minus_Minus_stack_aux0 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s)
    (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s) (IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s)"
  apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux0_state_upd_def IMP_Minus_to_IMP_Minus_Minus_stack_aux0_def)
  apply (simp add:EQUAL_neq_zero_imp_correct IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_imp_correct)
  done

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux0_IMP_Minus \<equiv>
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_a_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_c_str);;
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_b_str) ::= A (N 10);;
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str) ::= A (N 0);;
  invoke_subprogram EQUAL_neq_zero_prefix EQUAL_neq_zero_IMP_Minus;;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_cond ::= A (V (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str));;

  IF IMP_Minus_to_IMP_Minus_Minus_stack_aux_cond \<noteq>0
  THEN IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_IMP_Minus
  ELSE IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str ::= A (N 0)
  "

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux0_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_aux0_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_aux0_state_upd (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_aux0_state_upd_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux0_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule EQUAL_neq_zero_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {''ret''}"])
   subgoal premises p using p(6) by fastforce
   apply (erule  If_E)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_IMP_Minus_correct_function)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
     subgoal
     by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators)
   done

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux0_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_aux0_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (IMP_Minus_to_IMP_Minus_Minus_stack_aux0_state_upd_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_aux0_state_upd_time_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux0_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule EQUAL_neq_zero_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {''ret''}"])
   subgoal premises p using p(11) by fastforce
   apply (erule  If_tE)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_ten_IMP_Minus_correct_time)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
     subgoal
     by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators)
   done

paragraph IMP_Minus_to_IMP_Minus_Minus_stack_aux1

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux1_state_upd s \<equiv>
(let
  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s;
  EQUAL_neq_zero_b' = 8;
  EQUAL_neq_zero_ret' = 0;
  EQUAL_neq_zero_state =
    \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
    EQUAL_neq_zero_b = EQUAL_neq_zero_b',
    EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  cond = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state
in
 (if cond \<noteq> 0
 then IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_state_upd s
 else IMP_Minus_to_IMP_Minus_Minus_stack_aux0_state_upd s
   ))"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux1_state_upd_time t s \<equiv>
(let
  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s;
  t = t + 2;
  EQUAL_neq_zero_b' = 8;
  t = t + 2;
  EQUAL_neq_zero_ret' = 0;
  t = t + 2;
  EQUAL_neq_zero_state =
    \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
    EQUAL_neq_zero_b = EQUAL_neq_zero_b',
    EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  t = t + EQUAL_neq_zero_imp_time 0 EQUAL_neq_zero_state;
  cond = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;
  t = t + 2
in
 (if cond \<noteq> 0
 then (
  let
   t = t + 1;
   t = t + IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_state_upd_time 0 s
  in
   t)
 else
   (let
     t = t + 1;
     t = t + IMP_Minus_to_IMP_Minus_Minus_stack_aux0_state_upd_time 0 s
   in
    t)))"

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux1_imp_correct:
  "IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_aux1_state_upd s)
    = IMP_Minus_to_IMP_Minus_Minus_stack_aux1 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s)
    (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s) (IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s)"
  apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux1_state_upd_def IMP_Minus_to_IMP_Minus_Minus_stack_aux1_def)
  apply (simp add:EQUAL_neq_zero_imp_correct IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_imp_correct
  IMP_Minus_to_IMP_Minus_Minus_stack_aux0_imp_correct)
  done

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux1_IMP_Minus \<equiv>
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_a_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_c_str);;
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_b_str) ::= A (N 8);;
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str) ::= A (N 0);;
  invoke_subprogram EQUAL_neq_zero_prefix EQUAL_neq_zero_IMP_Minus;;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_cond ::= A (V (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str));;

  IF IMP_Minus_to_IMP_Minus_Minus_stack_aux_cond \<noteq>0
  THEN IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_IMP_Minus
  ELSE IMP_Minus_to_IMP_Minus_Minus_stack_aux0_IMP_Minus
  "

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux1_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_aux1_state_upd (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_aux1_state_upd_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux1_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule EQUAL_neq_zero_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {''ret''}"])
   subgoal premises p using p(6) by fastforce
   apply (erule  If_E)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_IMP_Minus_correct_function)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_aux0_IMP_Minus_correct_function)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
   done

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux1_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (IMP_Minus_to_IMP_Minus_Minus_stack_aux1_state_upd_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_aux1_state_upd_time_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux1_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule EQUAL_neq_zero_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {''ret''}"])
   subgoal premises p using p(11) by fastforce
   apply (erule  If_tE)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_eight_IMP_Minus_correct_time)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_aux0_IMP_Minus_correct_time)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
   done

paragraph IMP_Minus_to_IMP_Minus_Minus_stack_aux2

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux2_state_upd s \<equiv>
(let
  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s;
  EQUAL_neq_zero_b' = 5;
  EQUAL_neq_zero_ret' = 0;
  EQUAL_neq_zero_state =
    \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
    EQUAL_neq_zero_b = EQUAL_neq_zero_b',
    EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  cond = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state
in
 (if cond \<noteq> 0
 then IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_state_upd s
 else IMP_Minus_to_IMP_Minus_Minus_stack_aux1_state_upd s
   ))"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux2_state_upd_time t s \<equiv>
(let
  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s;
  t = t + 2;
  EQUAL_neq_zero_b' = 5;
  t = t + 2;
  EQUAL_neq_zero_ret' = 0;
  t = t + 2;
  EQUAL_neq_zero_state =
    \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
    EQUAL_neq_zero_b = EQUAL_neq_zero_b',
    EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  t = t + EQUAL_neq_zero_imp_time 0 EQUAL_neq_zero_state;
  cond = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;
  t = t + 2
in
 (if cond \<noteq> 0
 then (
  let
   t = t + 1;
   t = t + IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_state_upd_time 0 s
  in
   t)
 else
   (let
     t = t + 1;
     t = t + IMP_Minus_to_IMP_Minus_Minus_stack_aux1_state_upd_time 0 s
   in
    t)))"

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux2_imp_correct:
  "IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_aux2_state_upd s)
    = IMP_Minus_to_IMP_Minus_Minus_stack_aux2 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s)
    (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s) (IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s)"
  apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux2_state_upd_def IMP_Minus_to_IMP_Minus_Minus_stack_aux2_def)
  apply (simp add:EQUAL_neq_zero_imp_correct IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_imp_correct
  IMP_Minus_to_IMP_Minus_Minus_stack_aux1_imp_correct)
  done

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux2_IMP_Minus \<equiv>
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_a_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_c_str);;
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_b_str) ::= A (N 5);;
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str) ::= A (N 0);;
  invoke_subprogram EQUAL_neq_zero_prefix EQUAL_neq_zero_IMP_Minus;;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_cond ::= A (V (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str));;

  IF IMP_Minus_to_IMP_Minus_Minus_stack_aux_cond \<noteq>0
  THEN IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_IMP_Minus
  ELSE IMP_Minus_to_IMP_Minus_Minus_stack_aux1_IMP_Minus
  "

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux2_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_aux2_state_upd (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_aux2_state_upd_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux2_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule EQUAL_neq_zero_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {''ret''}"])
   subgoal premises p using p(6) by fastforce
   apply (erule  If_E)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_IMP_Minus_correct_function)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_aux1_IMP_Minus_correct_function)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
   done

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux2_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (IMP_Minus_to_IMP_Minus_Minus_stack_aux2_state_upd_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_aux2_state_upd_time_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux2_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule EQUAL_neq_zero_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {''ret''}"])
   subgoal premises p using p(11) by fastforce
   apply (erule  If_tE)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_five_IMP_Minus_correct_time)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_aux1_IMP_Minus_correct_time)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
   done

paragraph IMP_Minus_to_IMP_Minus_Minus_stack_aux3

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux3_state_upd s \<equiv>
(let
  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s;
  EQUAL_neq_zero_b' = 2;
  EQUAL_neq_zero_ret' = 0;
  EQUAL_neq_zero_state =
    \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
    EQUAL_neq_zero_b = EQUAL_neq_zero_b',
    EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  cond = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state
in
 (if cond \<noteq> 0
 then IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_state_upd s
 else IMP_Minus_to_IMP_Minus_Minus_stack_aux2_state_upd s
   ))"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux3_state_upd_time t s \<equiv>
(let
  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s;
  t = t + 2;
  EQUAL_neq_zero_b' = 2;
  t = t + 2;
  EQUAL_neq_zero_ret' = 0;
  t = t + 2;
  EQUAL_neq_zero_state =
    \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
    EQUAL_neq_zero_b = EQUAL_neq_zero_b',
    EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  t = t + EQUAL_neq_zero_imp_time 0 EQUAL_neq_zero_state;
  cond = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;
  t = t + 2
in
 (if cond \<noteq> 0
 then (
  let
   t = t + 1;
   t = t + IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_state_upd_time 0 s
  in
   t)
 else
   (let
     t = t + 1;
     t = t + IMP_Minus_to_IMP_Minus_Minus_stack_aux2_state_upd_time 0 s
   in
    t)))"

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux3_imp_correct:
  "IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_aux3_state_upd s)
    = IMP_Minus_to_IMP_Minus_Minus_stack_aux3 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s)
    (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s) (IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s)"
  apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux3_state_upd_def IMP_Minus_to_IMP_Minus_Minus_stack_aux3_def)
  apply (simp add:EQUAL_neq_zero_imp_correct IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_imp_correct
  IMP_Minus_to_IMP_Minus_Minus_stack_aux2_imp_correct)
  done

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux3_IMP_Minus \<equiv>
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_a_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_c_str);;
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_b_str) ::= A (N 2);;
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str) ::= A (N 0);;
  invoke_subprogram EQUAL_neq_zero_prefix EQUAL_neq_zero_IMP_Minus;;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_cond ::= A (V (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str));;

  IF IMP_Minus_to_IMP_Minus_Minus_stack_aux_cond \<noteq>0
  THEN IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_IMP_Minus
  ELSE IMP_Minus_to_IMP_Minus_Minus_stack_aux2_IMP_Minus
  "

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux3_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_aux3_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_aux3_state_upd (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_aux3_state_upd_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux3_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule EQUAL_neq_zero_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {''ret''}"])
   subgoal premises p using p(6) by fastforce
   apply (erule  If_E)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_IMP_Minus_correct_function)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_aux2_IMP_Minus_correct_function)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
   done

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux3_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_aux3_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (IMP_Minus_to_IMP_Minus_Minus_stack_aux3_state_upd_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_aux3_state_upd_time_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux3_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule EQUAL_neq_zero_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {''ret''}"])
   subgoal premises p using p(11) by fastforce
   apply (erule  If_tE)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_two_IMP_Minus_correct_time)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_aux2_IMP_Minus_correct_time)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
   done

paragraph IMP_Minus_to_IMP_Minus_Minus_stack_aux4

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux4_state_upd s \<equiv>
(let
  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s;
  EQUAL_neq_zero_b' = 1;
  EQUAL_neq_zero_ret' = 0;
  EQUAL_neq_zero_state =
    \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
    EQUAL_neq_zero_b = EQUAL_neq_zero_b',
    EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  cond = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state
in
 (if cond \<noteq> 0
 then IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_state_upd s
 else IMP_Minus_to_IMP_Minus_Minus_stack_aux3_state_upd s
   ))"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux4_state_upd_time t s \<equiv>
(let
  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s;
  t = t + 2;
  EQUAL_neq_zero_b' = 1;
  t = t + 2;
  EQUAL_neq_zero_ret' = 0;
  t = t + 2;
  EQUAL_neq_zero_state =
    \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
    EQUAL_neq_zero_b = EQUAL_neq_zero_b',
    EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  t = t + EQUAL_neq_zero_imp_time 0 EQUAL_neq_zero_state;
  cond = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;
  t = t + 2
in
 (if cond \<noteq> 0
 then (
  let
   t = t + 1;
   t = t + IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_state_upd_time 0 s
  in
   t)
 else
   (let
     t = t + 1;
     t = t + IMP_Minus_to_IMP_Minus_Minus_stack_aux3_state_upd_time 0 s
   in
    t)))"

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux4_imp_correct:
  "IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_aux4_state_upd s)
    = IMP_Minus_to_IMP_Minus_Minus_stack_aux4 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s)
    (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s) (IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s)"
  apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux4_state_upd_def IMP_Minus_to_IMP_Minus_Minus_stack_aux4_def)
  apply (simp add:EQUAL_neq_zero_imp_correct IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_imp_correct
  IMP_Minus_to_IMP_Minus_Minus_stack_aux3_imp_correct)
  done

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux4_IMP_Minus \<equiv>
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_a_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_c_str);;
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_b_str) ::= A (N 1);;
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str) ::= A (N 0);;
  invoke_subprogram EQUAL_neq_zero_prefix EQUAL_neq_zero_IMP_Minus;;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_cond ::= A (V (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str));;

  IF IMP_Minus_to_IMP_Minus_Minus_stack_aux_cond \<noteq>0
  THEN IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_IMP_Minus
  ELSE IMP_Minus_to_IMP_Minus_Minus_stack_aux3_IMP_Minus
  "

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux4_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_aux4_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_aux4_state_upd (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_aux4_state_upd_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux4_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule EQUAL_neq_zero_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {''ret''}"])
   subgoal premises p using p(6) by fastforce
   apply (erule  If_E)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_IMP_Minus_correct_function)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_aux3_IMP_Minus_correct_function)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
   done

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux4_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_aux4_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (IMP_Minus_to_IMP_Minus_Minus_stack_aux4_state_upd_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_aux4_state_upd_time_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux4_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule EQUAL_neq_zero_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {''ret''}"])
   subgoal premises p using p(11) by fastforce
   apply (erule  If_tE)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_one_IMP_Minus_correct_time)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_aux3_IMP_Minus_correct_time)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
   done

paragraph IMP_Minus_to_IMP_Minus_Minus_stack_aux5

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux5_state_upd s \<equiv>
(let
  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s;
  EQUAL_neq_zero_b' = 9;
  EQUAL_neq_zero_ret' = 0;
  EQUAL_neq_zero_state =
    \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
    EQUAL_neq_zero_b = EQUAL_neq_zero_b',
    EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  cond = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state
in
 (if cond \<noteq> 0
 then IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_state_upd s
 else IMP_Minus_to_IMP_Minus_Minus_stack_aux4_state_upd s
   ))"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux5_state_upd_time t s \<equiv>
(let
  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s;
  t = t + 2;
  EQUAL_neq_zero_b' = 9;
  t = t + 2;
  EQUAL_neq_zero_ret' = 0;
  t = t + 2;
  EQUAL_neq_zero_state =
    \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
    EQUAL_neq_zero_b = EQUAL_neq_zero_b',
    EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  t = t + EQUAL_neq_zero_imp_time 0 EQUAL_neq_zero_state;
  cond = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;
  t = t + 2
in
 (if cond \<noteq> 0
 then (
  let
   t = t + 1;
   t = t + IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_state_upd_time 0 s
  in
   t)
 else
   (let
     t = t + 1;
     t = t + IMP_Minus_to_IMP_Minus_Minus_stack_aux4_state_upd_time 0 s
   in
    t)))"

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux5_imp_correct:
  "IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_aux5_state_upd s)
    = IMP_Minus_to_IMP_Minus_Minus_stack_aux5
    (IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s) (IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s)
    (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s) (IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s)"
  apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux5_state_upd_def IMP_Minus_to_IMP_Minus_Minus_stack_aux5_def)
  apply (simp add:EQUAL_neq_zero_imp_correct IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_imp_correct
  IMP_Minus_to_IMP_Minus_Minus_stack_aux4_imp_correct)
  done

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux5_IMP_Minus \<equiv>
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_a_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_c_str);;
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_b_str) ::= A (N 9);;
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str) ::= A (N 0);;
  invoke_subprogram EQUAL_neq_zero_prefix EQUAL_neq_zero_IMP_Minus;;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_cond ::= A (V (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str));;

  IF IMP_Minus_to_IMP_Minus_Minus_stack_aux_cond \<noteq>0
  THEN IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_IMP_Minus
  ELSE IMP_Minus_to_IMP_Minus_Minus_stack_aux4_IMP_Minus
  "

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux5_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_aux5_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_aux5_state_upd (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_aux5_state_upd_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux5_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule EQUAL_neq_zero_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {''ret''}"])
   subgoal premises p using p(6) by fastforce
   apply (erule  If_E)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_IMP_Minus_correct_function)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_aux4_IMP_Minus_correct_function)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
   done

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux5_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_aux5_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (IMP_Minus_to_IMP_Minus_Minus_stack_aux5_state_upd_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_aux5_state_upd_time_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux5_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule EQUAL_neq_zero_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {''ret''}"])
   subgoal premises p using p(11) by fastforce
   apply (erule  If_tE)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_IMP_Minus_correct_time)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_aux4_IMP_Minus_correct_time)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
   done

paragraph IMP_Minus_to_IMP_Minus_Minus_stack_aux6

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux6_state_upd s \<equiv>
(let
  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s;
  EQUAL_neq_zero_b' = 7;
  EQUAL_neq_zero_ret' = 0;
  EQUAL_neq_zero_state =
    \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
    EQUAL_neq_zero_b = EQUAL_neq_zero_b',
    EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  cond = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state
in
 (if cond \<noteq> 0
 then IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_state_upd s
 else IMP_Minus_to_IMP_Minus_Minus_stack_aux5_state_upd s
   ))"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux6_state_upd_time t s \<equiv>
(let
  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s;
  t = t + 2;
  EQUAL_neq_zero_b' = 7;
  t = t + 2;
  EQUAL_neq_zero_ret' = 0;
  t = t + 2;
  EQUAL_neq_zero_state =
    \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
    EQUAL_neq_zero_b = EQUAL_neq_zero_b',
    EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  t = t + EQUAL_neq_zero_imp_time 0 EQUAL_neq_zero_state;
  cond = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;
  t = t + 2
in
 (if cond \<noteq> 0
 then (
  let
   t = t + 1;
   t = t + IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_state_upd_time 0 s
  in
   t)
 else
   (let
     t = t + 1;
     t = t + IMP_Minus_to_IMP_Minus_Minus_stack_aux5_state_upd_time 0 s
   in
    t)))"

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux6_imp_correct:
  "IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_aux6_state_upd s)
    = IMP_Minus_to_IMP_Minus_Minus_stack_aux6
    (IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s) (IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s)
    (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s) (IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s)"
  apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux6_state_upd_def IMP_Minus_to_IMP_Minus_Minus_stack_aux6_def)
  apply (simp add:EQUAL_neq_zero_imp_correct IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_imp_correct
  IMP_Minus_to_IMP_Minus_Minus_stack_aux5_imp_correct)
  done

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux6_IMP_Minus \<equiv>
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_a_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_c_str);;
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_b_str) ::= A (N 7);;
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str) ::= A (N 0);;
  invoke_subprogram EQUAL_neq_zero_prefix EQUAL_neq_zero_IMP_Minus;;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_cond ::= A (V (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str));;

  IF IMP_Minus_to_IMP_Minus_Minus_stack_aux_cond \<noteq>0
  THEN IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_IMP_Minus
  ELSE IMP_Minus_to_IMP_Minus_Minus_stack_aux5_IMP_Minus
  "

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux6_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_aux6_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_aux6_state_upd (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_aux6_state_upd_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux6_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule EQUAL_neq_zero_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {''ret''}"])
   subgoal premises p using p(6) by fastforce
   apply (erule  If_E)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_IMP_Minus_correct_function)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_aux5_IMP_Minus_correct_function)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
   done

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux6_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_aux6_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (IMP_Minus_to_IMP_Minus_Minus_stack_aux6_state_upd_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_aux6_state_upd_time_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux6_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule EQUAL_neq_zero_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {''ret''}"])
   subgoal premises p using p(11) by fastforce
   apply (erule  If_tE)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_seven_IMP_Minus_correct_time)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_aux5_IMP_Minus_correct_time)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
   done

paragraph IMP_Minus_to_IMP_Minus_Minus_stack_aux7

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux7_state_upd s \<equiv>
(let
  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s;
  EQUAL_neq_zero_b' = 6;
  EQUAL_neq_zero_ret' = 0;
  EQUAL_neq_zero_state =
    \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
    EQUAL_neq_zero_b = EQUAL_neq_zero_b',
    EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  cond = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state
in
 (if cond \<noteq> 0
 then IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_state_upd s
 else IMP_Minus_to_IMP_Minus_Minus_stack_aux6_state_upd s
   ))"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux7_state_upd_time t s \<equiv>
(let
  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s;
  t = t + 2;
  EQUAL_neq_zero_b' = 6;
  t = t + 2;
  EQUAL_neq_zero_ret' = 0;
  t = t + 2;
  EQUAL_neq_zero_state =
    \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
    EQUAL_neq_zero_b = EQUAL_neq_zero_b',
    EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  t = t + EQUAL_neq_zero_imp_time 0 EQUAL_neq_zero_state;
  cond = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;
  t = t + 2
in
 (if cond \<noteq> 0
 then (
  let
   t = t + 1;
   t = t + IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_state_upd_time 0 s
  in
   t)
 else
   (let
     t = t + 1;
     t = t + IMP_Minus_to_IMP_Minus_Minus_stack_aux6_state_upd_time 0 s
   in
    t)))"

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux7_imp_correct:
  "IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_aux7_state_upd s)
    = IMP_Minus_to_IMP_Minus_Minus_stack_aux7
    (IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s) (IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s)
    (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s) (IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s)"
  apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux7_state_upd_def IMP_Minus_to_IMP_Minus_Minus_stack_aux7_def)
  apply (simp add:EQUAL_neq_zero_imp_correct IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_imp_correct
  IMP_Minus_to_IMP_Minus_Minus_stack_aux6_imp_correct)
  done

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux7_IMP_Minus \<equiv>
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_a_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_c_str);;
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_b_str) ::= A (N 6);;
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str) ::= A (N 0);;
  invoke_subprogram EQUAL_neq_zero_prefix EQUAL_neq_zero_IMP_Minus;;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_cond ::= A (V (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str));;

  IF IMP_Minus_to_IMP_Minus_Minus_stack_aux_cond \<noteq>0
  THEN IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_IMP_Minus
  ELSE IMP_Minus_to_IMP_Minus_Minus_stack_aux6_IMP_Minus
  "

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux7_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_aux7_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_aux7_state_upd (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_aux7_state_upd_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux7_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule EQUAL_neq_zero_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {''ret''}"])
   subgoal premises p using p(6) by fastforce
   apply (erule  If_E)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_IMP_Minus_correct_function)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_aux6_IMP_Minus_correct_function)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
   done

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux7_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_aux7_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (IMP_Minus_to_IMP_Minus_Minus_stack_aux7_state_upd_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_aux7_state_upd_time_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux7_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule EQUAL_neq_zero_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {''ret''}"])
   subgoal premises p using p(11) by fastforce
   apply (erule  If_tE)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_six_IMP_Minus_correct_time)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_aux6_IMP_Minus_correct_time)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
   done

paragraph IMP_Minus_to_IMP_Minus_Minus_stack_aux8

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux8_state_upd s \<equiv>
(let
  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s;
  EQUAL_neq_zero_b' = 4;
  EQUAL_neq_zero_ret' = 0;
  EQUAL_neq_zero_state =
    \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
    EQUAL_neq_zero_b = EQUAL_neq_zero_b',
    EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  cond = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state
in
 (if cond \<noteq> 0
 then IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_state_upd s
 else IMP_Minus_to_IMP_Minus_Minus_stack_aux7_state_upd s
   ))"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux8_state_upd_time t s \<equiv>
(let
  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s;
  t = t + 2;
  EQUAL_neq_zero_b' = 4;
  t = t + 2;
  EQUAL_neq_zero_ret' = 0;
  t = t + 2;
  EQUAL_neq_zero_state =
    \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
    EQUAL_neq_zero_b = EQUAL_neq_zero_b',
    EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  t = t + EQUAL_neq_zero_imp_time 0 EQUAL_neq_zero_state;
  cond = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;
  t = t + 2
in
 (if cond \<noteq> 0
 then (
  let
   t = t + 1;
   t = t + IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_state_upd_time 0 s
  in
   t)
 else
   (let
     t = t + 1;
     t = t + IMP_Minus_to_IMP_Minus_Minus_stack_aux7_state_upd_time 0 s
   in
    t)))"

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux8_imp_correct:
  "IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_aux8_state_upd s)
    = IMP_Minus_to_IMP_Minus_Minus_stack_aux8
    (IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s) (IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s)
    (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s) (IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s)"
  apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux8_state_upd_def IMP_Minus_to_IMP_Minus_Minus_stack_aux8_def)
  apply (simp add:EQUAL_neq_zero_imp_correct IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_imp_correct
  IMP_Minus_to_IMP_Minus_Minus_stack_aux7_imp_correct)
  done

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux8_IMP_Minus \<equiv>
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_a_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_c_str);;
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_b_str) ::= A (N 4);;
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str) ::= A (N 0);;
  invoke_subprogram EQUAL_neq_zero_prefix EQUAL_neq_zero_IMP_Minus;;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_cond ::= A (V (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str));;

  IF IMP_Minus_to_IMP_Minus_Minus_stack_aux_cond \<noteq>0
  THEN IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_IMP_Minus
  ELSE IMP_Minus_to_IMP_Minus_Minus_stack_aux7_IMP_Minus
  "

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux8_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_aux8_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_aux8_state_upd (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_aux8_state_upd_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux8_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule EQUAL_neq_zero_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {''ret''}"])
   subgoal premises p using p(6) by fastforce
   apply (erule  If_E)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_IMP_Minus_correct_function)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_aux7_IMP_Minus_correct_function)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
   done

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux8_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_aux8_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (IMP_Minus_to_IMP_Minus_Minus_stack_aux8_state_upd_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_aux8_state_upd_time_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux8_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule EQUAL_neq_zero_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {''ret''}"])
   subgoal premises p using p(11) by fastforce
   apply (erule  If_tE)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_four_nine_IMP_Minus_correct_time)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_aux7_IMP_Minus_correct_time)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
   done

paragraph IMP_Minus_to_IMP_Minus_Minus_stack_aux9

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux9_state_upd s \<equiv>
(let
  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s;
  EQUAL_neq_zero_b' = 3;
  EQUAL_neq_zero_ret' = 0;
  EQUAL_neq_zero_state =
    \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
    EQUAL_neq_zero_b = EQUAL_neq_zero_b',
    EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  cond = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state
in
 (if cond \<noteq> 0
 then IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_state_upd s
 else IMP_Minus_to_IMP_Minus_Minus_stack_aux8_state_upd s
   ))"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux9_state_upd_time t s \<equiv>
(let
  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s;
  t = t + 2;
  EQUAL_neq_zero_b' = 3;
  t = t + 2;
  EQUAL_neq_zero_ret' = 0;
  t = t + 2;
  EQUAL_neq_zero_state =
    \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
    EQUAL_neq_zero_b = EQUAL_neq_zero_b',
    EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  t = t + EQUAL_neq_zero_imp_time 0 EQUAL_neq_zero_state;
  cond = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;
  t = t + 2
in
 (if cond \<noteq> 0
 then (
  let
   t = t + 1;
   t = t + IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_state_upd_time 0 s
  in
   t)
 else
   (let
     t = t + 1;
     t = t + IMP_Minus_to_IMP_Minus_Minus_stack_aux8_state_upd_time 0 s
   in
    t)))"

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux9_imp_correct:
  "IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_aux9_state_upd s)
    = IMP_Minus_to_IMP_Minus_Minus_stack_aux9
    (IMP_Minus_to_IMP_Minus_Minus_stack_aux_s s) (IMP_Minus_to_IMP_Minus_Minus_stack_aux_c s)
    (IMP_Minus_to_IMP_Minus_Minus_stack_aux_h s) (IMP_Minus_to_IMP_Minus_Minus_stack_aux_t s)"
  apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux9_state_upd_def IMP_Minus_to_IMP_Minus_Minus_stack_aux9_def)
  apply (simp add:EQUAL_neq_zero_imp_correct IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_imp_correct
  IMP_Minus_to_IMP_Minus_Minus_stack_aux8_imp_correct)
  done

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux9_IMP_Minus \<equiv>
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_a_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_aux_c_str);;
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_b_str) ::= A (N 3);;
  (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str) ::= A (N 0);;
  invoke_subprogram EQUAL_neq_zero_prefix EQUAL_neq_zero_IMP_Minus;;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_cond ::= A (V (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str));;

  IF IMP_Minus_to_IMP_Minus_Minus_stack_aux_cond \<noteq>0
  THEN IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_IMP_Minus
  ELSE IMP_Minus_to_IMP_Minus_Minus_stack_aux8_IMP_Minus
  "

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux9_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_aux9_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_aux9_state_upd (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_aux9_state_upd_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux9_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule EQUAL_neq_zero_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {''ret''}"])
   subgoal premises p using p(6) by fastforce
   apply (erule  If_E)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_IMP_Minus_correct_function)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_aux8_IMP_Minus_correct_function)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
   done

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux9_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_aux9_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (IMP_Minus_to_IMP_Minus_Minus_stack_aux9_state_upd_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state p s))"
   apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_aux9_state_upd_time_def)
   apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_aux9_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule EQUAL_neq_zero_IMP_Minus_correct[where vars="IMP_Minus_to_IMP_Minus_Minus_stack_aux_IMP_vars
     \<union> {''ret''}"])
   subgoal premises p using p(11) by fastforce
   apply (erule  If_tE)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_c_eq_three_IMP_Minus_correct_time)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
     subgoal
     apply (drule IMP_Minus_to_IMP_Minus_Minus_stack_aux8_IMP_Minus_correct_time)
     by (fastforce
       simp add: IMP_Minus_to_IMP_Minus_Minus_stack_aux_state_translators Let_def)
   done

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux9_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) IMP_Minus_to_IMP_Minus_Minus_stack_aux9_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (IMP_Minus_to_IMP_Minus_Minus_stack_aux9_state_upd_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str) =
          IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_aux9_state_upd
                                        (IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
   using IMP_Minus_to_IMP_Minus_Minus_stack_aux9_IMP_Minus_correct_function
   IMP_Minus_to_IMP_Minus_Minus_stack_aux9_IMP_Minus_correct_time
   by (meson com_add_prefix_valid_subset com_only_vars)

subsubsection IMP_Minus_to_IMP_Minus_Minus_stack_nat

paragraph IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition

record IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_state =
IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s::nat
IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c::nat
IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret::nat

abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_prefix
  \<equiv> ''IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition.''"
abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s_str \<equiv> ''s''"
abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c_str \<equiv> ''c''"
abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret_str \<equiv> ''ret''"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_state_upd s \<equiv>
(let

  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s s;
  EQUAL_neq_zero_b' = 0;
  EQUAL_neq_zero_ret' = 0;
  EQUAL_neq_zero_state = \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
  EQUAL_neq_zero_b = EQUAL_neq_zero_b',
  EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;

  LESS_neq_zero_a' = 10;
  LESS_neq_zero_b' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c s;
  LESS_neq_zero_ret' = 0;
  LESS_neq_zero_state = \<lparr>LESS_neq_zero_a = LESS_neq_zero_a',
  LESS_neq_zero_b = LESS_neq_zero_b',
  LESS_neq_zero_ret = LESS_neq_zero_ret'\<rparr>;
  LESS_neq_zero_ret_state = LESS_neq_zero_imp LESS_neq_zero_state;

  OR_neq_zero_a' = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;
  OR_neq_zero_b' = LESS_neq_zero_ret LESS_neq_zero_ret_state;
  OR_neq_zero_ret' = 0;
  OR_neq_zero_state = \<lparr>OR_neq_zero_a = OR_neq_zero_a',
  OR_neq_zero_b = OR_neq_zero_b',
  OR_neq_zero_ret = OR_neq_zero_ret'\<rparr>;
  OR_neq_zero_ret_state = OR_neq_zero_imp OR_neq_zero_state;

  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c s;
  EQUAL_neq_zero_b' = 0;
  EQUAL_neq_zero_ret' = 0;
  EQUAL_neq_zero_state = \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
  EQUAL_neq_zero_b = EQUAL_neq_zero_b',
  EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;

  OR_neq_zero_a' = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;
  OR_neq_zero_b' =  OR_neq_zero_ret OR_neq_zero_ret_state;
  OR_neq_zero_ret' = 0;
  OR_neq_zero_state = \<lparr>OR_neq_zero_a = OR_neq_zero_a',
  OR_neq_zero_b = OR_neq_zero_b',
  OR_neq_zero_ret = OR_neq_zero_ret'\<rparr>;
  OR_neq_zero_ret_state = OR_neq_zero_imp OR_neq_zero_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret' = OR_neq_zero_ret OR_neq_zero_ret_state;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c s,
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret'\<rparr>
  in
   ret
  )"

function IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp ::
  "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_state \<Rightarrow> IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_state" where
  "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp s =
  (let
      ret = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_state_upd s
    in
      ret
  )"
  by simp+
termination
  by (relation "measure IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s") simp

declare IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp.simps [simp del]

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_correct:
  "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp s)
  = (if (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s s) = 0
    \<or> (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c s = 0)
    \<or> (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c s > 10)
   then 1 else 0)"
apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp.simps
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_state_upd_def)
apply (simp add: hd_imp_correct EQUAL_neq_zero_imp_correct LESS_neq_zero_imp_correct Let_def)
by (simp add: OR_neq_zero_imp_correct)+

definition "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_state_upd_time t s \<equiv>
(let
  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s s;
  t = t + 2;
  EQUAL_neq_zero_b' = 0;
  t = t + 2;
  EQUAL_neq_zero_ret' = 0;
  t = t + 2;
  EQUAL_neq_zero_state = \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
  EQUAL_neq_zero_b = EQUAL_neq_zero_b',
  EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  t = t + EQUAL_neq_zero_imp_time 0 EQUAL_neq_zero_state;

  LESS_neq_zero_a' = 10;
  t = t + 2;
  LESS_neq_zero_b' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c s;
  t = t + 2;
  LESS_neq_zero_ret' = 0;
  t = t + 2;
  LESS_neq_zero_state = \<lparr>LESS_neq_zero_a = LESS_neq_zero_a',
  LESS_neq_zero_b = LESS_neq_zero_b',
  LESS_neq_zero_ret = LESS_neq_zero_ret'\<rparr>;
  LESS_neq_zero_ret_state = LESS_neq_zero_imp LESS_neq_zero_state;
  t = t + LESS_neq_zero_imp_time 0 LESS_neq_zero_state;

  OR_neq_zero_a' = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;
  t = t + 2;
  OR_neq_zero_b' = LESS_neq_zero_ret LESS_neq_zero_ret_state;
  t = t + 2;
  OR_neq_zero_ret' = 0;
  t = t + 2;
  OR_neq_zero_state = \<lparr>OR_neq_zero_a = OR_neq_zero_a',
  OR_neq_zero_b = OR_neq_zero_b',
  OR_neq_zero_ret = OR_neq_zero_ret'\<rparr>;
  OR_neq_zero_ret_state = OR_neq_zero_imp OR_neq_zero_state;
  t = t + OR_neq_zero_imp_time 0 OR_neq_zero_state;

  EQUAL_neq_zero_a' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c s;
  t = t + 2;
  EQUAL_neq_zero_b' = 0;
  t = t + 2;
  EQUAL_neq_zero_ret' = 0;
  t = t + 2;
  EQUAL_neq_zero_state = \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a',
  EQUAL_neq_zero_b = EQUAL_neq_zero_b',
  EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>;
  EQUAL_neq_zero_ret_state = EQUAL_neq_zero_imp EQUAL_neq_zero_state;
  t = t + EQUAL_neq_zero_imp_time 0 EQUAL_neq_zero_state;

  OR_neq_zero_a' = EQUAL_neq_zero_ret EQUAL_neq_zero_ret_state;
  t = t + 2;
  OR_neq_zero_b' =  OR_neq_zero_ret OR_neq_zero_ret_state;
  t = t + 2;
  OR_neq_zero_ret' = 0;
  t = t + 2;
  OR_neq_zero_state = \<lparr>OR_neq_zero_a = OR_neq_zero_a',
  OR_neq_zero_b = OR_neq_zero_b',
  OR_neq_zero_ret = OR_neq_zero_ret'\<rparr>;
  OR_neq_zero_ret_state = OR_neq_zero_imp OR_neq_zero_state;
  t = t + OR_neq_zero_imp_time 0 OR_neq_zero_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret' = OR_neq_zero_ret OR_neq_zero_ret_state;
  t = t + 2;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c s,
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret'\<rparr>
  in
   t
  )"

function IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time ::
  "nat \<Rightarrow> IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_state \<Rightarrow> nat" where
  "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time t s =
  (let
    t = t + IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_state_upd_time 0 s
  in
      t
  )"
  by auto
termination
  by (relation "measure (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s \<circ> snd)") simp

declare IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time.simps [simp del]

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time_acc:
  "(IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time (Suc t) s) = Suc (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time t s)"
  by (induction t s rule: IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time.induct)
    ((subst (1 2) IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time.simps);
      (simp add: IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_state_upd_def Let_def))

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time_acc_2_aux:
  "(IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time t s) = t + (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time_acc)+

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time t s) = t + (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time 0 s)"
  by (rule IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time_acc_2_aux)

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time_acc_3:
  "(IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time (a + b) s) = a + (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time_acc)+

definition IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_Minus where
  "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_Minus \<equiv>
(EQUAL_neq_zero_prefix @ EQUAL_neq_zero_a_str)
  ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s_str);;
(EQUAL_neq_zero_prefix @ EQUAL_neq_zero_b_str)
  ::= A (N 0);;
(EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str)
  ::= A (N 0);;
invoke_subprogram EQUAL_neq_zero_prefix EQUAL_neq_zero_IMP_Minus;;

(LESS_neq_zero_prefix @ LESS_neq_zero_a_str)
  ::= A (N 10);;
(LESS_neq_zero_prefix @ LESS_neq_zero_b_str)
  ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c_str);;
(LESS_neq_zero_prefix @ LESS_neq_zero_ret_str)
  ::= A (N 0);;
invoke_subprogram LESS_neq_zero_prefix LESS_neq_zero_IMP_Minus;;

(OR_neq_zero_prefix @ OR_neq_zero_a_str)
  ::= A (V (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str));;
(OR_neq_zero_prefix @ OR_neq_zero_b_str)
  ::= A (V (LESS_neq_zero_prefix @ LESS_neq_zero_ret_str));;
(OR_neq_zero_prefix @ OR_neq_zero_ret_str)
  ::= A (N 0);;
invoke_subprogram OR_neq_zero_prefix OR_neq_zero_IMP_Minus;;

(EQUAL_neq_zero_prefix @ EQUAL_neq_zero_a_str)
  ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c_str);;
(EQUAL_neq_zero_prefix @ EQUAL_neq_zero_b_str)
  ::= A (N 0);;
(EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str)
  ::= A (N 0);;
invoke_subprogram EQUAL_neq_zero_prefix EQUAL_neq_zero_IMP_Minus;;

(OR_neq_zero_prefix @ OR_neq_zero_a_str)
  ::= A (V (EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str));;
(OR_neq_zero_prefix @ OR_neq_zero_b_str)
  ::= A (V (OR_neq_zero_prefix @ OR_neq_zero_ret_str));;
(OR_neq_zero_prefix @ OR_neq_zero_ret_str)
  ::= A (N 0);;
invoke_subprogram OR_neq_zero_prefix OR_neq_zero_IMP_Minus;;
IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret_str
  ::= A (V (OR_neq_zero_prefix @ OR_neq_zero_ret_str))
"

abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_vars \<equiv>
  {IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s_str,
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c_str}"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_to_HOL_state p s =
  \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s
    = (s (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s_str)),
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c
   = (s (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c_str)),
   IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret
   = (s (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret_str))\<rparr>"

lemmas IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_state_translators =
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_to_HOL_state_def
  EQUAL_neq_zero_imp_to_HOL_state_def
  OR_neq_zero_imp_to_HOL_state_def
  LESS_neq_zero_imp_to_HOL_state_def

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_to_HOL_state p s))"
  apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp.simps)
  apply(simp only: IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule EQUAL_neq_zero_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_vars
    \<union> {(OR_neq_zero_prefix @ OR_neq_zero_ret_str)}"])
  subgoal premises p using p(21) by fastforce
  apply(erule OR_neq_zero_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_vars"])
  subgoal premises p using p(23) by fastforce
  apply(erule LESS_neq_zero_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_vars
    \<union> {(EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str)}"])
  subgoal premises p using p(25) by fastforce
  apply(erule EQUAL_neq_zero_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_vars"])
  subgoal premises p using p(27) by fastforce
  apply(erule OR_neq_zero_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_vars"])
  subgoal premises p using p(29) by fastforce
  by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_state_translators
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_state_upd_def Let_def)

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_pref) IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_to_HOL_state p s)"
  apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time.simps)
  apply(simp only: IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule EQUAL_neq_zero_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_vars
    \<union> {(OR_neq_zero_prefix @ OR_neq_zero_ret_str)}"])
  subgoal premises p using p(41) by fastforce
  apply(erule OR_neq_zero_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_vars"])
  subgoal premises p using p(43) by fastforce
  apply(erule LESS_neq_zero_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_vars
    \<union> {(EQUAL_neq_zero_prefix @ EQUAL_neq_zero_ret_str)}"])
  subgoal premises p using p(45) by fastforce
  apply(erule EQUAL_neq_zero_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_vars"])
  subgoal premises p using p(47) by fastforce
  apply(erule OR_neq_zero_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_vars"])
  subgoal premises p using p(49) by fastforce
  by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_state_translators
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_state_upd_time_def Let_def)

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret_str) =
          IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp
                                        (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_Minus_correct_function
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_Minus_correct_time
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_Minus_correct_effects
  by (meson set_mono_prefix)

record IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_state=
IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s::nat
IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret::nat

abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_prefix \<equiv> ''IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux.''"
abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s_str \<equiv> ''s''"
abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret_str \<equiv> ''ret''"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_state_upd s \<equiv>
(let
  hd_xs' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s s;
  hd_ret' = 0;
  hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
  hd_ret_state = hd_imp hd_state;

  hd_xs' = hd_ret hd_ret_state;
  hd_ret' = 0;
  hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
  hd_ret_state = hd_imp hd_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s s;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c' = hd_ret hd_ret_state;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret' = 0;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_state
    = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s',
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c',
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret'\<rparr>;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret_state
    = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_state;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret'
    = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret_state;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret'\<rparr>
in
 ret)"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_state_upd_time t s \<equiv>
(let
  hd_xs' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s s;
  t = t + 2;
  hd_ret' = 0;
  t = t + 2;
  hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
  hd_ret_state = hd_imp hd_state;
  t = t + hd_imp_time 0 hd_state;

  hd_xs' = hd_ret hd_ret_state;
  t = t + 2;
  hd_ret' = 0;
  t = t + 2;
  hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
  hd_ret_state = hd_imp hd_state;
  t = t + hd_imp_time 0 hd_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s s;
  t = t + 2;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c' = hd_ret hd_ret_state;
  t = t + 2;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret' = 0;
  t = t + 2;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_state
    = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s',
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c',
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret'\<rparr>;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret_state
    = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_state;
  t = t + IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_time 0 IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_state;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret'
    = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret_state;
  t = t + 2;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret'\<rparr>
in
  t)"

function IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp ::
  "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_state \<Rightarrow> IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_state" where
  "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp s =
  (let
      ret = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_state_upd s
    in
      ret
  )"
  by simp+
termination
  by (relation "measure IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s") simp

declare IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp.simps [simp del]

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_correct[let_function_correctness]:
  "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp s) =
    (if (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s s) = 0
    \<or> (hd_nat (hd_nat (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s s))) = 0
    \<or> (hd_nat (hd_nat (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s s))) > 10
   then 1 else 0)"
  apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp.simps Let_def IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_state_upd_def)
  apply (simp add: hd_imp_correct IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_correct)
  done

function IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time ::
  "nat \<Rightarrow> IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_state \<Rightarrow> nat" where
  "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time t s =
  (let
   t = t + IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_state_upd_time 0 s
  in
      t
  )"
  by auto
termination
  by (relation "measure (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s \<circ> snd)") simp

declare IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time.simps [simp del]

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time_acc:
  "(IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time (Suc t) s) = Suc (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time t s)"
  by (induction t s rule: IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time.induct)
    ((subst (1 2) IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time.simps);
      (simp add: IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_state_upd_def Let_def))

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time_acc_2_aux:
  "(IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time t s) = t + (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time_acc)+

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time t s) = t + (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time 0 s)"
  by (rule IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time_acc_2_aux)

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time_acc_3:
  "(IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time (a + b) s) = a + (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time_acc)+

definition IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus where
  "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus \<equiv>
  (hd_prefix @ hd_xs_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s_str);;
  (hd_prefix @ hd_ret_str) ::= A (N 0);;
  invoke_subprogram hd_prefix hd_IMP_Minus;;

  (hd_prefix @ hd_xs_str) ::= A (V (hd_prefix @ hd_ret_str));;
  (hd_prefix @ hd_ret_str) ::= A (N 0);;
  invoke_subprogram hd_prefix hd_IMP_Minus;;

  (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_s_str)
    ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s_str);;
  (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_c_str)
    ::= A (V (hd_prefix @ hd_ret_str));;
  (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret_str)
    ::= A (N 0);;
  invoke_subprogram IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_prefix IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_Minus;;

  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret_str
    ::= A (V (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_ret_str))
"

abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_vars \<equiv>
  {IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s_str}"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_to_HOL_state p s =
  \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s = (s (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s_str)),
   IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret = (s (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret_str))\<rparr>"

lemmas IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_state_translators =
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_to_HOL_state_def
  hd_imp_to_HOL_state_def
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_imp_to_HOL_state_def

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_to_HOL_state p s))"
  apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp.simps)
  apply(simp only: IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule hd_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_vars"])
  subgoal premises p using p(11) by fastforce
  apply(erule hd_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_vars"])
  subgoal premises p using p(13) by fastforce
  apply(erule IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_vars"])
  subgoal premises p using p(15) by fastforce
  by(fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_state_translators
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_state_upd_def)

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_pref) IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_to_HOL_state p s)"
  apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time.simps)
  apply(simp only: IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule hd_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_vars"])
  subgoal premises p using p(21) by fastforce
  apply(erule hd_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_vars"])
  subgoal premises p using p(23) by fastforce
  apply(erule IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_vars"])
  subgoal premises p using p(25) by fastforce
  by(fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_state_translators
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_state_upd_time_def Let_def)

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret_str) =
          IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp
                                        (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus_correct_function
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus_correct_time
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus_correct_effects
  by (meson set_mono_prefix)

paragraph "loop body"
record IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_state =
 IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s::nat
 IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret::nat

abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_prefix \<equiv> ''IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_state.''"
abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s_str \<equiv> ''s''"
abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret_str \<equiv> ''ret''"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_state_upd s \<equiv>
(let
  hd_xs' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s s;
  hd_ret' = 0;
  hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
  hd_ret_state = hd_imp hd_state;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_h' = hd_ret hd_ret_state;

  hd_xs' = hd_ret hd_ret_state;
  hd_ret' = 0;
  hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
  hd_ret_state = hd_imp hd_state;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_c' = hd_ret hd_ret_state;

  tl_xs' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s s;
  tl_ret' = 0;
  tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
  tl_ret_state = tl_imp tl_state;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_t' = tl_ret tl_ret_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret' = 0;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_s' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s s;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_state =
    \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c',
    IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h',
    IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t',
    IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s',
    IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_state
    = IMP_Minus_to_IMP_Minus_Minus_stack_aux9_state_upd IMP_Minus_to_IMP_Minus_Minus_stack_aux_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret'
    = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_state;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s = IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret = IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret'\<rparr>
in
 ret)"

function IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp ::
  "IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_state \<Rightarrow> IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_state" where
  "IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp s =
  (let
      ret = IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_state_upd s
    in
      ret
  )"
  by simp+
termination
  by (relation "measure IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s") simp

declare IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp.simps [simp del]

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_correct[let_function_correctness]:
  "IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret (IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp s) =
    IMP_Minus_to_IMP_Minus_Minus_stack_aux9
    (IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s s) (hd_nat (hd_nat (IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s s)))
    (hd_nat (IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s s)) (tl_nat (IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s s))
    "
  apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp.simps Let_def IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_state_upd_def)
  apply (simp add: hd_imp_correct tl_imp_correct IMP_Minus_to_IMP_Minus_Minus_stack_aux9_imp_correct )
  done

function IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time ::
  "nat \<Rightarrow> IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_state \<Rightarrow> nat" where
  "IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time t s =
  (let
  hd_xs' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s s;
  t = t + 2;
  hd_ret' = 0;
  t = t + 2;
  hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
  hd_ret_state = hd_imp hd_state;
  t = t + hd_imp_time 0 hd_state;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_h' = hd_ret hd_ret_state;
  t = t + 2;

  hd_xs' = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h';
  t = t + 2;
  hd_ret' = 0;
  t = t + 2;
  hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
  hd_ret_state = hd_imp hd_state;
  t = t + hd_imp_time 0 hd_state;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_c' = hd_ret hd_ret_state;
  t = t + 2;

  tl_xs' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s s;
  t = t + 2;
  tl_ret' = 0;
  t = t + 2;
  tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
  tl_ret_state = tl_imp tl_state;
  t = t + tl_imp_time 0 tl_state;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_t' = tl_ret tl_ret_state;
  t = t + 2;

  IMP_Minus_to_IMP_Minus_Minus_stack_aux_s' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s s;
  t = t + 2;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret' = 0;
  t = t + 2;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_state =
    \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_aux_c = IMP_Minus_to_IMP_Minus_Minus_stack_aux_c',
    IMP_Minus_to_IMP_Minus_Minus_stack_aux_h = IMP_Minus_to_IMP_Minus_Minus_stack_aux_h',
    IMP_Minus_to_IMP_Minus_Minus_stack_aux_t = IMP_Minus_to_IMP_Minus_Minus_stack_aux_t',
    IMP_Minus_to_IMP_Minus_Minus_stack_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_aux_s',
    IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret'\<rparr>;
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_state
    = IMP_Minus_to_IMP_Minus_Minus_stack_aux9_state_upd IMP_Minus_to_IMP_Minus_Minus_stack_aux_state;
  t = t + IMP_Minus_to_IMP_Minus_Minus_stack_aux9_state_upd_time 0 IMP_Minus_to_IMP_Minus_Minus_stack_aux_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret'
    = IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_state;
  t = t + 2;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s = IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret = IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret'\<rparr>
  in
      t
  )"
  by auto
termination
  by (relation "measure (IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s \<circ> snd)") simp

declare IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time.simps [simp del]

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time_acc:
  "(IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time (Suc t) s) = Suc (IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time t s)"
  by (induction t s rule: IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time.induct)
    ((subst (1 2) IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time.simps);
      (simp add: IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_state_upd_def Let_def))

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time_acc_2_aux:
  "(IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time t s) = t + (IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time_acc)+

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time t s) = t + (IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time 0 s)"
  by (rule IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time_acc_2_aux)

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time_acc_3:
  "(IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time (a + b) s) = a + (IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time_acc)+

definition IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_Minus where
  "IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_Minus \<equiv>
  (hd_prefix @ hd_xs_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s_str);;
  (hd_prefix @ hd_ret_str) ::= A (N 0);;
  invoke_subprogram hd_prefix hd_IMP_Minus;;
  (IMP_Minus_to_IMP_Minus_Minus_stack_aux_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str)
    ::= A (V (hd_prefix @ hd_ret_str));;

  (hd_prefix @ hd_xs_str) ::= A (V (hd_prefix @ hd_ret_str));;
  (hd_prefix @ hd_ret_str) ::= A (N 0);;
  invoke_subprogram hd_prefix hd_IMP_Minus;;
  (IMP_Minus_to_IMP_Minus_Minus_stack_aux_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_aux_c_str)
    ::= A (V (hd_prefix @ hd_ret_str));;

  (tl_prefix @ tl_xs_str) ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s_str);;
  (tl_prefix @ tl_ret_str) ::= A (N 0);;
  invoke_subprogram tl_prefix tl_IMP_Minus;;

  (IMP_Minus_to_IMP_Minus_Minus_stack_aux_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_aux_t_str)
    ::= A (V (tl_prefix @ tl_ret_str));;
  (IMP_Minus_to_IMP_Minus_Minus_stack_aux_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_aux_s_str)
    ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s_str);;
  (IMP_Minus_to_IMP_Minus_Minus_stack_aux_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str)
    ::= A (N 0);;
  invoke_subprogram IMP_Minus_to_IMP_Minus_Minus_stack_aux_prefix
    IMP_Minus_to_IMP_Minus_Minus_stack_aux9_IMP_Minus;;

  IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret_str
    ::= A (V (IMP_Minus_to_IMP_Minus_Minus_stack_aux_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_aux_ret_str))
"

abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_vars \<equiv>
  {IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s_str}"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_to_HOL_state p s =
  \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s = (s (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s_str)),
   IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret = (s (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret_str))\<rparr>"

lemmas IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_state_translators =
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_to_HOL_state_def
  hd_imp_to_HOL_state_def
  tl_imp_to_HOL_state_def
  IMP_Minus_to_IMP_Minus_Minus_stack_aux_imp_to_HOL_state_def

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_Minus_correct_function:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp (IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_to_HOL_state p s))"
  apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp.simps)
  apply(simp only: IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule hd_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_vars
    \<union> {(IMP_Minus_to_IMP_Minus_Minus_stack_aux_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str)}"])
  subgoal premises p using p(16) by fastforce
  apply(erule hd_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_vars"])
  subgoal premises p using p(18) by fastforce
  apply(erule tl_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_vars
    \<union> {(IMP_Minus_to_IMP_Minus_Minus_stack_aux_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str),
    (IMP_Minus_to_IMP_Minus_Minus_stack_aux_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_aux_c_str) }"])
  subgoal premises p using p(20) by fastforce
  apply(erule IMP_Minus_to_IMP_Minus_Minus_stack_aux9_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_vars"])
  subgoal premises p using p(22) by fastforce
  apply (clarsimp simp: IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_state_translators
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_state_upd_def Let_def)
  subgoal premises p
    using
    p(2)[of "(IMP_Minus_to_IMP_Minus_Minus_stack_aux_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str)", symmetric]
    p(6)[of "(IMP_Minus_to_IMP_Minus_Minus_stack_aux_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str)", symmetric]
    p(6)[of "(IMP_Minus_to_IMP_Minus_Minus_stack_aux_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_aux_c_str)", symmetric]
    apply simp
    unfolding p(8)[symmetric] p(4)
      using p(6)[of IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s_str, symmetric]
            p(2)[of IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s_str, symmetric]
    by simp
  done


lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_pref) IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_Minus_correct_time:
  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_to_HOL_state p s)"
  apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time.simps)
  apply(simp only: IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule hd_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_vars
    \<union> {(IMP_Minus_to_IMP_Minus_Minus_stack_aux_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str)}"])
  subgoal premises p using p(31) by fastforce
  apply(erule hd_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_vars"])
  subgoal premises p using p(33) by fastforce
  apply(erule tl_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_vars
    \<union> {(IMP_Minus_to_IMP_Minus_Minus_stack_aux_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str),
    (IMP_Minus_to_IMP_Minus_Minus_stack_aux_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_aux_c_str) }"])
  subgoal premises p using p(35) by fastforce
  apply(erule IMP_Minus_to_IMP_Minus_Minus_stack_aux9_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_vars"])
  subgoal premises p using p(37) by fastforce
  apply (clarsimp simp add: IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_state_translators
    Let_def)
  subgoal premises p
    using
    p(3)[of "(IMP_Minus_to_IMP_Minus_Minus_stack_aux_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str)"]
    p(7)[of "(IMP_Minus_to_IMP_Minus_Minus_stack_aux_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_aux_h_str)"]
    p(7)[of "(IMP_Minus_to_IMP_Minus_Minus_stack_aux_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_aux_c_str)"]
    apply simp
    unfolding p(5) p(9)[symmetric]
    using
    p(7)[of IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s_str, symmetric]
    p(3)[of IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s_str, symmetric]
    by simp
  done


lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret_str) =
          IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret (IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp
                                        (IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_Minus_correct_function
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_Minus_correct_time
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_Minus_correct_effects
  by (meson set_mono_prefix)

paragraph "the main function"

record IMP_Minus_to_IMP_Minus_Minus_stack_nat_state =
IMP_Minus_to_IMP_Minus_Minus_stack_nat_s::nat
IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret::nat

abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_nat_prefix \<equiv> ''IMP_Minus_to_IMP_Minus_Minus_stack_nat.''"
abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_nat_s_str \<equiv> ''s''"
abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret_str \<equiv> ''ret''"
abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_nat_while_cond \<equiv> ''cond''"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_nat_state_upd s \<equiv>
(let
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_s s;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret' = 0;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_state =
    \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s = IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s',
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret = IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret'\<rparr>;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret_state
    = IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_nat_s'
    = IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret_state;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_s = IMP_Minus_to_IMP_Minus_Minus_stack_nat_s',
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret = IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret s\<rparr>
in
 ret)"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_compute_loop_condition s \<equiv>
(let
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_s s;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret' = 0;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_state
    = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s',
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret'\<rparr>;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret_state
    = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_state;
  cond = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret_state
  in
   cond
  )"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_after_loop s \<equiv>
  (let
  IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_s s;
  IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret' = 0;
  IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_state =
    \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s = IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s',
    IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret = IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret'\<rparr>;
  IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret_state =
    IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_state;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret' =
    IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret_state;

  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_s = IMP_Minus_to_IMP_Minus_Minus_stack_nat_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret = IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret'\<rparr>
  in
   ret)
  "

function (domintros) IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp
  :: "IMP_Minus_to_IMP_Minus_Minus_stack_nat_state \<Rightarrow> IMP_Minus_to_IMP_Minus_Minus_stack_nat_state" where
"IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp s =
  (if IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_compute_loop_condition s \<noteq> 0
  then
    let next_iteration = IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp (IMP_Minus_to_IMP_Minus_Minus_stack_nat_state_upd s)
    in next_iteration
  else
    let ret = IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_after_loop s
    in ret)"
 by simp+

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_term:
  "IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_dom
    \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_s = IMPm_IMPmm_list_encode c,
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret = 0\<rparr>"
 apply (induction c rule: IMP_Minus_to_IMP_Minus_Minus_stack.induct)
 sorry


(*TODO: the partial termination of the imp function, should be resolved by
a similar induction as the functional implementation*)

lemmas IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_simps
  = IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp.psimps[OF IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_term]

lemmas IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_induct
  = IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp.pinduct[OF IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_term]

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_correct:
assumes "s = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_s = IMPm_IMPmm_list_encode c,
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret = 0\<rparr>"
shows  "IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret (IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp s)
    = IMP_Minus_to_IMP_Minus_Minus_stack_nat (IMP_Minus_to_IMP_Minus_Minus_stack_nat_s s)"
sorry

thm IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp.pinduct[OF IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_term]

lemmas IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_subprogram_simps =
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_state_upd_def
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_compute_loop_condition_def
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_after_loop_def

abbreviation "IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_vars \<equiv>
{IMP_Minus_to_IMP_Minus_Minus_stack_nat_s_str,
IMP_Minus_to_IMP_Minus_Minus_stack_nat_while_cond,
IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret_str}"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_to_HOL_state p s \<equiv>
  \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_s = s (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_nat_s_str),
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret = s  (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret_str)\<rparr>"

lemmas IMP_Minus_to_IMP_Minus_Minus_stack_nat_state_compute_loop_condition_state_translators=
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_to_HOL_state_def
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_to_HOL_state_def
  IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_to_HOL_state_def

definition "IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_init_while_cond \<equiv>
(IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s_str)
  ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_nat_s_str);;
(IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret_str)
  ::= A (N 0);;
invoke_subprogram IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_prefix IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus;;

IMP_Minus_to_IMP_Minus_Minus_stack_nat_while_cond
  ::= A (V (IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret_str))
"

lemmas IMP_Minus_to_IMP_Minus_Minus_stack_nat_state_loop_body_state_translators=
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_to_HOL_state_def
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_to_HOL_state_def
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_to_HOL_state_def

definition "IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_loop_body \<equiv>
(IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s_str)
  ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_nat_s_str);;
(IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret_str)
  ::= A (N 0);;
invoke_subprogram IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_prefix IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_Minus;;

IMP_Minus_to_IMP_Minus_Minus_stack_nat_s_str
  ::= A (V (IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret_str))
"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_after_loop \<equiv>
(IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s_str)
  ::= A (V IMP_Minus_to_IMP_Minus_Minus_stack_nat_s_str);;
(IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret_str)
  ::= A (N 0);;
invoke_subprogram IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_prefix IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_Minus;;

IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret_str
  ::= A (V (IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_prefix @ IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret_str))
"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_nat_state_upd_time t s \<equiv>
  (let
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_s s;
  t = t + 2;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret' = 0;
  t = t + 2;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_state =
    \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s = IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_s',
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret = IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret'\<rparr>;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret_state
    = IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_state;
  t = t + IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_imp_time 0 IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_state;

  IMP_Minus_to_IMP_Minus_Minus_stack_nat_s'
    = IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_ret_state;
  t = t + 2;
  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_s = IMP_Minus_to_IMP_Minus_Minus_stack_nat_s',
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret = IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret s\<rparr>
  in
    t)
"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_compute_loop_condition_time t s \<equiv>
  (let
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_s s;
  t = t + 2;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret' = 0;
  t = t + 2;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_state
    = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_s',
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret'\<rparr>;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret_state
    = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_state;
  t = t + IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_imp_time 0 IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_state;
  cond = IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_ret_state;
  t = t + 2
  in
    t)
"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_after_loop_time t s \<equiv>
  (let
  IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s' = IMP_Minus_to_IMP_Minus_Minus_stack_nat_s s;
  t = t + 2;
  IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret' = 0;
  t = t + 2;
  IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_state =
    \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s = IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_s',
    IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret = IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret'\<rparr>;
  IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret_state =
    IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_state;
  t = t + IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_imp_time 0 IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_state;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret' =
    IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_ret_state;
  t = t + 2;

  ret = \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_s = IMP_Minus_to_IMP_Minus_Minus_stack_nat_s s,
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret = IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret'\<rparr>
  in
    t)
"

lemmas IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_subprogram_time_simps =
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_state_upd_time_def
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_compute_loop_condition_time_def
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_after_loop_time_def
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_subprogram_simps

function (domintros) IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time::
  "nat \<Rightarrow> IMP_Minus_to_IMP_Minus_Minus_stack_nat_state \<Rightarrow> nat" where
  "IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time t s =
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_compute_loop_condition_time 0 s +
  (if IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_compute_loop_condition s \<noteq> 0
    then
      (let
        t = t + 1;
        next_iteration =
          IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time (t + IMP_Minus_to_IMP_Minus_Minus_stack_nat_state_upd_time 0 s)
                         (IMP_Minus_to_IMP_Minus_Minus_stack_nat_state_upd s)
       in next_iteration)
    else
      (let
        t = t + 2;
        ret = t + IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_after_loop_time 0 s
       in ret)
  )"
  by auto

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time_term:
  "IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time_dom
    (t, \<lparr>IMP_Minus_to_IMP_Minus_Minus_stack_nat_s = IMPm_IMPmm_list_encode c,
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret = 0\<rparr>)"
 apply (induction c rule: IMP_Minus_to_IMP_Minus_Minus_stack.induct)
 sorry


(*TODO: the partial termination of the imp function, should be resolved by
a similar induction as the functional implementation*)

lemmas IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time_simps
  = IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time.psimps[OF IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time_term]

lemmas IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time_induct
  = IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time.pinduct[OF IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time_term]

(*
lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time_acc:
  "(IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time (Suc t) s) = Suc (IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time t s)"
  by (induction t s rule: IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time_induct)
    ((subst (1 2) IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time_simps);
      (simp add: IMP_Minus_to_IMP_Minus_Minus_stack_nat_state_upd_def))

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time_acc_2_aux:
  "(IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time t s) = t + (IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time_acc)+

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time t s) = t + (IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time 0 s)"
  by (rule IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time_acc_2_aux)

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time_acc_3:
  "(IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time (a + b) s) = a + (IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time_acc)+

*)

definition IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_Minus where
  "IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_Minus \<equiv>
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_init_while_cond;;
  WHILE IMP_Minus_to_IMP_Minus_Minus_stack_nat_while_cond \<noteq>0 DO (
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_loop_body;;
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_init_while_cond
  );;
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_after_loop"

lemmas IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_subprogram_simps =
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_init_while_cond_def
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_loop_body_def
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_after_loop_def


lemmas IMP_Minus_to_IMP_Minus_Minus_stack_nat_complete_simps =
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_subprogram_simps
  IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_subprogram_simps

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_Minus_correct_function:
  "IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_dom (IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_to_HOL_state p s)
     \<Longrightarrow> (invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s'
     \<Longrightarrow>
     s' (add_prefix p IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret_str)
      = IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret
          (IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp (IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_to_HOL_state p s))"
  apply(induction "IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_to_HOL_state p s" arbitrary: s s' t
    rule: IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp.pinduct)
  apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp.psimps)
  apply(simp only: IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_Minus_def prefix_simps)+
  apply(erule Seq_E)+
  apply(erule While_tE)

  subgoal
    apply(simp only: IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_subprogram_simps prefix_simps)
    apply(erule Seq_E)+
    apply(erule IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_vars"])
    subgoal premises p using p(13) by fastforce
    apply(erule IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_vars"])
    subgoal premises p using p(15) by fastforce
    by (fastforce simp:  IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_subprogram_simps
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_state_compute_loop_condition_state_translators)


  apply(erule Seq_E)+
  apply(dest_com_gen)

  subgoal
      apply(simp only: IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_init_while_cond_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_vars"])
      subgoal premises p using p(13) by fastforce
      apply(erule IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_vars"])
      subgoal premises p using p(15) by fastforce
      by (fastforce simp:  IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_subprogram_simps
    IMP_Minus_to_IMP_Minus_Minus_stack_nat_state_compute_loop_condition_state_translators Let_def)

  subgoal
      apply(subst (asm) IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_init_while_cond_def)
      apply(simp only: IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_loop_body_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_vars"])
      subgoal premises p using p(13) by fastforce
      apply (erule IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_Minus_correct[where vars = IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_vars])
      subgoal premises p using p(15) by fastforce
      by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_subprogram_simps
      IMP_Minus_to_IMP_Minus_Minus_stack_nat_state_loop_body_state_translators Let_def)


  subgoal
      apply(simp only: IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_init_while_cond_def prefix_simps
          IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_loop_body_def)
      apply(erule Seq_E)+
      apply(erule IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_vars"])
      subgoal premises p using p(16) by fastforce
      apply (erule IMP_Minus_to_IMP_Minus_Minus_stack_nat_body_IMP_Minus_correct[where vars = IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_vars])
      subgoal premises p using p(18) by fastforce
      by (fastforce simp: IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_subprogram_simps
      IMP_Minus_to_IMP_Minus_Minus_stack_nat_state_loop_body_state_translators Let_def)
  done

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ IMP_Minus_to_IMP_Minus_Minus_stack_nat_pref) IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix IMP_Minus_to_IMP_Minus_Minus_stack_nat_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

thm IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time_induct

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_Minus_correct_time:
assumes dom: "IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time_dom (0::nat, (IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_to_HOL_state p s))"
shows  "(invoke_subprogram p IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_to_HOL_state p s)"
using dom apply (induction "IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_to_HOL_state p s" arbitrary: s s' t
      rule: IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time.pinduct)
  apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time.psimps)
  apply(simp only: IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_Minus_def prefix_simps)+

  apply(erule Seq_tE)+
  apply(erule While_tE_time)

  subgoal
    apply(simp only: IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_subprogram_simps prefix_simps)
    apply(erule Seq_tE)+
     apply(erule IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_vars"])
    subgoal premises p using p(21) by fastforce
    apply(erule IMP_Minus_to_IMP_Minus_Minus_stack_nat_condition_aux_IMP_Minus_correct[where vars = "IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_vars"])
    subgoal premises p using p(23) by fastforce
    sorry

  apply(erule Seq_tE)+
  apply(simp add: add.assoc)
sorry

(*
"apply (dest_com_gen_time)" fails here
*)

lemma IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_time 0 (IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret_str) =
          IMP_Minus_to_IMP_Minus_Minus_stack_nat_ret (IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp
                                        (IMP_Minus_to_IMP_Minus_Minus_stack_nat_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using IMP_Minus_to_IMP_Minus_Minus_stack_nat_IMP_Minus_correct_function
  sorry


end