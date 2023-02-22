\<^marker>\<open>creator Alexander Taepper\<close>

theory IMP_Minus_To_IMP_Minus_Minus_IMP
  imports
    Primitives_IMP_Minus
    Binary_Arithmetic_IMP
    IMP_Minus_To_IMP_Minus_Minus_State_Translations_IMP
    IMP_Minus_To_IMP_Minus_Minus_nat
    IMP_Minus.Com
begin


unbundle IMP_Minus_Minus_Com.no_com_syntax


subsection \<open>Useful Definitions and Lemmas\<close>


subsection \<open>map_var_bit_to_var\<close>

subsubsection \<open>map_var_bit_to_var_aux\<close>

fun map_var_bit_to_var_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_var_bit_to_var_aux acc v n = ((var_bit_to_var_nat (prod_encode (v,hd_nat n)))## acc)"

record map_var_bit_to_var_aux_state =
  map_var_bit_to_var_aux_acc::nat
  map_var_bit_to_var_aux_v::nat
  map_var_bit_to_var_aux_n::nat
  map_var_bit_to_var_aux_ret::nat

abbreviation "map_var_bit_to_var_aux_prefix \<equiv> ''map_var_bit_to_var_aux.''"
abbreviation "map_var_bit_to_var_aux_acc_str \<equiv> ''acc''"
abbreviation "map_var_bit_to_var_aux_v_str \<equiv> ''v''"
abbreviation "map_var_bit_to_var_aux_n_str \<equiv> ''n''"
abbreviation "map_var_bit_to_var_aux_ret_str \<equiv> ''ret''"


function map_var_bit_to_var_aux_imp :: "map_var_bit_to_var_aux_state \<Rightarrow> map_var_bit_to_var_aux_state" where 
"map_var_bit_to_var_aux_imp s = 
(let
    hd_xs' = map_var_bit_to_var_aux_n s;
    hd_ret' = 0;
    hd_state = \<lparr>hd_xs = hd_xs',
                hd_ret = hd_ret'\<rparr>;
    hd_ret_state = hd_imp hd_state;

    prod_encode_a' = map_var_bit_to_var_aux_v s;
    prod_encode_b' = hd_ret hd_ret_state;
    prod_encode_ret' = 0;
    prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                         prod_encode_b = prod_encode_b',
                         prod_encode_ret = prod_encode_ret'\<rparr>;
    prod_encode_ret_state = prod_encode_imp prod_encode_state;

    var_bit_to_var_nat_n' = prod_encode_ret prod_encode_ret_state;
    var_bit_to_var_nat_ret' = 0;
    var_bit_to_var_nat_state = \<lparr>var_bit_to_var_nat_n = var_bit_to_var_nat_n',
                                var_bit_to_var_nat_ret = var_bit_to_var_nat_ret'\<rparr>;
    var_bit_to_var_nat_ret_state = var_bit_to_var_nat_imp var_bit_to_var_nat_state;

    cons_h' = var_bit_to_var_nat_ret var_bit_to_var_nat_ret_state;
    cons_t' = map_var_bit_to_var_aux_acc s;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h',
                  cons_t = cons_t', 
                  cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    map_var_bit_to_var_aux_ret' = cons_ret cons_ret_state;
    
    tl_xs' = map_var_bit_to_var_aux_n s;
    tl_ret' = 0;
    tl_state = \<lparr>tl_xs = tl_xs', 
                tl_ret = tl_ret'\<rparr>;
    tl_ret_state = tl_imp tl_state;

    map_var_bit_to_var_aux_n' = tl_ret tl_ret_state;
    ret = \<lparr>map_var_bit_to_var_aux_acc = map_var_bit_to_var_aux_acc s,
          map_var_bit_to_var_aux_v = map_var_bit_to_var_aux_v s,
          map_var_bit_to_var_aux_n = map_var_bit_to_var_aux_n',
          map_var_bit_to_var_aux_ret = map_var_bit_to_var_aux_ret'\<rparr>
    in
     ret)
    " by simp+
    termination
    apply (relation "measure map_var_bit_to_var_aux_acc")
    apply simp 
    done 

declare map_var_bit_to_var_aux_imp.simps[simp del]

lemma map_var_bit_to_var_aux_imp_correct[let_function_correctness]:
"map_var_bit_to_var_aux_ret (map_var_bit_to_var_aux_imp s) = 
  map_var_bit_to_var_aux (map_var_bit_to_var_aux_acc s) (map_var_bit_to_var_aux_v s) (map_var_bit_to_var_aux_n s)
  \<and> map_var_bit_to_var_aux_n (map_var_bit_to_var_aux_imp s) = tl_nat (map_var_bit_to_var_aux_n s)"
apply (subst map_var_bit_to_var_aux_imp.simps)+
apply (auto simp add: hd_imp_correct prod_encode_imp_correct var_bit_to_var_nat_imp_correct cons_imp_correct
  tl_imp_correct)
done 

function map_var_bit_to_var_aux_imp_time :: "nat \<Rightarrow> map_var_bit_to_var_aux_state \<Rightarrow> nat" where 
"map_var_bit_to_var_aux_imp_time t s = 
(let
    hd_xs' = map_var_bit_to_var_aux_n s;
    t = t + 2;
    hd_ret' = 0;
    t = t + 2;
    hd_state = \<lparr>hd_xs = hd_xs',
                hd_ret = hd_ret'\<rparr>;
    hd_ret_state = hd_imp hd_state;
    t = t + hd_imp_time 0 hd_state;

    prod_encode_a' = map_var_bit_to_var_aux_v s;
    t = t + 2;
    prod_encode_b' = hd_ret hd_ret_state;
    t = t + 2;
    prod_encode_ret' = 0;
    t = t + 2;
    prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                         prod_encode_b = prod_encode_b',
                         prod_encode_ret = prod_encode_ret'\<rparr>;
    prod_encode_ret_state = prod_encode_imp prod_encode_state;
    t = t + prod_encode_imp_time 0 prod_encode_state;

    var_bit_to_var_nat_n' = prod_encode_ret prod_encode_ret_state;
    t = t + 2;
    var_bit_to_var_nat_ret' = 0;
    t = t + 2;
    var_bit_to_var_nat_state = \<lparr>var_bit_to_var_nat_n = var_bit_to_var_nat_n',
                                var_bit_to_var_nat_ret = var_bit_to_var_nat_ret'\<rparr>;
    var_bit_to_var_nat_ret_state = var_bit_to_var_nat_imp var_bit_to_var_nat_state;
    t = t + var_bit_to_var_nat_imp_time 0 var_bit_to_var_nat_state;

    cons_h' = var_bit_to_var_nat_ret var_bit_to_var_nat_ret_state;
    t = t + 2;
    cons_t' = map_var_bit_to_var_aux_acc s;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h',
                  cons_t = cons_t', 
                  cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;
    map_var_bit_to_var_aux_ret' = cons_ret cons_ret_state;
    t = t + 2;

    tl_xs' = map_var_bit_to_var_aux_n s;
    t = t + 2;
    tl_ret' = 0;
    t = t + 2;
    tl_state = \<lparr>tl_xs = tl_xs', 
                tl_ret = tl_ret'\<rparr>;
    tl_ret_state = tl_imp tl_state;
    t = t + tl_imp_time 0 tl_state;

    map_var_bit_to_var_aux_n' = tl_ret tl_ret_state;
    t = t + 2;
    ret = \<lparr>map_var_bit_to_var_aux_acc = map_var_bit_to_var_aux_acc s,
          map_var_bit_to_var_aux_v = map_var_bit_to_var_aux_v s,
          map_var_bit_to_var_aux_n = map_var_bit_to_var_aux_n',
          map_var_bit_to_var_aux_ret = map_var_bit_to_var_aux_ret'\<rparr>
    in
     t)
    " by auto
    termination
    apply (relation "measure (map_var_bit_to_var_aux_acc \<circ> snd)")
    apply simp 
    done 

declare map_var_bit_to_var_aux_imp_time.simps[simp del]

definition  "map_var_bit_to_var_aux_IMP_Minus \<equiv> 
  (hd_prefix @ hd_xs_str) ::= (A (V map_var_bit_to_var_aux_n_str));;
  (hd_prefix @ hd_ret_str) ::= (A (N 0));;
  invoke_subprogram hd_prefix hd_IMP_Minus;;

  (prod_encode_prefix @ prod_encode_a_str) ::= (A (V map_var_bit_to_var_aux_v_str));;
  (prod_encode_prefix @ prod_encode_b_str) ::= (A (V (hd_prefix @ hd_ret_str)));;
  (prod_encode_prefix @ prod_encode_ret_str) ::= (A (N 0));;
  invoke_subprogram prod_encode_prefix prod_encode_IMP_Minus;;

  (var_bit_to_var_nat_prefix @ var_bit_to_var_nat_n_str) ::= (A (V (prod_encode_prefix @ prod_encode_ret_str)));;
  (var_bit_to_var_nat_prefix @ var_bit_to_var_nat_ret_str) ::= (A (N 0));;
  invoke_subprogram var_bit_to_var_nat_prefix var_bit_to_var_nat_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= (A (V (var_bit_to_var_nat_prefix @ var_bit_to_var_nat_ret_str)));;
  (cons_prefix @ cons_t_str) ::= (A (V map_var_bit_to_var_aux_acc_str));;
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  map_var_bit_to_var_aux_ret_str ::= (A (V (cons_prefix @ cons_ret_str)));;

  (tl_prefix @ tl_xs_str) ::= (A (V map_var_bit_to_var_aux_n_str));;
  (tl_prefix @ tl_ret_str) ::= (A (N 0));;
  invoke_subprogram tl_prefix tl_IMP_Minus;;

  map_var_bit_to_var_aux_n_str ::= (A (V (tl_prefix @ tl_ret_str)))
"

definition "map_var_bit_to_var_aux_imp_to_HOL_state p s =
  \<lparr>map_var_bit_to_var_aux_acc = (s (add_prefix p map_var_bit_to_var_aux_acc_str)),
  map_var_bit_to_var_aux_v = (s (add_prefix p map_var_bit_to_var_aux_v_str)),
  map_var_bit_to_var_aux_n = (s (add_prefix p map_var_bit_to_var_aux_n_str)),
  map_var_bit_to_var_aux_ret = (s (add_prefix p map_var_bit_to_var_aux_ret_str))\<rparr>"

lemmas map_var_bit_to_var_aux_state_translators =
  map_var_bit_to_var_aux_imp_to_HOL_state_def
  hd_imp_to_HOL_state_def
  prod_encode_imp_to_HOL_state_def
  var_bit_to_var_nat_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  tl_imp_to_HOL_state_def

abbreviation "map_var_bit_to_var_aux_IMP_vars \<equiv> {
  map_var_bit_to_var_aux_acc_str, map_var_bit_to_var_aux_v_str, 
  map_var_bit_to_var_aux_n_str, map_var_bit_to_var_aux_ret_str}"

lemma map_var_bit_to_var_aux_IMP_Minus_correct_function_ret:
  "(invoke_subprogram p map_var_bit_to_var_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p map_var_bit_to_var_aux_ret_str)
      = map_var_bit_to_var_aux_ret
          (map_var_bit_to_var_aux_imp (map_var_bit_to_var_aux_imp_to_HOL_state p s))"
apply (simp only: map_var_bit_to_var_aux_IMP_Minus_def prefix_simps)
apply (erule Seq_E)+
apply (erule  hd_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(19) by fastforce
apply (erule  prod_encode_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(21) by fastforce
apply (erule  var_bit_to_var_nat_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(23) by fastforce
apply (erule  cons_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(25) by fastforce
apply (erule  tl_IMP_Minus_correct[where vars="map_var_bit_to_var_aux_IMP_vars"])
subgoal premises p using p(27) by fastforce
apply (clarsimp simp add:
  map_var_bit_to_var_aux_state_translators Let_def map_var_bit_to_var_aux_imp.simps)
subgoal premises p
  using p(10) p(8) p(6) p(4) p(2) by force 
done 

lemma map_var_bit_to_var_aux_IMP_Minus_correct_function_n:
  "(invoke_subprogram p map_var_bit_to_var_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p map_var_bit_to_var_aux_n_str)
      = map_var_bit_to_var_aux_n
          (map_var_bit_to_var_aux_imp (map_var_bit_to_var_aux_imp_to_HOL_state p s))"
apply (simp only: map_var_bit_to_var_aux_IMP_Minus_def prefix_simps)
apply (erule Seq_E)+
apply (erule  hd_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(19) by fastforce
apply (erule  prod_encode_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(21) by fastforce
apply (erule  var_bit_to_var_nat_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(23) by fastforce
apply (erule  cons_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(25) by fastforce
apply (erule  tl_IMP_Minus_correct[where vars="map_var_bit_to_var_aux_IMP_vars"])
subgoal premises p using p(27) by fastforce
apply (clarsimp simp add:
  map_var_bit_to_var_aux_state_translators Let_def map_var_bit_to_var_aux_imp.simps)
subgoal premises p
  using p(10) p(8) p(6) p(4) p(2) by force 
done 

lemma map_var_bit_to_var_aux_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ map_var_bit_to_var_aux_pref) map_var_bit_to_var_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix map_var_bit_to_var_aux_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            


lemma map_var_bit_to_var_aux_IMP_Minus_correct_time:
  "(invoke_subprogram p map_var_bit_to_var_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = map_var_bit_to_var_aux_imp_time 0 (map_var_bit_to_var_aux_imp_to_HOL_state p s)"
apply (simp only: map_var_bit_to_var_aux_IMP_Minus_def prefix_simps)
apply (erule Seq_tE)+
apply (erule hd_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(37) by fastforce
apply (erule prod_encode_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(39) by fastforce
apply (erule var_bit_to_var_nat_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(41) by fastforce
apply (erule cons_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(43) by fastforce
apply (erule tl_IMP_Minus_correct[where vars=map_var_bit_to_var_aux_IMP_vars])
subgoal premises p using p(45) by fastforce
apply (force simp: map_var_bit_to_var_aux_imp_time.simps 
  Let_def map_var_bit_to_var_aux_state_translators)
done 

lemma map_var_bit_to_var_aux_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) map_var_bit_to_var_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (map_var_bit_to_var_aux_imp_time 0 (map_var_bit_to_var_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) map_var_bit_to_var_aux_ret_str) =
          map_var_bit_to_var_aux_ret (map_var_bit_to_var_aux_imp
                                        (map_var_bit_to_var_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) map_var_bit_to_var_aux_n_str) =
          map_var_bit_to_var_aux_n (map_var_bit_to_var_aux_imp
                                        (map_var_bit_to_var_aux_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using map_var_bit_to_var_aux_IMP_Minus_correct_function_ret 
  map_var_bit_to_var_aux_IMP_Minus_correct_function_n
  by (auto simp: map_var_bit_to_var_aux_IMP_Minus_correct_time)
    (meson map_var_bit_to_var_aux_IMP_Minus_correct_effects set_mono_prefix) 

subsubsection \<open>map_var_bit_to_var_acc\<close>

fun map_var_bit_to_var_acc' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_var_bit_to_var_acc' acc v n = (if n \<noteq> 0 
   then (map_var_bit_to_var_acc' ((var_bit_to_var_nat (prod_encode (v,hd_nat n)))## acc) v (tl_nat n))
   else acc)"

lemma "map_var_bit_to_var_acc' acc v n = map_var_bit_to_var_acc acc v n"
proof (induction n arbitrary: acc v rule: less_induct)
  case (less x)
  then show ?case
  proof(cases x)
    case (Suc nat)
    have "tl_nat x < x" using Suc
      by simp
    then show ?thesis
      using less by force
  qed (simp)
qed

record map_var_bit_to_var_acc_state =
  map_var_bit_to_var_acc_acc::nat
  map_var_bit_to_var_acc_v::nat
  map_var_bit_to_var_acc_n::nat
  map_var_bit_to_var_acc_ret::nat

abbreviation "map_var_bit_to_var_acc_prefix \<equiv> ''map_var_bit_to_var_acc.''"
abbreviation "map_var_bit_to_var_acc_acc_str \<equiv> ''acc''"
abbreviation "map_var_bit_to_var_acc_v_str \<equiv> ''v''"
abbreviation "map_var_bit_to_var_acc_n_str \<equiv> ''n''"
abbreviation "map_var_bit_to_var_acc_ret_str \<equiv> ''ret''"

definition "map_var_bit_to_var_acc_state_upd s \<equiv>
  let
    map_var_bit_to_var_aux_acc' = map_var_bit_to_var_acc_acc s;
    map_var_bit_to_var_aux_v' = map_var_bit_to_var_acc_v s;
    map_var_bit_to_var_aux_n' = map_var_bit_to_var_acc_n s;
    map_var_bit_to_var_aux_ret' = 0;
    map_var_bit_to_var_aux_state = 
      \<lparr>map_var_bit_to_var_aux_acc = map_var_bit_to_var_aux_acc',
      map_var_bit_to_var_aux_v = map_var_bit_to_var_aux_v',
      map_var_bit_to_var_aux_n = map_var_bit_to_var_aux_n',
      map_var_bit_to_var_aux_ret = map_var_bit_to_var_aux_ret'\<rparr>;
    map_var_bit_to_var_aux_ret_state = 
        map_var_bit_to_var_aux_imp map_var_bit_to_var_aux_state;


    map_var_bit_to_var_acc_acc' = map_var_bit_to_var_aux_ret map_var_bit_to_var_aux_ret_state;
    map_var_bit_to_var_acc_n' = map_var_bit_to_var_aux_n map_var_bit_to_var_aux_ret_state;
    ret = \<lparr>map_var_bit_to_var_acc_acc = map_var_bit_to_var_acc_acc',
           map_var_bit_to_var_acc_v = map_var_bit_to_var_acc_v s,
           map_var_bit_to_var_acc_n = map_var_bit_to_var_acc_n',
           map_var_bit_to_var_acc_ret = map_var_bit_to_var_acc_ret s\<rparr>
    in ret
"

definition "map_var_bit_to_var_acc_imp_compute_loop_condition s \<equiv>
  (let
    condition = map_var_bit_to_var_acc_n s
   in condition
  )
"

definition "map_var_bit_to_var_acc_imp_after_loop s \<equiv>
  (let
    map_var_bit_to_var_acc_ret' = map_var_bit_to_var_acc_acc s;
    ret = \<lparr>map_var_bit_to_var_acc_acc = map_var_bit_to_var_acc_acc s,
           map_var_bit_to_var_acc_v = map_var_bit_to_var_acc_v s,
           map_var_bit_to_var_acc_n = map_var_bit_to_var_acc_n s,
           map_var_bit_to_var_acc_ret = map_var_bit_to_var_acc_ret'\<rparr>
   in ret
  )"

lemmas map_var_bit_to_var_acc_imp_subprogram_simps = 
  map_var_bit_to_var_acc_state_upd_def
  map_var_bit_to_var_acc_imp_compute_loop_condition_def
  map_var_bit_to_var_acc_imp_after_loop_def

function map_var_bit_to_var_acc_imp::
  "map_var_bit_to_var_acc_state \<Rightarrow> map_var_bit_to_var_acc_state" where
  "map_var_bit_to_var_acc_imp s =
  (if map_var_bit_to_var_acc_imp_compute_loop_condition s \<noteq> 0
   then
    let next_iteration = map_var_bit_to_var_acc_imp (map_var_bit_to_var_acc_state_upd s)
    in next_iteration
   else
    let ret = map_var_bit_to_var_acc_imp_after_loop s
    in ret
  )"
  by simp+
termination 
  apply (relation "measure map_var_bit_to_var_acc_n")
   apply (simp add: map_var_bit_to_var_acc_imp_subprogram_simps 
      map_var_bit_to_var_aux_imp_correct Let_def)+
  done

declare map_var_bit_to_var_acc_imp.simps [simp del]

lemma map_var_bit_to_var_acc_imp_correct[let_function_correctness]:
  "map_var_bit_to_var_acc_ret (map_var_bit_to_var_acc_imp s) =
    map_var_bit_to_var_acc' (map_var_bit_to_var_acc_acc s) 
  (map_var_bit_to_var_acc_v s) (map_var_bit_to_var_acc_n s)"
  apply (induction s rule: map_var_bit_to_var_acc_imp.induct)
  apply (subst map_var_bit_to_var_acc_imp.simps)
  apply (subst map_var_bit_to_var_acc'.simps)
  apply (simp del: map_var_bit_to_var_acc'.simps 
              add: map_var_bit_to_var_acc_imp_subprogram_simps Let_def 
                   fst_nat_fst'_nat snd_nat_snd'_nat snd'_imp_correct fst'_imp_correct
                   map_var_bit_to_var_aux_imp_correct tl_imp_correct)
  done            

definition "map_var_bit_to_var_acc_state_upd_time t s \<equiv>
  let
    map_var_bit_to_var_aux_acc' = map_var_bit_to_var_acc_acc s;
    t = t + 2;
    map_var_bit_to_var_aux_v' = map_var_bit_to_var_acc_v s;
    t = t + 2;
    map_var_bit_to_var_aux_n' = map_var_bit_to_var_acc_n s;
    t = t + 2;
    map_var_bit_to_var_aux_ret' = 0;
    t = t + 2;
    map_var_bit_to_var_aux_state = 
      \<lparr>map_var_bit_to_var_aux_acc = map_var_bit_to_var_aux_acc',
      map_var_bit_to_var_aux_v = map_var_bit_to_var_aux_v',
      map_var_bit_to_var_aux_n = map_var_bit_to_var_aux_n',
      map_var_bit_to_var_aux_ret = map_var_bit_to_var_aux_ret'\<rparr>;
    map_var_bit_to_var_aux_ret_state = 
        map_var_bit_to_var_aux_imp map_var_bit_to_var_aux_state;
    t = t + map_var_bit_to_var_aux_imp_time 0 map_var_bit_to_var_aux_state;

    map_var_bit_to_var_acc_acc' = map_var_bit_to_var_aux_ret map_var_bit_to_var_aux_ret_state;
    t = t + 2;
    map_var_bit_to_var_acc_n' = map_var_bit_to_var_aux_n map_var_bit_to_var_aux_ret_state;
    t = t + 2;
    ret = \<lparr>map_var_bit_to_var_acc_acc = map_var_bit_to_var_acc_acc',
           map_var_bit_to_var_acc_v = map_var_bit_to_var_acc_v s,
           map_var_bit_to_var_acc_n = map_var_bit_to_var_acc_n',
           map_var_bit_to_var_acc_ret = map_var_bit_to_var_acc_ret s\<rparr>
  in
    t
"

definition "map_var_bit_to_var_acc_imp_compute_loop_condition_time t s \<equiv>
  let
    condition = map_var_bit_to_var_acc_n s;
    t = t + 2
  in
    t
"

definition "map_var_bit_to_var_acc_imp_after_loop_time t s \<equiv>
  let
    map_var_bit_to_var_acc_ret' = map_var_bit_to_var_acc_acc s;
    t = t + 2;
    ret = \<lparr>map_var_bit_to_var_acc_acc = map_var_bit_to_var_acc_acc s,
           map_var_bit_to_var_acc_v = map_var_bit_to_var_acc_v s,
           map_var_bit_to_var_acc_n = map_var_bit_to_var_acc_n s,
           map_var_bit_to_var_acc_ret = map_var_bit_to_var_acc_ret'\<rparr>
  in
    t
"

lemmas map_var_bit_to_var_acc_imp_subprogram_time_simps = 
  map_var_bit_to_var_acc_state_upd_time_def
  map_var_bit_to_var_acc_imp_compute_loop_condition_time_def
  map_var_bit_to_var_acc_imp_after_loop_time_def
  map_var_bit_to_var_acc_imp_subprogram_simps

function map_var_bit_to_var_acc_imp_time::
  "nat \<Rightarrow> map_var_bit_to_var_acc_state \<Rightarrow> nat" where
  "map_var_bit_to_var_acc_imp_time t s =
  map_var_bit_to_var_acc_imp_compute_loop_condition_time 0 s +
  (if map_var_bit_to_var_acc_imp_compute_loop_condition s \<noteq> 0
    then
      (let
        t = t + 1;
        next_iteration =
          map_var_bit_to_var_acc_imp_time (t + map_var_bit_to_var_acc_state_upd_time 0 s)
                         (map_var_bit_to_var_acc_state_upd s)
       in next_iteration)
    else
      (let
        t = t + 2;
        ret = t + map_var_bit_to_var_acc_imp_after_loop_time 0 s
       in ret)
  )"
  by auto
termination
  apply (relation "measure (map_var_bit_to_var_acc_n \<circ> snd)")
  by (auto simp add: map_var_bit_to_var_acc_imp_subprogram_time_simps
        map_var_bit_to_var_aux_imp_correct Let_def)

declare map_var_bit_to_var_acc_imp_time.simps [simp del]            

lemma map_var_bit_to_var_acc_imp_time_acc:
  "(map_var_bit_to_var_acc_imp_time (Suc t) s) = Suc (map_var_bit_to_var_acc_imp_time t s)"
  by (induction t s rule: map_var_bit_to_var_acc_imp_time.induct)
    ((subst (1 2) map_var_bit_to_var_acc_imp_time.simps);
      (simp add: map_var_bit_to_var_acc_state_upd_def))            

lemma map_var_bit_to_var_acc_imp_time_acc_2_aux:
  "(map_var_bit_to_var_acc_imp_time t s) = t + (map_var_bit_to_var_acc_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: map_var_bit_to_var_acc_imp_time_acc)+            

lemma map_var_bit_to_var_acc_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (map_var_bit_to_var_acc_imp_time t s) = t + (map_var_bit_to_var_acc_imp_time 0 s)"
  by (rule map_var_bit_to_var_acc_imp_time_acc_2_aux)            

lemma map_var_bit_to_var_acc_imp_time_acc_3:
  "(map_var_bit_to_var_acc_imp_time (a + b) s) = a + (map_var_bit_to_var_acc_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: map_var_bit_to_var_acc_imp_time_acc)+            

abbreviation "map_var_bit_to_var_acc_while_cond \<equiv> ''condition''"

definition "map_var_bit_to_var_acc_IMP_init_while_cond \<equiv>
  \<comment> \<open>condition = map_var_bit_to_var_acc_n s\<close>
  map_var_bit_to_var_acc_while_cond ::= A (V map_var_bit_to_var_acc_n_str)
"

definition "map_var_bit_to_var_acc_IMP_loop_body \<equiv>
 (map_var_bit_to_var_aux_prefix @ map_var_bit_to_var_aux_acc_str)
   ::= A (V map_var_bit_to_var_acc_acc_str);;
 (map_var_bit_to_var_aux_prefix @ map_var_bit_to_var_aux_v_str)
   ::= A (V map_var_bit_to_var_acc_v_str);;
 (map_var_bit_to_var_aux_prefix @ map_var_bit_to_var_aux_n_str)
   ::= A (V map_var_bit_to_var_acc_n_str);;
 (map_var_bit_to_var_aux_prefix @ map_var_bit_to_var_aux_ret_str)
   ::= A (N 0);;
 invoke_subprogram map_var_bit_to_var_aux_prefix map_var_bit_to_var_aux_IMP_Minus;;
  
  (map_var_bit_to_var_acc_acc_str) ::= (A (V (map_var_bit_to_var_aux_prefix 
                                             @ map_var_bit_to_var_aux_ret_str)));;
  (map_var_bit_to_var_acc_n_str) ::=  (A (V (map_var_bit_to_var_aux_prefix 
                                             @ map_var_bit_to_var_aux_n_str)))
"

definition "map_var_bit_to_var_acc_IMP_after_loop \<equiv>
  (map_var_bit_to_var_acc_ret_str) ::= (A (V map_var_bit_to_var_acc_acc_str))
  \<comment> \<open>ret = \<lparr>map_var_bit_to_var_acc_acc = map_var_bit_to_var_acc_acc',\<close>
  \<comment> \<open>       map_var_bit_to_var_acc_v = map_var_bit_to_var_acc_v',\<close>
  \<comment> \<open>       map_var_bit_to_var_acc_n = map_var_bit_to_var_acc_n',\<close>
  \<comment> \<open>       map_var_bit_to_var_acc_ret = map_var_bit_to_var_acc_ret'\<rparr>\<close>
"

definition map_var_bit_to_var_acc_IMP_Minus where
  "map_var_bit_to_var_acc_IMP_Minus \<equiv>
  map_var_bit_to_var_acc_IMP_init_while_cond;;
  WHILE map_var_bit_to_var_acc_while_cond \<noteq>0 DO (
    map_var_bit_to_var_acc_IMP_loop_body;;
    map_var_bit_to_var_acc_IMP_init_while_cond
  );;
  map_var_bit_to_var_acc_IMP_after_loop"

abbreviation "map_var_bit_to_var_acc_IMP_vars\<equiv>
  {map_var_bit_to_var_acc_while_cond,
    map_var_bit_to_var_acc_acc_str, map_var_bit_to_var_acc_v_str,
  map_var_bit_to_var_acc_n_str,  map_var_bit_to_var_acc_ret_str}"

lemmas map_var_bit_to_var_acc_IMP_subprogram_simps =
  map_var_bit_to_var_acc_IMP_init_while_cond_def
  map_var_bit_to_var_acc_IMP_loop_body_def
  map_var_bit_to_var_acc_IMP_after_loop_def

definition "map_var_bit_to_var_acc_imp_to_HOL_state p s =
  \<lparr>map_var_bit_to_var_acc_acc = (s (add_prefix p map_var_bit_to_var_acc_acc_str)),
  map_var_bit_to_var_acc_v = (s (add_prefix p map_var_bit_to_var_acc_v_str)),
  map_var_bit_to_var_acc_n = (s (add_prefix p map_var_bit_to_var_acc_n_str)),
  map_var_bit_to_var_acc_ret = (s (add_prefix p map_var_bit_to_var_acc_ret_str))\<rparr>"

lemmas map_var_bit_to_var_acc_state_translators =
  map_var_bit_to_var_acc_imp_to_HOL_state_def
  map_var_bit_to_var_aux_imp_to_HOL_state_def

lemmas map_var_bit_to_var_acc_complete_simps =
  map_var_bit_to_var_acc_IMP_subprogram_simps
  map_var_bit_to_var_acc_imp_subprogram_simps
  map_var_bit_to_var_acc_state_translators

lemma map_var_bit_to_var_acc_IMP_Minus_correct_function:
  "(invoke_subprogram p map_var_bit_to_var_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p map_var_bit_to_var_acc_ret_str)
      = map_var_bit_to_var_acc_ret
          (map_var_bit_to_var_acc_imp (map_var_bit_to_var_acc_imp_to_HOL_state p s))"
  apply(induction "map_var_bit_to_var_acc_imp_to_HOL_state p s" arbitrary: s s' t
    rule: map_var_bit_to_var_acc_imp.induct)
  apply(subst map_var_bit_to_var_acc_imp.simps)
  apply(simp only: map_var_bit_to_var_acc_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule While_tE)

    subgoal 
      apply (simp only: map_var_bit_to_var_acc_IMP_subprogram_simps prefix_simps)
      apply (clarsimp simp: map_var_bit_to_var_acc_complete_simps) 
      done 

  apply(erule Seq_E)+
  apply(dest_com_gen)

  subgoal
      apply(simp only: map_var_bit_to_var_acc_IMP_init_while_cond_def prefix_simps)
      by(fastforce simp add: map_var_bit_to_var_acc_complete_simps)

  subgoal
      apply(subst (asm) map_var_bit_to_var_acc_IMP_init_while_cond_def)
      apply(simp only: map_var_bit_to_var_acc_IMP_loop_body_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule map_var_bit_to_var_aux_IMP_Minus_correct[where vars = "map_var_bit_to_var_acc_IMP_vars"])
      subgoal premises p using p(12) by fastforce
      apply (force simp add: map_var_bit_to_var_acc_imp_subprogram_simps 
         map_var_bit_to_var_acc_state_translators Let_def)
      done 

  subgoal
      apply(simp only: map_var_bit_to_var_acc_IMP_init_while_cond_def prefix_simps
          map_var_bit_to_var_acc_IMP_loop_body_def)
      apply(erule Seq_E)+
      apply(erule map_var_bit_to_var_aux_IMP_Minus_correct[where vars = "map_var_bit_to_var_acc_IMP_vars"])
      subgoal premises p using p(12) by fastforce
      apply (force simp add: map_var_bit_to_var_acc_imp_subprogram_simps 
         map_var_bit_to_var_acc_state_translators Let_def split: if_splits)
      done 
  done 

lemma map_var_bit_to_var_acc_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ map_var_bit_to_var_acc_pref) map_var_bit_to_var_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix map_var_bit_to_var_acc_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemmas map_var_bit_to_var_acc_complete_time_simps =
  map_var_bit_to_var_acc_imp_subprogram_time_simps
  map_var_bit_to_var_acc_imp_time_acc
  map_var_bit_to_var_acc_imp_time_acc_2
  map_var_bit_to_var_acc_imp_time_acc_3
  map_var_bit_to_var_acc_state_translators

lemma map_var_bit_to_var_acc_IMP_Minus_correct_time:
  "(invoke_subprogram p map_var_bit_to_var_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = map_var_bit_to_var_acc_imp_time 0 (map_var_bit_to_var_acc_imp_to_HOL_state p s)"
  apply(induction "map_var_bit_to_var_acc_imp_to_HOL_state p s" arbitrary: s s' t
      rule: map_var_bit_to_var_acc_imp.induct)
  apply(subst map_var_bit_to_var_acc_imp_time.simps)
  apply(simp only: map_var_bit_to_var_acc_IMP_Minus_def prefix_simps)

  apply(erule Seq_tE)+
  apply(erule While_tE_time)
  subgoal
    apply(simp only: map_var_bit_to_var_acc_IMP_subprogram_simps prefix_simps
     map_var_bit_to_var_acc_complete_time_simps Let_def split: if_splits) 
    apply force
    done 

  apply(erule Seq_tE)+
  apply(simp add: add.assoc)
  apply(dest_com_gen_time)

  subgoal
    apply(simp only: map_var_bit_to_var_acc_IMP_init_while_cond_def prefix_simps)
    by(fastforce simp add: map_var_bit_to_var_acc_complete_simps)

  subgoal
    apply(subst (asm) map_var_bit_to_var_acc_IMP_init_while_cond_def)
    apply(simp only: map_var_bit_to_var_acc_IMP_loop_body_def prefix_simps)
    apply(erule Seq_tE)+
    apply(erule map_var_bit_to_var_aux_IMP_Minus_correct[where vars = "map_var_bit_to_var_acc_IMP_vars"])
    subgoal premises p using p(21) by fastforce
    apply (force simp: map_var_bit_to_var_acc_imp_subprogram_time_simps
        map_var_bit_to_var_acc_state_translators Let_def)
    done 

  subgoal
    apply(simp only: prefix_simps map_var_bit_to_var_acc_IMP_init_while_cond_def
        map_var_bit_to_var_acc_IMP_loop_body_def)
    apply(erule Seq_tE)+
    apply(erule map_var_bit_to_var_aux_IMP_Minus_correct[where vars = "map_var_bit_to_var_acc_IMP_vars"])
    subgoal premises p using p(21) by fastforce
    apply (clarsimp simp add: map_var_bit_to_var_acc_complete_time_simps Let_def)
    subgoal premises p 
      using p(10) 
      by (smt (z3) fun_upd_def list.inject list.simps(3) 
      map_var_bit_to_var_acc_imp_time_acc_2_aux same_append_eq)
    done  
  done   

lemma map_var_bit_to_var_acc_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) map_var_bit_to_var_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (map_var_bit_to_var_acc_imp_time 0 (map_var_bit_to_var_acc_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) map_var_bit_to_var_acc_ret_str) =
          map_var_bit_to_var_acc_ret (map_var_bit_to_var_acc_imp
                                        (map_var_bit_to_var_acc_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using map_var_bit_to_var_acc_IMP_Minus_correct_function
  by (auto simp: map_var_bit_to_var_acc_IMP_Minus_correct_time)
    (meson map_var_bit_to_var_acc_IMP_Minus_correct_effects set_mono_prefix) 

subsubsection \<open>map_var_bit_to_var_tail\<close>

subsection \<open>push_on_stack\<close>
subsubsection \<open>push_on_stack_nat\<close>
record push_on_stack_nat_state =
push_on_stack_nat_c :: nat
push_on_stack_nat_n :: nat
push_on_stack_nat_s :: nat
push_on_stack_nat_ret :: nat

abbreviation "push_on_stack_nat_prefix \<equiv> ''push_on_stack_nat.''"
abbreviation "push_on_stack_nat_c_str \<equiv> ''push_on_stack_nat_c''"
abbreviation "push_on_stack_nat_n_str \<equiv> ''push_on_stack_nat_n''"
abbreviation "push_on_stack_nat_s_str \<equiv> ''push_on_stack_nat_s''"
abbreviation "push_on_stack_nat_ret_str \<equiv> ''push_on_stack_nat_ret''"

definition "push_on_stack_nat_imp_to_HOL_state p s \<equiv>
  \<lparr>push_on_stack_nat_c = s (add_prefix p push_on_stack_nat_c_str),
  push_on_stack_nat_n = s (add_prefix p push_on_stack_nat_n_str),
  push_on_stack_nat_s = s (add_prefix p push_on_stack_nat_s_str),
  push_on_stack_nat_ret = s (add_prefix p push_on_stack_nat_ret_str)\<rparr>"

abbreviation "push_on_stack_nat_hd_c \<equiv> ''push_on_stack_nat_hd_c''"
abbreviation "push_on_stack_nat_cons_n_0 \<equiv> ''push_on_stack_nat_cons_n_0''"
abbreviation "push_on_stack_nat_nth_nat_ret_one \<equiv> ''push_on_stack_nat_nth_nat_ret_one''"
abbreviation "push_on_stack_nat_nth_nat_ret_two \<equiv> ''push_on_stack_nat_nth_nat_ret_two''"
abbreviation "push_on_stack_nat_nth_nat_ret_three \<equiv> ''push_on_stack_nat_nth_nat_ret_three''"
abbreviation "push_on_stack_nat_cons_res \<equiv> ''push_on_stack_nat_cons_res''"
abbreviation "push_on_stack_nat_cond_one \<equiv> ''push_on_stack_nat_cond_one''"
abbreviation "push_on_stack_nat_cond_two \<equiv> ''push_on_stack_nat_cond_two''"
abbreviation "push_on_stack_nat_cond_three \<equiv> ''push_on_stack_nat_cond_three''"

abbreviation "push_on_stack_nat_IMP_vars \<equiv> {
  push_on_stack_nat_c_str, push_on_stack_nat_n_str, push_on_stack_nat_s_str, push_on_stack_nat_ret_str 
}"


lemmas push_on_stack_nat_state_translators =
  push_on_stack_nat_imp_to_HOL_state_def
  hd_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  NOTEQUAL_neq_zero_imp_to_HOL_state_def
  nth_nat_imp_to_HOL_state_def

paragraph if_eq_zero 

definition "push_on_stack_nat_eq_zero s \<equiv> 
  (let
  cons_h' = push_on_stack_nat_n s;
  cons_t' = 0;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  cons_h' = 1;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  cons_h' = cons_ret cons_ret_state;
  cons_t' = push_on_stack_nat_s s;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  push_on_stack_nat_ret' = cons_ret cons_ret_state;
  ret = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c s,
        push_on_stack_nat_n = push_on_stack_nat_n s,
        push_on_stack_nat_s = push_on_stack_nat_s s,
        push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>
in
  ret)"

lemma push_on_stack_nat_eq_zero_imp_correct[let_function_correctness]:
  "push_on_stack_nat_ret (push_on_stack_nat_eq_zero s) = 
    cons (cons 1 (cons (push_on_stack_nat_n s) 0)) (push_on_stack_nat_s s)"
  unfolding push_on_stack_nat_eq_zero_def
  apply (simp add: hd_imp_correct cons_imp_correct Let_def)
  done 

definition "push_on_stack_nat_eq_zero_time t s \<equiv> 
  (let
  cons_h' = push_on_stack_nat_n s;
  t = t + 2;
  cons_t' = 0;
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
  cons_t' = push_on_stack_nat_s s;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  push_on_stack_nat_ret' = cons_ret cons_ret_state;
  t = t + 2;
  ret = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c s,
        push_on_stack_nat_n = push_on_stack_nat_n s,
        push_on_stack_nat_s = push_on_stack_nat_s s,
        push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>
in
  t)"

definition "push_on_stack_nat_eq_zero_IMP_Minus \<equiv> 
 (cons_prefix @ cons_h_str) ::= A (V push_on_stack_nat_n_str);;
 (cons_prefix @ cons_t_str) ::= A (N 0);;
 (cons_prefix @ cons_ret_str) ::= A (N 0);;
 invoke_subprogram cons_prefix cons_IMP_Minus;;

 (cons_prefix @ cons_h_str) ::= A (N 1);;
 (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
 (cons_prefix @ cons_ret_str) ::= A (N 0);;
 invoke_subprogram cons_prefix cons_IMP_Minus;;

 (cons_prefix @ cons_h_str) ::= A (V (cons_prefix @ cons_ret_str));;
 (cons_prefix @ cons_t_str) ::= A (V push_on_stack_nat_s_str);;
 (cons_prefix @ cons_ret_str) ::= A (N 0);;
 invoke_subprogram cons_prefix cons_IMP_Minus;;
 push_on_stack_nat_ret_str ::= A (V (cons_prefix @ cons_ret_str))
"

lemma push_on_stack_nat_eq_zero_IMP_Minus_correct_function:
  "(invoke_subprogram p push_on_stack_nat_eq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p push_on_stack_nat_ret_str)
      = push_on_stack_nat_ret
          (push_on_stack_nat_eq_zero (push_on_stack_nat_imp_to_HOL_state p s))"
   apply (subst push_on_stack_nat_eq_zero_def)
   apply (simp only: push_on_stack_nat_eq_zero_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
   subgoal premises p using p(13) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
   subgoal premises p using p(15) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
   subgoal premises p using p(17) by fastforce 
   apply (force simp: 
      push_on_stack_nat_imp_to_HOL_state_def cons_imp_to_HOL_state_def Let_def)
   done 

lemma push_on_stack_nat_eq_zero_IMP_Minus_correct_time:
  "(invoke_subprogram p push_on_stack_nat_eq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = push_on_stack_nat_eq_zero_time 0 (push_on_stack_nat_imp_to_HOL_state p s)"
   apply (subst push_on_stack_nat_eq_zero_time_def)
   apply (simp only: push_on_stack_nat_eq_zero_IMP_Minus_def prefix_simps)
   apply (erule Seq_tE)+
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
   subgoal premises p using p(25) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
   subgoal premises p using p(27) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
   subgoal premises p using p(29) by fastforce 
   apply (timeit \<open>force simp:
      push_on_stack_nat_imp_to_HOL_state_def cons_imp_to_HOL_state_def Let_def\<close>)
   done

paragraph if_eq_one

definition "push_on_stack_nat_eq_one s \<equiv> 
  (let
  cons_h' = push_on_stack_nat_n s;
  cons_t' = 0;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  push_on_stack_nat_cons_res = cons_ret cons_ret_state;

  nth_nat_n' = 1;
  nth_nat_x' = push_on_stack_nat_c s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  push_on_stack_nat_nth_nat_ret_one = nth_nat_ret nth_nat_ret_state;

  nth_nat_n' = 2;
  nth_nat_x' = push_on_stack_nat_c s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  cons_t' = push_on_stack_nat_cons_res;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = push_on_stack_nat_nth_nat_ret_one;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = 2;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = cons_ret cons_ret_state;
  cons_t' = push_on_stack_nat_s s;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  push_on_stack_nat_ret' = cons_ret cons_ret_state;
  ret = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c s,
        push_on_stack_nat_n = push_on_stack_nat_n s,
        push_on_stack_nat_s = push_on_stack_nat_s s,
        push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>
in
  ret)"

lemma push_on_stack_nat_eq_one_imp_correct[let_function_correctness]:
  "push_on_stack_nat_ret (push_on_stack_nat_eq_one s) = 
    (2## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s)"
  unfolding push_on_stack_nat_eq_one_def
  apply (simp add: nth_nat_imp_correct cons_imp_correct Let_def numeral_2_eq_2)
  done

definition "push_on_stack_nat_eq_one_time t s \<equiv> 
  (let
  cons_h' = push_on_stack_nat_n s;
  t = t + 2;
  cons_t' = 0;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;
  push_on_stack_nat_cons_res = cons_ret cons_ret_state;
  t = t + 2;

  nth_nat_n' = 1;
  t = t + 2;
  nth_nat_x' = push_on_stack_nat_c s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;
  push_on_stack_nat_nth_nat_ret_one = nth_nat_ret nth_nat_ret_state;
  t = t + 2;

  nth_nat_n' = 2;
  t = t + 2;
  nth_nat_x' = push_on_stack_nat_c s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  t = t + 2;
  cons_t' = push_on_stack_nat_cons_res;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  cons_h' = push_on_stack_nat_nth_nat_ret_one;
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

  cons_h' = cons_ret cons_ret_state;
  t = t + 2;
  cons_t' = push_on_stack_nat_s s;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  push_on_stack_nat_ret' = cons_ret cons_ret_state;
  t = t + 2;
  ret = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c s,
        push_on_stack_nat_n = push_on_stack_nat_n s,
        push_on_stack_nat_s = push_on_stack_nat_s s,
        push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>
in
  t)"

definition "push_on_stack_nat_eq_one_IMP_Minus \<equiv>
  (cons_prefix @ cons_h_str) ::= A (V push_on_stack_nat_n_str);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  push_on_stack_nat_cons_res ::= A (V (cons_prefix @ cons_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 1);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V push_on_stack_nat_c_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  push_on_stack_nat_nth_nat_ret_one ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 2);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V push_on_stack_nat_c_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V push_on_stack_nat_cons_res);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V push_on_stack_nat_nth_nat_ret_one);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (N 2);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V push_on_stack_nat_s_str);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  push_on_stack_nat_ret_str ::= A (V (cons_prefix @ cons_ret_str))
"

abbreviation "push_on_stack_nat_IMP_vars_eq_one \<equiv> push_on_stack_nat_IMP_vars 
  \<union> {push_on_stack_nat_nth_nat_ret_one, push_on_stack_nat_cons_res}"

lemma push_on_stack_nat_eq_one_IMP_Minus_correct_function:
  "(invoke_subprogram p push_on_stack_nat_eq_one_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p push_on_stack_nat_ret_str)
      = push_on_stack_nat_ret
          (push_on_stack_nat_eq_one (push_on_stack_nat_imp_to_HOL_state p s))"
   apply (subst push_on_stack_nat_eq_one_def)
   apply (simp only: push_on_stack_nat_eq_one_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
   subgoal premises p using p(31) by fastforce 
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
   subgoal premises p using p(33) by fastforce 
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
   subgoal premises p using p(35) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
   subgoal premises p using p(37) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
   subgoal premises p using p(39) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
   subgoal premises p using p(41) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
   subgoal premises p using p(43) by fastforce
   apply (timeit \<open>force simp:
      push_on_stack_nat_imp_to_HOL_state_def cons_imp_to_HOL_state_def 
      nth_nat_imp_to_HOL_state_def Let_def\<close>)
   done


lemma push_on_stack_nat_eq_one_IMP_Minus_correct_time:
  "(invoke_subprogram p push_on_stack_nat_eq_one_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = push_on_stack_nat_eq_one_time 0 (push_on_stack_nat_imp_to_HOL_state p s)"
  apply (subst push_on_stack_nat_eq_one_time_def)
  apply (simp only: push_on_stack_nat_eq_one_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
  subgoal premises p using p(61) by fastforce 
  apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
  subgoal premises p using p(63) by fastforce 
  apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
  subgoal premises p using p(65) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
  subgoal premises p using p(67) by fastforce 
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
  subgoal premises p using p(69) by fastforce 
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
  subgoal premises p using p(71) by fastforce 
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_one])
  subgoal premises p using p(73) by fastforce
  apply (timeit \<open>force simp: 
      push_on_stack_nat_imp_to_HOL_state_def cons_imp_to_HOL_state_def 
      nth_nat_imp_to_HOL_state_def Let_def\<close>)
  done

paragraph if_eq_two

definition "push_on_stack_nat_eq_two s \<equiv> 
  (let
  cons_h' = push_on_stack_nat_n s;
  cons_t' = 0;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  push_on_stack_nat_cons_res = cons_ret cons_ret_state;

  nth_nat_n' = 1;
  nth_nat_x' = push_on_stack_nat_c s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  push_on_stack_nat_nth_nat_ret_one = nth_nat_ret nth_nat_ret_state;

  nth_nat_n' = 2;
  nth_nat_x' = push_on_stack_nat_c s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  cons_t' = push_on_stack_nat_cons_res;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = push_on_stack_nat_nth_nat_ret_one;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = 3;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = cons_ret cons_ret_state;
  cons_t' = push_on_stack_nat_s s;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  push_on_stack_nat_ret' = cons_ret cons_ret_state;
  ret = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c s,
        push_on_stack_nat_n = push_on_stack_nat_n s,
        push_on_stack_nat_s = push_on_stack_nat_s s,
        push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>
in
  ret)"

lemma push_on_stack_nat_eq_two_imp_correct[let_function_correctness]:
  "push_on_stack_nat_ret (push_on_stack_nat_eq_two s) = 
    (3## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s)"
  unfolding push_on_stack_nat_eq_two_def
  apply (simp add: nth_nat_imp_correct cons_imp_correct Let_def numeral_2_eq_2)
  done

definition "push_on_stack_nat_eq_two_time t s \<equiv> 
  (let
  cons_h' = push_on_stack_nat_n s;
  t = t + 2;
  cons_t' = 0;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;
  push_on_stack_nat_cons_res = cons_ret cons_ret_state;
  t = t + 2;

  nth_nat_n' = 1;
  t = t + 2;
  nth_nat_x' = push_on_stack_nat_c s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;
  push_on_stack_nat_nth_nat_ret_one = nth_nat_ret nth_nat_ret_state;
  t = t + 2;

  nth_nat_n' = 2;
  t = t + 2;
  nth_nat_x' = push_on_stack_nat_c s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  t = t + 2;
  cons_t' = push_on_stack_nat_cons_res;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  cons_h' = push_on_stack_nat_nth_nat_ret_one;
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

  cons_h' = cons_ret cons_ret_state;
  t = t + 2;
  cons_t' = push_on_stack_nat_s s;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  push_on_stack_nat_ret' = cons_ret cons_ret_state;
  t = t + 2;
  ret = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c s,
        push_on_stack_nat_n = push_on_stack_nat_n s,
        push_on_stack_nat_s = push_on_stack_nat_s s,
        push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>
in
  t)"

definition "push_on_stack_nat_eq_two_IMP_Minus \<equiv>
  (cons_prefix @ cons_h_str) ::= A (V push_on_stack_nat_n_str);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  push_on_stack_nat_cons_res ::= A (V (cons_prefix @ cons_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 1);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V push_on_stack_nat_c_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  push_on_stack_nat_nth_nat_ret_one ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 2);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V push_on_stack_nat_c_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V push_on_stack_nat_cons_res);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V push_on_stack_nat_nth_nat_ret_one);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (N 3);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V push_on_stack_nat_s_str);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  push_on_stack_nat_ret_str ::= A (V (cons_prefix @ cons_ret_str))
"

abbreviation "push_on_stack_nat_IMP_vars_eq_two \<equiv> push_on_stack_nat_IMP_vars 
  \<union> {push_on_stack_nat_nth_nat_ret_one, push_on_stack_nat_cons_res}"

lemma push_on_stack_nat_eq_two_IMP_Minus_correct_function:
  "(invoke_subprogram p push_on_stack_nat_eq_two_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p push_on_stack_nat_ret_str)
      = push_on_stack_nat_ret
          (push_on_stack_nat_eq_two (push_on_stack_nat_imp_to_HOL_state p s))"
   apply (subst push_on_stack_nat_eq_two_def)
   apply (simp only: push_on_stack_nat_eq_two_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
   subgoal premises p using p(31) by fastforce 
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
   subgoal premises p using p(33) by fastforce 
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
   subgoal premises p using p(35) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
   subgoal premises p using p(37) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
   subgoal premises p using p(39) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
   subgoal premises p using p(41) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
   subgoal premises p using p(43) by fastforce
   apply (timeit \<open>force simp:
      push_on_stack_nat_imp_to_HOL_state_def cons_imp_to_HOL_state_def 
      nth_nat_imp_to_HOL_state_def Let_def\<close>)
   done

lemma push_on_stack_nat_eq_two_IMP_Minus_correct_time:
  "(invoke_subprogram p push_on_stack_nat_eq_two_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = push_on_stack_nat_eq_two_time 0 (push_on_stack_nat_imp_to_HOL_state p s)"
  apply (subst push_on_stack_nat_eq_two_time_def)
  apply (simp only: push_on_stack_nat_eq_two_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
  subgoal premises p using p(61) by fastforce 
  apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
  subgoal premises p using p(63) by fastforce 
  apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
  subgoal premises p using p(65) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
  subgoal premises p using p(67) by fastforce 
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
  subgoal premises p using p(69) by fastforce 
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
  subgoal premises p using p(71) by fastforce 
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_two])
  subgoal premises p using p(73) by fastforce
  apply (timeit \<open>force simp:
      push_on_stack_nat_imp_to_HOL_state_def cons_imp_to_HOL_state_def 
      nth_nat_imp_to_HOL_state_def Let_def\<close>)
  done

paragraph if_else

definition "push_on_stack_nat_else s \<equiv> 
  (let
  cons_h' = push_on_stack_nat_n s;
  cons_t' = 0;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  push_on_stack_nat_cons_res = cons_ret cons_ret_state;

  nth_nat_n' = 1;
  nth_nat_x' = push_on_stack_nat_c s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  push_on_stack_nat_nth_nat_ret_one = nth_nat_ret nth_nat_ret_state;

  nth_nat_n' = 2;
  nth_nat_x' = push_on_stack_nat_c s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  cons_t' = push_on_stack_nat_cons_res;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = push_on_stack_nat_nth_nat_ret_one;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = 9;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = cons_ret cons_ret_state;
  cons_t' = push_on_stack_nat_s s;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  push_on_stack_nat_ret' = cons_ret cons_ret_state;
  ret = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c s,
        push_on_stack_nat_n = push_on_stack_nat_n s,
        push_on_stack_nat_s = push_on_stack_nat_s s,
        push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>
in
  ret)"

lemma push_on_stack_nat_else_imp_correct[let_function_correctness]:
  "push_on_stack_nat_ret (push_on_stack_nat_else s) = 
    (9## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s)"
  unfolding push_on_stack_nat_else_def
  apply (simp add: nth_nat_imp_correct cons_imp_correct Let_def numeral_2_eq_2)
  done

definition "push_on_stack_nat_else_time t s \<equiv> 
  (let
  cons_h' = push_on_stack_nat_n s;
  t = t + 2;
  cons_t' = 0;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;
  push_on_stack_nat_cons_res = cons_ret cons_ret_state;
  t = t + 2;

  nth_nat_n' = 1;
  t = t + 2;
  nth_nat_x' = push_on_stack_nat_c s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;
  push_on_stack_nat_nth_nat_ret_one = nth_nat_ret nth_nat_ret_state;
  t = t + 2;

  nth_nat_n' = 2;
  t = t + 2;
  nth_nat_x' = push_on_stack_nat_c s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  t = t + 2;
  cons_t' = push_on_stack_nat_cons_res;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  cons_h' = push_on_stack_nat_nth_nat_ret_one;
  t = t + 2;
  cons_t' = cons_ret cons_ret_state;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  cons_h' = 9;
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
  cons_t' = push_on_stack_nat_s s;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  push_on_stack_nat_ret' = cons_ret cons_ret_state;
  t = t + 2;
  ret = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c s,
        push_on_stack_nat_n = push_on_stack_nat_n s,
        push_on_stack_nat_s = push_on_stack_nat_s s,
        push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>
in
  t)"

definition "push_on_stack_nat_else_IMP_Minus \<equiv>
  (cons_prefix @ cons_h_str) ::= A (V push_on_stack_nat_n_str);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  push_on_stack_nat_cons_res ::= A (V (cons_prefix @ cons_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 1);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V push_on_stack_nat_c_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  push_on_stack_nat_nth_nat_ret_one ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 2);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V push_on_stack_nat_c_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V push_on_stack_nat_cons_res);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V push_on_stack_nat_nth_nat_ret_one);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (N 9);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V push_on_stack_nat_s_str);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  push_on_stack_nat_ret_str ::= A (V (cons_prefix @ cons_ret_str))
"

abbreviation "push_on_stack_nat_IMP_vars_else \<equiv> push_on_stack_nat_IMP_vars 
  \<union> {push_on_stack_nat_nth_nat_ret_one, push_on_stack_nat_cons_res}"

lemma push_on_stack_nat_else_IMP_Minus_correct_function:
  "(invoke_subprogram p push_on_stack_nat_else_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p push_on_stack_nat_ret_str)
      = push_on_stack_nat_ret
          (push_on_stack_nat_else (push_on_stack_nat_imp_to_HOL_state p s))"
   apply (subst push_on_stack_nat_else_def)
   apply (simp only: push_on_stack_nat_else_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
   subgoal premises p using p(31) by fastforce 
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
   subgoal premises p using p(33) by fastforce 
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
   subgoal premises p using p(35) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
   subgoal premises p using p(37) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
   subgoal premises p using p(39) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
   subgoal premises p using p(41) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
   subgoal premises p using p(43) by fastforce
   apply (timeit \<open>force simp:
      push_on_stack_nat_imp_to_HOL_state_def cons_imp_to_HOL_state_def 
      nth_nat_imp_to_HOL_state_def Let_def\<close>)
   done


lemma push_on_stack_nat_else_IMP_Minus_correct_time:
  "(invoke_subprogram p push_on_stack_nat_else_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = push_on_stack_nat_else_time 0 (push_on_stack_nat_imp_to_HOL_state p s)"
  apply (subst push_on_stack_nat_else_time_def)
  apply (simp only: push_on_stack_nat_else_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
  subgoal premises p using p(61) by fastforce 
  apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
  subgoal premises p using p(63) by fastforce 
  apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
  subgoal premises p using p(65) by fastforce
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
  subgoal premises p using p(67) by fastforce 
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
  subgoal premises p using p(69) by fastforce 
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
  subgoal premises p using p(71) by fastforce 
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_else])
  subgoal premises p using p(73) by fastforce
  apply (timeit \<open>force simp:
      push_on_stack_nat_imp_to_HOL_state_def cons_imp_to_HOL_state_def 
      nth_nat_imp_to_HOL_state_def Let_def\<close>)
  done

paragraph if_eq_three

definition "push_on_stack_nat_eq_three s \<equiv> 
  (let
  cons_h' = push_on_stack_nat_n s;
  cons_t' = 0;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  push_on_stack_nat_cons_res = cons_ret cons_ret_state;

  nth_nat_n' = 1;
  nth_nat_x' = push_on_stack_nat_c s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  push_on_stack_nat_nth_nat_ret_one = nth_nat_ret nth_nat_ret_state;

  nth_nat_n' = 2;
  nth_nat_x' = push_on_stack_nat_c s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  push_on_stack_nat_nth_nat_ret_two = nth_nat_ret nth_nat_ret_state;
  
  nth_nat_n' = 3;
  nth_nat_x' = push_on_stack_nat_c s;
  nth_nat_ret' = 0;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  cons_t' = push_on_stack_nat_cons_res;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = push_on_stack_nat_nth_nat_ret_two;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = push_on_stack_nat_nth_nat_ret_one;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = 6;
  cons_t' = cons_ret cons_ret_state;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  cons_h' = cons_ret cons_ret_state;
  cons_t' = push_on_stack_nat_s s;
  cons_ret' = 0;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;

  push_on_stack_nat_ret' = cons_ret cons_ret_state;
  ret = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c s,
        push_on_stack_nat_n = push_on_stack_nat_n s,
        push_on_stack_nat_s = push_on_stack_nat_s s,
        push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>
in
  ret)"

lemma push_on_stack_nat_eq_three_imp_correct[let_function_correctness]:
  "push_on_stack_nat_ret (push_on_stack_nat_eq_three s) = 
    (6## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
     (nth_nat (Suc (Suc (Suc 0))) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s)"
  unfolding push_on_stack_nat_eq_three_def
  apply (simp add: nth_nat_imp_correct cons_imp_correct Let_def numeral_2_eq_2 numeral_3_eq_3)
  done

definition "push_on_stack_nat_eq_three_time t s \<equiv> 
  (let
  cons_h' = push_on_stack_nat_n s;
  t = t + 2;
  cons_t' = 0;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;
  push_on_stack_nat_cons_res = cons_ret cons_ret_state;
  t = t + 2;

  nth_nat_n' = 1;
  t = t + 2;
  nth_nat_x' = push_on_stack_nat_c s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;
  push_on_stack_nat_nth_nat_ret_one = nth_nat_ret nth_nat_ret_state;
  t = t + 2;

  nth_nat_n' = 2;
  t = t + 2;
  nth_nat_x' = push_on_stack_nat_c s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;
  push_on_stack_nat_nth_nat_ret_two = nth_nat_ret nth_nat_ret_state;
  t = t + 2;
  
  nth_nat_n' = 3;
  t = t + 2;
  nth_nat_x' = push_on_stack_nat_c s;
  t = t + 2;
  nth_nat_ret' = 0;
  t = t + 2;
  nth_nat_state = \<lparr>nth_nat_n = nth_nat_n', nth_nat_x = nth_nat_x', nth_nat_ret = nth_nat_ret'\<rparr>;
  nth_nat_ret_state = nth_nat_imp nth_nat_state;
  t = t + nth_nat_imp_time 0 nth_nat_state;

  cons_h' = nth_nat_ret nth_nat_ret_state;
  t = t + 2;
  cons_t' = push_on_stack_nat_cons_res;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  cons_h' = push_on_stack_nat_nth_nat_ret_two;
  t = t + 2;
  cons_t' = cons_ret cons_ret_state;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  cons_h' = push_on_stack_nat_nth_nat_ret_one;
  t = t + 2;
  cons_t' = cons_ret cons_ret_state;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  cons_h' = 6;
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
  cons_t' = push_on_stack_nat_s s;
  t = t + 2;
  cons_ret' = 0;
  t = t + 2;
  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
  cons_ret_state = cons_imp cons_state;
  t = t + cons_imp_time 0 cons_state;

  push_on_stack_nat_ret' = cons_ret cons_ret_state;
  t = t + 2;
  ret = \<lparr>push_on_stack_nat_c = push_on_stack_nat_c s,
        push_on_stack_nat_n = push_on_stack_nat_n s,
        push_on_stack_nat_s = push_on_stack_nat_s s,
        push_on_stack_nat_ret = push_on_stack_nat_ret'\<rparr>
in
  t)"

definition "push_on_stack_nat_eq_three_IMP_Minus \<equiv>
  (cons_prefix @ cons_h_str) ::= A (V push_on_stack_nat_n_str);;
  (cons_prefix @ cons_t_str) ::= A (N 0);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  push_on_stack_nat_cons_res ::= A (V (cons_prefix @ cons_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 1);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V push_on_stack_nat_c_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  push_on_stack_nat_nth_nat_ret_one ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 2);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V push_on_stack_nat_c_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;
  push_on_stack_nat_nth_nat_ret_two ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;

  (nth_nat_prefix @ nth_nat_n_str) ::= A (N 3);;
  (nth_nat_prefix @ nth_nat_x_str) ::= A (V push_on_stack_nat_c_str);;
  (nth_nat_prefix @ nth_nat_ret_str) ::= A (N 0);;
  invoke_subprogram nth_nat_prefix nth_nat_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (nth_nat_prefix @ nth_nat_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V push_on_stack_nat_cons_res);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V push_on_stack_nat_nth_nat_ret_two);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V push_on_stack_nat_nth_nat_ret_one);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (N 6);;
  (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;

  (cons_prefix @ cons_h_str) ::= A (V (cons_prefix @ cons_ret_str));;
  (cons_prefix @ cons_t_str) ::= A (V push_on_stack_nat_s_str);;
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  push_on_stack_nat_ret_str ::= A (V (cons_prefix @ cons_ret_str))
"

abbreviation "push_on_stack_nat_IMP_vars_eq_three \<equiv> push_on_stack_nat_IMP_vars 
  \<union> {push_on_stack_nat_nth_nat_ret_one, push_on_stack_nat_nth_nat_ret_two, 
     push_on_stack_nat_cons_res}"

lemma push_on_stack_nat_eq_three_IMP_Minus_correct_function:
  "(invoke_subprogram p push_on_stack_nat_eq_three_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p push_on_stack_nat_ret_str)
      = push_on_stack_nat_ret
          (push_on_stack_nat_eq_three (push_on_stack_nat_imp_to_HOL_state p s))"
   apply (subst push_on_stack_nat_eq_three_def)
   apply (simp only: push_on_stack_nat_eq_three_IMP_Minus_def prefix_simps)
   apply (erule Seq_E)+
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(40) by fastforce 
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(42) by fastforce 
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(44) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(46) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(48) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(50) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(52) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(54) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(56) by fastforce
   apply (timeit \<open>force simp:
      push_on_stack_nat_imp_to_HOL_state_def cons_imp_to_HOL_state_def 
      nth_nat_imp_to_HOL_state_def Let_def\<close>)
   done 


lemma push_on_stack_nat_eq_three_IMP_Minus_correct_time:
  "(invoke_subprogram p push_on_stack_nat_eq_three_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = push_on_stack_nat_eq_three_time 0 (push_on_stack_nat_imp_to_HOL_state p s)"
  apply (subst push_on_stack_nat_eq_three_time_def)
  apply (simp only: push_on_stack_nat_eq_three_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(79) by fastforce 
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(81) by fastforce 
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(83) by fastforce
   apply (erule nth_nat_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(85) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(87) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(89) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(91) by fastforce 
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(93) by fastforce
   apply (erule cons_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars_eq_three])
   subgoal premises p using p(95) by fastforce
  apply (force simp: 
      push_on_stack_nat_imp_to_HOL_state_def cons_imp_to_HOL_state_def 
      nth_nat_imp_to_HOL_state_def Let_def)
  done

paragraph separations_of_nested_ifs

definition  "push_on_stack_nat_sub_branch_aux1 s \<equiv> 
       (let
          hd_xs' = push_on_stack_nat_c s;
          hd_ret' = 0;
          hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
          hd_ret_state = hd_imp hd_state;
          push_on_stack_nat_hd_c = hd_ret hd_ret_state;
          NOTEQUAL_neq_zero_a' = push_on_stack_nat_hd_c;
          NOTEQUAL_neq_zero_b' = 2;
          NOTEQUAL_neq_zero_ret' = 0;
          NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                                    NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                                    NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
          NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
          push_on_stack_nat_cond_three = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state)
        in 
          (if push_on_stack_nat_cond_three \<noteq> 0
                then push_on_stack_nat_else s
                else push_on_stack_nat_eq_two s))"

lemma push_on_stack_nat_sub_branch_aux1_imp_correct:
  "push_on_stack_nat_ret (push_on_stack_nat_sub_branch_aux1 s) = 
    (if (hd_nat (push_on_stack_nat_c s)) \<noteq>2
           then (9## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s)
           else (3## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s))"
  apply (subst push_on_stack_nat_sub_branch_aux1_def)
  apply (simp add: NOTEQUAL_neq_zero_imp_correct hd_imp_correct
   push_on_stack_nat_eq_one_imp_correct push_on_stack_nat_eq_two_imp_correct
   push_on_stack_nat_else_imp_correct
   Let_def)
  done

definition "push_on_stack_nat_sub_branch_aux1_IMP_Minus \<equiv>
  (hd_prefix @ hd_xs_str) ::= A (V push_on_stack_nat_c_str);;
  (hd_prefix @ hd_ret_str) ::= A (N 0);;
  invoke_subprogram hd_prefix hd_IMP_Minus;;
  push_on_stack_nat_hd_c ::= A (V (hd_prefix @ hd_ret_str));;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_a_str) ::= A (V push_on_stack_nat_hd_c);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_b_str) ::= A (N 2);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str) ::= A (N 0);;
  invoke_subprogram NOTEQUAL_neq_zero_prefix NOTEQUAL_neq_zero_IMP_Minus;;
  push_on_stack_nat_cond_three ::= A (V (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str));;
  (IF push_on_stack_nat_cond_three \<noteq>0
    THEN push_on_stack_nat_else_IMP_Minus
    ELSE push_on_stack_nat_eq_two_IMP_Minus)
  "
definition "push_on_stack_nat_sub_branch_aux1_time t s \<equiv> 
    (let
       hd_xs' = push_on_stack_nat_c s;
       t = t + 2;
       hd_ret' = 0;
       t = t + 2;
       hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
       hd_ret_state = hd_imp hd_state;
       t = t + hd_imp_time 0 hd_state;
       push_on_stack_nat_hd_c = hd_ret hd_ret_state;
       t = t + 2;
       NOTEQUAL_neq_zero_a' = push_on_stack_nat_hd_c;
       t = t + 2;
       NOTEQUAL_neq_zero_b' = 2;
       t = t + 2;
       NOTEQUAL_neq_zero_ret' = 0;
       t = t + 2;
       NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                                 NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                                 NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
       NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
       t = t + NOTEQUAL_neq_zero_imp_time 0 NOTEQUAL_neq_zero_state;
       push_on_stack_nat_cond_three = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state);
       t = t + 2
       in (if push_on_stack_nat_cond_three \<noteq> 0
                then 
                let
                 t = t + 1;
                 t = t + push_on_stack_nat_else_time 0 s
                in
                 t
                else 
                let
                 t = t + 1;
                 t = t + push_on_stack_nat_eq_two_time 0 s
                in
                 t))"

lemma push_on_stack_nat_sub_branch_aux1_IMP_Minus_correct_function:
  "(invoke_subprogram p push_on_stack_nat_sub_branch_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p push_on_stack_nat_ret_str)
      = push_on_stack_nat_ret
          (push_on_stack_nat_sub_branch_aux1 (push_on_stack_nat_imp_to_HOL_state p s))"
  apply (subst push_on_stack_nat_sub_branch_aux1_def)
  apply (simp only: push_on_stack_nat_sub_branch_aux1_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule hd_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(10) by fastforce
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(12) by fastforce
  apply (erule If_E)
    subgoal
      apply (force dest!: push_on_stack_nat_else_IMP_Minus_correct_function 
      simp: push_on_stack_nat_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def
          hd_imp_to_HOL_state_def Let_def)
    done 
    subgoal
     apply (force dest!: push_on_stack_nat_eq_two_IMP_Minus_correct_function 
      simp: push_on_stack_nat_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def
          hd_imp_to_HOL_state_def Let_def)
    done
  done

lemma push_on_stack_nat_sub_branch_aux1_IMP_Minus_correct_time:
  "(invoke_subprogram p push_on_stack_nat_sub_branch_aux1_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
    t = push_on_stack_nat_sub_branch_aux1_time 0 
           (push_on_stack_nat_imp_to_HOL_state p s)"
  apply (subst push_on_stack_nat_sub_branch_aux1_time_def)
  apply (simp only: push_on_stack_nat_sub_branch_aux1_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule hd_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(19) by fastforce
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(21) by fastforce
  apply (erule If_tE)
    subgoal
      apply (force dest!: push_on_stack_nat_else_IMP_Minus_correct_time
      simp: push_on_stack_nat_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def
          hd_imp_to_HOL_state_def Let_def)
    done 
    subgoal
     apply (force dest!: push_on_stack_nat_eq_two_IMP_Minus_correct_time 
      simp: push_on_stack_nat_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def
          hd_imp_to_HOL_state_def Let_def)
    done
  done

  definition "push_on_stack_nat_sub_branch_aux2 s \<equiv> 
    (let
       hd_xs' = push_on_stack_nat_c s;
       hd_ret' = 0;
       hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
       hd_ret_state = hd_imp hd_state;
       push_on_stack_nat_hd_c = hd_ret hd_ret_state;
       NOTEQUAL_neq_zero_a' = push_on_stack_nat_hd_c;
       NOTEQUAL_neq_zero_b' = 1;
       NOTEQUAL_neq_zero_ret' = 0;
       NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                                 NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                                 NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
       NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
       push_on_stack_nat_cond_two = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state)
       in (if push_on_stack_nat_cond_two \<noteq> 0
          then push_on_stack_nat_sub_branch_aux1 s
          else push_on_stack_nat_eq_one s))"


lemma push_on_stack_nat_sub_branch_aux2_imp_correct:
  "push_on_stack_nat_ret (push_on_stack_nat_sub_branch_aux2 s) = 
    (if (hd_nat (push_on_stack_nat_c s)) \<noteq>1
     then (if (hd_nat (push_on_stack_nat_c s)) \<noteq>2
           then (9## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s)
           else (3## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s))
     else (2## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s))"
  apply (subst push_on_stack_nat_sub_branch_aux2_def)
  apply (simp add: NOTEQUAL_neq_zero_imp_correct hd_imp_correct
   push_on_stack_nat_eq_one_imp_correct push_on_stack_nat_eq_two_imp_correct
   push_on_stack_nat_else_imp_correct push_on_stack_nat_sub_branch_aux1_imp_correct
   Let_def)
  done

definition "push_on_stack_nat_sub_branch_aux2_IMP_Minus \<equiv>
  (hd_prefix @ hd_xs_str) ::= A (V push_on_stack_nat_c_str);;
  (hd_prefix @ hd_ret_str) ::= A (N 0);;
  invoke_subprogram hd_prefix hd_IMP_Minus;;
  push_on_stack_nat_hd_c ::= A (V (hd_prefix @ hd_ret_str));;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_a_str) ::= A (V push_on_stack_nat_hd_c);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_b_str) ::= A (N 1);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str) ::= A (N 0);;
  invoke_subprogram NOTEQUAL_neq_zero_prefix NOTEQUAL_neq_zero_IMP_Minus;;
  push_on_stack_nat_cond_two ::= A (V (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str));;
  (IF push_on_stack_nat_cond_two \<noteq>0
  THEN push_on_stack_nat_sub_branch_aux1_IMP_Minus
  ELSE push_on_stack_nat_eq_one_IMP_Minus)"


lemma push_on_stack_nat_sub_branch_aux2_IMP_Minus_correct_function:
  "(invoke_subprogram p push_on_stack_nat_sub_branch_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p push_on_stack_nat_ret_str)
      = push_on_stack_nat_ret
          (push_on_stack_nat_sub_branch_aux2 (push_on_stack_nat_imp_to_HOL_state p s))"
  apply (subst push_on_stack_nat_sub_branch_aux2_def)
  apply (simp only: push_on_stack_nat_sub_branch_aux2_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule hd_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(10) by fastforce
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(12) by fastforce
  apply (erule If_E)
    subgoal 
      apply (force dest!: push_on_stack_nat_sub_branch_aux1_IMP_Minus_correct_function 
      simp: push_on_stack_nat_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def
      hd_imp_to_HOL_state_def Let_def)
    done 
    subgoal 
    apply (force dest!: push_on_stack_nat_eq_one_IMP_Minus_correct_function 
      simp: push_on_stack_nat_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def
      hd_imp_to_HOL_state_def Let_def)
    done
  done

definition "push_on_stack_nat_sub_branch_aux2_time t s \<equiv> 
    (let
       hd_xs' = push_on_stack_nat_c s;
       t = t + 2;
       hd_ret' = 0;
       t = t + 2;
       hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
       hd_ret_state = hd_imp hd_state;
       t = t + hd_imp_time 0 hd_state;
       push_on_stack_nat_hd_c = hd_ret hd_ret_state;
       t = t + 2;
       NOTEQUAL_neq_zero_a' = push_on_stack_nat_hd_c;
       t = t + 2;
       NOTEQUAL_neq_zero_b' = 1;
       t = t + 2;
       NOTEQUAL_neq_zero_ret' = 0;
       t = t + 2;
       NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                                 NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                                 NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
       NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
       t = t + NOTEQUAL_neq_zero_imp_time 0 NOTEQUAL_neq_zero_state;
       push_on_stack_nat_cond_two = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state);
       t = t + 2
       in (if push_on_stack_nat_cond_two \<noteq> 0
          then 
            (let 
             t = t + 1;
             t = t + push_on_stack_nat_sub_branch_aux1_time 0 s
            in 
             t)
          else 
          let 
           t = t + 1;
           t = t + push_on_stack_nat_eq_one_time 0 s
          in
           t))"

lemma push_on_stack_nat_sub_branch_aux2_IMP_Minus_correct_time:
  "(invoke_subprogram p push_on_stack_nat_sub_branch_aux2_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = push_on_stack_nat_sub_branch_aux2_time 0 
           (push_on_stack_nat_imp_to_HOL_state p s)"
  apply (subst push_on_stack_nat_sub_branch_aux2_time_def)
  apply (simp only: push_on_stack_nat_sub_branch_aux2_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule hd_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(19) by fastforce
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(21) by fastforce
  apply (erule If_tE)
    subgoal 
    apply (force dest!: push_on_stack_nat_sub_branch_aux1_IMP_Minus_correct_time simp:
            push_on_stack_nat_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def Let_def
            hd_imp_to_HOL_state_def)
    done
    subgoal 
    apply (force dest!: push_on_stack_nat_eq_one_IMP_Minus_correct_time simp:
            push_on_stack_nat_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def Let_def
            hd_imp_to_HOL_state_def)
    done
  done

definition "push_on_stack_nat_sub_branch_aux3 s \<equiv> 
(let
  hd_xs' = push_on_stack_nat_c s;
  hd_ret' = 0;
  hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
  hd_ret_state = hd_imp hd_state;
  push_on_stack_nat_hd_c = hd_ret hd_ret_state;
  NOTEQUAL_neq_zero_a' = push_on_stack_nat_hd_c;
  NOTEQUAL_neq_zero_b' = 3;
  NOTEQUAL_neq_zero_ret' = 0;
  NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                            NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                            NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
  NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
  push_on_stack_nat_cond_one = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state)
 in
  (if push_on_stack_nat_cond_one \<noteq> 0
      then (push_on_stack_nat_sub_branch_aux2 s)
      else push_on_stack_nat_eq_three s))"

lemma push_on_stack_nat_sub_branch_aux3_imp_correct:
   "push_on_stack_nat_ret (push_on_stack_nat_sub_branch_aux3 s) =
    (if (hd_nat (push_on_stack_nat_c s)) \<noteq>3 
    then (if (hd_nat (push_on_stack_nat_c s)) \<noteq>1
     then (if (hd_nat (push_on_stack_nat_c s)) \<noteq>2
           then (9## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s)
           else (3## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s))
     else (2## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
     (nth_nat (Suc (Suc 0)) (push_on_stack_nat_c s)) ##
      (push_on_stack_nat_n s) ## 0)## (push_on_stack_nat_s s))
    else (6## (nth_nat (Suc 0) (push_on_stack_nat_c s)) ## 
       (nth_nat (Suc (Suc 0))(push_on_stack_nat_c s)) ## 
       (nth_nat (Suc (Suc (Suc 0))) (push_on_stack_nat_c s)) 
       ## (push_on_stack_nat_n s)  ## 0) ## (push_on_stack_nat_s s)
    )"
  apply (subst push_on_stack_nat_sub_branch_aux3_def)
  apply (simp add: NOTEQUAL_neq_zero_imp_correct hd_imp_correct
   push_on_stack_nat_eq_three_imp_correct push_on_stack_nat_sub_branch_aux2_imp_correct
   Let_def)
  done

definition "push_on_stack_nat_sub_branch_aux3_IMP_Minus \<equiv> 
  (hd_prefix @ hd_xs_str) ::= A (V push_on_stack_nat_c_str);;
  (hd_prefix @ hd_ret_str) ::= A (N 0);;
  invoke_subprogram hd_prefix hd_IMP_Minus;;
  push_on_stack_nat_hd_c ::= A (V (hd_prefix @ hd_ret_str));;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_a_str) ::= A (V push_on_stack_nat_hd_c);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_b_str) ::= A (N 3);;
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str) ::= A (N 0);;
  invoke_subprogram NOTEQUAL_neq_zero_prefix NOTEQUAL_neq_zero_IMP_Minus;;
  push_on_stack_nat_cond_one ::= A (V (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str));;
  (IF push_on_stack_nat_cond_one \<noteq>0
  THEN push_on_stack_nat_sub_branch_aux2_IMP_Minus
  ELSE push_on_stack_nat_eq_three_IMP_Minus)"

definition "push_on_stack_nat_sub_branch_aux3_time t s \<equiv> 
(let
  hd_xs' = push_on_stack_nat_c s;
  t = t + 2;
  hd_ret' = 0;
  t = t + 2;
  hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
  hd_ret_state = hd_imp hd_state;
  t = t + hd_imp_time 0 hd_state;
  push_on_stack_nat_hd_c = hd_ret hd_ret_state;
  t = t + 2;
  NOTEQUAL_neq_zero_a' = push_on_stack_nat_hd_c;
  t = t + 2;
  NOTEQUAL_neq_zero_b' = 3;
  t = t + 2;
  NOTEQUAL_neq_zero_ret' = 0;
  t = t + 2;
  NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                            NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                            NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
  NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
  t = t + NOTEQUAL_neq_zero_imp_time 0 NOTEQUAL_neq_zero_state;
  push_on_stack_nat_cond_one = (NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state);
  t = t + 2
 in
  (if push_on_stack_nat_cond_one \<noteq> 0
      then 
        let 
         t = t + 1;
         t = t + push_on_stack_nat_sub_branch_aux2_time 0 s
        in t
      else 
       let 
        t = t + 1;
        t = t + push_on_stack_nat_eq_three_time 0 s
        in t))"

lemma push_on_stack_nat_sub_branch_aux3_IMP_Minus_correct_function:
  "(invoke_subprogram p push_on_stack_nat_sub_branch_aux3_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p push_on_stack_nat_ret_str)
      = push_on_stack_nat_ret
          (push_on_stack_nat_sub_branch_aux3 (push_on_stack_nat_imp_to_HOL_state p s))"
  apply (subst push_on_stack_nat_sub_branch_aux3_def)
  apply (simp only: push_on_stack_nat_sub_branch_aux3_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule hd_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(10) by fastforce
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(12) by fastforce
  apply (erule If_E)
    subgoal 
      apply (force dest!:push_on_stack_nat_sub_branch_aux2_IMP_Minus_correct_function simp:  
      Let_def hd_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def push_on_stack_nat_imp_to_HOL_state_def)
      done
    subgoal 
    apply (force dest!:push_on_stack_nat_eq_three_IMP_Minus_correct_function simp:  
      Let_def hd_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def push_on_stack_nat_imp_to_HOL_state_def)
    done 
  done 

lemma push_on_stack_nat_sub_branch_aux3_IMP_Minus_correct_time:
  "(invoke_subprogram p push_on_stack_nat_sub_branch_aux3_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = push_on_stack_nat_sub_branch_aux3_time 0 (push_on_stack_nat_imp_to_HOL_state p s)"
  apply (subst push_on_stack_nat_sub_branch_aux3_time_def)
  apply (simp only: push_on_stack_nat_sub_branch_aux3_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule hd_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(19) by fastforce
  apply (erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(21) by fastforce
  apply (erule If_tE)
    subgoal 
      apply (force dest!:push_on_stack_nat_sub_branch_aux2_IMP_Minus_correct_time simp:  
      Let_def hd_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def push_on_stack_nat_imp_to_HOL_state_def)
      done
    subgoal 
    apply (force dest!:push_on_stack_nat_eq_three_IMP_Minus_correct_time simp:  
      Let_def hd_imp_to_HOL_state_def NOTEQUAL_neq_zero_imp_to_HOL_state_def push_on_stack_nat_imp_to_HOL_state_def)
    done 
  done 

definition "push_on_stack_nat_state_upd s \<equiv> 
 (let
  hd_xs' = push_on_stack_nat_c s;
  hd_ret' = 0;
  hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
  hd_ret_state = hd_imp hd_state;
  push_on_stack_nat_hd_c = hd_ret hd_ret_state
 in
  (if push_on_stack_nat_hd_c \<noteq> 0
  then push_on_stack_nat_sub_branch_aux3 s
  else push_on_stack_nat_eq_zero s)
  )"

function push_on_stack_nat_imp::
  "push_on_stack_nat_state \<Rightarrow> push_on_stack_nat_state" where
  "push_on_stack_nat_imp s =
    (let 
      ret = push_on_stack_nat_state_upd s
    in 
     ret)"
  by simp+
termination
  by (relation "measure (\<lambda>s. push_on_stack_nat_c s)") simp

declare push_on_stack_nat_imp.simps[simp del]

lemma push_on_stack_nat_imp_correct:
   "push_on_stack_nat_ret (push_on_stack_nat_imp s) =
    push_on_stack_nat (push_on_stack_nat_c s) (push_on_stack_nat_n s) (push_on_stack_nat_s s)"
  apply (subst push_on_stack_nat_imp.simps)
  apply (subst push_on_stack_nat_def)
  apply (simp add: push_on_stack_nat_state_upd_def hd_imp_correct cons_imp_correct 
   NOTEQUAL_neq_zero_imp_correct 
    push_on_stack_nat_eq_zero_imp_correct
   push_on_stack_nat_sub_branch_aux3_imp_correct 
   Let_def split: if_splits)  
  done

definition "push_on_stack_nat_IMP_Minus \<equiv> 
 (hd_prefix @ hd_xs_str) ::= A (V push_on_stack_nat_c_str);;
 (hd_prefix @ hd_ret_str) ::= A (N 0);;
 invoke_subprogram hd_prefix hd_IMP_Minus;;
 push_on_stack_nat_hd_c ::= A (V (hd_prefix @ hd_ret_str));;
 IF push_on_stack_nat_hd_c \<noteq>0
  THEN  push_on_stack_nat_sub_branch_aux3_IMP_Minus
  ELSE push_on_stack_nat_eq_zero_IMP_Minus"

definition "push_on_stack_nat_state_upd_time t s\<equiv> 
(let
  hd_xs' = push_on_stack_nat_c s;
  t = t + 2;
  hd_ret' = 0;
  t = t + 2;
  hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
  hd_ret_state = hd_imp hd_state;
  t = t + hd_imp_time 0 hd_state;
  push_on_stack_nat_hd_c = hd_ret hd_ret_state;
  t = t + 2
 in
  (if push_on_stack_nat_hd_c \<noteq> 0
  then 
    let 
     t = t + 1;
     t = t + push_on_stack_nat_sub_branch_aux3_time 0 s
    in 
    t 
  else 
   let 
    t = t + 1;
    t = t + push_on_stack_nat_eq_zero_time 0 s
   in
    t)
  )"

function push_on_stack_nat_imp_time :: "nat \<Rightarrow> push_on_stack_nat_state \<Rightarrow> nat" where
  "push_on_stack_nat_imp_time t s =
    (let 
      ret = push_on_stack_nat_state_upd_time t s
    in 
     ret)"
  by auto
termination
  by (relation "measure (\<lambda>(t, s). push_on_stack_nat_c s)") simp

declare push_on_stack_nat_imp_time.simps[simp del]



lemma push_on_stack_nat_IMP_Minus_correct_function:
  "(invoke_subprogram p push_on_stack_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p push_on_stack_nat_ret_str)
      = push_on_stack_nat_ret
          (push_on_stack_nat_imp (push_on_stack_nat_imp_to_HOL_state p s))"
  apply (subst push_on_stack_nat_imp.simps)
  apply (simp only: push_on_stack_nat_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule hd_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(5) by fastforce
  apply (erule If_E)
    subgoal 
      apply (force dest!:push_on_stack_nat_sub_branch_aux3_IMP_Minus_correct_function simp:  
      push_on_stack_nat_state_upd_def Let_def hd_imp_to_HOL_state_def push_on_stack_nat_imp_to_HOL_state_def)
      done 
    subgoal 
    apply (force dest!:push_on_stack_nat_eq_zero_IMP_Minus_correct_function simp:  
      push_on_stack_nat_state_upd_def Let_def hd_imp_to_HOL_state_def push_on_stack_nat_imp_to_HOL_state_def)
    done 
  done 

lemma push_on_stack_nat_IMP_Minus_correct_time:
  "(invoke_subprogram p push_on_stack_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = push_on_stack_nat_imp_time 0 (push_on_stack_nat_imp_to_HOL_state p s)"
  apply (subst push_on_stack_nat_imp_time.simps)
  apply (simp only: push_on_stack_nat_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule hd_IMP_Minus_correct[where vars=push_on_stack_nat_IMP_vars])
  subgoal premises p using p(9) by fastforce
  apply (erule If_tE)
    subgoal 
      apply (force dest!:push_on_stack_nat_sub_branch_aux3_IMP_Minus_correct_time
      simp: push_on_stack_nat_state_upd_time_def 
      Let_def hd_imp_to_HOL_state_def push_on_stack_nat_imp_to_HOL_state_def)
      done 
    subgoal 
    apply (force dest!:push_on_stack_nat_eq_zero_IMP_Minus_correct_time simp:  
      push_on_stack_nat_state_upd_time_def Let_def hd_imp_to_HOL_state_def push_on_stack_nat_imp_to_HOL_state_def)
    done 
  done 

lemma push_on_stack_nat_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ push_on_stack_nat_prefix) push_on_stack_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix push_on_stack_nat_prefix v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def 
  by blast

lemma push_on_stack_nat_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) push_on_stack_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (push_on_stack_nat_imp_time 0 (push_on_stack_nat_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) push_on_stack_nat_ret_str) =
          push_on_stack_nat_ret (push_on_stack_nat_imp
                                        (push_on_stack_nat_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using push_on_stack_nat_IMP_Minus_correct_function 
       push_on_stack_nat_IMP_Minus_correct_time
       push_on_stack_nat_IMP_Minus_correct_effects set_mono_prefix
  by (smt (verit, ccfv_SIG) com_add_prefix_valid_subset com_only_vars)

end