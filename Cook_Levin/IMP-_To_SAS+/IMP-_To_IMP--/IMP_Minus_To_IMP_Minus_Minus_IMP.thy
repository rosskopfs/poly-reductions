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
    hd_xs' = map_var_bit_to_var_acc_n s;
    hd_ret' = 0;
    hd_state = \<lparr>hd_xs = hd_xs',
                hd_ret = hd_ret'\<rparr>;
    hd_ret_state = hd_imp hd_state;
    hd_result = hd_ret hd_ret_state;
    prod_encode_a' = map_var_bit_to_var_acc_v s;
    prod_encode_b' = hd_result;
    prod_encode_ret' = 0;
    prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                         prod_encode_b = prod_encode_b',
      prod_encode_ret = prod_encode_ret'\<rparr>;
    prod_encode_ret_state = prod_encode_imp prod_encode_state;
    prod_encode_result = prod_encode_ret prod_encode_ret_state;
    var_bit_to_var_nat_n' = prod_encode_result;
    var_bit_to_var_nat_ret' = 0;
    var_bit_to_var_nat_state = \<lparr>var_bit_to_var_nat_n = var_bit_to_var_nat_n',
                                var_bit_to_var_nat_ret = var_bit_to_var_nat_ret'\<rparr>;
    var_bit_to_var_nat_ret_state = var_bit_to_var_nat_imp var_bit_to_var_nat_state;
    var_bit_to_var_nat_result = var_bit_to_var_nat_ret var_bit_to_var_nat_ret_state;
    cons_h' = var_bit_to_var_nat_result;
    cons_t' = map_var_bit_to_var_acc_acc s;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h',
                  cons_t = cons_t', 
                  cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    cons_result = cons_ret cons_ret_state;
    tl_xs' = map_var_bit_to_var_acc_n s;
    tl_ret' = 0;
    tl_state = \<lparr>tl_xs = tl_xs', 
                tl_ret = tl_ret'\<rparr>;
    tl_ret_state = tl_imp tl_state;
    tl_result = tl_ret tl_ret_state;
    map_var_bit_to_var_acc_acc' = cons_result;
    map_var_bit_to_var_acc_v' = map_var_bit_to_var_acc_v s;
    map_var_bit_to_var_acc_n' = tl_result;
    map_var_bit_to_var_acc_ret' = map_var_bit_to_var_acc_ret s;
    ret = \<lparr>map_var_bit_to_var_acc_acc = map_var_bit_to_var_acc_acc',
           map_var_bit_to_var_acc_v = map_var_bit_to_var_acc_v',
           map_var_bit_to_var_acc_n = map_var_bit_to_var_acc_n',
           map_var_bit_to_var_acc_ret = map_var_bit_to_var_acc_ret'\<rparr>
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
    map_var_bit_to_var_acc_acc' = map_var_bit_to_var_acc_acc s;
    map_var_bit_to_var_acc_v' = map_var_bit_to_var_acc_v s;
    map_var_bit_to_var_acc_n' = map_var_bit_to_var_acc_n s;
    map_var_bit_to_var_acc_ret' = map_var_bit_to_var_acc_acc s;
    ret = \<lparr>map_var_bit_to_var_acc_acc = map_var_bit_to_var_acc_acc',
           map_var_bit_to_var_acc_v = map_var_bit_to_var_acc_v',
           map_var_bit_to_var_acc_n = map_var_bit_to_var_acc_n',
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
   apply (simp add: map_var_bit_to_var_acc_imp_subprogram_simps tl_imp_correct)+
  done

declare map_var_bit_to_var_acc_imp.simps [simp del]

lemma map_var_bit_to_var_acc_imp_correct[imp_let_correct_lemmas]:
  "map_var_bit_to_var_acc_ret (map_var_bit_to_var_acc_imp s) =
    map_var_bit_to_var_acc' (map_var_bit_to_var_acc_acc s) 
  (map_var_bit_to_var_acc_v s) (map_var_bit_to_var_acc_n s)"
  apply (induction s rule: map_var_bit_to_var_acc_imp.induct)
  apply (subst map_var_bit_to_var_acc_imp.simps)
  apply (subst map_var_bit_to_var_acc'.simps)
  apply (simp del: map_var_bit_to_var_acc'.simps 
              add: map_var_bit_to_var_acc_imp_subprogram_simps Let_def 
                   fst_nat_fst'_nat snd_nat_snd'_nat snd'_imp_correct fst'_imp_correct
                   hd_imp_correct prod_encode_imp_correct var_bit_to_var_nat_imp_correct
                   cons_imp_correct tl_imp_correct)
  done            

definition "map_var_bit_to_var_acc_state_upd_time t s \<equiv>
  let
    hd_xs' = map_var_bit_to_var_acc_n s;
    t = t + 2;
    hd_ret' = 0;
    t = t + 2;
    hd_state = \<lparr>hd_xs = hd_xs',
                hd_ret = hd_ret'\<rparr>;
    hd_ret_state = hd_imp hd_state;
    t = t + hd_imp_time 0 hd_state;
    hd_result = hd_ret hd_ret_state;
    t = t + 2;
    prod_encode_a' = map_var_bit_to_var_acc_v s;
    t = t + 2;
    prod_encode_b' = hd_result;
    t = t + 2;
    prod_encode_ret' = 0;
    t = t + 2;
    prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',
                         prod_encode_b = prod_encode_b',
      prod_encode_ret = prod_encode_ret'\<rparr>;
    prod_encode_ret_state = prod_encode_imp prod_encode_state;
    t = t + prod_encode_imp_time 0 prod_encode_state;
    prod_encode_result = prod_encode_ret prod_encode_ret_state;
    t = t + 2;
    var_bit_to_var_nat_n' = prod_encode_result;
    t = t + 2;
    var_bit_to_var_nat_ret' = 0;
    t = t + 2;
    var_bit_to_var_nat_state = \<lparr>var_bit_to_var_nat_n = var_bit_to_var_nat_n',
                                var_bit_to_var_nat_ret = var_bit_to_var_nat_ret'\<rparr>;
    var_bit_to_var_nat_ret_state = var_bit_to_var_nat_imp var_bit_to_var_nat_state;
    t = t + var_bit_to_var_nat_imp_time 0 var_bit_to_var_nat_state;
    var_bit_to_var_nat_result = var_bit_to_var_nat_ret var_bit_to_var_nat_ret_state;
    t = t + 2;
    cons_h' = var_bit_to_var_nat_result;
    t = t + 2;
    cons_t' = map_var_bit_to_var_acc_acc s;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h',
                  cons_t = cons_t', 
                  cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;
    cons_result = cons_ret cons_ret_state;
    t = t + 2;
    tl_xs' = map_var_bit_to_var_acc_n s;
    t = t + 2;
    tl_ret' = 0;
    t = t + 2;
    tl_state = \<lparr>tl_xs = tl_xs', 
                tl_ret = tl_ret'\<rparr>;
    tl_ret_state = tl_imp tl_state;
    t = t + tl_imp_time 0 tl_state;
    tl_result = tl_ret tl_ret_state;
    t = t + 2;
    map_var_bit_to_var_acc_acc' = cons_result;
    t = t + 2;
    map_var_bit_to_var_acc_v' = map_var_bit_to_var_acc_v s;
    t = t + 2;
    map_var_bit_to_var_acc_n' = tl_result;
    t = t + 2;
    map_var_bit_to_var_acc_ret' = map_var_bit_to_var_acc_ret s;
    t = t + 2;
    ret = \<lparr>map_var_bit_to_var_acc_acc = map_var_bit_to_var_acc_acc',
           map_var_bit_to_var_acc_v = map_var_bit_to_var_acc_v',
           map_var_bit_to_var_acc_n = map_var_bit_to_var_acc_n',
           map_var_bit_to_var_acc_ret = map_var_bit_to_var_acc_ret'\<rparr>
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
    map_var_bit_to_var_acc_acc' = map_var_bit_to_var_acc_acc s;
    t = t + 2;
    map_var_bit_to_var_acc_v' = map_var_bit_to_var_acc_v s;
    t = t + 2;
    map_var_bit_to_var_acc_n' = map_var_bit_to_var_acc_n s;
    t = t + 2;
    map_var_bit_to_var_acc_ret' = map_var_bit_to_var_acc_acc s;
    t = t + 2;
    ret = \<lparr>map_var_bit_to_var_acc_acc = map_var_bit_to_var_acc_acc',
           map_var_bit_to_var_acc_v = map_var_bit_to_var_acc_v',
           map_var_bit_to_var_acc_n = map_var_bit_to_var_acc_n',
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
  by (auto simp add: map_var_bit_to_var_acc_imp_subprogram_time_simps tl_imp_correct)

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
abbreviation "map_var_bit_to_var_acc_hd_result \<equiv> ''hd_result''"
abbreviation "map_var_bit_to_var_acc_prod_encode_result \<equiv> ''prod_encode_result''"
abbreviation "map_var_bit_to_var_acc_var_bit_to_var_nat_result \<equiv> ''var_bit_to_var_nat_result''"
abbreviation "map_var_bit_to_var_acc_cons_result \<equiv> ''cons_result''"
abbreviation "map_var_bit_to_var_acc_tl_result \<equiv> ''tl_result''"

definition "map_var_bit_to_var_acc_IMP_init_while_cond \<equiv>
  \<comment> \<open>condition = map_var_bit_to_var_acc_n s\<close>
  map_var_bit_to_var_acc_while_cond ::= A (V map_var_bit_to_var_acc_n_str)
"

definition "map_var_bit_to_var_acc_IMP_loop_body \<equiv>
  \<comment> \<open>hd_xs' = map_var_bit_to_var_acc_n s;\<close>
  (hd_prefix @ hd_xs_str) ::= (A (V map_var_bit_to_var_acc_n_str));;
  \<comment> \<open>hd_ret' = 0;\<close>
  (hd_prefix @ hd_ret_str) ::= (A (N 0));;
  \<comment> \<open>hd_state = \<lparr>hd_xs = hd_xs',\<close>
  \<comment> \<open>            hd_ret = hd_ret'\<rparr>;\<close>
  \<comment> \<open>hd_ret_state = hd_imp hd_state;\<close>
  invoke_subprogram hd_prefix hd_IMP_Minus;;
  \<comment> \<open>hd_result = hd_ret hd_ret_state;\<close>
  map_var_bit_to_var_acc_hd_result ::= (A (V (hd_prefix @ hd_ret_str)));;
  \<comment> \<open>prod_encode_a' = map_var_bit_to_var_acc_v s;\<close>
  (prod_encode_prefix @ prod_encode_a_str) ::= (A (V map_var_bit_to_var_acc_v_str));;
  \<comment> \<open>prod_encode_b' = hd_result;\<close>
  (prod_encode_prefix @ prod_encode_b_str) ::= (A (V map_var_bit_to_var_acc_hd_result));;
  \<comment> \<open>prod_encode_ret' = 0;\<close>
  (prod_encode_prefix @ prod_encode_ret_str) ::= (A (N 0));;
  \<comment> \<open>prod_encode_state = \<lparr>prod_encode_a = prod_encode_a',\<close>
  \<comment> \<open>                     prod_encode_b = prod_encode_b',\<close>
  \<comment> \<open>  prod_encode_ret = prod_encode_ret'\<rparr>;\<close>
  \<comment> \<open>prod_encode_ret_state = prod_encode_imp prod_encode_state;\<close>
  invoke_subprogram prod_encode_prefix prod_encode_IMP_Minus;;
  \<comment> \<open>prod_encode_result = prod_encode_ret prod_encode_ret_state;\<close>
  map_var_bit_to_var_acc_prod_encode_result ::= (A (V (prod_encode_prefix @ prod_encode_ret_str)));;
  \<comment> \<open>var_bit_to_var_nat_n' = prod_encode_result;\<close>
  (var_bit_to_var_nat_prefix @ var_bit_to_var_nat_n_str) ::= (A (V map_var_bit_to_var_acc_prod_encode_result));;
  \<comment> \<open>var_bit_to_var_nat_ret' = 0;\<close>
  (var_bit_to_var_nat_prefix @ var_bit_to_var_nat_ret_str) ::= (A (N 0));;
  \<comment> \<open>var_bit_to_var_nat_state = \<lparr>var_bit_to_var_nat_n = var_bit_to_var_nat_n',\<close>
  \<comment> \<open>                            var_bit_to_var_nat_ret = var_bit_to_var_nat_ret'\<rparr>;\<close>
  \<comment> \<open>var_bit_to_var_nat_ret_state = var_bit_to_var_nat_imp var_bit_to_var_nat_state;\<close>
  invoke_subprogram var_bit_to_var_nat_prefix var_bit_to_var_nat_IMP_Minus;;
  \<comment> \<open>var_bit_to_var_nat_result = var_bit_to_var_nat_ret var_bit_to_var_nat_ret_state;\<close>
  map_var_bit_to_var_acc_var_bit_to_var_nat_result ::= (A (V (var_bit_to_var_nat_prefix @ var_bit_to_var_nat_ret_str)));;
  \<comment> \<open>cons_h' = var_bit_to_var_nat_result;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V map_var_bit_to_var_acc_var_bit_to_var_nat_result));;
  \<comment> \<open>cons_t' = map_var_bit_to_var_acc_acc s;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V map_var_bit_to_var_acc_acc_str));;
  \<comment> \<open>cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>cons_state = \<lparr>cons_h = cons_h',\<close>
  \<comment> \<open>              cons_t = cons_t', \<close>
  \<comment> \<open>              cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>cons_ret_state = cons_imp cons_state;\<close>
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  \<comment> \<open>cons_result = cons_ret cons_ret_state;\<close>
  map_var_bit_to_var_acc_cons_result ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>tl_xs' = map_var_bit_to_var_acc_n s;\<close>
  (tl_prefix @ tl_xs_str) ::= (A (V map_var_bit_to_var_acc_n_str));;
  \<comment> \<open>tl_ret' = 0;\<close>
  (tl_prefix @ tl_ret_str) ::= (A (N 0));;
  \<comment> \<open>tl_state = \<lparr>tl_xs = tl_xs', \<close>
  \<comment> \<open>            tl_ret = tl_ret'\<rparr>;\<close>
  \<comment> \<open>tl_ret_state = tl_imp tl_state;\<close>
  invoke_subprogram tl_prefix tl_IMP_Minus;;
  \<comment> \<open>tl_result = tl_ret tl_ret_state;\<close>
  map_var_bit_to_var_acc_tl_result ::= (A (V (tl_prefix @ tl_ret_str)));;
  \<comment> \<open>map_var_bit_to_var_acc_acc' = cons_result;\<close>
  (map_var_bit_to_var_acc_acc_str) ::= (A (V map_var_bit_to_var_acc_cons_result));;
  \<comment> \<open>map_var_bit_to_var_acc_v' = map_var_bit_to_var_acc_v s;\<close>
  (map_var_bit_to_var_acc_v_str) ::= (A (V map_var_bit_to_var_acc_v_str));;
  \<comment> \<open>map_var_bit_to_var_acc_n' = tl_result;\<close>
  (map_var_bit_to_var_acc_n_str) ::= (A (V map_var_bit_to_var_acc_tl_result));;
  \<comment> \<open>map_var_bit_to_var_acc_ret' = map_var_bit_to_var_acc_ret s;\<close>
  (map_var_bit_to_var_acc_ret_str) ::= (A (V map_var_bit_to_var_acc_ret_str))
  \<comment> \<open>ret = \<lparr>map_var_bit_to_var_acc_acc = map_var_bit_to_var_acc_acc',\<close>
  \<comment> \<open>       map_var_bit_to_var_acc_v = map_var_bit_to_var_acc_v',\<close>
  \<comment> \<open>       map_var_bit_to_var_acc_n = map_var_bit_to_var_acc_n',\<close>
  \<comment> \<open>       map_var_bit_to_var_acc_ret = map_var_bit_to_var_acc_ret'\<rparr>\<close>
"

definition "map_var_bit_to_var_acc_IMP_after_loop \<equiv>
  \<comment> \<open>map_var_bit_to_var_acc_acc' = map_var_bit_to_var_acc_acc s;\<close>
  (map_var_bit_to_var_acc_acc_str) ::= (A (V map_var_bit_to_var_acc_cons_result));;
  \<comment> \<open>map_var_bit_to_var_acc_v' = map_var_bit_to_var_acc_v s;\<close>
  (map_var_bit_to_var_acc_v_str) ::= (A (V map_var_bit_to_var_acc_v_str));;
  \<comment> \<open>map_var_bit_to_var_acc_n' = map_var_bit_to_var_acc_n s;\<close>
  (map_var_bit_to_var_acc_n_str) ::= (A (V map_var_bit_to_var_acc_tl_result));;
  \<comment> \<open>map_var_bit_to_var_acc_ret' = map_var_bit_to_var_acc_acc s;\<close>
  (map_var_bit_to_var_acc_ret_str) ::= (A (V map_var_bit_to_var_acc_cons_result))
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
  {map_var_bit_to_var_acc_while_cond, map_var_bit_to_var_acc_hd_result,
    map_var_bit_to_var_acc_prod_encode_result, map_var_bit_to_var_acc_var_bit_to_var_nat_result,
    map_var_bit_to_var_acc_cons_result, map_var_bit_to_var_acc_tl_result}"

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
  hd_imp_to_HOL_state_def
  prod_encode_imp_to_HOL_state_def
  var_bit_to_var_nat_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  tl_imp_to_HOL_state_def

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
    apply(simp only: map_var_bit_to_var_acc_IMP_subprogram_simps prefix_simps)
    apply(erule Seq_E)+
    apply(fastforce_sorted_premises2 simp: map_var_bit_to_var_acc_IMP_subprogram_simps
        map_var_bit_to_var_acc_imp_subprogram_simps
        map_var_bit_to_var_acc_state_translators)

  apply(erule Seq_E)+
  apply(dest_com_gen)

  subgoal
      apply(simp only: map_var_bit_to_var_acc_IMP_init_while_cond_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule <?>_IMP_Minus_correct[where vars = "map_var_bit_to_var_acc_IMP_vars"])
      subgoal premises p using p(999) by fastforce
      by(fastforce simp add: map_var_bit_to_var_acc_complete_simps)

  subgoal
      apply(subst (asm) map_var_bit_to_var_acc_IMP_init_while_cond_def)
      apply(simp only: map_var_bit_to_var_acc_IMP_loop_body_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule <?>_IMP_Minus_correct[where vars = "map_var_bit_to_var_acc_IMP_vars"])
      subgoal premises p using p(999) by fastforce
      by (simp only: map_var_bit_to_var_acc_imp_subprogram_simps
          map_var_bit_to_var_acc_state_translators Let_def, force)

  subgoal
      apply(simp only: map_var_bit_to_var_acc_IMP_init_while_cond_def prefix_simps
          map_var_bit_to_var_acc_IMP_loop_body_def)
      apply(erule Seq_E)+
      apply(erule <?>_IMP_Minus_correct[where vars = "map_var_bit_to_var_acc_IMP_vars"])
      subgoal premises p using p(999) by fastforce
      by (simp only: map_var_bit_to_var_acc_imp_subprogram_simps
          map_var_bit_to_var_acc_state_translators Let_def, force)
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
    apply(simp only: map_var_bit_to_var_acc_IMP_subprogram_simps prefix_simps)
    apply(erule Seq_tE)+
    apply(erule <?>_IMP_Minus_correct[where vars = "map_var_bit_to_var_acc_IMP_vars"])
    subgoal premises p using p(999) by fastforce
    by (force simp: map_var_bit_to_var_acc_IMP_subprogram_simps
        map_var_bit_to_var_acc_imp_subprogram_time_simps map_var_bit_to_var_acc_state_translators)

  apply(erule Seq_tE)+
  apply(simp add: add.assoc)
  apply(dest_com_gen_time)

  subgoal
    apply(simp only: map_var_bit_to_var_acc_IMP_init_while_cond_def prefix_simps)
    apply(erule Seq_tE)+
    apply(erule <?>_IMP_Minus_correct[where vars = "map_var_bit_to_var_acc_IMP_vars"])
    subgoal premises p using p(999) by fastforce
    by(fastforce simp add: map_var_bit_to_var_acc_complete_simps)

  subgoal
    apply(subst (asm) map_var_bit_to_var_acc_IMP_init_while_cond_def)
    apply(simp only: map_var_bit_to_var_acc_IMP_loop_body_def prefix_simps)
    apply(erule Seq_tE)+
    apply(erule <?>_IMP_Minus_correct[where vars = "map_var_bit_to_var_acc_IMP_vars"])
    subgoal premises p using p(999) by fastforce
    by (simp only: map_var_bit_to_var_acc_imp_subprogram_time_simps
        map_var_bit_to_var_acc_state_translators Let_def, force)

  subgoal
    apply(simp only: prefix_simps map_var_bit_to_var_acc_IMP_init_while_cond_def
        map_var_bit_to_var_acc_IMP_loop_body_def)
    apply(erule Seq_tE)+
    apply(erule <?>_IMP_Minus_correct[where vars = "map_var_bit_to_var_acc_IMP_vars"])
    subgoal premises p using p(999) by fastforce
    apply(simp only: map_var_bit_to_var_acc_complete_time_simps Let_def)
    by force

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



end