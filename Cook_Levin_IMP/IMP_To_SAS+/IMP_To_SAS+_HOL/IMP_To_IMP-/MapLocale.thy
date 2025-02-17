
theory MapLocale
  imports Primitives_IMP
    "HOL-Eisbach.Eisbach"
begin

(* Mostly for testing, remove *)
method remove_assign = (assign_step+)?
(* Part of Alexander's propagate state thingy *)
method unfold_stuff uses state_translators = 
    unfold List.append.assoc let_function_correctness state_simps state_translators

(* Not tail-rec, create it *)
fun map_nat_tail' :: "(nat\<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "map_nat_tail' f n acc = (if n = 0 then acc else (map_nat_tail' f (tl_nat n)) (cons (f (hd_nat n)) acc))"

lemma map_nat_tail'_corr: "map_nat_tail' f xs acc = append_nat (reverse_nat (map_nat f xs)) acc"
  apply(induct f xs acc rule: map_nat_tail'.induct)
  by (smt (verit) Zero_not_Suc append_acc.elims append_nat.elims append_nat_0 append_nat_rev_acc cons_Nil hd_cons map_nat.elims map_nat_tail'.elims reverse_nat_0 tl_cons)

definition "map_nat_tail f n = reverse_nat (map_nat_tail' f n 0)" 

lemma map_nat_tail_corr: "map_nat_tail f n = map_nat f n"
  using append_nat_0 map_nat_tail'_corr map_nat_tail_def rev_rev_nat by presburger

(* For the stopper hack *)

lemma stopper_works: "s \<noteq> [] \<Longrightarrow> p \<noteq> []\<Longrightarrow> hd s \<notin> set p \<Longrightarrow> \<not> prefix p s" 
  by (metis hd_append2 list.set_sel(1) prefix_def)

locale map_imp =
  fixes f :: "nat \<Rightarrow> nat"

  (* I assume here that there is one input and one output var. Maybe I can generalize this to
    lists of those to *)
  (* state, in this case simple, in general more difficult, 
    find needed variables in record by analysis of tl-rec f *)
  fixes f_imp_state_in :: "'a \<Rightarrow> nat"
  fixes f_imp_state_out :: "'a \<Rightarrow> nat"
  fixes f_imp_state :: "nat \<Rightarrow> nat \<Rightarrow> 'a"

  (* Properties of state, usually provided by record/datatype package *)
  (* These are different from the usual record provided simps, are they enough? *)
  assumes f_imp_state_in[simp, state_simps]: "f_imp_state_in (f_imp_state in' out) = in'"
  assumes f_imp_state_out[simp, state_simps]: "f_imp_state_out (f_imp_state in' out) = out"
  assumes f_imp_state[simp, state_simps]: "f_imp_state (f_imp_state_in s) (f_imp_state_out s) = s"

  (* Do I even need those? Should they not be independent from this? *)

  (* Program on HOL level, should be translated from tl-rec f. Probably follow the _state_upd approach though *)
  fixes f_imp :: "'a \<Rightarrow> 'a"

  (* Timing function, generated from f_imp *)
  fixes f_imp_time :: "nat \<Rightarrow> 'a \<Rightarrow> nat"
  
  (* Correctness of f, more complicated in general, proof hopefully fairly automatic *)
  assumes f_imp_correct[let_function_correctness]: "f_imp_state_out (f_imp s) = f (f_imp_state_in s)"

  (* Pull out accumulator, maybe define without directly? Provable from from f_imp_time definition, nothing special *)
  assumes f_imp_time_acc: "f_imp_time (Suc t) s = Suc (f_imp_time t s)"

  (* Variable names occuring in IMP program, of course more general for others,
    note that there might be internal vars not in the record(Which are not relevant, input/output)
    Should be generateable from f_imp 
    prefix str without . for now
  *)
  fixes f_pref_str :: string
  fixes f_in_str :: string
  fixes f_out_str :: string
  assumes f_in_str_f_out_str[simp]: "f_in_str \<noteq> f_out_str"
  assumes f_pref_string_present[simp]: "f_pref_str \<noteq> []"

  (* Dirty hack to allow arbitrary prefixes: User has to provide a symbol that makes sure there 
    prefix does not conflict with variable names in locale. An alternative would be to expose the
    internal variable names...
  *)
  fixes stopper :: char
  assumes stopper[simp]: "stopper \<notin> set f_pref_str"
  (* IMP_MINUS version of f_imp, translate from f_imp *)
  fixes f_IMP :: "Com.com"
  (* Extract record from IMP state, generate from record *)
  fixes f_imp_to_HOL_state :: "string \<Rightarrow> AExp.state \<Rightarrow> 'a"

  (* Provable from from f_imp_to_HOL_state definition, nothing special *)
  assumes f_imp_to_HOL_state_def: 
    "f_imp_to_HOL_state p S = f_imp_state (S (add_prefix p f_in_str)) (S (add_prefix p f_out_str))"

  (* Final desired correctness result, for the proof we probably need functional/timing correctness lemmas in between
    Also should be fairly automatic, correctness part of statement is of course more general in other cases,

    proof should again be hopefully fairly automatic, problem is runtime
  *)
  assumes f_IMP_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) f_IMP, S) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = f_imp_time 0 (f_imp_to_HOL_state (p1 @ p2) S);
      s' (add_prefix (p1 @ p2) f_out_str) = 
        f_imp_state_out (f_imp (f_imp_to_HOL_state (p1 @ p2) S));
      \<And>v. v \<in> vars \<Longrightarrow> S (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
begin

lemma f_imp_state_in_f_imp_to_HOL_state: "f_imp_state_in (f_imp_to_HOL_state p S) = S (add_prefix p f_in_str)"
  by (simp add: f_imp_to_HOL_state_def)
lemma f_imp_state_out_f_imp_to_HOL_state: "f_imp_state_out (f_imp_to_HOL_state p S) = S (add_prefix p f_out_str)"
  by (simp add: f_imp_to_HOL_state_def)

(* No need to put this in interface *)
lemma f_imp_to_HOL_state_add_prefix: 
  "f_imp_to_HOL_state (add_prefix p1 p2) S = f_imp_to_HOL_state p2 (S o (add_prefix p1))" 
  by (simp add: f_imp_to_HOL_state_def)

(* Setup for alexander's tool. Is this correct? *)
declare
  arg_cong[where f=f_imp_state, state_congs]
  arg_cong[where f=f_imp_state_in, state_congs]
  arg_cong[where f=f_imp_state_out, state_congs]
  arg_cong[where f=f, let_lemmas]

(* 
lemma "fst'_state_p_update ?fst'_state_p' \<lparr>fst'_state_p = ?fst'_state_p, \<dots> = ?more\<rparr> =
  \<lparr>fst'_state_p = ?fst'_state_p' ?fst'_state_p, \<dots> = ?more\<rparr>"
 *)
thm f_imp_state f_imp_state_in f_imp_state_out

(* If I create a general locale struture for this, I can get theorems like this directly on the user level *)
lemma f_imp_time_acc': "f_imp_time t s = t + f_imp_time 0 s"
  by (induction t arbitrary: s) (simp_all add: f_imp_time_acc)

(* Record package not localized :( In this case I can just use a datatype instead,
  why still records btw? is there any reason? *)
datatype map'_f_state = map'_f_state (map'_f_state_xs: nat) (map'_f_state_acc: nat)

(* Not the same as with the record ones. Are they enough? I do not have an update function for this
  type, so these should not be needed. *)
declare 
  map'_f_state.sel[state_simps] 

definition "map'_f_state_upd s = (let
    hd_xs' = map'_f_state_xs s;
    hd_ret' = 0;
    hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
    hd_state_ret = hd_imp hd_state;

    f_imp_state_in' = hd_ret hd_state_ret;
    f_imp_state_out' = 0;
    f_imp_state = f_imp_state f_imp_state_in' f_imp_state_out';
    f_imp_state_ret = f_imp f_imp_state;

    cons_h' = f_imp_state_out f_imp_state_ret;
    cons_t' = map'_f_state_acc s;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', 
      cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    map'_f_state_acc = cons_ret cons_ret_state;

    tl_xs' = map'_f_state_xs s;
    tl_ret' = 0;
    tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
    tl_state_ret = tl_imp tl_state;

    map'_f_state_xs = tl_ret tl_state_ret;

    ret = map'_f_state map'_f_state_xs map'_f_state_acc
  in
    ret)
"

definition "map'_f_compute_loop_condition s \<equiv>
  (let
    condition = map'_f_state_xs s
   in condition
  )"

definition "map'_f_after_loop s \<equiv>
  (let
    ret = s
   in ret
  )"

lemmas map'_f_imp_subprogram_simps =
  map'_f_after_loop_def
  map'_f_state_upd_def
  map'_f_compute_loop_condition_def

function map'_f_imp:: "map'_f_state \<Rightarrow> map'_f_state" where
  "map'_f_imp s =
  (if map'_f_compute_loop_condition s \<noteq> 0
   then
    (let next_iteration = map'_f_imp (map'_f_state_upd s)
      in next_iteration)
  else
    (let ret = map'_f_after_loop s in ret)
  )"
  by simp+
termination by (relation "measure (\<lambda>s. map'_f_state_xs s)")
   (simp add: tl_imp_correct hd_imp_correct cons_imp_correct
     Let_def map'_f_imp_subprogram_simps)+

declare map'_f_imp.simps [simp del]

(* TODO: Do properly *)
lemma map'_f_imp_correct[let_function_correctness]:
  "map'_f_state_acc (map'_f_imp s)
    = map_nat_tail' f (map'_f_state_xs s) (map'_f_state_acc s)"
  apply (induction s rule: map'_f_imp.induct)
  apply (subst map'_f_imp.simps)
  apply (subst map_nat_tail'.simps)
  apply (simp add: cons_imp_correct tl_imp_correct hd_imp_correct f_imp_correct
      Let_def map'_f_imp_subprogram_simps)
  done

definition "map'_f_state_upd_time t s = (let

    hd_xs' = map'_f_state_xs s;
    t = t + 2;
    hd_ret' = 0;
    t = t + 2;
    hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
    hd_state_ret = hd_imp hd_state;
    t = t + hd_imp_time 0 hd_state;

    f_imp_state_in' = hd_ret hd_state_ret;
    t = t + 2;
    f_imp_state_out' = 0;
    t = t + 2;
    f_imp_state = f_imp_state f_imp_state_in' f_imp_state_out';
    f_imp_state_ret = f_imp f_imp_state;
    t = t + f_imp_time 0 f_imp_state;

    cons_h' = f_imp_state_out f_imp_state_ret;
    t = t + 2;
    cons_t' = map'_f_state_acc s;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', 
      cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    map'_f_state_acc = cons_ret cons_ret_state;
    t = t + 2;

    tl_xs' = map'_f_state_xs s;
    t = t + 2;
    tl_ret' = 0;
    t = t + 2;
    tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
    tl_state_ret = tl_imp tl_state;
    t = t + tl_imp_time 0 tl_state;
    map'_f_state_xs = tl_ret tl_state_ret;
    t = t + 2;

    ret = t
  in
    ret)
"

(* This seems to be the current format, somehwat superflous here*)
definition "map'_f_compute_loop_condition_time t s \<equiv>
  (let
    condition = map'_f_state_xs s;
    t = t + 2;
    ret = t
   in ret
  )"

definition "map'_f_after_loop_time t s \<equiv>
  (let
    t = t + 2;
    ret = t
   in ret
  )"

function map'_f_imp_time:: "nat \<Rightarrow> map'_f_state \<Rightarrow> nat" where
  "map'_f_imp_time t s =
  map'_f_compute_loop_condition_time 0 s +
  (if map'_f_compute_loop_condition s \<noteq> 0
   then
    (let
        t = t + 1;
        next_iteration
          = map'_f_imp_time (t + map'_f_state_upd_time 0 s)
                                     (map'_f_state_upd s)
     in next_iteration)
  else
    (let
        t = t + 2;
        ret = t + map'_f_after_loop_time 0 s
     in ret)
  )"
  by auto
termination
  by (relation "measure (\<lambda>(t,s). map'_f_state_xs s)")
    (simp add: tl_imp_correct hd_imp_correct cons_imp_correct 
      f_imp_correct Let_def map'_f_imp_subprogram_simps)+

lemmas map'_f_subprogram_time_simps =
  map'_f_imp_subprogram_simps
  map'_f_after_loop_time_def
  map'_f_state_upd_time_def
  map'_f_compute_loop_condition_time_def

lemmas [simp del] = map'_f_imp_time.simps

lemma map'_f_imp_time_acc:
  "(map'_f_imp_time (Suc t) s) = Suc (map'_f_imp_time t s)"
  by (induction t s rule: map'_f_imp_time.induct)
    ((subst (1 2) map'_f_imp_time.simps); simp)

lemma map'_f_imp_time_acc_2_aux:
  "(map'_f_imp_time t s) =
    t + (map'_f_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: map'_f_imp_time_acc)+

lemma map'_f_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (map'_f_imp_time t s) =
    t + (map'_f_imp_time 0 s)"
  by (rule map'_f_imp_time_acc_2_aux)

lemma map'_f_imp_time_acc_3:
  "(map'_f_imp_time (a + b) s) =
    a + (map'_f_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: map'_f_imp_time_acc)+



(* Names in program, note that I need to differentiate different instance *)
abbreviation "map'_f_pref_str \<equiv> stopper # ''map'_f_'' @  f_pref_str @ ''.''"
abbreviation "map'_f_xs_str \<equiv> stopper # ''xs''"
abbreviation "map'_f_acc_str \<equiv> stopper # ''acc''"


abbreviation "map'_f_while_cond \<equiv> stopper # ''condition''"

definition "map'_f_IMP_init_while_cond \<equiv>
  map'_f_while_cond ::= (A (V map'_f_xs_str))"

thm map'_f_state_upd_def

definition "map'_f_IMP_loop_body \<equiv>

  (hd_prefix @ hd_xs_str) ::= (A (V map'_f_xs_str));;
  (hd_prefix @ hd_ret_str) ::= (A (N 0));;
  invoke_subprogram hd_prefix hd_IMP;;

  (f_pref_str @ f_in_str) ::= (A (V (hd_prefix @ hd_ret_str)));;
  (f_pref_str @ f_out_str) ::= (A (N 0));;
  invoke_subprogram f_pref_str f_IMP;;

  (cons_prefix @ cons_h_str) ::= (A (V (f_pref_str @ f_out_str)));;
  (cons_prefix @ cons_t_str) ::= (A (V map'_f_acc_str));;
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  invoke_subprogram cons_prefix cons_IMP;;

  (map'_f_acc_str) ::= (A (V (cons_prefix @ cons_ret_str)));;

  (tl_prefix @ tl_xs_str) ::= (A (V map'_f_xs_str));;
  (tl_prefix @ tl_ret_str) ::= (A (N 0));;
  invoke_subprogram tl_prefix tl_IMP;;
  (map'_f_xs_str) ::= (A (V (tl_prefix @ tl_ret_str)))
"

definition "map'_f_IMP_after_loop \<equiv>
  (map'_f_acc_str) ::= (A (V map'_f_acc_str))"

definition map'_f_IMP where
  "map'_f_IMP \<equiv>
  map'_f_IMP_init_while_cond;;
  WHILE map'_f_while_cond \<noteq>0 DO (
    map'_f_IMP_loop_body;;
    map'_f_IMP_init_while_cond
  );;
  map'_f_IMP_after_loop"

abbreviation
  "map'_f_IMP_vars \<equiv>
  {map'_f_xs_str, map'_f_acc_str}"

lemma prefix_map'_f_IMP_vars[simp, dest]: "\<And>v . v \<in> map'_f_IMP_vars \<Longrightarrow> \<not> prefix f_pref_str v"
  using f_pref_string_present stopper by (auto simp add: stopper_works)
lemma prefix_map'_f_IMP_vars'[simp, dest]: "\<And>v . v \<in> map'_f_IMP_vars \<Longrightarrow> f_pref_str \<noteq> v"
  using f_pref_string_present stopper by fastforce

lemmas map'_f_IMP_subprogram_simps =
  map'_f_IMP_init_while_cond_def
  map'_f_IMP_loop_body_def
  map'_f_IMP_after_loop_def

definition "map'_f_imp_to_HOL_state p s = map'_f_state
  (s (add_prefix p map'_f_xs_str)) 
  (s (add_prefix p map'_f_acc_str))
"

lemmas map'_f_state_translators =
  f_imp_to_HOL_state_def
  hd_imp_to_HOL_state_def
  tl_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  map'_f_imp_to_HOL_state_def

lemmas map'_f_complete_simps =
  map'_f_IMP_subprogram_simps
  map'_f_imp_subprogram_simps
  map'_f_state_translators


lemma cond_elim: "(\<And>v . v \<in> insert w W \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)) 
  \<Longrightarrow> (s (add_prefix p w) = s' (add_prefix p w) \<Longrightarrow> (\<And>v . v \<in> W \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)) \<Longrightarrow> P)
  \<Longrightarrow> P"
  by auto

lemma s: "v = map'_f_xs_str \<or> v = map'_f_acc_str \<Longrightarrow> v \<noteq> CHR ''t'' # CHR ''l'' # CHR ''.'' # tl_ret_str" 
  by auto
lemma s': "v = map'_f_xs_str \<or> v = map'_f_acc_str \<Longrightarrow> v \<noteq> CHR ''t'' # CHR ''l'' # CHR ''.'' # append_nat_xs_str" 
  by auto

term reverse_nat_acc_state.make
(*This might be problematic, as the behaviour should not depend on ret, yet we might still propagate it
  Otherwise it might be needed
*)
lemma reverse_nat_acc_state_cong[let_lemmas]: "a = x \<Longrightarrow> b = y \<Longrightarrow> c = z \<Longrightarrow> 
  \<lparr>reverse_nat_acc_acc = a, reverse_nat_acc_n = b, reverse_nat_acc_ret = c\<rparr> =
  \<lparr>reverse_nat_acc_acc = x, reverse_nat_acc_n = y, reverse_nat_acc_ret = z\<rparr>"
  by (rule arg_cong3)

declare 
  reverse_nat_acc_state.simps[state_simps]


declare arg_cong2[where f=reverse_nat_acc, let_lemmas]

(* Proofs are horrible for now, at least it passes.. *)


lemma map'_f_state_cong[let_lemmas]: "a = x \<Longrightarrow> b = y \<Longrightarrow> 
  map'_f_state a b = map'_f_state x y"
  by (rule arg_cong2)

lemma neq_prefix_imp_test[simp, intro]: "\<not> prefix x z \<Longrightarrow> add_prefix x y \<noteq> z"
  by auto
lemma map'_f_IMP_correct_function:
  "(invoke_subprogram p map'_f_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p map'_f_acc_str)
      = map'_f_state_acc (map'_f_imp (map'_f_imp_to_HOL_state p s))"
  apply(induction "map'_f_imp_to_HOL_state p s" arbitrary: s s' t
      rule: map'_f_imp.induct)
  apply(subst map'_f_imp.simps)

  apply(simp only: map'_f_IMP_def prefix_simps)
  apply(vcg map'_f_IMP_vars)

  subgoal
    apply(subst (asm) (3) map'_f_IMP_init_while_cond_def)
    apply(subst (asm) (2) map'_f_IMP_after_loop_def)
    apply(simp only: prefix_simps)
    by(fastforce simp: map'_f_complete_simps)

  subgoal
    apply(subst (asm) (1) map'_f_IMP_init_while_cond_def)
    apply(simp only: prefix_simps)
    by(fastforce simp: Let_def map'_f_complete_simps)

  subgoal for s s' t x s2 y xa s2a ya x' s2b yb xb s2c yc
    apply(subst (asm) (1) map'_f_IMP_init_while_cond_def)
    apply(subst (asm) (1) map'_f_IMP_loop_body_def)
    apply(simp only: prefix_simps)
    apply(vcg map'_f_IMP_vars functional_correctness: f_IMP_correct)
    apply (unfold map'_f_complete_simps Let_def)
    by (propagate_state_pipeline p state_translators: 
     map'_f_state_translators)

  (* Does the third subgoal here always follow directly from the first two? *)
  subgoal premises p for s s' t x s2 y xa s2a ya x' s2b yb xb s2c yc 
  proof-
    have 1: "map'_f_compute_loop_condition (map'_f_imp_to_HOL_state p s) \<noteq> 0" 
      using p(2,3) 
      using \<open>\<And>yc y xb xa sa s2c s2b s2a s2 s'a. \<lbrakk>(invoke_subprogram p map'_f_IMP_after_loop, s2) \<Rightarrow>\<^bsup> y \<^esup> s'a; (invoke_subprogram p map'_f_IMP_init_while_cond, sa) \<Rightarrow>\<^bsup> xa \<^esup> s2a; 0 < s2a (add_prefix p map'_f_while_cond); (invoke_subprogram p map'_f_IMP_loop_body, s2a) \<Rightarrow>\<^bsup> xb \<^esup> s2c; (invoke_subprogram p map'_f_IMP_init_while_cond, s2c) \<Rightarrow>\<^bsup> yc \<^esup> s2b\<rbrakk> \<Longrightarrow> map'_f_compute_loop_condition (map'_f_imp_to_HOL_state p sa) \<noteq> 0\<close> p(1) p(4) p(5) by blast
    have 2: " (map'_f_state_upd (map'_f_imp_to_HOL_state p s))
      =  (map'_f_imp_to_HOL_state p s2c)"
      using p
          \<open>\<And>yc y xb xa sa s2c s2b s2a s2 s'a. \<lbrakk>(invoke_subprogram p map'_f_IMP_after_loop, s2) \<Rightarrow>\<^bsup> y \<^esup> s'a; (invoke_subprogram p map'_f_IMP_init_while_cond, sa) \<Rightarrow>\<^bsup> xa \<^esup> s2a; 0 < s2a (add_prefix p map'_f_while_cond); (invoke_subprogram p map'_f_IMP_loop_body, s2a) \<Rightarrow>\<^bsup> xb \<^esup> s2c; (invoke_subprogram p map'_f_IMP_init_while_cond, s2c) \<Rightarrow>\<^bsup> yc \<^esup> s2b\<rbrakk> \<Longrightarrow> map'_f_state_upd (map'_f_imp_to_HOL_state p sa) = map'_f_imp_to_HOL_state p s2c\<close>  by blast
    show ?thesis 
      using "1" "2" by presburger
  qed
  done


lemma map'_f_IMP_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ map'_f_pref) map'_f_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix map'_f_pref v)\<rbrakk>
  \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma map'_f_IMP_correct_time_loop_condition:
  "(invoke_subprogram p map'_f_IMP_init_while_cond, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = map'_f_compute_loop_condition_time 0 (map'_f_imp_to_HOL_state p s)"
  by (subst map'_f_compute_loop_condition_time_def)
    (auto simp: map'_f_IMP_init_while_cond_def)

lemmas map'_f_complete_time_simps =
  map'_f_subprogram_time_simps
  map'_f_imp_time_acc_2
  map'_f_imp_time_acc_3
  map'_f_state_translators

lemma map'_f_IMP_correct_time:
  "(invoke_subprogram p map'_f_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = map'_f_imp_time 0 (map'_f_imp_to_HOL_state p s)"
  apply(induction "map'_f_imp_to_HOL_state p s" arbitrary: s s' t
      rule: map'_f_imp.induct)
  apply(subst map'_f_imp_time.simps)
  apply(simp only: map'_f_IMP_def prefix_simps)
  apply(vcg_time map'_f_IMP_vars)

  subgoal
    apply(subst (asm) (3) map'_f_IMP_init_while_cond_def)
    apply(subst (asm) (2) map'_f_IMP_after_loop_def)
    apply(simp only: prefix_simps)
    by (fastforce simp: map'_f_subprogram_time_simps
        map'_f_state_translators)

  apply(simp add: add.assoc)
  apply(vcg_time map'_f_IMP_vars)

  subgoal
    apply(subst (asm) (1) map'_f_IMP_init_while_cond_def)
    apply(simp only: prefix_simps)
    by(fastforce simp: Let_def map'_f_complete_simps)

  subgoal
    apply(subst (asm) (1) map'_f_IMP_init_while_cond_def)
    apply(subst (asm) (1) map'_f_IMP_loop_body_def)
    apply(simp only: prefix_simps)
    apply(vcg map'_f_IMP_vars functional_correctness: f_IMP_correct)

    apply (simp add: f_imp_correct hd_imp_correct tl_imp_correct cons_imp_correct map'_f_complete_simps)
    apply safe
    subgoal apply simp 
      (* Some problem with the stopper and prefixes... I do not know why yet... *)
      by (smt (z3) append_Nil2 append_assoc char.inject f_pref_string_present fun_upd_apply list.inject list.sel(1) prefix_def same_append_eq stopper stopper_works)
    subgoal apply simp 
      (* Some problem with the stopper and prefixes... I do not know why yet... *)
      by (smt (z3) append_Nil2 append_assoc char.inject f_pref_string_present fun_upd_apply list.inject list.sel(1) prefix_def same_append_eq stopper stopper_works)
    done

  (* Tried to exploit previous subgoals again, could not be bothered to write a real proof in the end,
  needs cleanup *)
  subgoal premises p for s s' t x s2 y xa s2a ya x' s2b yb xb s2c yc
  proof-
    show ?thesis
    proof(cases "0 < map'_f_compute_loop_condition (map'_f_imp_to_HOL_state p s) ")
      case True
      have 1: "map'_f_compute_loop_condition (map'_f_imp_to_HOL_state p s) \<noteq> 0" 
        using True by blast
      thm \<open>\<And>s s' t x s2 y xa s2a ya x' s2b yb xb s2c yc.
       t = Suc (xa + (xb + (yc + (yb + y)))) \<Longrightarrow>
       (invoke_subprogram p map'_f_IMP_after_loop, s2) \<Rightarrow>\<^bsup> y \<^esup> s' \<Longrightarrow>
       x = Suc (xa + (xb + (yc + yb))) \<Longrightarrow>
       (invoke_subprogram p map'_f_IMP_init_while_cond, s) \<Rightarrow>\<^bsup> xa \<^esup> s2a \<Longrightarrow>
       0 < s2a (add_prefix p map'_f_while_cond) \<Longrightarrow>
       ya = Suc (xb + (yc + yb)) \<Longrightarrow>
       x' = xb + yc \<Longrightarrow>
       (invoke_subprogram p map'_f_IMP_loop_body, s2a) \<Rightarrow>\<^bsup> xb \<^esup> s2c \<Longrightarrow>
       (invoke_subprogram p map'_f_IMP_init_while_cond, s2c) \<Rightarrow>\<^bsup> yc \<^esup> s2b \<Longrightarrow>
       map'_f_state_upd (map'_f_imp_to_HOL_state p s) = map'_f_imp_to_HOL_state p s2c\<close>

      have 2: " (map'_f_state_upd (map'_f_imp_to_HOL_state p s))
      =  (map'_f_imp_to_HOL_state p s2c)"
        using p
        using \<open>\<And>s s' t x s2 y xa s2a ya x' s2b yb xb s2c yc.
       t = Suc (xa + (xb + (yc + (yb + y)))) \<Longrightarrow>
       (invoke_subprogram p map'_f_IMP_after_loop, s2) \<Rightarrow>\<^bsup> y \<^esup> s' \<Longrightarrow>
       x = Suc (xa + (xb + (yc + yb))) \<Longrightarrow>
       (invoke_subprogram p map'_f_IMP_init_while_cond, s) \<Rightarrow>\<^bsup> xa \<^esup> s2a \<Longrightarrow>
       0 < s2a (add_prefix p map'_f_while_cond) \<Longrightarrow>
       ya = Suc (xb + (yc + yb)) \<Longrightarrow>
       x' = xb + yc \<Longrightarrow>
       (invoke_subprogram p map'_f_IMP_loop_body, s2a) \<Rightarrow>\<^bsup> xb \<^esup> s2c \<Longrightarrow>
       (invoke_subprogram p map'_f_IMP_init_while_cond, s2c) \<Rightarrow>\<^bsup> yc \<^esup> s2b \<Longrightarrow>
       map'_f_state_upd (map'_f_imp_to_HOL_state p s) = map'_f_imp_to_HOL_state p s2c\<close>
        by blast

      
      show ?thesis
        using p apply - 
        apply (unfold map'_f_IMP_loop_body_def map'_f_IMP_init_while_cond_def)
        apply (simp (no_asm) add: prefix_simps map'_f_state_upd_time_def)
        apply (simp only: prefix_simps)
        apply(vcg_time map'_f_IMP_vars functional_correctness: f_IMP_correct)
        apply (simp (no_asm_simp) add: Let_def )
        apply(drule AssignD)+
        apply (erule conjE)+
        apply (intro conjI impI)
          apply (remove_assign)
         apply (unfold_stuff state_translators: )
        subgoal
          apply (simp (no_asm) add: map'_f_compute_loop_condition_time_def)
          apply (subst (2) map'_f_imp_time_acc_2_aux)
          apply (subst 2)
         apply (unfold_stuff state_translators: map'_f_state_translators)
          
          apply simp
            by (smt (z3) append_eq_append_conv f_pref_string_present fun_upd_other list.inject list.sel(1)
                list.simps(3) prefixI stopper stopper_works) (* Prefixes again, I thought I have solved this... *)
          subgoal
            apply (simp (no_asm) add: map'_f_compute_loop_condition_time_def)
            apply (subst (asm) map'_f_IMP_after_loop_def)
        apply(remove_assign)
         apply (unfold_stuff state_translators: map'_f_state_translators)
          
          apply simp 
            by (metis "1" map'_f_imp_to_HOL_state_def) (* not all stuff before is not needed? *)
          done
    next
      case False
      then show ?thesis
        using p apply -
        apply (simp add: map'_f_compute_loop_condition_time_def map'_f_after_loop_time_def
            map'_f_IMP_after_loop_def map'_f_IMP_init_while_cond_def prefix_simps )
        by (meson False \<open>\<And>yc yb ya y xb xa x' x ta sa s2c s2b s2a s2 s'a. \<lbrakk>ta = Suc (xa + (xb + (yc + (yb + y)))); (invoke_subprogram p map'_f_IMP_after_loop, s2) \<Rightarrow>\<^bsup> y \<^esup> s'a; x = Suc (xa + (xb + (yc + yb))); (invoke_subprogram p map'_f_IMP_init_while_cond, sa) \<Rightarrow>\<^bsup> xa \<^esup> s2a; 0 < s2a (add_prefix p map'_f_while_cond); ya = Suc (xb + (yc + yb)); x' = xb + yc; (invoke_subprogram p map'_f_IMP_loop_body, s2a) \<Rightarrow>\<^bsup> xb \<^esup> s2c; (invoke_subprogram p map'_f_IMP_init_while_cond, s2c) \<Rightarrow>\<^bsup> yc \<^esup> s2b\<rbrakk> \<Longrightarrow> 0 < map'_f_compute_loop_condition (map'_f_imp_to_HOL_state p sa)\<close> p(2) p(4) p(9))
    qed
  qed
  done

lemma map'_f_IMP_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) map'_f_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (map'_f_imp_time 0 (map'_f_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) map'_f_acc_str) =
        map'_f_state_acc (map'_f_imp (map'_f_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using map'_f_IMP_correct_function
  by (auto simp: map'_f_IMP_correct_time)
    (meson map'_f_IMP_correct_effects set_mono_prefix)

datatype map_f_state =
  map_f_state (map_f_state_xs: nat) (map_f_state_ret: nat)

abbreviation "map_f_prefix \<equiv> stopper # ''map_f_'' @ f_pref_str @ ''.''"
abbreviation "map_f_xs_str \<equiv> stopper # ''xs''"
abbreviation "map_f_ret_str \<equiv> stopper # ''ret''"


definition "map_f_state_upd s \<equiv>
  (let
      map'_f_xs = map_f_state_xs s;
      map'_f_acc = 0;
      map'_f_state = map'_f_state map'_f_xs map'_f_acc;
      map'_f_ret = map'_f_imp map'_f_state;

      reverse_nat_n = map'_f_state_acc map'_f_ret;
      reverse_nat_ret' = 0;
      reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n, reverse_nat_ret = reverse_nat_ret'\<rparr>;
      reverse_nat_ret'' = reverse_nat_imp reverse_nat_state;
      
      map_f_ret = reverse_nat_ret reverse_nat_ret'';
      ret = map_f_state (map_f_state_xs s) map_f_ret
    in
      ret
)"

term reverse_nat_imp

function map_f_imp:: "map_f_state \<Rightarrow> map_f_state" where
  "map_f_imp s =
  (let
      ret = map_f_state_upd s
    in
      ret
  )"
  by simp+
termination
  by (relation "measure (\<lambda>s. map_f_state_xs s)") simp

lemmas [simp del] = map_f_imp.simps

lemma map_f_imp_correct[let_function_correctness]:
  "map_f_state_ret (map_f_imp s) = map_nat_tail f (map_f_state_xs s)"
  apply (subst map_f_imp.simps)
  apply (subst map_nat_tail_def)
  apply (subst Let_def)
  apply (subst map_f_state_upd_def)
  apply (subst Let_def)+
  apply (subst map'_f_imp_correct)
  by (simp add: reverse_nat_imp_correct)
  

function map_f_imp_time:: "nat \<Rightarrow> map_f_state \<Rightarrow> nat" where
  "map_f_imp_time t s =
  (let
      map'_f_xs = map_f_state_xs s;
      t = t + 2;
      map'_f_acc = 0;
      t = t + 2;
      map'_f_state = map'_f_state map'_f_xs map'_f_acc;
      map'_f_ret = map'_f_imp map'_f_state;
      t = t + map'_f_imp_time 0 map'_f_state;

      reverse_nat_n = map'_f_state_acc map'_f_ret;
      t = t + 2;
      reverse_nat_ret' = 0;
      t = t + 2;
      reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n, reverse_nat_ret = reverse_nat_ret'\<rparr>;
      reverse_nat_ret'' = reverse_nat_imp reverse_nat_state;
      t = t + reverse_nat_imp_time 0 reverse_nat_state;
      
      map_f_ret = reverse_nat_ret reverse_nat_ret'';
      t = t + 2;
      ret = t
    in
      ret
  )"
  by auto
termination
  by (relation "measure (\<lambda>(t, s). map_f_state_ret s)") simp

lemmas [simp del] = map_f_imp_time.simps

lemma map_f_imp_time_acc:
  "(map_f_imp_time (Suc t) s) = Suc (map_f_imp_time t s)"
  by (simp add: Let_def map_f_imp_time.simps reverse_nat_imp_time.simps)

lemma map_f_imp_time_acc_2:
  "(map_f_imp_time x s) = x + (map_f_imp_time 0 s)"
  by (simp add: Let_def map_f_imp_time.simps reverse_nat_imp_time.simps)

(* 
      reverse_nat_n = map'_f_state_acc map'_f_ret;
      reverse_nat_ret' = 0;
      reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n, reverse_nat_ret = reverse_nat_ret'\<rparr>;
      reverse_nat_ret'' = reverse_nat_imp reverse_nat_state;*)
definition map_f_IMP where
  "map_f_IMP \<equiv>

  (map'_f_pref_str @ map'_f_xs_str) ::= (A (V map_f_xs_str));;
  (map'_f_pref_str @ map'_f_acc_str) ::= (A (N 0));;
  invoke_subprogram map'_f_pref_str map'_f_IMP;;

  (reverse_nat_prefix @ reverse_nat_n_str) ::= A (V (map'_f_pref_str @ map'_f_acc_str));;
  (reverse_nat_prefix @ reverse_nat_ret_str) ::= A (N 0);;
  invoke_subprogram reverse_nat_prefix reverse_nat_IMP;;

  map_f_ret_str ::= (A (V (reverse_nat_prefix @ reverse_nat_ret_str)))
"

abbreviation
  "map_f_IMP_vars \<equiv>
  {map_f_xs_str, map_f_ret_str}"

definition "map_f_imp_to_HOL_state p s = map_f_state
  (s (add_prefix p map_f_xs_str))
  (s (add_prefix p map_f_ret_str))
"

lemma map_f_IMP_correct_function:
  "(invoke_subprogram p map_f_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p map_f_ret_str)
      = map_f_state_ret (map_f_imp (map_f_imp_to_HOL_state p s))"
  by (fastforce elim: map'_f_IMP_correct reverse_nat_IMP_correct simp: map_f_imp_to_HOL_state_def
      map_f_imp.simps map_f_state_upd_def map'_f_imp_to_HOL_state_def
      map_f_IMP_def 
      reverse_nat_imp_to_HOL_state_def
      invoke_subprogram_append)

lemma map_f_IMP_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ map_f_pref) map_f_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix map_f_pref v)\<rbrakk>
  \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma map_f_IMP_correct_time:
  "(invoke_subprogram p map_f_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = map_f_imp_time 0 (map_f_imp_to_HOL_state p s)"
  by (fastforce elim: map'_f_IMP_correct reverse_nat_IMP_correct simp: map_f_imp_to_HOL_state_def
      map_f_imp_time.simps map'_f_imp_to_HOL_state_def map_f_IMP_def reverse_nat_imp_to_HOL_state_def
      invoke_subprogram_append Let_def)

lemma map_f_IMP_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) map_f_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (map_f_imp_time 0 (map_f_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) map_f_ret_str) =
        map_f_state_ret (map_f_imp (map_f_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using map_f_IMP_correct_time map_f_IMP_correct_function
    map_f_IMP_correct_effects
  by (meson set_mono_prefix)

end

term snd'_imp

(* Wanted to instantiate with snd'_nat, but it only uses one variable.
  Use the same locale idea to transform functions in the expected format of the map locale
*)

locale one_var_to_two_var =
  fixes f :: "nat \<Rightarrow> nat"

  (* assume a single variable, generate one fwith seperat in 
    and output ones *)
  fixes f_imp_state_var :: "'a \<Rightarrow> nat"
  fixes f_imp_state :: "nat \<Rightarrow> 'a"

  (* Properties of state, usually provided by record/datatype package *)
  assumes f_imp_state_var[simp, state_simps]: "f_imp_state_var (f_imp_state var) = var"
  assumes f_imp_state[simp, state_simps]: "f_imp_state (f_imp_state_var s) = s"

  (* Program on HOL level, should be translated from tl-rec f. Probably follow the _state_upd approach though *)
  fixes f_imp :: "'a \<Rightarrow> 'a"
  (* Timing function, generated from f_imp *)
  fixes f_imp_time :: "nat \<Rightarrow> 'a \<Rightarrow> nat"
  
  (* Correctness of f, more complicated in general, proof hopefully fairly automatic *)
  assumes f_imp_correct[let_function_correctness]: "f_imp_state_var (f_imp s) = f (f_imp_state_var s)"

  (* Pull out accumulator, maybe define without directly? Provable from from f_imp_time definition, nothing special *)
  assumes f_imp_time_acc: "f_imp_time (Suc t) s = Suc (f_imp_time t s)"

  (* Variable names occuring in IMP program, of course more general for others,
    note that there might be internal vars not in the record(Which are not relevant, input/output)
    Should be generateable from f_imp 
    prefix str without . for now
  *)
  fixes f_pref_str :: string
  fixes f_var_str :: string
  assumes f_pref_string_present[simp]: "f_pref_str \<noteq> []"

  (* Dirty hack to allow arbitrary prefixes: User has to provide a symbol that makes sure there 
    prefix does not conflict with variable names in locale. An alternative would be to expose the
    internal variable names...
  *)
  fixes stopper :: char
  assumes stopper[simp]: "stopper \<notin> set f_pref_str"
  (* IMP_MINUS version of f_imp, translate from f_imp *)
  fixes f_IMP :: "Com.com"
  (* Extract record from IMP state, generate from record *)
  fixes f_imp_to_HOL_state :: "string \<Rightarrow> AExp.state \<Rightarrow> 'a"

  (* Provable from from f_imp_to_HOL_state definition, nothing special *)
  assumes f_imp_to_HOL_state_def: 
    "f_imp_to_HOL_state p S = f_imp_state (S (add_prefix p f_var_str))"

  (* Final desired correctness result, for the proof we probably need functional/timing correctness lemmas in between
    Also should be fairly automatic, correctness part of statement is of course more general in other cases,

    proof should again be hopefully fairly automatic, problem is runtime
  *)
  assumes f_IMP_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) f_IMP, S) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = f_imp_time 0 (f_imp_to_HOL_state (p1 @ p2) S);
      s' (add_prefix (p1 @ p2) f_var_str) = 
        f_imp_state_var (f_imp (f_imp_to_HOL_state (p1 @ p2) S));
      \<And>v. v \<in> vars \<Longrightarrow> S (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
begin

datatype one_to_two_state =
  one_to_two_state (one_to_two_state_in: nat) (one_to_two_state_out: nat)

abbreviation "one_to_two_prefix \<equiv> stopper # ''one_to_two'' @ f_pref_str @ ''.''"
abbreviation "one_to_two_in_str \<equiv> stopper # ''in''"
abbreviation "one_to_two_out_str \<equiv> stopper # ''out''"

definition "one_to_two_state_upd s \<equiv>
  (let
      f_var = one_to_two_state_in s;
      f_state = f_imp_state f_var;
      f_ret = f_imp f_state;
      one_to_two_out = f_imp_state_var f_ret;
      ret = one_to_two_state (one_to_two_state_in s) one_to_two_out
    in
      ret
)"

function one_to_two_imp:: "one_to_two_state \<Rightarrow> one_to_two_state" where
  "one_to_two_imp s =
  (let
      ret = one_to_two_state_upd s
    in
      ret
  )"
  by simp+
termination
  by (relation "measure (\<lambda>s. one_to_two_state_out s)") simp

lemmas [simp del] = one_to_two_imp.simps

lemma one_to_two_imp_correct[let_function_correctness]:
  "one_to_two_state_out (one_to_two_imp s) = f (one_to_two_state_in s)"
  by (simp add: one_to_two_imp.simps one_to_two_state_upd_def Let_def f_imp_correct)

function one_to_two_imp_time:: "nat \<Rightarrow> one_to_two_state \<Rightarrow> nat" where
  "one_to_two_imp_time t s =
  (let
      f_var = one_to_two_state_in s;
      t = t + 2;
      f_state = f_imp_state f_var;
      f_ret = f_imp f_state;
      t = t + f_imp_time 0 f_state;
      one_to_two_out = f_imp_state_var f_ret;
      t = t + 2;
      ret = t
    in
      ret
  )"
  by auto
termination
  by (relation "measure (\<lambda>(t, s). one_to_two_state_out s)") simp

lemmas [simp del] = one_to_two_imp_time.simps

lemma one_to_two_imp_time_acc:
  "(one_to_two_imp_time (Suc t) s) = Suc (one_to_two_imp_time t s)"
  by (simp add: one_to_two_imp_time.simps)

lemma one_to_two_imp_time_acc_2:
  "(one_to_two_imp_time x s) = x + (one_to_two_imp_time 0 s)"
  by (simp add: one_to_two_imp_time.simps)

definition one_to_two_IMP where
  "one_to_two_IMP \<equiv>
  (f_pref_str @ f_var_str) ::= (A (V one_to_two_in_str));;
  invoke_subprogram f_pref_str f_IMP;;
  one_to_two_out_str ::= (A (V (f_pref_str @ f_var_str)))
"

abbreviation
  "one_to_two_IMP_vars \<equiv>
  {one_to_two_in_str, one_to_two_out_str}"


lemma prefix_vars[simp, dest]: "\<And>v . v \<in> one_to_two_IMP_vars \<Longrightarrow> \<not> prefix f_pref_str v"
  using f_pref_string_present stopper by (auto simp add: stopper_works)
lemma prefix_vars'[simp, dest]: "\<And>v . v \<in> one_to_two_IMP_vars \<Longrightarrow> f_pref_str \<noteq> v"
  using f_pref_string_present stopper by fastforce

definition "one_to_two_imp_to_HOL_state p s = one_to_two_state
  (s (add_prefix p one_to_two_in_str))
  (s (add_prefix p one_to_two_out_str))
"

lemma one_to_two_IMP_correct_function:
  "(invoke_subprogram p one_to_two_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p one_to_two_out_str)
      = one_to_two_state_out
 (one_to_two_imp (one_to_two_imp_to_HOL_state p s))"
  apply (subst (asm) one_to_two_IMP_def)
  apply(simp only: prefix_simps)
  apply (erule Seq_tE)+
  apply (erule f_IMP_correct[where vars=one_to_two_IMP_vars])
   apply simp
  thm functional_correctness
  apply (remove_assign)
  apply (unfold_stuff state_translators: one_to_two_imp_to_HOL_state_def f_imp_to_HOL_state_def)
  by (auto elim: f_IMP_correct simp add: one_to_two_imp_to_HOL_state_def
      one_to_two_imp.simps one_to_two_state_upd_def
      one_to_two_IMP_def invoke_subprogram_append)
  
lemma one_to_two_IMP_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ one_to_two_pref) one_to_two_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix one_to_two_pref v)\<rbrakk>
  \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma one_to_two_IMP_correct_time:
  "(invoke_subprogram p one_to_two_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = one_to_two_imp_time 0 (one_to_two_imp_to_HOL_state p s)"
  by (fastforce elim: f_IMP_correct simp: one_to_two_imp_to_HOL_state_def
      one_to_two_imp_time.simps f_imp_to_HOL_state_def one_to_two_IMP_def
      invoke_subprogram_append)

lemma one_to_two_IMP_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) one_to_two_IMP, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (one_to_two_imp_time 0 (one_to_two_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) one_to_two_out_str) =
        one_to_two_state_out (one_to_two_imp (one_to_two_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using one_to_two_IMP_correct_time one_to_two_IMP_correct_function
    one_to_two_IMP_correct_effects 
  by (meson set_mono_prefix)


end

(* Problem when interpreting: Records are ugly. *)

find_consts "_ snd'_state_scheme \<Rightarrow> snd'_state"

find_theorems snd'_state.truncate
find_theorems snd'_state.fields
lemma "snd'_state_p s = snd'_state_p (snd'_state.truncate s)"
  by (simp add: snd'_state.defs(4))
lemma "snd'_state_p (snd'_state.fields p) = p" 
  by code_simp (* There is something, I am just to lazy to find it ;) *)

abbreviation "snd'_state_p' \<equiv> snd'_state_p o snd'_state.truncate"
abbreviation "snd'_state p \<equiv> snd'_state.fields p"

interpretation snd'_nat_two_var_version: 
  one_var_to_two_var snd_nat snd'_state_p' snd'_state.fields snd'_imp snd'_imp_time snd'_prefix
  snd'_p_str "CHR ''$''" snd'_IMP snd'_imp_to_HOL_state
  apply standard
         apply (simp add: snd'_state.defs(4))
  apply code_simp
  apply code_simp 
  apply simp 
  apply simp
       apply (simp add: snd'_state.defs(4) snd'_imp_correct snd_nat_snd'_nat)
      apply (simp add: snd'_imp_time_acc)
     apply simp
    apply simp
   apply (simp add: snd'_imp_to_HOL_state_def snd'_state.defs(2))
  using  snd'_IMP_correct apply (auto simp add: snd'_state.defs) by blast

thm snd'_nat_two_var_version.one_to_two_IMP_correct
find_consts name: snd'_nat_two_var_version
(* Now I have something with the correct format, I can throw it into the map locale *)

(* Names  are still needlesly verbose *)
interpretation 
  map_snd:
  map_imp snd'_nat snd'_nat_two_var_version.one_to_two_state_in snd'_nat_two_var_version.one_to_two_state_out
  snd'_nat_two_var_version.one_to_two_state snd'_nat_two_var_version.one_to_two_imp snd'_nat_two_var_version.one_to_two_imp_time
  snd'_nat_two_var_version.one_to_two_prefix
  snd'_nat_two_var_version.one_to_two_in_str snd'_nat_two_var_version.one_to_two_out_str
  "CHR ''&''" snd'_nat_two_var_version.one_to_two_IMP snd'_nat_two_var_version.one_to_two_imp_to_HOL_state
  apply standard
           apply (auto simp add: snd'_nat_two_var_version.one_to_two_imp_correct snd_nat_snd'_nat
      snd'_nat_two_var_version.one_to_two_imp_time_acc snd'_nat_two_var_version.one_to_two_imp_to_HOL_state_def)[9]
  (* Should be easier, investigate *)
  subgoal for p1 p2 S t s' vars P
    using [[unify_trace_failure]] apply (rule 
        one_var_to_two_var.one_to_two_IMP_correct[OF snd'_nat_two_var_version.one_var_to_two_var_axioms,
          of p1 p2 S t s' vars P]) by blast+ 
  done

(* map snd is refined! *)

term map_snd.map_f_IMP
thm map_snd.map_f_IMP_def
thm map_snd.map_f_IMP_correct




end