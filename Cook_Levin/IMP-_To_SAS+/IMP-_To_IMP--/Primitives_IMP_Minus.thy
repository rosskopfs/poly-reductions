\<^marker>\<open>creator Mohammad Abdulaziz, Florian Keßler\<close>

theory Primitives_IMP_Minus
  imports "HOL-Library.Nat_Bijection" Primitives IMP_Minus.Call_By_Prefixes "HOL-Library.Sublist"
    (* Merge those *)
    "Poly_Reductions_Lib.Triangle_Extensions"
    "Poly_Reductions_Lib.Discrete_Extensions"
begin


(* 
  Disable syntax for IMP_Minus_Minus programs. This prevents parsing becoming exponential.
*)
unbundle IMP_Minus_Minus_Com.no_com_syntax

subsection \<open>Multiplication\<close>

record mul_state = mul_a::nat mul_b::nat mul_c::nat

named_theorems functional_correctness
lemmas functional_correctness_lemmas = functional_correctness

abbreviation "mul_prefix \<equiv> ''mul.''"
abbreviation "mul_a_str \<equiv> ''a''"
abbreviation "mul_b_str \<equiv> ''b''"
abbreviation "mul_c_str \<equiv> ''c''"


definition "mul_state_upd s \<equiv>
      let
        d = (mul_b s) mod 2;
        mul_c = (if d \<noteq> 0 then mul_c s + mul_a s else mul_c s);
        mul_a = mul_a s + mul_a s;
        mul_b = (mul_b s) div 2;
        ret = \<lparr>mul_a = mul_a, mul_b = mul_b, mul_c = mul_c\<rparr>
      in
        ret
"

function mul_imp:: "mul_state \<Rightarrow> mul_state" where
"mul_imp s = 
  (if mul_b s \<noteq> 0 then \<comment> \<open>While b \<noteq> 0\<close>
    (
      let
        next_iteration = mul_imp (mul_state_upd s)
      in
        next_iteration
    )
  else
    (
      let
        ret = s
      in
        ret
    )
  )"
  by pat_completeness auto
termination
  by  (relation "Wellfounded.measure (\<lambda>s. mul_b s)") (auto simp: mul_state_upd_def Let_def split: if_splits)

lemmas [simp del] = mul_imp.simps

lemma mul_imp_correct: "mul_c (mul_imp s) = mul_c s + mul_a s * mul_b s"
proof (induction s rule: mul_imp.induct)
  case (1 s)
  then show ?case
    apply(subst mul_imp.simps)
    apply (auto simp: mul_state_upd_def Let_def split: if_splits)
    by (metis (no_types, lifting) One_nat_def add.commute add_mult_distrib2 distrib_right mult.right_neutral mult_2 mult_div_mod_eq)
qed 

function mul_imp_time:: "nat \<Rightarrow> mul_state\<Rightarrow> nat" where
"mul_imp_time t s = 
(
    (if mul_b s \<noteq> 0 then \<comment> \<open>While b \<noteq> 0\<close>
      (
        let
          t = t + 1; \<comment> \<open>To account for while loop condition checking\<close>
          mul_d = (mul_b s) mod 2::nat;
          t = t + 2;
          mul_c = (if mul_d \<noteq> 0 then mul_c s + mul_a s else mul_c s);
          t = t + 1 + (if mul_d \<noteq> 0 then 2 else 2);
          mul_a = mul_a s + mul_a s;
          t = t + 2;
          mul_b = mul_b s div 2;
          t = t + 2;
          next_iteration = mul_imp_time t (mul_state_upd s)
        in
          next_iteration
      )
    else
      (
         \<comment> \<open>To account for the two steps of checking the condition and skipping the loop\<close>
        let
          t = t + 2;
          ret = t
        in
          ret
      )
    )
)"
  by pat_completeness auto
termination
  by  (relation "Wellfounded.measure (\<lambda>(t, s). mul_b s)") (auto simp: mul_state_upd_def Let_def split: if_splits)

lemmas [simp del] = mul_imp_time.simps

lemma mul_imp_time_acc: "(mul_imp_time (Suc t) s) = Suc (mul_imp_time t s)"
  by (induction t s arbitrary:  rule: mul_imp_time.induct)
     (auto simp add: mul_imp_time.simps mul_state_upd_def Let_def eval_nat_numeral split: if_splits)

definition mul_IMP_minus where
"mul_IMP_minus \<equiv>
  (\<comment> \<open>if b \<noteq> 0 then\<close>
   WHILE mul_b_str\<noteq>0 DO
        \<comment> \<open>d = b mod 2;\<close>
        (''d'' ::= ((V mul_b_str) \<doteq>1);;
        \<comment> \<open>c = (if d \<noteq> 0 then c + a else c);\<close>
        IF ''d''\<noteq>0 THEN mul_c_str ::= ((V mul_c_str) \<oplus> (V mul_a_str)) ELSE mul_c_str ::= A (V mul_c_str);;
        \<comment> \<open>a = a + a;\<close>
        mul_a_str ::= ((V mul_a_str) \<oplus> (V mul_a_str));;
        \<comment> \<open>b = b div 2;\<close>
        mul_b_str ::= ((V mul_b_str) \<then>))
  )"

(*definition mul_IMP_Minus_state_transformer where "mul_IMP_Minus_state_transformer p s \<equiv>
  state_transformer p  
    [(''a'', mul_a s),(''b'',  mul_b s),(''c'',  mul_c s),(''d'', mul_d s)]"*)

definition "mul_imp_to_HOL_state p s =
  \<lparr>mul_a = s (add_prefix p mul_a_str), mul_b = (s (add_prefix p mul_b_str)),
   mul_c = (s (add_prefix p mul_c_str))\<rparr>"

lemma mul_imp_to_HOL_state_add_prefix: 
  "mul_imp_to_HOL_state (add_prefix p1 p2) s = mul_imp_to_HOL_state p2 (s o (add_prefix p1))"
  by (auto simp: mul_imp_to_HOL_state_def)

lemma mul_imp_to_HOL_state_add_prefix':
  "mul_imp_to_HOL_state (x # p2) s = mul_imp_to_HOL_state p2 (s o (add_prefix [x]))"
  by (auto simp: mul_imp_to_HOL_state_def)

lemma mul_IMP_minus_correct_time:
  "(invoke_subprogram p mul_IMP_minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> t = (mul_imp_time 0 (mul_imp_to_HOL_state p s))"
  apply(induction "mul_imp_to_HOL_state p s" arbitrary: s s' t rule: mul_imp.induct)
  apply(simp only: mul_IMP_minus_def com_add_prefix.simps)
  apply(erule While_tE)
   apply(subst mul_imp_time.simps)
   apply(auto simp: mul_imp_time_acc mul_imp_to_HOL_state_def)[1]
  apply(dest_com')
  apply(erule Seq_tE)+
  apply(erule If_tE)
   apply(drule AssignD)+
   apply(elim conjE)
   apply(subst mul_imp_time.simps)
   apply(auto simp: mul_imp_time_acc mul_imp_to_HOL_state_def mul_state_upd_def)[1]
  apply(subst mul_imp_time.simps)
  apply(auto simp: mul_imp_time_acc mul_imp_to_HOL_state_def mul_state_upd_def)[1]
  done

lemma mul_IMP_minus_correct_function:
  "(invoke_subprogram p mul_IMP_minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> s' (add_prefix p mul_c_str) = mul_c (mul_imp (mul_imp_to_HOL_state p s))"
  apply(induction "mul_imp_to_HOL_state p s" arbitrary: s s' t rule: mul_imp.induct)
  apply(simp only: mul_IMP_minus_def com_add_prefix.simps)
  apply(erule While_tE)
   apply(subst mul_imp.simps)
   apply(auto simp: mul_imp_to_HOL_state_def)[1]
  apply(dest_com')
  apply(erule Seq_tE)+
  apply(erule If_tE)
   apply(drule AssignD)+
   apply(elim conjE)
   apply(subst mul_imp.simps mul_imp_time.simps)
   apply(auto simp: mul_imp_to_HOL_state_def mul_state_upd_def)[1]
  apply(subst mul_imp.simps mul_imp_time.simps)
  apply(auto simp: mul_imp_to_HOL_state_def mul_state_upd_def)[1]
  done

lemma mul_IMP_minus_correct_effects:
  "(invoke_subprogram (p @ mul_pref) mul_IMP_minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> p @ v \<in> vars \<Longrightarrow> \<not> (set mul_pref \<subseteq> set v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma mul_IMP_minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) mul_IMP_minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
     \<lbrakk>t = (mul_imp_time 0 (mul_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) mul_c_str) = mul_c (mul_imp (mul_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. p1 @ v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v) \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using mul_IMP_minus_correct_time mul_IMP_minus_correct_function mul_IMP_minus_correct_effects
  by auto

subsubsection \<open>Squaring\<close>

record square_state = square_x :: nat square_square :: nat

abbreviation "square_prefix \<equiv> ''square.''"
abbreviation "square_x_str \<equiv> ''x''"
abbreviation "square_square_str \<equiv> ''square''"

definition "square_state_upd s \<equiv> 
  let
    mul_a' = square_x s;
    mul_b' = square_x s;
    mul_c' = 0;
    (square_mul_state::mul_state) = \<lparr>mul_a = mul_a', mul_b = mul_b', mul_c = mul_c'\<rparr>;
    mul_ret = (mul_imp square_mul_state);
    square_square' = mul_c mul_ret;
    ret = \<lparr>square_x = square_x s, square_square = square_square'\<rparr>
  in
    ret
"

fun square_imp :: "square_state \<Rightarrow> square_state" where
  "square_imp s = (let
     ret = square_state_upd s
   in
     ret
  )"

declare square_imp.simps[simp del]

lemma square_imp_correct: "square_square (square_imp s) = (square_x s)^2"
  by (induction s rule: square_imp.induct)
    (auto simp: square_imp.simps square_state_upd_def Let_def mul_imp_correct power2_eq_square split: if_splits)

fun square_imp_time :: "nat \<Rightarrow> square_state \<Rightarrow> nat" where
  "square_imp_time t s = (let
     mul_a' = square_x s;
     t = t + 2;
     mul_b' = square_x s;
     t = t + 2;
     mul_c' = 0;
     t = t + 2;
     (square_mul_state::mul_state) = \<lparr>mul_a = mul_a', mul_b = mul_b', mul_c = mul_c'\<rparr>;
     mul_ret = (mul_imp square_mul_state);
     t = t + mul_imp_time 0 square_mul_state;
     square_square = mul_c mul_ret;
     t = t + 2;
     ret = t
   in
     ret
  )"

declare square_imp_time.simps[simp del]

lemma square_imp_time_acc: "(square_imp_time (Suc t) s) = Suc (square_imp_time t s)"
  by (induction t s rule: square_imp_time.induct) 
    (auto simp add: square_imp_time.simps Let_def split: if_splits)

definition square_IMP_Minus where
"square_IMP_Minus \<equiv>
  (
   \<comment> \<open>mul_a' = square_x s;\<close>
   (mul_prefix @ mul_a_str) ::= A (V square_x_str);;
   \<comment> \<open>mul_b' = (square_x s);\<close>
   (mul_prefix @ mul_b_str) ::= A (V square_x_str);;
   \<comment> \<open>mul_c' = 0;\<close>
   (mul_prefix @  mul_c_str) ::= (A (N 0)) ;;
   \<comment> \<open>(mul_state::mul_state) = \<lparr>mul_a = mul_a, mul_b = mul_b, mul_c = 0\<rparr>;\<close>
   \<comment> \<open>mul_ret = (mul_imp mul_state);\<close>
   invoke_subprogram mul_prefix mul_IMP_minus;;
  square_square_str ::= A (V (mul_prefix @ mul_c_str))
  )"

definition "square_imp_to_HOL_state p s =
  \<lparr>square_x = s (add_prefix p square_x_str), square_square = s (add_prefix p square_square_str)\<rparr>"

lemma square_imp_to_HOL_state_add_prefix: 
  "square_imp_to_HOL_state (add_prefix p1 p2) s = square_imp_to_HOL_state p2 (s o (add_prefix p1))"
  by (auto simp only: square_imp_to_HOL_state_def append.assoc[symmetric] comp_def)

(* But why the vars? Do they add anything? *)
lemma square_IMP_Minus_correct_function: 
  "(invoke_subprogram p square_IMP_Minus, s) 
      \<Rightarrow>\<^bsup>t \<^esup> s'
    \<Longrightarrow> s' (add_prefix p square_square_str) = square_square (square_imp (square_imp_to_HOL_state p s))"
  apply(simp only: square_IMP_Minus_def square_imp.simps com_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  \<comment> \<open>Variables that we want to preserve: variables of this program minus the variables of the
     program we call. If automation fails, this should be manually chosen variables.\<close>
  apply(erule mul_IMP_minus_correct[where vars = "{p @ ''square''}"]) (* Fix rules for mul *)
  apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: square_state_upd_def Let_def square_imp_to_HOL_state_def)[1]
  apply(auto simp: mul_imp_to_HOL_state_def)[1]
  done

lemma square_IMP_Minus_correct_time: 
  "(invoke_subprogram p square_IMP_Minus, s) 
      \<Rightarrow>\<^bsup>t\<^esup> s'
    \<Longrightarrow> t = square_imp_time 0 (square_imp_to_HOL_state p s)"
  apply(simp only: square_IMP_Minus_def com_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
   apply(drule AssignD)+
   apply(elim conjE)
   apply(subst square_imp_time.simps)
  apply(erule mul_IMP_minus_correct[where vars = "{p @ square_square_str}"])
  \<comment> \<open>Warning: in the following, I am unfolding mul_imp_to_HOL_state_def. With more experiments, it
      should become clear if this will cascade down multiple layers\<close>
  apply(simp add: square_imp_time_acc square_imp_to_HOL_state_def square_state_upd_def)[1]
  apply (auto simp: mul_imp_to_HOL_state_def)[1]
  done

lemma square_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ square_pref) square_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>  v \<in> vars \<Longrightarrow> \<not> (prefix square_pref v) 
  \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars 
  by (metis prefix_def)

lemma square_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) square_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (square_imp_time 0 (square_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) square_square_str) = 
        square_square (square_imp (square_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using square_IMP_Minus_correct_time square_IMP_Minus_correct_function
        square_IMP_Minus_correct_effects 
  by auto

subsection \<open>Square root\<close>

record dsqrt'_state = dsqrt'_state_y :: nat dsqrt'_state_L :: nat dsqrt'_state_R :: nat

abbreviation "dsqrt'_pref \<equiv> ''dsqrt'.''"
abbreviation "dsqrt'_y_str \<equiv> ''y''"
abbreviation "dsqrt'_L_str \<equiv> ''L''"
abbreviation "dsqrt'_R_str \<equiv> ''R''"

definition "dsqrt'_imp_state_upd s = (let
    M = dsqrt'_state_L s + dsqrt'_state_R s;
    M = M div 2;
    
    square_x' = M;
    square_square' = 0; \<comment> \<open>Is this necessary? If yes, does it make sense to introduce a concept of input/output vars?\<close>
    (dsqrt'_square_state::square_state) = \<lparr>square_x = square_x', square_square = square_square'\<rparr>;
    square_ret = square_imp dsqrt'_square_state;
    M2 = square_square square_ret;
    
    \<comment> \<open>Canonical way to do general (i.e. not just one assignment) branching?\<close>
    cond = M2 - dsqrt'_state_y s;
    L = if cond \<noteq> 0 then dsqrt'_state_L s else M;
    R = if cond \<noteq> 0 then M else dsqrt'_state_R s;

    ret = \<lparr>dsqrt'_state_y = dsqrt'_state_y s, dsqrt'_state_L = L, dsqrt'_state_R = R\<rparr>
  in
    ret)
"
     
function dsqrt'_imp :: "dsqrt'_state \<Rightarrow> dsqrt'_state" where
  "dsqrt'_imp s = 
  (if dsqrt'_state_R s - (dsqrt'_state_L s + 1) \<noteq> 0 then \<comment> \<open>While L+1 < R\<close>
    (
      let
        next_iteration = dsqrt'_imp (dsqrt'_imp_state_upd s)
      in
        next_iteration
    )
  else
    (
      let
        ret = s
      in
        ret
    )
  )"
  by pat_completeness auto
termination (* Same termination proof as recursive version, just some additional decoration *)
  by (relation "Wellfounded.measure (\<lambda>s. dsqrt'_state_R s - dsqrt'_state_L s)") 
    (auto simp: dsqrt'_imp_state_upd_def Let_def split: if_splits)

declare dsqrt'_imp.simps[simp del]

lemma dsqrt'_imp_correct: "dsqrt'_state_L (dsqrt'_imp s) = dsqrt' (dsqrt'_state_y s) (dsqrt'_state_L s) (dsqrt'_state_R s)"
proof (induction s rule: dsqrt'_imp.induct)
  case (1 s)
  then show ?case
    apply(subst dsqrt'_imp.simps)
    apply (auto simp: dsqrt'_imp_state_upd_def Let_def power2_eq_square square_imp_correct 
        dsqrt'_simps split: if_splits) (* Slow, very slow, do better*)
    done
qed

function dsqrt'_imp_time :: "nat \<Rightarrow> dsqrt'_state \<Rightarrow> nat" where
  "dsqrt'_imp_time t s = 
  (if dsqrt'_state_R s - (dsqrt'_state_L s + 1) \<noteq> 0 then \<comment> \<open>While L+1 < R\<close>
    (
      let
        t = t + 5; \<comment> \<open>To account for while loop condition checking and difference computation\<close>
         \<comment> \<open>Computation of M\<close>
        M = dsqrt'_state_L s + dsqrt'_state_R s;
        t = t + 2;
        M = M div 2;
        t = t + 2;
        
        square_x' = M;
        t = t + 2;
        square_square' = 0; \<comment> \<open>Is this necessary? If yes, does it make sense to introduce a concept of input/output vars?\<close>
        t = t + 2;
        (dsqrt'_square_state::square_state) = \<lparr>square_x = square_x', square_square = square_square'\<rparr>;
        square_ret = square_imp dsqrt'_square_state;
        t = t + square_imp_time 0 dsqrt'_square_state;
        M2 = square_square square_ret;
        t = t + 2;
        
        \<comment> \<open>Canonical way to do general (i.e. not just one assignment) branching?\<close>
        cond = M2 - dsqrt'_state_y s;
        t = t + 2;
        L = if cond \<noteq> 0 then dsqrt'_state_L s else M;
        t = t + 3;
        R = if cond \<noteq> 0 then M else dsqrt'_state_R s;
        t = t + 3;

        next_iteration = dsqrt'_imp_time t (dsqrt'_imp_state_upd s)
      in
        next_iteration
    )
  else
    (
      let
        t = t + 7;
        ret = t
      in
        ret
    )
  )"
  by pat_completeness auto
termination (* Same termination proof as recursive version, just some additional decoration *)
  by (relation "Wellfounded.measure (\<lambda>(t,s). dsqrt'_state_R s - dsqrt'_state_L s)") 
    (auto simp: dsqrt'_imp_state_upd_def Let_def split: if_splits)

declare dsqrt'_imp_time.simps[simp del]

lemma dsqrt'_imp_time_acc: "(dsqrt'_imp_time (Suc t) s) = Suc (dsqrt'_imp_time t s)"
proof (induction t s arbitrary: rule: dsqrt'_imp_time.induct)
  case (1 t s)
  then show ?case
  proof(cases "dsqrt'_state_R s - (dsqrt'_state_L s + 1) \<noteq> 0")
    case True
    hence "(Suc (dsqrt'_state_L s)) < dsqrt'_state_R s"
      by simp
    with True show ?thesis
      apply (subst (2) dsqrt'_imp_time.simps)
      apply (subst dsqrt'_imp_time.simps)
      using 1 by (simp add: dsqrt'_imp_state_upd_def Let_def split: if_splits)
  next
    case False
    then show ?thesis 
      by (auto simp add: dsqrt'_imp_time.simps split: if_splits)
  qed
qed

lemma dsqrt'_imp_time_acc': "(dsqrt'_imp_time t s) = t + (dsqrt'_imp_time 0 s)"
  by (induction t) (auto simp add: dsqrt'_imp_time_acc)
lemma dsqrt'_imp_time_acc'': "NO_MATCH 0 t \<Longrightarrow> (dsqrt'_imp_time t s) = t + (dsqrt'_imp_time 0 s)"
  using dsqrt'_imp_time_acc' .

definition dsqrt'_IMP_Minus_while_condition where
  "dsqrt'_IMP_Minus_while_condition \<equiv> 
  ''inc'' ::= ((V dsqrt'_L_str) \<oplus> (N 1));;
   ''diff'' ::= ((V dsqrt'_R_str) \<ominus> (V ''inc''))"

definition dsqrt'_IMP_Minus_loop_body where
  "dsqrt'_IMP_Minus_loop_body =
    \<comment> \<open>M = (L+R) / 2;\<close>
    ''M'' ::= ((V dsqrt'_L_str) \<oplus> (V dsqrt'_R_str));;
    ''M'' ::= ((V ''M'')\<then>);;

    \<comment> \<open>M*M,\<close>
    (square_prefix @ square_x_str) ::= A (V ''M'');;
    (square_prefix @ square_square_str) ::= A (N 0);;
    invoke_subprogram square_prefix square_IMP_Minus;;
    ''M2'' ::= A (V (square_prefix @ square_square_str));;

    \<comment> \<open>New left bound\<close>
    ''cond'' ::= ((V ''M2'') \<ominus> (V dsqrt'_y_str));;
    (IF ''cond''\<noteq>0 THEN dsqrt'_L_str ::= A (V dsqrt'_L_str) ELSE dsqrt'_L_str ::= A (V ''M''));;
    \<comment> \<open>New right bound\<close>
    (IF ''cond''\<noteq>0 THEN dsqrt'_R_str ::= A (V ''M'') ELSE dsqrt'_R_str ::= A (V dsqrt'_R_str))"

definition dsqrt'_IMP_Minus_after_loop where
  "dsqrt'_IMP_Minus_after_loop = Com.SKIP"

definition dsqrt'_IMP_Minus where
"dsqrt'_IMP_Minus \<equiv>
  \<comment> \<open>if L+1 < R\<close>
  dsqrt'_IMP_Minus_while_condition;;
  WHILE ''diff''\<noteq>0 DO (
    dsqrt'_IMP_Minus_loop_body;;
    dsqrt'_IMP_Minus_while_condition
  );;
  dsqrt'_IMP_Minus_after_loop"

lemmas dsqrt'_IMP_Minus_subprogram_simps =
  dsqrt'_IMP_Minus_while_condition_def dsqrt'_IMP_Minus_loop_body_def dsqrt'_IMP_Minus_after_loop_def

definition "dsqrt'_imp_to_HOL_state p s =
  \<lparr>dsqrt'_state_y = s (add_prefix p dsqrt'_y_str), dsqrt'_state_L = s (add_prefix p dsqrt'_L_str), 
    dsqrt'_state_R = s (add_prefix p dsqrt'_R_str)\<rparr>"

abbreviation 
  "dsqrt'_IMP_vars \<equiv> {dsqrt'_y_str, dsqrt'_L_str, dsqrt'_R_str, ''inc'', ''diff'', ''cond'', ''M'', ''M2''}"

lemma square_imp_state_in_square_imp_to_HOL_state[simp]: "square_x (square_imp_to_HOL_state p S) = S (add_prefix p square_x_str)"
  by (auto simp add: square_imp_to_HOL_state_def)
lemma square_imp_state_out_square_imp_to_HOL_state[simp]: "square_square (square_imp_to_HOL_state p S) = S (add_prefix p square_square_str)"
  by (auto simp add: square_imp_to_HOL_state_def)

lemma cond_elim: "(\<And>v . v \<in> insert w W \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)) 
  \<Longrightarrow> (s (add_prefix p w) = s' (add_prefix p w) \<Longrightarrow> (\<And>v . v \<in> W \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)) \<Longrightarrow> P)
  \<Longrightarrow> P"
  by auto

lemma dsqrt'_IMP_Minus_correct_function_1: 
  "(invoke_subprogram p dsqrt'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p dsqrt'_L_str) = 
       dsqrt'_state_L (dsqrt'_imp (dsqrt'_imp_to_HOL_state p s))"
proof (induction "dsqrt'_imp_to_HOL_state p s" arbitrary: s s' t rule: dsqrt'_imp.induct)
  case 1
  then show ?case 
  apply (subst dsqrt'_imp.simps)
  apply (simp only: dsqrt'_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule While_tE)
   apply (auto simp add: dsqrt'_imp_state_upd_def prefix_simps Let_def dsqrt'_imp_to_HOL_state_def dsqrt'_IMP_Minus_subprogram_simps split: if_splits)[]
    apply (erule Seq_tE)+
    apply dest_com_gen

    subgoal for x s2 y xa s2a ya xb s2b yb xc s2c yc
    apply (simp only: dsqrt'_IMP_Minus_while_condition_def prefix_simps)
    apply (erule Seq_tE)+
      by (auto simp add: dsqrt'_imp_to_HOL_state_def) 

    subgoal premises p for x s2 y xa s2a ya xb s2b yb xc s2c yc 
      thm p
      using p(4,5,8,9) apply -
      apply (simp only: dsqrt'_IMP_Minus_while_condition_def dsqrt'_IMP_Minus_loop_body_def prefix_simps)
      apply(erule Seq_tE)+
      apply(all \<open>erule square_IMP_Minus_correct[where vars = "dsqrt'_IMP_vars"]\<close>)
      subgoal premises p  using p(24) by (auto simp add: prefix_Cons) (* Here we already see how auto gets confused by all the crap in p, 
        also a free prefix made it more difficult, abuse . *)
      apply(elim If_tE)
      apply (all \<open>drule AssignD\<close>)+
         apply (all \<open>erule conjE\<close>)+
          (* All proofs the same now, instantiations maybe with simprocs, problem is still to much stuff in goal state, maybe a filter tactic is the least work?
            Otherwise do more "structured" accumulation of information with ML
           *)
          subgoal premises p 
          using p(1,13,15-) p(14) apply (elim cond_elim)
          apply (auto simp add: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_correct
                Cons_eq_append_conv power2_eq_square split: if_splits) 
          done
          subgoal premises p 
          using p(1,13,15-) p(14) apply (elim cond_elim)
          apply (auto simp add: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_correct
                Cons_eq_append_conv power2_eq_square split: if_splits) 
          done
          subgoal premises p 
          using p(1,13,15-) p(14) apply (elim cond_elim)
          apply (auto simp add: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_correct
                Cons_eq_append_conv power2_eq_square split: if_splits) 
          done
          subgoal premises p 
          using p(1,13,15-) p(14) apply (elim cond_elim)
          apply (auto simp add: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_correct
                Cons_eq_append_conv power2_eq_square split: if_splits) 
          done
        done

      subgoal premises p for x s2 y xa s2a ya xb s2b yb xc s2c yc 
      thm p
      using p(4,5,8,9) apply -
      apply (simp only: dsqrt'_IMP_Minus_while_condition_def dsqrt'_IMP_Minus_loop_body_def prefix_simps)
      apply(erule Seq_tE)+
      apply(all \<open>erule square_IMP_Minus_correct[where vars = "dsqrt'_IMP_vars"]\<close>)
      subgoal premises p  using p(24) by (auto simp add: prefix_Cons) (* Here we already see how auto gets confused by all the crap in p, 
        also a free prefix made it more difficult, abuse . *)
      apply(elim If_tE)
      apply (all \<open>drule AssignD\<close>)+
         apply (all \<open>erule conjE\<close>)+
          (* All proofs the same now, instantiations maybe with simprocs, problem is still to much stuff in goal state, maybe a filter tactic is the least work?
            Otherwise do more "structured" accumulation of information with ML
           *)
          subgoal premises p 
          using p(1,13,15-) p(14) apply (elim cond_elim)
          apply (auto simp add: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_correct
                Cons_eq_append_conv power2_eq_square split: if_splits) 
          done
          subgoal premises p 
          using p(1,13,15-) p(14) apply (elim cond_elim)
          apply (auto simp add: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_correct
                Cons_eq_append_conv power2_eq_square split: if_splits) 
          done
          subgoal premises p 
          using p(1,13,15-) p(14) apply (elim cond_elim)
          apply (auto simp add: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_correct
                Cons_eq_append_conv power2_eq_square split: if_splits) 
          done
          subgoal premises p 
          using p(1,13,15-) p(14) apply (elim cond_elim)
          apply (auto simp add: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_correct
                Cons_eq_append_conv power2_eq_square split: if_splits) 
          done
        done
      done
  qed

lemma square_x[simp]: "square_x \<lparr>square_x = x, square_square = out\<rparr> = x"
  by auto
lemma square_square[simp]: "square_square  \<lparr>square_x = x, square_square = out\<rparr> = out"
  by auto
lemma square_state[simp]: "\<lparr>square_x = (square_x s), square_square = (square_square s)\<rparr> = s"
  by auto

lemma dsqrt'_IMP_Minus_correct_time: 
  "(invoke_subprogram p dsqrt'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> t = dsqrt'_imp_time 0 (dsqrt'_imp_to_HOL_state p s)"
proof (induction "dsqrt'_imp_to_HOL_state p s" arbitrary: s s' t rule: dsqrt'_imp.induct)
  case 1
  from "1.prems" show ?case 
  apply (subst dsqrt'_imp_time.simps)
  apply (simp only: dsqrt'_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule While_tE_time)
     apply (auto simp add: dsqrt'_imp_state_upd_def prefix_simps Let_def dsqrt'_imp_to_HOL_state_def dsqrt'_IMP_Minus_subprogram_simps 
          dsqrt'_imp_time_acc split: if_splits)[]
    apply (erule Seq_tE)+
    using "1.hyps"[unfolded dsqrt'_IMP_Minus_def] apply -
    apply (simp add: add.assoc)
    apply (dest_com_gen_time)

    subgoal for x s2 y xa s2a ya xb s2b yb xc s2c yc
    apply (simp only: dsqrt'_IMP_Minus_while_condition_def prefix_simps)
    apply (erule Seq_tE)+
      by (auto simp add: dsqrt'_imp_to_HOL_state_def) 

    subgoal premises p for x s2 y xa s2a ya xb s2b yb xc s2c yc 
      thm p
      using p(4,5,8,9) apply -
      apply (simp only: dsqrt'_IMP_Minus_while_condition_def dsqrt'_IMP_Minus_loop_body_def prefix_simps)
      apply(erule Seq_tE)+
      apply(all \<open>erule square_IMP_Minus_correct[where vars = "dsqrt'_IMP_vars"]\<close>)
      subgoal premises p  using p(24) by (auto simp add: prefix_Cons) (* Here we already see how auto gets confused by all the crap in p, 
        also a free prefix made it more difficult, abuse . *)
      apply(elim If_tE)
      apply (all \<open>drule AssignD\<close>)+
         apply (all \<open>erule conjE\<close>)+
          (* All proofs the same now, instantiations maybe with simprocs, problem is still to much stuff in goal state, maybe a filter tactic is the least work?
            Otherwise do more "structured" accumulation of information with ML
           *)
          subgoal premises p 
          using p(1,13,15-) p(14) apply (elim cond_elim)
          apply (auto simp add: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_correct
                Cons_eq_append_conv power2_eq_square split: if_splits) 
          done
          subgoal premises p 
          using p(1,13,15-) p(14) apply (elim cond_elim)
          apply (auto simp add: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_correct
                Cons_eq_append_conv power2_eq_square split: if_splits) 
          done
          subgoal premises p 
          using p(1,13,15-) p(14) apply (elim cond_elim)
          apply (auto simp add: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_correct
                Cons_eq_append_conv power2_eq_square split: if_splits) 
          done
          subgoal premises p 
          using p(1,13,15-) p(14) apply (elim cond_elim)
          apply (auto simp add: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_correct
                Cons_eq_append_conv power2_eq_square split: if_splits) 
          done
        done

      subgoal premises p' for x s2 y xa s2a ya xb s2b yb xc s2c yc 
        thm p' (* Strange, I am in timing but can still filter some timing infos, probably they already passed through a simp and their effects are 
          ttherefore present?*) 
      using p'(4,5,8,9) apply -
      apply (simp only: dsqrt'_IMP_Minus_while_condition_def dsqrt'_IMP_Minus_loop_body_def prefix_simps)
      apply(erule Seq_tE)+
      apply(all \<open>erule square_IMP_Minus_correct[where vars = "dsqrt'_IMP_vars"]\<close>)
      subgoal premises p  using p(24) by (auto simp add: prefix_Cons) (* Here we already see how auto gets confused by all the crap in p, 
        also a free prefix made it more difficult, abuse . *)
      apply(elim If_tE)
      apply (all \<open>drule AssignD\<close>)+
         apply (all \<open>erule conjE\<close>)+
          (* All proofs the same now, instantiations maybe with simprocs, problem is still to much stuff in goal state, maybe a filter tactic is the least work?
            Otherwise do more "structured" accumulation of information with ML

            Interesting guess: Only cases 1/4 need to look at the timing(check added lemmas), the other ones are recognized to be impossible?
           *)
          subgoal premises p 
          using p apply (elim cond_elim)
          apply (auto simp add: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_correct dsqrt'_imp_time_acc''
                Cons_eq_append_conv power2_eq_square square_imp_time.simps split: if_splits)
          done
          subgoal premises p 
          using p(1,13,15-) p(14) apply (elim cond_elim)
          apply (auto simp add: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_correct
                Cons_eq_append_conv power2_eq_square split: if_splits) 
          done
          subgoal premises p 
          using p(1,13,15-) p(14) apply (elim cond_elim)
          apply (auto simp add: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_correct
                Cons_eq_append_conv power2_eq_square split: if_splits) 
          done
          subgoal premises p thm p (*Here I need them... Check again*)
          using p(1,13,15-) p(14) apply (elim cond_elim)
          apply (auto simp add: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def Let_def square_imp_correct dsqrt'_imp_time_acc''
                Cons_eq_append_conv power2_eq_square square_imp_to_HOL_state_def split: if_splits)
          using p(2-12) apply (auto simp add: square_imp_to_HOL_state_def)
          done
        done
      done
  qed

lemma dsqrt'_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ dsqrt'_prefix) dsqrt'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>  v \<in> vars \<Longrightarrow> \<not> (prefix dsqrt'_prefix v) 
  \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars
  by (metis prefix_def)

lemma dsqrt'_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) dsqrt'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (dsqrt'_imp_time 0 (dsqrt'_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) dsqrt'_L_str) = 
        dsqrt'_state_L (dsqrt'_imp (dsqrt'_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using dsqrt'_IMP_Minus_correct_time dsqrt'_IMP_Minus_correct_function_1
        dsqrt'_IMP_Minus_correct_effects
  by auto


record dsqrt_state = dsqrt_state_y :: nat dsqrt_state_ret :: nat 

abbreviation "dsqrt_prefix \<equiv> ''dsqrt.''"
abbreviation "dsqrt_y_str \<equiv> ''y''"
abbreviation "dsqrt_ret_str \<equiv> ''ret''"

abbreviation 
  "dsqrt_IMP_vars \<equiv> {dsqrt_y_str, dsqrt_ret_str}"

definition "dsqrt_imp_state_upd s = (let
    dsqrt'_y = dsqrt_state_y s;
    dsqrt'_L = 0;
    dsqrt'_R = Suc (dsqrt_state_y s);
    
    dsqrt_dsqrt'_state = \<lparr>dsqrt'_state_y = dsqrt'_y, dsqrt'_state_L = dsqrt'_L, dsqrt'_state_R = dsqrt'_R\<rparr>;
    dsqrt'_ret = dsqrt'_imp dsqrt_dsqrt'_state;
    
    dsqrt_ret = dsqrt'_state_L dsqrt'_ret;
    ret = \<lparr>dsqrt_state_y = dsqrt_state_y s, dsqrt_state_ret = dsqrt_ret\<rparr>
  in
    ret)
"
     
fun dsqrt_imp :: "dsqrt_state \<Rightarrow> dsqrt_state" where
  "dsqrt_imp s = 
  (let
    ret = dsqrt_imp_state_upd s
  in
    ret
  )"

declare dsqrt_imp.simps [simp del]

lemma dsqrt_imp_correct:
   "dsqrt_state_ret (dsqrt_imp s) = Discrete.sqrt (dsqrt_state_y s)"
  by (subst dsqrt_imp.simps) (auto simp: dsqrt'_imp_correct dsqrt_def dsqrt_imp_state_upd_def
      Let_def dsqrt_correct[symmetric] split: if_splits)

fun dsqrt_imp_time:: "nat \<Rightarrow> dsqrt_state\<Rightarrow> nat" where
  "dsqrt_imp_time t s = 
    (
      let
        dsqrt'_y = dsqrt_state_y s;
        t = t+2;
        dsqrt'_L = 0;
        t = t+2;
        dsqrt'_R = Suc (dsqrt_state_y s);
        t = t+2;
        
        dsqrt_dsqrt'_state = \<lparr>dsqrt'_state_y = dsqrt'_y, dsqrt'_state_L = dsqrt'_L, dsqrt'_state_R = dsqrt'_R\<rparr>;
        dsqrt'_ret = dsqrt'_imp dsqrt_dsqrt'_state;
        t = t + dsqrt'_imp_time 0 dsqrt_dsqrt'_state;
        
        dsqrt_ret = dsqrt'_state_L dsqrt'_ret;
        t = t+2;
        ret = t
      in
        ret
    )
"

lemmas [simp del] = dsqrt_imp_time.simps

lemma dsqrt_imp_time_acc: "(dsqrt_imp_time (Suc t) s) = Suc (dsqrt_imp_time t s)"
  apply(subst dsqrt_imp_time.simps)
  apply(subst dsqrt_imp_time.simps)
  apply (auto simp add: dsqrt_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)
  done

lemma dsqrt_imp_time_acc_2: "(dsqrt_imp_time x s) = x + (dsqrt_imp_time 0 s)"
  by (induction x arbitrary: s)
     (auto simp add: dsqrt_imp_time_acc dsqrt_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)


definition dsqrt_IMP_Minus where
"dsqrt_IMP_Minus \<equiv>
  (
    (dsqrt'_pref @ dsqrt'_y_str) ::= A (V dsqrt_y_str);;
    (dsqrt'_pref @ dsqrt'_L_str) ::= A (N 0);;
    (dsqrt'_pref @ dsqrt'_R_str) ::= (V dsqrt_y_str \<oplus> N 1);;
    
    invoke_subprogram dsqrt'_pref dsqrt'_IMP_Minus;;

    dsqrt_ret_str ::= A (V (dsqrt'_pref @ dsqrt'_L_str))
  )"

definition "dsqrt_imp_to_HOL_state p s =
  \<lparr>dsqrt_state_y = (s (add_prefix p dsqrt_y_str)), dsqrt_state_ret = (s (add_prefix p dsqrt_ret_str))\<rparr>"


lemma dsqrt_IMP_Minus_correct_function: 
  "(invoke_subprogram p dsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p dsqrt_ret_str) = dsqrt_state_ret (dsqrt_imp (dsqrt_imp_to_HOL_state p s))"
  apply(subst dsqrt_imp.simps)
  apply(simp only: dsqrt_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(all \<open>erule dsqrt'_IMP_Minus_correct[where vars = "dsqrt_IMP_vars"]\<close>) (* Probably do not need this here *)
   apply simp
  apply (drule AssignD)+
  apply (auto simp add: dsqrt_imp_state_upd_def dsqrt_imp_to_HOL_state_def dsqrt'_imp_to_HOL_state_def)
  done

lemma dsqrt_IMP_Minus_correct_time: 
  "(invoke_subprogram p dsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = dsqrt_imp_time 0 (dsqrt_imp_to_HOL_state p s)"
  apply(subst dsqrt_imp_time.simps)
  apply(simp only: dsqrt_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(all \<open>erule dsqrt'_IMP_Minus_correct[where vars = "dsqrt_IMP_vars"]\<close>) (* Probably do not need this here *)
   apply simp
  apply (drule AssignD)+
  apply (auto simp add: dsqrt_imp_state_upd_def dsqrt_imp_to_HOL_state_def dsqrt'_imp_to_HOL_state_def)
  done

lemma dsqrt_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ dsqrt_pref) dsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>  v \<in> vars 
  \<Longrightarrow> \<not> (set dsqrt_pref \<subseteq> set v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma dsqrt_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) dsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
     \<lbrakk>t = (dsqrt_imp_time 0 (dsqrt_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) dsqrt_ret_str) = 
        dsqrt_state_ret (dsqrt_imp (dsqrt_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using dsqrt_IMP_Minus_correct_time dsqrt_IMP_Minus_correct_function
        dsqrt_IMP_Minus_correct_effects 
  by auto

subsection \<open>Triangle\<close>

record triangle_state = triangle_a::nat triangle_triangle::nat

abbreviation "triangle_prefix \<equiv> ''triangle.''"
abbreviation "triangle_a_str \<equiv> ''a''"
abbreviation "triangle_triangle_str \<equiv> ''triangle''"


definition "triangle_state_upd (s::triangle_state) \<equiv>
      let
        mul_a' = triangle_a s;
        mul_b' = (triangle_a s) + 1;
        mul_c' = 0;
        (triangle_mul_state::mul_state) = \<lparr>mul_a = mul_a', mul_b = mul_b', mul_c = mul_c'\<rparr>;
        mul_ret = (mul_imp triangle_mul_state);
        triangle_triangle = (mul_c mul_ret) div 2;
        ret = \<lparr>triangle_a = triangle_a s,triangle_triangle = triangle_triangle\<rparr>
      in
        ret
"

fun triangle_imp:: "triangle_state \<Rightarrow> triangle_state" where
"triangle_imp s = 
  (let
     ret = triangle_state_upd s
   in
     ret
  )"

lemmas [simp del] = triangle_imp.simps

lemma triangle_imp_correct: "triangle_triangle (triangle_imp s) = Nat_Bijection.triangle (triangle_a s)"
proof (induction s rule: triangle_imp.induct)
  case (1 s)
  then show ?case
    by (auto simp: triangle_imp.simps triangle_def triangle_state_upd_def Let_def mul_imp_correct split: if_splits)
qed 

fun triangle_imp_time:: "nat \<Rightarrow> triangle_state \<Rightarrow> nat" where
"triangle_imp_time t s = 
  (let
     mul_a' = triangle_a s;
     t = t + 2;
     mul_b' = (triangle_a s) + 1;
     t = t + 2;
     mul_c' = 0;
     t = t + 2;
     (triangle_mul_state::mul_state) = \<lparr>mul_a = mul_a', mul_b = mul_b', mul_c = mul_c'\<rparr>;
     mul_ret = (mul_imp triangle_mul_state);
     t = t + mul_imp_time 0 triangle_mul_state;
     triangle_triangle = mul_c mul_ret div 2;
     t = t + 2;
     triangle_a = triangle_a s;
     t = t + 2;
     ret = t
   in
     ret
  )"

lemmas [simp del] = triangle_imp_time.simps

lemma triangle_imp_time_acc: "(triangle_imp_time (Suc t) s) = Suc (triangle_imp_time t s)"
  by (induction t s rule: triangle_imp_time.induct)
     (auto simp add: triangle_imp_time.simps mul_state_upd_def Let_def eval_nat_numeral split: if_splits)

definition triangle_IMP_Minus where
"triangle_IMP_Minus \<equiv>
  (
   \<comment> \<open>mul_a' = triangle_a s;\<close>
   (mul_prefix @ mul_a_str) ::= (A (V mul_a_str)) ;;
   \<comment> \<open>mul_b' = (triangle_a s) + 1;\<close>
   (mul_prefix @ mul_b_str) ::= ((V mul_a_str) \<oplus> (N 1));;
   \<comment> \<open>mul_c' = 0;\<close>
   (mul_prefix @  mul_c_str) ::= (A (N 0)) ;;
   \<comment> \<open>(mul_state::mul_state) = \<lparr>mul_a = mul_a, mul_b = mul_b, mul_c = 0\<rparr>;\<close>
   \<comment> \<open>mul_ret = (mul_imp mul_state);\<close>
   invoke_subprogram mul_prefix mul_IMP_minus;;
   \<comment> \<open>triangle_triangle = mul_c mul_ret div 2;\<close>
  triangle_triangle_str ::= (V (mul_prefix @ mul_c_str) \<then>);;
  triangle_a_str ::= A (V mul_a_str)
  )"


(*definition triangle_IMP_Minus_state_transformer where "triangle_IMP_Minus_state_transformer p s \<equiv>
 (state_transformer p [(''a'',  triangle_a s), (''triangle'',  triangle_triangle s)]) o
 (mul_IMP_Minus_state_transformer (''mul'' @ p) (triangle_mul_state s))"*)

definition "triangle_imp_to_HOL_state p s =
              \<lparr>triangle_a = s (add_prefix p triangle_a_str), triangle_triangle = (s (add_prefix p triangle_triangle_str))\<rparr>"

lemma triangle_imp_to_HOL_state_add_prefix: 
  "triangle_imp_to_HOL_state (add_prefix p1 p2) s = triangle_imp_to_HOL_state p2 (s o (add_prefix p1))"
  by (auto simp only: triangle_imp_to_HOL_state_def append.assoc[symmetric] comp_def
                      mul_imp_to_HOL_state_add_prefix)

(*lemma rev_add_prefix_all_variables:
  "p1 \<noteq> [] \<Longrightarrow> (add_prefix p2 v \<notin> set (all_variables (invoke_subprogram p1 (c::pcom) p2)))"
  nitpick
  apply(induction p1 arbitrary: c p2)
  subgoal by auto
  subgoal apply auto


lemma rev_add_prefix_all_variables:"(add_prefix p v \<in> set (all_variables (invoke_subprogram p1 c p2)))
       = (rev (add_prefix p v) \<in> set (map rev (all_variables (invoke_subprogram p1 c p2))))"
  by auto
*)

lemma cons_append: "xs \<noteq> [] \<Longrightarrow> x # xs = [x] @ xs"
  by simp

lemma triangle_IMP_Minus_correct_function: 
  "(invoke_subprogram p triangle_IMP_Minus, s) 
      \<Rightarrow>\<^bsup>t \<^esup> s'
    \<Longrightarrow> s' (add_prefix p triangle_triangle_str) = triangle_triangle (triangle_imp (triangle_imp_to_HOL_state p s))"
  apply(simp only: triangle_IMP_Minus_def triangle_imp.simps com_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  \<comment> \<open>Variables that we want to preserve: variables of this program minus the variables of the
     program we call. If automation fails, this should be manually chosen variables.\<close>
  apply(erule mul_IMP_minus_correct[where vars = "{p @ ''traingle''}"])
  apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: triangle_state_upd_def Let_def triangle_imp_to_HOL_state_def)[1]
  apply(auto simp: mul_imp_to_HOL_state_def)[1]
  done

lemma triangle_IMP_Minus_correct_time: 
  "(invoke_subprogram p triangle_IMP_Minus, s) 
      \<Rightarrow>\<^bsup>t\<^esup> s'
    \<Longrightarrow> t = triangle_imp_time 0 (triangle_imp_to_HOL_state p s)"
  apply(simp only: triangle_IMP_Minus_def com_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
   apply(drule AssignD)+
   apply(elim conjE)
   apply(subst triangle_imp_time.simps)
  apply(erule mul_IMP_minus_correct[where vars = "{p @ triangle_triangle_str}"])
  \<comment> \<open>Warning: in the following, I am unfolding mul_imp_to_HOL_state_def. With more experiments, it
      should become clear if this will cascade down multiple layers\<close>
  apply(simp add: triangle_imp_time_acc triangle_imp_to_HOL_state_def triangle_state_upd_def)[1]
  apply (auto simp: mul_imp_to_HOL_state_def)[1]
  done

lemma triangle_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ triangle_pref) triangle_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> p @ v \<in> vars \<Longrightarrow> \<not> (set triangle_pref \<subseteq> set v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma triangle_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) triangle_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
     \<lbrakk>t = (triangle_imp_time 0 (triangle_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) triangle_triangle_str) = triangle_triangle (triangle_imp (triangle_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. p1 @ v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v) \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using triangle_IMP_Minus_correct_time triangle_IMP_Minus_correct_function
        triangle_IMP_Minus_correct_effects 
  by auto

subsection \<open>Triangular root\<close>

record tsqrt_state = tsqrt_state_y :: nat tsqrt_state_ret :: nat 

abbreviation "tsqrt_prefix \<equiv> ''tsqrt.''"
abbreviation "tsqrt_y_str \<equiv> ''y''"
abbreviation "tsqrt_ret_str \<equiv> ''ret''"

abbreviation 
  "tsqrt_IMP_vars \<equiv> {tsqrt_y_str, tsqrt_ret_str}"

definition "tsqrt_imp_state_upd s = (let
    tsqrt_mul_a = tsqrt_state_y s;
    tsqrt_mul_b = 8;
    tsqrt_mul_c = 0;
    tsqrt_mul_state = \<lparr>mul_a = tsqrt_mul_a, mul_b = tsqrt_mul_b, mul_c = tsqrt_mul_c\<rparr>;
    mul_ret = mul_imp tsqrt_mul_state;
    
    tsqrt_y = mul_c mul_ret + 1;

    tsqrt_dsqrt_y = tsqrt_y;
    tsqrt_dsqrt_ret = 0;
    tsqrt_dsqrt_state = \<lparr>dsqrt_state_y = tsqrt_dsqrt_y, dsqrt_state_ret = tsqrt_dsqrt_ret\<rparr>;
    dsqrt_ret = dsqrt_imp tsqrt_dsqrt_state;

    tsqrt_y = dsqrt_state_ret dsqrt_ret - 1;
    tsqrt_ret = tsqrt_y div 2;
    ret = \<lparr>tsqrt_state_y = tsqrt_y, tsqrt_state_ret = tsqrt_ret\<rparr>
  in
    ret)
"

fun tsqrt_imp :: "tsqrt_state \<Rightarrow> tsqrt_state" where
  "tsqrt_imp s = 
  (let
    ret = tsqrt_imp_state_upd s
  in
    ret
  )"

declare tsqrt_imp.simps [simp del]

lemma tsqrt_imp_correct:
   "tsqrt_state_ret (tsqrt_imp s) = tsqrt (tsqrt_state_y s)"
  by (subst tsqrt_imp.simps) (auto simp: dsqrt_imp_correct tsqrt_def tsqrt_imp_state_upd_def
      Let_def mul_imp_correct mult.commute split: if_splits)

fun tsqrt_imp_time:: "nat \<Rightarrow> tsqrt_state\<Rightarrow> nat" where
  "tsqrt_imp_time t s = 
    (
      let
        tsqrt_mul_a = tsqrt_state_y s;
        t = t+2;
        tsqrt_mul_b = 8;
        t = t+2;
        tsqrt_mul_c = 0;
        t = t+2;
        tsqrt_mul_state = \<lparr>mul_a = tsqrt_mul_a, mul_b = tsqrt_mul_b, mul_c = tsqrt_mul_c\<rparr>;
        mul_ret = mul_imp tsqrt_mul_state;
        t = t+ mul_imp_time 0 tsqrt_mul_state;
        
        tsqrt_y = mul_c mul_ret + 1;
        t = t+2;
    
        tsqrt_dsqrt_y = tsqrt_y;
        t = t+2;
        tsqrt_dsqrt_ret = 0;
        t = t+2;
        tsqrt_dsqrt_state = \<lparr>dsqrt_state_y = tsqrt_dsqrt_y, dsqrt_state_ret = tsqrt_dsqrt_ret\<rparr>;
        dsqrt_ret = dsqrt_imp tsqrt_dsqrt_state;
        t = t + dsqrt_imp_time 0 tsqrt_dsqrt_state;
    
        tsqrt_y = dsqrt_state_ret dsqrt_ret - 1;
        t = t+2;
        tsqrt_ret = tsqrt_y div 2;
        t = t+2;
        ret = t
      in
        ret
    )
"

lemmas [simp del] = tsqrt_imp_time.simps

lemma tsqrt_imp_time_acc: "(tsqrt_imp_time (Suc t) s) = Suc (tsqrt_imp_time t s)"
  apply(subst tsqrt_imp_time.simps)
  apply(subst tsqrt_imp_time.simps)
  apply (auto simp add: tsqrt_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)
  done

lemma tsqrt_imp_time_acc_2: "(tsqrt_imp_time x s) = x + (tsqrt_imp_time 0 s)"
  by (induction x arbitrary: s)
     (auto simp add: tsqrt_imp_time_acc tsqrt_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)

definition tsqrt_IMP_Minus where
"tsqrt_IMP_Minus \<equiv>
  (
    (mul_prefix @ mul_a_str) ::= A (V tsqrt_y_str);;
    (mul_prefix @ mul_b_str) ::= A (N 8);;
    (mul_prefix @ mul_c_str) ::= A (N 0);;
    invoke_subprogram mul_prefix mul_IMP_minus;;

    \<comment> \<open>Could save an assignment here, combine with next one\<close>
    tsqrt_y_str ::= (V (mul_prefix @ mul_c_str) \<oplus> N 1);;

    (dsqrt_prefix @ dsqrt_y_str) ::= A (V tsqrt_y_str);;
    (dsqrt_prefix @ dsqrt_ret_str) ::= A (N 0);;
    invoke_subprogram dsqrt_prefix dsqrt_IMP_Minus;;

    tsqrt_y_str ::= (V (dsqrt_prefix @ dsqrt_ret_str) \<ominus> N 1);;
    tsqrt_ret_str ::= (V tsqrt_y_str\<then>)
  )"

definition "tsqrt_imp_to_HOL_state p s =
  \<lparr>tsqrt_state_y = (s (add_prefix p tsqrt_y_str)), tsqrt_state_ret = (s (add_prefix p tsqrt_ret_str))\<rparr>"

(* TODO: *)
(* Use the new style correctness lemma to be safe, replace the old ones later, also we need to do
  a standardization pass for naming *)
lemma mul_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ mul_pref) mul_IMP_minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>  v \<in> vars 
  \<Longrightarrow> \<not> (prefix mul_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars
  using prefix_def by blast

lemma mul_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) mul_IMP_minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (mul_imp_time 0 (mul_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) mul_c_str) = 
        mul_c (mul_imp (mul_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using mul_IMP_minus_correct_time mul_IMP_minus_correct_function
        mul_IMP_Minus_correct_effects 
  by auto


lemma tsqrt_IMP_Minus_correct_function: 
  "(invoke_subprogram p tsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p tsqrt_ret_str) = tsqrt_state_ret (tsqrt_imp (tsqrt_imp_to_HOL_state p s))"
  apply(subst tsqrt_imp.simps)
  apply(simp only: tsqrt_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(erule mul_IMP_Minus_correct[where vars = "tsqrt_IMP_vars"])
   apply auto[]
  apply(erule dsqrt_IMP_Minus_correct[where vars = "tsqrt_IMP_vars"])
   apply auto[]
  apply (drule AssignD)+
   apply (auto simp add: tsqrt_imp_state_upd_def tsqrt_imp_to_HOL_state_def dsqrt_imp_to_HOL_state_def
      mul_imp_to_HOL_state_def Let_def)
  done

lemma tsqrt_IMP_Minus_correct_time: 
  "(invoke_subprogram p tsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = tsqrt_imp_time 0 (tsqrt_imp_to_HOL_state p s)"
  apply(subst tsqrt_imp_time.simps)
  apply(simp only: tsqrt_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(erule mul_IMP_Minus_correct[where vars = "tsqrt_IMP_vars"])
   apply auto[]
  apply(erule dsqrt_IMP_Minus_correct[where vars = "tsqrt_IMP_vars"])
   apply auto[]
  apply (drule AssignD)+
   apply (auto simp add: tsqrt_imp_state_upd_def tsqrt_imp_to_HOL_state_def dsqrt_imp_to_HOL_state_def
      mul_imp_to_HOL_state_def Let_def)
  done

lemma tsqrt_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ tsqrt_pref) tsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>  v \<in> vars 
  \<Longrightarrow> \<not> (prefix tsqrt_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma tsqrt_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) tsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (tsqrt_imp_time 0 (tsqrt_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) tsqrt_ret_str) = 
        tsqrt_state_ret (tsqrt_imp (tsqrt_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using tsqrt_IMP_Minus_correct_time tsqrt_IMP_Minus_correct_function
        tsqrt_IMP_Minus_correct_effects 
  by auto

subsection \<open>Decoding products\<close>

definition "fst'_nat p \<equiv> p - triangle (tsqrt p)"

lemma fst'_nat_correct: "fst'_nat (prod_encode (m,n)) = m"
  unfolding prod_encode_def apply simp unfolding fst'_nat_def
  by (metis add.commute add_diff_cancel_left' le_add1 less_add_Suc2 nat_add_left_cancel_less triangle_Suc tsqrt_unique)

(* Connect to existing \<^const>\<open>fst_nat\<close>, unify this at some point*)
lemma fst_nat_fst'_nat: "fst_nat p = fst'_nat p"
  by (metis fst'_nat_correct fst_nat_def o_def prod.collapse prod_decode_inverse)

definition "snd'_nat p \<equiv> tsqrt p - fst'_nat p"

lemma snd'_nat_correct: "snd'_nat (prod_encode (m,n)) = n"
  unfolding prod_encode_def apply simp unfolding snd'_nat_def
  using fst'_nat_correct 
  by (metis add.commute add_diff_cancel_left' fst'_nat_def le_add1 less_add_Suc2 nat_add_left_cancel_less triangle_Suc tsqrt_unique)

(* Connect to existing \<^const>\<open>snd_nat\<close>, unify this at some point*)
lemma snd_nat_snd'_nat: "snd_nat p = snd'_nat p"
  by (metis snd'_nat_correct snd_nat_def o_def prod.collapse prod_decode_inverse)

record fst'_state = fst'_state_p :: nat

abbreviation "fst'_prefix \<equiv> ''fst'.''"
abbreviation "fst'_p_str \<equiv> ''p''"
abbreviation "fst'_internal_str \<equiv> ''internal''"

abbreviation 
  "fst'_IMP_vars \<equiv> {fst'_p_str, fst'_internal_str}"

(* Copying directly from function outputs *)
definition "fst'_imp_state_upd s = (let
    fst'_tsqrt_y = fst'_state_p s;
    fst'_tsqrt_ret = 0;
    fst'_tsqrt_state = \<lparr>tsqrt_state_y = fst'_tsqrt_y, tsqrt_state_ret = fst'_tsqrt_ret\<rparr>;
    fst'_tsqrt_ret = tsqrt_imp fst'_tsqrt_state;
    
    fst'_triangle_a = tsqrt_state_ret fst'_tsqrt_ret;
    fst'_triangle_triangle = 0;
    fst'_triangle_state = \<lparr>triangle_a = fst'_triangle_a, triangle_triangle = fst'_triangle_triangle\<rparr>;
    fst'_triangle_ret = triangle_imp fst'_triangle_state;

    fst'_p = fst'_state_p s - triangle_triangle fst'_triangle_ret;
    
    ret = \<lparr>fst'_state_p = fst'_p\<rparr>
  in
    ret)
"

fun fst'_imp :: "fst'_state \<Rightarrow> fst'_state" where
  "fst'_imp s = 
  (let
    ret = fst'_imp_state_upd s
  in
    ret
  )"

declare fst'_imp.simps [simp del]

lemma fst'_imp_correct:
   "fst'_state_p (fst'_imp s) = fst'_nat (fst'_state_p s)"
  by (subst fst'_imp.simps) (auto simp: dsqrt_imp_correct fst'_imp_state_upd_def tsqrt_imp_correct
      Let_def triangle_imp_correct fst'_nat_def split: if_splits)

fun fst'_imp_time:: "nat \<Rightarrow> fst'_state\<Rightarrow> nat" where
  "fst'_imp_time t s = 
    (
      let
        fst'_tsqrt_y = fst'_state_p s;
        t = t+2;
        fst'_tsqrt_ret = 0;
        t = t+2;
        fst'_tsqrt_state = \<lparr>tsqrt_state_y = fst'_tsqrt_y, tsqrt_state_ret = fst'_tsqrt_ret\<rparr>;
        fst'_tsqrt_ret = tsqrt_imp fst'_tsqrt_state;
        t = t + tsqrt_imp_time 0 fst'_tsqrt_state;
        
        fst'_triangle_a = tsqrt_state_ret fst'_tsqrt_ret;
        t = t+2;
        fst'_triangle_triangle = 0;
        t = t+2;
        fst'_triangle_state = \<lparr>triangle_a = fst'_triangle_a, triangle_triangle = fst'_triangle_triangle\<rparr>;
        fst'_triangle_ret = triangle_imp fst'_triangle_state;
        t = t + triangle_imp_time 0 fst'_triangle_state;
    
        fst'_p = fst'_state_p s - triangle_triangle fst'_triangle_ret;
        t = t+2;
        
        ret = t
      in
        ret
    )
"

lemmas [simp del] = fst'_imp_time.simps

lemma fst'_imp_time_acc: "(fst'_imp_time (Suc t) s) = Suc (fst'_imp_time t s)"
  apply(subst fst'_imp_time.simps)
  apply(subst fst'_imp_time.simps)
  apply (auto simp add: fst'_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)
  done

lemma fst'_imp_time_acc_2: "(fst'_imp_time x s) = x + (fst'_imp_time 0 s)"
  by (induction x arbitrary: s)
     (auto simp add: fst'_imp_time_acc fst'_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)

definition fst'_IMP_Minus where
"fst'_IMP_Minus \<equiv>
  (
    (tsqrt_prefix @ tsqrt_y_str) ::= A (V fst'_p_str);;
    (tsqrt_prefix @ tsqrt_ret_str) ::= A (N 0);;
    invoke_subprogram tsqrt_prefix tsqrt_IMP_Minus;;

    (triangle_prefix @ triangle_a_str) ::= A (V (tsqrt_prefix @ tsqrt_ret_str));;
    (triangle_prefix @ triangle_triangle_str) ::= A (N 0);;
    invoke_subprogram triangle_prefix triangle_IMP_Minus;;

    fst'_p_str ::= ((V fst'_p_str) \<ominus> V (triangle_prefix @ triangle_triangle_str))
  )"

definition "fst'_imp_to_HOL_state p s = \<lparr>fst'_state_p = (s (add_prefix p fst'_p_str))\<rparr>"

(* New correctness lemma, replace above *)
lemma triangle_IMP_Minus_correct_effects':
  "(invoke_subprogram (p @ triangle_pref) triangle_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> v \<in> vars 
  \<Longrightarrow> \<not> (prefix triangle_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def by blast

lemma triangle_IMP_Minus_correct':
  "\<lbrakk>(invoke_subprogram (p1 @ p2) triangle_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (triangle_imp_time 0 (triangle_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) triangle_triangle_str) = 
        triangle_triangle (triangle_imp (triangle_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using triangle_IMP_Minus_correct_time triangle_IMP_Minus_correct_function
        triangle_IMP_Minus_correct_effects'
  by auto

lemma fst'_IMP_Minus_correct_function: 
  "(invoke_subprogram p fst'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p fst'_p_str) = fst'_state_p (fst'_imp (fst'_imp_to_HOL_state p s))"
  apply(subst fst'_imp.simps)
  apply(simp only: fst'_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(erule tsqrt_IMP_Minus_correct[where vars = "fst'_IMP_vars"])
   apply auto[]
  apply(erule triangle_IMP_Minus_correct'[where vars = "fst'_IMP_vars"])
  apply auto[]
  (* Seems to work, but looks like automation needs to figure out that the input variable is not changed during the program
    No idea if this is new
  *)
   apply (fastforce simp add: fst'_imp_state_upd_def fst'_imp_to_HOL_state_def tsqrt_imp_to_HOL_state_def
      triangle_imp_to_HOL_state_def Let_def)
  done

lemma fst'_IMP_Minus_correct_time: 
  "(invoke_subprogram p fst'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = fst'_imp_time 0 (fst'_imp_to_HOL_state p s)"
  apply(subst fst'_imp_time.simps)
  apply(simp only: fst'_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(erule tsqrt_IMP_Minus_correct[where vars = "fst'_IMP_vars"])
   apply auto[]
  apply(erule triangle_IMP_Minus_correct'[where vars = "fst'_IMP_vars"])
  apply auto[]
  (* Seems to work, but looks like automation needs to figure out that the input variable is not changed during the program
    No idea if this is new
  *)
   apply (fastforce simp add: fst'_imp_state_upd_def fst'_imp_to_HOL_state_def tsqrt_imp_to_HOL_state_def
      triangle_imp_to_HOL_state_def Let_def)
  done

lemma fst'_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ fst'_pref) fst'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>  v \<in> vars 
  \<Longrightarrow> \<not> (prefix fst'_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma fst'_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) fst'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (fst'_imp_time 0 (fst'_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) fst'_p_str) = 
        fst'_state_p (fst'_imp (fst'_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using fst'_IMP_Minus_correct_time fst'_IMP_Minus_correct_function
        fst'_IMP_Minus_correct_effects 
  by auto


record snd'_state = snd'_state_p :: nat
abbreviation "snd'_prefix \<equiv> ''snd'.''"
abbreviation "snd'_p_str \<equiv> ''p''"

abbreviation 
  "snd'_IMP_vars \<equiv> {snd'_p_str}"

(* Copying directly from function outputs *)
definition "snd'_imp_state_upd s = (let
    snd'_tsqrt_y = snd'_state_p s;
    snd'_tsqrt_ret = 0;
    snd'_tsqrt_state = \<lparr>tsqrt_state_y = snd'_tsqrt_y, tsqrt_state_ret = snd'_tsqrt_ret\<rparr>;
    snd'_tsqrt_ret = tsqrt_imp snd'_tsqrt_state;
    
    snd'_fst'_p = snd'_state_p s;
    snd'_fst'_state = \<lparr>fst'_state_p = snd'_fst'_p\<rparr>;
    snd'_fst'_ret = fst'_imp snd'_fst'_state;

    snd'_p = tsqrt_state_ret snd'_tsqrt_ret - fst'_state_p snd'_fst'_ret;
    
    ret = \<lparr>snd'_state_p = snd'_p\<rparr>
  in
    ret)
"

fun snd'_imp :: "snd'_state \<Rightarrow> snd'_state" where
  "snd'_imp s = 
  (let
    ret = snd'_imp_state_upd s
  in
    ret
  )"

declare snd'_imp.simps [simp del]

lemma snd'_imp_correct:
   "snd'_state_p (snd'_imp s) = snd'_nat (snd'_state_p s)"
  by (subst snd'_imp.simps) (auto simp: dsqrt_imp_correct snd'_imp_state_upd_def tsqrt_imp_correct
      fst'_imp_correct snd'_nat_def)

fun snd'_imp_time:: "nat \<Rightarrow> snd'_state\<Rightarrow> nat" where
  "snd'_imp_time t s = 
    (
      let
        snd'_tsqrt_y = snd'_state_p s;
        t = t+2;
        snd'_tsqrt_ret = 0;
        t = t+2;
        snd'_tsqrt_state = \<lparr>tsqrt_state_y = snd'_tsqrt_y, tsqrt_state_ret = snd'_tsqrt_ret\<rparr>;
        snd'_tsqrt_ret = tsqrt_imp snd'_tsqrt_state;
        t = t + tsqrt_imp_time 0 snd'_tsqrt_state;
        
        snd'_fst'_p = snd'_state_p s;
        t = t+2;
        snd'_fst'_state = \<lparr>fst'_state_p = snd'_fst'_p\<rparr>;
        snd'_fst'_ret = fst'_imp snd'_fst'_state;
        t = t + fst'_imp_time 0 snd'_fst'_state;
    
        snd'_p = tsqrt_state_ret snd'_tsqrt_ret - fst'_state_p snd'_fst'_ret;
        t = t+2;
        
        ret = t
      in
        ret
    )
"

lemmas [simp del] = snd'_imp_time.simps

lemma snd'_imp_time_acc: "(snd'_imp_time (Suc t) s) = Suc (snd'_imp_time t s)"
  apply(subst snd'_imp_time.simps)
  apply(subst snd'_imp_time.simps)
  apply (auto simp add: snd'_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)
  done

lemma snd'_imp_time_acc_2: "(snd'_imp_time x s) = x + (snd'_imp_time 0 s)"
  by (induction x arbitrary: s)
     (auto simp add: snd'_imp_time_acc snd'_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)

definition snd'_IMP_Minus where
"snd'_IMP_Minus \<equiv>
  (
    (tsqrt_prefix @ tsqrt_y_str) ::= A (V snd'_p_str);;
    (tsqrt_prefix @ tsqrt_ret_str) ::= A (N 0);;
    invoke_subprogram tsqrt_prefix tsqrt_IMP_Minus;;

    (fst'_prefix @ fst'_p_str) ::= A (V snd'_p_str);;
    invoke_subprogram fst'_prefix fst'_IMP_Minus;;

    snd'_p_str ::= ((V (tsqrt_prefix @ tsqrt_ret_str)) \<ominus> V (fst'_prefix @ fst'_p_str))
  )"

definition "snd'_imp_to_HOL_state p s = \<lparr>snd'_state_p = (s (add_prefix p snd'_p_str))\<rparr>"

lemma snd'_IMP_Minus_correct_function: 
  "(invoke_subprogram p snd'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p snd'_p_str) = snd'_state_p (snd'_imp (snd'_imp_to_HOL_state p s))"
  apply(subst snd'_imp.simps)
  apply(simp only: snd'_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(erule tsqrt_IMP_Minus_correct[where vars = "snd'_IMP_vars"])
   apply auto[]
  (* Not copying means I might have to pass the return variables here *)
  apply(erule fst'_IMP_Minus_correct[where vars = "insert (tsqrt_prefix @ tsqrt_ret_str) snd'_IMP_vars"])
  apply auto[]
   apply (force simp add: snd'_imp_state_upd_def snd'_imp_to_HOL_state_def tsqrt_imp_to_HOL_state_def
      fst'_imp_to_HOL_state_def Let_def)
  done
    

lemma snd'_IMP_Minus_correct_time: 
  "(invoke_subprogram p snd'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = snd'_imp_time 0 (snd'_imp_to_HOL_state p s)"
  apply(subst snd'_imp_time.simps)
  apply(simp only: snd'_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(erule tsqrt_IMP_Minus_correct[where vars = "snd'_IMP_vars"])
   apply auto[]
  (* Not copying means I might have to pass the return variables here *)
  apply(erule fst'_IMP_Minus_correct[where vars = "insert (tsqrt_prefix @ tsqrt_ret_str) snd'_IMP_vars"])
  apply auto[]
   apply (force simp add: snd'_imp_state_upd_def snd'_imp_to_HOL_state_def tsqrt_imp_to_HOL_state_def
      fst'_imp_to_HOL_state_def Let_def)
  done

lemma snd'_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ snd'_pref) snd'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>  v \<in> vars 
  \<Longrightarrow> \<not> (prefix snd'_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma snd'_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) snd'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (snd'_imp_time 0 (snd'_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) snd'_p_str) = 
        snd'_state_p (snd'_imp (snd'_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using snd'_IMP_Minus_correct_time snd'_IMP_Minus_correct_function
        snd'_IMP_Minus_correct_effects 
  by auto

(* Restore prod_decode *)

record prod_decode_state = prod_decode_state_p :: nat prod_decode_state_fst :: nat prod_decode_state_snd :: nat

abbreviation "prod_decode_prefix \<equiv> ''prod_decode.''"
abbreviation "prod_decode_p_str \<equiv> ''p''"
abbreviation "prod_decode_fst_str \<equiv> ''fst''"
abbreviation "prod_decode_snd_str \<equiv> ''snd''"

abbreviation 
  "prod_decode_IMP_vars \<equiv> {prod_decode_p_str, prod_decode_fst_str, prod_decode_snd_str}"

(* Copying directly from function outputs *)
definition "prod_decode_imp_state_upd s = (let
    prod_decode_fst'_p = prod_decode_state_p s;
    prod_decode_fst'_state = \<lparr>fst'_state_p = prod_decode_fst'_p\<rparr>;
    prod_decode_fst'_ret = fst'_imp prod_decode_fst'_state;
    prod_decode_fst = fst'_state_p prod_decode_fst'_ret;

    prod_decode_snd'_p = prod_decode_state_p s;
    prod_decode_snd'_state = \<lparr>snd'_state_p = prod_decode_snd'_p\<rparr>;
    prod_decode_snd'_ret = snd'_imp prod_decode_snd'_state;
    prod_decode_snd = snd'_state_p prod_decode_snd'_ret;
    
    ret = \<lparr>prod_decode_state_p = prod_decode_state_p s, 
      prod_decode_state_fst = prod_decode_fst, prod_decode_state_snd = prod_decode_snd\<rparr>
  in
    ret)
"

fun prod_decode_imp :: "prod_decode_state \<Rightarrow> prod_decode_state" where
  "prod_decode_imp s = 
  (let
    ret = prod_decode_imp_state_upd s
  in
    ret
  )"

declare prod_decode_imp.simps [simp del]

lemma prod_decode_imp_correct':
   "prod_decode_state_fst (prod_decode_imp s) = fst'_nat (prod_decode_state_p s)"
   "prod_decode_state_snd (prod_decode_imp s) = snd'_nat (prod_decode_state_p s)"
  by (all \<open>subst prod_decode_imp.simps\<close>) (auto simp: fst'_imp_correct snd'_imp_correct 
      prod_decode_imp_state_upd_def)

lemma prod_decode_imp_correct:
   "prod_decode_state_fst (prod_decode_imp s) = fst_nat (prod_decode_state_p s)"
   "prod_decode_state_snd (prod_decode_imp s) = snd_nat (prod_decode_state_p s)"
  by (simp_all add: fst_nat_fst'_nat snd_nat_snd'_nat prod_decode_imp_correct')

fun prod_decode_imp_time:: "nat \<Rightarrow> prod_decode_state\<Rightarrow> nat" where
  "prod_decode_imp_time t s = 
    (
      let
        prod_decode_fst'_p = prod_decode_state_p s;
        t = t+2;
        prod_decode_fst'_state = \<lparr>fst'_state_p = prod_decode_fst'_p\<rparr>;
        prod_decode_fst'_ret = fst'_imp prod_decode_fst'_state;
        t = t + fst'_imp_time 0 prod_decode_fst'_state;
        prod_decode_fst = fst'_state_p prod_decode_fst'_ret;
        t = t+2;
    
        prod_decode_snd'_p = prod_decode_state_p s;
        t = t+2;
        prod_decode_snd'_state = \<lparr>snd'_state_p = prod_decode_snd'_p\<rparr>;
        prod_decode_snd'_ret = snd'_imp prod_decode_snd'_state;
        t = t + snd'_imp_time 0 prod_decode_snd'_state;
        prod_decode_snd = snd'_state_p prod_decode_snd'_ret;
        t = t+2;
        
        ret = t
      in
        ret
    )
"

lemmas [simp del] = prod_decode_imp_time.simps

lemma prod_decode_imp_time_acc: "(prod_decode_imp_time (Suc t) s) = Suc (prod_decode_imp_time t s)"
  apply(subst prod_decode_imp_time.simps)
  apply(subst prod_decode_imp_time.simps)
  apply (auto simp add: prod_decode_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)
  done

lemma prod_decode_imp_time_acc_2: "(prod_decode_imp_time x s) = x + (prod_decode_imp_time 0 s)"
  by (induction x arbitrary: s)
     (auto simp add: prod_decode_imp_time_acc prod_decode_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)

definition prod_decode_IMP_Minus where
"prod_decode_IMP_Minus \<equiv>
  (
    (fst'_prefix @ fst'_p_str) ::= A (V prod_decode_p_str);;
    invoke_subprogram fst'_prefix fst'_IMP_Minus;;
    prod_decode_fst_str ::= A (V (fst'_prefix @ fst'_p_str));;

    (snd'_prefix @ snd'_p_str) ::= A (V prod_decode_p_str);;
    invoke_subprogram snd'_prefix snd'_IMP_Minus;;
    prod_decode_snd_str ::= A (V (snd'_prefix @ snd'_p_str))
  )"

definition "prod_decode_imp_to_HOL_state p s = \<lparr>prod_decode_state_p = (s (add_prefix p prod_decode_p_str)),
  prod_decode_state_fst = (s (add_prefix p prod_decode_fst_str)),
  prod_decode_state_snd = (s (add_prefix p prod_decode_snd_str))\<rparr>"

lemma prod_decode_IMP_Minus_correct_function_1: 
  "(invoke_subprogram p prod_decode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p prod_decode_fst_str) = prod_decode_state_fst (prod_decode_imp (prod_decode_imp_to_HOL_state p s))"
  apply(subst prod_decode_imp.simps)
  apply(simp only: prod_decode_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(erule fst'_IMP_Minus_correct[where vars = "prod_decode_IMP_vars"])
   apply auto[]
  apply(erule snd'_IMP_Minus_correct[where vars = "prod_decode_IMP_vars"])
   apply auto[] (* Check why this is taking so much longer *)
  apply (force simp add: prod_decode_imp_state_upd_def prod_decode_imp_to_HOL_state_def tsqrt_imp_to_HOL_state_def
      fst'_imp_to_HOL_state_def snd'_imp_to_HOL_state_def Let_def)
  done

lemma prod_decode_IMP_Minus_correct_function_2: 
  "(invoke_subprogram p prod_decode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p prod_decode_snd_str) = prod_decode_state_snd (prod_decode_imp (prod_decode_imp_to_HOL_state p s))"
  apply(subst prod_decode_imp.simps)
  apply(simp only: prod_decode_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(erule fst'_IMP_Minus_correct[where vars = "prod_decode_IMP_vars"])
   apply auto[]
  apply(erule snd'_IMP_Minus_correct[where vars = "prod_decode_IMP_vars"])
   apply auto[] (* Check why this is taking so much longer *)
  apply (force simp add: prod_decode_imp_state_upd_def prod_decode_imp_to_HOL_state_def tsqrt_imp_to_HOL_state_def
      fst'_imp_to_HOL_state_def snd'_imp_to_HOL_state_def Let_def)
  done
    

lemma prod_decode_IMP_Minus_correct_time: 
  "(invoke_subprogram p prod_decode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = prod_decode_imp_time 0 (prod_decode_imp_to_HOL_state p s)"
  apply(subst prod_decode_imp_time.simps)
  apply(simp only: prod_decode_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(erule fst'_IMP_Minus_correct[where vars = "prod_decode_IMP_vars"])
   apply auto[]
  apply(erule snd'_IMP_Minus_correct[where vars = "prod_decode_IMP_vars"])
   apply auto[]
  apply (force simp add: prod_decode_imp_state_upd_def prod_decode_imp_to_HOL_state_def tsqrt_imp_to_HOL_state_def
      fst'_imp_to_HOL_state_def snd'_imp_to_HOL_state_def Let_def)
  done

lemma prod_decode_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ prod_decode_pref) prod_decode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>  v \<in> vars 
  \<Longrightarrow> \<not> (prefix prod_decode_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma prod_decode_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) prod_decode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (prod_decode_imp_time 0 (prod_decode_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) prod_decode_fst_str) 
        = prod_decode_state_fst (prod_decode_imp (prod_decode_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) prod_decode_snd_str)
        = prod_decode_state_snd (prod_decode_imp (prod_decode_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using prod_decode_IMP_Minus_correct_time 
        prod_decode_IMP_Minus_correct_function_1 prod_decode_IMP_Minus_correct_function_2
        prod_decode_IMP_Minus_correct_effects 
  by auto

record prod_encode_state = prod_encode_a::nat prod_encode_b::nat prod_encode_ret::nat

abbreviation "prod_encode_prefix \<equiv> ''prod_encode.''"
abbreviation "prod_encode_a_str \<equiv> ''a''"
abbreviation "prod_encode_b_str \<equiv> ''b''"
abbreviation "prod_encode_ret_str \<equiv> ''prod_encode_ret''"

definition "prod_encode_state_upd (s::prod_encode_state) \<equiv>
      let
        triangle_a = prod_encode_a s + prod_encode_b s;
        triangle_triangle' = 0;
        (triangle_state::triangle_state) = \<lparr>triangle_a = triangle_a, triangle_triangle = triangle_triangle'\<rparr>;
        triangle_ret = (triangle_imp triangle_state);
        prod_encode_ret = triangle_triangle triangle_ret;
        prod_encode_ret = prod_encode_ret + prod_encode_a s;
        ret = \<lparr>prod_encode_a = prod_encode_a s,prod_encode_b = prod_encode_b s, prod_encode_ret = prod_encode_ret\<rparr>
      in
        ret
"

fun prod_encode_imp:: "prod_encode_state \<Rightarrow> prod_encode_state" where
"prod_encode_imp s = 
  (let
     ret = prod_encode_state_upd s
   in
     ret
  )"

lemmas [simp del] = prod_encode_imp.simps

lemma prod_encode_imp_correct: "prod_encode_ret (prod_encode_imp s) = prod_encode (prod_encode_a s, prod_encode_b s)"
proof (induction s rule: prod_encode_imp.induct)
  case (1 s)
  then show ?case
    by (auto simp: prod_encode_imp.simps prod_encode_def prod_encode_state_upd_def Let_def triangle_imp_correct split: if_splits)
qed 

fun prod_encode_imp_time:: "nat \<Rightarrow> prod_encode_state \<Rightarrow> nat" where
"prod_encode_imp_time t s = 
  (let
     triangle_a = prod_encode_a s + prod_encode_b s;
     t = t + 2;
     triangle_triangle' = 0;
     t = t + 2;
     (triangle_state::triangle_state) = \<lparr>triangle_a = triangle_a, triangle_triangle = triangle_triangle'\<rparr>;
     triangle_ret = (triangle_imp triangle_state);
     t = t + triangle_imp_time 0 triangle_state;
     prod_encode_ret = triangle_triangle triangle_ret;
     t = t + 2;
     prod_encode_ret = prod_encode_ret + prod_encode_a s;
     t = t + 2;
     ret = t
   in
     ret
  )"

lemmas [simp del] = prod_encode_imp_time.simps

lemma prod_encode_imp_time_acc: "(prod_encode_imp_time (Suc t) s) = Suc (prod_encode_imp_time t s)"
  by (induction t s rule: prod_encode_imp_time.induct)
     (auto simp add: prod_encode_imp_time.simps Let_def eval_nat_numeral split: if_splits)

(*        triangle_a = prod_encode_a s + prod_encode_b s;
        (triangle_state::triangle_state) = \<lparr>triangle_a = triangle_a, triangle_triangle = 0\<rparr>;
        triangle_ret = (triangle_imp triangle_state);
        prod_encode_ret = triangle_triangle triangle_ret + prod_encode_a s;
*)

definition prod_encode_IMP_Minus where "prod_encode_IMP_Minus \<equiv>
  (triangle_prefix @ triangle_a_str) ::= ((V prod_encode_a_str) \<oplus> (V prod_encode_b_str)) ;;
  (triangle_prefix @ triangle_triangle_str) ::= (A (N 0)) ;;
  invoke_subprogram triangle_prefix triangle_IMP_Minus ;;
  prod_encode_ret_str ::= (A (V (triangle_prefix @ triangle_triangle_str))) ;;
  prod_encode_ret_str ::= ((V prod_encode_a_str) \<oplus> (V prod_encode_ret_str))"

definition "prod_encode_imp_to_HOL_state p s =
  \<lparr>prod_encode_a = s (add_prefix p prod_encode_a_str), prod_encode_b = s (add_prefix p prod_encode_b_str), prod_encode_ret = (s (add_prefix p prod_encode_ret_str))\<rparr>"

lemma notD: "x \<notin> s \<Longrightarrow> (x \<in> s \<Longrightarrow> False)"
  by auto

lemma prod_encode_IMP_Minus_correct_function: 
  "(invoke_subprogram p prod_encode_IMP_Minus, s) 
      \<Rightarrow>\<^bsup>t \<^esup> s'
    \<Longrightarrow> s' (add_prefix p prod_encode_ret_str) = prod_encode_ret (prod_encode_imp (prod_encode_imp_to_HOL_state p s))"
  apply(simp only: prod_encode_IMP_Minus_def prod_encode_imp.simps com_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  \<comment> \<open>Variables that we want to preserve: variables of this program minus the variables of the
     program we call. If automation fails, this should be manually chosen variables.\<close>
  apply(erule triangle_IMP_Minus_correct[where vars = "{p @ prod_encode_a_str}"])
  apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: prod_encode_state_upd_def Let_def prod_encode_imp_to_HOL_state_def)[1]
  apply(auto simp: triangle_imp_to_HOL_state_def)[1]
  done

lemma prod_encode_IMP_Minus_correct_time: 
  "(invoke_subprogram p prod_encode_IMP_Minus, s) 
      \<Rightarrow>\<^bsup>t\<^esup> s'
    \<Longrightarrow> t = prod_encode_imp_time 0 (prod_encode_imp_to_HOL_state p s)"
  apply(simp only: prod_encode_IMP_Minus_def prod_encode_imp_time.simps com_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  \<comment> \<open>Variables that we want to preserve: variables of this program minus the variables of the
     program we call. If automation fails, this should be manually chosen variables.\<close>
  apply(erule triangle_IMP_Minus_correct[where vars = "{p @ ''a''}"])
  apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: prod_encode_state_upd_def Let_def prod_encode_imp_to_HOL_state_def)[1]
  apply(auto simp: triangle_imp_to_HOL_state_def)[1]
  done

lemma prod_encode_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ prod_encode_pref) prod_encode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> p @ v \<in> vars \<Longrightarrow> \<not> (set prod_encode_pref \<subseteq> set v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma prod_encode_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) prod_encode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
     \<lbrakk>t = (prod_encode_imp_time 0 (prod_encode_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) prod_encode_ret_str) = prod_encode_ret (prod_encode_imp (prod_encode_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. p1 @ v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v) \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using prod_encode_IMP_Minus_correct_time prod_encode_IMP_Minus_correct_function
        prod_encode_IMP_Minus_correct_effects 
  by auto

(*
record prod_decode_aux_state = prod_decode_aux_k::nat prod_decode_aux_m::nat

abbreviation "prod_decode_aux_pref \<equiv> ''prod_decode_aux.''"
abbreviation "prod_decode_aux_k_str \<equiv> ''k''"
abbreviation "prod_decode_aux_m_str \<equiv> ''m''"

definition "prod_decode_aux_state_upd s \<equiv>
      let
        prod_decode_aux_k' = Suc (prod_decode_aux_k s);
        prod_decode_aux_m' = (prod_decode_aux_m s) - prod_decode_aux_k';
        ret = \<lparr>prod_decode_aux_k = prod_decode_aux_k', prod_decode_aux_m = prod_decode_aux_m'\<rparr>
      in
        ret
"

function prod_decode_aux_imp :: "prod_decode_aux_state \<Rightarrow> prod_decode_aux_state"
  where "prod_decode_aux_imp s =    
    (if prod_decode_aux_m s - prod_decode_aux_k s  \<noteq> 0 \<comment> \<open>while condition\<close>
     then
       let
         next_iteration = prod_decode_aux_imp (prod_decode_aux_state_upd s)
       in
         next_iteration
     else
       s)"
  by pat_completeness auto
termination
  by  (relation "Wellfounded.measure (\<lambda>s. prod_decode_aux_m s)")  (auto simp: prod_decode_aux_state_upd_def Let_def split: if_splits)

declare prod_decode_aux_imp.simps [simp del]

lemma prod_decode_aux_imp_correct:
  "prod_decode_aux_m (prod_decode_aux_imp s) = fst (prod_decode_aux (prod_decode_aux_k s) (prod_decode_aux_m s))"(is ?g1)
  "prod_decode_aux_k (prod_decode_aux_imp s) - prod_decode_aux_m (prod_decode_aux_imp s) = snd (prod_decode_aux (prod_decode_aux_k s) (prod_decode_aux_m s))" (is ?g2)
proof-
  show ?g1
  proof (induction s rule: prod_decode_aux_imp.induct)
    case (1 s)
    then show ?case
      apply(subst prod_decode_aux_imp.simps)
      apply (auto simp: prod_decode_aux_state_upd_def Let_def split: if_splits)
       apply (metis diff_is_0_eq prod_decode_aux.simps prod_decode_aux_imp.simps prod_decode_aux_state_upd_def)
      by (simp add: prod_decode_aux.simps prod_decode_aux_imp.simps)
  qed
  show ?g2
  proof (induction s rule: prod_decode_aux_imp.induct)
    case (1 s)
    then show ?case
      apply(subst prod_decode_aux_imp.simps)
      apply (auto simp: prod_decode_aux_state_upd_def Let_def split: if_splits)
       apply (metis diff_is_0_eq prod_decode_aux.simps prod_decode_aux_imp.simps prod_decode_aux_state_upd_def)
      by (simp add: prod_decode_aux.simps prod_decode_aux_imp.simps)
  qed
qed 

function prod_decode_aux_imp_time:: "nat \<Rightarrow> prod_decode_aux_state\<Rightarrow> nat" where
"prod_decode_aux_imp_time t s = 
(
    (if prod_decode_aux_m s - prod_decode_aux_k s \<noteq> 0 then \<comment> \<open>While\<close>
      (
        let
          t = t + 3; \<comment> \<open>To account for while loop condition checking and difference computation\<close>
          prod_decode_aux_k' = Suc (prod_decode_aux_k s);
          t = t + 2;
          prod_decode_aux_m' = (prod_decode_aux_m s) - prod_decode_aux_k';
          t = t + 2;
          next_iteration = prod_decode_aux_imp_time t (prod_decode_aux_state_upd s)
        in
          next_iteration
      )
    else
      (
         \<comment> \<open>To account for the two steps of checking the condition, skipping the loop, and the difference computation\<close>
        let
          t = t + 4;
          ret = t
        in
          ret
      )
    )
)"
  by pat_completeness auto
termination
  by  (relation "Wellfounded.measure (\<lambda>(t, s). prod_decode_aux_m s)")  (auto simp: prod_decode_aux_state_upd_def Let_def split: if_splits)

lemmas [simp del] = prod_decode_aux_imp_time.simps

lemma prod_decode_aux_imp_time_acc: "(prod_decode_aux_imp_time (Suc t) s) = Suc (prod_decode_aux_imp_time t s)"
  by (induction t s arbitrary:  rule: prod_decode_aux_imp_time.induct)
     (auto simp add: prod_decode_aux_imp_time.simps prod_decode_aux_state_upd_def Let_def eval_nat_numeral split: if_splits)

definition prod_decode_aux_IMP_Minus where
"prod_decode_aux_IMP_Minus \<equiv>
  (\<comment> \<open>if prod_decode_aux_m s - prod_decode_aux_k s \<noteq> 0 then\<close>
   ''diff'' ::= ((V prod_decode_aux_m_str) \<ominus> (V prod_decode_aux_k_str));;
   WHILE ''diff''\<noteq>0 DO (
        \<comment> \<open>prod_decode_aux_k' = Suc (prod_decode_aux_k s);\<close>
        prod_decode_aux_k_str ::= ((V prod_decode_aux_k_str) \<oplus> (N 1));;
        \<comment> \<open>prod_decode_aux_m' = (prod_decode_aux_m s) - prod_decode_aux_k';\<close>
        prod_decode_aux_m_str ::= ((V prod_decode_aux_m_str) \<ominus> (V prod_decode_aux_k_str));;
        ''diff'' ::= ((V prod_decode_aux_m_str) \<ominus> (V prod_decode_aux_k_str)))
  )"

definition "prod_decode_aux_imp_to_HOL_state p s =
  \<lparr>prod_decode_aux_k = s (add_prefix p prod_decode_aux_k_str), prod_decode_aux_m = (s (add_prefix p prod_decode_aux_m_str))\<rparr>"

lemma prod_decode_aux_IMP_Minus_correct_function_1: 
  "(invoke_subprogram p prod_decode_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p prod_decode_aux_m_str) = 
       prod_decode_aux_m (prod_decode_aux_imp (prod_decode_aux_imp_to_HOL_state p s))"
  apply(induction "prod_decode_aux_imp_to_HOL_state p s" arbitrary: s s' t rule: prod_decode_aux_imp.induct)
  apply(simp only: prod_decode_aux_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps)
  apply(erule Seq_tE)
  apply(erule While_tE)
   apply(drule AssignD)+
   apply(subst prod_decode_aux_imp.simps)
   apply(auto simp: prod_decode_aux_imp_to_HOL_state_def)[1]
  apply(erule Seq_tE)
  apply(erule Seq_tE_While_init)
  apply simp
  apply(dest_com_init_while)
  apply(erule Seq_tE)+
   apply(drule AssignD)+
   apply(elim conjE)
   apply(subst prod_decode_aux_imp.simps mul_imp_time.simps)
   apply(auto simp: prod_decode_aux_imp_to_HOL_state_def prod_decode_aux_state_upd_def)[1]
  done

lemma prod_decode_aux_IMP_Minus_correct_function_2: 
  "(invoke_subprogram p prod_decode_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p prod_decode_aux_k_str) = 
       prod_decode_aux_k (prod_decode_aux_imp (prod_decode_aux_imp_to_HOL_state p s))"
  apply(induction "prod_decode_aux_imp_to_HOL_state p s" arbitrary: s s' t rule: prod_decode_aux_imp.induct)
  apply(simp only: prod_decode_aux_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps)
  apply(erule Seq_tE)
  apply(erule While_tE)
   apply(drule AssignD)+
   apply(subst prod_decode_aux_imp.simps)
   apply(auto simp: prod_decode_aux_imp_to_HOL_state_def)[1]
  apply(erule Seq_tE)
  apply(erule Seq_tE_While_init)
  apply assumption
  apply(dest_com_init_while)
  apply(erule Seq_tE)+
   apply(drule AssignD)+
   apply(elim conjE)
   apply(subst prod_decode_aux_imp.simps)
   apply(auto simp: prod_decode_aux_imp_to_HOL_state_def prod_decode_aux_state_upd_def)[1]
  done

lemma prod_decode_aux_IMP_Minus_correct_time: 
  "(invoke_subprogram p prod_decode_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = 
       prod_decode_aux_imp_time 0 (prod_decode_aux_imp_to_HOL_state p s)"
  apply(induction "prod_decode_aux_imp_to_HOL_state p s" arbitrary: s s' t rule: prod_decode_aux_imp.induct)
  apply(simp only: prod_decode_aux_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps)
  apply(erule Seq_tE)
  apply(erule While_tE)
   apply(drule AssignD)+
   apply(subst prod_decode_aux_imp_time.simps)
   apply(auto simp: prod_decode_aux_imp_to_HOL_state_def)[1]
  apply(erule Seq_tE)
  apply(erule Seq_tE_While_init)
  apply assumption
  apply(dest_com_init_while)
  apply(erule Seq_tE)+
   apply(drule AssignD)+
   apply(elim conjE)
   apply(subst prod_decode_aux_imp_time.simps)
  apply(auto simp: prod_decode_aux_imp_to_HOL_state_def prod_decode_aux_state_upd_def
                   eval_nat_numeral prod_decode_aux_imp_time_acc)[1]
  done

lemma prod_decode_aux_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ p2) prod_decode_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> p @ v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma prod_decode_aux_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) prod_decode_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
     \<lbrakk>t = (prod_decode_aux_imp_time 0 (prod_decode_aux_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) prod_decode_aux_m_str) =
         prod_decode_aux_m (prod_decode_aux_imp (prod_decode_aux_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) prod_decode_aux_k_str) =
         prod_decode_aux_k (prod_decode_aux_imp (prod_decode_aux_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. p1 @ v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v) \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using prod_decode_aux_IMP_Minus_correct_time prod_decode_aux_IMP_Minus_correct_function_1
        prod_decode_aux_IMP_Minus_correct_function_2
        prod_decode_aux_IMP_Minus_correct_effects 
  by auto

record prod_decode_state = prod_decode_m::nat prod_decode_fst_ret::nat prod_decode_snd_ret::nat

abbreviation "prod_decode_prefix \<equiv> ''prod_decode.''"
abbreviation "prod_decode_m_str \<equiv> ''m''"
abbreviation "prod_decode_fst_ret_str \<equiv> ''fst_ret''"
abbreviation "prod_decode_snd_ret_str \<equiv> ''snd_ret''"

definition "prod_decode_state_upd s \<equiv>
      let
        prod_decode_aux_k' = 0;
        prod_decode_aux_m' = (prod_decode_m s);
        prod_decode_aux_state = \<lparr>prod_decode_aux_k = prod_decode_aux_k', prod_decode_aux_m = prod_decode_aux_m'\<rparr>;
        prod_decode_aux_ret = prod_decode_aux_imp prod_decode_aux_state;
        fst_ret' = prod_decode_aux_m prod_decode_aux_ret;
        snd_ret' = prod_decode_aux_k prod_decode_aux_ret - prod_decode_aux_m prod_decode_aux_ret;
        ret = \<lparr>prod_decode_m = prod_decode_m s, fst_ret = fst_ret', snd_ret = snd_ret'\<rparr>
      in
        ret
"

fun prod_decode_imp :: "prod_decode_state \<Rightarrow> prod_decode_state"
  where "prod_decode_imp s =    
    (let
       ret = (prod_decode_state_upd s)
     in
         ret)
"

declare prod_decode_imp.simps [simp del]

lemma prod_decode_imp_correct:
   "prod_decode_fst_ret (prod_decode_imp s) = fst (prod_decode (prod_decode_m s))"
   "prod_decode_snd_ret (prod_decode_imp s) = snd (prod_decode (prod_decode_m s))"
   apply(subst prod_decode_imp.simps)
  apply (auto simp: prod_decode_aux_imp_correct(1) prod_decode_def prod_decode_imp.simps prod_decode_state_upd_def  Let_def split: if_splits)[1]
   apply(subst prod_decode_imp.simps)
  apply (auto simp: prod_decode_aux_imp_correct(2) prod_decode_def prod_decode_imp.simps prod_decode_state_upd_def  Let_def split: if_splits)[1]
  done


fun prod_decode_imp_time:: "nat \<Rightarrow> prod_decode_state\<Rightarrow> nat" where
  "prod_decode_imp_time t s = 
(
        let
          prod_decode_aux_k' = 0;
          t = t + 2;
          prod_decode_aux_m' = (prod_decode_m s);
          t = t + 2;
          prod_decode_aux_state = \<lparr>prod_decode_aux_k = prod_decode_aux_k', prod_decode_aux_m = prod_decode_aux_m'\<rparr>;
          prod_decode_aux_ret = prod_decode_aux_imp prod_decode_aux_state;
          t = t + prod_decode_aux_imp_time 0 prod_decode_aux_state;
          fst_ret' = prod_decode_aux_m prod_decode_aux_ret;
          t = t + 2;
          snd_ret' = prod_decode_aux_k prod_decode_aux_ret - prod_decode_aux_m prod_decode_aux_ret;
          t = t + 2;
          ret = t
        in
          ret
      )
"

lemmas [simp del] = prod_decode_imp_time.simps

lemma prod_decode_imp_time_acc: "(prod_decode_imp_time (Suc t) s) = Suc (prod_decode_imp_time t s)"
  by (induction t s arbitrary:  rule: prod_decode_imp_time.induct)
     (auto simp add: prod_decode_imp_time.simps prod_decode_state_upd_def Let_def eval_nat_numeral split: if_splits)

definition prod_decode_IMP_Minus where
"prod_decode_IMP_Minus \<equiv>
  (     \<comment> \<open>prod_decode_aux_k' = 0;\<close>
   (prod_decode_aux_pref @ prod_decode_aux_k_str) ::= (A (N 0));;
        \<comment> \<open>prod_decode_aux_m' = (prod_decode_m s);\<close>
   (prod_decode_aux_pref @ prod_decode_aux_m_str) ::= (A (V prod_decode_m_str));;
        \<comment> \<open>prod_decode_aux_state = \<lparr>prod_decode_aux_k = prod_decode_aux_k', prod_decode_aux_m = prod_decode_aux_m'\<rparr>;\<close>
        \<comment> \<open>prod_decode_aux_ret = prod_decode_aux_imp prod_decode_aux_state;\<close>
   invoke_subprogram prod_decode_aux_pref prod_decode_aux_IMP_Minus;;
        \<comment> \<open>fst_ret' = prod_decode_aux_m prod_decode_aux_ret;\<close>
   prod_decode_fst_ret_str ::= (A (V (prod_decode_aux_pref @ prod_decode_aux_m_str)));;
        \<comment> \<open>snd_ret' = prod_decode_aux_k prod_decode_aux_ret - prod_decode_aux_m prod_decode_aux_ret;\<close>
   prod_decode_snd_ret_str ::= ((V (prod_decode_aux_pref @ prod_decode_aux_k_str)) \<ominus> (V (prod_decode_aux_pref @ prod_decode_aux_m_str)))
  )"

definition "prod_decode_imp_to_HOL_state p s =
  \<lparr>prod_decode_m = (s (add_prefix p prod_decode_m_str)), prod_decode_fst_ret = (s (add_prefix p prod_decode_fst_ret_str)) , prod_decode_snd_ret = (s (add_prefix p prod_decode_snd_ret_str))\<rparr>"

lemma prod_decode_IMP_Minus_correct_function_1: 
  "(invoke_subprogram p prod_decode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p prod_decode_fst_ret_str) = prod_decode_fst_ret (prod_decode_imp (prod_decode_imp_to_HOL_state p s))"
  apply(simp only: prod_decode_IMP_Minus_def prod_decode_imp.simps com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  apply(erule prod_decode_aux_IMP_Minus_correct[where vars = "{p @ prod_decode_m_str}"])
   apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: prod_decode_state_upd_def Let_def prod_decode_aux_imp_to_HOL_state_def)[1]
  apply(auto simp: prod_decode_imp_to_HOL_state_def)[1]
  done

lemma prod_decode_IMP_Minus_correct_function_2: 
  "(invoke_subprogram p prod_decode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p prod_decode_snd_ret_str) = prod_decode_snd_ret (prod_decode_imp (prod_decode_imp_to_HOL_state p s))"
  apply(simp only: prod_decode_IMP_Minus_def prod_decode_imp.simps com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  apply(erule prod_decode_aux_IMP_Minus_correct[where vars = "{p @ prod_decode_m_str}"])
   apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: prod_decode_state_upd_def Let_def prod_decode_aux_imp_to_HOL_state_def)[1]
  apply(auto simp: prod_decode_imp_to_HOL_state_def)[1]
  done

lemma prod_decode_IMP_Minus_correct_time: 
  "(invoke_subprogram p prod_decode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (prod_decode_imp_time 0 (prod_decode_imp_to_HOL_state p s))"
  apply(simp only: prod_decode_IMP_Minus_def prod_decode_imp_time.simps com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  apply(erule prod_decode_aux_IMP_Minus_correct[where vars = "{p @ prod_decode_m_str}"])
   apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: prod_decode_state_upd_def Let_def prod_decode_aux_imp_to_HOL_state_def)[1]
  apply(auto simp: prod_decode_imp_to_HOL_state_def)[1]
  done

lemma prod_decode_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ p2) prod_decode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> p @ v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma prod_decode_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) prod_decode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
     \<lbrakk>t = (prod_decode_imp_time 0 (prod_decode_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) prod_decode_fst_ret_str) = prod_decode_fst_ret (prod_decode_imp (prod_decode_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) prod_decode_snd_ret_str) = prod_decode_snd_ret (prod_decode_imp (prod_decode_imp_to_HOL_state (p1 @ p2) s));      \<And>v. p1 @ v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v) \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v);
      \<And>v. p1 @ v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v) \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using prod_decode_IMP_Minus_correct_time prod_decode_IMP_Minus_correct_function_1
        prod_decode_IMP_Minus_correct_function_2
        prod_decode_IMP_Minus_correct_effects 
  by auto
*)

subsection \<open>Head and tail of lists\<close>

record hd_state = hd_xs::nat hd_ret::nat

abbreviation "hd_prefix \<equiv> ''hd.''"
abbreviation "hd_xs_str \<equiv> ''xs''"
abbreviation "hd_ret_str \<equiv> ''hd_ret''"

term prod_decode_state_p
definition "hd_state_upd s \<equiv>
      let
        prod_decode_m' = hd_xs s - 1;
        prod_decode_fst_ret' = 0;
        prod_decode_snd_ret' = 0;
        prod_decode_state = \<lparr>prod_decode_state_p = prod_decode_m',
          prod_decode_state_fst = prod_decode_fst_ret', prod_decode_state_snd = prod_decode_snd_ret'\<rparr>;
        prod_decode_ret = prod_decode_imp prod_decode_state;
        hd_ret' = prod_decode_state_fst prod_decode_ret;
        ret = \<lparr>hd_xs = hd_xs s, hd_ret = hd_ret'\<rparr>
      in
        ret
"

fun hd_imp :: "hd_state \<Rightarrow> hd_state"
  where "hd_imp s =    
    (let
       ret = (hd_state_upd s)
     in
         ret)
"

declare hd_imp.simps [simp del]

lemma hd_imp_correct:
   "hd_ret (hd_imp s) = hd_nat (hd_xs s)"
  by (subst hd_imp.simps) (auto simp: prod_decode_imp_correct hd_nat_def fst_nat_def hd_imp.simps 
      hd_state_upd_def Let_def fst_nat_fst'_nat[symmetric] split: if_splits)[1]

fun hd_imp_time:: "nat \<Rightarrow> hd_state\<Rightarrow> nat" where
  "hd_imp_time t s = 
(
      let
        prod_decode_m' = hd_xs s - 1;
        t = t + 2;
        prod_decode_fst_ret' = 0;
        t = t + 2;
        prod_decode_snd_ret' = 0;
        t = t + 2;
        prod_decode_state = \<lparr>prod_decode_state_p = prod_decode_m',
          prod_decode_state_fst = prod_decode_fst_ret', prod_decode_state_snd = prod_decode_snd_ret'\<rparr>;
        prod_decode_ret = prod_decode_imp prod_decode_state;
        t = t + prod_decode_imp_time 0 prod_decode_state;
        hd_ret' = prod_decode_state_fst prod_decode_ret;
        t = t + 2;
        ret = t
      in
        ret
      )
"

lemmas [simp del] = hd_imp_time.simps

lemma hd_imp_time_acc: "(hd_imp_time (Suc t) s) = Suc (hd_imp_time t s)"
  by (induction t s arbitrary:  rule: hd_imp_time.induct)
     (auto simp add: hd_imp_time.simps split: if_splits)

definition hd_IMP_Minus where
"hd_IMP_Minus \<equiv>
  (     \<comment> \<open>prod_decode_m' = hd_xs s - 1;\<close>
        (prod_decode_prefix @ prod_decode_p_str) ::= ((V hd_xs_str) \<ominus> (N 1));;
        \<comment> \<open>prod_decode_fst_ret' = 0;\<close>
        (prod_decode_prefix @ prod_decode_fst_str) ::= (A (N 0));;
        \<comment> \<open>prod_decode_snd_ret' = 0;\<close>
        (prod_decode_prefix @ prod_decode_snd_str) ::= (A (N 0));;
        \<comment> \<open>prod_decode_state = \<lparr>prod_decode_m = prod_decode_m', prod_decode_fst_ret = prod_decode_fst_ret', prod_decode_snd_ret = prod_decode_snd_ret'\<rparr>;\<close>
        \<comment> \<open>prod_decode_ret = prod_decode_imp prod_decode_state;\<close>
        invoke_subprogram prod_decode_prefix prod_decode_IMP_Minus;;
        \<comment> \<open>hd_ret' = prod_decode_fst_ret prod_decode_ret;\<close>
        (hd_ret_str) ::= (A (V (prod_decode_prefix @ prod_decode_fst_str)))
  )"

definition "hd_imp_to_HOL_state p s =
  \<lparr>hd_xs = (s (add_prefix p hd_xs_str)), hd_ret = (s (add_prefix p hd_ret_str))\<rparr>"

lemma hd_IMP_Minus_correct_function: 
  "(invoke_subprogram p hd_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p hd_ret_str) = hd_ret (hd_imp (hd_imp_to_HOL_state p s))"
  apply(simp only: hd_IMP_Minus_def hd_imp.simps com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  apply(erule prod_decode_IMP_Minus_correct[where vars = "{hd_xs_str}"])
   apply auto[]
  apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: hd_state_upd_def Let_def hd_imp_to_HOL_state_def)[1]
  apply(auto simp: prod_decode_imp_to_HOL_state_def )[1]
  done

lemma hd_IMP_Minus_correct_time: 
  "(invoke_subprogram p hd_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = hd_imp_time 0 (hd_imp_to_HOL_state p s)"
  apply(simp only: hd_IMP_Minus_def hd_imp_time.simps com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  apply(erule prod_decode_IMP_Minus_correct[where vars = "{hd_xs_str}"])
   apply auto[]
  apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: hd_state_upd_def Let_def hd_imp_to_HOL_state_def)[1]
  apply(auto simp: prod_decode_imp_to_HOL_state_def)[1]
  done

lemma hd_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ hd_pref) hd_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> v \<in> vars \<Longrightarrow> \<not> (prefix hd_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma hd_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) hd_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (hd_imp_time 0 (hd_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) hd_ret_str) = 
        hd_ret (hd_imp (hd_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using hd_IMP_Minus_correct_time hd_IMP_Minus_correct_function
        hd_IMP_Minus_correct_effects 
  by auto

record tl_state = tl_xs::nat tl_ret::nat

abbreviation "tl_prefix \<equiv> ''tl.''"
abbreviation "tl_xs_str \<equiv> ''xs''"
abbreviation "tl_ret_str \<equiv> ''tl_ret''"

definition "tl_state_upd s \<equiv>
      let
        prod_decode_m' = tl_xs s - 1;
        prod_decode_fst_ret' = 0;
        prod_decode_snd_ret' = 0;
        prod_decode_state = \<lparr>prod_decode_state_p = prod_decode_m', 
          prod_decode_state_fst = prod_decode_fst_ret', prod_decode_state_snd = prod_decode_snd_ret'\<rparr>;
        prod_decode_ret = prod_decode_imp prod_decode_state;
        tl_ret' = prod_decode_state_snd prod_decode_ret;
        ret = \<lparr>tl_xs = tl_xs s, tl_ret = tl_ret'\<rparr>
      in
        ret
"

fun tl_imp :: "tl_state \<Rightarrow> tl_state"
  where "tl_imp s =    
    (let
       ret = (tl_state_upd s)
     in
         ret)
"

declare tl_imp.simps [simp del]

lemma tl_imp_correct:
   "tl_ret (tl_imp s) = tl_nat (tl_xs s)"
  by (subst tl_imp.simps) (auto simp: prod_decode_imp_correct tl_nat_def snd_nat_def tl_imp.simps tl_state_upd_def Let_def split: if_splits)[1]

fun tl_imp_time:: "nat \<Rightarrow> tl_state\<Rightarrow> nat" where
  "tl_imp_time t s = 
(
      let
        prod_decode_m' = tl_xs s - 1;
        t = t + 2;
        prod_decode_fst_ret' = 0;
        t = t + 2;
        prod_decode_snd_ret' = 0;
        t = t + 2;
        prod_decode_state = \<lparr>prod_decode_state_p = prod_decode_m', 
          prod_decode_state_fst = prod_decode_fst_ret', prod_decode_state_snd = prod_decode_snd_ret'\<rparr>;
        prod_decode_ret = prod_decode_imp prod_decode_state;
        t = t + prod_decode_imp_time 0 prod_decode_state;
        tl_ret' = prod_decode_state_snd prod_decode_ret;
        t = t + 2;
        ret = t
      in
        ret
      )
"

lemmas [simp del] = tl_imp_time.simps

lemma tl_imp_time_acc: "(tl_imp_time (Suc t) s) = Suc (tl_imp_time t s)"
  by (induction t s arbitrary:  rule: tl_imp_time.induct)
     (auto simp add: tl_imp_time.simps split: if_splits)

definition tl_IMP_Minus where
"tl_IMP_Minus \<equiv>
  (     \<comment> \<open>prod_decode_m' = tl_xs s - 1;\<close>
        (prod_decode_prefix @ prod_decode_p_str) ::= ((V tl_xs_str) \<ominus> (N 1));;
        \<comment> \<open>prod_decode_snd_ret' = 0;\<close>
        (prod_decode_prefix @ prod_decode_fst_str) ::= (A (N 0));;
        \<comment> \<open>prod_decode_snd_ret' = 0;\<close>
        (prod_decode_prefix @ prod_decode_snd_str) ::= (A (N 0));;
        \<comment> \<open>prod_decode_state = \<lparr>prod_decode_m = prod_decode_m', prod_decode_snd_ret = prod_decode_snd_ret', prod_decode_snd_ret = prod_decode_snd_ret'\<rparr>;\<close>
        \<comment> \<open>prod_decode_ret = prod_decode_imp prod_decode_state;\<close>
        invoke_subprogram prod_decode_prefix prod_decode_IMP_Minus;;
        \<comment> \<open>tl_ret' = prod_decode_snd_ret prod_decode_ret;\<close>
        (tl_ret_str) ::= (A (V (prod_decode_prefix @ prod_decode_snd_str)))
  )"

definition "tl_imp_to_HOL_state p s =
  \<lparr>tl_xs = (s (add_prefix p tl_xs_str)), tl_ret = (s (add_prefix p tl_ret_str))\<rparr>"

lemma tl_IMP_Minus_correct_function: 
  "(invoke_subprogram p tl_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p tl_ret_str) = tl_ret (tl_imp (tl_imp_to_HOL_state p s))"
  apply(simp only: tl_IMP_Minus_def tl_imp.simps com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  apply(erule prod_decode_IMP_Minus_correct[where vars = "{tl_xs_str}"])
   apply auto[]
  apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: tl_state_upd_def Let_def tl_imp_to_HOL_state_def)[1]
  apply(auto simp: prod_decode_imp_to_HOL_state_def)[1]
  done

lemma tl_IMP_Minus_correct_time: 
  "(invoke_subprogram p tl_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = tl_imp_time 0 (tl_imp_to_HOL_state p s)"
  apply(simp only: tl_IMP_Minus_def tl_imp_time.simps com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  apply(erule prod_decode_IMP_Minus_correct[where vars = "{tl_xs_str}"])
   apply auto[]
  apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: tl_state_upd_def Let_def tl_imp_to_HOL_state_def)[1]
  apply(auto simp: prod_decode_imp_to_HOL_state_def)[1]
  done

lemma tl_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ tl_pref) tl_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> v \<in> vars \<Longrightarrow> \<not> (prefix tl_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma tl_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) tl_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (tl_imp_time 0 (tl_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) tl_ret_str) = 
        tl_ret (tl_imp (tl_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using tl_IMP_Minus_correct_time tl_IMP_Minus_correct_function
        tl_IMP_Minus_correct_effects 
  by auto

subsection \<open>List length\<close>

record length_state = length_xs::nat length_ret::nat

abbreviation "length_prefix \<equiv> ''length.''"
abbreviation "length_xs_str \<equiv> ''xs''"
abbreviation "length_ret_str \<equiv> ''length_ret''"

definition "length_state_upd s \<equiv>
      let
        tl_xs' = (length_xs s);
        tl_ret' = 0;
        tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
        tl_state_ret = tl_imp tl_state;
        length_xs' = tl_ret tl_state_ret;
        length_ret' = length_ret s + 1;
        ret = \<lparr>length_xs = length_xs', length_ret = length_ret'\<rparr>
      in
        ret
"

function length_imp:: "length_state \<Rightarrow> length_state" where
"length_imp s = 
  (if length_xs s \<noteq> 0 then \<comment> \<open>While xs \<noteq> 0\<close>
    (
      let
        next_iteration = length_imp (length_state_upd s)
      in
        next_iteration
    )
  else
    (
      let
        ret = s
      in
        ret
    )
  )"
  by pat_completeness auto
termination
  by  (relation "Wellfounded.measure (\<lambda>s. length_xs s)")
      (auto simp: tl_imp_correct length_state_upd_def Let_def split: if_splits)

declare length_imp.simps [simp del]

lemma length_imp_correct:
   "length_ret (length_imp s) - length_ret s = length_nat (length_xs s)"
proof (induction s rule: length_imp.induct)
  case (1 s)
  then show ?case
    apply(subst length_imp.simps)
    apply (auto simp: length_state_upd_def Let_def split: if_splits)
    by (metis Suc_diff_Suc diff_is_0_eq le_imp_less_Suc le_less length_imp.elims
              length_nat.elims length_state.select_convs(1) length_state.select_convs(2)
              neq0_conv tl_imp_correct tl_state.select_convs(1) zero_less_diff)
qed 

function length_imp_time:: "nat \<Rightarrow> length_state\<Rightarrow> nat" where
  "length_imp_time t s = 
  (if length_xs s \<noteq> 0 then \<comment> \<open>While xs \<noteq> 0\<close>
    (
      let
        t = t + 1;
        tl_xs' = (length_xs s);
        t = t+2;
        tl_ret' = 0;
        t = t+2;
        tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
        tl_state_ret = tl_imp tl_state;
        t = t + tl_imp_time 0 tl_state;
        length_xs' = tl_ret tl_state_ret;
        t = t + 2;
        length_ret' = length_ret s + 1;
        t = t + 2;
        next_iteration = length_imp_time t (length_state_upd s)
      in
        next_iteration
    )
  else
    (
      let
        t = t + 2;
        ret = t
      in
        ret
    )
  )
"
  by pat_completeness auto
termination
  by  (relation "Wellfounded.measure (\<lambda>(t,s). length_xs s)")
      (auto simp: tl_imp_correct length_state_upd_def Let_def split: if_splits)

lemmas [simp del] = length_imp_time.simps

lemma length_imp_time_acc: "(length_imp_time (Suc t) s) = Suc (length_imp_time t s)"
  apply (induction t s arbitrary:  rule: length_imp_time.induct)
  apply(subst length_imp_time.simps)
  apply(subst (2) length_imp_time.simps)
  apply (auto simp add: length_state_upd_def Let_def eval_nat_numeral split: if_splits)
  done

lemma length_imp_time_acc_2: "(length_imp_time x s) = x + (length_imp_time 0 s)"
  by (induction x arbitrary: s)
     (auto simp add: length_imp_time_acc length_state_upd_def Let_def eval_nat_numeral split: if_splits)

definition length_IMP_Minus where
"length_IMP_Minus \<equiv>
  (
  \<comment> \<open>if length_xs s \<noteq> 0 then \<comment> \<open>While xs \<noteq> 0\<close>\<close>
  WHILE length_xs_str \<noteq>0 DO (
        \<comment> \<open>tl_xs' = (length_xs s);\<close>
     (tl_prefix @ tl_xs_str) ::= (A (V length_xs_str));;
        \<comment> \<open>tl_ret' = 0;\<close>
     (tl_prefix @ tl_ret_str) ::= (A (N 0));;
        \<comment> \<open>tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;\<close>
        \<comment> \<open>tl_state_ret = tl_imp tl_state;\<close>
     invoke_subprogram tl_prefix tl_IMP_Minus;;
        \<comment> \<open>length_xs' = tl_ret tl_state_ret;\<close>
     length_xs_str ::= (A (V (tl_prefix @ tl_ret_str)));;
        \<comment> \<open>length_ret' = length_ret s + 1;\<close>
     length_ret_str ::= ((V (length_ret_str) \<oplus> N 1))
     )
  )"

definition "length_imp_to_HOL_state p s =
  \<lparr>length_xs = (s (add_prefix p length_xs_str)), length_ret = (s (add_prefix p length_ret_str))\<rparr>"

lemma length_IMP_Minus_correct_function: 
  "(invoke_subprogram p length_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p length_ret_str) = length_ret (length_imp (length_imp_to_HOL_state p s))"
  apply(induction "length_imp_to_HOL_state p s" arbitrary: s s' t rule: length_imp.induct)
  apply(subst length_imp.simps)
  apply(simp only: length_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule While_tE)
   apply(subst length_imp.simps)
   apply(auto simp: length_imp_time_acc length_imp_to_HOL_state_def)[1]
  apply(dest_com')
  apply(erule Seq_tE)+
  apply(erule tl_IMP_Minus_correct[where vars = "{length_ret_str}"])
  apply auto [1]
   apply(drule AssignD)+
   apply(elim conjE)
   apply(auto simp: length_state_upd_def length_imp_to_HOL_state_def)[1]
  apply(auto simp: tl_imp_to_HOL_state_def )[1]
  done

lemma length_IMP_Minus_correct_time: 
  "(invoke_subprogram p length_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = length_imp_time 0 (length_imp_to_HOL_state p s)"                      
  apply(induction "length_imp_to_HOL_state p s" arbitrary: s s' t rule: length_imp.induct)
  apply(subst length_imp_time.simps)
  apply(simp only: length_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps
                    atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule While_tE)
   apply(auto simp: length_imp_to_HOL_state_def)[1]
  apply(dest_com')
  apply(erule Seq_tE)+
  apply(erule tl_IMP_Minus_correct[where vars = "{length_ret_str}"])
  apply auto [1]

   apply(drule AssignD)+
  apply(elim conjE)
  apply(auto simp: length_state_upd_def length_imp_to_HOL_state_def length_imp_time_acc)[1]
  apply(subst length_imp_time_acc_2)
  apply(auto simp: tl_imp_to_HOL_state_def)[1]
  done

lemma length_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ p2) length_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma length_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) length_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
     \<lbrakk>t = (length_imp_time 0 (length_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) length_ret_str) = length_ret (length_imp (length_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v) \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using length_IMP_Minus_correct_time length_IMP_Minus_correct_function
        length_IMP_Minus_correct_effects 
  by auto

subsection \<open>List cons\<close>

record cons_state = cons_h::nat cons_t::nat cons_ret::nat

abbreviation "cons_prefix \<equiv> ''cons.''"
abbreviation "cons_h_str \<equiv> ''h''"
abbreviation "cons_t_str \<equiv> ''t''"
abbreviation "cons_ret_str \<equiv> ''cons_ret''"


definition "cons_state_upd s \<equiv>
      let
        prod_encode_a' = (cons_h s);
        prod_encode_b' = (cons_t s);
        prod_encode_ret' = 0;
        prod_encode_state = \<lparr>prod_encode_a = prod_encode_a', prod_encode_b = prod_encode_b', prod_encode_ret = prod_encode_ret'\<rparr>;
        prod_encode_state_ret = prod_encode_imp prod_encode_state;
        cons_ret' = (prod_encode_ret prod_encode_state_ret) + 1;
        ret = \<lparr>cons_h = cons_h s, cons_t = cons_t s, cons_ret = cons_ret'\<rparr>
      in
        ret
"

fun cons_imp:: "cons_state \<Rightarrow> cons_state" where
"cons_imp s = 
      (let
        ret = cons_state_upd s
      in
        ret)
"

declare cons_imp.simps [simp del]

lemma cons_imp_correct:
   "cons_ret (cons_imp s) = cons (cons_h s) (cons_t s)"
  by (auto simp: cons_imp.simps prod_encode_imp_correct cons_state_upd_def Let_def cons_def split: if_splits)

fun cons_imp_time:: "nat \<Rightarrow> cons_state\<Rightarrow> nat" where
  "cons_imp_time t s = 
    (
      let
        prod_encode_a' = (cons_h s);
        t = t + 2;
        prod_encode_b' = (cons_t s);
        t = t + 2;
        prod_encode_ret' = 0;
        t = t + 2;
        prod_encode_state = \<lparr>prod_encode_a = prod_encode_a', prod_encode_b = prod_encode_b', prod_encode_ret = prod_encode_ret'\<rparr>;
        prod_encode_state_ret = prod_encode_imp prod_encode_state;
        t = t + prod_encode_imp_time 0 prod_encode_state;
        cons_ret' = (prod_encode_ret prod_encode_state_ret) + 1;
        t = t + 2;
        ret = t
      in
        ret
    )
"

lemmas [simp del] = cons_imp_time.simps

lemma cons_imp_time_acc: "(cons_imp_time (Suc t) s) = Suc (cons_imp_time t s)"
  by (auto simp add: cons_imp_time.simps cons_state_upd_def Let_def eval_nat_numeral split: if_splits)

lemma cons_imp_time_acc_2: "(cons_imp_time x s) = x + (cons_imp_time 0 s)"
  by (induction x arbitrary: s)
     (auto simp add: cons_imp_time_acc cons_state_upd_def Let_def eval_nat_numeral split: if_splits)

definition cons_IMP_Minus where
"cons_IMP_Minus \<equiv>
  (
        \<comment> \<open>prod_encode_a' = (cons_h s);\<close>
        (prod_encode_prefix @ prod_encode_a_str) ::= (A (V cons_h_str));;
        \<comment> \<open>prod_encode_b' = (cons_t s);\<close>
        (prod_encode_prefix @ prod_encode_b_str) ::= (A (V cons_t_str));;
        \<comment> \<open>prod_encode_ret' = 0;\<close>
        (prod_encode_prefix @ prod_encode_ret_str) ::= (A (N 0));;
        \<comment> \<open>prod_encode_state = \<lparr>prod_encode_a = prod_encode_a', prod_encode_b = prod_encode_b', prod_encode_ret = prod_encode_ret'\<rparr>;\<close>
        \<comment> \<open>prod_encode_state_ret = prod_encode_imp prod_encode_state;\<close>
        invoke_subprogram prod_encode_prefix prod_encode_IMP_Minus;;
        \<comment> \<open>cons_ret' = (prod_encode_ret prod_encode_state_ret) + 1;\<close>
        (cons_ret_str) ::= (V (prod_encode_prefix @ prod_encode_ret_str) \<oplus> (N 1))
 )"

definition "cons_imp_to_HOL_state p s =
  \<lparr>cons_h = (s (add_prefix p cons_h_str)), cons_t = (s (add_prefix p cons_t_str)), cons_ret = (s (add_prefix p cons_ret_str))\<rparr>"

lemma cons_IMP_Minus_correct_function: 
  "(invoke_subprogram p cons_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p cons_ret_str) = cons_ret (cons_imp (cons_imp_to_HOL_state p s))"
  apply(subst cons_imp.simps)
  apply(simp only: cons_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  apply(erule prod_encode_IMP_Minus_correct[where vars = "{cons_ret_str}"])
   apply(drule AssignD)+
   apply(elim conjE)
   apply(auto simp: cons_state_upd_def cons_imp_to_HOL_state_def)[1]
  apply(auto simp: prod_encode_imp_to_HOL_state_def )[1]
  done

lemma cons_IMP_Minus_correct_time: 
  "(invoke_subprogram p cons_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = cons_imp_time 0 (cons_imp_to_HOL_state p s)"
  apply(subst cons_imp_time.simps)
  apply(simp only: cons_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  apply(erule prod_encode_IMP_Minus_correct[where vars = "{cons_ret_str}"])
   apply(drule AssignD)+
   apply(elim conjE)
   apply(auto simp: cons_state_upd_def cons_imp_to_HOL_state_def)[1]
  apply(auto simp: prod_encode_imp_to_HOL_state_def )[1]
  done


lemma cons_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ cons_pref) cons_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> v \<in> vars \<Longrightarrow> \<not> (set cons_pref \<subseteq> set v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma cons_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) cons_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    (\<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v));
     \<lbrakk>t = (cons_imp_time 0 (cons_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) cons_ret_str) = cons_ret (cons_imp (cons_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using cons_IMP_Minus_correct_time cons_IMP_Minus_correct_function
        cons_IMP_Minus_correct_effects 
  by auto

subsection \<open>List append\<close>

record append_state = append_acc::nat append_xs::nat

abbreviation "append_prefix \<equiv> ''append.''"
abbreviation "append_acc_str \<equiv> ''acc''"
abbreviation "append_xs_str \<equiv> ''xs''"

definition "append_state_upd s \<equiv>
      let
        hd_xs' = append_xs s;
        hd_ret' = 0;
        hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
        hd_state_ret = hd_imp (hd_state);
        cons_h' = hd_ret hd_state_ret;
        cons_t' = append_acc s;
        cons_ret' = 0;
        cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
        cons_ret_state = cons_imp cons_state;
        append_acc' = cons_ret cons_ret_state;
        tl_xs' = append_xs s;
        tl_ret' = 0;
        tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
        tl_state_ret = tl_imp tl_state;
        append_xs' = tl_ret tl_state_ret;
        ret = \<lparr>append_acc = append_acc', append_xs = append_xs'\<rparr>
      in
        ret
"

function append_imp:: "append_state \<Rightarrow> append_state" where
"append_imp s = 
  (if append_xs s \<noteq> 0 then \<comment> \<open>While xs \<noteq> 0\<close>
    (
      let
        next_iteration = append_imp (append_state_upd s)
      in
        next_iteration
    )
  else
    (
      let
        ret = s
      in
        ret
    )
  )"
  by pat_completeness auto
termination
  by  (relation "Wellfounded.measure (\<lambda>s. append_xs s)")
      (auto simp: tl_imp_correct append_state_upd_def Let_def split: if_splits)

declare append_imp.simps [simp del]

lemma append_imp_correct:
   "append_acc (append_imp s) = Primitives.append_acc (append_acc s) (append_xs s)"
proof (induction s rule: append_imp.induct)
  case (1 s)
  then show ?case
    apply(subst append_imp.simps)
    apply (auto simp: append_state_upd_def Let_def split: if_splits)
    by (metis Suc_pred' append_acc.simps(2) cons_imp_correct cons_state.select_convs(2)
              cons_state.simps(1) hd_imp_correct hd_state.simps(1) tl_imp_correct
              tl_state.select_convs(1))
qed 

function append_imp_time:: "nat \<Rightarrow> append_state\<Rightarrow> nat" where
  "append_imp_time t s = 
  (if append_xs s \<noteq> 0 then \<comment> \<open>While xs \<noteq> 0\<close>
    (
      let
        t = t + 1;
        hd_xs' = append_xs s;
        t = t + 2;
        hd_ret' = 0;
        t = t + 2;
        hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
        hd_state_ret = hd_imp (hd_state);
        t = t + hd_imp_time 0 hd_state;
        cons_h' = hd_ret hd_state_ret;
        t = t + 2;
        cons_t' = append_state.append_acc s;
        t = t + 2;
        cons_ret' = 0;
        t = t + 2;
        cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
        cons_ret_state = cons_imp cons_state;
        t = t + cons_imp_time 0 cons_state;
        append_acc' = cons_ret cons_ret_state;
        t = t + 2;
        tl_xs' = append_xs s;
        t = t + 2;
        tl_ret' = 0;
        t = t + 2;
        tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
        tl_state_ret = tl_imp tl_state;
        t = t + tl_imp_time 0 tl_state;
        append_xs' = tl_ret tl_state_ret;
        t = t + 2;
        next_iteration = append_imp_time t (append_state_upd s)
      in
        next_iteration
    )
  else
    (
      let
        t = t + 2;
        ret = t
      in
        ret
    )
  )
"
  by pat_completeness auto
termination
  by  (relation "Wellfounded.measure (\<lambda>(t,s). append_xs s)")
      (auto simp: tl_imp_correct append_state_upd_def Let_def split: if_splits)

lemmas [simp del] = append_imp_time.simps

lemma append_imp_time_acc: "(append_imp_time (Suc t) s) = Suc (append_imp_time t s)"
  apply (induction t s arbitrary:  rule: append_imp_time.induct)
  apply(subst append_imp_time.simps)
  apply(subst (2) append_imp_time.simps)
  apply (auto simp add: append_state_upd_def Let_def eval_nat_numeral split: if_splits)
  done

lemma append_imp_time_acc_2: "(append_imp_time x s) = x + (append_imp_time 0 s)"
  by (induction x arbitrary: s)
     (auto simp add: append_imp_time_acc append_state_upd_def Let_def eval_nat_numeral split: if_splits)


\<comment> \<open>The following separation is due to parsing time, whic grows exponentially in the length of IMP-
    programs.\<close>

abbreviation "append_IMP_Minus_1 \<equiv>
        \<comment> \<open>hd_xs' = append_xs s;\<close>
        ((hd_prefix @ hd_xs_str) ::= (A (V append_xs_str)));;
        \<comment> \<open>hd_ret' = 0;\<close>
        ((hd_prefix @ hd_ret_str) ::= (A (N 0)));;
        \<comment> \<open>hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;\<close>
        \<comment> \<open>hd_state_ret = hd_imp (hd_state);\<close>
        (invoke_subprogram hd_prefix hd_IMP_Minus);;
        \<comment> \<open>cons_h' = hd_ret hd_state_ret;\<close>
        ((cons_prefix @ cons_h_str) ::= (A (V (hd_prefix @ hd_ret_str))));;
        \<comment> \<open>cons_t' = append_acc s;\<close>
        ((cons_prefix @ cons_t_str) ::= (A (V append_acc_str)));;
        \<comment> \<open>cons_ret' = 0;\<close>
        ((cons_prefix @ cons_ret_str) ::= (A (N 0)));;
        \<comment> \<open>cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
        \<comment> \<open>cons_ret_state = cons_imp cons_state;\<close>
        (invoke_subprogram cons_prefix cons_IMP_Minus)
"

definition append_IMP_Minus where
"append_IMP_Minus \<equiv>
  (
  \<comment> \<open>if append_xs s \<noteq> 0 then \<comment> \<open>While xs \<noteq> 0\<close>\<close>
  WHILE append_xs_str \<noteq>0 DO (
        append_IMP_Minus_1;;
        \<comment> \<open>append_acc' = cons_ret cons_ret_state;\<close>
        ((append_acc_str) ::= (A (V (cons_prefix @ cons_ret_str))));;
        \<comment> \<open>tl_xs' = append_xs s;\<close>
        ((tl_prefix @ tl_xs_str) ::= (A (V (append_xs_str))));;
        \<comment> \<open>tl_ret' = 0;\<close>
        ((tl_prefix @ tl_ret_str) ::= (A (N 0)));;
        \<comment> \<open>tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;\<close>
        \<comment> \<open>tl_state_ret = tl_imp tl_state;\<close>
        (invoke_subprogram tl_prefix tl_IMP_Minus);;
        \<comment> \<open>append_xs' = tl_ret tl_state_ret;\<close>
        ((append_xs_str) ::= (A (V (tl_prefix @ tl_ret_str))))
      )
     
  )"

definition "append_imp_to_HOL_state p s =
  \<lparr>append_acc = (s (add_prefix p append_acc_str)), append_xs = (s (add_prefix p append_xs_str))\<rparr>"

lemma append_IMP_Minus_correct_function: 
  "(invoke_subprogram p append_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p append_acc_str) = append_state.append_acc (append_imp (append_imp_to_HOL_state p s))"
  apply(induction "append_imp_to_HOL_state p s" arbitrary: s s' t rule: append_imp.induct)
  apply(subst append_imp.simps)
  apply(simp only: append_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule While_tE)
   apply(auto simp: append_imp_time_acc append_imp_to_HOL_state_def)[1]
  apply(dest_com')
  apply(erule Seq_tE)+
  apply(erule tl_IMP_Minus_correct[where vars = "{append_xs_str, append_acc_str}"])
  apply fastforce [1]
  apply(erule hd_IMP_Minus_correct[where vars = "{append_xs_str, append_acc_str}"])
   apply fastforce [1]
  apply(erule cons_IMP_Minus_correct[where vars = "{append_xs_str, append_acc_str}"])
   apply fastforce [1]
   apply(drule AssignD)+
  apply(elim conjE)
  apply(simp add: append_state_upd_def append_imp_to_HOL_state_def append_imp_time_acc 
                        cons_imp_to_HOL_state_def hd_imp_to_HOL_state_def tl_imp_to_HOL_state_def
                        Let_def)
  apply fastforce [1]
  done

lemma append_IMP_Minus_correct_time: 
  "(invoke_subprogram p append_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = append_imp_time 0 (append_imp_to_HOL_state p s)"
  apply(induction "append_imp_to_HOL_state p s" arbitrary: s s' t rule: append_imp.induct)
  apply(subst append_imp_time.simps)
  apply(simp only: append_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule While_tE)
   apply(auto simp: append_imp_time_acc append_imp_to_HOL_state_def)[1]
  apply(dest_com')
  apply(erule Seq_tE)+
  apply(erule tl_IMP_Minus_correct[where vars = "{append_xs_str, append_acc_str}"])
  apply fastforce [1]
  apply(erule hd_IMP_Minus_correct[where vars = "{append_xs_str, append_acc_str}"])
   apply fastforce [1]
  apply(erule cons_IMP_Minus_correct[where vars = "{append_xs_str, append_acc_str}"])
   apply fastforce [1]
   apply(drule AssignD)+
  apply(elim conjE)
  apply(subst append_imp_time_acc_2)
  apply(simp add: append_state_upd_def append_imp_to_HOL_state_def append_imp_time_acc 
                        cons_imp_to_HOL_state_def hd_imp_to_HOL_state_def tl_imp_to_HOL_state_def
                        Let_def)
  apply fastforce [1]
  done

lemma append_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ append_pref) append_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>  v \<in> vars \<Longrightarrow> \<not> (set append_pref \<subseteq> set v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma append_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) append_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
     \<lbrakk>t = (append_imp_time 0 (append_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) append_acc_str) = 
        append_state.append_acc (append_imp (append_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using append_IMP_Minus_correct_time append_IMP_Minus_correct_function
        append_IMP_Minus_correct_effects 
  by auto


subsection \<open>List reverse\<close>

record reverse_nat_acc_state =
  reverse_nat_acc_acc::nat
  reverse_nat_acc_n::nat
  reverse_nat_acc_ret::nat

abbreviation "reverse_nat_acc_prefix \<equiv> ''append.''"
abbreviation "reverse_nat_acc_acc_str \<equiv> ''acc''"
abbreviation "reverse_nat_acc_n_str \<equiv> ''n''"
abbreviation "reverse_nat_acc_ret_str \<equiv> ''ret''"

definition "reverse_nat_acc_state_upd s \<equiv>
      let
        hd_xs' = reverse_nat_acc_n s;
        hd_ret' = 0;
        hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
        hd_state_ret = hd_imp (hd_state);
        cons_h' = hd_ret hd_state_ret;
        cons_t' = reverse_nat_acc_acc s;
        cons_ret' = 0;
        cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
        cons_ret_state = cons_imp cons_state;
        reverse_nat_acc_acc' = cons_ret cons_ret_state;
        tl_xs' = reverse_nat_acc_n s;
        tl_ret' = 0;
        tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
        tl_state_ret = tl_imp tl_state;
        reverse_nat_acc_n' = tl_ret tl_state_ret;
        ret = \<lparr>reverse_nat_acc_acc = reverse_nat_acc_acc',
               reverse_nat_acc_n = reverse_nat_acc_n',
               reverse_nat_acc_ret = reverse_nat_acc_ret s\<rparr>
      in
        ret
"

definition "reverse_nat_acc_imp_compute_loop_condition s \<equiv>
  (let
    condition = reverse_nat_acc_n s
   in condition
  )"

definition "reverse_nat_acc_imp_after_loop s \<equiv>
  (let
    ret = \<lparr>reverse_nat_acc_acc = reverse_nat_acc_acc s,
           reverse_nat_acc_n = reverse_nat_acc_n s,
           reverse_nat_acc_ret = reverse_nat_acc_acc s\<rparr>
   in ret
  )"

lemmas reverse_nat_acc_imp_subprogram_simps =
  reverse_nat_acc_imp_after_loop_def
  reverse_nat_acc_state_upd_def
  reverse_nat_acc_imp_compute_loop_condition_def

function reverse_nat_acc_imp:: "reverse_nat_acc_state \<Rightarrow> reverse_nat_acc_state" where
  "reverse_nat_acc_imp s =
  (if reverse_nat_acc_imp_compute_loop_condition s \<noteq> 0
   then
    (let next_iteration = reverse_nat_acc_imp (reverse_nat_acc_state_upd s)
      in next_iteration)
  else
    (let ret = reverse_nat_acc_imp_after_loop s in ret)
  )"
  by simp+
termination by (relation "measure (\<lambda>s. reverse_nat_acc_n s)")
    (simp add: tl_imp_correct reverse_nat_acc_imp_subprogram_simps)+

declare reverse_nat_acc_imp.simps [simp del]

lemma reverse_nat_acc_imp_correct:
  "reverse_nat_acc_ret (reverse_nat_acc_imp s)
    = reverse_nat_acc (reverse_nat_acc_acc s) (reverse_nat_acc_n s)"
  by(induction s rule: reverse_nat_acc_imp.induct)
    (subst reverse_nat_acc_imp.simps,
      simp add: cons_imp_correct hd_imp_correct tl_imp_correct reverse_nat_acc_imp_subprogram_simps)


subsection \<open>Logical And\<close>

record AND_neq_zero_state = AND_neq_zero_a::nat AND_neq_zero_b::nat AND_neq_zero_ret::nat

abbreviation "AND_neq_zero_prefix \<equiv> ''AND_neq_zero.''"
abbreviation "AND_neq_zero_a_str \<equiv> ''AND_a''"
abbreviation "AND_neq_zero_b_str \<equiv> ''AND_b''"
abbreviation "AND_neq_zero_ret_str \<equiv> ''AND_ret''"

definition "AND_neq_zero_state_upd s \<equiv>
      let
        AND_neq_zero_ret' = 
          (if AND_neq_zero_a s \<noteq> 0 then
            (if AND_neq_zero_b s \<noteq> 0 then
               1
             else
               0)
           else
             0);
        ret = \<lparr>AND_neq_zero_a = AND_neq_zero_a s, AND_neq_zero_b = AND_neq_zero_b s, AND_neq_zero_ret = AND_neq_zero_ret'\<rparr>
      in
        ret
"

fun AND_neq_zero_imp:: "AND_neq_zero_state \<Rightarrow> AND_neq_zero_state" where
"AND_neq_zero_imp s = 
      (let
        ret = AND_neq_zero_state_upd s
      in
        ret
      )"

declare AND_neq_zero_imp.simps [simp del]

lemma AND_neq_zero_imp_correct:
   "AND_neq_zero_ret (AND_neq_zero_imp s) = (if (AND_neq_zero_a s) \<noteq> 0 \<and> (AND_neq_zero_b s) \<noteq> 0 then 1 else 0)"
  by (subst AND_neq_zero_imp.simps) (auto simp: AND_neq_zero_state_upd_def Let_def split: if_splits)

fun AND_neq_zero_imp_time:: "nat \<Rightarrow> AND_neq_zero_state\<Rightarrow> nat" where
  "AND_neq_zero_imp_time t s = 
    (
      let
        AND_neq_zero_ret' = 
          (if AND_neq_zero_a s \<noteq> 0 then
            (if AND_neq_zero_b s \<noteq> 0 then
               (1::nat)
             else
               0)
           else
             0);
        t = t + 1 + (if AND_neq_zero_a s \<noteq> 0 then
            1 +
            (if AND_neq_zero_b s \<noteq> 0 then
               2
             else
               2)
           else
             2);
        ret = t
      in
        ret
    )
"

lemmas [simp del] = AND_neq_zero_imp_time.simps

lemma AND_neq_zero_imp_time_acc: "(AND_neq_zero_imp_time (Suc t) s) = Suc (AND_neq_zero_imp_time t s)"
  apply(subst AND_neq_zero_imp_time.simps)
  apply(subst AND_neq_zero_imp_time.simps)
  apply (auto simp add: AND_neq_zero_state_upd_def Let_def eval_nat_numeral split: if_splits)
  done

lemma AND_neq_zero_imp_time_acc_2: "(AND_neq_zero_imp_time x s) = x + (AND_neq_zero_imp_time 0 s)"
  by (induction x arbitrary: s)
     (auto simp add: AND_neq_zero_imp_time_acc AND_neq_zero_state_upd_def Let_def eval_nat_numeral split: if_splits)


\<comment> \<open>The following separation is due to parsing time, whic grows exponentially in the length of IMP-
    programs.\<close>

definition AND_neq_zero_IMP_Minus where
"AND_neq_zero_IMP_Minus \<equiv>
  (
          \<comment> \<open>(if AND_neq_zero_a s \<noteq> 0 then\<close>
          IF AND_neq_zero_a_str \<noteq>0 THEN
            \<comment> \<open>(if AND_neq_zero_b s \<noteq> 0 then\<close>
            IF AND_neq_zero_b_str \<noteq>0 THEN
               \<comment> \<open>1\<close>
               AND_neq_zero_ret_str ::= (A (N 1))
            \<comment> \<open>else\<close>
            ELSE
               \<comment> \<open>0)\<close>
               AND_neq_zero_ret_str ::= (A (N 0))
           \<comment> \<open>else\<close>
           ELSE
             \<comment> \<open>0);\<close>
             AND_neq_zero_ret_str ::= (A (N 0))
  )"

definition "AND_neq_zero_imp_to_HOL_state p s =
  \<lparr>AND_neq_zero_a = (s (add_prefix p AND_neq_zero_a_str)), AND_neq_zero_b = (s (add_prefix p AND_neq_zero_b_str)), AND_neq_zero_ret = (s (add_prefix p AND_neq_zero_ret_str))\<rparr>"

lemma AND_neq_zero_IMP_Minus_correct_function: 
  "(invoke_subprogram p AND_neq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p AND_neq_zero_ret_str) = AND_neq_zero_ret (AND_neq_zero_imp (AND_neq_zero_imp_to_HOL_state p s))"
  apply(subst AND_neq_zero_imp.simps)
  apply(simp only: AND_neq_zero_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule If_tE)
   apply(erule If_tE)
    apply(drule AssignD)+
    apply(elim conjE)
    apply(simp add: AND_neq_zero_state_upd_def AND_neq_zero_imp_to_HOL_state_def AND_neq_zero_imp_time_acc 
      cons_imp_to_HOL_state_def hd_imp_to_HOL_state_def tl_imp_to_HOL_state_def
      Let_def)[1]
   apply(drule AssignD)+
   apply(elim conjE)
   apply(simp add: AND_neq_zero_state_upd_def AND_neq_zero_imp_to_HOL_state_def AND_neq_zero_imp_time_acc 
      cons_imp_to_HOL_state_def hd_imp_to_HOL_state_def tl_imp_to_HOL_state_def
      Let_def)[1]
  apply(drule AssignD)+
  apply(elim conjE)
  apply(simp add: AND_neq_zero_state_upd_def AND_neq_zero_imp_to_HOL_state_def AND_neq_zero_imp_time_acc 
      cons_imp_to_HOL_state_def hd_imp_to_HOL_state_def tl_imp_to_HOL_state_def
      Let_def)[1]
  done

lemma AND_neq_zero_IMP_Minus_correct_time: 
  "(invoke_subprogram p AND_neq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = AND_neq_zero_imp_time 0 (AND_neq_zero_imp_to_HOL_state p s)"
  apply(subst AND_neq_zero_imp_time.simps)
  apply(simp only: AND_neq_zero_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule If_tE)
   apply(erule If_tE)
    apply(drule AssignD)+
    apply(elim conjE)
    apply(simp add: AND_neq_zero_state_upd_def AND_neq_zero_imp_to_HOL_state_def AND_neq_zero_imp_time_acc 
      cons_imp_to_HOL_state_def hd_imp_to_HOL_state_def tl_imp_to_HOL_state_def
      Let_def)[1]
   apply(drule AssignD)+
   apply(elim conjE)
   apply(simp add: AND_neq_zero_state_upd_def AND_neq_zero_imp_to_HOL_state_def AND_neq_zero_imp_time_acc 
      cons_imp_to_HOL_state_def hd_imp_to_HOL_state_def tl_imp_to_HOL_state_def
      Let_def)[1]
  apply(drule AssignD)+
  apply(elim conjE)
  apply(simp add: AND_neq_zero_state_upd_def AND_neq_zero_imp_to_HOL_state_def AND_neq_zero_imp_time_acc 
      cons_imp_to_HOL_state_def hd_imp_to_HOL_state_def tl_imp_to_HOL_state_def
      Let_def)[1]
  done

lemma AND_neq_zero_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ AND_neq_zero_pref) AND_neq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>  v \<in> vars \<Longrightarrow> \<not> (set AND_neq_zero_pref \<subseteq> set v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma AND_neq_zero_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) AND_neq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
     \<lbrakk>t = (AND_neq_zero_imp_time 0 (AND_neq_zero_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) AND_neq_zero_ret_str) = 
        AND_neq_zero_ret (AND_neq_zero_imp (AND_neq_zero_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using AND_neq_zero_IMP_Minus_correct_time AND_neq_zero_IMP_Minus_correct_function
        AND_neq_zero_IMP_Minus_correct_effects 
  by auto


subsection \<open>Logical Or\<close>

record OR_neq_zero_state = OR_neq_zero_a::nat OR_neq_zero_b::nat OR_neq_zero_ret::nat

abbreviation "OR_neq_zero_prefix \<equiv> ''OR_neq_zero.''"
abbreviation "OR_neq_zero_a_str \<equiv> ''OR_a''"
abbreviation "OR_neq_zero_b_str \<equiv> ''OR_b''"
abbreviation "OR_neq_zero_ret_str \<equiv> ''OR_ret''"

definition "OR_neq_zero_state_upd s \<equiv>
      let
        OR_neq_zero_ret' = 
          (if OR_neq_zero_a s \<noteq> 0 then
            1
           else
             (if OR_neq_zero_b s \<noteq> 0 then
               1
             else
               0));
        ret = \<lparr>OR_neq_zero_a = OR_neq_zero_a s, OR_neq_zero_b = OR_neq_zero_b s, OR_neq_zero_ret = OR_neq_zero_ret'\<rparr>
      in
        ret
"

fun OR_neq_zero_imp:: "OR_neq_zero_state \<Rightarrow> OR_neq_zero_state" where
"OR_neq_zero_imp s = 
      (let
        ret = OR_neq_zero_state_upd s
      in
        ret
      )"

declare OR_neq_zero_imp.simps [simp del]

lemma OR_neq_zero_imp_correct:
   "OR_neq_zero_ret (OR_neq_zero_imp s) = (if (OR_neq_zero_a s) \<noteq> 0 \<or> (OR_neq_zero_b s) \<noteq> 0 then 1 else 0)"
  by (subst OR_neq_zero_imp.simps) (auto simp: OR_neq_zero_state_upd_def Let_def split: if_splits)

fun OR_neq_zero_imp_time:: "nat \<Rightarrow> OR_neq_zero_state\<Rightarrow> nat" where
  "OR_neq_zero_imp_time t s = 
    (
      let
        OR_neq_zero_ret' = 
          (if OR_neq_zero_a s \<noteq> 0 then
             1::nat
           else
             (if OR_neq_zero_b s \<noteq> 0 then
               (1::nat)
             else
               0));
        t = t + 1 + (if OR_neq_zero_a s \<noteq> 0 then
            2
           else
             1 +
            (if OR_neq_zero_b s \<noteq> 0 then
               2
             else
               2));
        ret = t
      in
        ret
    )
"

lemmas [simp del] = OR_neq_zero_imp_time.simps

lemma OR_neq_zero_imp_time_acc: "(OR_neq_zero_imp_time (Suc t) s) = Suc (OR_neq_zero_imp_time t s)"
  apply(subst OR_neq_zero_imp_time.simps)
  apply(subst OR_neq_zero_imp_time.simps)
  apply (auto simp add: OR_neq_zero_state_upd_def Let_def eval_nat_numeral split: if_splits)
  done

lemma OR_neq_zero_imp_time_acc_2: "(OR_neq_zero_imp_time x s) = x + (OR_neq_zero_imp_time 0 s)"
  by (induction x arbitrary: s)
     (auto simp add: OR_neq_zero_imp_time_acc OR_neq_zero_state_upd_def Let_def eval_nat_numeral split: if_splits)


\<comment> \<open>The following separation is due to parsing time, whic grows exponentially in the length of IMP-
    programs.\<close>

definition OR_neq_zero_IMP_Minus where
"OR_neq_zero_IMP_Minus \<equiv>
  (
          \<comment> \<open>(if OR_neq_zero_a s \<noteq> 0 then\<close>
          IF OR_neq_zero_a_str \<noteq>0 THEN
             \<comment> \<open>1);\<close>
            OR_neq_zero_ret_str ::= (A (N 1))
           \<comment> \<open>else\<close>
           ELSE
            \<comment> \<open>(if OR_neq_zero_b s \<noteq> 0 then\<close>
            IF OR_neq_zero_b_str \<noteq>0 THEN
               \<comment> \<open>1\<close>
               OR_neq_zero_ret_str ::= (A (N 1))
            \<comment> \<open>else\<close>
            ELSE
               \<comment> \<open>0)\<close>
               OR_neq_zero_ret_str ::= (A (N 0))
             
  )"

definition "OR_neq_zero_imp_to_HOL_state p s =
  \<lparr>OR_neq_zero_a = (s (add_prefix p OR_neq_zero_a_str)), OR_neq_zero_b = (s (add_prefix p OR_neq_zero_b_str)), OR_neq_zero_ret = (s (add_prefix p OR_neq_zero_ret_str))\<rparr>"

lemma OR_neq_zero_IMP_Minus_correct_function: 
  "(invoke_subprogram p OR_neq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p OR_neq_zero_ret_str) = OR_neq_zero_ret (OR_neq_zero_imp (OR_neq_zero_imp_to_HOL_state p s))"
  apply(subst OR_neq_zero_imp.simps)
  apply(simp only: OR_neq_zero_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule If_tE)
    apply(drule AssignD)+
    apply(elim conjE)
    apply(simp add: OR_neq_zero_state_upd_def OR_neq_zero_imp_to_HOL_state_def OR_neq_zero_imp_time_acc 
      cons_imp_to_HOL_state_def hd_imp_to_HOL_state_def tl_imp_to_HOL_state_def
      Let_def)[1]
   apply(erule If_tE)
   apply(drule AssignD)+
   apply(elim conjE)
   apply(simp add: OR_neq_zero_state_upd_def OR_neq_zero_imp_to_HOL_state_def OR_neq_zero_imp_time_acc 
      cons_imp_to_HOL_state_def hd_imp_to_HOL_state_def tl_imp_to_HOL_state_def
      Let_def)[1]
  apply(drule AssignD)+
  apply(elim conjE)
  apply(simp add: OR_neq_zero_state_upd_def OR_neq_zero_imp_to_HOL_state_def OR_neq_zero_imp_time_acc 
      cons_imp_to_HOL_state_def hd_imp_to_HOL_state_def tl_imp_to_HOL_state_def
      Let_def)[1]
  done

lemma OR_neq_zero_IMP_Minus_correct_time: 
  "(invoke_subprogram p OR_neq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = OR_neq_zero_imp_time 0 (OR_neq_zero_imp_to_HOL_state p s)"
  apply(subst OR_neq_zero_imp_time.simps)
  apply(simp only: OR_neq_zero_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule If_tE)
    apply(drule AssignD)+
    apply(elim conjE)
    apply(simp add: OR_neq_zero_state_upd_def OR_neq_zero_imp_to_HOL_state_def OR_neq_zero_imp_time_acc 
      cons_imp_to_HOL_state_def hd_imp_to_HOL_state_def tl_imp_to_HOL_state_def
      Let_def)[1]
   apply(erule If_tE)
   apply(drule AssignD)+
   apply(elim conjE)
   apply(simp add: OR_neq_zero_state_upd_def OR_neq_zero_imp_to_HOL_state_def OR_neq_zero_imp_time_acc 
      cons_imp_to_HOL_state_def hd_imp_to_HOL_state_def tl_imp_to_HOL_state_def
      Let_def)[1]
  apply(drule AssignD)+
  apply(elim conjE)
  apply(simp add: OR_neq_zero_state_upd_def OR_neq_zero_imp_to_HOL_state_def OR_neq_zero_imp_time_acc 
      cons_imp_to_HOL_state_def hd_imp_to_HOL_state_def tl_imp_to_HOL_state_def
      Let_def)[1]
  done

lemma OR_neq_zero_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ OR_neq_zero_pref) OR_neq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>  v \<in> vars \<Longrightarrow> \<not> (set OR_neq_zero_pref \<subseteq> set v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma OR_neq_zero_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) OR_neq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
     \<lbrakk>t = (OR_neq_zero_imp_time 0 (OR_neq_zero_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) OR_neq_zero_ret_str) = 
        OR_neq_zero_ret (OR_neq_zero_imp (OR_neq_zero_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using OR_neq_zero_IMP_Minus_correct_time OR_neq_zero_IMP_Minus_correct_function
        OR_neq_zero_IMP_Minus_correct_effects 
  by auto


end