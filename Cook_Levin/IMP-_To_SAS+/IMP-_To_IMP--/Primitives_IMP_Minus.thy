\<^marker>\<open>creator Mohammad Abdulaziz, Florian Keßler\<close>

theory Primitives_IMP_Minus
  imports
    "HOL-Library.Nat_Bijection"
    Primitives IMP_Minus.Call_By_Prefixes
    "HOL-Library.Sublist"
    Utilities
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

(*definition [prefix_defs]:*) abbreviation  "mul_prefix \<equiv> ''mul.''"
(*definition [prefix_defs]:*) abbreviation   "mul_a_str \<equiv> ''a''"
(*definition [prefix_defs]:*) abbreviation   "mul_b_str \<equiv> ''b''"
(*definition [prefix_defs]:*) abbreviation   "mul_c_str \<equiv> ''c''"

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
  by simp+
termination
  by (relation "Wellfounded.measure mul_b")
    (simp add: mul_state_upd_def Let_def)+

lemmas [simp del] = mul_imp.simps

lemma mul_imp_correct[let_function_correctness]: "mul_c (mul_imp s) = mul_c s + mul_a s * mul_b s"
  apply (induction s rule: mul_imp.induct)
  apply (subst mul_imp.simps)
  apply (auto simp add: mul_state_upd_def Let_def add_mult_distrib simp del: One_nat_def)[1]
  by (metis distrib_left mod_mult_div_eq mult_2 mult_numeral_1_right numerals(1))

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
  by auto
termination
  by (relation "Wellfounded.measure (mul_b \<circ> snd)")
    (simp add: mul_state_upd_def Let_def)+

lemmas [simp del] = mul_imp_time.simps

lemma mul_imp_time_acc: "(mul_imp_time (Suc t) s) = Suc (mul_imp_time t s)"
  by (induction t s rule: mul_imp_time.induct) (simp add: mul_imp_time.simps mul_state_upd_def)

definition mul_IMP_Minus where
  "mul_IMP_Minus \<equiv>
  (\<comment> \<open>if b \<noteq> 0 then\<close>
   WHILE mul_b_str\<noteq>0 DO
        \<comment> \<open>d = b mod 2;\<close>
        (''d'' ::= ((V mul_b_str) \<doteq>1);;
        \<comment> \<open>c = (if d \<noteq> 0 then c + a else c);\<close>
        IF ''d''\<noteq>0
        THEN mul_c_str ::= ((V mul_c_str) \<oplus> (V mul_a_str))
        ELSE mul_c_str ::= A (V mul_c_str);;
        \<comment> \<open>a = a + a;\<close>
        mul_a_str ::= ((V mul_a_str) \<oplus> (V mul_a_str));;
        \<comment> \<open>b = b div 2;\<close>
        mul_b_str ::= ((V mul_b_str) \<then>))
  )"

definition "mul_imp_to_HOL_state p s =
  \<lparr>mul_a = s (add_prefix p mul_a_str),
   mul_b = (s (add_prefix p mul_b_str)),
   mul_c = (s (add_prefix p mul_c_str))\<rparr>"

lemma mul_imp_to_HOL_state_add_prefix:
  "mul_imp_to_HOL_state (add_prefix p1 p2) s = mul_imp_to_HOL_state p2 (s o (add_prefix p1))"
  by (simp add: mul_imp_to_HOL_state_def)

lemma mul_imp_to_HOL_state_add_prefix':
  "mul_imp_to_HOL_state (x # p2) s = mul_imp_to_HOL_state p2 (s o (add_prefix [x]))"
  by (simp add: mul_imp_to_HOL_state_def)

lemma mul_IMP_Minus_correct_time:
  "(invoke_subprogram p mul_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
    t = (mul_imp_time 0 (mul_imp_to_HOL_state p s))"
  apply(induction "mul_imp_to_HOL_state p s" arbitrary: s s' t rule: mul_imp.induct)
  apply(simp only: mul_IMP_Minus_def com_add_prefix.simps)

  apply(erule While_tE)
  subgoal by (subst mul_imp_time.simps, fastforce simp: mul_imp_time_acc mul_imp_to_HOL_state_def)

  apply(dest_com')
  apply(erule Seq_tE)+
  apply(erule If_tE)
  by (subst mul_imp_time.simps, fastforce simp add: mul_imp_time_acc mul_imp_to_HOL_state_def
      mul_state_upd_def prefix_defs)+

lemma mul_IMP_Minus_correct_function:
  "(invoke_subprogram p mul_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
    s' (add_prefix p mul_c_str) = mul_c (mul_imp (mul_imp_to_HOL_state p s))"
  apply(induction "mul_imp_to_HOL_state p s" arbitrary: s s' t rule: mul_imp.induct)
  apply(simp only: mul_IMP_Minus_def com_add_prefix.simps)

  apply(erule While_tE)
  subgoal by (subst mul_imp.simps, fastforce simp: mul_imp_to_HOL_state_def)

  apply(dest_com')
  apply(erule Seq_tE)+
  apply(erule If_tE)
  by (subst mul_imp.simps mul_imp_time.simps, fastforce simp add: mul_imp_to_HOL_state_def
      mul_state_upd_def prefix_defs)+

lemma mul_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ mul_pref) mul_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
  p @ v \<in> vars \<Longrightarrow> \<not> (set mul_pref \<subseteq> set v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma mul_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) mul_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (mul_imp_time 0 (mul_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) mul_c_str) = mul_c (mul_imp (mul_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using mul_IMP_Minus_correct_time mul_IMP_Minus_correct_function mul_IMP_Minus_correct_effects
  by (meson com_only_vars)


subsubsection \<open>Squaring\<close>

record square_state =
  square_x :: nat
  square_square :: nat

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

lemma square_imp_correct[let_function_correctness]: "square_square (square_imp s) = (square_x s)^2"
  by (induction s rule: square_imp.induct)
    (simp add: square_imp.simps square_state_upd_def mul_imp_correct power2_eq_square)

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
    (simp add: square_imp_time.simps)

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
   invoke_subprogram mul_prefix mul_IMP_Minus;;
  square_square_str ::= A (V (mul_prefix @ mul_c_str))
  )"

definition "square_imp_to_HOL_state p s =
  \<lparr>square_x = s (add_prefix p square_x_str),
   square_square = s (add_prefix p square_square_str)\<rparr>"

lemma square_imp_to_HOL_state_add_prefix:
  "square_imp_to_HOL_state (add_prefix p1 p2) s = square_imp_to_HOL_state p2 (s o (add_prefix p1))"
  by (simp only: square_imp_to_HOL_state_def append.assoc[symmetric] comp_def)

declare prefix_defs[simp]

lemma square_IMP_Minus_correct_function:
  "(invoke_subprogram p square_IMP_Minus, s) \<Rightarrow>\<^bsup>t \<^esup> s' \<Longrightarrow>
    s' (add_prefix p square_square_str) = square_square (square_imp (square_imp_to_HOL_state p s))"
  apply(subst square_imp.simps prefix_defs)
  apply(simp only: square_IMP_Minus_def prefix_simps)
  apply(vcg "{square_square_str}")
  by (fastforce simp add: mul_imp_to_HOL_state_def square_state_upd_def Let_def
      square_imp_to_HOL_state_def)


lemma square_IMP_Minus_correct_time:
  "(invoke_subprogram p square_IMP_Minus, s)
      \<Rightarrow>\<^bsup>t\<^esup> s'
    \<Longrightarrow> t = square_imp_time 0 (square_imp_to_HOL_state p s)"
  apply(subst square_imp_time.simps)
  apply(simp only: square_IMP_Minus_def prefix_simps)
  apply(vcg_time "{square_square_str}")
  by(fastforce simp add: mul_imp_to_HOL_state_def square_imp_to_HOL_state_def)
  
declare prefix_defs[simp del]

lemma square_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ square_pref) square_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
  v \<in> vars \<Longrightarrow> \<not> (prefix square_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
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

subsubsection \<open>dsqrt'\<close>

record dsqrt'_state =
  dsqrt'_state_y :: nat
  dsqrt'_state_L :: nat
  dsqrt'_state_R :: nat

(*definition [prefix_defs]:*) abbreviation   "dsqrt'_pref \<equiv> ''dsqrt'.''"
(*definition [prefix_defs]:*) abbreviation   "dsqrt'_y_str \<equiv> ''y''"
(*definition [prefix_defs]:*) abbreviation   "dsqrt'_L_str \<equiv> ''L''"
(*definition [prefix_defs]:*) abbreviation   "dsqrt'_R_str \<equiv> ''R''"

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
  by auto
termination (* Same termination proof as recursive version, just some additional decoration *)
  by (relation "Wellfounded.measure (\<lambda>s. dsqrt'_state_R s - dsqrt'_state_L s)")
    (auto simp add: dsqrt'_imp_state_upd_def Let_def)

declare dsqrt'_imp.simps[simp del]

lemma dsqrt'_imp_correct[let_function_correctness]:
  "dsqrt'_state_L (dsqrt'_imp s) = dsqrt' (dsqrt'_state_y s) (dsqrt'_state_L s) (dsqrt'_state_R s)"
  by (induction "(dsqrt'_state_y s)" "(dsqrt'_state_L s)" "(dsqrt'_state_R s)" arbitrary: s
      rule: dsqrt'.induct)
    (subst dsqrt'_imp.simps, fastforce simp: dsqrt'_imp_state_upd_def Let_def power2_eq_square
      square_imp_correct dsqrt'_simps)

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
  by auto
termination (* Same termination proof as recursive version, just some additional decoration *)
  by (relation "Wellfounded.measure (\<lambda>(t,s). dsqrt'_state_R s - dsqrt'_state_L s)")
    (auto simp add: dsqrt'_imp_state_upd_def Let_def)

declare dsqrt'_imp_time.simps[simp del]

lemma dsqrt'_imp_time_acc: "(dsqrt'_imp_time (Suc t) s) = Suc (dsqrt'_imp_time t s)"
  by (induction t s rule: dsqrt'_imp_time.induct) (simp add: dsqrt'_imp_time.simps)

lemma dsqrt'_imp_time_acc': "(dsqrt'_imp_time t s) = t + (dsqrt'_imp_time 0 s)"
  by (induction t) (simp add: dsqrt'_imp_time_acc)+

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
  dsqrt'_IMP_Minus_while_condition_def
  dsqrt'_IMP_Minus_loop_body_def
  dsqrt'_IMP_Minus_after_loop_def

definition "dsqrt'_imp_to_HOL_state p s =
  \<lparr>dsqrt'_state_y = s (add_prefix p dsqrt'_y_str),
   dsqrt'_state_L = s (add_prefix p dsqrt'_L_str),
   dsqrt'_state_R = s (add_prefix p dsqrt'_R_str)\<rparr>"

abbreviation "dsqrt'_IMP_vars \<equiv>
  {dsqrt'_y_str, dsqrt'_L_str, dsqrt'_R_str, ''inc'', ''diff'', ''cond'', ''M'', ''M2''}"

lemma square_imp_state_in_square_imp_to_HOL_state[simp]:
  "square_x (square_imp_to_HOL_state p S) = S (add_prefix p square_x_str)"
  by (simp add: square_imp_to_HOL_state_def)

lemma square_imp_state_out_square_imp_to_HOL_state[simp]:
  "square_square (square_imp_to_HOL_state p S) = S (add_prefix p square_square_str)"
  by (simp add: square_imp_to_HOL_state_def)

lemma cond_elim:
  "(\<And>v . v \<in> insert w W \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)) \<Longrightarrow>
  (s (add_prefix p w) = s' (add_prefix p w) \<Longrightarrow>
  (\<And>v . v \<in> W \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)) \<Longrightarrow> P)
  \<Longrightarrow> P"
  by simp

lemma dsqrt'_IMP_Minus_correct_function_1:
  "(invoke_subprogram p dsqrt'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p dsqrt'_L_str) =
       dsqrt'_state_L (dsqrt'_imp (dsqrt'_imp_to_HOL_state p s))"
  apply (induction "dsqrt'_imp_to_HOL_state p s" arbitrary: s s' t rule: dsqrt'_imp.induct)
  apply (subst dsqrt'_imp.simps)
  apply (simp only: dsqrt'_IMP_Minus_def prefix_simps)
  apply(vcg dsqrt'_IMP_vars)

  subgoal by (fastforce simp add: dsqrt'_imp_to_HOL_state_def dsqrt'_IMP_Minus_subprogram_simps)

  subgoal
    apply (simp only: dsqrt'_IMP_Minus_while_condition_def prefix_simps)
    by (auto simp add: dsqrt'_imp_to_HOL_state_def)
    

  subgoal
    apply(subst (asm) (1) dsqrt'_IMP_Minus_while_condition_def)
    apply(subst (asm) (1) dsqrt'_IMP_Minus_loop_body_def)
    apply(simp only: prefix_simps)
    apply(vcg dsqrt'_IMP_vars)

    subgoal
      apply (elim cond_elim)
      by (fastforce_sorted_premises2 simp: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def
          square_imp_correct)
    subgoal
      by (fastforce_sorted_premises2 simp: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def
          square_imp_correct)
    subgoal
      by (fastforce_sorted_premises2 simp: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def
          square_imp_correct)
    subgoal
      apply (elim cond_elim)
      by (fastforce_sorted_premises2 simp: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def
          square_imp_correct)
    done

  subgoal
    apply(subst (asm) (1) dsqrt'_IMP_Minus_while_condition_def)
    apply(subst (asm) (1) dsqrt'_IMP_Minus_loop_body_def)
    apply (simp only: prefix_simps)
    apply(vcg dsqrt'_IMP_vars)

    subgoal
      apply (elim cond_elim)
      by (fastforce_sorted_premises2 simp: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def
          square_imp_correct)
    subgoal
      by (fastforce_sorted_premises2 simp: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def
          square_imp_correct)
    subgoal
      by (fastforce_sorted_premises2 simp: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def
          square_imp_correct)
    subgoal
      apply (elim cond_elim)
      by (fastforce_sorted_premises2 simp: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def
          square_imp_correct)
    done
  done

lemma square_x[simp]: "square_x \<lparr>square_x = x, square_square = out\<rparr> = x"
  by simp

lemma square_square[simp]: "square_square  \<lparr>square_x = x, square_square = out\<rparr> = out"
  by simp

lemma square_state[simp]: "\<lparr>square_x = (square_x s), square_square = (square_square s)\<rparr> = s"
  by simp

lemma dsqrt'_IMP_Minus_correct_time:
  "(invoke_subprogram p dsqrt'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
    t = dsqrt'_imp_time 0 (dsqrt'_imp_to_HOL_state p s)"
  apply (induction "dsqrt'_imp_to_HOL_state p s" arbitrary: s s' t rule: dsqrt'_imp.induct)
  apply (subst dsqrt'_imp_time.simps)
  apply (simp only: dsqrt'_IMP_Minus_def prefix_simps)
  apply(vcg_time dsqrt'_IMP_vars)

  subgoal by (fastforce simp add: dsqrt'_imp_to_HOL_state_def dsqrt'_IMP_Minus_subprogram_simps)

  apply(simp add: add.assoc)
  apply(vcg_time dsqrt'_IMP_vars)

  subgoal
    apply (simp only: dsqrt'_IMP_Minus_while_condition_def prefix_simps)
    by (auto simp add: dsqrt'_imp_to_HOL_state_def)

  subgoal
    apply(subst (asm) (1) dsqrt'_IMP_Minus_while_condition_def)
    apply(subst (asm) (1) dsqrt'_IMP_Minus_loop_body_def)
    apply(simp only: prefix_simps)
    apply(vcg dsqrt'_IMP_vars)

    subgoal
      apply (elim cond_elim)
      by (auto_sorted_premises2 simp: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def
          square_imp_correct)

    subgoal
      by (auto_sorted_premises2 simp: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def
          square_imp_correct)
    subgoal
      by (auto_sorted_premises2 simp: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def
          square_imp_correct)

    subgoal
      apply (elim cond_elim)
      by (auto_sorted_premises2 simp: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def
          square_imp_correct)
    done

  subgoal
    apply(subst (asm) (1) dsqrt'_IMP_Minus_while_condition_def)
    apply(subst (asm) (1) dsqrt'_IMP_Minus_loop_body_def)
    apply (simp only: prefix_simps)
    apply(vcg_time dsqrt'_IMP_vars)

    subgoal
      apply (elim cond_elim)
      by (auto_sorted_premises2 simp: dsqrt'_imp_state_upd_def square_imp_to_HOL_state_def
          dsqrt'_imp_time_acc'' square_imp_correct dsqrt'_imp_to_HOL_state_def)

    subgoal
      by (auto_sorted_premises2 simp: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def
          square_imp_correct)
    subgoal
      by (auto_sorted_premises2 simp: dsqrt'_imp_state_upd_def dsqrt'_imp_to_HOL_state_def
          square_imp_correct)

    subgoal
      apply (elim cond_elim)
      by (auto_sorted_premises2 simp: dsqrt'_imp_state_upd_def square_imp_to_HOL_state_def
          dsqrt'_imp_time_acc'' square_imp_correct dsqrt'_imp_to_HOL_state_def)
    done
  done

lemma dsqrt'_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ dsqrt'_prefix) dsqrt'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
  v \<in> vars \<Longrightarrow> \<not> (prefix dsqrt'_prefix v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
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


subsubsection \<open>dsqrt\<close>

record dsqrt_state =
  dsqrt_state_y :: nat
  dsqrt_state_ret :: nat

(*definition [prefix_defs]:*) abbreviation   "dsqrt_prefix \<equiv> ''dsqrt.''"
(*definition [prefix_defs]:*) abbreviation   "dsqrt_y_str \<equiv> ''y''"
(*definition [prefix_defs]:*) abbreviation   "dsqrt_ret_str \<equiv> ''ret''"

abbreviation
  "dsqrt_IMP_vars \<equiv> {dsqrt_y_str, dsqrt_ret_str}"

definition "dsqrt_imp_state_upd s = (let
    dsqrt'_y = dsqrt_state_y s;
    dsqrt'_L = 0;
    dsqrt'_R = Suc (dsqrt_state_y s);

    dsqrt_dsqrt'_state = \<lparr>dsqrt'_state_y = dsqrt'_y,
                          dsqrt'_state_L = dsqrt'_L,
                          dsqrt'_state_R = dsqrt'_R\<rparr>;
    dsqrt'_ret = dsqrt'_imp dsqrt_dsqrt'_state;

    dsqrt_ret = dsqrt'_state_L dsqrt'_ret;
    ret = \<lparr>dsqrt_state_y = dsqrt_state_y s,
           dsqrt_state_ret = dsqrt_ret\<rparr>
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

lemma dsqrt_imp_correct[let_function_correctness]:
  "dsqrt_state_ret (dsqrt_imp s) = Discrete.sqrt (dsqrt_state_y s)"
  by (subst dsqrt_imp.simps) (simp add: dsqrt'_imp_correct dsqrt_def dsqrt_imp_state_upd_def
      dsqrt_correct[symmetric])

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

declare dsqrt_imp_time.simps[simp del]

lemma dsqrt_imp_time_acc: "(dsqrt_imp_time (Suc t) s) = Suc (dsqrt_imp_time t s)"
  by (subst dsqrt_imp_time.simps, subst dsqrt_imp_time.simps) simp

lemma dsqrt_imp_time_acc_2: "(dsqrt_imp_time x s) = x + (dsqrt_imp_time 0 s)"
  by (induction x arbitrary: s) (simp add: dsqrt_imp_time_acc)+

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
  \<lparr>dsqrt_state_y = (s (add_prefix p dsqrt_y_str)),
   dsqrt_state_ret = (s (add_prefix p dsqrt_ret_str))\<rparr>"

lemma dsqrt_IMP_Minus_correct_function:
  "(invoke_subprogram p dsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p dsqrt_ret_str) = dsqrt_state_ret (dsqrt_imp (dsqrt_imp_to_HOL_state p s))"
  apply(subst dsqrt_imp.simps)
  apply(simp only: dsqrt_IMP_Minus_def prefix_simps)
  apply(vcg dsqrt_IMP_vars)
  by (fastforce simp add: dsqrt_imp_state_upd_def dsqrt_imp_to_HOL_state_def
      dsqrt'_imp_to_HOL_state_def prefix_defs)

lemma dsqrt_IMP_Minus_correct_time:
  "(invoke_subprogram p dsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = dsqrt_imp_time 0 (dsqrt_imp_to_HOL_state p s)"
  apply(subst dsqrt_imp_time.simps)
  apply(simp only: dsqrt_IMP_Minus_def prefix_simps)
  apply(vcg_time dsqrt_IMP_vars)
  by (fastforce simp add: dsqrt_imp_state_upd_def dsqrt_imp_to_HOL_state_def
      dsqrt'_imp_to_HOL_state_def prefix_defs)

lemma dsqrt_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ dsqrt_pref) dsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
  v \<in> vars \<Longrightarrow> \<not> (prefix dsqrt_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma dsqrt_IMP_Minus_correct[let_function_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) dsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (dsqrt_imp_time 0 (dsqrt_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) dsqrt_ret_str) =
        dsqrt_state_ret (dsqrt_imp (dsqrt_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using dsqrt_IMP_Minus_correct_time dsqrt_IMP_Minus_correct_function
    dsqrt_IMP_Minus_correct_effects
  by auto


subsection \<open>Triangle\<close>

record triangle_state =
  triangle_a::nat
  triangle_triangle::nat

(*definition [prefix_defs]:*) abbreviation   "triangle_prefix \<equiv> ''triangle.''"
(*definition [prefix_defs]:*) abbreviation   "triangle_a_str \<equiv> ''a''"
(*definition [prefix_defs]:*) abbreviation   "triangle_triangle_str \<equiv> ''triangle''"

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

declare triangle_imp.simps[simp del]

lemma triangle_imp_correct[let_function_correctness]:
  "triangle_triangle (triangle_imp s) = Nat_Bijection.triangle (triangle_a s)"
  by (induction s rule: triangle_imp.induct)
    (simp add: triangle_imp.simps triangle_def triangle_state_upd_def Let_def mul_imp_correct)

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

declare triangle_imp_time.simps[simp del]

lemma triangle_imp_time_acc: "(triangle_imp_time (Suc t) s) = Suc (triangle_imp_time t s)"
  by (induction t s rule: triangle_imp_time.induct) (simp add: triangle_imp_time.simps)

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
   invoke_subprogram mul_prefix mul_IMP_Minus;;
   \<comment> \<open>triangle_triangle = mul_c mul_ret div 2;\<close>
  triangle_triangle_str ::= (V (mul_prefix @ mul_c_str) \<then>);;
  triangle_a_str ::= A (V mul_a_str)
  )"

definition "triangle_imp_to_HOL_state p s =
  \<lparr>triangle_a = s (add_prefix p triangle_a_str),
   triangle_triangle = (s (add_prefix p triangle_triangle_str))\<rparr>"

lemma triangle_IMP_Minus_correct_function:
  "(invoke_subprogram p triangle_IMP_Minus, s)
      \<Rightarrow>\<^bsup>t \<^esup> s'
    \<Longrightarrow> s' (add_prefix p triangle_triangle_str) =
          triangle_triangle (triangle_imp (triangle_imp_to_HOL_state p s))"
  by (fastforce elim: mul_IMP_Minus_correct simp: triangle_IMP_Minus_def triangle_imp.simps
      invoke_subprogram_append mul_imp_to_HOL_state_def triangle_state_upd_def
      triangle_imp_to_HOL_state_def)

lemma triangle_IMP_Minus_correct_time:
  "(invoke_subprogram p triangle_IMP_Minus, s)
      \<Rightarrow>\<^bsup>t\<^esup> s'
    \<Longrightarrow> t = triangle_imp_time 0 (triangle_imp_to_HOL_state p s)"
  by (fastforce elim: mul_IMP_Minus_correct simp: triangle_IMP_Minus_def invoke_subprogram_append
      triangle_imp_to_HOL_state_def mul_imp_to_HOL_state_def triangle_imp_time.simps)

lemma triangle_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ triangle_pref) triangle_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
  v \<in> vars \<Longrightarrow> \<not> (prefix triangle_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma triangle_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) triangle_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
    \<lbrakk>t = (triangle_imp_time 0 (triangle_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) triangle_triangle_str) =
      triangle_triangle (triangle_imp (triangle_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using triangle_IMP_Minus_correct_time triangle_IMP_Minus_correct_function
    triangle_IMP_Minus_correct_effects
  by auto


subsection \<open>Triangular root\<close>

record tsqrt_state = tsqrt_state_y :: nat tsqrt_state_ret :: nat

(*definition [prefix_defs]:*) abbreviation   "tsqrt_prefix \<equiv> ''tsqrt.''"
(*definition [prefix_defs]:*) abbreviation   "tsqrt_y_str \<equiv> ''y''"
(*definition [prefix_defs]:*) abbreviation   "tsqrt_ret_str \<equiv> ''ret''"

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

lemma tsqrt_imp_correct[let_function_correctness]:
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
  by (subst tsqrt_imp_time.simps, subst tsqrt_imp_time.simps) (simp add: Let_def)

lemma tsqrt_imp_time_acc_2: "(tsqrt_imp_time x s) = x + (tsqrt_imp_time 0 s)"
  by (induction x arbitrary: s) (simp add: tsqrt_imp_time_acc)+

definition tsqrt_IMP_Minus where
  "tsqrt_IMP_Minus \<equiv>
  (
    (mul_prefix @ mul_a_str) ::= A (V tsqrt_y_str);;
    (mul_prefix @ mul_b_str) ::= A (N 8);;
    (mul_prefix @ mul_c_str) ::= A (N 0);;
    invoke_subprogram mul_prefix mul_IMP_Minus;;

    \<comment> \<open>Could save an assignment here, combine with next one\<close>
    tsqrt_y_str ::= (V (mul_prefix @ mul_c_str) \<oplus> N 1);;

    (dsqrt_prefix @ dsqrt_y_str) ::= A (V tsqrt_y_str);;
    (dsqrt_prefix @ dsqrt_ret_str) ::= A (N 0);;
    invoke_subprogram dsqrt_prefix dsqrt_IMP_Minus;;

    tsqrt_y_str ::= (V (dsqrt_prefix @ dsqrt_ret_str) \<ominus> N 1);;
    tsqrt_ret_str ::= (V tsqrt_y_str\<then>)
  )"

definition "tsqrt_imp_to_HOL_state p s =
  \<lparr>tsqrt_state_y = (s (add_prefix p tsqrt_y_str)),
   tsqrt_state_ret = (s (add_prefix p tsqrt_ret_str))\<rparr>"

lemma tsqrt_IMP_Minus_correct_function:
  "(invoke_subprogram p tsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p tsqrt_ret_str) = tsqrt_state_ret (tsqrt_imp (tsqrt_imp_to_HOL_state p s))"
  by (fastforce elim: mul_IMP_Minus_correct dsqrt_IMP_Minus_correct simp: tsqrt_imp.simps
      tsqrt_imp_state_upd_def tsqrt_imp_to_HOL_state_def dsqrt_imp_to_HOL_state_def
      mul_imp_to_HOL_state_def Let_def tsqrt_IMP_Minus_def invoke_subprogram_append)

lemma tsqrt_IMP_Minus_correct_time:
  "(invoke_subprogram p tsqrt_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = tsqrt_imp_time 0 (tsqrt_imp_to_HOL_state p s)"
  by (fastforce elim: mul_IMP_Minus_correct dsqrt_IMP_Minus_correct simp: tsqrt_imp_time.simps
      tsqrt_imp_state_upd_def tsqrt_imp_to_HOL_state_def dsqrt_imp_to_HOL_state_def
      mul_imp_to_HOL_state_def Let_def tsqrt_IMP_Minus_def invoke_subprogram_append)

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

lemma fst'_nat_correct[let_function_correctness]: "fst'_nat (prod_encode (m,n)) = m"
  by (simp add: prod_encode_def fst'_nat_def)
    (metis add.commute add_diff_cancel_left' le_add1 less_add_Suc2 nat_add_left_cancel_less
      triangle_Suc tsqrt_unique)

(* Connect to existing \<^const>\<open>fst_nat\<close>, unify this at some point*)
lemma fst_nat_fst'_nat: "fst_nat p = fst'_nat p"
  by (metis fst'_nat_correct fst_nat_def o_def prod.collapse prod_decode_inverse)

definition "snd'_nat p \<equiv> tsqrt p - fst'_nat p"

lemma snd'_nat_correct[let_function_correctness]: "snd'_nat (prod_encode (m,n)) = n"
  by (simp add: prod_encode_def snd'_nat_def fst'_nat_correct)
    (metis add.commute add_diff_cancel_left' fst'_nat_def le_add1 less_add_Suc2
      nat_add_left_cancel_less triangle_Suc tsqrt_unique)

(* Connect to existing \<^const>\<open>snd_nat\<close>, unify this at some point*)
lemma snd_nat_snd'_nat: "snd_nat p = snd'_nat p"
  by (metis snd'_nat_correct snd_nat_def o_def prod.collapse prod_decode_inverse)


subsubsection \<open>fst'\<close>

record fst'_state = fst'_state_p :: nat

(*definition [prefix_defs]:*) abbreviation   "fst'_prefix \<equiv> ''fst'.''"
(*definition [prefix_defs]:*) abbreviation   "fst'_p_str \<equiv> ''fst'_p''"
(*definition [prefix_defs]:*) abbreviation   "fst'_internal_str \<equiv> ''internal''"

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
declare
  arg_cong[where f=fst'_state.make, state_congs]
  arg_cong[where f=fst'_state_p, state_congs]
  arg_cong[where f=fst'_imp, state_congs]
  arg_cong[where f=fst'_nat, let_lemmas]
  fst'_state.simps[state_simps]

lemma fst'_imp_correct[let_function_correctness]: "fst'_state_p (fst'_imp s) = fst'_nat (fst'_state_p s)"
  by (subst fst'_imp.simps) (simp add: fst'_imp_state_upd_def tsqrt_imp_correct fst'_nat_def
      triangle_imp_correct)

fun fst'_imp_time :: "nat \<Rightarrow> fst'_state\<Rightarrow> nat" where
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
  by (subst fst'_imp_time.simps, subst fst'_imp_time.simps) (simp add: Let_def)

lemma fst'_imp_time_acc_2: "(fst'_imp_time x s) = x + (fst'_imp_time 0 s)"
  by (induction x arbitrary: s) (simp add: fst'_imp_time_acc)+

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

lemma fst'_IMP_Minus_correct_function:
  "(invoke_subprogram p fst'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p fst'_p_str) = fst'_state_p (fst'_imp (fst'_imp_to_HOL_state p s))"
  apply(subst fst'_imp.simps)
  apply(simp only: fst'_IMP_Minus_def prefix_simps)
  apply(vcg fst'_IMP_vars)
  by (fastforce simp add: fst'_imp_state_upd_def fst'_imp_to_HOL_state_def
      tsqrt_imp_to_HOL_state_def triangle_imp_to_HOL_state_def)

lemma fst'_IMP_Minus_correct_time:
  "(invoke_subprogram p fst'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = fst'_imp_time 0 (fst'_imp_to_HOL_state p s)"
  apply(subst fst'_imp_time.simps)
  apply(simp only: fst'_IMP_Minus_def prefix_simps)
  apply(vcg_time fst'_IMP_vars)
  by (fastforce simp add: fst'_imp_state_upd_def fst'_imp_to_HOL_state_def
      tsqrt_imp_to_HOL_state_def triangle_imp_to_HOL_state_def Let_def)

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


subsubsection \<open>snd'\<close>

record snd'_state = snd'_state_p :: nat
(*definition [prefix_defs]:*) abbreviation   "snd'_prefix \<equiv> ''snd'.''"
(*definition [prefix_defs]:*) abbreviation   "snd'_p_str \<equiv> ''p''"

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
declare
  arg_cong[where f=snd'_state.make, state_congs]
  arg_cong[where f=snd'_state_p, state_congs]
  arg_cong[where f=snd'_imp, state_congs]
  arg_cong[where f=snd'_nat, let_lemmas]
  snd'_state.simps[state_simps]

lemma snd'_imp_correct[let_function_correctness]:
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
  by (subst snd'_imp_time.simps, subst snd'_imp_time.simps) simp

lemma snd'_imp_time_acc_2: "(snd'_imp_time x s) = x + (snd'_imp_time 0 s)"
  by (induction x arbitrary: s) (simp add: snd'_imp_time_acc)+

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
  apply(simp only: snd'_IMP_Minus_def prefix_simps)
  apply(vcg "insert (tsqrt_prefix @ tsqrt_ret_str) snd'_IMP_vars")
  apply(vcg snd'_IMP_vars)
  by(fastforce simp: snd'_imp_state_upd_def snd'_imp_to_HOL_state_def tsqrt_imp_to_HOL_state_def
      fst'_imp_to_HOL_state_def)

lemma snd'_IMP_Minus_correct_time:
  "(invoke_subprogram p snd'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = snd'_imp_time 0 (snd'_imp_to_HOL_state p s)"
  apply(subst snd'_imp_time.simps)
  apply(simp only: snd'_IMP_Minus_def prefix_simps)
  apply(vcg_time "insert (tsqrt_prefix @ tsqrt_ret_str) snd'_IMP_vars")
  apply(vcg_time snd'_IMP_vars)
  by (fastforce simp add: snd'_imp_state_upd_def snd'_imp_to_HOL_state_def
      tsqrt_imp_to_HOL_state_def fst'_imp_to_HOL_state_def)

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


subsubsection \<open>prod_decode\<close>

record prod_decode_state = prod_decode_state_p :: nat prod_decode_state_fst :: nat prod_decode_state_snd :: nat

(*definition [prefix_defs]:*) abbreviation   "prod_decode_prefix \<equiv> ''prod_decode.''"
(*definition [prefix_defs]:*) abbreviation   "prod_decode_p_str \<equiv> ''p''"
(*definition [prefix_defs]:*) abbreviation   "prod_decode_fst_str \<equiv> ''fst''"
(*definition [prefix_defs]:*) abbreviation   "prod_decode_snd_str \<equiv> ''snd''"

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
declare
  arg_cong3[where f=prod_decode_state.make, state_congs]
  arg_cong[where f=prod_decode_imp, state_congs]
  prod_decode_state.simps[state_simps]

lemma prod_decode_imp_correct'[let_function_correctness]:
  "prod_decode_state_fst (prod_decode_imp s) = fst'_nat (prod_decode_state_p s)"
  "prod_decode_state_snd (prod_decode_imp s) = snd'_nat (prod_decode_state_p s)"
  by (all \<open>subst prod_decode_imp.simps\<close>) (auto simp: fst'_imp_correct snd'_imp_correct
      prod_decode_imp_state_upd_def)

lemma prod_decode_imp_correct[let_function_correctness]:
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
  by (subst prod_decode_imp_time.simps, subst prod_decode_imp_time.simps) simp

lemma prod_decode_imp_time_acc_2: "(prod_decode_imp_time x s) = x + (prod_decode_imp_time 0 s)"
  by (induction x arbitrary: s) (simp add: prod_decode_imp_time_acc)+

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
     s' (add_prefix p prod_decode_fst_str)
      = prod_decode_state_fst (prod_decode_imp (prod_decode_imp_to_HOL_state p s))"
  apply(subst prod_decode_imp.simps)
  apply(simp only: prod_decode_IMP_Minus_def prefix_simps)
  apply(vcg prod_decode_IMP_vars)
  by (fastforce simp add: prod_decode_imp_state_upd_def prod_decode_imp_to_HOL_state_def
      fst'_imp_to_HOL_state_def)

lemma prod_decode_IMP_Minus_correct_function_2:
  "(invoke_subprogram p prod_decode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p prod_decode_snd_str)
      = prod_decode_state_snd (prod_decode_imp (prod_decode_imp_to_HOL_state p s))"
  apply(subst prod_decode_imp.simps)
  apply(simp only: prod_decode_IMP_Minus_def prefix_simps)
  apply(vcg_time prod_decode_IMP_vars)
  by (fastforce simp add: prod_decode_imp_state_upd_def prod_decode_imp_to_HOL_state_def
      snd'_imp_to_HOL_state_def )

lemma prod_decode_IMP_Minus_correct_time:
  "(invoke_subprogram p prod_decode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = prod_decode_imp_time 0 (prod_decode_imp_to_HOL_state p s)"
  by (fastforce
      elim: fst'_IMP_Minus_correct[where vars = "prod_decode_IMP_vars"] snd'_IMP_Minus_correct
      simp:  prod_decode_imp_to_HOL_state_def invoke_subprogram_append fst'_imp_to_HOL_state_def
      snd'_imp_to_HOL_state_def prod_decode_IMP_Minus_def prod_decode_imp_time.simps)

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


subsubsection \<open>prod_encode\<close>

record prod_encode_state = prod_encode_a::nat prod_encode_b::nat prod_encode_ret::nat

(*definition [prefix_defs]:*) abbreviation   "prod_encode_prefix \<equiv> ''prod_encode.''"
(*definition [prefix_defs]:*) abbreviation   "prod_encode_a_str \<equiv> ''a''"
(*definition [prefix_defs]:*) abbreviation   "prod_encode_b_str \<equiv> ''b''"
(*definition [prefix_defs]:*) abbreviation   "prod_encode_ret_str \<equiv> ''prod_encode_ret''"

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

declare prod_encode_imp.simps[simp del]
declare
  arg_cong3[where f=prod_encode_state.make, state_congs]
  arg_cong[where f=prod_encode_ret, state_congs]
  arg_cong[where f=prod_encode_imp, state_congs]
  prod_arg_cong2[where f=prod_encode, let_lemmas]
  prod_encode_state.simps[state_simps]

lemma prod_encode_imp_correct[let_function_correctness]: "prod_encode_ret (prod_encode_imp s) = prod_encode (prod_encode_a s, prod_encode_b s)"
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
  by (fastforce elim: triangle_IMP_Minus_correct[where vars = "{prod_encode_a_str}"]
      simp: prod_encode_state_upd_def prod_encode_imp_to_HOL_state_def triangle_imp_to_HOL_state_def
      prod_encode_IMP_Minus_def prod_encode_imp.simps invoke_subprogram_append)

lemma prod_encode_IMP_Minus_correct_time:
  "(invoke_subprogram p prod_encode_IMP_Minus, s)
      \<Rightarrow>\<^bsup>t\<^esup> s'
    \<Longrightarrow> t = prod_encode_imp_time 0 (prod_encode_imp_to_HOL_state p s)"
  by (fastforce elim: triangle_IMP_Minus_correct[where vars = "{prod_encode_a_str}"]
      simp: prod_encode_state_upd_def prod_encode_imp_to_HOL_state_def triangle_imp_to_HOL_state_def
      prod_encode_IMP_Minus_def prod_encode_imp_time.simps invoke_subprogram_append)

lemma prod_encode_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ prod_encode_pref) prod_encode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> v \<in> vars
  \<Longrightarrow> \<not> (prefix prod_encode_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma prod_encode_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) prod_encode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (prod_encode_imp_time 0 (prod_encode_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) prod_encode_ret_str) =
        prod_encode_ret (prod_encode_imp (prod_encode_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using prod_encode_IMP_Minus_correct_time prod_encode_IMP_Minus_correct_function
    prod_encode_IMP_Minus_correct_effects
  by fastforce


subsection \<open>Logic\<close>

subsubsection \<open>Logical And\<close>

record AND_neq_zero_state = AND_neq_zero_a::nat AND_neq_zero_b::nat AND_neq_zero_ret::nat

(*definition [prefix_defs]:*) abbreviation   "AND_neq_zero_prefix \<equiv> ''AND_neq_zero.''"
(*definition [prefix_defs]:*) abbreviation   "AND_neq_zero_a_str \<equiv> ''AND_a''"
(*definition [prefix_defs]:*) abbreviation   "AND_neq_zero_b_str \<equiv> ''AND_b''"
(*definition [prefix_defs]:*) abbreviation   "AND_neq_zero_ret_str \<equiv> ''AND_ret''"

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

lemma AND_neq_zero_imp_correct[let_function_correctness]:
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
      Let_def)[1]
   apply(drule AssignD)+
   apply(elim conjE)
   apply(simp add: AND_neq_zero_state_upd_def AND_neq_zero_imp_to_HOL_state_def AND_neq_zero_imp_time_acc
      Let_def)[1]
  apply(drule AssignD)+
  apply(elim conjE)
  apply(simp add: AND_neq_zero_state_upd_def AND_neq_zero_imp_to_HOL_state_def AND_neq_zero_imp_time_acc
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
      Let_def)[1]
   apply(drule AssignD)+
   apply(elim conjE)
   apply(simp add: AND_neq_zero_state_upd_def AND_neq_zero_imp_to_HOL_state_def AND_neq_zero_imp_time_acc
      Let_def)[1]
  apply(drule AssignD)+
  apply(elim conjE)
  apply(simp add: AND_neq_zero_state_upd_def AND_neq_zero_imp_to_HOL_state_def AND_neq_zero_imp_time_acc
      Let_def)[1]
  done

lemma AND_neq_zero_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ AND_neq_zero_pref) AND_neq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
  v \<in> vars \<Longrightarrow> \<not> (prefix AND_neq_zero_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma AND_neq_zero_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) AND_neq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (AND_neq_zero_imp_time 0 (AND_neq_zero_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) AND_neq_zero_ret_str) =
        AND_neq_zero_ret (AND_neq_zero_imp (AND_neq_zero_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using AND_neq_zero_IMP_Minus_correct_time AND_neq_zero_IMP_Minus_correct_function
    AND_neq_zero_IMP_Minus_correct_effects
  by auto


subsubsection \<open>Logical Or\<close>

record OR_neq_zero_state = OR_neq_zero_a::nat OR_neq_zero_b::nat OR_neq_zero_ret::nat

(*definition [prefix_defs]:*) abbreviation   "OR_neq_zero_prefix \<equiv> ''OR_neq_zero.''"
(*definition [prefix_defs]:*) abbreviation   "OR_neq_zero_a_str \<equiv> ''OR_a''"
(*definition [prefix_defs]:*) abbreviation   "OR_neq_zero_b_str \<equiv> ''OR_b''"
(*definition [prefix_defs]:*) abbreviation   "OR_neq_zero_ret_str \<equiv> ''OR_ret''"

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

lemma OR_neq_zero_imp_correct[let_function_correctness]:
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
      Let_def)[1]
  apply(erule If_tE)
   apply(drule AssignD)+
   apply(elim conjE)
   apply(simp add: OR_neq_zero_state_upd_def OR_neq_zero_imp_to_HOL_state_def OR_neq_zero_imp_time_acc
      Let_def)[1]
  apply(drule AssignD)+
  apply(elim conjE)
  apply(simp add: OR_neq_zero_state_upd_def OR_neq_zero_imp_to_HOL_state_def OR_neq_zero_imp_time_acc
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
      Let_def)[1]
  apply(erule If_tE)
   apply(drule AssignD)+
   apply(elim conjE)
   apply(simp add: OR_neq_zero_state_upd_def OR_neq_zero_imp_to_HOL_state_def OR_neq_zero_imp_time_acc
      Let_def)[1]
  apply(drule AssignD)+
  apply(elim conjE)
  apply(simp add: OR_neq_zero_state_upd_def OR_neq_zero_imp_to_HOL_state_def OR_neq_zero_imp_time_acc
      Let_def)[1]
  done

lemma OR_neq_zero_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ OR_neq_zero_pref) OR_neq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
  v \<in> vars \<Longrightarrow> \<not> (prefix OR_neq_zero_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma OR_neq_zero_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) OR_neq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (OR_neq_zero_imp_time 0 (OR_neq_zero_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) OR_neq_zero_ret_str) =
        OR_neq_zero_ret (OR_neq_zero_imp (OR_neq_zero_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using OR_neq_zero_IMP_Minus_correct_time OR_neq_zero_IMP_Minus_correct_function
    OR_neq_zero_IMP_Minus_correct_effects
  by auto


subsubsection \<open>Equality\<close>

record EQUAL_neq_zero_state =
  EQUAL_neq_zero_a::nat
  EQUAL_neq_zero_b::nat
  EQUAL_neq_zero_ret::nat

abbreviation "EQUAL_neq_zero_prefix \<equiv> ''EQUAL_neq_zero.''"
abbreviation "EQUAL_neq_zero_a_str \<equiv> ''EQUAL_a''"
abbreviation "EQUAL_neq_zero_b_str \<equiv> ''EQUAL_b''"
abbreviation "EQUAL_neq_zero_ret_str \<equiv> ''EQUAL_ret''"

definition "EQUAL_neq_zero_state_upd s \<equiv>
  let cond1 = EQUAL_neq_zero_a s - EQUAL_neq_zero_b s;
      cond2 = EQUAL_neq_zero_b s - EQUAL_neq_zero_a s;
      cond = cond1 + cond2;
      EQUAL_neq_zero_ret' = (if cond \<noteq> 0 then (0::nat) else 1);
      ret = \<lparr>EQUAL_neq_zero_a = EQUAL_neq_zero_a s,
             EQUAL_neq_zero_b = EQUAL_neq_zero_b s,
             EQUAL_neq_zero_ret = EQUAL_neq_zero_ret'\<rparr>
  in ret"

fun EQUAL_neq_zero_imp:: "EQUAL_neq_zero_state \<Rightarrow> EQUAL_neq_zero_state" where
  "EQUAL_neq_zero_imp s =
    (let ret = EQUAL_neq_zero_state_upd s
     in ret
    )"

declare EQUAL_neq_zero_imp.simps [simp del]
declare
  EQUAL_neq_zero_state.simps[state_simps]

lemma EQUAL_neq_zero_imp_correct[let_function_correctness]:
  "EQUAL_neq_zero_ret (EQUAL_neq_zero_imp s) =
    (if (EQUAL_neq_zero_a s) = (EQUAL_neq_zero_b s) then 1 else 0)"
  by (simp add: EQUAL_neq_zero_imp.simps EQUAL_neq_zero_state_upd_def)

fun EQUAL_neq_zero_imp_time:: "nat \<Rightarrow> EQUAL_neq_zero_state \<Rightarrow> nat" where
  "EQUAL_neq_zero_imp_time t s =
    (let cond1 = EQUAL_neq_zero_a s - EQUAL_neq_zero_b s;
         t = t + 2;
         cond2 = EQUAL_neq_zero_b s - EQUAL_neq_zero_a s;
         t = t + 2;
         cond = cond1 + cond2;
         t = t + 2;
         EQUAL_neq_zero_ret' = (if cond \<noteq> 0 then (0::nat) else 1);
         t = t + 1 + (if cond \<noteq> 0 then 2 else 2);
         ret = t
     in ret
    )"

lemmas [simp del] = EQUAL_neq_zero_imp_time.simps

lemma EQUAL_neq_zero_imp_time_acc:
  "(EQUAL_neq_zero_imp_time (Suc t) s) = Suc (EQUAL_neq_zero_imp_time t s)"
  by (simp add: EQUAL_neq_zero_imp_time.simps)

lemma EQUAL_neq_zero_imp_time_acc_2:
  "(EQUAL_neq_zero_imp_time x s) = x + (EQUAL_neq_zero_imp_time 0 s)"
  by (simp add: EQUAL_neq_zero_imp_time.simps)

abbreviation "EQUAL_neq_zero_cond1 \<equiv> ''cond1''"
abbreviation "EQUAL_neq_zero_cond2 \<equiv> ''cond2''"
abbreviation "EQUAL_neq_zero_cond \<equiv> ''condition''"

definition "EQUAL_neq_zero_IMP_Minus \<equiv>
  \<comment> \<open>(let cond1 = EQUAL_neq_zero_a s - EQUAL_neq_zero_b s;\<close>
  EQUAL_neq_zero_cond1 ::= (Sub (V EQUAL_neq_zero_a_str) (V EQUAL_neq_zero_b_str));;
  \<comment> \<open>(    cond2 = EQUAL_neq_zero_b s - EQUAL_neq_zero_a s;\<close>
  EQUAL_neq_zero_cond2 ::= (Sub (V EQUAL_neq_zero_b_str) (V EQUAL_neq_zero_a_str));;
  \<comment> \<open>(    cond = cond1 + cond2;\<close>
  EQUAL_neq_zero_cond ::= (Plus (V EQUAL_neq_zero_cond1) (V EQUAL_neq_zero_cond2));;
  \<comment> \<open>(    EQUAL_neq_zero_ret' = (if cond \<noteq> 0 then (0::nat) else 1);\<close>
  \<comment> \<open>(    ret = (if cond \<noteq> 0 then (0::nat) else 1);\<close>
  IF EQUAL_neq_zero_cond \<noteq>0
  THEN EQUAL_neq_zero_ret_str ::= (A (N 0))
  ELSE EQUAL_neq_zero_ret_str ::= (A (N 1))"

abbreviation
  "EQUAL_neq_zero_IMP_vars \<equiv> {EQUAL_neq_zero_a_str, EQUAL_neq_zero_b_str, EQUAL_neq_zero_ret_str}"

definition "EQUAL_neq_zero_imp_to_HOL_state p s =
  \<lparr>EQUAL_neq_zero_a = (s (add_prefix p EQUAL_neq_zero_a_str)),
   EQUAL_neq_zero_b = (s (add_prefix p EQUAL_neq_zero_b_str)),
   EQUAL_neq_zero_ret = (s (add_prefix p EQUAL_neq_zero_ret_str))\<rparr>"

lemma EQUAL_neq_zero_IMP_Minus_correct_function:
  "(invoke_subprogram p EQUAL_neq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p EQUAL_neq_zero_ret_str)
      = EQUAL_neq_zero_ret (EQUAL_neq_zero_imp (EQUAL_neq_zero_imp_to_HOL_state p s))"
  by (force simp: EQUAL_neq_zero_imp.simps EQUAL_neq_zero_IMP_Minus_def
      EQUAL_neq_zero_imp_to_HOL_state_def EQUAL_neq_zero_state_upd_def)

lemma EQUAL_neq_zero_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ EQUAL_neq_zero_pref) EQUAL_neq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix EQUAL_neq_zero_pref v)\<rbrakk>
  \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma EQUAL_neq_zero_IMP_Minus_correct_time:
  "(invoke_subprogram p EQUAL_neq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = EQUAL_neq_zero_imp_time 0 (EQUAL_neq_zero_imp_to_HOL_state p s)"
  by(force simp: EQUAL_neq_zero_imp_time.simps EQUAL_neq_zero_IMP_Minus_def
      EQUAL_neq_zero_imp_to_HOL_state_def EQUAL_neq_zero_state_upd_def)

lemma EQUAL_neq_zero_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) EQUAL_neq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (EQUAL_neq_zero_imp_time 0 (EQUAL_neq_zero_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) EQUAL_neq_zero_ret_str) =
        EQUAL_neq_zero_ret (EQUAL_neq_zero_imp (EQUAL_neq_zero_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using EQUAL_neq_zero_IMP_Minus_correct_function
  by (auto simp: EQUAL_neq_zero_IMP_Minus_correct_time)
    (meson EQUAL_neq_zero_IMP_Minus_correct_effects set_mono_prefix)


subsubsection \<open>Inequality\<close>

record NOTEQUAL_neq_zero_state =
  NOTEQUAL_neq_zero_a::nat
  NOTEQUAL_neq_zero_b::nat
  NOTEQUAL_neq_zero_ret::nat

abbreviation "NOTEQUAL_neq_zero_prefix \<equiv> ''NOTEQUAL_neq_zero.''"
abbreviation "NOTEQUAL_neq_zero_a_str \<equiv> ''NOTEQUAL_a''"
abbreviation "NOTEQUAL_neq_zero_b_str \<equiv> ''NOTEQUAL_b''"
abbreviation "NOTEQUAL_neq_zero_ret_str \<equiv> ''NOTEQUAL_ret''"

definition "NOTEQUAL_neq_zero_state_upd s \<equiv>
  let cond1 = NOTEQUAL_neq_zero_a s - NOTEQUAL_neq_zero_b s;
      cond2 = NOTEQUAL_neq_zero_b s - NOTEQUAL_neq_zero_a s;
      cond = cond1 + cond2;
      NOTEQUAL_neq_zero_ret' = (if cond \<noteq> 0 then (1::nat) else 0);
      ret = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a s,
             NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b s,
             NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>
  in ret"

fun NOTEQUAL_neq_zero_imp:: "NOTEQUAL_neq_zero_state \<Rightarrow> NOTEQUAL_neq_zero_state" where
  "NOTEQUAL_neq_zero_imp s =
    (let ret = NOTEQUAL_neq_zero_state_upd s
     in ret
    )"

declare NOTEQUAL_neq_zero_imp.simps [simp del]

lemma NOTEQUAL_neq_zero_imp_correct[let_function_correctness]:
  "NOTEQUAL_neq_zero_ret (NOTEQUAL_neq_zero_imp s) =
    (if (NOTEQUAL_neq_zero_a s) \<noteq> (NOTEQUAL_neq_zero_b s) then 1 else 0)"
  by (simp add: NOTEQUAL_neq_zero_imp.simps NOTEQUAL_neq_zero_state_upd_def)

fun NOTEQUAL_neq_zero_imp_time:: "nat \<Rightarrow> NOTEQUAL_neq_zero_state \<Rightarrow> nat" where
  "NOTEQUAL_neq_zero_imp_time t s =
    (let cond1 = NOTEQUAL_neq_zero_a s - NOTEQUAL_neq_zero_b s;
         t = t + 2;
         cond2 = NOTEQUAL_neq_zero_b s - NOTEQUAL_neq_zero_a s;
         t = t + 2;
         cond = cond1 + cond2;
         t = t + 2;
         NOTEQUAL_neq_zero_ret' = (if cond \<noteq> 0 then (0::nat) else 1);
         t = t + 1 + (if cond \<noteq> 0 then 2 else 2);
         ret = t
     in ret
    )"

lemmas [simp del] = NOTEQUAL_neq_zero_imp_time.simps

lemma NOTEQUAL_neq_zero_imp_time_acc:
  "(NOTEQUAL_neq_zero_imp_time (Suc t) s) = Suc (NOTEQUAL_neq_zero_imp_time t s)"
  by (simp add: NOTEQUAL_neq_zero_imp_time.simps)

lemma NOTEQUAL_neq_zero_imp_time_acc_2:
  "(NOTEQUAL_neq_zero_imp_time x s) = x + (NOTEQUAL_neq_zero_imp_time 0 s)"
  by (simp add: NOTEQUAL_neq_zero_imp_time.simps)

abbreviation "NOTEQUAL_neq_zero_cond1 \<equiv> ''cond1''"
abbreviation "NOTEQUAL_neq_zero_cond2 \<equiv> ''cond2''"
abbreviation "NOTEQUAL_neq_zero_cond \<equiv> ''condition''"

definition "NOTEQUAL_neq_zero_IMP_Minus \<equiv>
  \<comment> \<open>(let cond1 = NOTEQUAL_neq_zero_a s - NOTEQUAL_neq_zero_b s;\<close>
  NOTEQUAL_neq_zero_cond1 ::= (Sub (V NOTEQUAL_neq_zero_a_str) (V NOTEQUAL_neq_zero_b_str));;
  \<comment> \<open>(    cond2 = NOTEQUAL_neq_zero_b s - NOTEQUAL_neq_zero_a s;\<close>
  NOTEQUAL_neq_zero_cond2 ::= (Sub (V NOTEQUAL_neq_zero_b_str) (V NOTEQUAL_neq_zero_a_str));;
  \<comment> \<open>(    cond = cond1 + cond2;\<close>
  NOTEQUAL_neq_zero_cond ::= (Plus (V NOTEQUAL_neq_zero_cond1) (V NOTEQUAL_neq_zero_cond2));;
  \<comment> \<open>(    NOTEQUAL_neq_zero_ret' = (if cond \<noteq> 0 then (0::nat) else 1);\<close>
  \<comment> \<open>(    ret = (if cond \<noteq> 0 then (0::nat) else 1);\<close>
  IF NOTEQUAL_neq_zero_cond \<noteq>0
  THEN NOTEQUAL_neq_zero_ret_str ::= (A (N 1))
  ELSE NOTEQUAL_neq_zero_ret_str ::= (A (N 0))"

abbreviation
  "NOTEQUAL_neq_zero_IMP_vars \<equiv>
    {NOTEQUAL_neq_zero_a_str, NOTEQUAL_neq_zero_b_str, NOTEQUAL_neq_zero_ret_str}"

definition "NOTEQUAL_neq_zero_imp_to_HOL_state p s =
  \<lparr>NOTEQUAL_neq_zero_a = (s (add_prefix p NOTEQUAL_neq_zero_a_str)),
   NOTEQUAL_neq_zero_b = (s (add_prefix p NOTEQUAL_neq_zero_b_str)),
   NOTEQUAL_neq_zero_ret = (s (add_prefix p NOTEQUAL_neq_zero_ret_str))\<rparr>"

lemma NOTEQUAL_neq_zero_IMP_Minus_correct_function:
  "(invoke_subprogram p NOTEQUAL_neq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p NOTEQUAL_neq_zero_ret_str)
      = NOTEQUAL_neq_zero_ret (NOTEQUAL_neq_zero_imp (NOTEQUAL_neq_zero_imp_to_HOL_state p s))"
  by (force simp: NOTEQUAL_neq_zero_imp.simps NOTEQUAL_neq_zero_IMP_Minus_def
      NOTEQUAL_neq_zero_imp_to_HOL_state_def NOTEQUAL_neq_zero_state_upd_def)

lemma NOTEQUAL_neq_zero_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ NOTEQUAL_neq_zero_pref) NOTEQUAL_neq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix NOTEQUAL_neq_zero_pref v)\<rbrakk>
  \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma NOTEQUAL_neq_zero_IMP_Minus_correct_time:
  "(invoke_subprogram p NOTEQUAL_neq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = NOTEQUAL_neq_zero_imp_time 0 (NOTEQUAL_neq_zero_imp_to_HOL_state p s)"
  by(force simp: NOTEQUAL_neq_zero_imp_time.simps NOTEQUAL_neq_zero_IMP_Minus_def
      NOTEQUAL_neq_zero_imp_to_HOL_state_def NOTEQUAL_neq_zero_state_upd_def)

lemma NOTEQUAL_neq_zero_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) NOTEQUAL_neq_zero_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
    \<lbrakk>t = (NOTEQUAL_neq_zero_imp_time 0 (NOTEQUAL_neq_zero_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) NOTEQUAL_neq_zero_ret_str) =
        NOTEQUAL_neq_zero_ret (NOTEQUAL_neq_zero_imp
                                  (NOTEQUAL_neq_zero_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk> \<Longrightarrow> P\<rbrakk>
  \<Longrightarrow> P"
  using NOTEQUAL_neq_zero_IMP_Minus_correct_function
  by (auto simp: NOTEQUAL_neq_zero_IMP_Minus_correct_time)
    (meson NOTEQUAL_neq_zero_IMP_Minus_correct_effects set_mono_prefix)

subsection \<open>Options\<close>

subsubsection \<open>some_nat\<close>

text \<open>The function some_nat is just defined as "some_nat = Suc", however for the purpose 
of the refinement we treat it as if it were defined as "some_nat n = n + 1" (the two 
definitions are equivalent).\<close>

record some_nat_state =
  some_nat_n::nat
  some_nat_ret::nat

abbreviation "some_nat_prefix \<equiv> ''some_nat.''"
abbreviation "some_nat_n_str \<equiv> ''n''"
abbreviation "some_nat_ret_str \<equiv> ''ret''"

definition "some_nat_state_upd s \<equiv>
  (let
      some_nat_n' = some_nat_n s;
      some_nat_ret' = some_nat_n s + 1;
      ret = \<lparr>some_nat_n = some_nat_n',
             some_nat_ret = some_nat_ret'\<rparr>
  in
      ret
)"

function some_nat_imp:: "some_nat_state \<Rightarrow> some_nat_state" where
  "some_nat_imp s =
  (let
      ret = some_nat_state_upd s
    in
      ret
  )"
  by simp+
termination
  by (relation "measure (\<lambda>s. some_nat_n s)") simp

declare some_nat_imp.simps [simp del]

lemma some_nat_imp_correct[let_function_correctness]:
  "some_nat_ret (some_nat_imp s) =
    some_nat (some_nat_n s)"
  by (simp add: some_nat_imp.simps some_nat_def Let_def
      some_nat_state_upd_def)

function some_nat_imp_time :: "nat \<Rightarrow> some_nat_state \<Rightarrow> nat" where
  "some_nat_imp_time t s = 
  (let
      some_nat_n' = some_nat_n s;
      t = t + 2;
      some_nat_ret' = some_nat_n s + 1;
      t = t + 2;
      ret = \<lparr>some_nat_n = some_nat_n',
             some_nat_ret = some_nat_ret'\<rparr>
  in
      t
  )"
  by auto
termination
  by (relation "measure (\<lambda>(t, s). some_nat_n s)") simp

declare some_nat_imp_time.simps [simp del]

lemma some_nat_imp_time_acc:
  "(some_nat_imp_time (Suc t) s) = Suc (some_nat_imp_time t s)"
  by (induction t s rule: some_nat_imp_time.induct)
    ((subst (1 2) some_nat_imp_time.simps);
      (simp add: some_nat_state_upd_def))            

lemma some_nat_imp_time_acc_2_aux:
  "(some_nat_imp_time t s) = t + (some_nat_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: some_nat_imp_time_acc)+            

lemma some_nat_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (some_nat_imp_time t s) = t + (some_nat_imp_time 0 s)"
  by (rule some_nat_imp_time_acc_2_aux)            

lemma some_nat_imp_time_acc_3:
  "(some_nat_imp_time (a + b) s) = a + (some_nat_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: some_nat_imp_time_acc)+      

definition some_nat_IMP_Minus where
  "some_nat_IMP_Minus \<equiv>
  \<comment> \<open>  some_nat_n' = some_nat_n s;\<close>
  (some_nat_n_str) ::= (A (V some_nat_n_str));;
  \<comment> \<open>  some_nat_ret' = some_nat_n s + 1;\<close>
  (some_nat_ret_str) ::= (Plus (V some_nat_n_str) (N 1))
  \<comment> \<open>  ret = \<lparr>some_nat_n = some_nat_n',\<close>
  \<comment> \<open>         some_nat_ret = some_nat_ret'\<rparr>\<close>
"

abbreviation "some_nat_IMP_vars \<equiv>
  {some_nat_n_str, some_nat_ret_str}"

definition "some_nat_imp_to_HOL_state p s =
  \<lparr>some_nat_n = (s (add_prefix p some_nat_n_str)),
   some_nat_ret = (s (add_prefix p some_nat_ret_str))\<rparr>"

lemmas some_nat_state_translators =
  some_nat_imp_to_HOL_state_def

lemma some_nat_IMP_Minus_correct_function:
  "(invoke_subprogram p some_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p some_nat_ret_str)
      = some_nat_ret
          (some_nat_imp (some_nat_imp_to_HOL_state p s))"
  apply(simp only: some_nat_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  by (fastforce simp: some_nat_state_translators some_nat_imp.simps
      some_nat_state_upd_def)

lemma some_nat_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ some_nat_pref) some_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix some_nat_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast 

lemma some_nat_IMP_Minus_correct_time:
  "(invoke_subprogram p some_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = some_nat_imp_time 0 (some_nat_imp_to_HOL_state p s)"
  apply(simp only: some_nat_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  by (fastforce simp: some_nat_state_translators Let_def 
      some_nat_imp_time.simps some_nat_state_upd_def)

lemma some_nat_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) some_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (some_nat_imp_time 0 (some_nat_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) some_nat_ret_str) =
          some_nat_ret (some_nat_imp
                                        (some_nat_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using some_nat_IMP_Minus_correct_function some_nat_IMP_Minus_correct_time
  by (meson some_nat_IMP_Minus_correct_effects set_mono_prefix)

subsection \<open>Lists\<close>

subsubsection \<open>hd\<close>

record hd_state = hd_xs::nat hd_ret::nat

(*definition [prefix_defs]:*) abbreviation   "hd_prefix \<equiv> ''hd.''"
(*definition [prefix_defs]:*) abbreviation   "hd_xs_str \<equiv> ''hd_xs''"
(*definition [prefix_defs]:*) abbreviation   "hd_ret_str \<equiv> ''hd_ret''"

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
declare
  arg_cong2[where f=hd_state.make, state_congs]
  arg_cong[where f=hd_ret, state_congs]
  arg_cong[where f=hd_imp, state_congs]
  arg_cong[where f=hd_nat, let_lemmas]
  hd_state.simps[state_simps]

lemma hd_imp_correct[let_function_correctness]:
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

abbreviation "hd_IMP_vars \<equiv> {hd_xs_str, hd_ret_str}"

definition "hd_imp_to_HOL_state p s =
  \<lparr>hd_xs = (s (add_prefix p hd_xs_str)), hd_ret = (s (add_prefix p hd_ret_str))\<rparr>"

lemma hd_IMP_Minus_correct_function:
  "(invoke_subprogram p hd_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p hd_ret_str) = hd_ret (hd_imp (hd_imp_to_HOL_state p s))"
  apply(subst hd_imp.simps)
  apply(simp only: hd_IMP_Minus_def prefix_simps)
  apply(vcg hd_IMP_vars)
  by (fastforce simp: prod_decode_imp_to_HOL_state_def hd_state_upd_def hd_imp_to_HOL_state_def)

lemma hd_IMP_Minus_correct_time:
  "(invoke_subprogram p hd_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = hd_imp_time 0 (hd_imp_to_HOL_state p s)"
  apply(subst hd_imp_time.simps)
  apply(simp only: hd_IMP_Minus_def prefix_simps)
  apply(vcg_time hd_IMP_vars)
  by (fastforce simp: prod_decode_imp_to_HOL_state_def hd_state_upd_def hd_imp_to_HOL_state_def)

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


subsubsection \<open>tl\<close>

record tl_state = tl_xs::nat tl_ret::nat

(*definition [prefix_defs]:*) abbreviation   "tl_prefix \<equiv> ''tl.''"
(*definition [prefix_defs]:*) abbreviation   "tl_xs_str \<equiv> ''tl_xs''"
(*definition [prefix_defs]:*) abbreviation   "tl_ret_str \<equiv> ''tl_ret''"

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
declare
  arg_cong2[where f=tl_state.make, state_congs]
  arg_cong[where f=tl_ret, state_congs]
  arg_cong[where f=tl_imp, state_congs]
  arg_cong[where f=tl_nat, let_lemmas]
  tl_state.simps[state_simps]

lemma tl_imp_correct[let_function_correctness]:
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

abbreviation "tl_IMP_vars \<equiv> {tl_xs_str, tl_ret_str}"

definition "tl_imp_to_HOL_state p s =
  \<lparr>tl_xs = (s (add_prefix p tl_xs_str)), tl_ret = (s (add_prefix p tl_ret_str))\<rparr>"

lemma tl_IMP_Minus_correct_function:
  "(invoke_subprogram p tl_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p tl_ret_str) = tl_ret (tl_imp (tl_imp_to_HOL_state p s))"
  apply(subst tl_imp.simps)
  apply(simp only: tl_IMP_Minus_def prefix_simps)
  apply(vcg tl_IMP_vars)
  by (fastforce simp: tl_state_upd_def tl_imp_to_HOL_state_def prod_decode_imp_to_HOL_state_def)

lemma tl_IMP_Minus_correct_time:
  "(invoke_subprogram p tl_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = tl_imp_time 0 (tl_imp_to_HOL_state p s)"
  apply(subst tl_imp_time.simps)
  apply(simp only: tl_IMP_Minus_def prefix_simps)
  apply(vcg_time tl_IMP_vars)
  by (fastforce simp: tl_state_upd_def tl_imp_to_HOL_state_def prod_decode_imp_to_HOL_state_def)

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

subsubsection \<open>map_list_find\<close>
paragraph map_list_find_aux 

fun map_list_find_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"map_list_find_aux xs a = (
  if xs \<noteq> 0 \<and> fst_nat (hd_nat xs) \<noteq> a 
  then map_list_find_nat (tl_nat xs) a 
  else (
    if xs \<noteq> 0 then some_nat (snd_nat (hd_nat xs))
    else 0
  )
)"

lemma map_list_find_aux_eq_map_list_find_nat:
 "map_list_find_aux xs a = map_list_find_nat xs a"
 by (induction xs) auto

record map_list_find_aux_state = 
  map_list_find_aux_xs::nat
  map_list_find_aux_a::nat
  map_list_find_aux_ret::nat


abbreviation "map_list_find_aux_prefix \<equiv> ''map_list_find_aux.''"
abbreviation "map_list_find_aux_xs_str \<equiv> ''map_list_find_aux_xs''"
abbreviation "map_list_find_aux_a_str \<equiv> ''map_list_find_aux_a''"
abbreviation "map_list_find_aux_ret_str \<equiv> ''map_list_find_aux_ret''"

definition "map_list_find_aux_state_upd s \<equiv>
  (let
     tl_xs' = map_list_find_aux_xs s;
     tl_ret' = 0;
     tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
     tl_ret_state = tl_imp tl_state;
     map_list_find_aux_xs' = tl_ret tl_ret_state;
     ret = \<lparr>map_list_find_aux_xs = map_list_find_aux_xs',
            map_list_find_aux_a = map_list_find_aux_a s,
            map_list_find_aux_ret = map_list_find_aux_ret s\<rparr>
   in
     ret)"

definition "map_list_find_aux_imp_compute_loop_condition s \<equiv>
  (let
    hd_xs' = map_list_find_aux_xs s;
    hd_ret' = 0;
    hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
    hd_ret_state = hd_imp hd_state;

    fst'_state_p' = hd_ret hd_ret_state;
    fst'_state = \<lparr>fst'_state_p = fst'_state_p'\<rparr>;
    fst'_ret_state = fst'_imp fst'_state;

    NOTEQUAL_neq_zero_a' = fst'_state_p fst'_ret_state;
    NOTEQUAL_neq_zero_b' = map_list_find_aux_a s;
    NOTEQUAL_neq_zero_ret' = 0;
    NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                               NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                               NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
    NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;

    AND_neq_zero_a' =  map_list_find_aux_xs s;
    AND_neq_zero_b' = NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state;
    AND_neq_zero_ret' = 0;
    AND_neq_zero_state = \<lparr>AND_neq_zero_a = AND_neq_zero_a',
                         AND_neq_zero_b = AND_neq_zero_b',
                         AND_neq_zero_ret = AND_neq_zero_ret'\<rparr>;
    AND_neq_zero_ret_state = AND_neq_zero_imp AND_neq_zero_state;
    condition = AND_neq_zero_ret AND_neq_zero_ret_state
  in
    condition
  )"

definition "map_list_find_aux_imp_after_loop s \<equiv>
  (
    let 
      map_list_find_aux_xs' = map_list_find_aux_xs s
    in
    (if map_list_find_aux_xs' \<noteq> 0 then  
      let 
       hd_xs' = map_list_find_aux_xs s;
       hd_ret' = 0;
       hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
       hd_ret_state = hd_imp hd_state;

       snd'_state_p' = hd_ret hd_ret_state;
       snd'_state = \<lparr>snd'_state_p = snd'_state_p'\<rparr>;
       snd'_ret_state = snd'_imp snd'_state;

       some_nat_n' = snd'_state_p snd'_ret_state;
       some_nat_ret' = 0;
       some_nat_state = \<lparr>some_nat_n = some_nat_n', some_nat_ret = some_nat_ret'\<rparr>;
       some_nat_ret_state = some_nat_imp some_nat_state;
       map_list_find_aux_ret' = some_nat_ret some_nat_ret_state;
       
       ret = \<lparr>map_list_find_aux_xs = map_list_find_aux_xs s,
             map_list_find_aux_a = map_list_find_aux_a s,
             map_list_find_aux_ret = map_list_find_aux_ret'\<rparr>
      in 
        ret
    else (
      let 
        map_list_find_aux_ret' = 0;
        ret = \<lparr>map_list_find_aux_xs = map_list_find_aux_xs s,
               map_list_find_aux_a = map_list_find_aux_a s,
               map_list_find_aux_ret = map_list_find_aux_ret'\<rparr>
      in 
        ret
    )))"

lemmas map_list_find_aux_imp_subprogram_simps = 
  map_list_find_aux_state_upd_def
  map_list_find_aux_imp_compute_loop_condition_def
  map_list_find_aux_imp_after_loop_def

function map_list_find_aux_imp::
  "map_list_find_aux_state \<Rightarrow> map_list_find_aux_state" where
  "map_list_find_aux_imp s =
  (if map_list_find_aux_imp_compute_loop_condition s \<noteq> 0
   then
    let next_iteration = map_list_find_aux_imp (map_list_find_aux_state_upd s)
    in next_iteration
   else
    let ret = map_list_find_aux_imp_after_loop s
    in ret
  )"
  by simp+
termination
  apply (relation "measure map_list_find_aux_xs")
  apply (simp add: map_list_find_aux_imp_subprogram_simps 
     AND_neq_zero_imp_correct NOTEQUAL_neq_zero_imp_correct
    hd_imp_correct tl_imp_correct fst'_imp_correct snd'_imp_correct split: if_splits)+
  done

declare map_list_find_aux_imp.simps [simp del]

lemma map_list_find_aux_imp_correct[let_function_correctness]:
  "map_list_find_aux_ret (map_list_find_aux_imp s) =
    map_list_find_nat (map_list_find_aux_xs s) (map_list_find_aux_a s)"
  apply (subst map_list_find_aux_eq_map_list_find_nat[symmetric])
  apply (induction s rule: map_list_find_aux_imp.induct)
  apply (subst map_list_find_aux_imp.simps)
  apply (subst map_list_find_aux.simps)
  apply (simp del: map_list_find_aux.simps only: map_list_find_aux_imp_subprogram_simps Let_def
  AND_neq_zero_imp_correct NOTEQUAL_neq_zero_imp_correct
    hd_imp_correct tl_imp_correct fst'_imp_correct snd'_imp_correct some_nat_imp_correct
    fst_nat_fst'_nat snd_nat_snd'_nat)
  apply simp
  done          

definition "map_list_find_aux_state_upd_time t s \<equiv>
  (let
     tl_xs' = map_list_find_aux_xs s;
     t = t + 2;
     tl_ret' = 0;
     t = t + 2;
     tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
     tl_ret_state = tl_imp tl_state;
     t = t + tl_imp_time 0 tl_state;
     map_list_find_aux_xs' = tl_ret tl_ret_state;
     t = t + 2;
     ret = \<lparr>map_list_find_aux_xs = map_list_find_aux_xs',
            map_list_find_aux_a = map_list_find_aux_a s,
            map_list_find_aux_ret = map_list_find_aux_ret s\<rparr>
   in
     t)"

definition "map_list_find_aux_imp_compute_loop_condition_time t s \<equiv>
  (let
    hd_xs' = map_list_find_aux_xs s;
    t = t + 2;
    hd_ret' = 0;
    t = t + 2;
    hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
    hd_ret_state = hd_imp hd_state;

    t = t + hd_imp_time 0 hd_state;
    fst'_state_p' = hd_ret hd_ret_state;
    t = t + 2;
    fst'_state = \<lparr>fst'_state_p = fst'_state_p'\<rparr>;
    fst'_ret_state = fst'_imp fst'_state;
    t = t + fst'_imp_time 0 fst'_state;

    NOTEQUAL_neq_zero_a' = fst'_state_p fst'_ret_state;
    t = t + 2;
    NOTEQUAL_neq_zero_b' = map_list_find_aux_a s;
    t = t + 2;
    NOTEQUAL_neq_zero_ret' = 0;
    t = t + 2;
    NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                               NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                               NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
    NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
    t = t + NOTEQUAL_neq_zero_imp_time 0 NOTEQUAL_neq_zero_state;

    AND_neq_zero_a' =  map_list_find_aux_xs s;
    t = t + 2;
    AND_neq_zero_b' = NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state;
    t = t + 2;
    AND_neq_zero_ret' = 0;
    t = t + 2;
    AND_neq_zero_state = \<lparr>AND_neq_zero_a = AND_neq_zero_a',
                         AND_neq_zero_b = AND_neq_zero_b',
                         AND_neq_zero_ret = AND_neq_zero_ret'\<rparr>;
    AND_neq_zero_ret_state = AND_neq_zero_imp AND_neq_zero_state;
    t = t + AND_neq_zero_imp_time 0 AND_neq_zero_state;
    condition = AND_neq_zero_ret AND_neq_zero_ret_state;
    t = t + 2
  in
    t
  )"

definition "map_list_find_aux_imp_after_loop_time t s \<equiv>
  (
    let 
      map_list_find_aux_xs' = map_list_find_aux_xs s;
      t = t + 2
    in
    (if map_list_find_aux_xs' \<noteq> 0 then  
      let 
       t = t + 1;
       hd_xs' = map_list_find_aux_xs s;
       t = t + 2;
       hd_ret' = 0;
       t = t + 2;
       hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
       hd_ret_state = hd_imp hd_state;
       t = t + hd_imp_time 0 hd_state;

       snd'_state_p' = hd_ret hd_ret_state;
       t = t + 2;
       snd'_state = \<lparr>snd'_state_p = snd'_state_p'\<rparr>;
       snd'_ret_state = snd'_imp snd'_state;
       t = t + snd'_imp_time 0 snd'_state;

       some_nat_n' = snd'_state_p snd'_ret_state;
       t = t + 2;
       some_nat_ret' = 0;
       t = t + 2;
       some_nat_state = \<lparr>some_nat_n = some_nat_n', some_nat_ret = some_nat_ret'\<rparr>;
       some_nat_ret_state = some_nat_imp some_nat_state;
       t = t + some_nat_imp_time 0 some_nat_state;
       map_list_find_aux_ret' = some_nat_ret some_nat_ret_state;
       t = t + 2;
       
       ret = \<lparr>map_list_find_aux_xs = map_list_find_aux_xs s,
             map_list_find_aux_a = map_list_find_aux_a s,
             map_list_find_aux_ret = map_list_find_aux_ret'\<rparr>
      in
        t
     else (
      let 
        t = t + 1;
        map_list_find_aux_ret' = 0;
        t = t + 2;
        ret = \<lparr>map_list_find_aux_xs = map_list_find_aux_xs s,
               map_list_find_aux_a = map_list_find_aux_a s,
               map_list_find_aux_ret = map_list_find_aux_ret'\<rparr>
      in 
        t
     )))
"

lemmas map_list_find_aux_imp_subprogram_time_simps = 
  map_list_find_aux_state_upd_time_def
  map_list_find_aux_imp_compute_loop_condition_time_def
  map_list_find_aux_imp_after_loop_time_def
  map_list_find_aux_imp_subprogram_simps

function map_list_find_aux_imp_time::
  "nat \<Rightarrow> map_list_find_aux_state \<Rightarrow> nat" where
  "map_list_find_aux_imp_time t s =
  map_list_find_aux_imp_compute_loop_condition_time 0 s +
  (if map_list_find_aux_imp_compute_loop_condition s \<noteq> 0
    then
      (let
        t = t + 1;
        next_iteration =
          map_list_find_aux_imp_time (t + map_list_find_aux_state_upd_time 0 s)
                         (map_list_find_aux_state_upd s)
       in next_iteration)
    else
      (let
        t = t + 2;
        ret = t + map_list_find_aux_imp_after_loop_time 0 s
       in ret)
  )"
  by auto
termination
  apply (relation "measure (map_list_find_aux_xs \<circ> snd)")
  apply (simp add: map_list_find_aux_imp_subprogram_time_simps AND_neq_zero_imp_correct NOTEQUAL_neq_zero_imp_correct
    hd_imp_correct tl_imp_correct fst'_imp_correct snd'_imp_correct some_nat_imp_correct
    fst_nat_fst'_nat snd_nat_snd'_nat split: if_splits)+
  done

declare map_list_find_aux_imp_time.simps [simp del]            

lemma map_list_find_aux_imp_time_acc:
  "(map_list_find_aux_imp_time (Suc t) s) = Suc (map_list_find_aux_imp_time t s)"
  by (induction t s rule: map_list_find_aux_imp_time.induct)
    ((subst (1 2) map_list_find_aux_imp_time.simps);
      (simp add: map_list_find_aux_state_upd_def))            

lemma map_list_find_aux_imp_time_acc_2_aux:
  "(map_list_find_aux_imp_time t s) = t + (map_list_find_aux_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: map_list_find_aux_imp_time_acc)+            

lemma map_list_find_aux_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (map_list_find_aux_imp_time t s) = t + (map_list_find_aux_imp_time 0 s)"
  by (rule map_list_find_aux_imp_time_acc_2_aux)            

lemma map_list_find_aux_imp_time_acc_3:
  "(map_list_find_aux_imp_time (a + b) s) = a + (map_list_find_aux_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: map_list_find_aux_imp_time_acc)+            

abbreviation "map_list_find_aux_while_cond \<equiv> ''condition''"

definition "map_list_find_aux_IMP_init_while_cond \<equiv>
  \<comment> \<open>hd_xs' = map_list_find_aux_xs s;\<close>
  (hd_prefix @ hd_xs_str) ::= A (V map_list_find_aux_xs_str);;
  \<comment> \<open>hd_ret' = 0;\<close>
  (hd_prefix @ hd_ret_str) ::= A (N 0);;
  \<comment> \<open>hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;\<close>
  \<comment> \<open>hd_ret_state = hd_imp hd_state;\<close>
  invoke_subprogram hd_prefix hd_IMP_Minus;;
  \<comment> \<open>\<close>
  \<comment> \<open>fst'_state_p' = hd_ret hd_ret_state;\<close>
  (fst'_prefix @ fst'_p_str) ::= A (V (hd_prefix @ hd_ret_str));;
  \<comment> \<open>fst'_state = \<lparr>fst'_state_p = fst'_state_p'\<rparr>;\<close>
  \<comment> \<open>fst'_ret_state = fst'_imp fst'_state;\<close>
  invoke_subprogram fst'_prefix fst'_IMP_Minus;;
  \<comment> \<open>\<close>
  \<comment> \<open>NOTEQUAL_neq_zero_a' = fst'_state_p fst'_ret_state;\<close>
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_a_str) ::= A (V (fst'_prefix @ fst'_p_str));;
  \<comment> \<open>NOTEQUAL_neq_zero_b' = map_list_find_aux_a s;\<close>
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_b_str) ::= A (V map_list_find_aux_a_str);;
  \<comment> \<open>NOTEQUAL_neq_zero_ret' = 0;\<close>
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str) ::= A (N 0);;
  \<comment> \<open>NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',\<close>
  \<comment> \<open>                           NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',\<close>
  \<comment> \<open>                           NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;\<close>
  \<comment> \<open>NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;\<close>
  invoke_subprogram NOTEQUAL_neq_zero_prefix NOTEQUAL_neq_zero_IMP_Minus;;
  \<comment> \<open>\<close>
  \<comment> \<open>AND_neq_zero_a' =  map_list_find_aux_xs s;\<close>
  (AND_neq_zero_prefix @ AND_neq_zero_a_str) ::= A (V map_list_find_aux_xs_str);;
  \<comment> \<open>AND_neq_zero_b' = NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state;\<close>
  (AND_neq_zero_prefix @ AND_neq_zero_b_str) ::= A (V (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str));;
  \<comment> \<open>AND_neq_zero_ret' = 0;\<close>
  (AND_neq_zero_prefix @ AND_neq_zero_ret_str) ::= A (N 0);;
  \<comment> \<open>AND_neq_zero_state = \<lparr>AND_neq_zero_a = AND_neq_zero_a',\<close>
  \<comment> \<open>                     AND_neq_zero_b = AND_neq_zero_b',\<close>
  \<comment> \<open>                     AND_neq_zero_ret = AND_neq_zero_ret'\<rparr>;\<close>
  \<comment> \<open>AND_neq_zero_ret_state = AND_neq_zero_imp AND_neq_zero_state;\<close>
  invoke_subprogram AND_neq_zero_prefix AND_neq_zero_IMP_Minus;;
  \<comment> \<open>condition = AND_neq_zero_ret AND_neq_zero_ret_state\<close>
  map_list_find_aux_while_cond ::= A (V (AND_neq_zero_prefix @ AND_neq_zero_ret_str))
  \<comment> \<open>\<close>
  \<comment> \<open>condition\<close>
"

definition "map_list_find_aux_IMP_loop_body \<equiv>
  \<comment> \<open> tl_xs' = map_list_find_aux_xs s;\<close>
  (tl_prefix @ tl_xs_str) ::= A (V map_list_find_aux_xs_str);;
  \<comment> \<open> tl_ret' = 0;\<close>
  (tl_prefix @ tl_ret_str) ::= A (N 0);;
  \<comment> \<open> tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;\<close>
  \<comment> \<open> tl_ret_state = tl_imp tl_state;\<close>
  invoke_subprogram tl_prefix tl_IMP_Minus;;
  \<comment> \<open> map_list_find_aux_xs' = tl_ret tl_ret_state;\<close>
  map_list_find_aux_xs_str ::= A (V (tl_prefix @ tl_ret_str))
  \<comment> \<open> ret = \<lparr>map_list_find_aux_xs = map_list_find_aux_xs',\<close>
  \<comment> \<open>        map_list_find_aux_a = map_list_find_aux_a s,\<close>
  \<comment> \<open>        map_list_find_aux_ret = map_list_find_aux_ret s\<rparr>\<close>
  \<comment> \<open>in\<close>
  \<comment> \<open> ret)\<close>
  \<comment> \<open>\<close>
"

abbreviation "map_list_find_aux_xs_temp_str \<equiv> ''map_list_find_aux_xs_temp''"

definition "map_list_find_aux_IMP_after_loop \<equiv>
  \<comment> \<open>let \<close>
  \<comment> \<open>  map_list_find_aux_xs' = map_list_find_aux_xs s\<close>
  map_list_find_aux_xs_temp_str ::= A (V map_list_find_aux_xs_str);;

  \<comment> \<open>in\<close>
  \<comment> \<open>(if map_list_find_aux_xs' \<noteq> 0 then  \<close>
  (IF  map_list_find_aux_xs_temp_str \<noteq>0 
    THEN (    
  \<comment> \<open>  let \<close>
  \<comment> \<open>   hd_xs' = map_list_find_aux_xs s;\<close>
  (hd_prefix @ hd_xs_str) ::= A (V map_list_find_aux_xs_str);;
  \<comment> \<open>   hd_ret' = 0;\<close>
  (hd_prefix @ hd_ret_str) ::= A (N 0);;
  \<comment> \<open>   hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;\<close>
  \<comment> \<open>   hd_ret_state = hd_imp hd_state;\<close>
  invoke_subprogram hd_prefix hd_IMP_Minus;;
  \<comment> \<open>\<close>
  \<comment> \<open>   snd'_state_p' = hd_ret hd_ret_state;\<close>
  (snd'_prefix @ snd'_p_str) ::= A (V (hd_prefix @ hd_ret_str));;
  \<comment> \<open>   snd'_state = \<lparr>snd'_state_p = snd'_state_p'\<rparr>;\<close>
  \<comment> \<open>   snd'_ret_state = snd'_imp snd'_state;\<close>
  invoke_subprogram snd'_prefix snd'_IMP_Minus;;
  \<comment> \<open>\<close>
  \<comment> \<open>   some_nat_n' = snd'_state_p snd'_ret_state;\<close>
  (some_nat_prefix @ some_nat_n_str) ::= A (V (snd'_prefix @ snd'_p_str));;
  \<comment> \<open>   some_nat_ret' = 0;\<close>
  (some_nat_prefix @ some_nat_ret_str) ::= A (N 0);;
  \<comment> \<open>   some_nat_state = \<lparr>some_nat_n = some_nat_n', some_nat_ret = some_nat_ret'\<rparr>;\<close>
  \<comment> \<open>   some_nat_ret_state = some_nat_imp some_nat_state;\<close>
  invoke_subprogram some_nat_prefix some_nat_IMP_Minus;;
  \<comment> \<open>   map_list_find_aux_ret' = some_nat_ret some_nat_ret_state;\<close>
  map_list_find_aux_ret_str ::= A (V (some_nat_prefix @ some_nat_ret_str))
  \<comment> \<open>   \<close>
  \<comment> \<open>   ret = \<lparr>map_list_find_aux_xs = map_list_find_aux_xs s,\<close>
  \<comment> \<open>         map_list_find_aux_a = map_list_find_aux_a s,\<close>
  \<comment> \<open>         map_list_find_aux_ret = map_list_find_aux_ret'\<rparr>\<close>
  )
  ELSE (
  \<comment>\<open>map_list_find_aux_ret' = 0;
        t = t + 2;
        ret = \<lparr>map_list_find_aux_xs = map_list_find_aux_xs s,
               map_list_find_aux_a = map_list_find_aux_a s,
               map_list_find_aux_ret = map_list_find_aux_ret'\<rparr>\<close>
  map_list_find_aux_ret_str ::= A (N 0)
  ))
"

definition map_list_find_aux_IMP_Minus where
  "map_list_find_aux_IMP_Minus \<equiv>
  map_list_find_aux_IMP_init_while_cond;;
  WHILE map_list_find_aux_while_cond \<noteq>0 DO (
    map_list_find_aux_IMP_loop_body;;
    map_list_find_aux_IMP_init_while_cond
  );;
  map_list_find_aux_IMP_after_loop"

abbreviation "map_list_find_aux_IMP_vars\<equiv>
  {map_list_find_aux_xs_str, map_list_find_aux_a_str, map_list_find_aux_ret_str,
  map_list_find_aux_xs_temp_str, map_list_find_aux_while_cond}"

lemmas map_list_find_aux_IMP_subprogram_simps =
  map_list_find_aux_IMP_init_while_cond_def
  map_list_find_aux_IMP_loop_body_def
  map_list_find_aux_IMP_after_loop_def

definition "map_list_find_aux_imp_to_HOL_state p s =
  \<lparr>map_list_find_aux_xs = (s (add_prefix p map_list_find_aux_xs_str)),
   map_list_find_aux_a = (s (add_prefix p map_list_find_aux_a_str)),
   map_list_find_aux_ret = (s (add_prefix p map_list_find_aux_ret_str))\<rparr>"

lemmas map_list_find_aux_state_translators =
  map_list_find_aux_imp_to_HOL_state_def
  hd_imp_to_HOL_state_def tl_imp_to_HOL_state_def
  fst'_imp_to_HOL_state_def snd'_imp_to_HOL_state_def
  some_nat_imp_to_HOL_state_def 
  NOTEQUAL_neq_zero_imp_to_HOL_state_def
  AND_neq_zero_imp_to_HOL_state_def

lemmas map_list_find_aux_complete_simps =
  map_list_find_aux_IMP_subprogram_simps
  map_list_find_aux_imp_subprogram_simps
  map_list_find_aux_state_translators      

lemma map_list_find_aux_IMP_Minus_correct_function:
  "(invoke_subprogram p map_list_find_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p map_list_find_aux_ret_str)
      = map_list_find_aux_ret
          (map_list_find_aux_imp (map_list_find_aux_imp_to_HOL_state p s))"
  apply(induction "map_list_find_aux_imp_to_HOL_state p s" arbitrary: s s' t
    rule: map_list_find_aux_imp.induct)
  apply(subst map_list_find_aux_imp.simps)
  apply(simp only: map_list_find_aux_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule While_tE)

  subgoal
    apply(simp only: map_list_find_aux_IMP_subprogram_simps prefix_simps)
    apply(erule Seq_E)+
    apply(erule hd_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(20) by fastforce
    apply(erule fst'_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(22) by fastforce
    apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(24) by fastforce
    apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(26) by fastforce
    apply (erule If_E) 
      subgoal 
        apply (erule Seq_E)+
        apply(erule hd_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
        subgoal premises p using p(37) by fastforce
        apply(erule snd'_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
        subgoal premises p using p(39) by fastforce
        apply(erule some_nat_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
        subgoal premises p using p(41) by fastforce
        apply (fastforce simp: map_list_find_aux_IMP_subprogram_simps
          map_list_find_aux_imp_subprogram_simps
          map_list_find_aux_state_translators)
      done
      subgoal 
        apply (fastforce simp: map_list_find_aux_IMP_subprogram_simps
          map_list_find_aux_imp_subprogram_simps
          map_list_find_aux_state_translators)
      done
    done

  apply(erule Seq_E)+
  apply(dest_com_gen)

  subgoal
      apply(simp only: map_list_find_aux_IMP_init_while_cond_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule hd_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
      subgoal premises p using p(32) by fastforce
      apply(erule fst'_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
      subgoal premises p using p(34) by fastforce
      apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
      subgoal premises p using p(36) by fastforce
      apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
      subgoal premises p using p(38) by fastforce
      apply (simp only: map_list_find_aux_complete_simps Let_def) 
      apply fastforce
      done

  subgoal
      apply(subst (asm) map_list_find_aux_IMP_init_while_cond_def)
      apply(simp only: map_list_find_aux_IMP_loop_body_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule hd_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
      subgoal premises p using p(22) by fastforce
      apply(erule fst'_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
      subgoal premises p using p(24) by fastforce
      apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
      subgoal premises p using p(26) by fastforce
      apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
      subgoal premises p using p(28) by fastforce
      apply(erule tl_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
      subgoal premises p using p(30) by fastforce
      apply (simp only: map_list_find_aux_imp_subprogram_simps
          map_list_find_aux_state_translators Let_def, force)
      done

  subgoal
      apply(simp only: map_list_find_aux_IMP_init_while_cond_def prefix_simps
          map_list_find_aux_IMP_loop_body_def)
      apply(erule Seq_E)+
      apply(erule hd_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
      subgoal premises p using p(35) by fastforce
      apply(erule fst'_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
      subgoal premises p using p(37) by fastforce
      apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
      subgoal premises p using p(39) by fastforce
      apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
      subgoal premises p using p(41) by fastforce
      apply(erule tl_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
      subgoal premises p using p(43) by fastforce
      apply (simp only: map_list_find_aux_imp_subprogram_simps
          map_list_find_aux_state_translators Let_def split: if_split)
      apply fastforce
      done
  done        

lemma map_list_find_aux_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ map_list_find_aux_pref) map_list_find_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix map_list_find_aux_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemmas map_list_find_aux_complete_time_simps =
  map_list_find_aux_imp_subprogram_time_simps
  map_list_find_aux_imp_time_acc
  map_list_find_aux_imp_time_acc_2
  map_list_find_aux_imp_time_acc_3
  map_list_find_aux_state_translators

lemma map_list_find_aux_IMP_Minus_correct_time:
  "(invoke_subprogram p map_list_find_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = map_list_find_aux_imp_time 0 (map_list_find_aux_imp_to_HOL_state p s)"
  apply(induction "map_list_find_aux_imp_to_HOL_state p s" arbitrary: s s' t
      rule: map_list_find_aux_imp.induct)
  apply(subst map_list_find_aux_imp_time.simps)
  apply(simp only: map_list_find_aux_IMP_Minus_def prefix_simps)

  apply(erule Seq_tE)+
  apply(erule While_tE_time)

  subgoal
    apply(simp only: map_list_find_aux_IMP_subprogram_simps prefix_simps)
    apply(erule Seq_tE)+
    apply(erule hd_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(36) by fastforce
    apply(erule fst'_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(38) by fastforce
    apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(40) by fastforce
    apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(42) by fastforce
    apply (erule If_tE) 
      subgoal 
        apply (erule Seq_tE)+
        apply(erule hd_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
        subgoal premises p using p(62) by fastforce
        apply(erule snd'_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
        subgoal premises p using p(64) by fastforce
        apply(erule some_nat_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
        subgoal premises p using p(66) by fastforce
        apply (fastforce simp: map_list_find_aux_IMP_subprogram_simps
          map_list_find_aux_imp_subprogram_time_simps
          map_list_find_aux_state_translators Let_def)
      done
      subgoal 
        apply (fastforce simp: map_list_find_aux_IMP_subprogram_simps
          map_list_find_aux_imp_subprogram_time_simps
          map_list_find_aux_state_translators Let_def)
      done
    done

  apply(erule Seq_tE)+
  apply(simp add: add.assoc)
  apply(dest_com_gen_time)

  subgoal
    apply(simp only: map_list_find_aux_IMP_init_while_cond_def prefix_simps)
    apply(erule Seq_tE)+
    apply(erule hd_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(61) by fastforce
    apply(erule fst'_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(63) by fastforce
    apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(65) by fastforce
    apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(67) by fastforce
    apply (simp only: map_list_find_aux_complete_simps Let_def) 
    apply fastforce
    done

  subgoal
    apply(subst (asm) map_list_find_aux_IMP_init_while_cond_def)
    apply(simp only: map_list_find_aux_IMP_loop_body_def prefix_simps)
    apply(erule Seq_tE)+
    apply(erule hd_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(41) by fastforce
    apply(erule fst'_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(43) by fastforce
    apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(45) by fastforce
    apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(47) by fastforce
    apply(erule tl_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(49) by fastforce
    apply (simp only: map_list_find_aux_imp_subprogram_simps
          map_list_find_aux_state_translators Let_def split: if_split)
    apply fastforce
    done

  subgoal
    apply(simp only: prefix_simps map_list_find_aux_IMP_init_while_cond_def
        map_list_find_aux_IMP_loop_body_def)
    apply(erule Seq_tE)+
    apply(erule hd_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(67) by fastforce
    apply(erule fst'_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(69) by fastforce
    apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(71) by fastforce
    apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(73) by fastforce
    apply(erule tl_IMP_Minus_correct[where vars = "map_list_find_aux_IMP_vars"])
    subgoal premises p using p(75) by fastforce
    apply (simp only: map_list_find_aux_complete_time_simps Let_def)
    apply fastforce
    done
  done  

lemma map_list_find_aux_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) map_list_find_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (map_list_find_aux_imp_time 0 (map_list_find_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) map_list_find_aux_ret_str) =
          map_list_find_aux_ret (map_list_find_aux_imp
                                        (map_list_find_aux_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using map_list_find_aux_IMP_Minus_correct_function
  by (auto simp: map_list_find_aux_IMP_Minus_correct_time)
    (meson map_list_find_aux_IMP_Minus_correct_effects set_mono_prefix)    

subsubsection \<open>length\<close>
(* changes its argument which makes very messy correctness lemmas *)
(* therefore we now wrap this length in the below length' *)

record length_state = length_xs::nat length_ret::nat

(*definition [prefix_defs]:*) abbreviation   "length_prefix \<equiv> ''length.''"
(*definition [prefix_defs]:*) abbreviation   "length_xs_str \<equiv> ''xs''"
(*definition [prefix_defs]:*) abbreviation   "length_ret_str \<equiv> ''length_ret''"

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
declare
  arg_cong[where f=length_nat, let_lemmas]
  length_state.simps[state_simps]

lemma length_imp_correct[let_function_correctness]:
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

lemma length_imp_correct2:
  "length_ret s = 0 \<Longrightarrow> length_ret (length_imp s) = length_nat (length_xs s)"
  by (metis length_imp_correct minus_nat.diff_0)

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
  apply (subst length_imp_time.simps)
  apply (subst (2) length_imp_time.simps)
  by (simp add: length_state_upd_def Let_def eval_nat_numeral)

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
  apply(simp only: length_IMP_Minus_def prefix_simps)
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
  apply (auto simp: prefix_defs) [1]

  apply(drule AssignD)+
  apply(elim conjE)
  apply(auto simp: length_state_upd_def length_imp_to_HOL_state_def length_imp_time_acc)[1]
  apply(subst length_imp_time_acc_2)
  apply(auto simp: tl_imp_to_HOL_state_def prefix_defs)[1]
  done

lemma length_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ p2) length_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> v \<in> vars \<Longrightarrow>
  \<not> (prefix p2 v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma length_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) length_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (length_imp_time 0 (length_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) length_ret_str) = length_ret (length_imp (length_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using length_IMP_Minus_correct_time length_IMP_Minus_correct_function
    length_IMP_Minus_correct_effects
  by auto


subsubsection \<open>length'\<close> (* wrapper for length *)


record length'_state = length'_xs::nat length'_ret::nat

(*definition [prefix_defs]:*) abbreviation "length'_prefix \<equiv> ''length'.''"
(*definition [prefix_defs]:*) abbreviation "length'_xs_str \<equiv> ''xs''"
(*definition [prefix_defs]:*) abbreviation "length'_ret_str \<equiv> ''length'_ret''"

function length'_imp:: "length'_state \<Rightarrow> length'_state" where
  "length'_imp s =
    (
     let
        length_xs' = (length'_xs s);
        length_ret' = 0;
        length_state = \<lparr>length_xs = length_xs', length_ret = length_ret'\<rparr>;
        length_state_ret = length_imp length_state;
        length'_xs' = (length'_xs s);
        length'_ret' = length_ret length_state_ret;
        ret = \<lparr>length'_xs = length'_xs', length'_ret = length'_ret'\<rparr>
      in
        ret
    )
  "
  by pat_completeness auto
termination
  using "termination" by blast

declare length'_imp.simps [simp del]

declare
  arg_cong2[where f=length'_state.make, state_congs]
  arg_cong[where f=length'_ret, state_congs]
  arg_cong[where f=length'_imp, state_congs]
  length'_state.simps[state_simps]

lemma length'_imp_correct[let_function_correctness]:
  "length'_ret (length'_imp s)  = length_nat (length'_xs s)"
  by (metis length'_imp.elims length'_state.select_convs(2)
      length_imp_correct2 length_state.select_convs(1) length_state.select_convs(2))


function length'_imp_time:: "nat \<Rightarrow> length'_state\<Rightarrow> nat" where
  "length'_imp_time t s =
  (
     let
        length_xs' = (length'_xs s);
        t = t + 2;
        length_ret' = 0;
        t = t + 2;
        length_state = \<lparr>length_xs = length_xs', length_ret = length_ret'\<rparr>;
        length_state_ret = length_imp length_state;
        t = t + length_imp_time 0 length_state;
        length'_xs' = (length'_xs s);
        t = t + 2;
        length'_ret' = length_ret length_state_ret;
        t = t + 2;
        ret = t
      in
        ret
    )
"
  by pat_completeness auto
termination
  by  (relation "Wellfounded.measure (\<lambda>(t,s). length'_xs s)")
    (auto simp: length_imp_correct Let_def split: if_splits)

lemmas [simp del] = length'_imp_time.simps

lemma length'_imp_time_acc: "(length'_imp_time (Suc t) s) = Suc (length'_imp_time t s)"
  apply (induction t s arbitrary:  rule: length'_imp_time.induct)
  apply (subst length'_imp_time.simps)
  by (simp add: length'_imp_time.simps Let_def eval_nat_numeral)

lemma length'_imp_time_acc_2: "(length'_imp_time x s) = x + (length'_imp_time 0 s)"
  by (induction x arbitrary: s)
     (auto simp add: length'_imp_time_acc length_state_upd_def Let_def eval_nat_numeral split: if_splits)

definition length'_IMP_Minus where
  "length'_IMP_Minus \<equiv>
  (
        \<comment> \<open>length_xs' = (length'_xs s);\<close>
     (length_prefix @ length_xs_str) ::= (A (V length'_xs_str));;
        \<comment> \<open>length_ret' = 0;\<close>
     (length_prefix @ length_ret_str) ::= (A (N 0));;
        \<comment> \<open>length_state = \<lparr>length_xs = length_xs', length_ret = length_ret'\<rparr>;\<close>
        \<comment> \<open>length_state_ret = length_imp length_state;\<close>
     invoke_subprogram length_prefix length_IMP_Minus;;
        \<comment> \<open>length'_xs' = (length'_xs s);\<close>
     length'_xs_str ::= (A (V (length'_xs_str)));;
        \<comment> \<open>length'_ret' = length_ret length_state_ret;\<close>
     length'_ret_str ::= (A (V (length_prefix @ length_ret_str)))

  )"

definition "length'_imp_to_HOL_state p s =
  \<lparr>length'_xs = (s (add_prefix p length'_xs_str)), length'_ret = (s (add_prefix p length'_ret_str))\<rparr>"

lemma length'_IMP_Minus_correct_function:
  "(invoke_subprogram p length'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p length'_ret_str) = length'_ret (length'_imp (length'_imp_to_HOL_state p s))"
  apply(induction "length'_imp_to_HOL_state p s" arbitrary: s s' t rule: length'_imp.induct)
  apply(subst length'_imp.simps)
  apply(simp only: length'_IMP_Minus_def prefix_simps)
   apply(subst length_imp.simps)
   apply(auto simp: length'_imp_time_acc length'_imp_to_HOL_state_def)
  apply(erule length_IMP_Minus_correct[where vars = "{length'_ret_str}"])
  subgoal by auto
  apply (simp only: Let_def)
  apply(auto simp: length'_imp_to_HOL_state_def)[1]
  apply(auto simp: length_imp_to_HOL_state_def length_state_upd_def )[1]
  subgoal
    (* the stupid case where the correctness lemma from imp_correct fails *)
    by (metis One_nat_def add_0 length_imp.elims length_state.select_convs(1)
         length_state.select_convs(2) length_state_upd_def not_gr0)
  apply(auto simp: length_imp_to_HOL_state_def length_state_upd_def)[1]
  by (auto simp: length_imp_correct2)



lemma length'_IMP_Minus_correct_time:
  "(invoke_subprogram p length'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = length'_imp_time 0 (length'_imp_to_HOL_state p s)"
  apply(induction "length'_imp_to_HOL_state p s" arbitrary: s s' t rule: length'_imp.induct)
  apply(subst length'_imp_time.simps)
  apply(simp only: length'_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps
      atomExp_add_prefix.simps invoke_subprogram_append)
   apply(auto simp: length'_imp_to_HOL_state_def)[1]
  apply(erule length_IMP_Minus_correct[where vars = "{length'_ret_str}"])
   apply auto [1]
  by(auto simp: length_imp_to_HOL_state_def)[1]

lemma length'_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ p2) length'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> v \<in> vars \<Longrightarrow>
  \<not> (prefix p2 v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma length'_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) length'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (length'_imp_time 0 (length'_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) length'_ret_str) = length'_ret (length'_imp (length'_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using length'_IMP_Minus_correct_time length'_IMP_Minus_correct_function
    length'_IMP_Minus_correct_effects
  by auto

subsubsection \<open>cons\<close>

record cons_state = cons_h::nat cons_t::nat cons_ret::nat

(*definition [prefix_defs]:*) abbreviation   "cons_prefix \<equiv> ''cons.''"
(*definition [prefix_defs]:*) abbreviation   "cons_h_str \<equiv> ''h''"
(*definition [prefix_defs]:*) abbreviation   "cons_t_str \<equiv> ''t''"
(*definition [prefix_defs]:*) abbreviation   "cons_ret_str \<equiv> ''cons_ret''"

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
declare
  arg_cong3[where f=cons_state.make, state_congs]
  arg_cong[where f=cons_imp, state_congs]
  arg_cong[where f=cons_ret, state_congs]
  arg_cong2[where f=cons, let_lemmas]
  cons_state.simps[state_simps]

lemma cons_imp_correct[let_function_correctness]:
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
  \<lparr>cons_h = (s (add_prefix p cons_h_str)),
   cons_t = (s (add_prefix p cons_t_str)),
   cons_ret = (s (add_prefix p cons_ret_str))\<rparr>"

lemma cons_IMP_Minus_correct_function:
  "(invoke_subprogram p cons_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p cons_ret_str) = cons_ret (cons_imp (cons_imp_to_HOL_state p s))"
  by(fastforce elim: prod_encode_IMP_Minus_correct simp add: cons_IMP_Minus_def cons_imp.simps
      invoke_subprogram_append cons_state_upd_def cons_imp_to_HOL_state_def
      prod_encode_imp_to_HOL_state_def)

lemma cons_IMP_Minus_correct_time:
  "(invoke_subprogram p cons_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = cons_imp_time 0 (cons_imp_to_HOL_state p s)"
  by(fastforce elim: prod_encode_IMP_Minus_correct simp add: cons_IMP_Minus_def cons_imp_time.simps
      invoke_subprogram_append cons_state_upd_def cons_imp_to_HOL_state_def
      prod_encode_imp_to_HOL_state_def)

lemma cons_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ cons_pref) cons_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> v \<in> vars
  \<Longrightarrow> \<not> (prefix cons_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma cons_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) cons_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (cons_imp_time 0 (cons_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) cons_ret_str) =
        cons_ret (cons_imp (cons_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using cons_IMP_Minus_correct_time cons_IMP_Minus_correct_function
    cons_IMP_Minus_correct_effects
  by auto


subsubsection \<open>reverse\<close>

paragraph \<open>reverse_nat_acc\<close>

record reverse_nat_acc_state =
  reverse_nat_acc_acc::nat
  reverse_nat_acc_n::nat
  reverse_nat_acc_ret::nat

abbreviation "reverse_nat_acc_prefix \<equiv> ''reverse_nat_acc.''"
abbreviation "reverse_nat_acc_acc_str \<equiv> ''acc''"
abbreviation "reverse_nat_acc_n_str \<equiv> ''n''"
abbreviation "reverse_nat_acc_ret_str \<equiv> ''ret''"

definition "reverse_nat_acc_state_upd s \<equiv>
      let
        hd_xs' = reverse_nat_acc_n s;
        hd_ret' = 0;
        hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
        hd_state_ret = hd_imp hd_state;
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

lemma reverse_nat_acc_imp_correct[let_function_correctness]:
  "reverse_nat_acc_ret (reverse_nat_acc_imp s)
    = reverse_nat_acc (reverse_nat_acc_acc s) (reverse_nat_acc_n s)"
  by(induction s rule: reverse_nat_acc_imp.induct)
    (subst reverse_nat_acc_imp.simps,
      simp add: cons_imp_correct hd_imp_correct tl_imp_correct reverse_nat_acc_imp_subprogram_simps)

definition "reverse_nat_acc_state_upd_time t s \<equiv>
      let
        hd_xs' = reverse_nat_acc_n s;
        t = t + 2;
        hd_ret' = 0;
        t = t + 2;
        hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
        hd_state_ret = hd_imp hd_state;
        t = t + hd_imp_time 0 hd_state;
        cons_h' = hd_ret hd_state_ret;
        t = t + 2;
        cons_t' = reverse_nat_acc_acc s;
        t = t + 2;
        cons_ret' = 0;
        t = t + 2;
        cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
        cons_ret_state = cons_imp cons_state;
        t = t + cons_imp_time 0 cons_state;
        reverse_nat_acc_acc' = cons_ret cons_ret_state;
        t = t + 2;
        tl_xs' = reverse_nat_acc_n s;
        t = t + 2;
        tl_ret' = 0;
        t = t + 2;
        tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
        tl_state_ret = tl_imp tl_state;
        t = t + tl_imp_time 0 tl_state;
        reverse_nat_acc_n' = tl_ret tl_state_ret;
        t = t + 2;
        ret = t
      in
        ret
"

definition "reverse_nat_acc_imp_compute_loop_condition_time t s \<equiv>
  (let
    condition = reverse_nat_acc_n s;
    t = t + 2;
    ret = t
   in ret
  )"

definition "reverse_nat_acc_imp_after_loop_time t s \<equiv>
  (let
    t = t + 2;
    ret = t
   in ret
  )"

function reverse_nat_acc_imp_time:: "nat \<Rightarrow> reverse_nat_acc_state \<Rightarrow> nat" where
  "reverse_nat_acc_imp_time t s =
  reverse_nat_acc_imp_compute_loop_condition_time 0 s +
  (if reverse_nat_acc_imp_compute_loop_condition s \<noteq> 0
   then
    (let
        t = t + 1;
        next_iteration
          = reverse_nat_acc_imp_time (t + reverse_nat_acc_state_upd_time 0 s)
                                     (reverse_nat_acc_state_upd s)
     in next_iteration)
  else
    (let
        t = t + 2;
        ret = t + reverse_nat_acc_imp_after_loop_time 0 s
     in ret)
  )"
  by auto
termination
  by (relation "measure (\<lambda>(t,s). reverse_nat_acc_n s)")
    (simp add: tl_imp_correct reverse_nat_acc_imp_subprogram_simps)+

lemmas reverse_nat_acc_imp_subprogram_time_simps =
  reverse_nat_acc_imp_subprogram_simps
  reverse_nat_acc_imp_after_loop_time_def
  reverse_nat_acc_state_upd_time_def
  reverse_nat_acc_imp_compute_loop_condition_time_def

lemmas [simp del] = reverse_nat_acc_imp_time.simps

lemma reverse_nat_acc_imp_time_acc:
  "(reverse_nat_acc_imp_time (Suc t) s) = Suc (reverse_nat_acc_imp_time t s)"
  by (induction t s rule: reverse_nat_acc_imp_time.induct)
    ((subst (1 2) reverse_nat_acc_imp_time.simps); (simp add: reverse_nat_acc_state_upd_def))

lemma reverse_nat_acc_imp_time_acc_2_aux:
  "(reverse_nat_acc_imp_time t s) =
    t + (reverse_nat_acc_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: reverse_nat_acc_imp_time_acc)+

lemma reverse_nat_acc_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (reverse_nat_acc_imp_time t s) =
    t + (reverse_nat_acc_imp_time 0 s)"
  by (rule reverse_nat_acc_imp_time_acc_2_aux)

lemma reverse_nat_acc_imp_time_acc_3:
  "(reverse_nat_acc_imp_time (a + b) s) =
    a + (reverse_nat_acc_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: reverse_nat_acc_imp_time_acc)+

abbreviation "reverse_nat_acc_while_cond \<equiv> ''condition''"

definition "reverse_nat_acc_IMP_init_while_cond \<equiv>
  \<comment> \<open>condition = n_hashes_n s\<close>
  reverse_nat_acc_while_cond ::= (A (V reverse_nat_acc_n_str))"

definition "reverse_nat_acc_IMP_loop_body \<equiv>
  \<comment> \<open>hd_xs' = reverse_nat_acc_n s;\<close>
  (hd_prefix @ hd_xs_str) ::= (A (V reverse_nat_acc_n_str));;
  \<comment> \<open>hd_ret' = 0;\<close>
  (hd_prefix @ hd_ret_str) ::= (A (N 0));;
  \<comment> \<open>hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;\<close>
  \<comment> \<open>hd_state_ret = hd_imp hd_state;\<close>
  invoke_subprogram hd_prefix hd_IMP_Minus;;
  \<comment> \<open>cons_h' = hd_ret hd_state_ret;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V (hd_prefix @ hd_ret_str)));;
  \<comment> \<open>cons_t' = reverse_nat_acc_acc s;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V reverse_nat_acc_acc_str));;
  \<comment> \<open>cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>cons_ret_state = cons_imp cons_state;\<close>
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  \<comment> \<open>reverse_nat_acc_acc' = cons_ret cons_ret_state;\<close>
  reverse_nat_acc_acc_str ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>tl_xs' = reverse_nat_acc_n s;\<close>
  (tl_prefix @ tl_xs_str) ::= (A (V reverse_nat_acc_n_str));;
  \<comment> \<open>tl_ret' = 0;\<close>
  (tl_prefix @ tl_ret_str) ::= (A (N 0));;
  \<comment> \<open>tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;\<close>
  \<comment> \<open>tl_state_ret = tl_imp tl_state;\<close>
  invoke_subprogram tl_prefix tl_IMP_Minus;;
  \<comment> \<open>reverse_nat_acc_n' = tl_ret tl_state_ret;\<close>
  reverse_nat_acc_n_str ::= (A (V (tl_prefix @ tl_ret_str)))
"

definition "reverse_nat_acc_IMP_after_loop \<equiv>
  \<comment> \<open>ret = s\<close>
  ((reverse_nat_acc_ret_str) ::= (A (V reverse_nat_acc_acc_str)))"

definition reverse_nat_acc_IMP_Minus where
  "reverse_nat_acc_IMP_Minus \<equiv>
  reverse_nat_acc_IMP_init_while_cond;;
  WHILE reverse_nat_acc_while_cond \<noteq>0 DO (
    reverse_nat_acc_IMP_loop_body;;
    reverse_nat_acc_IMP_init_while_cond
  );;
  reverse_nat_acc_IMP_after_loop"

abbreviation
  "reverse_nat_acc_IMP_vars \<equiv>
  {reverse_nat_acc_acc_str, reverse_nat_acc_n_str, reverse_nat_acc_ret_str}"

lemmas reverse_nat_acc_IMP_subprogram_simps =
  reverse_nat_acc_IMP_init_while_cond_def
  reverse_nat_acc_IMP_loop_body_def
  reverse_nat_acc_IMP_after_loop_def

definition "reverse_nat_acc_imp_to_HOL_state p s =
  \<lparr>reverse_nat_acc_acc = (s (add_prefix p reverse_nat_acc_acc_str)),
   reverse_nat_acc_n = (s (add_prefix p reverse_nat_acc_n_str)),
   reverse_nat_acc_ret = (s (add_prefix p reverse_nat_acc_ret_str))\<rparr>"

lemmas reverse_nat_acc_state_translators =
  hd_imp_to_HOL_state_def
  tl_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def
  reverse_nat_acc_imp_to_HOL_state_def

lemmas reverse_nat_acc_complete_simps =
  reverse_nat_acc_IMP_subprogram_simps
  reverse_nat_acc_imp_subprogram_simps
  reverse_nat_acc_state_translators

lemma reverse_nat_acc_IMP_Minus_correct_function:
  "(invoke_subprogram p reverse_nat_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p reverse_nat_acc_ret_str)
      = reverse_nat_acc_ret (reverse_nat_acc_imp (reverse_nat_acc_imp_to_HOL_state p s))"
  apply(induction "reverse_nat_acc_imp_to_HOL_state p s" arbitrary: s s' t
      rule: reverse_nat_acc_imp.induct)
  apply(subst reverse_nat_acc_imp.simps)

  apply(simp only: reverse_nat_acc_IMP_Minus_def prefix_simps)
  apply(vcg reverse_nat_acc_IMP_vars)

  subgoal
    apply(subst (asm) (3) reverse_nat_acc_IMP_init_while_cond_def)
    apply(subst (asm) (2) reverse_nat_acc_IMP_after_loop_def)
    apply(simp only: prefix_simps)
    by(fastforce simp: reverse_nat_acc_complete_simps)

  subgoal
    apply(subst (asm) (1) reverse_nat_acc_IMP_init_while_cond_def)
    apply(simp only: prefix_simps)
    by(fastforce simp: Let_def reverse_nat_acc_complete_simps)

  subgoal
    apply(subst (asm) (1) reverse_nat_acc_IMP_init_while_cond_def)
    apply(subst (asm) (1) reverse_nat_acc_IMP_loop_body_def)
    apply(simp only: prefix_simps)
    apply(vcg reverse_nat_acc_IMP_vars)
    by(fastforce simp: reverse_nat_acc_complete_simps)

  subgoal
    apply(subst (asm) (1) reverse_nat_acc_IMP_init_while_cond_def)
    apply(subst (asm) (1) reverse_nat_acc_IMP_loop_body_def)
    apply(simp only: prefix_simps)
    apply(vcg reverse_nat_acc_IMP_vars)
    by(fastforce simp: reverse_nat_acc_complete_simps)
  done

lemma reverse_nat_acc_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ reverse_nat_acc_pref) reverse_nat_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix reverse_nat_acc_pref v)\<rbrakk>
  \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma reverse_nat_acc_IMP_Minus_correct_time_loop_condition:
  "(invoke_subprogram p reverse_nat_acc_IMP_init_while_cond, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = reverse_nat_acc_imp_compute_loop_condition_time 0 (reverse_nat_acc_imp_to_HOL_state p s)"
  by (subst reverse_nat_acc_imp_compute_loop_condition_time_def)
    (auto simp: reverse_nat_acc_IMP_init_while_cond_def)

lemmas reverse_nat_acc_complete_time_simps =
  reverse_nat_acc_imp_subprogram_time_simps
  reverse_nat_acc_imp_time_acc_2
  reverse_nat_acc_imp_time_acc_3
  reverse_nat_acc_state_translators

lemma reverse_nat_acc_IMP_Minus_correct_time:
  "(invoke_subprogram p reverse_nat_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = reverse_nat_acc_imp_time 0 (reverse_nat_acc_imp_to_HOL_state p s)"
  apply(induction "reverse_nat_acc_imp_to_HOL_state p s" arbitrary: s s' t
      rule: reverse_nat_acc_imp.induct)
  apply(subst reverse_nat_acc_imp_time.simps)
  apply(simp only: reverse_nat_acc_IMP_Minus_def prefix_simps)
  apply(vcg_time reverse_nat_acc_IMP_vars)

  subgoal
    apply(subst (asm) (3) reverse_nat_acc_IMP_init_while_cond_def)
    apply(subst (asm) (2) reverse_nat_acc_IMP_after_loop_def)
    apply(simp only: prefix_simps)
    by (fastforce simp: reverse_nat_acc_imp_subprogram_time_simps
        reverse_nat_acc_state_translators)

  apply(simp add: add.assoc)
  apply(vcg_time reverse_nat_acc_IMP_vars)


  subgoal
    apply(subst (asm) (1) reverse_nat_acc_IMP_init_while_cond_def)
    apply(simp only: prefix_simps)
    by(fastforce simp: Let_def reverse_nat_acc_complete_simps)

  subgoal
    apply(subst (asm) (1) reverse_nat_acc_IMP_init_while_cond_def)
    apply(subst (asm) (1) reverse_nat_acc_IMP_loop_body_def)
    apply(simp only: prefix_simps)
    apply(vcg reverse_nat_acc_IMP_vars)
    by(fastforce simp: reverse_nat_acc_complete_simps)

  subgoal
    apply(subst (asm) (1) reverse_nat_acc_IMP_init_while_cond_def)
    apply(subst (asm) (1) reverse_nat_acc_IMP_loop_body_def)
    apply(simp only: prefix_simps)
    apply(vcg_time reverse_nat_acc_IMP_vars)
    by(fastforce_sorted_premises simp: reverse_nat_acc_complete_time_simps Let_def)
  done

lemma reverse_nat_acc_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) reverse_nat_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (reverse_nat_acc_imp_time 0 (reverse_nat_acc_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) reverse_nat_acc_ret_str) =
        reverse_nat_acc_ret (reverse_nat_acc_imp (reverse_nat_acc_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using reverse_nat_acc_IMP_Minus_correct_function
  by (auto simp: reverse_nat_acc_IMP_Minus_correct_time)
    (meson reverse_nat_acc_IMP_Minus_correct_effects set_mono_prefix)


paragraph \<open>reverse_nat\<close>

record reverse_nat_state =
  reverse_nat_n::nat
  reverse_nat_ret::nat

abbreviation "reverse_nat_prefix \<equiv> ''reverse_nat.''"
abbreviation "reverse_nat_n_str \<equiv> ''n''"
abbreviation "reverse_nat_ret_str \<equiv> ''ret''"


definition "reverse_nat_state_upd s \<equiv>
  (let
      reverse_nat_acc_acc' = 0;
      reverse_nat_acc_n' = reverse_nat_n s;
      reverse_nat_acc_ret' = 0;
      reverse_nat_acc_state = \<lparr>reverse_nat_acc_acc = reverse_nat_acc_acc',
                            reverse_nat_acc_n = reverse_nat_acc_n',
                            reverse_nat_acc_ret = reverse_nat_acc_ret'\<rparr>;
      reverse_nat_acc_ret_state = reverse_nat_acc_imp reverse_nat_acc_state;
      reverse_nat_ret' = reverse_nat_acc_ret reverse_nat_acc_ret_state;
      reverse_nat_n' = reverse_nat_n s;
      ret = \<lparr>reverse_nat_n = reverse_nat_n',
             reverse_nat_ret = reverse_nat_ret' \<rparr>
    in
      ret
)"

function reverse_nat_imp:: "reverse_nat_state \<Rightarrow> reverse_nat_state" where
  "reverse_nat_imp s =
  (let
      ret = reverse_nat_state_upd s
    in
      ret
  )"
  by simp+
termination
  by (relation "measure (\<lambda>s. reverse_nat_n s)") simp

lemmas [simp del] = reverse_nat_imp.simps

lemma reverse_nat_imp_correct[let_function_correctness]:
  "reverse_nat_ret (reverse_nat_imp s) = reverse_nat (reverse_nat_n s)"
  by (simp add: reverse_nat_imp.simps reverse_nat_acc_imp_correct reverse_nat_def Let_def
      reverse_nat_state_upd_def)

function reverse_nat_imp_time:: "nat \<Rightarrow> reverse_nat_state \<Rightarrow> nat" where
  "reverse_nat_imp_time t s =
  (let
      reverse_nat_acc_acc' = 0;
      t = t + 2;
      reverse_nat_acc_n' = reverse_nat_n s;
      t = t + 2;
      reverse_nat_acc_ret' = 0;
      t = t + 2;
      reverse_nat_acc_state = \<lparr>reverse_nat_acc_acc = reverse_nat_acc_acc',
                            reverse_nat_acc_n = reverse_nat_acc_n',
                            reverse_nat_acc_ret = reverse_nat_acc_ret'\<rparr>;
      reverse_nat_acc_ret_state = reverse_nat_acc_imp reverse_nat_acc_state;
      t = t + reverse_nat_acc_imp_time 0 reverse_nat_acc_state;
      reverse_nat_ret' = reverse_nat_acc_ret reverse_nat_acc_ret_state;
      t = t + 2;
      ret = t
    in
      ret
  )"
  by auto
termination
  by (relation "measure (\<lambda>(t, s). reverse_nat_n s)") simp

lemmas [simp del] = reverse_nat_imp_time.simps

lemma reverse_nat_imp_time_acc:
  "(reverse_nat_imp_time (Suc t) s) = Suc (reverse_nat_imp_time t s)"
  by (simp add: reverse_nat_imp_time.simps)

lemma reverse_nat_imp_time_acc_2:
  "(reverse_nat_imp_time x s) = x + (reverse_nat_imp_time 0 s)"
  by (simp add: reverse_nat_imp_time.simps)

definition reverse_nat_IMP_Minus where
  "reverse_nat_IMP_Minus \<equiv>
  \<comment> \<open>reverse_nat_acc_acc' = 0;\<close>
  (reverse_nat_acc_prefix @ reverse_nat_acc_acc_str) ::= (A (N 0));;
  \<comment> \<open>reverse_nat_acc_n' = reverse_nat_n s;\<close>
  (reverse_nat_acc_prefix @ reverse_nat_acc_n_str) ::= (A (V reverse_nat_n_str));;
  \<comment> \<open>reverse_nat_acc_ret' = 0;\<close>
  (reverse_nat_acc_prefix @ reverse_nat_acc_ret_str) ::= (A (N 0));;
  \<comment> \<open>reverse_nat_acc_state = \<lparr>reverse_nat_acc_acc = reverse_nat_acc_acc',\<close>
  \<comment> \<open>                         reverse_nat_acc_n = reverse_nat_acc_n',\<close>
  \<comment> \<open>                         reverse_nat_acc_ret = reverse_nat_acc_ret'\<rparr>;\<close>
  \<comment> \<open>reverse_nat_acc_ret_state = reverse_nat_acc_imp reverse_nat_acc_state;\<close>
  invoke_subprogram reverse_nat_acc_prefix reverse_nat_acc_IMP_Minus;;
  \<comment> \<open>reverse_nat_ret' = reverse_nat_acc_ret reverse_nat_acc_ret_state;\<close>
  reverse_nat_ret_str ::= (A (V (reverse_nat_acc_prefix @ reverse_nat_acc_ret_str)))
"

abbreviation
  "reverse_nat_IMP_vars \<equiv>
  {reverse_nat_n_str, reverse_nat_ret_str}"

definition "reverse_nat_imp_to_HOL_state p s =
  \<lparr>reverse_nat_n = (s (add_prefix p reverse_nat_n_str)),
   reverse_nat_ret = (s (add_prefix p reverse_nat_ret_str))\<rparr>"

lemma reverse_nat_IMP_Minus_correct_function:
  "(invoke_subprogram p reverse_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p reverse_nat_ret_str)
      = reverse_nat_ret (reverse_nat_imp (reverse_nat_imp_to_HOL_state p s))"
  by (fastforce elim: reverse_nat_acc_IMP_Minus_correct simp: reverse_nat_imp_to_HOL_state_def
      reverse_nat_imp.simps reverse_nat_state_upd_def reverse_nat_acc_imp_to_HOL_state_def
      reverse_nat_IMP_Minus_def invoke_subprogram_append)

lemma reverse_nat_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ reverse_nat_pref) reverse_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix reverse_nat_pref v)\<rbrakk>
  \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma reverse_nat_IMP_Minus_correct_time:
  "(invoke_subprogram p reverse_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = reverse_nat_imp_time 0 (reverse_nat_imp_to_HOL_state p s)"
  by (fastforce elim: reverse_nat_acc_IMP_Minus_correct simp: reverse_nat_imp_to_HOL_state_def
      reverse_nat_imp_time.simps reverse_nat_acc_imp_to_HOL_state_def reverse_nat_IMP_Minus_def
      invoke_subprogram_append)

lemma reverse_nat_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) reverse_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (reverse_nat_imp_time 0 (reverse_nat_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) reverse_nat_ret_str) =
        reverse_nat_ret (reverse_nat_imp (reverse_nat_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using reverse_nat_IMP_Minus_correct_time reverse_nat_IMP_Minus_correct_function
    reverse_nat_IMP_Minus_correct_effects
  by (meson set_mono_prefix)


subsubsection \<open>append\<close>

paragraph \<open>append_acc\<close>

record append_state =
  append_acc::nat
  append_xs::nat

(*definition [prefix_defs]:*) abbreviation   "append_prefix \<equiv> ''append.''"
(*definition [prefix_defs]:*) abbreviation   "append_acc_str \<equiv> ''acc''"
(*definition [prefix_defs]:*) abbreviation   "append_xs_str \<equiv> ''xs''"

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
        ret"

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
  by (relation "Wellfounded.measure (\<lambda>s. append_xs s)")
    (auto simp: tl_imp_correct append_state_upd_def Let_def split: if_splits)

declare append_imp.simps [simp del]

lemma append_imp_correct[let_function_correctness]:
  "append_acc (append_imp s) = Primitives.append_acc (append_acc s) (append_xs s)"
  by (induction s rule: append_imp.induct, subst append_imp.simps)
    (simp, force simp add: append_state_upd_def cons_imp_correct hd_imp_correct tl_imp_correct
      gr0_conv_Suc split: if_splits)

function append_imp_time:: "nat \<Rightarrow> append_state \<Rightarrow> nat" where
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
  by (relation "Wellfounded.measure (\<lambda>(t,s). append_xs s)")
    (auto simp: tl_imp_correct append_state_upd_def Let_def split: if_splits)

lemmas [simp del] = append_imp_time.simps

lemma append_imp_time_acc: "(append_imp_time (Suc t) s) = Suc (append_imp_time t s)"
  by (induction t s rule: append_imp_time.induct)
    (subst (2) append_imp_time.simps, subst append_imp_time.simps, simp add: Let_def)

lemma append_imp_time_acc_2: "(append_imp_time x s) = x + (append_imp_time 0 s)"
  by (induction x) (simp add: append_imp_time_acc)+


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

abbreviation "append_IMP_vars \<equiv> {append_xs_str, append_acc_str}"

definition "append_imp_to_HOL_state p s =
  \<lparr>append_acc = (s (add_prefix p append_acc_str)), append_xs = (s (add_prefix p append_xs_str))\<rparr>"

lemma append_IMP_Minus_correct_function:
  "(invoke_subprogram p append_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p append_acc_str)
      = append_state.append_acc (append_imp (append_imp_to_HOL_state p s))"
  apply(induction "append_imp_to_HOL_state p s" arbitrary: s s' t rule: append_imp.induct)
  apply(subst append_imp.simps)
  apply(simp only: append_IMP_Minus_def prefix_simps)
  apply(erule While_tE, fastforce simp: append_imp_time_acc append_imp_to_HOL_state_def)
  apply(dest_com')
  apply(erule Seq_tE)+
  apply(erule tl_IMP_Minus_correct[where vars = append_IMP_vars], fastforce)
  apply(erule hd_IMP_Minus_correct[where vars = append_IMP_vars], fastforce)
  apply(erule cons_IMP_Minus_correct[where vars = append_IMP_vars], fastforce)
  by (fastforce simp add: append_state_upd_def append_imp_to_HOL_state_def append_imp_time_acc
      cons_imp_to_HOL_state_def hd_imp_to_HOL_state_def tl_imp_to_HOL_state_def Let_def)

lemma append_IMP_Minus_correct_time:
  "(invoke_subprogram p append_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = append_imp_time 0 (append_imp_to_HOL_state p s)"
  apply(induction "append_imp_to_HOL_state p s" arbitrary: s s' t rule: append_imp.induct)
  apply(subst append_imp_time.simps)
  apply(simp only: append_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps
      atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule While_tE, fastforce simp: append_imp_time_acc append_imp_to_HOL_state_def)
  apply(dest_com')
  apply(erule Seq_tE)+
  apply(erule tl_IMP_Minus_correct[where vars = append_IMP_vars], fastforce)
  apply(erule hd_IMP_Minus_correct[where vars = append_IMP_vars], fastforce)
  apply(erule cons_IMP_Minus_correct[where vars = append_IMP_vars], fastforce)
  apply(drule AssignD)+
  apply(elim conjE)
  apply(subst append_imp_time_acc_2)
  by(fastforce simp add: append_state_upd_def append_imp_to_HOL_state_def append_imp_time_acc
      cons_imp_to_HOL_state_def hd_imp_to_HOL_state_def tl_imp_to_HOL_state_def Let_def)

lemma append_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ append_pref) append_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> v \<in> vars \<Longrightarrow>
  \<not> (prefix append_pref v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma append_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) append_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (append_imp_time 0 (append_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) append_acc_str) =
        append_state.append_acc (append_imp (append_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using append_IMP_Minus_correct_time append_IMP_Minus_correct_function
    append_IMP_Minus_correct_effects
  by auto


paragraph \<open>append_nat\<close>

lemma append_nat_rev_acc:
  "append_nat xs ys = reverse_nat (Primitives.append_acc (reverse_nat xs) ys)"
proof-
  from append_induct
  have "reverse_nat (reverse_nat (append_nat xs ys))
        = reverse_nat (Primitives.append_acc (reverse_nat xs) ys)"
    by simp
  then show ?thesis using rev_rev_nat by fastforce
qed

record append_nat_state =
  append_nat_xs::nat
  append_nat_ys::nat
  append_nat_ret::nat

abbreviation "append_nat_prefix \<equiv> ''append_nat.''"
abbreviation "append_nat_xs_str \<equiv> ''xs''"
abbreviation "append_nat_ys_str \<equiv> ''ys''"
abbreviation "append_nat_ret_str \<equiv> ''ret''"

definition "append_nat_state_upd s \<equiv>
  (let
      reverse_nat_n' = append_nat_xs s;
      reverse_nat_ret' = 0;
      reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n', reverse_nat_ret = reverse_nat_ret'\<rparr>;
      reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;
      append_acc' = reverse_nat_ret reverse_nat_ret_state;
      append_xs' = append_nat_ys s;
      append_state = \<lparr>append_acc = append_acc', append_xs = append_xs'\<rparr>;
      append_ret_state = append_imp append_state;
      reverse_nat_n' = append_acc append_ret_state;
      reverse_nat_ret' = 0;
      reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n', reverse_nat_ret = reverse_nat_ret'\<rparr>;
      reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;
      append_nat_xs' = append_nat_xs s;
      append_nat_ys' = append_nat_ys s;
      append_nat_ret' = reverse_nat_ret reverse_nat_ret_state;
      ret = \<lparr>append_nat_xs = append_nat_xs',
             append_nat_ys = append_nat_ys',
             append_nat_ret = append_nat_ret' \<rparr>
    in
      ret
)"

function append_nat_imp:: "append_nat_state \<Rightarrow> append_nat_state" where
  "append_nat_imp s =
  (let
      ret = append_nat_state_upd s
    in
      ret
  )"
  by simp+
termination
  by (relation "measure (\<lambda>s. append_nat_ys s)") simp

lemmas [simp del] = append_nat_imp.simps

lemma append_nat_imp_correct[let_function_correctness]:
  "append_nat_ret (append_nat_imp s) = append_nat (append_nat_xs s) (append_nat_ys s)"
  by (simp add: append_nat_imp.simps reverse_nat_imp_correct append_imp_correct Let_def
      append_nat_state_upd_def append_nat_rev_acc)

function append_nat_imp_time:: "nat \<Rightarrow> append_nat_state \<Rightarrow> nat" where
  "append_nat_imp_time t s =
  (let
      reverse_nat_n' = append_nat_xs s;
      t = t + 2;
      reverse_nat_ret' = 0;
      t = t + 2;
      reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n', reverse_nat_ret = reverse_nat_ret'\<rparr>;
      reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;
      t = t + reverse_nat_imp_time 0 reverse_nat_state;
      append_acc' = reverse_nat_ret reverse_nat_ret_state;
      t = t + 2;
      append_xs' = append_nat_ys s;
      t = t + 2;
      append_state = \<lparr>append_acc = append_acc', append_xs = append_xs'\<rparr>;
      append_ret_state = append_imp append_state;
      t = t + append_imp_time 0 append_state;
      reverse_nat_n' = append_acc append_ret_state;
      t = t + 2;
      reverse_nat_ret' = 0;
      t = t + 2;
      reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n', reverse_nat_ret = reverse_nat_ret'\<rparr>;
      reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;
      t = t + reverse_nat_imp_time 0 reverse_nat_state;
      append_nat_xs' = append_nat_xs s;
      t = t + 2;
      append_nat_ys' = append_nat_ys s;
      t = t + 2;
      append_nat_ret' = reverse_nat_ret reverse_nat_ret_state;
      t = t + 2;
      ret = t
    in
      ret
  )"
  by auto
termination
  by (relation "measure (\<lambda>(t, s). append_nat_ys s)") simp

lemmas [simp del] = append_nat_imp_time.simps

lemma append_nat_imp_time_acc:
  "(append_nat_imp_time (Suc t) s) = Suc (append_nat_imp_time t s)"
  by (simp add: append_nat_imp_time.simps Let_def)

lemma append_nat_imp_time_acc_2:
  "(append_nat_imp_time x s) = x + (append_nat_imp_time 0 s)"
  by (simp add: append_nat_imp_time.simps Let_def)

definition append_nat_IMP_Minus where
  "append_nat_IMP_Minus \<equiv>
  \<comment> \<open>reverse_nat_n' = append_nat_xs s;\<close>
  (reverse_nat_prefix @ reverse_nat_n_str) ::= (A (V append_nat_xs_str));;
  \<comment> \<open>reverse_nat_ret' = 0;\<close>
  (reverse_nat_prefix @ reverse_nat_ret_str) ::= (A (N 0));;
  \<comment> \<open>reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n', reverse_nat_ret = reverse_nat_ret'\<rparr>;\<close>
  \<comment> \<open>reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;\<close>
  invoke_subprogram reverse_nat_prefix reverse_nat_IMP_Minus;;
  \<comment> \<open>append_acc' = reverse_nat_ret reverse_nat_ret_state;\<close>
  (append_prefix @ append_acc_str) ::= (A (V (reverse_nat_prefix @ reverse_nat_ret_str)));;
  \<comment> \<open>append_xs' = append_nat_ys s;\<close>
  (append_prefix @ append_xs_str) ::= (A (V append_nat_ys_str));;
  \<comment> \<open>append_state = \<lparr>append_acc = append_acc', append_xs = append_xs'\<rparr>;\<close>
  \<comment> \<open>append_ret_state = append_imp append_state;\<close>
  invoke_subprogram append_prefix append_IMP_Minus;;
  \<comment> \<open>reverse_nat_n' = append_acc append_ret_state;\<close>
  (reverse_nat_prefix @ reverse_nat_n_str) ::= (A (V (append_prefix @ append_acc_str)));;
  \<comment> \<open>reverse_nat_ret' = 0;\<close>
  (reverse_nat_prefix @ reverse_nat_ret_str) ::= (A (N 0));;
  \<comment> \<open>reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n', reverse_nat_ret = reverse_nat_ret'\<rparr>;\<close>
  \<comment> \<open>reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;\<close>
  invoke_subprogram reverse_nat_prefix reverse_nat_IMP_Minus;;
  \<comment> \<open>append_nat_xs' = append_nat_xs s;\<close>
  append_nat_xs_str ::= (A (V append_nat_xs_str));;
  \<comment> \<open>append_nat_ys' = append_nat_ys s;\<close>
  append_nat_ys_str ::= (A (V append_nat_ys_str));;
  \<comment> \<open>append_nat_ret' = reverse_nat_ret reverse_nat_ret_state;\<close>
  append_nat_ret_str ::= (A (V (reverse_nat_prefix @ reverse_nat_ret_str)))
"

abbreviation
  "append_nat_IMP_vars \<equiv>
  {append_nat_xs_str, append_nat_ys_str, append_nat_ret_str}"

definition "append_nat_imp_to_HOL_state p s =
  \<lparr>append_nat_xs = (s (add_prefix p append_nat_xs_str)),
   append_nat_ys = (s (add_prefix p append_nat_ys_str)),
   append_nat_ret = (s (add_prefix p append_nat_ret_str))\<rparr>"

lemma append_nat_IMP_Minus_correct_function:
  "(invoke_subprogram p append_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p append_nat_ret_str)
      = append_nat_ret (append_nat_imp (append_nat_imp_to_HOL_state p s))"
  apply (simp add: append_nat_IMP_Minus_def invoke_subprogram_append)
  apply(vcg append_nat_IMP_vars functional_correctness: append_IMP_Minus_correct)
  by (fastforce simp add: append_nat_imp_to_HOL_state_def append_nat_imp.simps
      append_nat_state_upd_def append_imp_to_HOL_state_def reverse_nat_imp_to_HOL_state_def)

lemma append_nat_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ append_nat_pref) append_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix append_nat_pref v)\<rbrakk>
  \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma append_nat_IMP_Minus_correct_time:
  "(invoke_subprogram p append_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = append_nat_imp_time 0 (append_nat_imp_to_HOL_state p s)"
  apply (simp add: append_nat_IMP_Minus_def invoke_subprogram_append)
  apply(vcg_time append_nat_IMP_vars functional_correctness: append_IMP_Minus_correct)
  by (fastforce simp add: append_nat_imp_to_HOL_state_def append_nat_imp_time.simps Let_def
      append_imp_to_HOL_state_def reverse_nat_imp_to_HOL_state_def)

lemma append_nat_IMP_Minus_correct[functional_correctness]:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) append_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (append_nat_imp_time 0 (append_nat_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) append_nat_ret_str) =
        append_nat_ret (append_nat_imp (append_nat_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using append_nat_IMP_Minus_correct_time append_nat_IMP_Minus_correct_function
    append_nat_IMP_Minus_correct_effects
  by (meson set_mono_prefix)


subsubsection \<open>list_from\<close>

paragraph \<open>list_from_acc\<close>

record list_from_acc_state =
  list_from_acc_acc::nat
  list_from_acc_s::nat
  list_from_acc_n::nat
  list_from_acc_ret::nat

abbreviation "list_from_acc_prefix \<equiv> ''list_from_acc.''"
abbreviation "list_from_acc_acc_str \<equiv> ''acc''"
abbreviation "list_from_acc_s_str \<equiv> ''s''"
abbreviation "list_from_acc_n_str \<equiv> ''n''"
abbreviation "list_from_acc_ret_str \<equiv> ''ret''"

definition "list_from_acc_state_upd s \<equiv>
  (let
      cons_h' = list_from_acc_s s;
      cons_t' = list_from_acc_acc s;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      list_from_acc_s' = list_from_acc_s s + 1;
      list_from_acc_n' = list_from_acc_n s - 1;
      list_from_acc_acc' = cons_ret cons_ret_state;
      list_from_acc_ret' = 0;
      ret = \<lparr>list_from_acc_acc = list_from_acc_acc',
              list_from_acc_s = list_from_acc_s',
             list_from_acc_n = list_from_acc_n',
             list_from_acc_ret = list_from_acc_ret' \<rparr>
    in
      ret
      
)"

definition "list_from_acc_imp_compute_loop_condition s \<equiv>
  (let
    condition = list_from_acc_n s
   in condition
  )"

definition "list_from_acc_imp_after_loop s \<equiv>
  (let
    ret = \<lparr>list_from_acc_acc = list_from_acc_acc s,
           list_from_acc_s = list_from_acc_s s,
           list_from_acc_n = list_from_acc_n s,
          list_from_acc_ret = list_from_acc_acc s\<rparr>
   in ret
  )"

lemmas list_from_acc_imp_subprogram_simps =
  list_from_acc_imp_after_loop_def
  list_from_acc_state_upd_def
  list_from_acc_imp_compute_loop_condition_def

function list_from_acc_imp:: "list_from_acc_state \<Rightarrow> list_from_acc_state" where
  "list_from_acc_imp s =
  (if list_from_acc_imp_compute_loop_condition s \<noteq> 0
    then
      (let next_iteration = list_from_acc_imp (list_from_acc_state_upd s)
      in
        next_iteration)
    else 
      (let ret = list_from_acc_imp_after_loop s in ret)
    )"
  by simp+
termination
  apply (relation "measure (\<lambda>s. list_from_acc_n s)")
  by (auto simp add: list_from_acc_imp_subprogram_simps)

declare list_from_acc_imp.simps [simp del]

lemma list_from_acc_imp_correct[let_function_correctness]:
  "list_from_acc_ret (list_from_acc_imp s) =
   list_from_acc (list_from_acc_acc s) (list_from_acc_s s) (list_from_acc_n s)"
  apply(induction s rule: list_from_acc_imp.induct)
  by (simp add: cons_imp_correct list_from_acc_imp_subprogram_simps list_from_acc_imp.simps)

definition "list_from_acc_state_upd_time t s \<equiv> (
  let
      cons_h' = list_from_acc_s s;
    t = t + 2;
      cons_t' = list_from_acc_acc s;
    t = t + 2;
      cons_ret' = 0;
    t = t + 2;
      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;
      list_from_acc_s' = list_from_acc_s s + 1;
    t = t + 2;
      list_from_acc_n' = list_from_acc_n s - 1;
    t = t + 2;
      list_from_acc_acc' = cons_ret cons_ret_state;
    t = t + 2;
      list_from_acc_ret' = 0;
    t = t + 2;
      ret = \<lparr>list_from_acc_acc = list_from_acc_acc',
              list_from_acc_s = list_from_acc_s',
             list_from_acc_n = list_from_acc_n',
             list_from_acc_ret = list_from_acc_ret' \<rparr>
    in
    t
)"

    
definition "list_from_acc_imp_compute_loop_condition_time t s \<equiv>
  (let
    condition = list_from_acc_n s;
    t = t + 2
  in
    t)
"

definition "list_from_acc_imp_after_loop_time t s \<equiv>
  let
    ret = \<lparr>list_from_acc_acc = list_from_acc_acc s,
           list_from_acc_s = list_from_acc_s s,
           list_from_acc_n = list_from_acc_n s,
          list_from_acc_ret = list_from_acc_acc s\<rparr>;
    t = t + 2
  in
    t
"

lemmas list_from_acc_imp_subprogram_time_simps = 
  list_from_acc_state_upd_time_def
  list_from_acc_imp_compute_loop_condition_time_def
  list_from_acc_imp_after_loop_time_def
  list_from_acc_imp_subprogram_simps

function list_from_acc_imp_time::
  "nat \<Rightarrow> list_from_acc_state \<Rightarrow> nat" where
  "list_from_acc_imp_time t s =
  list_from_acc_imp_compute_loop_condition_time 0 s +
  (if list_from_acc_imp_compute_loop_condition s \<noteq> 0
    then
      (let
        t = t + 1;
        next_iteration =
          list_from_acc_imp_time (t + list_from_acc_state_upd_time 0 s)
                         (list_from_acc_state_upd s)
       in next_iteration)
    else
      (let
        t = t + 2;
        ret = t + list_from_acc_imp_after_loop_time 0 s
       in ret)
  )"
  by auto
termination
  apply (relation "measure (\<lambda>(t, s). list_from_acc_n s)")
  by (simp add: list_from_acc_imp_subprogram_time_simps)+

declare list_from_acc_imp_time.simps [simp del]            

lemma list_from_acc_imp_time_acc:
  "(list_from_acc_imp_time (Suc t) s) = Suc (list_from_acc_imp_time t s)"
  by (induction t s rule: list_from_acc_imp_time.induct)
    ((subst (1 2) list_from_acc_imp_time.simps);
      (simp add: list_from_acc_state_upd_def))            

lemma list_from_acc_imp_time_acc_2_aux:
  "(list_from_acc_imp_time t s) = t + (list_from_acc_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: list_from_acc_imp_time_acc)+            

lemma list_from_acc_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (list_from_acc_imp_time t s) = t + (list_from_acc_imp_time 0 s)"
  by (rule list_from_acc_imp_time_acc_2_aux)            

lemma list_from_acc_imp_time_acc_3:
  "(list_from_acc_imp_time (a + b) s) = a + (list_from_acc_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: list_from_acc_imp_time_acc)+            

abbreviation "list_from_acc_while_cond \<equiv> ''condition''"

definition "list_from_acc_IMP_init_while_cond \<equiv>
  \<comment> \<open>condition = list_from_acc_n s\<close>
  list_from_acc_while_cond ::= A (V list_from_acc_n_str)
"

definition "list_from_acc_IMP_loop_body \<equiv>
  \<comment> \<open>  cons_h' = list_from_acc_s s;\<close>
  (cons_prefix @ cons_h_str) ::= A (V list_from_acc_s_str);;
  \<comment> \<open>  cons_t' = list_from_acc_acc s;\<close>
  (cons_prefix @ cons_t_str) ::= A (V list_from_acc_acc_str);;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  list_from_acc_s' = list_from_acc_s s + 1;\<close>
  list_from_acc_s_str ::= Plus (V list_from_acc_s_str) (N 1);;
  \<comment> \<open>  list_from_acc_n' = list_from_acc_n s - 1;\<close>
  list_from_acc_n_str ::= Sub (V list_from_acc_n_str) (N 1);;
  \<comment> \<open>  list_from_acc_acc' = cons_ret cons_ret_state;\<close>
  list_from_acc_acc_str ::= A (V (cons_prefix @ cons_ret_str));;
  \<comment> \<open>  list_from_acc_ret' = 0;\<close>
  list_from_acc_ret_str ::= A (N 0)
  \<comment> \<open>  ret = \<lparr>list_from_acc_acc = list_from_acc_acc',\<close>
  \<comment> \<open>          list_from_acc_s = list_from_acc_s',\<close>
  \<comment> \<open>         list_from_acc_n = list_from_acc_n',\<close>
  \<comment> \<open>         list_from_acc_ret = list_from_acc_ret' \<rparr>\<close>
"

definition "list_from_acc_IMP_after_loop \<equiv>
  \<comment> \<open>ret = \<lparr>list_from_acc_acc = list_from_acc_acc s,\<close>
  \<comment> \<open>       list_from_acc_s = list_from_acc_s s,\<close>
  \<comment> \<open>       list_from_acc_n = list_from_acc_n s,\<close>
  \<comment> \<open>      list_from_acc_ret = list_from_acc_acc s\<rparr>\<close>
  list_from_acc_ret_str ::= A (V (list_from_acc_acc_str))
"

definition list_from_acc_IMP_Minus where
  "list_from_acc_IMP_Minus \<equiv>
  list_from_acc_IMP_init_while_cond;;
  WHILE list_from_acc_while_cond \<noteq>0 DO (
    list_from_acc_IMP_loop_body;;
    list_from_acc_IMP_init_while_cond
  );;
  list_from_acc_IMP_after_loop"

abbreviation "list_from_acc_IMP_vars\<equiv>
  {list_from_acc_while_cond, list_from_acc_s_str, list_from_acc_n_str,
  list_from_acc_acc_str, list_from_acc_ret_str}"

lemmas list_from_acc_IMP_subprogram_simps =
  list_from_acc_IMP_init_while_cond_def
  list_from_acc_IMP_loop_body_def
  list_from_acc_IMP_after_loop_def

definition "list_from_acc_imp_to_HOL_state p s =
  \<lparr>list_from_acc_acc = (s (add_prefix p list_from_acc_acc_str)),
   list_from_acc_s = (s (add_prefix p list_from_acc_s_str)),
   list_from_acc_n = (s (add_prefix p list_from_acc_n_str)),
   list_from_acc_ret = (s (add_prefix p list_from_acc_ret_str))\<rparr>"

lemmas list_from_acc_state_translators =
  list_from_acc_imp_to_HOL_state_def

lemmas list_from_acc_complete_simps =
  list_from_acc_IMP_subprogram_simps
  list_from_acc_imp_subprogram_simps
  list_from_acc_state_translators

lemma list_from_acc_IMP_Minus_correct_function:
  "(invoke_subprogram p list_from_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p list_from_acc_ret_str)
      = list_from_acc_ret
          (list_from_acc_imp (list_from_acc_imp_to_HOL_state p s))"
  apply(induction "list_from_acc_imp_to_HOL_state p s" arbitrary: s s' t
    rule: list_from_acc_imp.induct)
  apply(subst list_from_acc_imp.simps)
  apply(simp only: list_from_acc_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule While_tE)

  subgoal
    apply(simp only: list_from_acc_IMP_subprogram_simps prefix_simps)
    by(fastforce simp: list_from_acc_IMP_subprogram_simps
        list_from_acc_imp_subprogram_simps
        list_from_acc_state_translators)

  apply(erule Seq_E)+
  apply(dest_com_gen)

  subgoal
      apply(simp only: list_from_acc_IMP_init_while_cond_def prefix_simps)
      by(fastforce simp add: list_from_acc_complete_simps)

  subgoal
      apply(subst (asm) list_from_acc_IMP_init_while_cond_def)
      apply(simp only: list_from_acc_IMP_loop_body_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule cons_IMP_Minus_correct[where vars = "list_from_acc_IMP_vars"])
    subgoal premises p using p(13) by fastforce
      apply (simp only: list_from_acc_imp_subprogram_simps list_from_acc_IMP_subprogram_simps
          list_from_acc_state_translators Let_def cons_imp_correct list_from_acc_state.simps
          cons_state.simps prefix_simps cons_imp_to_HOL_state_def)
    by force

  subgoal
      apply(simp only: list_from_acc_IMP_init_while_cond_def prefix_simps
          list_from_acc_IMP_loop_body_def)
      apply(erule Seq_E)+
      apply(erule cons_IMP_Minus_correct[where vars = "list_from_acc_IMP_vars"])
      subgoal premises p using p(13) by fastforce
      apply (simp only:  list_from_acc_state.simps
          list_from_acc_state_translators Let_def cons_imp_to_HOL_state_def 
           cons_state.simps cons_imp_correct list_from_acc_imp_subprogram_simps)
      apply (clarsimp)
      subgoal premises p using p(4)
        by (smt (z3) fun_upd_other list.discI remove_nth.simps(2) same_append_eq)
      done        
done

lemma list_from_acc_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ list_from_acc_pref) list_from_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix list_from_acc_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemmas list_from_acc_complete_time_simps =
  list_from_acc_imp_subprogram_time_simps
  list_from_acc_imp_time_acc
  list_from_acc_imp_time_acc_2
  list_from_acc_imp_time_acc_3
  list_from_acc_state_translators

lemma list_from_acc_IMP_Minus_correct_time:
  "(invoke_subprogram p list_from_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = list_from_acc_imp_time 0 (list_from_acc_imp_to_HOL_state p s)"
  apply(induction "list_from_acc_imp_to_HOL_state p s" arbitrary: s s' t
      rule: list_from_acc_imp.induct)
  apply(subst list_from_acc_imp_time.simps)
  apply(simp only: list_from_acc_IMP_Minus_def prefix_simps)

  apply(erule Seq_tE)+
  apply(erule While_tE_time)

  subgoal
    apply(simp only: list_from_acc_IMP_subprogram_simps prefix_simps
    list_from_acc_complete_time_simps Let_def cons_imp_correct
             list_from_acc_state.simps cons_state.simps cons_IMP_Minus_correct_time)
    by(clarsimp)

  apply(erule Seq_tE)+
  apply(simp add: add.assoc)
  apply(dest_com_gen_time)

  subgoal
    apply(simp only: list_from_acc_IMP_init_while_cond_def prefix_simps)
    by(fastforce simp add: list_from_acc_complete_simps)

  subgoal
    apply(subst (asm) list_from_acc_IMP_init_while_cond_def)
    apply(simp only: list_from_acc_IMP_loop_body_def prefix_simps)
    apply(erule Seq_tE)+
    apply(erule cons_IMP_Minus_correct[where vars = "list_from_acc_IMP_vars"])
    subgoal premises p using p(23) by fastforce
    apply (simp only: list_from_acc_imp_subprogram_time_simps
          list_from_acc_state_translators Let_def cons_imp_correct list_from_acc_state.simps
          cons_state.simps prefix_simps cons_imp_to_HOL_state_def )
    apply (clarsimp)
    subgoal premises p using p(9)
      by (smt (z3) fun_upd_other list.simps(3) p(10) remove_nth.simps(2) same_append_eq)
    done

  
  subgoal
    apply(simp only: prefix_simps list_from_acc_IMP_init_while_cond_def
        list_from_acc_IMP_loop_body_def)
    apply(erule Seq_tE)+
    apply(erule cons_IMP_Minus_correct[where vars = "list_from_acc_IMP_vars"])
    subgoal premises p using p(23) by fastforce
    apply(simp only: list_from_acc_complete_time_simps Let_def 
           cons_imp_correct list_from_acc_state.simps
          cons_state.simps prefix_simps cons_imp_to_HOL_state_def 
          cons_IMP_Minus_correct_time)
    apply(clarsimp)
    subgoal premises p using p(9)[of list_from_acc_n_str] p(9)[of list_from_acc_s_str]
      by fastforce
    done

  done        

lemma list_from_acc_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) list_from_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (list_from_acc_imp_time 0 (list_from_acc_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) list_from_acc_ret_str) =
          list_from_acc_ret (list_from_acc_imp
                                        (list_from_acc_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using list_from_acc_IMP_Minus_correct_function list_from_acc_IMP_Minus_correct_effects
    list_from_acc_IMP_Minus_correct_time
  by (meson set_mono_prefix)

paragraph \<open>list_from_tail\<close>

record list_from_tail_state =
  list_from_tail_s::nat
  list_from_tail_n::nat
  list_from_tail_ret::nat

abbreviation "list_from_tail_prefix \<equiv> ''list_from_tail.''"
abbreviation "list_from_tail_s_str \<equiv> ''s''"
abbreviation "list_from_tail_n_str \<equiv> ''n''"
abbreviation "list_from_tail_ret_str \<equiv> ''ret''"

definition "list_from_tail_state_upd s \<equiv>
  (let
      list_from_acc_acc' = 0;
      list_from_acc_s' = list_from_tail_s s;
      list_from_acc_n' = list_from_tail_n s;
      list_from_acc_ret' = 0;
      list_from_acc_state = \<lparr>list_from_acc_acc = list_from_acc_acc',
                             list_from_acc_s = list_from_acc_s',
                             list_from_acc_n = list_from_acc_n',
                             list_from_acc_ret = list_from_acc_ret'\<rparr>;
      list_from_acc_ret_state = list_from_acc_imp list_from_acc_state;
      reverse_nat_n' = list_from_acc_ret list_from_acc_ret_state;
      reverse_nat_ret' = 0;
      reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n',
                           reverse_nat_ret = reverse_nat_ret'\<rparr>;
      reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;
      list_from_tail_s' = list_from_tail_s s;
      list_from_tail_n' = list_from_tail_n s;
      list_from_tail_ret' = reverse_nat_ret reverse_nat_ret_state;
      ret = \<lparr>list_from_tail_s = list_from_tail_s',
             list_from_tail_n = list_from_tail_n',
             list_from_tail_ret = list_from_tail_ret'\<rparr>
    in
      ret
)"

function list_from_tail_imp:: "list_from_tail_state \<Rightarrow> list_from_tail_state" where
  "list_from_tail_imp s =
  (let
      ret = list_from_tail_state_upd s
    in
      ret
  )"
  by simp+
termination
  by (relation "measure (\<lambda>s. list_from_tail_n s)") simp

declare list_from_tail_imp.simps [simp del]

lemma list_from_tail_imp_correct[let_function_correctness]:
  "list_from_tail_ret (list_from_tail_imp s) = 
    list_from_tail (list_from_tail_s s) (list_from_tail_n s)"
  by (simp add: list_from_tail_imp.simps reverse_nat_imp_correct
      list_from_acc_imp_correct list_from_tail_def Let_def
      list_from_tail_state_upd_def)

function list_from_tail_imp_time:: "nat \<Rightarrow> list_from_tail_state \<Rightarrow> nat" where
  "list_from_tail_imp_time t s =
  (let
      list_from_acc_acc' = 0;
      t = t + 2;
      list_from_acc_s' = list_from_tail_s s;
      t = t + 2;
      list_from_acc_n' = list_from_tail_n s;
      t = t + 2;
      list_from_acc_ret' = 0;
      t = t + 2;
      list_from_acc_state = \<lparr>list_from_acc_acc = list_from_acc_acc',
                             list_from_acc_s = list_from_acc_s',
                             list_from_acc_n = list_from_acc_n',
                             list_from_acc_ret = list_from_acc_ret'\<rparr>;
      list_from_acc_ret_state = list_from_acc_imp list_from_acc_state;
      t = t + list_from_acc_imp_time 0 list_from_acc_state;
      reverse_nat_n' = list_from_acc_ret list_from_acc_ret_state;
      t = t + 2;
      reverse_nat_ret' = 0;
      t = t + 2;
      reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n',
                           reverse_nat_ret = reverse_nat_ret'\<rparr>;
      reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;
      t = t + reverse_nat_imp_time 0 reverse_nat_state;
      list_from_tail_s' = list_from_tail_s s;
      t = t + 2;
      list_from_tail_n' = list_from_tail_n s;
      t = t + 2;
      list_from_tail_ret' = reverse_nat_ret reverse_nat_ret_state;
      t = t + 2;
      ret = \<lparr>list_from_tail_s = list_from_tail_s',
             list_from_tail_n = list_from_tail_n',
             list_from_tail_ret = list_from_tail_ret'\<rparr>
    in
      t
  )"
  by auto
termination
  by (relation "measure (\<lambda>(t, s). list_from_tail_n s)") simp

declare list_from_tail_imp_time.simps [simp del]

lemma list_from_tail_imp_time_acc:
  "(list_from_tail_imp_time (Suc t) s) = Suc (list_from_tail_imp_time t s)"
  by (induction t s rule: list_from_tail_imp_time.induct)
    ((subst (1 2) list_from_tail_imp_time.simps);
      (simp add: list_from_tail_state_upd_def Let_def))      

lemma list_from_tail_imp_time_acc_2_aux:
  "(list_from_tail_imp_time t s) = t + (list_from_tail_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: list_from_tail_imp_time_acc)+            

lemma list_from_tail_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (list_from_tail_imp_time t s) = t + (list_from_tail_imp_time 0 s)"
  by (rule list_from_tail_imp_time_acc_2_aux)            

lemma list_from_tail_imp_time_acc_3:
  "(list_from_tail_imp_time (a + b) s) = a + (list_from_tail_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: list_from_tail_imp_time_acc)+   

definition list_from_tail_IMP_Minus where
  "list_from_tail_IMP_Minus \<equiv> 
  \<comment> \<open>  list_from_acc_acc' = 0;\<close>
  (list_from_acc_prefix @ list_from_acc_acc_str) ::= (A (N 0));;
  \<comment> \<open>  list_from_acc_s' = list_from_tail_s s;\<close>
  (list_from_acc_prefix @ list_from_acc_s_str) ::= (A (V list_from_tail_s_str));;
  \<comment> \<open>  list_from_acc_n' = list_from_tail_n s;\<close>
  (list_from_acc_prefix @ list_from_acc_n_str) ::= (A (V list_from_tail_n_str));;
  \<comment> \<open>  list_from_acc_ret' = 0;\<close>
  (list_from_acc_prefix @ list_from_acc_ret_str) ::= (A (N 0));;
  \<comment> \<open>  list_from_acc_state = \<lparr>list_from_acc_acc = list_from_acc_acc',\<close>
  \<comment> \<open>                         list_from_acc_s = list_from_acc_s',\<close>
  \<comment> \<open>                         list_from_acc_n = list_from_acc_n',\<close>
  \<comment> \<open>                         list_from_acc_ret = list_from_acc_ret'\<rparr>;\<close>
  \<comment> \<open>  list_from_acc_ret_state = list_from_acc_imp list_from_acc_state;\<close>
  invoke_subprogram list_from_acc_prefix list_from_acc_IMP_Minus;;
  \<comment> \<open>  reverse_nat_n' = list_from_acc_ret list_from_acc_ret_state;\<close>
  (reverse_nat_prefix @ reverse_nat_n_str) ::= (A (V (list_from_acc_prefix @ list_from_acc_ret_str)));;
  \<comment> \<open>  reverse_nat_ret' = 0;\<close>
  (reverse_nat_prefix @ reverse_nat_ret_str) ::= (A (N 0));;
  \<comment> \<open>  reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n',\<close>
  \<comment> \<open>                       reverse_nat_ret = reverse_nat_ret'\<rparr>;\<close>
  \<comment> \<open>  reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;\<close>
  invoke_subprogram reverse_nat_prefix reverse_nat_IMP_Minus;;
  \<comment> \<open>  list_from_tail_s' = list_from_tail_s s;\<close>
  list_from_tail_s_str ::= (A (V list_from_tail_s_str));;
  \<comment> \<open>  list_from_tail_n' = list_from_tail_n s;\<close>
  list_from_tail_n_str ::= (A (V list_from_tail_n_str));;
  \<comment> \<open>  list_from_tail_ret' = reverse_nat_ret reverse_nat_ret_state;\<close>
  list_from_tail_ret_str ::= (A (V (reverse_nat_prefix @ reverse_nat_ret_str)))
  \<comment> \<open>  ret = \<lparr>list_from_tail_s = list_from_tail_s',\<close>
  \<comment> \<open>         list_from_tail_n = list_from_tail_n',\<close>
  \<comment> \<open>         list_from_tail_ret = list_from_tail_ret'\<rparr>\<close>
"

abbreviation
  "list_from_tail_IMP_vars \<equiv>
  {list_from_tail_s_str, list_from_tail_n_str, list_from_tail_ret_str}"

definition "list_from_tail_imp_to_HOL_state p s =
  \<lparr>list_from_tail_s = (s (add_prefix p list_from_tail_s_str)),
   list_from_tail_n = (s (add_prefix p list_from_tail_n_str)),
   list_from_tail_ret = (s (add_prefix p list_from_tail_ret_str))\<rparr>"

lemmas list_from_tail_state_translators =
  list_from_tail_imp_to_HOL_state_def
  list_from_acc_imp_to_HOL_state_def
  reverse_nat_imp_to_HOL_state_def    

lemma list_from_tail_IMP_Minus_correct_function:
  "(invoke_subprogram p list_from_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p list_from_tail_ret_str)
      = list_from_tail_ret
          (list_from_tail_imp (list_from_tail_imp_to_HOL_state p s))"
  by (fastforce elim: list_from_acc_IMP_Minus_correct reverse_nat_IMP_Minus_correct
      simp: list_from_tail_imp_to_HOL_state_def
      list_from_tail_imp.simps list_from_tail_state_upd_def 
      reverse_nat_imp_to_HOL_state_def
      list_from_acc_imp_to_HOL_state_def
      list_from_tail_IMP_Minus_def invoke_subprogram_append)

lemma list_from_tail_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ list_from_tail_pref) list_from_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix list_from_tail_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast   

lemma list_from_tail_IMP_Minus_correct_time:
  "(invoke_subprogram p list_from_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = list_from_tail_imp_time 0 (list_from_tail_imp_to_HOL_state p s)"
  apply(simp only: list_from_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule list_from_acc_IMP_Minus_correct[where vars=list_from_tail_IMP_vars])
  subgoal premises p using p(21) by fastforce
  apply(erule reverse_nat_IMP_Minus_correct[where vars=list_from_tail_IMP_vars])
  subgoal premises p using p(23) by fastforce
  by (fastforce simp: Let_def list_from_tail_state_translators
      list_from_tail_imp_time.simps list_from_tail_state_upd_def)

lemma list_from_tail_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) list_from_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (list_from_tail_imp_time 0 (list_from_tail_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) list_from_tail_ret_str) =
          list_from_tail_ret (list_from_tail_imp
                                        (list_from_tail_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using list_from_tail_IMP_Minus_correct_function list_from_tail_IMP_Minus_correct_time
  by (meson list_from_tail_IMP_Minus_correct_effects set_mono_prefix)

subsubsection \<open>list_less\<close>

paragraph \<open>list_less_tail\<close>

record list_less_tail_state =
  list_less_tail_n::nat
  list_less_tail_ret::nat

abbreviation "list_less_tail_prefix \<equiv> ''list_less_tail.''"
abbreviation "list_less_tail_n_str \<equiv> ''n''"
abbreviation "list_less_tail_ret_str \<equiv> ''ret''"

definition "list_less_tail_state_upd s \<equiv>
  (let
      list_from_tail_s' = 0;
      list_from_tail_n' = list_less_tail_n s;
      list_from_tail_ret' = 0;
      list_from_tail_state = \<lparr>list_from_tail_s = list_from_tail_s',
                              list_from_tail_n = list_from_tail_n',
                              list_from_tail_ret = list_from_tail_ret'\<rparr>;
      list_from_tail_ret_state = list_from_tail_imp list_from_tail_state;
      list_less_tail_n' = list_less_tail_n s;
      list_less_tail_ret' = list_from_tail_ret list_from_tail_ret_state;
      ret = \<lparr>list_less_tail_n = list_less_tail_n',
             list_less_tail_ret = list_less_tail_ret'\<rparr>
    in
      ret
)"

function list_less_tail_imp:: "list_less_tail_state \<Rightarrow> list_less_tail_state" where
  "list_less_tail_imp s =
  (let
      ret = list_less_tail_state_upd s
    in
      ret
  )"
  by simp+
termination
  by (relation "measure (\<lambda>s. list_less_tail_n s)") simp

declare list_less_tail_imp.simps [simp del]

lemma list_less_tail_imp_correct[let_function_correctness]:
  "list_less_tail_ret (list_less_tail_imp s) =
    list_less_tail (list_less_tail_n s)"
  by (simp add: list_less_tail_imp.simps 
      list_from_tail_imp_correct list_less_tail_def Let_def
      list_less_tail_state_upd_def)

function list_less_tail_imp_time :: "nat \<Rightarrow> list_less_tail_state \<Rightarrow> nat" where
  "list_less_tail_imp_time t s = 
  (let
      list_from_tail_s' = 0;
      t = t + 2;
      list_from_tail_n' = list_less_tail_n s;
      t = t + 2;
      list_from_tail_ret' = 0;
      t = t + 2;
      list_from_tail_state = \<lparr>list_from_tail_s = list_from_tail_s',
                              list_from_tail_n = list_from_tail_n',
                              list_from_tail_ret = list_from_tail_ret'\<rparr>;
      list_from_tail_ret_state = list_from_tail_imp list_from_tail_state;
      t = t + list_from_tail_imp_time 0 list_from_tail_state;
      list_less_tail_n' = list_less_tail_n s;
      t = t + 2;
      list_less_tail_ret' = list_from_tail_ret list_from_tail_ret_state;
      t = t + 2;
      ret = \<lparr>list_less_tail_n = list_less_tail_n',
             list_less_tail_ret = list_less_tail_ret'\<rparr>
    in
      t
  )"
  by auto
termination
  by (relation "measure (\<lambda>(t, s). list_less_tail_n s)") simp

declare list_less_tail_imp_time.simps [simp del]

lemma list_less_tail_imp_time_acc:
  "(list_less_tail_imp_time (Suc t) s) = Suc (list_less_tail_imp_time t s)"
  by (induction t s rule: list_less_tail_imp_time.induct)
    ((subst (1 2) list_less_tail_imp_time.simps);
      (simp add: list_less_tail_state_upd_def))            

lemma list_less_tail_imp_time_acc_2_aux:
  "(list_less_tail_imp_time t s) = t + (list_less_tail_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: list_less_tail_imp_time_acc)+            

lemma list_less_tail_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (list_less_tail_imp_time t s) = t + (list_less_tail_imp_time 0 s)"
  by (rule list_less_tail_imp_time_acc_2_aux)            

lemma list_less_tail_imp_time_acc_3:
  "(list_less_tail_imp_time (a + b) s) = a + (list_less_tail_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: list_less_tail_imp_time_acc)+ 

definition list_less_tail_IMP_Minus where
  "list_less_tail_IMP_Minus \<equiv> 
  \<comment> \<open>  list_from_tail_s' = 0;\<close>
  (list_from_tail_prefix @ list_from_tail_s_str) ::= (A (N 0));;
  \<comment> \<open>  list_from_tail_n' = list_less_tail_n s;\<close>
  (list_from_tail_prefix @ list_from_tail_n_str) ::= (A (V list_less_tail_n_str));;
  \<comment> \<open>  list_from_tail_ret' = 0;\<close>
  (list_from_tail_prefix @ list_from_tail_ret_str) ::= (A (N 0));;
  \<comment> \<open>  list_from_tail_state = \<lparr>list_from_tail_s = list_from_tail_s',\<close>
  \<comment> \<open>                          list_from_tail_n = list_from_tail_n',\<close>
  \<comment> \<open>                          list_from_tail_ret = list_from_tail_ret'\<rparr>;\<close>
  \<comment> \<open>  list_from_tail_ret_state = list_from_tail_imp list_from_tail_state;\<close>
  invoke_subprogram list_from_tail_prefix list_from_tail_IMP_Minus;;
  \<comment> \<open>  list_less_tail_n' = list_less_tail_n s;\<close>
  list_less_tail_n_str ::= (A (V list_less_tail_n_str));;
  \<comment> \<open>  list_less_tail_ret' = list_from_tail_ret list_from_tail_ret_state;\<close>
  list_less_tail_ret_str ::= (A (V (list_from_tail_prefix @ list_from_tail_ret_str)))
  \<comment> \<open>  ret = \<lparr>list_less_tail_n = list_less_tail_n',\<close>
  \<comment> \<open>         list_less_tail_ret = list_less_tail_ret'\<rparr>\<close>
"

abbreviation "list_less_tail_IMP_vars \<equiv>
  {list_less_tail_n_str, list_less_tail_ret_str}"

definition "list_less_tail_imp_to_HOL_state p s =
  \<lparr>list_less_tail_n = (s (add_prefix p list_less_tail_n_str)),
   list_less_tail_ret = (s (add_prefix p list_less_tail_ret_str))\<rparr>"

lemmas list_less_tail_state_translators =
  list_less_tail_imp_to_HOL_state_def
  list_from_tail_imp_to_HOL_state_def 

lemma list_less_tail_IMP_Minus_correct_function:
  "(invoke_subprogram p list_less_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p list_less_tail_ret_str)
      = list_less_tail_ret
          (list_less_tail_imp (list_less_tail_imp_to_HOL_state p s))"
  apply(simp only: list_less_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule list_from_tail_IMP_Minus_correct[where vars=list_less_tail_IMP_vars])
  subgoal premises p using p(6) by fastforce
  by (fastforce simp: list_less_tail_state_translators list_less_tail_imp.simps
      list_less_tail_state_upd_def)

lemma list_less_tail_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ list_less_tail_pref) list_less_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix list_less_tail_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemma list_less_tail_IMP_Minus_correct_time:
  "(invoke_subprogram p list_less_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = list_less_tail_imp_time 0 (list_less_tail_imp_to_HOL_state p s)"
  apply(simp only: list_less_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule list_from_tail_IMP_Minus_correct[where vars=list_less_tail_IMP_vars])
  subgoal premises p using p(11) by fastforce
  by (fastforce simp: list_less_tail_state_translators Let_def
      list_less_tail_imp_time.simps list_less_tail_state_upd_def)

lemma list_less_tail_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) list_less_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (list_less_tail_imp_time 0 (list_less_tail_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) list_less_tail_ret_str) =
          list_less_tail_ret (list_less_tail_imp
                                        (list_less_tail_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using list_less_tail_IMP_Minus_correct_function list_less_tail_IMP_Minus_correct_time
  by (meson list_less_tail_IMP_Minus_correct_effects set_mono_prefix)

subsubsection \<open>concat\<close>

paragraph \<open>concat_acc\<close>

record concat_acc_state =
  concat_acc_acc::nat
  concat_acc_n::nat
  concat_acc_ret::nat

abbreviation "concat_acc_prefix \<equiv> ''concat_acc.''"
abbreviation "concat_acc_acc_str \<equiv> ''acc''"
abbreviation "concat_acc_n_str \<equiv> ''n''"
abbreviation "concat_acc_ret_str \<equiv> ''ret''"

definition "concat_acc_state_upd s \<equiv>
  (let
      hd_xs' = concat_acc_n s;
      hd_ret' = 0;
      hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
      hd_ret_state = hd_imp hd_state;
      reverse_nat_n' = hd_ret hd_ret_state;
      reverse_nat_ret' = 0;
      reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n',
                           reverse_nat_ret = reverse_nat_ret'\<rparr>;
      reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;
      append_nat_xs' = reverse_nat_ret reverse_nat_ret_state;
      append_nat_ys' = concat_acc_acc s;
      append_nat_ret' = 0;
      append_nat_state = \<lparr>append_nat_xs = append_nat_xs',
                          append_nat_ys = append_nat_ys',
                          append_nat_ret = append_nat_ret'\<rparr>;
      append_nat_ret_state = append_nat_imp append_nat_state;
      concat_acc_acc' = append_nat_ret append_nat_ret_state;
      tl_xs' = concat_acc_n s;
      tl_ret' = 0;
      tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
      tl_ret_state = tl_imp tl_state;
      concat_acc_n' = tl_ret tl_ret_state;
      concat_acc_ret' = 0;
      ret = \<lparr>concat_acc_acc = concat_acc_acc',
             concat_acc_n = concat_acc_n',
             concat_acc_ret = concat_acc_ret'\<rparr>
    in
      ret
)"

definition "concat_acc_imp_compute_loop_condition s \<equiv> (
  let 
    condition = concat_acc_n s
  in 
    condition
)"

definition "concat_acc_imp_after_loop s \<equiv>
  (let
     ret = \<lparr>concat_acc_acc = concat_acc_acc s,
         concat_acc_n = concat_acc_n s,
         concat_acc_ret = concat_acc_acc s\<rparr>
  in
    ret
)"

lemmas concat_acc_imp_subprogram_simps = 
  concat_acc_state_upd_def
  concat_acc_imp_compute_loop_condition_def
  concat_acc_imp_after_loop_def

function concat_acc_imp::
  "concat_acc_state \<Rightarrow> concat_acc_state" where
  "concat_acc_imp s =
  (if concat_acc_imp_compute_loop_condition s \<noteq> 0
   then
    let next_iteration = concat_acc_imp (concat_acc_state_upd s)
    in next_iteration
   else
    let ret = concat_acc_imp_after_loop s
    in ret
  )"
  by simp+
termination
  apply (relation "measure (\<lambda>s. concat_acc_n s)")
  by (simp add: concat_acc_imp_subprogram_simps tl_imp_correct)+
 

declare concat_acc_imp.simps [simp del]

lemma concat_acc_imp_correct[let_function_correctness]:
  "concat_acc_ret (concat_acc_imp s) =
    concat_acc (concat_acc_acc s) (concat_acc_n s)"
  apply (induction s rule: concat_acc_imp.induct)
  apply (subst concat_acc_imp.simps)
  apply (subst concat_acc.simps)
  apply (simp del: concat_acc.simps add: concat_acc_imp_subprogram_simps 
        Let_def tl_imp_correct hd_imp_correct append_nat_imp_correct
        reverse_nat_imp_correct)
  using subtail_append by presburger

definition "concat_acc_state_upd_time t s \<equiv> (
  let
      hd_xs' = concat_acc_n s;
      t = t + 2;
      hd_ret' = 0;
      t = t + 2;
      hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
      hd_ret_state = hd_imp hd_state;
      t = t + hd_imp_time 0 hd_state;
      reverse_nat_n' = hd_ret hd_ret_state;
      t = t + 2;
      reverse_nat_ret' = 0;
      t = t + 2;
      reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n',
                           reverse_nat_ret = reverse_nat_ret'\<rparr>;
      reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;
      t = t + reverse_nat_imp_time 0 reverse_nat_state;
      append_nat_xs' = reverse_nat_ret reverse_nat_ret_state;
      t = t + 2;
      append_nat_ys' = concat_acc_acc s;
      t = t + 2;
      append_nat_ret' = 0;
      t = t + 2;
      append_nat_state = \<lparr>append_nat_xs = append_nat_xs',
                          append_nat_ys = append_nat_ys',
                          append_nat_ret = append_nat_ret'\<rparr>;
      append_nat_ret_state = append_nat_imp append_nat_state;
      t = t + append_nat_imp_time 0 append_nat_state;
      concat_acc_acc' = append_nat_ret append_nat_ret_state;
      t = t + 2;
      tl_xs' = concat_acc_n s;
      t = t + 2;
      tl_ret' = 0;
      t = t + 2;
      tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
      tl_ret_state = tl_imp tl_state;
      t = t + tl_imp_time 0 tl_state;
      concat_acc_n' = tl_ret tl_ret_state;
      t = t + 2;
      concat_acc_ret' = 0;
      t = t + 2;
      ret = \<lparr>concat_acc_acc = concat_acc_acc',
             concat_acc_n = concat_acc_n',
             concat_acc_ret = concat_acc_ret'\<rparr>
    in
      t
)"

definition "concat_acc_imp_compute_loop_condition_time t s \<equiv> 
  (let 
    condition = concat_acc_n s;
    t = t + 2
  in
    t)
"

definition "concat_acc_imp_after_loop_time t s \<equiv> (
  let
    ret = \<lparr>concat_acc_acc = concat_acc_acc s,
          concat_acc_n = concat_acc_n s,
          concat_acc_ret = concat_acc_acc s\<rparr>;
    t = t + 2
  in
    t)
"


lemmas concat_acc_imp_subprogram_time_simps = 
  concat_acc_state_upd_time_def
  concat_acc_imp_compute_loop_condition_time_def
  concat_acc_imp_after_loop_time_def
  concat_acc_imp_subprogram_simps

function concat_acc_imp_time::
  "nat \<Rightarrow> concat_acc_state \<Rightarrow> nat" where
  "concat_acc_imp_time t s =
  concat_acc_imp_compute_loop_condition_time 0 s +
  (if concat_acc_imp_compute_loop_condition s \<noteq> 0
    then
      (let
        t = t + 1;
        next_iteration =
          concat_acc_imp_time (t + concat_acc_state_upd_time 0 s)
                         (concat_acc_state_upd s)
       in next_iteration)
    else
      (let
        t = t + 2;
        ret = t + concat_acc_imp_after_loop_time 0 s
       in ret)
  )"
  by auto
termination
  apply (relation "measure (\<lambda>(t, s). concat_acc_n s)")
   by (simp add: concat_acc_imp_subprogram_simps tl_imp_correct)+

declare concat_acc_imp_time.simps [simp del]            

lemma concat_acc_imp_time_acc:
  "(concat_acc_imp_time (Suc t) s) = Suc (concat_acc_imp_time t s)"
  by (induction t s rule: concat_acc_imp_time.induct)
    ((subst (1 2) concat_acc_imp_time.simps);
      (simp add: concat_acc_state_upd_def))            

lemma concat_acc_imp_time_acc_2_aux:
  "(concat_acc_imp_time t s) = t + (concat_acc_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: concat_acc_imp_time_acc)+            

lemma concat_acc_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (concat_acc_imp_time t s) = t + (concat_acc_imp_time 0 s)"
  by (rule concat_acc_imp_time_acc_2_aux)            

lemma concat_acc_imp_time_acc_3:
  "(concat_acc_imp_time (a + b) s) = a + (concat_acc_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: concat_acc_imp_time_acc)+            

abbreviation "concat_acc_while_cond \<equiv> ''condition''"

definition "concat_acc_IMP_init_while_cond \<equiv>
  \<comment> \<open>condition = concat_acc_n s\<close>
  concat_acc_while_cond ::= A (V concat_acc_n_str)
"

definition "concat_acc_IMP_loop_body \<equiv>
 \<comment> \<open>hd_xs' = concat_acc_n s;\<close>
  (hd_prefix @ hd_xs_str) ::= A (V concat_acc_n_str);;
  \<comment> \<open>hd_ret' = 0;\<close>
  (hd_prefix @ hd_ret_str) ::= A (N 0);;
      \<comment> \<open>hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;\<close>
      \<comment> \<open> hd_ret_state = hd_imp hd_state;\<close>

  invoke_subprogram hd_prefix hd_IMP_Minus;;
       \<comment> \<open>reverse_nat_n' = hd_ret hd_ret_state;\<close>
  (reverse_nat_prefix @ reverse_nat_n_str) ::= A (V (hd_prefix @ hd_ret_str));;
       \<comment> \<open>reverse_nat_ret' = 0;\<close>
  (reverse_nat_prefix @ reverse_nat_ret_str) ::= A (N 0);;
       \<comment> \<open>reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n',
                           reverse_nat_ret = reverse_nat_ret'\<rparr>;\<close>
       \<comment> \<open>reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;\<close>
  invoke_subprogram reverse_nat_prefix reverse_nat_IMP_Minus;;
       \<comment> \<open>append_nat_xs' = reverse_nat_ret reverse_nat_ret_state;\<close>
  (append_nat_prefix @ append_nat_xs_str) ::= A (V (reverse_nat_prefix @ reverse_nat_ret_str));;
       \<comment> \<open>append_nat_ys' = concat_acc_acc s;\<close>
  (append_nat_prefix @ append_nat_ys_str) ::= A (V concat_acc_acc_str);;
       \<comment> \<open>append_nat_ret' = 0;\<close>
  (append_nat_prefix @ append_nat_ret_str) ::= A (N 0);;
       \<comment> \<open>append_nat_state = \<lparr>append_nat_xs = append_nat_xs',
                          append_nat_ys = append_nat_ys',
                          append_nat_ret = append_nat_ret'\<rparr>;\<close>
       \<comment> \<open>append_nat_ret_state = append_nat_imp append_nat_state;\<close>
  invoke_subprogram append_nat_prefix append_nat_IMP_Minus;;
  \<comment> \<open>concat_acc_acc' = append_nat_ret append_nat_ret_state;\<close>
  concat_acc_acc_str ::= A (V (append_nat_prefix @ append_nat_ret_str));;
       \<comment> \<open>tl_xs' = concat_acc_n s;\<close>     
  (tl_prefix @ tl_xs_str) ::= A (V concat_acc_n_str);;
       \<comment> \<open>tl_ret' = 0;\<close>
  (tl_prefix @ tl_ret_str) ::= A (N 0);;
       \<comment> \<open>tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;\<close>
       \<comment> \<open>tl_ret_state = tl_imp tl_state;\<close>
  invoke_subprogram tl_prefix tl_IMP_Minus;;
       \<comment> \<open>concat_acc_n' = tl_ret tl_ret_state;\<close>
  concat_acc_n_str ::= A (V (tl_prefix @ tl_ret_str));;
  concat_acc_ret_str ::= A (N 0)
       \<comment> \<open>ret = \<lparr>concat_acc_acc = concat_acc_acc',
             concat_acc_n = concat_acc_n',
             concat_acc_ret = concat_acc_ret'\<rparr>\<close>
"

definition "concat_acc_IMP_after_loop \<equiv> 
              concat_acc_ret_str ::= A (V concat_acc_acc_str)"

definition "concat_acc_IMP_Minus \<equiv>
              concat_acc_IMP_init_while_cond;;
              WHILE concat_acc_while_cond \<noteq>0 DO (
                concat_acc_IMP_loop_body;;
                concat_acc_IMP_init_while_cond
              );;
              concat_acc_IMP_after_loop
            "
abbreviation "concat_acc_IMP_vars \<equiv>
  {concat_acc_while_cond, concat_acc_acc_str, concat_acc_n_str,
  concat_acc_ret_str}"

lemmas concat_acc_IMP_subprogram_simps = 
  concat_acc_IMP_init_while_cond_def
  concat_acc_IMP_loop_body_def
  concat_acc_IMP_after_loop_def

definition "concat_acc_imp_to_HOL_state p s = 
  \<lparr>concat_acc_acc = (s (add_prefix p concat_acc_acc_str)),
  concat_acc_n = (s (add_prefix p concat_acc_n_str)),
  concat_acc_ret = (s (add_prefix p concat_acc_ret_str))\<rparr>"

lemmas concat_acc_state_translators =
  concat_acc_imp_to_HOL_state_def

lemmas concat_acc_complete_simps =
  concat_acc_IMP_subprogram_simps
  concat_acc_imp_subprogram_simps
  concat_acc_state_translators

lemma concat_acc_IMP_Minus_correct_function:
  "(invoke_subprogram p concat_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p concat_acc_ret_str)
      = concat_acc_ret
          (concat_acc_imp (concat_acc_imp_to_HOL_state p s))"
  
  apply(induction "concat_acc_imp_to_HOL_state p s" arbitrary: s s' t
    rule: concat_acc_imp.induct)
  apply(subst concat_acc_imp.simps)
  apply(simp only: concat_acc_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply(erule While_tE)

  subgoal
    apply(simp only: concat_acc_IMP_subprogram_simps prefix_simps)
    by(fastforce simp: concat_acc_complete_simps)

  apply(erule Seq_E)+
  apply(dest_com_gen)
    subgoal
     apply(simp only: concat_acc_IMP_init_while_cond_def prefix_simps)
      by(fastforce simp add: concat_acc_complete_simps)
    subgoal
       apply(subst (asm) concat_acc_IMP_init_while_cond_def)
       apply(simp only: concat_acc_IMP_loop_body_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule hd_IMP_Minus_correct[where vars = "concat_acc_IMP_vars"])
      subgoal premises p using p(23) by fastforce
      apply(erule reverse_nat_IMP_Minus_correct[where vars = "concat_acc_IMP_vars"])
      subgoal premises p using p(25) by fastforce
      apply(erule append_nat_IMP_Minus_correct[where vars = "concat_acc_IMP_vars"])
      subgoal premises p using p(27) by fastforce
      apply(erule tl_IMP_Minus_correct[where vars = "concat_acc_IMP_vars"])
      subgoal premises p using p(29) by fastforce
      apply (simp only: concat_acc_imp_subprogram_simps
          concat_acc_state_translators Let_def prefix_simps
      concat_acc_state.simps
      append_nat_imp_to_HOL_state_def append_nat_imp_correct append_nat_state.simps
      hd_imp_to_HOL_state_def hd_imp_correct hd_state.simps
      tl_imp_to_HOL_state_def tl_imp_correct tl_state.simps
      reverse_nat_imp_to_HOL_state_def reverse_nat_imp_correct reverse_nat_state.simps)
      by force
    subgoal 
       apply(simp only: concat_acc_IMP_init_while_cond_def prefix_simps
          concat_acc_IMP_loop_body_def)
      apply(erule Seq_E)+
      apply(erule hd_IMP_Minus_correct[where vars = "concat_acc_IMP_vars"])
      subgoal premises p using p(23) by fastforce
      apply(erule reverse_nat_IMP_Minus_correct[where vars = "concat_acc_IMP_vars"])
      subgoal premises p using p(25) by fastforce
      apply(erule append_nat_IMP_Minus_correct[where vars = "concat_acc_IMP_vars"])
      subgoal premises p using p(27) by fastforce
      apply(erule tl_IMP_Minus_correct[where vars = "concat_acc_IMP_vars"])
      subgoal premises p using p(29) by fastforce
      apply (simp only: concat_acc_imp_subprogram_simps
          concat_acc_state_translators Let_def prefix_simps
      concat_acc_state.simps
      append_nat_imp_to_HOL_state_def append_nat_imp_correct append_nat_state.simps
      hd_imp_to_HOL_state_def hd_imp_correct hd_state.simps
      tl_imp_to_HOL_state_def tl_imp_correct tl_state.simps
      reverse_nat_imp_to_HOL_state_def reverse_nat_imp_correct reverse_nat_state.simps)
      apply clarsimp
      subgoal premises p using p(6) p(10) p(12) p(8)
      by (smt (z3) fun_upd_other fun_upd_same list.inject list.simps(3) same_append_eq) 
      done
    done


lemma concat_acc_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ concat_acc_pref) concat_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix concat_acc_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemmas concat_acc_complete_time_simps =
  concat_acc_imp_subprogram_time_simps
  concat_acc_imp_time_acc
  concat_acc_imp_time_acc_2
  concat_acc_imp_time_acc_3
  concat_acc_state_translators

lemma concat_acc_IMP_Minus_correct_time:
  "(invoke_subprogram p concat_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = concat_acc_imp_time 0 (concat_acc_imp_to_HOL_state p s)"
  apply(induction "concat_acc_imp_to_HOL_state p s" arbitrary: s s' t
      rule: concat_acc_imp.induct)
  apply(subst concat_acc_imp_time.simps)
  apply(simp only: concat_acc_IMP_Minus_def prefix_simps)

  apply(erule Seq_tE)+
  apply(erule While_tE_time)

  subgoal
    apply(simp only: concat_acc_IMP_subprogram_simps prefix_simps)
    by (force simp: concat_acc_IMP_subprogram_simps
        concat_acc_imp_subprogram_time_simps concat_acc_state_translators)

  apply(erule Seq_tE)+
  apply(simp add: add.assoc)
  apply(dest_com_gen_time)

  subgoal
    apply(simp only: concat_acc_IMP_init_while_cond_def prefix_simps)
    by(fastforce simp add: concat_acc_complete_simps)

  subgoal
    apply(subst (asm) concat_acc_IMP_init_while_cond_def)
       apply(simp only: concat_acc_IMP_loop_body_def prefix_simps)
      apply(erule Seq_tE)+
      apply(erule hd_IMP_Minus_correct[where vars = "concat_acc_IMP_vars"])
      subgoal premises p using p(39) by fastforce
      apply(erule reverse_nat_IMP_Minus_correct[where vars = "concat_acc_IMP_vars"])
      subgoal premises p using p(41) by fastforce
      apply(erule append_nat_IMP_Minus_correct[where vars = "concat_acc_IMP_vars"])
      subgoal premises p using p(43) by fastforce
      apply(erule tl_IMP_Minus_correct[where vars = "concat_acc_IMP_vars"])
      subgoal premises p using p(45) by fastforce
      apply (simp only: concat_acc_imp_subprogram_simps
          concat_acc_state_translators Let_def prefix_simps
      concat_acc_state.simps
      append_nat_imp_to_HOL_state_def append_nat_imp_correct append_nat_state.simps
      hd_imp_to_HOL_state_def hd_imp_correct hd_state.simps
      tl_imp_to_HOL_state_def tl_imp_correct tl_state.simps
      reverse_nat_imp_to_HOL_state_def reverse_nat_imp_correct reverse_nat_state.simps)
      by force
  subgoal
    apply(simp only: prefix_simps concat_acc_IMP_init_while_cond_def
          concat_acc_IMP_loop_body_def) 
      apply(erule Seq_tE)+ 
      apply(erule hd_IMP_Minus_correct[where vars = "concat_acc_IMP_vars"])
      subgoal premises p using p(39) by fastforce
      apply(erule reverse_nat_IMP_Minus_correct[where vars = "concat_acc_IMP_vars"])
      subgoal premises p using p(41) by fastforce
      apply(erule append_nat_IMP_Minus_correct[where vars = "concat_acc_IMP_vars"])
      subgoal premises p using p(43) by fastforce
      apply(erule tl_IMP_Minus_correct[where vars = "concat_acc_IMP_vars"])
      subgoal premises p using p(45) by fastforce
      apply (simp only: concat_acc_complete_time_simps 
       Let_def prefix_simps
      concat_acc_state.simps 
      append_nat_imp_to_HOL_state_def append_nat_imp_correct append_nat_state.simps
      append_nat_IMP_Minus_correct_time
      hd_imp_to_HOL_state_def hd_imp_correct hd_state.simps hd_IMP_Minus_correct_time
      tl_imp_to_HOL_state_def tl_imp_correct tl_state.simps tl_IMP_Minus_correct_time
      reverse_nat_imp_to_HOL_state_def reverse_nat_imp_correct reverse_nat_state.simps
      reverse_nat_IMP_Minus_correct_time
      )
      apply clarsimp
      subgoal premises p
              by (smt (z3) fun_upd_other fun_upd_same list.inject 
              list.simps(3) p(11) p(13) p(15) p(9) same_append_eq)
      done
    done

lemma concat_acc_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) concat_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (concat_acc_imp_time 0 (concat_acc_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) concat_acc_ret_str) =
          concat_acc_ret (concat_acc_imp
                                        (concat_acc_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using concat_acc_IMP_Minus_correct_function
  by (auto simp: concat_acc_IMP_Minus_correct_time)
    (meson concat_acc_IMP_Minus_correct_effects set_mono_prefix) 

subsubsection \<open>nth\<close>
paragraph nth_nat

record nth_nat_state =
nth_nat_n::nat
nth_nat_x::nat
nth_nat_ret::nat

abbreviation "nth_nat_prefix \<equiv> ''nth_nat.''"
abbreviation "nth_nat_n_str \<equiv> ''n''"
abbreviation "nth_nat_x_str \<equiv> ''x''"
abbreviation "nth_nat_ret_str \<equiv> ''ret''"

definition "nth_nat_state_upd s \<equiv> 
  (let 
     tl_xs' = nth_nat_x s;
     tl_ret' = 0;
     tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
     tl_ret_state = tl_imp tl_state;
     nth_nat_n' = nth_nat_n s - 1;
     nth_nat_x' = tl_ret tl_ret_state;
     nth_nat_ret' = 0;
     ret = \<lparr>nth_nat_n = nth_nat_n',
           nth_nat_x = nth_nat_x',
           nth_nat_ret = nth_nat_ret'\<rparr>
     in
     ret
  )"

definition "nth_nat_imp_compute_loop_condition s \<equiv>
  (
    let 
      condition = nth_nat_n s
    in 
      condition
  )"

definition "nth_nat_imp_after_loop s \<equiv>
  (
    let
      hd_xs' = nth_nat_x s;
      hd_ret' = 0;
      hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
      hd_ret_state = hd_imp hd_state;
      nth_nat_ret' = hd_ret hd_ret_state;
      ret = \<lparr>nth_nat_n = nth_nat_n s,
            nth_nat_x = nth_nat_x s,
            nth_nat_ret = nth_nat_ret'\<rparr>
    in
      ret
  )"

lemmas nth_nat_imp_subprogram_simps = 
  nth_nat_state_upd_def
  nth_nat_imp_compute_loop_condition_def
  nth_nat_imp_after_loop_def

function nth_nat_imp::
  "nth_nat_state \<Rightarrow> nth_nat_state" where
  "nth_nat_imp s =
  (if nth_nat_imp_compute_loop_condition s \<noteq> 0
   then
    let next_iteration = nth_nat_imp (nth_nat_state_upd s)
    in next_iteration
   else
    let ret = nth_nat_imp_after_loop s
    in ret
  )"
  by simp+
termination
  apply (relation "measure (\<lambda>s. nth_nat_n s)")
  apply (simp add: nth_nat_imp_subprogram_simps)+
  done

declare nth_nat_imp.simps [simp del]

lemma nth_nat_imp_correct:
  "nth_nat_ret (nth_nat_imp s) =
    nth_nat (nth_nat_n s) (nth_nat_x s)"
  apply (induction s rule: nth_nat_imp.induct)
  apply (subst nth_nat_imp.simps)
  apply (simp del: nth_nat.simps add: nth_nat_imp_subprogram_simps Let_def hd_imp_correct
  tl_imp_correct) 
  using gr0_conv_Suc by fastforce 

definition "nth_nat_state_upd_time t s \<equiv>
  (let
     tl_xs' = nth_nat_x s;
     t = t + 2;
     tl_ret' = 0;
     t = t + 2;
     tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
     tl_ret_state = tl_imp tl_state;
     t = t + tl_imp_time 0 tl_state;
     nth_nat_n' = nth_nat_n s - 1;
     t = t + 2;
     nth_nat_x' = tl_ret tl_ret_state;
     t = t + 2;
     nth_nat_ret' = 0;
     t = t + 2;
     ret = \<lparr>nth_nat_n = nth_nat_n',
           nth_nat_x = nth_nat_x',
           nth_nat_ret = nth_nat_ret'\<rparr>
     in
     t
  )"


definition "nth_nat_imp_compute_loop_condition_time t s \<equiv>
  (let
      condition = nth_nat_n s;
      t = t + 2
  in
    t)
"

definition "nth_nat_imp_after_loop_time t s \<equiv>
  (let
     hd_xs' = nth_nat_x s;
     t = t + 2;
     hd_ret' = 0;
     t = t + 2;
     hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
     hd_ret_state = hd_imp hd_state;
     t = t + hd_imp_time 0 hd_state;
     nth_nat_ret' = hd_ret hd_ret_state;
     t = t + 2;
     ret = \<lparr>nth_nat_n = nth_nat_n s,
            nth_nat_x = nth_nat_x s,
            nth_nat_ret = nth_nat_ret'\<rparr>
    in
      t
  )
"

lemmas nth_nat_imp_subprogram_time_simps = 
  nth_nat_state_upd_time_def
  nth_nat_imp_compute_loop_condition_time_def
  nth_nat_imp_after_loop_time_def
  nth_nat_imp_subprogram_simps

function nth_nat_imp_time::
  "nat \<Rightarrow> nth_nat_state \<Rightarrow> nat" where
  "nth_nat_imp_time t s =
  nth_nat_imp_compute_loop_condition_time 0 s +
  (if nth_nat_imp_compute_loop_condition s \<noteq> 0
    then
      (let
        t = t + 1;
        next_iteration =
          nth_nat_imp_time (t + nth_nat_state_upd_time 0 s)
                         (nth_nat_state_upd s)
       in next_iteration)
    else
      (let
        t = t + 2;
        ret = t + nth_nat_imp_after_loop_time 0 s
       in ret)
  )"
  by auto
termination
  apply (relation "measure (\<lambda>(t, s). nth_nat_n s)")
  by (simp add: nth_nat_imp_subprogram_time_simps)+

declare nth_nat_imp_time.simps [simp del]            

lemma nth_nat_imp_time_acc:
  "(nth_nat_imp_time (Suc t) s) = Suc (nth_nat_imp_time t s)"
  by (induction t s rule: nth_nat_imp_time.induct)
    ((subst (1 2) nth_nat_imp_time.simps);
      (simp add: nth_nat_state_upd_def))            

lemma nth_nat_imp_time_acc_2_aux:
  "(nth_nat_imp_time t s) = t + (nth_nat_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: nth_nat_imp_time_acc)+            

lemma nth_nat_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (nth_nat_imp_time t s) = t + (nth_nat_imp_time 0 s)"
  by (rule nth_nat_imp_time_acc_2_aux)            

lemma nth_nat_imp_time_acc_3:
  "(nth_nat_imp_time (a + b) s) = a + (nth_nat_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: nth_nat_imp_time_acc)+            

abbreviation "nth_nat_while_cond \<equiv> ''condition''"

definition "nth_nat_IMP_init_while_cond \<equiv>
  \<comment> \<open>let \<close>
  \<comment> \<open>  condition = nth_nat_n s\<close>
  nth_nat_while_cond ::= A (V nth_nat_n_str)
"

definition "nth_nat_IMP_loop_body \<equiv>
  \<comment> \<open> tl_xs' = nth_nat_x s;\<close>
  (tl_prefix @ tl_xs_str) ::= A (V nth_nat_x_str);;
  \<comment> \<open> tl_ret' = 0;\<close>
  (tl_prefix @ tl_ret_str) ::= A (N 0);;
  \<comment> \<open> tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;\<close>
  \<comment> \<open> tl_ret_state = tl_imp tl_state;\<close>
  invoke_subprogram tl_prefix tl_IMP_Minus;;
  \<comment> \<open> nth_nat_n' = nth_nat_n s - 1;\<close>
  nth_nat_n_str ::= Sub (V nth_nat_n_str) (N 1);;
  \<comment> \<open> nth_nat_x' = tl_ret tl_ret_state;\<close>
  nth_nat_x_str ::= A (V (tl_prefix @ tl_ret_str));;
  \<comment> \<open> nth_nat_ret' = 0;\<close>
  nth_nat_ret_str ::= A (N 0)
  \<comment> \<open> ret = \<lparr>nth_nat_n = nth_nat_n',\<close>
  \<comment> \<open>       nth_nat_x = nth_nat_x',\<close>
  \<comment> \<open>       nth_nat_ret = nth_nat_ret'\<rparr>\<close>
  \<comment> \<open> in\<close>
  \<comment> \<open> ret\<close>
"

definition "nth_nat_IMP_after_loop \<equiv>
  \<comment>\<open>hd_xs' = nth_nat_x s;\<close>
  (hd_prefix @ hd_xs_str) ::= A (V nth_nat_x_str);;
  \<comment>\<open>hd_ret' = 0;\<close>
  (hd_prefix @ hd_ret_str) ::= A (N 0);;
  \<comment>\<open>hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
      hd_ret_state = hd_imp hd_state;\<close>
  invoke_subprogram hd_prefix hd_IMP_Minus;;
  \<comment>\<open>nth_nat_ret' = hd_ret hd_ret_state;\<close>
  \<comment>\<open>ret = \<lparr>nth_nat_n = nth_nat_n s,
            nth_nat_x = nth_nat_x s,
            nth_nat_ret = nth_nat_ret'\<rparr>\<close>
  nth_nat_ret_str ::= A (V (hd_prefix @ hd_ret_str))
"

definition nth_nat_IMP_Minus where
  "nth_nat_IMP_Minus \<equiv>
  nth_nat_IMP_init_while_cond;;
  WHILE nth_nat_while_cond \<noteq>0 DO (
    nth_nat_IMP_loop_body;;
    nth_nat_IMP_init_while_cond
  );;
  nth_nat_IMP_after_loop"

abbreviation "nth_nat_IMP_vars\<equiv>
  {nth_nat_while_cond, nth_nat_n_str, nth_nat_x_str, nth_nat_ret_str}"

lemmas nth_nat_IMP_subprogram_simps =
  nth_nat_IMP_init_while_cond_def
  nth_nat_IMP_loop_body_def
  nth_nat_IMP_after_loop_def

definition "nth_nat_imp_to_HOL_state p s =
  \<lparr>nth_nat_n = (s (add_prefix p nth_nat_n_str)),
   nth_nat_x = (s (add_prefix p nth_nat_x_str)),
   nth_nat_ret = (s (add_prefix p nth_nat_ret_str))\<rparr>"

lemmas nth_nat_state_translators =
  nth_nat_imp_to_HOL_state_def

lemmas nth_nat_complete_simps =
  nth_nat_IMP_subprogram_simps
  nth_nat_imp_subprogram_simps
  nth_nat_state_translators

lemma nth_nat_IMP_Minus_correct_function:
  "(invoke_subprogram p nth_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p nth_nat_ret_str)
      = nth_nat_ret
          (nth_nat_imp (nth_nat_imp_to_HOL_state p s))"
  apply(induction "nth_nat_imp_to_HOL_state p s" arbitrary: s s' t
    rule: nth_nat_imp.induct)
  apply(subst nth_nat_imp.simps)
  apply(simp only: nth_nat_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule While_tE)

  subgoal
    apply(simp only: nth_nat_IMP_subprogram_simps prefix_simps)
    apply(erule Seq_E)+
    apply(erule hd_IMP_Minus_correct[where vars = "nth_nat_IMP_vars"])
    subgoal premises p using p(9) by fastforce
    apply (simp only: nth_nat_imp_subprogram_simps
          nth_nat_state_translators Let_def prefix_simps
          hd_imp_correct hd_state.simps hd_imp_to_HOL_state_def
          )
      by force
    

  apply(erule Seq_E)+
  apply(dest_com_gen)

  subgoal
      apply(simp only: nth_nat_IMP_init_while_cond_def prefix_simps)
      by(fastforce simp add: nth_nat_complete_simps)

  subgoal
      apply(subst (asm) nth_nat_IMP_init_while_cond_def)
      apply(simp only: nth_nat_IMP_loop_body_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule tl_IMP_Minus_correct[where vars = "nth_nat_IMP_vars"])
      subgoal premises p using p(11) by fastforce
      apply (simp only: nth_nat_imp_subprogram_simps
          nth_nat_state_translators Let_def prefix_simps
          tl_imp_correct tl_state.simps tl_imp_to_HOL_state_def
          )
      by force

  subgoal
      apply(simp only: nth_nat_IMP_init_while_cond_def prefix_simps
          nth_nat_IMP_loop_body_def)
      apply(erule Seq_E)+
      apply(erule tl_IMP_Minus_correct[where vars = "nth_nat_IMP_vars"])
      subgoal premises p using p(11) by fastforce
      apply (simp only: nth_nat_imp_subprogram_simps
          nth_nat_state_translators Let_def prefix_simps
          tl_imp_correct tl_state.simps tl_imp_to_HOL_state_def
          )
      by force
  done        

lemma nth_nat_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ nth_nat_pref) nth_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix nth_nat_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemmas nth_nat_complete_time_simps =
  nth_nat_imp_subprogram_time_simps
  nth_nat_imp_time_acc
  nth_nat_imp_time_acc_2
  nth_nat_imp_time_acc_3
  nth_nat_state_translators

lemma nth_nat_IMP_Minus_correct_time:
  "(invoke_subprogram p nth_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = nth_nat_imp_time 0 (nth_nat_imp_to_HOL_state p s)"
  apply(induction "nth_nat_imp_to_HOL_state p s" arbitrary: s s' t
      rule: nth_nat_imp.induct)
  apply(subst nth_nat_imp_time.simps)
  apply(simp only: nth_nat_IMP_Minus_def prefix_simps)

  apply(erule Seq_tE)+
  apply(erule While_tE_time)

  subgoal
    apply(simp only: nth_nat_IMP_subprogram_simps prefix_simps)
    apply(erule Seq_tE)+
    apply(erule hd_IMP_Minus_correct[where vars = "nth_nat_IMP_vars"])
    subgoal premises p using p(14) by fastforce
    apply (simp only: nth_nat_complete_time_simps Let_def prefix_simps
    hd_imp_correct hd_state.simps hd_imp_to_HOL_state_def hd_IMP_Minus_correct_time) 
   by force

  apply(erule Seq_tE)+
  apply(simp add: add.assoc)
  apply(dest_com_gen_time)

  subgoal
    apply(simp only: nth_nat_IMP_init_while_cond_def prefix_simps)
    by(fastforce simp add: nth_nat_complete_simps)

  subgoal
    apply(subst (asm) nth_nat_IMP_init_while_cond_def)
    apply(simp only: nth_nat_IMP_loop_body_def prefix_simps)
    apply(erule Seq_tE)+
    apply(erule tl_IMP_Minus_correct[where vars = "nth_nat_IMP_vars"])
    subgoal premises p using p(19) by fastforce
    apply (simp only: nth_nat_imp_subprogram_simps
          nth_nat_state_translators Let_def prefix_simps
          tl_imp_correct tl_state.simps tl_imp_to_HOL_state_def
          ) 
    by force

  subgoal
    apply(simp only: prefix_simps nth_nat_IMP_init_while_cond_def
        nth_nat_IMP_loop_body_def)
    apply(erule Seq_tE)+
    apply(erule tl_IMP_Minus_correct[where vars = "nth_nat_IMP_vars"])
    subgoal premises p using p(19) by fastforce
    apply (simp only: nth_nat_complete_time_simps nth_nat_state.simps Let_def prefix_simps
          tl_imp_correct tl_state.simps tl_imp_to_HOL_state_def
          tl_IMP_Minus_correct_time
          )
    by force

done        

lemma nth_nat_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) nth_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (nth_nat_imp_time 0 (nth_nat_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) nth_nat_ret_str) =
          nth_nat_ret (nth_nat_imp
                                        (nth_nat_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using nth_nat_IMP_Minus_correct_function
  by (auto simp: nth_nat_IMP_Minus_correct_time)
    (meson nth_nat_IMP_Minus_correct_effects set_mono_prefix)


subsubsection \<open>elemof\<close>

fun elemof' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"elemof' e l = 
  (if l \<noteq> 0 \<and> hd_nat l \<noteq> e
  then elemof' e (tl_nat l)
  else (if l \<noteq> 0
       then 1
       else 0)
  )"

lemma elemof'_correct: "elemof' e l = elemof e l"
  by (induction e l rule: elemof.induct) simp

record elemof_state =
  elemof_e::nat
  elemof_l::nat
  elemof_ret::nat

abbreviation "elemof_prefix \<equiv> ''elemof.''"
abbreviation "elemof_e_str \<equiv> ''e''"
abbreviation "elemof_l_str \<equiv> ''l''"
abbreviation "elemof_ret_str \<equiv> ''ret''"

definition "elemof_state_upd s \<equiv>
  (let
      tl_xs' = elemof_l s;
      tl_ret' = 0;
      tl_state = \<lparr>tl_xs = tl_xs',
                  tl_ret = tl_ret'\<rparr>;
      tl_ret_state = tl_imp tl_state;
      elemof_l' = tl_ret tl_ret_state;
      elemof_e' = elemof_e s;
      elemof_ret' = elemof_ret s;
      ret = \<lparr>elemof_e = elemof_e',
             elemof_l = elemof_l',
             elemof_ret = elemof_ret'\<rparr>
  in
      ret
)"

definition "elemof_imp_compute_loop_condition s \<equiv>
  (let
      hd_xs' = elemof_l s;
      hd_ret' = 0;
      hd_state = \<lparr>hd_xs = hd_xs', 
                  hd_ret = hd_ret'\<rparr>;
      hd_ret_state = hd_imp hd_state;
      NOTEQUAL_neq_zero_a' = hd_ret hd_ret_state;
      NOTEQUAL_neq_zero_b' = elemof_e s;
      NOTEQUAL_neq_zero_ret' = 0;
      NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                                 NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                                 NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
      NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
      AND_neq_zero_a' = elemof_l s;
      AND_neq_zero_b' = NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state;
      AND_neq_zero_ret' = 0;
      AND_neq_zero_state = \<lparr>AND_neq_zero_a = AND_neq_zero_a',
                            AND_neq_zero_b = AND_neq_zero_b',
                            AND_neq_zero_ret = AND_neq_zero_ret'\<rparr>;
      AND_neq_zero_ret_state = AND_neq_zero_imp AND_neq_zero_state;
      condition = AND_neq_zero_ret AND_neq_zero_ret_state
   in
      condition
)"

definition "elemof_imp_after_loop s \<equiv>
  (let
      elemof_e' = elemof_e s;
      elemof_l' = elemof_l s;
      elemof_ret' = 
        (if elemof_l' \<noteq> 0
        then 1
        else 0);
      ret = \<lparr>elemof_e = elemof_e',
             elemof_l = elemof_l',
             elemof_ret = elemof_ret'\<rparr>
  in
      ret
)"

lemmas elemof_imp_subprogram_simps = 
  elemof_state_upd_def
  elemof_imp_compute_loop_condition_def
  elemof_imp_after_loop_def

function elemof_imp :: "elemof_state \<Rightarrow> elemof_state" where
  "elemof_imp s =
  (if elemof_imp_compute_loop_condition s \<noteq> 0
  then let next_iteration = elemof_imp (elemof_state_upd s)
       in next_iteration
  else let ret = elemof_imp_after_loop s
       in ret
  )"
  by simp+
termination
  apply (relation "measure elemof_l")
  apply (simp add: elemof_imp_subprogram_simps AND_neq_zero_imp_correct
    NOTEQUAL_neq_zero_imp_correct hd_imp_correct tl_imp_correct split: if_splits)+
  done

declare elemof_imp.simps [simp del]

lemma elemof_imp_correct[let_function_correctness]:
  "elemof_ret (elemof_imp s) =
    elemof (elemof_e s) (elemof_l s)"
  apply (induction s rule: elemof_imp.induct)
  apply (subst elemof_imp.simps)
  apply (subst elemof.simps)
  apply (simp del: elemof.simps add: elemof_imp_subprogram_simps Let_def
  AND_neq_zero_imp_correct NOTEQUAL_neq_zero_imp_correct hd_imp_correct tl_imp_correct)
  done 

definition "elemof_state_upd_time t s \<equiv>
  let
      tl_xs' = elemof_l s;
      t = t + 2;
      tl_ret' = 0;
      t = t + 2;
      tl_state = \<lparr>tl_xs = tl_xs',
                  tl_ret = tl_ret'\<rparr>;
      tl_ret_state = tl_imp tl_state;
      t = t + tl_imp_time 0 tl_state;
      elemof_l' = tl_ret tl_ret_state;
      t = t + 2;
      elemof_e' = elemof_e s;
      t = t + 2;
      elemof_ret' = elemof_ret s;
      t = t + 2;
      ret = \<lparr>elemof_e = elemof_e',
             elemof_l = elemof_l',
             elemof_ret = elemof_ret'\<rparr>
  in
      t
"

definition "elemof_imp_compute_loop_condition_time t s \<equiv>
  let
      hd_xs' = elemof_l s;
      t = t + 2;
      hd_ret' = 0;
      t = t + 2;
      hd_state = \<lparr>hd_xs = hd_xs', 
                  hd_ret = hd_ret'\<rparr>;
      hd_ret_state = hd_imp hd_state;
      t = t + hd_imp_time 0 hd_state;
      NOTEQUAL_neq_zero_a' = hd_ret hd_ret_state;
      t = t + 2;
      NOTEQUAL_neq_zero_b' = elemof_e s;
      t = t + 2;
      NOTEQUAL_neq_zero_ret' = 0;
      t = t + 2;
      NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',
                                 NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',
                                 NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;
      NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;
      t = t + NOTEQUAL_neq_zero_imp_time 0 NOTEQUAL_neq_zero_state;
      AND_neq_zero_a' = elemof_l s;
      t = t + 2;
      AND_neq_zero_b' = NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state;
      t = t + 2;
      AND_neq_zero_ret' = 0;
      t = t + 2;
      AND_neq_zero_state = \<lparr>AND_neq_zero_a = AND_neq_zero_a',
                            AND_neq_zero_b = AND_neq_zero_b',
                            AND_neq_zero_ret = AND_neq_zero_ret'\<rparr>;
      AND_neq_zero_ret_state = AND_neq_zero_imp AND_neq_zero_state;
      t = t + AND_neq_zero_imp_time 0 AND_neq_zero_state;
      condition = AND_neq_zero_ret AND_neq_zero_ret_state;
      t = t + 2
  in
      t
"

definition "elemof_imp_after_loop_time t s \<equiv>
  let
      elemof_e' = elemof_e s;
      t = t + 2;
      elemof_l' = elemof_l s;
      t = t + 2;
      elemof_ret' = 
        (if elemof_l' \<noteq> 0
        then 1
        else 0);
      t = t + 1 +
        (if elemof_l' \<noteq> 0
        then 2
        else 2);
      ret = \<lparr>elemof_e = elemof_e',
             elemof_l = elemof_l',
             elemof_ret = elemof_ret'\<rparr>
  in
      t
"

lemmas elemof_imp_subprogram_time_simps = 
  elemof_state_upd_time_def
  elemof_imp_compute_loop_condition_time_def
  elemof_imp_after_loop_time_def
  elemof_imp_subprogram_simps

function elemof_imp_time :: "nat \<Rightarrow> elemof_state \<Rightarrow> nat" where
  "elemof_imp_time t s =
  elemof_imp_compute_loop_condition_time 0 s +
  (if elemof_imp_compute_loop_condition s \<noteq> 0
    then
      (let
        t = t + 1;
        next_iteration =
          elemof_imp_time (t + elemof_state_upd_time 0 s)
                         (elemof_state_upd s)
       in next_iteration)
    else
      (let
        t = t + 2;
        ret = t + elemof_imp_after_loop_time 0 s
       in ret)
  )"
  by auto
termination
  apply (relation "measure (elemof_l \<circ> snd)")
  by (simp add: elemof_imp_subprogram_time_simps AND_neq_zero_imp_correct
    NOTEQUAL_neq_zero_imp_correct hd_imp_correct tl_imp_correct split: if_splits)+

declare elemof_imp_time.simps [simp del]

lemma elemof_imp_time_acc:
  "(elemof_imp_time (Suc t) s) = Suc (elemof_imp_time t s)"
  by (induction t s rule: elemof_imp_time.induct)
    ((subst (1 2) elemof_imp_time.simps);
      (simp add: elemof_state_upd_def))            

lemma elemof_imp_time_acc_2_aux:
  "(elemof_imp_time t s) = t + (elemof_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: elemof_imp_time_acc)+            

lemma elemof_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (elemof_imp_time t s) = t + (elemof_imp_time 0 s)"
  by (rule elemof_imp_time_acc_2_aux)            

lemma elemof_imp_time_acc_3:
  "(elemof_imp_time (a + b) s) = a + (elemof_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: elemof_imp_time_acc)+  

abbreviation "elemof_while_cond \<equiv> ''condition''"

definition "elemof_IMP_init_while_cond \<equiv>
  \<comment> \<open>  hd_xs' = elemof_l s;\<close>
  (hd_prefix @ hd_xs_str) ::= (A (V elemof_l_str));;
  \<comment> \<open>  hd_ret' = 0;\<close>
  (hd_prefix @ hd_ret_str) ::= (A (N 0));;
  \<comment> \<open>  hd_state = \<lparr>hd_xs = hd_xs',\<close> 
  \<comment> \<open>              hd_ret = hd_ret'\<rparr>;\<close>
  \<comment> \<open>  hd_ret_state = hd_imp hd_state;\<close>
  (invoke_subprogram hd_prefix hd_IMP_Minus);;
  \<comment> \<open>  NOTEQUAL_neq_zero_a' = hd_ret hd_ret_state;\<close>
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_a_str) ::= (A (V (hd_prefix @ hd_ret_str)));;
  \<comment> \<open>  NOTEQUAL_neq_zero_b' = elemof_e s;\<close>
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_b_str) ::= (A (V elemof_e_str));;
  \<comment> \<open>  NOTEQUAL_neq_zero_ret' = 0;\<close>
  (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str) ::= (A (N 0));;
  \<comment> \<open>  NOTEQUAL_neq_zero_state = \<lparr>NOTEQUAL_neq_zero_a = NOTEQUAL_neq_zero_a',\<close>
  \<comment> \<open>                             NOTEQUAL_neq_zero_b = NOTEQUAL_neq_zero_b',\<close>
  \<comment> \<open>                             NOTEQUAL_neq_zero_ret = NOTEQUAL_neq_zero_ret'\<rparr>;\<close>
  \<comment> \<open>  NOTEQUAL_neq_zero_ret_state = NOTEQUAL_neq_zero_imp NOTEQUAL_neq_zero_state;\<close>
  (invoke_subprogram NOTEQUAL_neq_zero_prefix NOTEQUAL_neq_zero_IMP_Minus);;
  \<comment> \<open>  AND_neq_zero_a' = elemof_l s;\<close>
  (AND_neq_zero_prefix @ AND_neq_zero_a_str) ::= (A (V elemof_l_str));;
  \<comment> \<open>  AND_neq_zero_b' = NOTEQUAL_neq_zero_ret NOTEQUAL_neq_zero_ret_state;\<close>
  (AND_neq_zero_prefix @ AND_neq_zero_b_str) ::= 
    (A (V (NOTEQUAL_neq_zero_prefix @ NOTEQUAL_neq_zero_ret_str)));;
  \<comment> \<open>  AND_neq_zero_ret' = 0;\<close>
  (AND_neq_zero_prefix @ AND_neq_zero_ret_str) ::= (A (N 0));;
  \<comment> \<open>  AND_neq_zero_state = \<lparr>AND_neq_zero_a = AND_neq_zero_a',\<close>
  \<comment> \<open>                        AND_neq_zero_b = AND_neq_zero_b',\<close>
  \<comment> \<open>                        AND_neq_zero_ret = AND_neq_zero_ret'\<rparr>;\<close>
  \<comment> \<open>  AND_neq_zero_ret_state = AND_neq_zero_imp AND_neq_zero_state;\<close>
  (invoke_subprogram AND_neq_zero_prefix AND_neq_zero_IMP_Minus);;
  \<comment> \<open>  condition = AND_neq_zero_ret AND_neq_zero_ret_state\<close>
  (elemof_while_cond) ::= (A (V (AND_neq_zero_prefix @ AND_neq_zero_ret_str)))
"

definition "elemof_IMP_loop_body \<equiv>
  \<comment> \<open>  tl_xs' = elemof_l s;\<close>
  (tl_prefix @ tl_xs_str) ::= (A (V elemof_l_str));;
  \<comment> \<open>  tl_ret' = 0;\<close>
  (tl_prefix @ tl_ret_str) ::= (A (N 0));;
  \<comment> \<open>  tl_state = \<lparr>tl_xs = tl_xs',\<close>
  \<comment> \<open>              tl_ret = tl_ret'\<rparr>;\<close>
  \<comment> \<open>  tl_ret_state = tl_imp tl_state;\<close>
  (invoke_subprogram tl_prefix tl_IMP_Minus);;
  \<comment> \<open>  elemof_l' = tl_ret tl_ret_state;\<close>
  (elemof_l_str) ::= (A (V (tl_prefix @ tl_ret_str)));;
  \<comment> \<open>  elemof_e' = elemof_e s;\<close>
  (elemof_e_str) ::= (A (V elemof_e_str));;
  \<comment> \<open>  elemof_ret' = elemof_ret s;\<close>
  (elemof_ret_str) ::= (A (V elemof_ret_str))
  \<comment> \<open>  ret = \<lparr>elemof_e = elemof_e',\<close>
  \<comment> \<open>         elemof_l = elemof_l',\<close>
  \<comment> \<open>         elemof_ret = elemof_ret'\<rparr>\<close>
"

definition "elemof_IMP_after_loop \<equiv>
  \<comment> \<open>  elemof_e' = elemof_e s;\<close>
  (elemof_e_str) ::= (A (V elemof_e_str));;
  \<comment> \<open>  elemof_l' = elemof_l s;\<close>
  (elemof_l_str) ::= (A (V elemof_l_str));;
  \<comment> \<open>  elemof_ret' = \<close>
  \<comment> \<open>    (if elemof_l' \<noteq> 0\<close>
  \<comment> \<open>    then 1\<close>
  \<comment> \<open>    else 0);\<close>
  (IF elemof_l_str \<noteq>0 THEN
    (elemof_ret_str) ::= (A (N 1))
  ELSE
    (elemof_ret_str) ::= (A (N 0))
  )
  \<comment> \<open>  ret = \<lparr>elemof_e = elemof_e',\<close>
  \<comment> \<open>         elemof_l = elemof_l',\<close>
  \<comment> \<open>         elemof_ret = elemof_ret'\<rparr>\<close>
"

definition elemof_IMP_Minus where
  "elemof_IMP_Minus \<equiv>
  elemof_IMP_init_while_cond;;
  WHILE elemof_while_cond \<noteq>0 DO (
    elemof_IMP_loop_body;;
    elemof_IMP_init_while_cond
  );;
  elemof_IMP_after_loop"

abbreviation "elemof_IMP_vars \<equiv>
  {elemof_e_str, elemof_l_str, elemof_ret_str}"

lemmas elemof_IMP_subprogram_simps =
  elemof_IMP_init_while_cond_def
  elemof_IMP_loop_body_def
  elemof_IMP_after_loop_def

definition "elemof_imp_to_HOL_state p s =
  \<lparr>elemof_e = (s (add_prefix p elemof_e_str)),
   elemof_l = (s (add_prefix p elemof_l_str)),
   elemof_ret = (s (add_prefix p elemof_ret_str))\<rparr>"

lemmas elemof_state_translators =
  elemof_imp_to_HOL_state_def
  hd_imp_to_HOL_state_def
  tl_imp_to_HOL_state_def
  NOTEQUAL_neq_zero_imp_to_HOL_state_def
  AND_neq_zero_imp_to_HOL_state_def

lemmas elemof_complete_simps =
  elemof_IMP_subprogram_simps
  elemof_imp_subprogram_simps
  elemof_state_translators

lemma elemof_IMP_Minus_correct_function:
  "(invoke_subprogram p elemof_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p elemof_ret_str)
      = elemof_ret
          (elemof_imp (elemof_imp_to_HOL_state p s))"
  apply(induction "elemof_imp_to_HOL_state p s" arbitrary: s s' t
    rule: elemof_imp.induct)
  apply(subst elemof_imp.simps)
  apply(simp only: elemof_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule While_tE)

  subgoal
    apply(simp only: elemof_IMP_subprogram_simps prefix_simps)
    apply(erule Seq_E)+
    apply(erule hd_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(19) by fastforce
    apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(21) by fastforce
    apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(23) by fastforce
    by(fastforce simp: elemof_IMP_subprogram_simps
        elemof_imp_subprogram_simps
        elemof_state_translators)

  apply(erule Seq_E)+
  apply(dest_com_gen)

  subgoal
    apply(simp only: elemof_IMP_init_while_cond_def prefix_simps)
    apply(erule Seq_E)+
    apply(erule hd_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(28) by fastforce
    apply(erule hd_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(30) by fastforce
    apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(32) by fastforce
    apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(34) by fastforce
    by(fastforce simp add: elemof_complete_simps)

  subgoal
    apply(subst (asm) elemof_IMP_init_while_cond_def)
    apply(simp only: elemof_IMP_loop_body_def prefix_simps)
    apply(erule Seq_E)+
    apply(erule hd_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(22) by fastforce
    apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(24) by fastforce
    apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(26) by fastforce
    apply(erule tl_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(28) by fastforce
    by (simp only: elemof_imp_subprogram_simps
        elemof_state_translators Let_def, fastforce)

  subgoal
    apply(simp only: elemof_IMP_init_while_cond_def prefix_simps
        elemof_IMP_loop_body_def)
    apply(erule Seq_E)+
    apply(erule hd_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(33) by fastforce
    apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(35) by fastforce
    apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(37) by fastforce
    apply(erule tl_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(39) by fastforce
    by (simp only: elemof_imp_subprogram_simps
        elemof_state_translators Let_def, fastforce)
  done

lemma elemof_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ elemof_pref) elemof_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix elemof_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast

lemmas elemof_complete_time_simps =
  elemof_imp_subprogram_time_simps
  elemof_imp_time_acc
  elemof_imp_time_acc_2
  elemof_imp_time_acc_3
  elemof_state_translators

lemma elemof_IMP_Minus_correct_time:
  "(invoke_subprogram p elemof_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = elemof_imp_time 0 (elemof_imp_to_HOL_state p s)"
  apply(induction "elemof_imp_to_HOL_state p s" arbitrary: s s' t
      rule: elemof_imp.induct)
  apply(subst elemof_imp_time.simps)
  apply(simp only: elemof_IMP_Minus_def prefix_simps)

  apply(erule Seq_tE)+
  apply(erule While_tE_time)

  subgoal
    apply(simp only: elemof_IMP_subprogram_simps prefix_simps)
    apply(erule Seq_tE)+
    apply(erule hd_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(34) by fastforce
    apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(36) by fastforce
    apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(38) by fastforce
    by (force simp: elemof_imp_subprogram_time_simps Let_def
        elemof_state_translators)

  apply(erule Seq_tE)+
  apply(simp add: add.assoc)
  apply(dest_com_gen_time)

  subgoal
    apply(simp only: elemof_IMP_init_while_cond_def prefix_simps)
    apply(erule Seq_tE)+
    apply(erule hd_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(53) by fastforce
    apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(55) by fastforce
    apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(57) by fastforce
    by(fastforce simp add: elemof_complete_simps)

  subgoal
    apply(subst (asm) elemof_IMP_init_while_cond_def)
    apply(simp only: elemof_IMP_loop_body_def prefix_simps)
    apply(erule Seq_tE)+
    apply(erule hd_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(41) by fastforce
    apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(43) by fastforce
    apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(45) by fastforce
    apply(erule tl_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(47) by fastforce
    by (simp only: elemof_imp_subprogram_time_simps
        elemof_state_translators Let_def, force)

  subgoal
    apply(simp only: prefix_simps elemof_IMP_init_while_cond_def
        elemof_IMP_loop_body_def)
    apply(erule Seq_tE)+
    apply(erule hd_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(63) by fastforce
    apply(erule NOTEQUAL_neq_zero_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(65) by fastforce
    apply(erule AND_neq_zero_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(67) by fastforce
    apply(erule tl_IMP_Minus_correct[where vars = "elemof_IMP_vars"])
    subgoal premises p using p(69) by fastforce
    apply(simp only: elemof_complete_time_simps Let_def)
    by force

  done 

lemma elemof_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) elemof_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (elemof_imp_time 0 (elemof_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) elemof_ret_str) =
          elemof_ret (elemof_imp
                                        (elemof_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using elemof_IMP_Minus_correct_function
    elemof_IMP_Minus_correct_time
    elemof_IMP_Minus_correct_effects
  by (meson set_mono_prefix) 


subsubsection \<open>remdups\<close>

paragraph \<open>remdups_acc_aux\<close>

record remdups_acc_aux_state =
  remdups_acc_aux_acc::nat
  remdups_acc_aux_n::nat

abbreviation "remdups_acc_aux_prefix \<equiv> ''remdups_acc_aux.''"
abbreviation "remdups_acc_aux_acc_str \<equiv> ''acc''"
abbreviation "remdups_acc_aux_n_str \<equiv> ''n''"

definition "remdups_acc_aux_state_upd s \<equiv>
  (let
      hd_xs' = remdups_acc_aux_n s;
      hd_ret' = 0;
      hd_state = \<lparr>hd_xs = hd_xs',
                  hd_ret = hd_ret'\<rparr>;
      hd_ret_state = hd_imp hd_state;
      hd_result = hd_ret hd_ret_state;
      tl_xs' = remdups_acc_aux_n s;
      tl_ret' = 0;
      tl_state = \<lparr>tl_xs = tl_xs',
                  tl_ret = tl_ret'\<rparr>;
      tl_ret_state = tl_imp tl_state;
      tl_result = tl_ret tl_ret_state;
      elemof_e' = hd_result;
      elemof_l' = tl_result;
      elemof_ret' = 0;
      elemof_state = \<lparr>elemof_e = elemof_e',
                      elemof_l = elemof_l',
                      elemof_ret = elemof_ret'\<rparr>;
      elemof_ret_state = elemof_imp elemof_state;
      elemof_result = elemof_ret elemof_ret_state
  in
  (if elemof_result \<noteq> 0 then
    (let
      remdups_acc_aux_n' = tl_result;
      ret = \<lparr>remdups_acc_aux_acc = remdups_acc_aux_acc s,
             remdups_acc_aux_n = remdups_acc_aux_n'\<rparr>
    in
      ret
    )
  else
    (let
      cons_h' = hd_result;
      cons_t' = remdups_acc_aux_acc s;
      cons_ret' = 0;
      cons_state = \<lparr>cons_h = cons_h',
                    cons_t = cons_t',
                    cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      remdups_acc_aux_acc' = cons_ret cons_ret_state;
      remdups_acc_aux_n' = tl_result;
      ret = \<lparr>remdups_acc_aux_acc = remdups_acc_aux_acc',
             remdups_acc_aux_n = remdups_acc_aux_n'\<rparr>
    in
      ret
    )
  )
)"

function remdups_acc_aux_imp:: "remdups_acc_aux_state \<Rightarrow> remdups_acc_aux_state" where
  "remdups_acc_aux_imp s =
  (let
      ret = remdups_acc_aux_state_upd s
    in
      ret
  )"
  by simp+
termination
  by (relation "measure (\<lambda>s. remdups_acc_aux_n s)") simp

declare remdups_acc_aux_imp.simps [simp del]

lemma remdups_acc_aux_imp_correct_acc[let_function_correctness]:
  "remdups_acc_aux_acc (remdups_acc_aux_imp s) =
    (if elemof (hd_nat (remdups_acc_aux_n s)) (tl_nat (remdups_acc_aux_n s)) \<noteq> 0
    then (remdups_acc_aux_acc s)
    else cons (hd_nat (remdups_acc_aux_n s)) (remdups_acc_aux_acc s))"
  apply (subst remdups_acc_aux_imp.simps)
  apply (simp only: remdups_acc_aux_state_upd_def Let_def hd_imp_correct tl_imp_correct
  elemof_imp_correct cons_imp_correct split: if_splits)
  by (metis cons_state.select_convs(1) cons_state.select_convs(2) elemof_state.select_convs(1) 
  elemof_state.select_convs(2) hd_state.select_convs(1) remdups_acc_aux_state.select_convs(1)
  tl_state.select_convs(1))

lemma remdups_acc_aux_imp_correct_n[let_function_correctness]:
  "remdups_acc_aux_n (remdups_acc_aux_imp s) =
    (tl_nat (remdups_acc_aux_n s))"
  apply (subst remdups_acc_aux_imp.simps)
  apply (simp only: remdups_acc_aux_state_upd_def Let_def hd_imp_correct tl_imp_correct
  elemof_imp_correct cons_imp_correct split: if_splits)
  by (metis remdups_acc_aux_state.select_convs(2) tl_state.select_convs(1))

function remdups_acc_aux_imp_time:: "nat \<Rightarrow> remdups_acc_aux_state \<Rightarrow> nat" where
  "remdups_acc_aux_imp_time t s = 
  (let
      hd_xs' = remdups_acc_aux_n s;
      t = t + 2;
      hd_ret' = 0;
      t = t + 2;
      hd_state = \<lparr>hd_xs = hd_xs',
                  hd_ret = hd_ret'\<rparr>;
      hd_ret_state = hd_imp hd_state;
      t = t + hd_imp_time 0 hd_state;
      hd_result = hd_ret hd_ret_state;
      t = t + 2;
      tl_xs' = remdups_acc_aux_n s;
      t = t + 2;
      tl_ret' = 0;
      t = t + 2;
      tl_state = \<lparr>tl_xs = tl_xs',
                  tl_ret = tl_ret'\<rparr>;
      tl_ret_state = tl_imp tl_state;
      t = t + tl_imp_time 0 tl_state;
      tl_result = tl_ret tl_ret_state;
      t = t + 2;
      elemof_e' = hd_result;
      t = t + 2;
      elemof_l' = tl_result;
      t = t + 2;
      elemof_ret' = 0;
      t = t + 2;
      elemof_state = \<lparr>elemof_e = elemof_e',
                      elemof_l = elemof_l',
                      elemof_ret = elemof_ret'\<rparr>;
      elemof_ret_state = elemof_imp elemof_state;
      t = t + elemof_imp_time 0 elemof_state;
      elemof_result = elemof_ret elemof_ret_state;
      t = t + 2
  in
  (if elemof_result \<noteq> 0 then
    (let
      t = t + 1;
      remdups_acc_aux_n' = tl_result;
      t = t + 2;
      ret = \<lparr>remdups_acc_aux_acc = remdups_acc_aux_acc s,
             remdups_acc_aux_n = remdups_acc_aux_n'\<rparr>
    in
      t
    )
  else
    (let
      t = t + 1;
      cons_h' = hd_result;
      t = t + 2;
      cons_t' = remdups_acc_aux_acc s;
      t = t + 2;
      cons_ret' = 0;
      t = t + 2;
      cons_state = \<lparr>cons_h = cons_h',
                    cons_t = cons_t',
                    cons_ret = cons_ret'\<rparr>;
      cons_ret_state = cons_imp cons_state;
      t = t + cons_imp_time 0 cons_state;
      remdups_acc_aux_acc' = cons_ret cons_ret_state;
      t = t + 2;
      remdups_acc_aux_n' = tl_result;
      t = t + 2;
      ret = \<lparr>remdups_acc_aux_acc = remdups_acc_aux_acc',
             remdups_acc_aux_n = remdups_acc_aux_n'\<rparr>
    in
      t
    )
  )
)"
  by auto
termination
  by (relation "measure (remdups_acc_aux_n \<circ> snd)") simp

declare remdups_acc_aux_imp_time.simps [simp del] 

lemma remdups_acc_aux_imp_time_acc:
  "(remdups_acc_aux_imp_time (Suc t) s) = Suc (remdups_acc_aux_imp_time t s)"
  by (induction t s rule: remdups_acc_aux_imp_time.induct)
    ((subst (1 2) remdups_acc_aux_imp_time.simps);
      (simp add: remdups_acc_aux_state_upd_def Let_def))            

lemma remdups_acc_aux_imp_time_acc_2_aux:
  "(remdups_acc_aux_imp_time t s) = t + (remdups_acc_aux_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: remdups_acc_aux_imp_time_acc)+            

lemma remdups_acc_aux_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (remdups_acc_aux_imp_time t s) = t + (remdups_acc_aux_imp_time 0 s)"
  by (rule remdups_acc_aux_imp_time_acc_2_aux)            

lemma remdups_acc_aux_imp_time_acc_3:
  "(remdups_acc_aux_imp_time (a + b) s) = a + (remdups_acc_aux_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: remdups_acc_aux_imp_time_acc)+ 

abbreviation "remdups_acc_aux_hd_result \<equiv> ''hd_result''"
abbreviation "remdups_acc_aux_tl_result \<equiv> ''tl_result''"
abbreviation "remdups_acc_aux_elemof_result \<equiv> ''elemof_result''"

abbreviation "remdups_acc_aux_IMP_if \<equiv>
  \<comment> \<open>  remdups_acc_aux_n' = tl_result;\<close>
  (remdups_acc_aux_n_str) ::= (A (V remdups_acc_aux_tl_result))
  \<comment> \<open>  ret = \<lparr>remdups_acc_aux_acc = remdups_acc_aux_acc s,\<close>
  \<comment> \<open>         remdups_acc_aux_n = remdups_acc_aux_n'\<rparr>\<close>
"

abbreviation "remdups_acc_aux_IMP_else \<equiv>
  \<comment> \<open>  cons_h' = hd_result;\<close>
  (cons_prefix @ cons_h_str) ::= (A (V remdups_acc_aux_hd_result));;
  \<comment> \<open>  cons_t' = remdups_acc_aux_acc s;\<close>
  (cons_prefix @ cons_t_str) ::= (A (V remdups_acc_aux_acc_str));;
  \<comment> \<open>  cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= (A (N 0));;
  \<comment> \<open>  cons_state = \<lparr>cons_h = cons_h',\<close>
  \<comment> \<open>                cons_t = cons_t',\<close>
  \<comment> \<open>                cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>  cons_ret_state = cons_imp cons_state;\<close>
  (invoke_subprogram cons_prefix cons_IMP_Minus);;
  \<comment> \<open>  remdups_acc_aux_acc' = cons_ret cons_ret_state;\<close>
  (remdups_acc_aux_acc_str) ::= (A (V (cons_prefix @ cons_ret_str)));;
  \<comment> \<open>  remdups_acc_aux_n' = tl_result;\<close>
  (remdups_acc_aux_n_str) ::= (A (V remdups_acc_aux_tl_result))
  \<comment> \<open>  ret = \<lparr>remdups_acc_aux_acc = remdups_acc_aux_acc',\<close>
  \<comment> \<open>         remdups_acc_aux_n = remdups_acc_aux_n'\<rparr>\<close>
"

definition remdups_acc_aux_IMP_Minus where
  "remdups_acc_aux_IMP_Minus \<equiv>
  \<comment> \<open>  hd_xs' = remdups_acc_aux_n s;\<close>
  (hd_prefix @ hd_xs_str) ::= (A (V remdups_acc_aux_n_str));;
  \<comment> \<open>  hd_ret' = 0;\<close>
  (hd_prefix @ hd_ret_str) ::= (A (N 0));;
  \<comment> \<open>  hd_state = \<lparr>hd_xs = hd_xs',\<close>
  \<comment> \<open>              hd_ret = hd_ret'\<rparr>;\<close>
  \<comment> \<open>  hd_ret_state = hd_imp hd_state;\<close>
  (invoke_subprogram hd_prefix hd_IMP_Minus);;
  \<comment> \<open>  hd_result = hd_ret hd_ret_state;\<close>
  (remdups_acc_aux_hd_result) ::= (A (V (hd_prefix @ hd_ret_str)));;
  \<comment> \<open>  tl_xs' = remdups_acc_aux_n s;\<close>
  (tl_prefix @ tl_xs_str) ::= (A (V remdups_acc_aux_n_str));;
  \<comment> \<open>  tl_ret' = 0;\<close>
  (tl_prefix @ tl_ret_str) ::= (A (N 0));;
  \<comment> \<open>  tl_state = \<lparr>tl_xs = tl_xs',\<close>
  \<comment> \<open>              tl_ret = tl_ret'\<rparr>;\<close>
  \<comment> \<open>  tl_ret_state = tl_imp tl_state;\<close>
  (invoke_subprogram tl_prefix tl_IMP_Minus);;
  \<comment> \<open>  tl_result = tl_ret tl_ret_state;\<close>
  (remdups_acc_aux_tl_result) ::= (A (V (tl_prefix @ tl_ret_str)));;
  \<comment> \<open>  elemof_e' = hd_result;\<close>
  (elemof_prefix @ elemof_e_str) ::= (A (V remdups_acc_aux_hd_result));;
  \<comment> \<open>  elemof_l' = tl_result;\<close>
  (elemof_prefix @ elemof_l_str) ::= (A (V remdups_acc_aux_tl_result));;
  \<comment> \<open>  elemof_ret' = 0;\<close>
  (elemof_prefix @ elemof_ret_str) ::= (A (N 0));;
  \<comment> \<open>  elemof_state = \<lparr>elemof_e = elemof_e',\<close>
  \<comment> \<open>                  elemof_l = elemof_l',\<close>
  \<comment> \<open>                  elemof_ret = elemof_ret'\<rparr>;\<close>
  \<comment> \<open>  elemof_ret_state = elemof_imp elemof_state;\<close>
  (invoke_subprogram elemof_prefix elemof_IMP_Minus);;
  \<comment> \<open>  elemof_result = elemof_ret elemof_ret_state\<close>
  (remdups_acc_aux_elemof_result) ::= (A (V (elemof_prefix @ elemof_ret_str)));;
  \<comment> \<open>(if elemof_result \<noteq> 0 then\<close>
  (IF remdups_acc_aux_elemof_result \<noteq>0 THEN
    remdups_acc_aux_IMP_if
  \<comment> \<open>else\<close>
  ELSE
    remdups_acc_aux_IMP_else
  )
"

abbreviation "remdups_acc_aux_IMP_vars \<equiv>
  {remdups_acc_aux_acc_str, remdups_acc_aux_n_str, remdups_acc_aux_hd_result,
  remdups_acc_aux_tl_result, remdups_acc_aux_elemof_result}"

definition "remdups_acc_aux_imp_to_HOL_state p s =
  \<lparr>remdups_acc_aux_acc = (s (add_prefix p remdups_acc_aux_acc_str)),
   remdups_acc_aux_n = (s (add_prefix p remdups_acc_aux_n_str))\<rparr>"

lemmas remdups_acc_aux_state_translators =
  remdups_acc_aux_imp_to_HOL_state_def
  hd_imp_to_HOL_state_def
  tl_imp_to_HOL_state_def
  elemof_imp_to_HOL_state_def
  cons_imp_to_HOL_state_def

lemma remdups_acc_aux_IMP_Minus_correct_function_acc:
  "(invoke_subprogram p remdups_acc_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p remdups_acc_aux_acc_str)
      = remdups_acc_aux_acc
          (remdups_acc_aux_imp (remdups_acc_aux_imp_to_HOL_state p s))"
  apply(subst remdups_acc_aux_imp.simps)
  apply(simp only: remdups_acc_aux_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule hd_IMP_Minus_correct[where vars = "remdups_acc_aux_IMP_vars"])
  subgoal premises p using p(14) by fastforce
  apply(erule tl_IMP_Minus_correct[where vars = "remdups_acc_aux_IMP_vars"])
  subgoal premises p using p(16) by fastforce
  apply(erule elemof_IMP_Minus_correct[where vars = "remdups_acc_aux_IMP_vars"])
  subgoal premises p using p(18) by fastforce
  apply(erule If_E)
  subgoal
    by (fastforce_sorted_premises2 simp: remdups_acc_aux_state_upd_def Let_def
      remdups_acc_aux_state_translators)
  subgoal
    apply(erule Seq_E)+
    apply(erule cons_IMP_Minus_correct[where vars = "remdups_acc_aux_IMP_vars"])
    subgoal premises p using p(26) by fastforce
    by (fastforce_sorted_premises2 simp: remdups_acc_aux_state_upd_def Let_def
      remdups_acc_aux_state_translators)
  done

lemma remdups_acc_aux_IMP_Minus_correct_function_n:
  "(invoke_subprogram p remdups_acc_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p remdups_acc_aux_n_str)
      = remdups_acc_aux_n
          (remdups_acc_aux_imp (remdups_acc_aux_imp_to_HOL_state p s))"
  apply(subst remdups_acc_aux_imp.simps)
  apply(simp only: remdups_acc_aux_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule hd_IMP_Minus_correct[where vars = "remdups_acc_aux_IMP_vars"])
  subgoal premises p using p(14) by fastforce
  apply(erule tl_IMP_Minus_correct[where vars = "remdups_acc_aux_IMP_vars"])
  subgoal premises p using p(16) by fastforce
  apply(erule elemof_IMP_Minus_correct[where vars = "remdups_acc_aux_IMP_vars"])
  subgoal premises p using p(18) by fastforce
  apply(erule If_E)
  subgoal
    by (fastforce_sorted_premises2 simp: remdups_acc_aux_state_upd_def Let_def
      remdups_acc_aux_state_translators)
  subgoal
    apply(erule Seq_E)+
    apply(erule cons_IMP_Minus_correct[where vars = "remdups_acc_aux_IMP_vars"])
    subgoal premises p using p(26) by fastforce
    by (fastforce_sorted_premises2 simp: remdups_acc_aux_state_upd_def Let_def
      remdups_acc_aux_state_translators)
  done

lemma remdups_acc_aux_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ remdups_acc_aux_pref) remdups_acc_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix remdups_acc_aux_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast    

lemma remdups_acc_aux_IMP_Minus_correct_time:
  "(invoke_subprogram p remdups_acc_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = remdups_acc_aux_imp_time 0 (remdups_acc_aux_imp_to_HOL_state p s)"
  apply(subst remdups_acc_aux_imp_time.simps)
  apply(simp only: remdups_acc_aux_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule hd_IMP_Minus_correct[where vars = "remdups_acc_aux_IMP_vars"])
  subgoal premises p using p(27) by fastforce
  apply(erule tl_IMP_Minus_correct[where vars = "remdups_acc_aux_IMP_vars"])
  subgoal premises p using p(29) by fastforce
  apply(erule elemof_IMP_Minus_correct[where vars = "remdups_acc_aux_IMP_vars"])
  subgoal premises p using p(31) by fastforce
  apply(erule If_tE)
  subgoal
    by (fastforce_sorted_premises2 simp: Let_def
      remdups_acc_aux_state_translators)
  subgoal
    apply(erule Seq_tE)+
    apply(erule cons_IMP_Minus_correct[where vars = "remdups_acc_aux_IMP_vars"])
    subgoal premises p using p(45) by fastforce
    by (fastforce_sorted_premises2 simp: Let_def
      remdups_acc_aux_state_translators)
  done

lemma remdups_acc_aux_IMP_Minus_correct_acc:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) remdups_acc_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (remdups_acc_aux_imp_time 0 (remdups_acc_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) remdups_acc_aux_acc_str) =
          remdups_acc_aux_acc (remdups_acc_aux_imp
                                        (remdups_acc_aux_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using remdups_acc_aux_IMP_Minus_correct_function_acc
  remdups_acc_aux_IMP_Minus_correct_time
  remdups_acc_aux_IMP_Minus_correct_effects
  by (meson set_mono_prefix)

lemma remdups_acc_aux_IMP_Minus_correct_n:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) remdups_acc_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (remdups_acc_aux_imp_time 0 (remdups_acc_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) remdups_acc_aux_n_str) =
          remdups_acc_aux_n (remdups_acc_aux_imp
                                        (remdups_acc_aux_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using remdups_acc_aux_IMP_Minus_correct_function_n
  remdups_acc_aux_IMP_Minus_correct_time
  remdups_acc_aux_IMP_Minus_correct_effects
  by (meson set_mono_prefix)

lemma remdups_acc_aux_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) remdups_acc_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (remdups_acc_aux_imp_time 0 (remdups_acc_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) remdups_acc_aux_acc_str) =
          remdups_acc_aux_acc (remdups_acc_aux_imp
                                        (remdups_acc_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) remdups_acc_aux_n_str) =
          remdups_acc_aux_n (remdups_acc_aux_imp
                                        (remdups_acc_aux_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using remdups_acc_aux_IMP_Minus_correct_acc
  remdups_acc_aux_IMP_Minus_correct_n
  by (smt (verit, del_insts))



paragraph \<open>remdups_acc\<close>

record remdups_acc_state =
  remdups_acc_acc::nat
  remdups_acc_n::nat
  remdups_acc_ret::nat

abbreviation "remdups_acc_prefix \<equiv> ''remdups_acc.''"
abbreviation "remdups_acc_acc_str \<equiv> ''acc''"
abbreviation "remdups_acc_n_str \<equiv> ''n''"
abbreviation "remdups_acc_ret_str \<equiv> ''ret''"

definition "remdups_acc_state_upd s \<equiv>
  (let
      remdups_acc_aux_acc' = remdups_acc_acc s;
      remdups_acc_aux_n' = remdups_acc_n s;
      remdups_acc_aux_state = \<lparr>remdups_acc_aux_acc = remdups_acc_aux_acc',
                               remdups_acc_aux_n = remdups_acc_aux_n'\<rparr>;
      remdups_acc_aux_ret_state = remdups_acc_aux_imp remdups_acc_aux_state;
      remdups_acc_acc' = remdups_acc_aux_acc remdups_acc_aux_ret_state;
      remdups_acc_n' = remdups_acc_aux_n remdups_acc_aux_ret_state;
      ret = \<lparr>remdups_acc_acc = remdups_acc_acc',
             remdups_acc_n = remdups_acc_n',
             remdups_acc_ret = remdups_acc_ret s\<rparr>
  in
      ret
)"

definition "remdups_acc_imp_compute_loop_condition s \<equiv>
  (let
      condition = remdups_acc_n s
  in
      condition
)"

definition "remdups_acc_imp_after_loop s \<equiv>
  (let
      remdups_acc_ret' = remdups_acc_acc s;
      ret = \<lparr>remdups_acc_acc = remdups_acc_acc s,
             remdups_acc_n = remdups_acc_n s,
             remdups_acc_ret = remdups_acc_ret'\<rparr>
  in
      ret
)"

lemmas remdups_acc_imp_subprogram_simps = 
  remdups_acc_state_upd_def
  remdups_acc_imp_compute_loop_condition_def
  remdups_acc_imp_after_loop_def

function remdups_acc_imp :: "remdups_acc_state \<Rightarrow> remdups_acc_state" where
  "remdups_acc_imp s =
  (if remdups_acc_imp_compute_loop_condition s \<noteq> 0
   then let next_iteration = remdups_acc_imp (remdups_acc_state_upd s)
        in next_iteration
   else let ret = remdups_acc_imp_after_loop s
        in ret
  )"
  by simp+
termination
  apply (relation "measure remdups_acc_n")
  apply (simp add: remdups_acc_imp_subprogram_simps remdups_acc_aux_imp_correct_n
  Let_def)+
  done

declare remdups_acc_imp.simps [simp del]

lemma remdups_acc_imp_correct[let_function_correctness]:
  "remdups_acc_ret (remdups_acc_imp s) =
    remdups_acc (remdups_acc_acc s) (remdups_acc_n s)"
  apply (induction s rule: remdups_acc_imp.induct)
  apply (subst remdups_acc_imp.simps)
  apply (subst remdups_acc.simps)
  apply (simp del: remdups_acc.simps only: remdups_acc_imp_subprogram_simps Let_def
  remdups_acc_aux_imp_correct_acc remdups_acc_aux_imp_correct_n)
  by (smt (z3) remdups_acc_aux_state.select_convs(1) remdups_acc_aux_state.select_convs(2)
  remdups_acc_state.select_convs(1) remdups_acc_state.select_convs(2) remdups_acc_state.select_convs(3))
   
definition "remdups_acc_state_upd_time t s \<equiv>
  (let
      remdups_acc_aux_acc' = remdups_acc_acc s;
      t = t + 2;
      remdups_acc_aux_n' = remdups_acc_n s;
      t = t + 2;
      remdups_acc_aux_state = \<lparr>remdups_acc_aux_acc = remdups_acc_aux_acc',
                               remdups_acc_aux_n = remdups_acc_aux_n'\<rparr>;
      remdups_acc_aux_ret_state = remdups_acc_aux_imp remdups_acc_aux_state;
      t = t + remdups_acc_aux_imp_time 0 remdups_acc_aux_state;
      remdups_acc_acc' = remdups_acc_aux_acc remdups_acc_aux_ret_state;
      t = t + 2;
      remdups_acc_n' = remdups_acc_aux_n remdups_acc_aux_ret_state;
      t = t + 2;
      ret = \<lparr>remdups_acc_acc = remdups_acc_acc',
             remdups_acc_n = remdups_acc_n',
             remdups_acc_ret = remdups_acc_ret s\<rparr>
  in
      t
)"

definition "remdups_acc_imp_compute_loop_condition_time t s \<equiv>
  (let
      condition = remdups_acc_n s;
      t = t + 2
  in
      t
)"

definition "remdups_acc_imp_after_loop_time t s \<equiv>
  (let
      remdups_acc_ret' = remdups_acc_acc s;
      t = t + 2;
      ret = \<lparr>remdups_acc_acc = remdups_acc_acc s,
             remdups_acc_n = remdups_acc_n s,
             remdups_acc_ret = remdups_acc_ret'\<rparr>
  in
      t
)"

lemmas remdups_acc_imp_subprogram_time_simps = 
  remdups_acc_state_upd_time_def
  remdups_acc_imp_compute_loop_condition_time_def
  remdups_acc_imp_after_loop_time_def
  remdups_acc_imp_subprogram_simps

function remdups_acc_imp_time :: "nat \<Rightarrow> remdups_acc_state \<Rightarrow> nat" where
  "remdups_acc_imp_time t s =
  remdups_acc_imp_compute_loop_condition_time 0 s +
  (if remdups_acc_imp_compute_loop_condition s \<noteq> 0
    then
      (let
        t = t + 1;
        next_iteration =
          remdups_acc_imp_time (t + remdups_acc_state_upd_time 0 s)
                         (remdups_acc_state_upd s)
       in next_iteration)
    else
      (let
        t = t + 2;
        ret = t + remdups_acc_imp_after_loop_time 0 s
       in ret)
  )"
  by auto
termination
  apply (relation "measure (remdups_acc_n \<circ> snd)")
  by (simp add: remdups_acc_imp_subprogram_time_simps remdups_acc_aux_imp_correct_n
  Let_def)+

declare remdups_acc_imp_time.simps [simp del]

lemma remdups_acc_imp_time_acc:
  "(remdups_acc_imp_time (Suc t) s) = Suc (remdups_acc_imp_time t s)"
  by (induction t s rule: remdups_acc_imp_time.induct)
    ((subst (1 2) remdups_acc_imp_time.simps);
      (simp add: remdups_acc_state_upd_def))            

lemma remdups_acc_imp_time_acc_2_aux:
  "(remdups_acc_imp_time t s) = t + (remdups_acc_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: remdups_acc_imp_time_acc)+            

lemma remdups_acc_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (remdups_acc_imp_time t s) = t + (remdups_acc_imp_time 0 s)"
  by (rule remdups_acc_imp_time_acc_2_aux)            

lemma remdups_acc_imp_time_acc_3:
  "(remdups_acc_imp_time (a + b) s) = a + (remdups_acc_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: remdups_acc_imp_time_acc)+

abbreviation "remdups_acc_while_cond \<equiv> ''condition''"

definition "remdups_acc_IMP_init_while_cond \<equiv>
  \<comment> \<open>  condition = remdups_acc_n s\<close>
  (remdups_acc_while_cond) ::= (A (V remdups_acc_n_str))
"

definition "remdups_acc_IMP_loop_body \<equiv>
  \<comment> \<open>  remdups_acc_aux_acc' = remdups_acc_acc s;\<close>
  (remdups_acc_aux_prefix @ remdups_acc_aux_acc_str) ::= (A (V remdups_acc_acc_str));;
  \<comment> \<open>  remdups_acc_aux_n' = remdups_acc_n s;\<close>
  (remdups_acc_aux_prefix @ remdups_acc_aux_n_str) ::= (A (V remdups_acc_n_str));;
  \<comment> \<open>  remdups_acc_aux_state = \<lparr>remdups_acc_aux_acc = remdups_acc_aux_acc',\<close>
  \<comment> \<open>                           remdups_acc_aux_n = remdups_acc_aux_n'\<rparr>;\<close>
  \<comment> \<open>  remdups_acc_aux_ret_state = remdups_acc_aux_imp remdups_acc_aux_state;\<close>
  (invoke_subprogram remdups_acc_aux_prefix remdups_acc_aux_IMP_Minus);;
  \<comment> \<open>  remdups_acc_acc' = remdups_acc_aux_acc remdups_acc_aux_ret_state;\<close>
  (remdups_acc_acc_str) ::= (A (V (remdups_acc_aux_prefix @ remdups_acc_aux_acc_str)));;
  \<comment> \<open>  remdups_acc_n' = remdups_acc_aux_n remdups_acc_aux_ret_state;\<close>
  (remdups_acc_n_str) ::= (A (V (remdups_acc_aux_prefix @ remdups_acc_aux_n_str)))
  \<comment> \<open>  ret = \<lparr>remdups_acc_acc = remdups_acc_acc',\<close>
  \<comment> \<open>         remdups_acc_n = remdups_acc_n',\<close>
  \<comment> \<open>         remdups_acc_ret = remdups_acc_ret s\<rparr>\<close>
"

definition "remdups_acc_IMP_after_loop \<equiv>
  \<comment> \<open>  remdups_acc_ret' = remdups_acc_acc s;\<close>
  (remdups_acc_ret_str) ::= (A (V remdups_acc_acc_str))
  \<comment> \<open>  ret = \<lparr>remdups_acc_acc = remdups_acc_acc s,\<close>
  \<comment> \<open>         remdups_acc_n = remdups_acc_n s,\<close>
  \<comment> \<open>         remdups_acc_ret = remdups_acc_ret'\<rparr>\<close>
"

definition remdups_acc_IMP_Minus where
  "remdups_acc_IMP_Minus \<equiv>
  remdups_acc_IMP_init_while_cond;;
  WHILE remdups_acc_while_cond \<noteq>0 DO (
    remdups_acc_IMP_loop_body;;
    remdups_acc_IMP_init_while_cond
  );;
  remdups_acc_IMP_after_loop"

abbreviation "remdups_acc_IMP_vars \<equiv>
  {remdups_acc_acc_str, remdups_acc_n_str, remdups_acc_ret_str}"

lemmas remdups_acc_IMP_subprogram_simps =
  remdups_acc_IMP_init_while_cond_def
  remdups_acc_IMP_loop_body_def
  remdups_acc_IMP_after_loop_def

definition "remdups_acc_imp_to_HOL_state p s =
  \<lparr>remdups_acc_acc = (s (add_prefix p remdups_acc_acc_str)),
   remdups_acc_n = (s (add_prefix p remdups_acc_n_str)),
   remdups_acc_ret = (s (add_prefix p remdups_acc_ret_str))\<rparr>"

lemmas remdups_acc_state_translators =
  remdups_acc_imp_to_HOL_state_def
  remdups_acc_aux_imp_to_HOL_state_def

lemmas remdups_acc_complete_simps =
  remdups_acc_IMP_subprogram_simps
  remdups_acc_imp_subprogram_simps
  remdups_acc_state_translators

lemma remdups_acc_IMP_Minus_correct_function:
  "(invoke_subprogram p remdups_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p remdups_acc_ret_str)
      = remdups_acc_ret
          (remdups_acc_imp (remdups_acc_imp_to_HOL_state p s))"
  apply(induction "remdups_acc_imp_to_HOL_state p s" arbitrary: s s' t
    rule: remdups_acc_imp.induct)
  apply(subst remdups_acc_imp.simps)
  apply(simp only: remdups_acc_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule While_tE)

  subgoal
    by(fastforce simp: remdups_acc_IMP_subprogram_simps
        remdups_acc_imp_subprogram_simps
        remdups_acc_state_translators)

  apply(erule Seq_E)+
  apply(dest_com_gen)

  subgoal
      by(fastforce simp add: remdups_acc_complete_simps)

  subgoal
      apply(subst (asm) remdups_acc_IMP_init_while_cond_def)
      apply(simp only: remdups_acc_IMP_loop_body_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule remdups_acc_aux_IMP_Minus_correct[where vars = "remdups_acc_IMP_vars"])
      subgoal premises p using p(10) by fastforce
      by (simp only: remdups_acc_imp_subprogram_simps
          remdups_acc_state_translators Let_def, force)

  subgoal
      apply(simp only: remdups_acc_IMP_init_while_cond_def prefix_simps
          remdups_acc_IMP_loop_body_def)
      apply(erule Seq_E)+
      apply(erule remdups_acc_aux_IMP_Minus_correct[where vars = "remdups_acc_IMP_vars"])
      subgoal premises p using p(10) by fastforce
      by (simp only: remdups_acc_imp_subprogram_simps
          remdups_acc_state_translators Let_def, force)
  done

lemma remdups_acc_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ remdups_acc_pref) remdups_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix remdups_acc_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast  

lemmas remdups_acc_complete_time_simps =
  remdups_acc_imp_subprogram_time_simps
  remdups_acc_imp_time_acc
  remdups_acc_imp_time_acc_2
  remdups_acc_imp_time_acc_3
  remdups_acc_state_translators

lemma remdups_acc_IMP_Minus_correct_time:
  "(invoke_subprogram p remdups_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = remdups_acc_imp_time 0 (remdups_acc_imp_to_HOL_state p s)"
  apply(induction "remdups_acc_imp_to_HOL_state p s" arbitrary: s s' t
      rule: remdups_acc_imp.induct)
  apply(subst remdups_acc_imp_time.simps)
  apply(simp only: remdups_acc_IMP_Minus_def prefix_simps)

  apply(erule Seq_tE)+
  apply(erule While_tE_time)

  subgoal
    apply(simp only: remdups_acc_IMP_subprogram_simps prefix_simps)
    by (force simp: remdups_acc_IMP_subprogram_simps
        remdups_acc_imp_subprogram_time_simps remdups_acc_state_translators)

  apply(erule Seq_tE)+
  apply(simp add: add.assoc)
  apply(dest_com_gen_time)

  subgoal
    apply(simp only: remdups_acc_IMP_init_while_cond_def prefix_simps)
    by(fastforce simp add: remdups_acc_complete_simps)

  subgoal
    apply(subst (asm) remdups_acc_IMP_init_while_cond_def)
    apply(simp only: remdups_acc_IMP_loop_body_def prefix_simps)
    apply(erule Seq_tE)+
    apply(erule remdups_acc_aux_IMP_Minus_correct[where vars = "remdups_acc_IMP_vars"])
    subgoal premises p using p(17) by fastforce
    by (simp only: remdups_acc_imp_subprogram_time_simps
        remdups_acc_state_translators Let_def, force)

  subgoal
    apply(simp only: prefix_simps remdups_acc_IMP_init_while_cond_def
        remdups_acc_IMP_loop_body_def)
    apply(erule Seq_tE)+
    apply(erule remdups_acc_aux_IMP_Minus_correct[where vars = "remdups_acc_IMP_vars"])
    subgoal premises p using p(17) by fastforce
    apply(simp only: remdups_acc_complete_time_simps Let_def)
    by force

  done

lemma remdups_acc_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) remdups_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (remdups_acc_imp_time 0 (remdups_acc_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) remdups_acc_ret_str) =
          remdups_acc_ret (remdups_acc_imp
                                        (remdups_acc_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using remdups_acc_IMP_Minus_correct_function
  remdups_acc_IMP_Minus_correct_time
  remdups_acc_IMP_Minus_correct_effects 
  by (meson set_mono_prefix)


paragraph \<open>remdups_tail\<close>

record remdups_tail_state =
  remdups_tail_xs::nat
  remdups_tail_ret::nat

abbreviation "remdups_tail_prefix \<equiv> ''remdups_tail.''"
abbreviation "remdups_tail_xs_str \<equiv> ''xs''"
abbreviation "remdups_tail_ret_str \<equiv> ''ret''"

definition "remdups_tail_state_upd s \<equiv>
  (let
      remdups_acc_acc' = 0;
      remdups_acc_n' = remdups_tail_xs s;
      remdups_acc_ret' = 0;
      remdups_acc_state = \<lparr>remdups_acc_acc = remdups_acc_acc',
                           remdups_acc_n = remdups_acc_n',
                           remdups_acc_ret = remdups_acc_ret'\<rparr>;
      remdups_acc_ret_state = remdups_acc_imp remdups_acc_state;
      reverse_nat_n' = remdups_acc_ret remdups_acc_ret_state;
      reverse_nat_ret' = 0;
      reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n',
                           reverse_nat_ret = reverse_nat_ret'\<rparr>;
      reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;
      remdups_tail_ret' = reverse_nat_ret reverse_nat_ret_state;
      ret = \<lparr>remdups_tail_xs = remdups_tail_xs s,
             remdups_tail_ret = remdups_tail_ret'\<rparr>
  in
      ret
)"

function remdups_tail_imp:: "remdups_tail_state \<Rightarrow> remdups_tail_state" where
  "remdups_tail_imp s =
  (let
      ret = remdups_tail_state_upd s
    in
      ret
  )"
  by simp+
termination
  by (relation "measure (\<lambda>s. remdups_tail_xs s)") simp

declare remdups_tail_imp.simps [simp del]

lemma remdups_tail_imp_correct[let_function_correctness]:
  "remdups_tail_ret (remdups_tail_imp s) =
    remdups_tail (remdups_tail_xs s)"
  apply (simp only: remdups_tail_imp.simps reverse_nat_imp_correct
  remdups_acc_imp_correct remdups_tail_def Let_def remdups_tail_state_upd_def)
  by simp

function remdups_tail_imp_time :: "nat \<Rightarrow> remdups_tail_state \<Rightarrow> nat" where
  "remdups_tail_imp_time t s =
  (let
      remdups_acc_acc' = 0;
      t = t + 2;
      remdups_acc_n' = remdups_tail_xs s;
      t = t + 2;
      remdups_acc_ret' = 0;
      t = t + 2;
      remdups_acc_state = \<lparr>remdups_acc_acc = remdups_acc_acc',
                           remdups_acc_n = remdups_acc_n',
                           remdups_acc_ret = remdups_acc_ret'\<rparr>;
      remdups_acc_ret_state = remdups_acc_imp remdups_acc_state;
      t = t + remdups_acc_imp_time 0 remdups_acc_state;
      reverse_nat_n' = remdups_acc_ret remdups_acc_ret_state;
      t = t + 2;
      reverse_nat_ret' = 0;
      t = t + 2;
      reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n',
                           reverse_nat_ret = reverse_nat_ret'\<rparr>;
      reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;
      t = t + reverse_nat_imp_time 0 reverse_nat_state;
      remdups_tail_ret' = reverse_nat_ret reverse_nat_ret_state;
      t = t + 2;
      ret = \<lparr>remdups_tail_xs = remdups_tail_xs s,
             remdups_tail_ret = remdups_tail_ret'\<rparr>
  in
      t
  )"
  by auto
termination
  by (relation "measure (remdups_tail_xs \<circ> snd)") simp

declare remdups_tail_imp_time.simps [simp del]

lemma remdups_tail_imp_time_acc:
  "(remdups_tail_imp_time (Suc t) s) = Suc (remdups_tail_imp_time t s)"
  by (induction t s rule: remdups_tail_imp_time.induct)
    ((subst (1 2) remdups_tail_imp_time.simps);
      (simp add: remdups_tail_state_upd_def Let_def))            

lemma remdups_tail_imp_time_acc_2_aux:
  "(remdups_tail_imp_time t s) = t + (remdups_tail_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: remdups_tail_imp_time_acc)+            

lemma remdups_tail_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (remdups_tail_imp_time t s) = t + (remdups_tail_imp_time 0 s)"
  by (rule remdups_tail_imp_time_acc_2_aux)            

lemma remdups_tail_imp_time_acc_3:
  "(remdups_tail_imp_time (a + b) s) = a + (remdups_tail_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: remdups_tail_imp_time_acc)+  

definition remdups_tail_IMP_Minus where
  "remdups_tail_IMP_Minus \<equiv>
  \<comment> \<open>  remdups_acc_acc' = 0;\<close>
  (remdups_acc_prefix @ remdups_acc_acc_str) ::= (A (N 0));;
  \<comment> \<open>  remdups_acc_n' = remdups_tail_xs s;\<close>
  (remdups_acc_prefix @ remdups_acc_n_str) ::= (A (V remdups_tail_xs_str));;
  \<comment> \<open>  remdups_acc_ret' = 0;\<close>
  (remdups_acc_prefix @ remdups_acc_ret_str) ::= (A (N 0));;
  \<comment> \<open>  remdups_acc_state = \<lparr>remdups_acc_acc = remdups_acc_acc',\<close>
  \<comment> \<open>                       remdups_acc_n = remdups_acc_n',\<close>
  \<comment> \<open>                       remdups_acc_ret = remdups_acc_ret'\<rparr>;\<close>
  \<comment> \<open>  remdups_acc_ret_state = remdups_acc_imp remdups_acc_state;\<close>
  (invoke_subprogram remdups_acc_prefix remdups_acc_IMP_Minus);;
  \<comment> \<open>  reverse_nat_n' = remdups_acc_ret remdups_acc_ret_state;\<close>
  (reverse_nat_prefix @ reverse_nat_n_str) ::= (A (V (remdups_acc_prefix @ remdups_acc_ret_str)));;
  \<comment> \<open>  reverse_nat_ret' = 0;\<close>
  (reverse_nat_prefix @ reverse_nat_ret_str) ::= (A (N 0));;
  \<comment> \<open>  reverse_nat_state = \<lparr>reverse_nat_n = reverse_nat_n',\<close>
  \<comment> \<open>                       reverse_nat_ret = reverse_nat_ret'\<rparr>;\<close>
  \<comment> \<open>  reverse_nat_ret_state = reverse_nat_imp reverse_nat_state;\<close>
  (invoke_subprogram reverse_nat_prefix reverse_nat_IMP_Minus);;
  \<comment> \<open>  remdups_tail_ret' = reverse_nat_ret reverse_nat_ret_state;\<close>
  (remdups_tail_ret_str) ::= (A (V (reverse_nat_prefix @ reverse_nat_ret_str)))
  \<comment> \<open>  ret = \<lparr>remdups_tail_xs = remdups_tail_xs s,\<close>
  \<comment> \<open>         remdups_tail_ret = remdups_tail_ret'\<rparr>\<close>
"

abbreviation "remdups_tail_IMP_vars \<equiv>
  {remdups_tail_xs_str, remdups_tail_ret_str}"

definition "remdups_tail_imp_to_HOL_state p s =
  \<lparr>remdups_tail_xs = (s (add_prefix p remdups_tail_xs_str)),
   remdups_tail_ret = (s (add_prefix p remdups_tail_ret_str))\<rparr>"

lemmas remdups_tail_state_translators =
  remdups_tail_imp_to_HOL_state_def
  remdups_acc_imp_to_HOL_state_def
  reverse_nat_imp_to_HOL_state_def

lemma remdups_tail_IMP_Minus_correct_function:
  "(invoke_subprogram p remdups_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p remdups_tail_ret_str)
      = remdups_tail_ret
          (remdups_tail_imp (remdups_tail_imp_to_HOL_state p s))"
  apply(subst remdups_tail_imp.simps)
  apply(simp only: remdups_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule remdups_acc_IMP_Minus_correct[where vars = "remdups_tail_IMP_vars"])
  subgoal premises p using p(8) by fastforce
  apply(erule reverse_nat_IMP_Minus_correct[where vars = "remdups_tail_IMP_vars"])
  subgoal premises p using p(10) by fastforce
  by (fastforce simp: remdups_tail_state_translators remdups_tail_state_upd_def)

lemma remdups_tail_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ remdups_tail_pref) remdups_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix remdups_tail_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast  

lemma remdups_tail_IMP_Minus_correct_time:
  "(invoke_subprogram p remdups_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = remdups_tail_imp_time 0 (remdups_tail_imp_to_HOL_state p s)"
  apply(subst remdups_tail_imp_time.simps)
  apply(simp only: remdups_tail_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply(erule remdups_acc_IMP_Minus_correct[where vars = "remdups_tail_IMP_vars"])
  subgoal premises p using p(15) by fastforce
  apply(erule reverse_nat_IMP_Minus_correct[where vars = "remdups_tail_IMP_vars"])
  subgoal premises p using p(17) by fastforce
  by (fastforce simp add: Let_def remdups_tail_state_translators)

lemma remdups_tail_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) remdups_tail_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (remdups_tail_imp_time 0 (remdups_tail_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) remdups_tail_ret_str) =
          remdups_tail_ret (remdups_tail_imp
                                        (remdups_tail_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using remdups_tail_IMP_Minus_correct_function
    remdups_tail_IMP_Minus_correct_time
    remdups_tail_IMP_Minus_correct_effects
  by (meson set_mono_prefix)

subsubsection \<open>restrict_acc\<close>
paragraph restrict_aux
record restrict_aux_state = restrict_aux_acc::nat restrict_aux_l::nat restrict_aux_s::nat
abbreviation "restrict_aux_prefix \<equiv> ''restrict_aux.''"
abbreviation "restrict_aux_acc_str \<equiv> ''restrict_aux_acc''"
abbreviation "restrict_aux_l_str \<equiv> ''restrict_aux_l''"
abbreviation "restrict_aux_s_str \<equiv> ''restrict_aux_s''"

definition "restrict_aux_state_upd s \<equiv>
  (
    let
      hd_xs' = restrict_aux_l s;
      hd_ret' = 0;
      hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
      hd_ret_state = hd_imp hd_state;
      hd_result = hd_ret hd_ret_state;

      tl_xs' = restrict_aux_l s;
      tl_ret' = 0;
      tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
      tl_ret_state = tl_imp tl_state;
      tl_result = tl_ret tl_ret_state;

      fst'_state_p' = hd_result;
      fst'_state = \<lparr>fst'_state_p = fst'_state_p'\<rparr>;
      fst'_ret_state = fst'_imp fst'_state;
      fst'_result = fst'_state_p fst'_ret_state;

      elemof_e' = fst'_result;
      elemof_l' = restrict_aux_s s;
      elemof_ret' = 0;
      elemof_state = \<lparr>elemof_e = elemof_e', elemof_l = elemof_l', elemof_ret = elemof_ret'\<rparr>;
      elemof_ret_state = elemof_imp elemof_state;

      elemof_result = elemof_ret elemof_ret_state
    in
      (if elemof_result \<noteq> 0 then (
        let
          cons_h' = hd_result;
          cons_t' = restrict_aux_acc s;
          cons_ret' = 0;
          cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
          cons_ret_state = cons_imp cons_state;
          restrict_aux_acc' = cons_ret cons_ret_state;
          ret = \<lparr>restrict_aux_acc = restrict_aux_acc', 
                 restrict_aux_l = tl_result,
                 restrict_aux_s = restrict_aux_s s\<rparr>
        in 
          ret
      ) 
      else (
        let
          restrict_aux_acc' = restrict_aux_acc s;
          ret = \<lparr>restrict_aux_acc = restrict_aux_acc', 
                 restrict_aux_l = tl_result,
                 restrict_aux_s = restrict_aux_s s\<rparr>
        in 
          ret
      ))
  )"

lemmas restrict_aux_imp_subprogram_simps = 
  restrict_aux_state_upd_def

function restrict_aux_imp::
  "restrict_aux_state \<Rightarrow> restrict_aux_state" where
  "restrict_aux_imp s =
    (let 
      ret = restrict_aux_state_upd s
    in 
     ret)"
  by simp+
termination
  by (relation "measure (\<lambda>s. restrict_aux_acc s)") simp

declare restrict_aux_imp.simps [simp del]

lemma restrict_aux_imp_correct_acc[let_function_correctness]:
  "restrict_aux_acc (restrict_aux_imp s) =
    (if elemof (fst_nat (hd_nat (restrict_aux_l s))) (restrict_aux_s s) \<noteq> 0 then 
   (hd_nat (restrict_aux_l s))## (restrict_aux_acc s) else (restrict_aux_acc s))"
  apply (subst restrict_aux_imp.simps)
  apply (simp only: restrict_aux_state_upd_def elemof_imp_correct hd_imp_correct tl_imp_correct 
        fst'_imp_correct cons_imp_correct Let_def split: if_splits)
  by (metis cons_state.select_convs(1) cons_state.select_convs(2) elemof_state.select_convs(1) 
  elemof_state.select_convs(2) fst'_state.select_convs(1) 
  fst_nat_fst'_nat hd_state.select_convs(1) restrict_aux_state.select_convs(1))

lemma restrict_aux_imp_correct_l[let_function_correctness]:
  "restrict_aux_l (restrict_aux_imp s) = (tl_nat (restrict_aux_l s))"
  apply (subst restrict_aux_imp.simps)
  apply (simp only: restrict_aux_state_upd_def elemof_imp_correct hd_imp_correct tl_imp_correct 
        fst'_imp_correct cons_imp_correct Let_def split: if_splits) 
  by (metis restrict_aux_state.select_convs(2) tl_state.select_convs(1))


lemma restrict_aux_imp_correct_s[let_function_correctness]:
  "restrict_aux_s (restrict_aux_imp s) = (restrict_aux_s s)"
  apply (subst restrict_aux_imp.simps)
  apply (simp only: restrict_aux_state_upd_def elemof_imp_correct hd_imp_correct tl_imp_correct 
        fst'_imp_correct cons_imp_correct Let_def split: if_splits) 
  by (meson restrict_aux_state.select_convs(3))

definition "restrict_aux_state_upd_time t s \<equiv>
  (
    let
      hd_xs' = restrict_aux_l s;
      t = t + 2;
      hd_ret' = 0;
      t = t + 2;
      hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
      hd_ret_state = hd_imp hd_state;
      t = t + hd_imp_time 0 hd_state;
      hd_result = hd_ret hd_ret_state;
      t = t + 2;

      tl_xs' = restrict_aux_l s;
      t = t + 2;
      tl_ret' = 0;
      t = t + 2;
      tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
      tl_ret_state = tl_imp tl_state;
      t = t + tl_imp_time 0 tl_state;
      tl_result = tl_ret tl_ret_state;
      t = t + 2;

      fst'_state_p' = hd_result;
      t = t + 2;
      fst'_state = \<lparr>fst'_state_p = fst'_state_p'\<rparr>;
      fst'_ret_state = fst'_imp fst'_state;
      t = t + fst'_imp_time 0 fst'_state;
      fst'_result = fst'_state_p fst'_ret_state;
      t = t + 2;
      elemof_e' = fst'_result;
      t = t + 2;
      elemof_l' = restrict_aux_s s;
      t = t + 2;
      elemof_ret' = 0;
      t = t + 2;
      elemof_state = \<lparr>elemof_e = elemof_e', elemof_l = elemof_l', elemof_ret = elemof_ret'\<rparr>;
      elemof_ret_state = elemof_imp elemof_state;
      t = t + elemof_imp_time 0 elemof_state;
      elemof_result = elemof_ret elemof_ret_state;
      t = t + 2
    in
      (if elemof_result \<noteq> 0 then (
        let
          t = t + 1;
          cons_h' = hd_result;
          t = t + 2;
          cons_t' = restrict_aux_acc s;
          t = t + 2;
          cons_ret' = 0;
          t = t + 2;
          cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
          cons_ret_state = cons_imp cons_state;
          t = t + cons_imp_time 0 cons_state;
          restrict_aux_acc' = cons_ret cons_ret_state;
          t = t + 2;
          restrict_aux_l' = tl_result;
          t = t + 2;
          ret = \<lparr>restrict_aux_acc = restrict_aux_acc', 
                 restrict_aux_l = restrict_aux_l',
                 restrict_aux_s = restrict_aux_s s\<rparr>
        in 
          t
      ) 
      else (
        let
          t = t + 1;
          restrict_aux_l' = tl_result;
          t = t + 2;
          ret = \<lparr>restrict_aux_acc = restrict_aux_acc s, 
                 restrict_aux_l = restrict_aux_l',
                 restrict_aux_s = restrict_aux_s s\<rparr>
        in 
          t
      )))
"

lemmas restrict_aux_imp_subprogram_time_simps = 
  restrict_aux_state_upd_time_def
  restrict_aux_imp_subprogram_simps

function restrict_aux_imp_time::
  "nat \<Rightarrow> restrict_aux_state \<Rightarrow> nat" where
  "restrict_aux_imp_time t s = 
    (let 
      ret = t + restrict_aux_state_upd_time 0 s
    in
      ret)"
  by auto
termination
  by (relation "measure (\<lambda>(t, s). restrict_aux_acc s)") simp

declare restrict_aux_imp_time.simps [simp del]            

lemma restrict_aux_imp_time_acc:
  "(restrict_aux_imp_time (Suc t) s) = Suc (restrict_aux_imp_time t s)"
  by (induction t s rule: restrict_aux_imp_time.induct)
    ((subst (1 2) restrict_aux_imp_time.simps);
      (simp add: restrict_aux_state_upd_def))            

lemma restrict_aux_imp_time_acc_2_aux:
  "(restrict_aux_imp_time t s) = t + (restrict_aux_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: restrict_aux_imp_time_acc)+            

lemma restrict_aux_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (restrict_aux_imp_time t s) = t + (restrict_aux_imp_time 0 s)"
  by (rule restrict_aux_imp_time_acc_2_aux)            

lemma restrict_aux_imp_time_acc_3:
  "(restrict_aux_imp_time (a + b) s) = a + (restrict_aux_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: restrict_aux_imp_time_acc)+            


abbreviation "restrict_aux_hd_result \<equiv> ''restrict_aux_hd_result''"
abbreviation "restrict_aux_tl_result \<equiv> ''restrict_aux_tl_resultt''"
abbreviation "restrict_aux_elemof_result \<equiv> ''restrict_aux_elemof_resultt''"
abbreviation "restrict_aux_fst'_result \<equiv> ''restrict_aux_fst'_result''"

abbreviation "restrict_aux_IMP_if \<equiv> 
  \<comment> \<open>    let\<close>
  \<comment> \<open>      cons_h' = hd_result;\<close>
  (cons_prefix @ cons_h_str) ::= A (V restrict_aux_hd_result);;
  \<comment> \<open>      cons_t' = restrict_aux_acc s;\<close>
  (cons_prefix @ cons_t_str) ::= A (V restrict_aux_acc_str);;
  \<comment> \<open>      cons_ret' = 0;\<close>
  (cons_prefix @ cons_ret_str) ::= A (N 0);;
  \<comment> \<open>      cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>      cons_ret_state = cons_imp cons_state;\<close>
  invoke_subprogram cons_prefix cons_IMP_Minus;;
  \<comment> \<open>      restrict_aux_acc' = cons_ret cons_ret_state;\<close>
  restrict_aux_acc_str ::= A (V (cons_prefix @ cons_ret_str));;
  \<comment>\<open>       restrict_aux_l' = tl_result;\<close>
  restrict_aux_l_str ::= A (V restrict_aux_tl_result)
  \<comment> \<open>      ret = \<lparr>restrict_aux_acc = restrict_aux_acc', \<close>
  \<comment> \<open>             restrict_aux_l = restrict_aux_l',\<close>
  \<comment> \<open>             restrict_aux_s = restrict_aux_s'\<rparr>\<close>"

abbreviation "restrict_aux_IMP_else \<equiv> 
  restrict_aux_l_str ::= A (V restrict_aux_tl_result)
  \<comment>\<open>restrict_aux_l' = restrict_aux_l s;
          ret = \<lparr>restrict_aux_acc = restrict_aux_acc s, 
                 restrict_aux_l = restrict_aux_l'
                 restrict_aux_s = restrict_aux_s s\<rparr>\<close> "

definition "restrict_aux_IMP_Minus \<equiv>
  \<comment> \<open>let\<close>
  \<comment> \<open>  hd_xs' = restrict_aux_l s;\<close>
  (hd_prefix @ hd_xs_str) ::= A (V restrict_aux_l_str);;
  \<comment> \<open>  hd_ret' = 0;\<close>
  (hd_prefix @ hd_ret_str) ::= A (N 0);;
  \<comment> \<open>  hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;\<close>
  \<comment> \<open>  hd_ret_state = hd_imp hd_state;\<close>
  invoke_subprogram hd_prefix hd_IMP_Minus;;
  \<comment> \<open>  fst'_state_p' = hd_ret hd_ret_state;\<close>
  \<comment> \<open>\<close>
  (restrict_aux_hd_result) ::= A (V (hd_prefix @ hd_ret_str));;
  \<comment> \<open>  tl_xs' = restrict_aux_l s;\<close>
  (tl_prefix @ tl_xs_str) ::= A (V (restrict_aux_l_str));;
  \<comment> \<open>  tl_ret' = 0;\<close>
  (tl_prefix @ tl_ret_str) ::= A (N 0);;
  \<comment> \<open>  tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;\<close>
  \<comment> \<open>  tl_ret_state = tl_imp tl_state;\<close>
  invoke_subprogram tl_prefix tl_IMP_Minus;;
  (restrict_aux_tl_result) ::= A (V (tl_prefix @ tl_ret_str));;

  \<comment> \<open> fst'_state_p' = hd_result;\<close>
  (fst'_prefix @ fst'_p_str) ::= A (V restrict_aux_hd_result);;
  \<comment> \<open>  fst'_state = \<lparr>fst'_state_p = fst'_state_p'\<rparr>;\<close>
  \<comment> \<open>  fst'_ret_state = fst'_imp fst'_state;\<close>
  invoke_subprogram fst'_prefix fst'_IMP_Minus;;
  \<comment> \<open>\<close>
  \<comment> \<open>  elemof_e' = fst'_state_p fst'_ret_state;\<close>
  restrict_aux_fst'_result ::= A (V (fst'_prefix @ fst'_p_str));;
  (elemof_prefix @ elemof_e_str) ::= A (V restrict_aux_fst'_result);;
  \<comment> \<open>  elemof_l' = restrict_aux_s s;\<close>
  (elemof_prefix @ elemof_l_str) ::= A (V restrict_aux_s_str);;
  \<comment> \<open>  elemof_ret' = 0;\<close>
  (elemof_prefix @ elemof_ret_str) ::= A (N 0);;
  \<comment> \<open>  elemof_state = \<lparr>elemof_e = elemof_e', elemof_l = elemof_l', elemof_ret = elemof_ret'\<rparr>;\<close>
  \<comment> \<open>  elemof_ret_state = elemof_imp elemof_state;\<close>
  \<comment> \<open>\<close>
  invoke_subprogram elemof_prefix elemof_IMP_Minus;;
  \<comment> \<open>  elemof_ret' = elemof_ret elemof_ret_state\<close>
  (restrict_aux_elemof_result) ::= A (V (elemof_prefix @ elemof_ret_str));;
  \<comment> \<open>in\<close>
  \<comment> \<open>  (if elemof_ret' \<noteq> 0 then (\<close>
  (IF restrict_aux_elemof_result \<noteq>0 THEN  
    restrict_aux_IMP_if
  ELSE 
    restrict_aux_IMP_else)
"

abbreviation "restrict_aux_IMP_vars \<equiv>
  {restrict_aux_acc_str, restrict_aux_l_str, restrict_aux_s_str,
   restrict_aux_hd_result, restrict_aux_tl_result, restrict_aux_elemof_result,
   restrict_aux_fst'_result}"

lemmas restrict_aux_IMP_subprogram_simps =
  restrict_aux_IMP_Minus_def

definition "restrict_aux_imp_to_HOL_state p s =
  \<lparr>restrict_aux_acc = (s (add_prefix p restrict_aux_acc_str)),
   restrict_aux_l = (s (add_prefix p restrict_aux_l_str)),
   restrict_aux_s = (s (add_prefix p restrict_aux_s_str))\<rparr>"

lemmas restrict_aux_state_translators =
  restrict_aux_imp_to_HOL_state_def
  hd_imp_to_HOL_state_def
  tl_imp_to_HOL_state_def
  fst'_imp_to_HOL_state_def
  elemof_imp_to_HOL_state_def

lemmas restrict_aux_complete_simps =
  restrict_aux_IMP_subprogram_simps
  restrict_aux_imp_subprogram_simps
  restrict_aux_state_translators

lemma restrict_aux_IMP_Minus_correct_function_acc:
  "(invoke_subprogram p restrict_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p restrict_aux_acc_str)
      = restrict_aux_acc
          (restrict_aux_imp (restrict_aux_imp_to_HOL_state p s))"
  apply (subst restrict_aux_imp.simps)
  apply (simp only: restrict_aux_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule hd_IMP_Minus_correct[where vars=restrict_aux_IMP_vars])
  subgoal premises p using p(17) by fastforce
  apply (erule tl_IMP_Minus_correct[where vars=restrict_aux_IMP_vars])
  subgoal premises p using p(19) by fastforce
  apply (erule fst'_IMP_Minus_correct[where vars=restrict_aux_IMP_vars])
  subgoal premises p using p(21) by fastforce
  apply (erule elemof_IMP_Minus_correct[where vars=restrict_aux_IMP_vars])
  subgoal premises p using p(23) by fastforce
  apply (erule If_E)
  subgoal 
    apply (erule Seq_E)+
    apply (erule cons_IMP_Minus_correct[where vars=restrict_aux_IMP_vars])
    subgoal premises p using p(31) by fastforce
    apply (fastforce_sorted_premises2 simp: restrict_aux_state_upd_def Let_def
      restrict_aux_state_translators cons_imp_to_HOL_state_def)
    done
  subgoal
    apply (fastforce_sorted_premises2 simp: restrict_aux_state_upd_def Let_def
      restrict_aux_state_translators)
    done
  done

lemma restrict_aux_IMP_Minus_correct_function_l:
  "(invoke_subprogram p restrict_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p restrict_aux_l_str)
      = restrict_aux_l
          (restrict_aux_imp (restrict_aux_imp_to_HOL_state p s))"
  apply (subst restrict_aux_imp.simps)
  apply (simp only: restrict_aux_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule hd_IMP_Minus_correct[where vars=restrict_aux_IMP_vars])
  subgoal premises p using p(17) by fastforce
  apply (erule tl_IMP_Minus_correct[where vars=restrict_aux_IMP_vars])
  subgoal premises p using p(19) by fastforce
  apply (erule fst'_IMP_Minus_correct[where vars=restrict_aux_IMP_vars])
  subgoal premises p using p(21) by fastforce
  apply (erule elemof_IMP_Minus_correct[where vars=restrict_aux_IMP_vars])
  subgoal premises p using p(23) by fastforce
  apply (erule If_E)
  subgoal 
    apply (erule Seq_E)+
    apply (erule cons_IMP_Minus_correct[where vars=restrict_aux_IMP_vars])
    subgoal premises p using p(31) by fastforce
    apply (fastforce_sorted_premises2 simp: restrict_aux_state_upd_def Let_def
      restrict_aux_state_translators cons_imp_to_HOL_state_def)
    done
  subgoal
    apply (fastforce_sorted_premises2 simp: restrict_aux_state_upd_def Let_def
      restrict_aux_state_translators)
    done
  done

lemma restrict_aux_IMP_Minus_correct_function_s:
  "(invoke_subprogram p restrict_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p restrict_aux_s_str)
      = restrict_aux_s
          (restrict_aux_imp (restrict_aux_imp_to_HOL_state p s))"
  apply (subst restrict_aux_imp.simps)
  apply (simp only: restrict_aux_IMP_Minus_def prefix_simps)
  apply (erule Seq_E)+
  apply (erule hd_IMP_Minus_correct[where vars=restrict_aux_IMP_vars])
  subgoal premises p using p(17) by fastforce
  apply (erule tl_IMP_Minus_correct[where vars=restrict_aux_IMP_vars])
  subgoal premises p using p(19) by fastforce
  apply (erule fst'_IMP_Minus_correct[where vars=restrict_aux_IMP_vars])
  subgoal premises p using p(21) by fastforce
  apply (erule elemof_IMP_Minus_correct[where vars=restrict_aux_IMP_vars])
  subgoal premises p using p(23) by fastforce
  apply (erule If_E)
  subgoal 
    apply (erule Seq_E)+
    apply (erule cons_IMP_Minus_correct[where vars=restrict_aux_IMP_vars])
    subgoal premises p using p(31) by fastforce
    apply (fastforce_sorted_premises2 simp: restrict_aux_state_upd_def Let_def
      restrict_aux_state_translators cons_imp_to_HOL_state_def)
    done
  subgoal
    apply (fastforce_sorted_premises2 simp: restrict_aux_state_upd_def Let_def
      restrict_aux_state_translators)
    done
  done

lemma restrict_aux_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ restrict_aux_pref) restrict_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix restrict_aux_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemma restrict_aux_IMP_Minus_correct_time:
  "(invoke_subprogram p restrict_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = restrict_aux_imp_time 0 (restrict_aux_imp_to_HOL_state p s)"
  apply (subst restrict_aux_imp_time.simps)
  apply (simp only: restrict_aux_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule hd_IMP_Minus_correct[where vars=restrict_aux_IMP_vars])
  subgoal premises p using p(33) by fastforce
  apply (erule tl_IMP_Minus_correct[where vars=restrict_aux_IMP_vars])
  subgoal premises p using p(35) by fastforce
  apply (erule fst'_IMP_Minus_correct[where vars=restrict_aux_IMP_vars])
  subgoal premises p using p(37) by fastforce
  apply (erule elemof_IMP_Minus_correct[where vars=restrict_aux_IMP_vars])
  subgoal premises p using p(39) by fastforce
  apply (erule If_tE)
  subgoal 
    apply (erule Seq_tE)+
    apply (erule cons_IMP_Minus_correct[where vars=restrict_aux_IMP_vars])
    subgoal premises p using p(53) by fastforce
    apply (fastforce_sorted_premises2 simp: restrict_aux_state_upd_time_def Let_def
      restrict_aux_state_translators cons_imp_to_HOL_state_def)
    done
  subgoal
    apply (fastforce_sorted_premises2 simp: restrict_aux_state_upd_time_def Let_def
      restrict_aux_state_translators)
    done
  done      

lemma restrict_aux_IMP_Minus_correct_acc:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) restrict_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (restrict_aux_imp_time 0 (restrict_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) restrict_aux_acc_str) =
          restrict_aux_acc (restrict_aux_imp
                                        (restrict_aux_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using restrict_aux_IMP_Minus_correct_function_acc
  by (auto simp: restrict_aux_IMP_Minus_correct_time)
    (meson restrict_aux_IMP_Minus_correct_effects set_mono_prefix) 

lemma restrict_aux_IMP_Minus_correct_l:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) restrict_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (restrict_aux_imp_time 0 (restrict_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) restrict_aux_l_str) =
          restrict_aux_l (restrict_aux_imp
                                        (restrict_aux_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using restrict_aux_IMP_Minus_correct_function_l
  by (auto simp: restrict_aux_IMP_Minus_correct_time)
    (meson restrict_aux_IMP_Minus_correct_effects set_mono_prefix)

lemma restrict_aux_IMP_Minus_correct_s:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) restrict_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (restrict_aux_imp_time 0 (restrict_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) restrict_aux_s_str) =
          restrict_aux_s (restrict_aux_imp
                                        (restrict_aux_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using restrict_aux_IMP_Minus_correct_function_s
  by (auto simp: restrict_aux_IMP_Minus_correct_time)
    (meson restrict_aux_IMP_Minus_correct_effects set_mono_prefix)

lemma restrict_aux_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) restrict_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (restrict_aux_imp_time 0 (restrict_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) restrict_aux_acc_str) =
          restrict_aux_acc (restrict_aux_imp
                                        (restrict_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) restrict_aux_l_str) =
          restrict_aux_l (restrict_aux_imp
                                        (restrict_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) restrict_aux_s_str) =
          restrict_aux_s (restrict_aux_imp
                                        (restrict_aux_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
   using restrict_aux_IMP_Minus_correct_acc 
     restrict_aux_IMP_Minus_correct_l restrict_aux_IMP_Minus_correct_s
     by (smt (verit, del_insts))

paragraph restrict_acc
record restrict_acc_state = restrict_acc_acc::nat restrict_acc_l::nat restrict_acc_s::nat restrict_acc_ret::nat

abbreviation "restrict_acc_prefix \<equiv> ''restrict_acc.''"
abbreviation "restrict_acc_acc_str \<equiv> ''restrict_acc_acc''"
abbreviation "restrict_acc_l_str \<equiv> ''restrict_acc_l''"
abbreviation "restrict_acc_s_str \<equiv> ''restrict_acc_s''"
abbreviation "restrict_acc_ret_str \<equiv> ''restrict_acc_ret''"

definition "restrict_acc_state_upd s \<equiv> 
  (let
    restrict_aux_acc' = restrict_acc_acc s;
    restrict_aux_l' = restrict_acc_l s;
    restrict_aux_s' = restrict_acc_s s;
    restrict_aux_state = \<lparr>restrict_aux_acc = restrict_aux_acc',
                          restrict_aux_l = restrict_aux_l',
                          restrict_aux_s = restrict_aux_s'\<rparr>;
    restrict_aux_ret_state = restrict_aux_imp restrict_aux_state;
    restrict_acc_acc' = restrict_aux_acc restrict_aux_ret_state;
    restrict_acc_l' = restrict_aux_l restrict_aux_ret_state;
    restrict_acc_s' = restrict_aux_s restrict_aux_ret_state;
    ret = \<lparr>restrict_acc_acc = restrict_aux_acc restrict_aux_ret_state,
           restrict_acc_l = restrict_aux_l restrict_aux_ret_state,
           restrict_acc_s = restrict_aux_s restrict_aux_ret_state,
           restrict_acc_ret = restrict_acc_ret s\<rparr>
  in
    ret)"

definition "restrict_acc_imp_compute_loop_condition s \<equiv> (
  let
    condition = restrict_acc_l s
  in
  condition
)"

definition "restrict_acc_imp_after_loop s \<equiv> (
  let
   restrict_acc_ret' = restrict_acc_acc s;
   ret = \<lparr>restrict_acc_acc = restrict_acc_acc s,
          restrict_acc_l = restrict_acc_l s,
          restrict_acc_s = restrict_acc_s s,
          restrict_acc_ret = restrict_acc_acc s\<rparr>
  in
    ret
)"

lemmas restrict_acc_imp_subprogram_simps = 
  restrict_acc_state_upd_def
  restrict_acc_imp_compute_loop_condition_def
  restrict_acc_imp_after_loop_def

function restrict_acc_imp::
  "restrict_acc_state \<Rightarrow> restrict_acc_state" where
  "restrict_acc_imp s =
  (if restrict_acc_imp_compute_loop_condition s \<noteq> 0
   then
    let next_iteration = restrict_acc_imp (restrict_acc_state_upd s)
    in next_iteration
   else
    let ret = restrict_acc_imp_after_loop s
    in ret
  )"
  by simp+
termination
  apply (relation "measure restrict_acc_l")
  apply (simp add: restrict_acc_imp_subprogram_simps restrict_aux_imp_correct_l Let_def)+
  done

declare restrict_acc_imp.simps [simp del]

lemma restrict_acc_imp_correct:
  "restrict_acc_ret (restrict_acc_imp s) =
    restrict_acc (restrict_acc_acc s) (restrict_acc_l s) (restrict_acc_s s)"
  apply (induction s rule: restrict_acc_imp.induct)
  apply (subst restrict_acc_imp.simps)
  apply (subst restrict_acc.simps)
  apply (simp del: restrict_acc.simps only: restrict_acc_imp_subprogram_simps Let_def
  restrict_aux_imp_correct_acc restrict_aux_imp_correct_l restrict_aux_imp_correct_s)
  by (smt (z3) restrict_acc_state.select_convs(1) restrict_acc_state.select_convs(2) 
  restrict_acc_state.select_convs(3) restrict_acc_state.select_convs(4) 
  restrict_aux_state.select_convs(1) restrict_aux_state.select_convs(2) 
  restrict_aux_state.select_convs(3)) 

definition "restrict_acc_state_upd_time t s \<equiv>
  let
    restrict_aux_acc' = restrict_acc_acc s;
    t = t + 2;
    restrict_aux_l' = restrict_acc_l s;
    t = t + 2;
    restrict_aux_s' = restrict_acc_s s;
    t = t + 2;
    restrict_aux_state = \<lparr>restrict_aux_acc = restrict_aux_acc',
                          restrict_aux_l = restrict_aux_l',
                          restrict_aux_s = restrict_aux_s'\<rparr>;
    restrict_aux_ret_state = restrict_aux_imp restrict_aux_state;
    t = t + restrict_aux_imp_time 0 restrict_aux_state;
    restrict_acc_acc' = restrict_aux_acc restrict_aux_ret_state;
    t = t + 2;
    restrict_acc_l' = restrict_aux_l restrict_aux_ret_state;
    t = t + 2;
    restrict_acc_s' = restrict_aux_s restrict_aux_ret_state;
    t = t + 2;
    ret = \<lparr>restrict_acc_acc = restrict_acc_acc',
           restrict_acc_l = restrict_acc_l',
           restrict_acc_s = restrict_acc_s',
           restrict_acc_ret = restrict_acc_ret s\<rparr>
  in
    t
"

definition "restrict_acc_imp_compute_loop_condition_time t s \<equiv>
  let
    condition = restrict_acc_l s;
    t = t + 2
  in
    t
"

definition "restrict_acc_imp_after_loop_time t s \<equiv>
 let
   restrict_acc_ret' = restrict_acc_acc s;
   t = t + 2;
   ret = \<lparr>restrict_acc_acc = restrict_acc_acc s,
          restrict_acc_l = restrict_acc_l s,
          restrict_acc_s = restrict_acc_s s,
          restrict_acc_ret = restrict_acc_acc s\<rparr>
  in
    t
"

lemmas restrict_acc_imp_subprogram_time_simps = 
  restrict_acc_state_upd_time_def
  restrict_acc_imp_compute_loop_condition_time_def
  restrict_acc_imp_after_loop_time_def
  restrict_acc_imp_subprogram_simps

function restrict_acc_imp_time::
  "nat \<Rightarrow> restrict_acc_state \<Rightarrow> nat" where
  "restrict_acc_imp_time t s =
  restrict_acc_imp_compute_loop_condition_time 0 s +
  (if restrict_acc_imp_compute_loop_condition s \<noteq> 0
    then
      (let
        t = t + 1;
        next_iteration =
          restrict_acc_imp_time (t + restrict_acc_state_upd_time 0 s)
                         (restrict_acc_state_upd s)
       in next_iteration)
    else
      (let
        t = t + 2;
        ret = t + restrict_acc_imp_after_loop_time 0 s
       in ret)
  )"
  by auto
termination
  apply (relation "measure (restrict_acc_l \<circ> snd)")
  apply (simp add: restrict_acc_imp_subprogram_time_simps
     restrict_aux_imp_correct_l Let_def)+
  done

declare restrict_acc_imp_time.simps [simp del]            

lemma restrict_acc_imp_time_acc:
  "(restrict_acc_imp_time (Suc t) s) = Suc (restrict_acc_imp_time t s)"
  by (induction t s rule: restrict_acc_imp_time.induct)
    ((subst (1 2) restrict_acc_imp_time.simps);
      (simp add: restrict_acc_state_upd_def))            

lemma restrict_acc_imp_time_acc_2_aux:
  "(restrict_acc_imp_time t s) = t + (restrict_acc_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: restrict_acc_imp_time_acc)+            

lemma restrict_acc_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (restrict_acc_imp_time t s) = t + (restrict_acc_imp_time 0 s)"
  by (rule restrict_acc_imp_time_acc_2_aux)            

lemma restrict_acc_imp_time_acc_3:
  "(restrict_acc_imp_time (a + b) s) = a + (restrict_acc_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: restrict_acc_imp_time_acc)+            

abbreviation "restrict_acc_while_cond \<equiv> ''restrict_acc_condition''"

definition "restrict_acc_IMP_init_while_cond \<equiv>
  \<comment>\<open>condition = restrict_acc_l s\<close>
  restrict_acc_while_cond ::= A (V restrict_acc_l_str)
"

definition "restrict_acc_IMP_loop_body \<equiv>
  \<comment>\<open>  restrict_aux_acc' = restrict_acc_acc s;\<close>
  (restrict_aux_prefix @ restrict_aux_acc_str) ::= A (V restrict_acc_acc_str);;
  \<comment>\<open>  restrict_aux_l' = restrict_acc_l s;\<close>
  (restrict_aux_prefix @ restrict_aux_l_str) ::= A (V restrict_acc_l_str);;
  \<comment>\<open>  restrict_aux_s' = restrict_acc_s s;\<close>
  (restrict_aux_prefix @ restrict_aux_s_str) ::= A (V restrict_acc_s_str);;
  \<comment>\<open>  restrict_aux_state = \<lparr>restrict_aux_acc = restrict_aux_acc',
                          restrict_aux_l = restrict_aux_l',
                          restrict_aux_s = restrict_aux_s'\<rparr>;\<close>
  \<comment>\<open>  restrict_aux_ret_state = restrict_aux_imp restrict_aux_state;\<close>
  invoke_subprogram restrict_aux_prefix restrict_aux_IMP_Minus;;
  \<comment>\<open>  restrict_acc_acc' = restrict_aux_acc restrict_aux_ret_state;\<close>
  (restrict_acc_acc_str) ::= A (V (restrict_aux_prefix @ restrict_aux_acc_str));;
  \<comment>\<open>  restrict_acc_l' = restrict_aux_l restrict_aux_ret_state;\<close>
  (restrict_acc_l_str) ::= A (V (restrict_aux_prefix @ restrict_aux_l_str));;
  \<comment>\<open>  restrict_acc_s' = restrict_aux_s restrict_aux_ret_state;\<close>
  (restrict_acc_s_str) ::= A (V (restrict_aux_prefix @ restrict_aux_s_str))
  \<comment>\<open>  ret = \<lparr>restrict_acc_acc = restrict_acc_acc',
           restrict_acc_l = restrict_acc_l',
           restrict_acc_s = restrict_acc_s',
           restrict_acc_ret = restrict_acc_ret s\<rparr>\<close>
"

definition "restrict_acc_IMP_after_loop \<equiv>
  \<comment>\<open>restrict_acc_ret' = restrict_acc_acc s;\<close>
  restrict_acc_ret_str ::= A (V restrict_acc_acc_str)
  \<comment>\<open>ret = \<lparr>restrict_acc_acc = restrict_acc_acc s,
          restrict_acc_l = restrict_acc_l s,
          restrict_acc_s = restrict_acc_s s,
          restrict_acc_ret = restrict_acc_acc s\<rparr>\<close>
"

definition restrict_acc_IMP_Minus where
  "restrict_acc_IMP_Minus \<equiv>
  restrict_acc_IMP_init_while_cond;;
  WHILE restrict_acc_while_cond \<noteq>0 DO (
    restrict_acc_IMP_loop_body;;
    restrict_acc_IMP_init_while_cond
  );;
  restrict_acc_IMP_after_loop"

abbreviation "restrict_acc_IMP_vars\<equiv>
  {restrict_acc_acc_str, restrict_acc_l_str, restrict_acc_s_str, 
  restrict_acc_ret_str, restrict_acc_while_cond}"

lemmas restrict_acc_IMP_subprogram_simps =
  restrict_acc_IMP_init_while_cond_def
  restrict_acc_IMP_loop_body_def
  restrict_acc_IMP_after_loop_def

definition "restrict_acc_imp_to_HOL_state p s =
  \<lparr>restrict_acc_acc = (s (add_prefix p restrict_acc_acc_str)),
   restrict_acc_l = (s (add_prefix p restrict_acc_l_str)),
   restrict_acc_s = (s (add_prefix p restrict_acc_s_str)),
   restrict_acc_ret = (s (add_prefix p restrict_acc_ret_str))\<rparr>"

lemmas restrict_acc_state_translators =
  restrict_acc_imp_to_HOL_state_def
  restrict_aux_imp_to_HOL_state_def

lemmas restrict_acc_complete_simps =
  restrict_acc_IMP_subprogram_simps
  restrict_acc_imp_subprogram_simps
  restrict_acc_state_translators

lemma restrict_acc_IMP_Minus_correct_function:
  "(invoke_subprogram p restrict_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p restrict_acc_ret_str)
      = restrict_acc_ret
          (restrict_acc_imp (restrict_acc_imp_to_HOL_state p s))"
  apply(induction "restrict_acc_imp_to_HOL_state p s" arbitrary: s s' t
    rule: restrict_acc_imp.induct)
  apply(subst restrict_acc_imp.simps)
  apply(simp only: restrict_acc_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule While_tE)

  subgoal
    by(fastforce simp: restrict_acc_IMP_subprogram_simps
        restrict_acc_imp_subprogram_simps
        restrict_acc_state_translators)

  apply(erule Seq_E)+
  apply(dest_com_gen)

  subgoal
      by(fastforce simp add: restrict_acc_complete_simps)

  subgoal
      apply(subst (asm) restrict_acc_IMP_init_while_cond_def)
      apply(simp only: restrict_acc_IMP_loop_body_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule restrict_aux_IMP_Minus_correct[where vars = "restrict_acc_IMP_vars"])
      subgoal premises p using p(12) by fastforce
      apply (simp only: restrict_acc_imp_subprogram_simps
          restrict_acc_state_translators Let_def)
      apply force
      done

  subgoal
      apply(simp only: restrict_acc_IMP_init_while_cond_def prefix_simps
          restrict_acc_IMP_loop_body_def)
      apply(erule Seq_E)+
      apply(erule restrict_aux_IMP_Minus_correct[where vars = "restrict_acc_IMP_vars"])
      subgoal premises p using p(12) by fastforce
      apply (simp only: restrict_acc_imp_subprogram_simps
          restrict_acc_state_translators Let_def)
      apply force
      done
  done        

lemma restrict_acc_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ restrict_acc_pref) restrict_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix restrict_acc_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemmas restrict_acc_complete_time_simps =
  restrict_acc_imp_subprogram_time_simps
  restrict_acc_imp_time_acc
  restrict_acc_imp_time_acc_2
  restrict_acc_imp_time_acc_3
  restrict_acc_state_translators

lemma restrict_acc_IMP_Minus_correct_time:
  "(invoke_subprogram p restrict_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = restrict_acc_imp_time 0 (restrict_acc_imp_to_HOL_state p s)"
  apply(induction "restrict_acc_imp_to_HOL_state p s" arbitrary: s s' t
      rule: restrict_acc_imp.induct)
  apply(subst restrict_acc_imp_time.simps)
  apply(simp only: restrict_acc_IMP_Minus_def prefix_simps)

  apply(erule Seq_tE)+
  apply(erule While_tE_time)

  subgoal
    apply(simp only: restrict_acc_IMP_subprogram_simps prefix_simps)
    by (force simp: restrict_acc_IMP_subprogram_simps
        restrict_acc_imp_subprogram_time_simps restrict_acc_state_translators)

  apply(erule Seq_tE)+
  apply(simp add: add.assoc)
  apply(dest_com_gen_time)

  subgoal
    apply(simp only: restrict_acc_IMP_init_while_cond_def prefix_simps)
    by(fastforce simp add: restrict_acc_complete_simps)

  subgoal
    apply(subst (asm) restrict_acc_IMP_init_while_cond_def)
    apply(simp only: restrict_acc_IMP_loop_body_def prefix_simps)
    apply(erule Seq_tE)+
    apply(erule restrict_aux_IMP_Minus_correct[where vars = "restrict_acc_IMP_vars"])
    subgoal premises p using p(21) by fastforce
    by (simp only: restrict_acc_imp_subprogram_time_simps
        restrict_acc_state_translators Let_def, force)

  subgoal
    apply(simp only: prefix_simps restrict_acc_IMP_init_while_cond_def
        restrict_acc_IMP_loop_body_def)
    apply(erule Seq_tE)+
    apply(erule restrict_aux_IMP_Minus_correct[where vars = "restrict_acc_IMP_vars"])
    subgoal premises p using p(21) by fastforce
    apply(simp only: restrict_acc_complete_time_simps Let_def)
    apply force
    done

  done        

lemma restrict_acc_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) restrict_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (restrict_acc_imp_time 0 (restrict_acc_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) restrict_acc_ret_str) =
          restrict_acc_ret (restrict_acc_imp
                                        (restrict_acc_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using restrict_acc_IMP_Minus_correct_function
  by (auto simp: restrict_acc_IMP_Minus_correct_time)
    (meson restrict_acc_IMP_Minus_correct_effects set_mono_prefix) 

section \<open>Logic, continued\<close>
text \<open>This is a structural issue to be handled, for elemof uses logical operations
BigAnd uses the cons of lists
\<close>

subsection\<open>BigAnd\<close>
subsubsection \<open>BigAnd\<close>
paragraph BigAnd_aux

record BigAnd_aux_state = BigAnd_aux_acc::nat BigAnd_aux_xs::nat BigAnd_aux_ret::nat

abbreviation "BigAnd_aux_prefix \<equiv> ''BigAnd_aux.''"
abbreviation "BigAnd_aux_acc_str \<equiv> ''acc''"
abbreviation "BigAnd_aux_xs_str \<equiv> ''xs''"
abbreviation "BigAnd_aux_ret_str \<equiv> ''ret''"

definition "BigAnd_aux_state_upd s \<equiv> 
  (let
    cons_h' = BigAnd_aux_acc s;
    cons_t' = 0;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    hd_xs' = BigAnd_aux_xs s;
    hd_ret' = 0;
    hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;
    hd_ret_state = hd_imp hd_state;

    cons_h' = hd_ret hd_ret_state;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    cons_h' = 3;
    cons_t' = cons_ret cons_ret_state;
    cons_ret' = 0;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    BigAnd_aux_ret' = cons_ret cons_ret_state;
    ret = \<lparr>BigAnd_aux_acc = BigAnd_aux_acc s, 
          BigAnd_aux_xs = BigAnd_aux_xs s, 
          BigAnd_aux_ret = BigAnd_aux_ret'
          \<rparr>
    in
      ret
  )"

lemmas BigAnd_aux_imp_subprogram_simps = 
  BigAnd_aux_state_upd_def

function BigAnd_aux_imp::
  "BigAnd_aux_state \<Rightarrow> BigAnd_aux_state" where
  "BigAnd_aux_imp s =
  (let
     next_iteration = BigAnd_aux_state_upd s
    in 
     next_iteration)"
  by simp+
termination
  apply (relation "measure (\<lambda>s. BigAnd_aux_acc s)")
  apply simp
  done

declare BigAnd_aux_imp.simps [simp del]

lemma BigAnd_aux_imp_correct:
  "BigAnd_aux_ret (BigAnd_aux_imp s) =
   3 ## (hd_nat (BigAnd_aux_xs s)) ## (BigAnd_aux_acc s) ## 0"
  apply (induction s rule: BigAnd_aux_imp.induct)
  apply (subst BigAnd_aux_imp.simps)
  apply (simp add: BigAnd_aux_imp_subprogram_simps Let_def 
        cons_imp_correct hd_imp_correct)
  done            

definition "BigAnd_aux_state_upd_time t s \<equiv>
  let
    cons_h' = BigAnd_aux_acc s;
    t = t + 2;
    cons_t' = 0;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;

    t = t + cons_imp_time 0 cons_state;
    hd_xs' = BigAnd_aux_xs s;
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

    cons_h' = 3;
    t = t + 2;
    cons_t' = cons_ret cons_ret_state;
    t = t + 2;
    cons_ret' = 0;
    t = t + 2;
    cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
    cons_ret_state = cons_imp cons_state;
    t = t + cons_imp_time 0 cons_state;

    BigAnd_aux_ret' = cons_ret cons_ret_state;
    t = t + 2;
    ret = \<lparr>BigAnd_aux_acc = BigAnd_aux_acc s, 
          BigAnd_aux_xs = BigAnd_aux_xs s, 
          BigAnd_aux_ret = BigAnd_aux_ret'\<rparr>
  in
    t
"

lemmas BigAnd_aux_imp_subprogram_time_simps = 
  BigAnd_aux_state_upd_time_def
  BigAnd_aux_imp_subprogram_simps

function BigAnd_aux_imp_time::
  "nat \<Rightarrow> BigAnd_aux_state \<Rightarrow> nat" where
  "BigAnd_aux_imp_time t s =
  (let
    ret = t + BigAnd_aux_state_upd_time 0 s
  in
    ret)"
  by auto
termination
  apply (relation "measure (\<lambda>(t, s). BigAnd_aux_xs s)")
  apply simp
  done

declare BigAnd_aux_imp_time.simps [simp del]            

lemma BigAnd_aux_imp_time_acc:
  "(BigAnd_aux_imp_time (Suc t) s) = Suc (BigAnd_aux_imp_time t s)"
  by (induction t s rule: BigAnd_aux_imp_time.induct)
    ((subst (1 2) BigAnd_aux_imp_time.simps);
      (simp add: BigAnd_aux_state_upd_def))            

lemma BigAnd_aux_imp_time_acc_2_aux:
  "(BigAnd_aux_imp_time t s) = t + (BigAnd_aux_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: BigAnd_aux_imp_time_acc)+            

lemma BigAnd_aux_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (BigAnd_aux_imp_time t s) = t + (BigAnd_aux_imp_time 0 s)"
  by (rule BigAnd_aux_imp_time_acc_2_aux)            

lemma BigAnd_aux_imp_time_acc_3:
  "(BigAnd_aux_imp_time (a + b) s) = a + (BigAnd_aux_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: BigAnd_aux_imp_time_acc)+            

definition BigAnd_aux_IMP_Minus where
  "BigAnd_aux_IMP_Minus \<equiv>

    \<comment> \<open>cons_h' = BigAnd_aux_acc s;\<close>
    (cons_prefix @ cons_h_str) ::= A (V BigAnd_aux_acc_str);;
  \<comment> \<open>cons_t' = 0;\<close>
    (cons_prefix @ cons_t_str) ::= A (N 0);;
  \<comment> \<open>cons_ret' = 0;\<close>
    (cons_prefix @ cons_ret_str) ::= A (N 0);;
  \<comment> \<open>cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>cons_ret_state = cons_imp cons_state;\<close>
     invoke_subprogram cons_prefix cons_IMP_Minus;;
    \<comment> \<open>hd_xs' = BigAnd_aux_xs s;\<close>
    (hd_prefix @ hd_xs_str) ::= A (V BigAnd_aux_xs_str);;
  \<comment> \<open>hd_ret' = 0;\<close>
    (hd_prefix @ hd_ret_str) ::= A (N 0);;
  \<comment> \<open>hd_state = \<lparr>hd_xs = hd_xs', hd_ret = hd_ret'\<rparr>;\<close>
  \<comment> \<open>hd_ret_state = hd_imp hd_state;\<close>
     invoke_subprogram hd_prefix hd_IMP_Minus;;

  \<comment> \<open>cons_h' = hd_ret hd_ret_state;\<close>
    (cons_prefix @ cons_h_str) ::= A (V (hd_prefix @ hd_ret_str));;
  \<comment> \<open>cons_t' = cons_ret cons_ret_state;\<close>
    (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  \<comment> \<open>cons_ret' = 0;\<close>
    (cons_prefix @ cons_ret_str) ::= A (N 0);;

  \<comment> \<open>cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>cons_ret_state = cons_imp cons_state;\<close>
    invoke_subprogram (cons_prefix) cons_IMP_Minus;;

  \<comment> \<open>cons_t' = cons_ret cons_ret_state;\<close>
    (cons_prefix @ cons_t_str) ::= A (V (cons_prefix @ cons_ret_str));;
  \<comment> \<open>cons_h' = 3;\<close>
    (cons_prefix @ cons_h_str) ::= A (N 3);;
  \<comment> \<open>cons_ret' = 0;\<close>
    (cons_prefix @ cons_ret_str) ::= A (N 0);;
  \<comment> \<open>cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
  \<comment> \<open>cons_ret_state = cons_imp cons_state;\<close>
    invoke_subprogram (cons_prefix) cons_IMP_Minus;;

  \<comment>\<open>BigAnd_aux_ret' = cons_ret cons_ret_state'';
    ret = \<lparr>BigAnd_aux_acc = BigAnd_aux_acc s, 
          BigAnd_aux_xs = BigAnd_aux_xs s, 
          BigAnd_aux_ret = BigAnd_aux_ret'\<rparr>\<close>
    BigAnd_aux_ret_str ::= A (V (cons_prefix @ cons_ret_str))
  
  "

abbreviation "BigAnd_aux_IMP_vars\<equiv>
  {BigAnd_aux_acc_str, BigAnd_aux_xs_str, BigAnd_aux_ret_str}"

lemmas BigAnd_aux_IMP_subprogram_simps =
  BigAnd_aux_IMP_Minus_def
  
definition "BigAnd_aux_imp_to_HOL_state p s =
  \<lparr>BigAnd_aux_acc = (s (add_prefix p BigAnd_aux_acc_str)),
   BigAnd_aux_xs = (s (add_prefix p BigAnd_aux_xs_str)),
   BigAnd_aux_ret = (s (add_prefix p BigAnd_aux_ret_str))\<rparr>"

lemmas BigAnd_aux_state_translators =
  BigAnd_aux_imp_to_HOL_state_def

lemmas BigAnd_aux_complete_simps =
  BigAnd_aux_IMP_subprogram_simps
  BigAnd_aux_imp_subprogram_simps
  BigAnd_aux_state_translators

lemma BigAnd_aux_IMP_Minus_correct_function:
  "(invoke_subprogram p BigAnd_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p BigAnd_aux_ret_str)
      = BigAnd_aux_ret
          (BigAnd_aux_imp (BigAnd_aux_imp_to_HOL_state p s))"
  apply(subst BigAnd_aux_imp.simps)
  apply(simp only: BigAnd_aux_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply (erule  cons_IMP_Minus_correct[where vars=BigAnd_aux_IMP_vars])
  subgoal premises p using p(16) by fastforce
  apply (erule hd_IMP_Minus_correct[where vars="BigAnd_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
  subgoal premises p using p(18) by fastforce
  apply (erule  cons_IMP_Minus_correct[where vars=BigAnd_aux_IMP_vars])
  subgoal premises p using p(20) by fastforce
  apply (erule  cons_IMP_Minus_correct[where vars=BigAnd_aux_IMP_vars])
  subgoal premises p using p(22) by fastforce
  apply (simp only: BigAnd_aux_state_translators
  Let_def BigAnd_aux_state_upd_def
  cons_imp_to_HOL_state_def
  hd_imp_to_HOL_state_def)
  apply fastforce
  done
  (*
    A stepwise alternative for better understanding
    apply clarsimp
    subgoal premises p
    using p(8)[of BigAnd_aux_xs_str] apply simp
    apply (subst p(7)[symmetric])
    using p(4)[of "cons_prefix @ cons_ret_str"] 
    by force
  *)

lemma BigAnd_aux_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ BigAnd_aux_pref) BigAnd_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix BigAnd_aux_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemmas BigAnd_aux_complete_time_simps =
  BigAnd_aux_imp_subprogram_time_simps
  BigAnd_aux_imp_time_acc
  BigAnd_aux_imp_time_acc_2
  BigAnd_aux_imp_time_acc_3
  BigAnd_aux_state_translators

lemma BigAnd_aux_IMP_Minus_correct_time:
  "(invoke_subprogram p BigAnd_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = BigAnd_aux_imp_time 0 (BigAnd_aux_imp_to_HOL_state p s)"
  apply(subst BigAnd_aux_imp_time.simps)
  apply(simp only: BigAnd_aux_IMP_Minus_def prefix_simps)
  apply(erule Seq_tE)+
  apply (erule  cons_IMP_Minus_correct[where vars=BigAnd_aux_IMP_vars])
  subgoal premises p using p(31) by fastforce
  apply (erule hd_IMP_Minus_correct[where vars="BigAnd_aux_IMP_vars \<union> {cons_prefix @ cons_ret_str}"])
  subgoal premises p using p(33) by fastforce
  apply (erule  cons_IMP_Minus_correct[where vars=BigAnd_aux_IMP_vars])
  subgoal premises p using p(35) by fastforce
  apply (erule  cons_IMP_Minus_correct[where vars=BigAnd_aux_IMP_vars])
  subgoal premises p using p(37) by fastforce 
  apply (simp only: BigAnd_aux_state_translators
  Let_def BigAnd_aux_state_upd_time_def
  cons_imp_to_HOL_state_def 
  hd_imp_to_HOL_state_def )
  apply fastforce
  done
  (*
  A similar stepwise alternative
  apply clarsimp
  subgoal premises p
  using p(9)[of BigAnd_aux_xs_str, symmetric] apply simp
  using p(5)[of "cons_prefix @ cons_ret_str", symmetric] apply simp
  apply (subst p(8))+
  apply blast
  done
  *)

lemma BigAnd_aux_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) BigAnd_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (BigAnd_aux_imp_time 0 (BigAnd_aux_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) BigAnd_aux_ret_str) =
          BigAnd_aux_ret (BigAnd_aux_imp
                                        (BigAnd_aux_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using BigAnd_aux_IMP_Minus_correct_function
  by (auto simp: BigAnd_aux_IMP_Minus_correct_time)
    (meson BigAnd_aux_IMP_Minus_correct_effects set_mono_prefix)

paragraph BigAnd_acc
record BigAnd_acc_state = BigAnd_acc_acc::nat BigAnd_acc_xs::nat BigAnd_acc_ret::nat

abbreviation "BigAnd_acc_prefix \<equiv> ''BigAnd_acc.''"
abbreviation "BigAnd_acc_acc_str \<equiv> ''acc''"
abbreviation "BigAnd_acc_xs_str \<equiv> ''xs''"
abbreviation "BigAnd_acc_ret_str \<equiv> ''ret''"

definition "BigAnd_acc_state_upd s \<equiv>
  (let
    BigAnd_aux_acc' = BigAnd_acc_acc s;
    BigAnd_aux_xs' = BigAnd_acc_xs s;
    BigAnd_aux_ret' = 0;
    BigAnd_state = \<lparr>BigAnd_aux_acc = BigAnd_aux_acc',
                    BigAnd_aux_xs = BigAnd_aux_xs',
                    BigAnd_aux_ret = BigAnd_aux_ret'\<rparr>;
    BigAnd_aux_ret_state = BigAnd_aux_imp BigAnd_state;

    tl_xs' = BigAnd_acc_xs s;
    tl_ret' = 0;
    tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
    tl_ret_state = tl_imp tl_state;

    BigAnd_acc_acc' = BigAnd_aux_ret BigAnd_aux_ret_state;
    BigAnd_acc_xs' = tl_ret tl_ret_state;
    ret = \<lparr>BigAnd_acc_acc = BigAnd_acc_acc',
          BigAnd_acc_xs = BigAnd_acc_xs',
          BigAnd_acc_ret = BigAnd_acc_ret s\<rparr>
  in
    ret
  )" 

definition "BigAnd_acc_imp_compute_loop_condition s \<equiv> (
  let
    condition = BigAnd_acc_xs s
  in 
    condition
)"

definition "BigAnd_acc_imp_after_loop s \<equiv> (
  let
    ret = \<lparr>BigAnd_acc_acc = BigAnd_acc_acc s,
          BigAnd_acc_xs = BigAnd_acc_xs s,
          BigAnd_acc_ret = BigAnd_acc_acc s\<rparr>
  in
    ret
)"

lemmas BigAnd_acc_imp_subprogram_simps = 
  BigAnd_acc_state_upd_def
  BigAnd_acc_imp_compute_loop_condition_def
  BigAnd_acc_imp_after_loop_def

function BigAnd_acc_imp::
  "BigAnd_acc_state \<Rightarrow> BigAnd_acc_state" where
  "BigAnd_acc_imp s =
  (if BigAnd_acc_imp_compute_loop_condition s \<noteq> 0
   then
    let next_iteration = BigAnd_acc_imp (BigAnd_acc_state_upd s)
    in next_iteration
   else
    let ret = BigAnd_acc_imp_after_loop s
    in ret
  )"
  by simp+
termination
  apply (relation "measure (\<lambda>s. BigAnd_acc_xs s)")
  apply (simp add: BigAnd_acc_imp_subprogram_simps tl_imp_correct)+
  done

declare BigAnd_acc_imp.simps [simp del]

lemma BigAnd_acc_imp_correct:
  "BigAnd_acc_ret (BigAnd_acc_imp s) =
    BigAnd_acc (BigAnd_acc_acc s) (BigAnd_acc_xs s)"
  apply (induction s rule: BigAnd_acc_imp.induct)
  apply (subst BigAnd_acc_imp.simps)
  apply (subst BigAnd_acc.simps)
  apply (simp del: BigAnd_acc.simps 
      add: BigAnd_acc_imp_subprogram_simps Let_def
      tl_imp_correct BigAnd_aux_imp_correct)
  done            

definition "BigAnd_acc_state_upd_time t s \<equiv>
(
  let
    BigAnd_aux_acc' = BigAnd_acc_acc s;
    t = t + 2;
    BigAnd_aux_xs' = BigAnd_acc_xs s;
    t = t + 2;
    BigAnd_aux_ret' = 0;
    t = t + 2;
    BigAnd_state = \<lparr>BigAnd_aux_acc = BigAnd_aux_acc',
                    BigAnd_aux_xs = BigAnd_aux_xs',
                    BigAnd_aux_ret = BigAnd_aux_ret'\<rparr>;
    BigAnd_aux_ret_state = BigAnd_aux_imp BigAnd_state;
    t = t + BigAnd_aux_imp_time 0 BigAnd_state;

    tl_xs' = BigAnd_acc_xs s;
    t = t + 2;
    tl_ret' = 0;
    t = t + 2;
    tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;
    tl_ret_state = tl_imp tl_state;
    t = t + tl_imp_time 0 tl_state;

    BigAnd_acc_acc' = BigAnd_aux_ret BigAnd_aux_ret_state;
    t = t + 2;
    BigAnd_acc_xs' = tl_ret tl_ret_state;
    t = t + 2;
    ret = \<lparr>BigAnd_acc_acc = BigAnd_acc_acc',
          BigAnd_acc_xs = BigAnd_acc_xs',
          BigAnd_acc_ret = BigAnd_acc_ret s\<rparr>
  in
    t
  )" 


definition "BigAnd_acc_imp_compute_loop_condition_time t s \<equiv>
  let
    t = t + 2;
    condition = BigAnd_acc_xs s
  in
    t
"

definition "BigAnd_acc_imp_after_loop_time t s \<equiv>
  let
    t = t + 2;
    ret = \<lparr>BigAnd_acc_acc = BigAnd_acc_acc s,
          BigAnd_acc_xs = BigAnd_acc_xs s,
          BigAnd_acc_ret = BigAnd_acc_acc s\<rparr>
  in
    t
"

lemmas BigAnd_acc_imp_subprogram_time_simps = 
  BigAnd_acc_state_upd_time_def
  BigAnd_acc_imp_compute_loop_condition_time_def
  BigAnd_acc_imp_after_loop_time_def
  BigAnd_acc_imp_subprogram_simps

function BigAnd_acc_imp_time::
  "nat \<Rightarrow> BigAnd_acc_state \<Rightarrow> nat" where
  "BigAnd_acc_imp_time t s =
  BigAnd_acc_imp_compute_loop_condition_time 0 s +
  (if BigAnd_acc_imp_compute_loop_condition s \<noteq> 0
    then
      (let
        t = t + 1;
        next_iteration =
          BigAnd_acc_imp_time (t + BigAnd_acc_state_upd_time 0 s)
                         (BigAnd_acc_state_upd s)
       in next_iteration)
    else
      (let
        t = t + 2;
        ret = t + BigAnd_acc_imp_after_loop_time 0 s
       in ret)
  )"
  by auto
termination
  apply (relation "measure (\<lambda>(t, s). BigAnd_acc_xs s)")
  apply (simp add: BigAnd_acc_imp_subprogram_time_simps tl_imp_correct)+
  done

declare BigAnd_acc_imp_time.simps [simp del]            

lemma BigAnd_acc_imp_time_acc:
  "(BigAnd_acc_imp_time (Suc t) s) = Suc (BigAnd_acc_imp_time t s)"
  by (induction t s rule: BigAnd_acc_imp_time.induct)
    ((subst (1 2) BigAnd_acc_imp_time.simps);
      (simp add: BigAnd_acc_state_upd_def))            

lemma BigAnd_acc_imp_time_acc_2_aux:
  "(BigAnd_acc_imp_time t s) = t + (BigAnd_acc_imp_time 0 s)"
  by (induction t arbitrary: s) (simp add: BigAnd_acc_imp_time_acc)+            

lemma BigAnd_acc_imp_time_acc_2:
  "t \<noteq> 0 \<Longrightarrow> (BigAnd_acc_imp_time t s) = t + (BigAnd_acc_imp_time 0 s)"
  by (rule BigAnd_acc_imp_time_acc_2_aux)            

lemma BigAnd_acc_imp_time_acc_3:
  "(BigAnd_acc_imp_time (a + b) s) = a + (BigAnd_acc_imp_time b s)"
  by (induction a arbitrary: b s) (simp add: BigAnd_acc_imp_time_acc)+            

abbreviation "BigAnd_acc_while_cond \<equiv> ''condition''"

definition "BigAnd_acc_IMP_init_while_cond \<equiv>
  \<comment> \<open>condition = BigAnd_acc_xs s\<close>
  BigAnd_acc_while_cond ::= A (V BigAnd_acc_xs_str)
"

definition "BigAnd_acc_IMP_loop_body \<equiv>
  \<comment> \<open>BigAnd_aux_acc' = BigAnd_acc_acc s;
    BigAnd_aux_xs' = BigAnd_acc_xs s;
    BigAnd_aux_ret' = 0;
    BigAnd_state = \<lparr>BigAnd_aux_acc = BigAnd_aux_acc',
                    BigAnd_aux_xs = BigAnd_aux_xs',
                    BigAnd_aux_ret = BigAnd_aux_ret'\<rparr>;
    BigAnd_aux_ret_state = BigAnd_aux_imp BigAnd_state;\<close>
    (BigAnd_aux_prefix @ BigAnd_aux_acc_str) ::= A (V BigAnd_acc_acc_str);;
    (BigAnd_aux_prefix @ BigAnd_aux_xs_str) ::= A (V BigAnd_acc_xs_str);;
    (BigAnd_aux_prefix @ BigAnd_aux_ret_str) ::= A (N 0);;
    invoke_subprogram BigAnd_aux_prefix BigAnd_aux_IMP_Minus;;
    \<comment> \<open>BigAnd_acc_acc' = cons_ret cons_ret_state;\<close>
    BigAnd_acc_acc_str ::= A (V (BigAnd_aux_prefix @ BigAnd_aux_ret_str));;

  \<comment> \<open>tl_xs' = BigAnd_acc_xs s;\<close>
    (tl_prefix @ tl_xs_str) ::= A (V BigAnd_acc_xs_str);;
  \<comment> \<open>tl_ret' = 0;\<close>
    (tl_prefix @ tl_ret_str) ::= A (N 0);;
  \<comment> \<open>tl_state = \<lparr>tl_xs = tl_xs', tl_ret = tl_ret'\<rparr>;\<close>
  \<comment> \<open>tl_ret_state = tl_imp tl_state;\<close>
    invoke_subprogram tl_prefix tl_IMP_Minus;;
  
  \<comment> \<open>BigAnd_acc_xs' = tl_ret tl_ret_state;\<close>
    BigAnd_acc_xs_str ::= A (V (tl_prefix @ tl_ret_str))
  \<comment> \<open>ret = \<lparr>BigAnd_acc_acc = BigAnd_acc_acc',\<close>
  \<comment> \<open>      BigAnd_acc_xs = BigAnd_acc_xs',\<close>
  \<comment> \<open>      BigAnd_acc_ret = BigAnd_acc_ret s\<rparr>\<close>
"

definition "BigAnd_acc_IMP_after_loop \<equiv>
 \<comment>\<open>ret = \<lparr>BigAnd_acc_acc = BigAnd_acc_acc s,
          BigAnd_acc_xs = BigAnd_acc_xs s,
          BigAnd_acc_ret = BigAnd_acc_acc s\<rparr>\<close>
    BigAnd_acc_ret_str ::= A (V BigAnd_acc_acc_str)
"

definition BigAnd_acc_IMP_Minus where
  "BigAnd_acc_IMP_Minus \<equiv>
  BigAnd_acc_IMP_init_while_cond;;
  WHILE BigAnd_acc_while_cond \<noteq>0 DO (
    BigAnd_acc_IMP_loop_body;;
    BigAnd_acc_IMP_init_while_cond
  );;
  BigAnd_acc_IMP_after_loop"

abbreviation "BigAnd_acc_IMP_vars\<equiv>
  {BigAnd_acc_while_cond, BigAnd_acc_acc_str, BigAnd_acc_xs_str, BigAnd_acc_ret_str}"

lemmas BigAnd_acc_IMP_subprogram_simps =
  BigAnd_acc_IMP_init_while_cond_def
  BigAnd_acc_IMP_loop_body_def
  BigAnd_acc_IMP_after_loop_def

definition "BigAnd_acc_imp_to_HOL_state p s =
  \<lparr>BigAnd_acc_acc = (s (add_prefix p BigAnd_acc_acc_str)),
   BigAnd_acc_xs = (s (add_prefix p BigAnd_acc_xs_str)),
   BigAnd_acc_ret = (s (add_prefix p BigAnd_acc_ret_str))\<rparr>"

lemmas BigAnd_acc_state_translators =
  BigAnd_acc_imp_to_HOL_state_def

lemmas BigAnd_acc_complete_simps =
  BigAnd_acc_IMP_subprogram_simps
  BigAnd_acc_imp_subprogram_simps
  BigAnd_acc_state_translators

lemma BigAnd_acc_IMP_Minus_correct_function:
  "(invoke_subprogram p BigAnd_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p BigAnd_acc_ret_str)
      = BigAnd_acc_ret
          (BigAnd_acc_imp (BigAnd_acc_imp_to_HOL_state p s))"
  apply(induction "BigAnd_acc_imp_to_HOL_state p s" arbitrary: s s' t
    rule: BigAnd_acc_imp.induct)
  apply(subst BigAnd_acc_imp.simps)
  apply(simp only: BigAnd_acc_IMP_Minus_def prefix_simps)
  apply(erule Seq_E)+
  apply(erule While_tE)

  subgoal
    apply(simp only: BigAnd_acc_IMP_subprogram_simps prefix_simps)
    by(fastforce simp: BigAnd_acc_complete_simps)

  apply(erule Seq_E)+
  apply(dest_com_gen)

  subgoal
      apply(simp only: BigAnd_acc_IMP_init_while_cond_def prefix_simps)
      by(fastforce simp add: BigAnd_acc_complete_simps)

  subgoal
      apply(subst (asm) BigAnd_acc_IMP_init_while_cond_def)
      apply(simp only: BigAnd_acc_IMP_loop_body_def prefix_simps)
      apply(erule Seq_E)+
      apply(erule tl_IMP_Minus_correct[where vars = "BigAnd_acc_IMP_vars"])
      subgoal premises p using p(14) by fastforce
      apply(erule BigAnd_aux_IMP_Minus_correct[where vars = "BigAnd_acc_IMP_vars"])
      subgoal premises p using p(16) by fastforce
      apply (simp only: Let_def prefix_simps
          BigAnd_acc_state.simps BigAnd_acc_imp_to_HOL_state_def
          BigAnd_acc_imp_subprogram_simps 
          BigAnd_aux_imp_to_HOL_state_def BigAnd_aux_imp_correct
          tl_imp_to_HOL_state_def tl_imp_correct)+
      apply force
      done

  subgoal
      apply(simp only: BigAnd_acc_IMP_init_while_cond_def prefix_simps
          BigAnd_acc_IMP_loop_body_def)
      apply(erule Seq_E)+
      apply(erule tl_IMP_Minus_correct[where vars = "BigAnd_acc_IMP_vars"])
      subgoal premises p using p(14) by fastforce
      apply(erule BigAnd_aux_IMP_Minus_correct[where vars = "BigAnd_acc_IMP_vars"])
      subgoal premises p using p(16) by fastforce
      apply (simp only: Let_def prefix_simps
          BigAnd_acc_state.simps BigAnd_acc_imp_to_HOL_state_def
          BigAnd_acc_imp_subprogram_simps 
          BigAnd_aux_imp_to_HOL_state_def BigAnd_aux_state.simps BigAnd_aux_imp_correct
          tl_imp_to_HOL_state_def tl_state.simps tl_imp_correct)+
      apply clarsimp 
      subgoal premises p 
        using p(6)[of BigAnd_acc_xs_str]
              p(6)[of BigAnd_acc_acc_str]
              p(4) p(6) same_append_eq by fastforce
  done
done        

lemma BigAnd_acc_IMP_Minus_correct_effects:
  "\<lbrakk>(invoke_subprogram (p @ BigAnd_acc_pref) BigAnd_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    v \<in> vars; \<not> (prefix BigAnd_acc_pref v)\<rbrakk>
   \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid'' com_only_vars prefix_def
  by blast            

lemmas BigAnd_acc_complete_time_simps =
  BigAnd_acc_imp_subprogram_time_simps
  BigAnd_acc_imp_time_acc
  BigAnd_acc_imp_time_acc_2
  BigAnd_acc_imp_time_acc_3
  BigAnd_acc_state_translators

lemma BigAnd_acc_IMP_Minus_correct_time:
  "(invoke_subprogram p BigAnd_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = BigAnd_acc_imp_time 0 (BigAnd_acc_imp_to_HOL_state p s)"
  apply(induction "BigAnd_acc_imp_to_HOL_state p s" arbitrary: s s' t
      rule: BigAnd_acc_imp.induct)
  apply(subst BigAnd_acc_imp_time.simps)
  apply(simp only: BigAnd_acc_IMP_Minus_def prefix_simps)

  apply(erule Seq_tE)+
  apply(erule While_tE_time)

  subgoal
    apply(simp only: BigAnd_acc_IMP_subprogram_simps prefix_simps)
    by (force simp: BigAnd_acc_IMP_subprogram_simps
        BigAnd_acc_imp_subprogram_time_simps BigAnd_acc_state_translators)

  apply(erule Seq_tE)+
  apply(simp add: add.assoc)
  apply(dest_com_gen_time)

  subgoal
    apply(simp only: BigAnd_acc_IMP_init_while_cond_def prefix_simps)
    by(fastforce simp add: BigAnd_acc_complete_simps)

  subgoal
    apply(subst (asm) BigAnd_acc_IMP_init_while_cond_def)
    apply(simp only: BigAnd_acc_IMP_loop_body_def prefix_simps)
    apply(erule Seq_E)+
      apply(erule tl_IMP_Minus_correct[where vars = "BigAnd_acc_IMP_vars"])
      subgoal premises p using p(17) by fastforce
      apply(erule BigAnd_aux_IMP_Minus_correct[where vars = "BigAnd_acc_IMP_vars"])
      subgoal premises p using p(19) by fastforce
      apply (simp only: Let_def prefix_simps
          BigAnd_acc_state.simps BigAnd_acc_imp_to_HOL_state_def
          BigAnd_acc_imp_subprogram_simps 
          BigAnd_aux_imp_to_HOL_state_def BigAnd_aux_state.simps BigAnd_aux_imp_correct
          tl_imp_to_HOL_state_def tl_state.simps tl_imp_correct)+
      apply force
      done

  subgoal
    apply(simp only: BigAnd_acc_IMP_init_while_cond_def prefix_simps
          BigAnd_acc_IMP_loop_body_def)
      apply(erule Seq_tE)+
      apply(erule tl_IMP_Minus_correct[where vars = "BigAnd_acc_IMP_vars"])
      subgoal premises p using p(25) by fastforce
      apply(erule BigAnd_aux_IMP_Minus_correct[where vars = "BigAnd_acc_IMP_vars"])
      subgoal premises p using p(27) by fastforce
      apply (simp only: Let_def prefix_simps
          BigAnd_acc_complete_time_simps
          BigAnd_aux_imp_to_HOL_state_def BigAnd_aux_imp_correct
          BigAnd_aux_IMP_Minus_correct_time
          tl_imp_to_HOL_state_def tl_imp_correct
          tl_IMP_Minus_correct_time)+
      apply clarsimp
        subgoal premises p 
        using p(11)[of BigAnd_acc_xs_str] apply simp
        using p(11)[of BigAnd_acc_ret_str] apply simp
        using p(9)[of BigAnd_acc_ret_str] apply simp
        using p(9)[of BigAnd_acc_acc_str] apply simp
        done
      
      done

  done        

lemma BigAnd_acc_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) BigAnd_acc_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v);
    \<lbrakk>t = (BigAnd_acc_imp_time 0 (BigAnd_acc_imp_to_HOL_state (p1 @ p2) s));
     s' (add_prefix (p1 @ p2) BigAnd_acc_ret_str) =
          BigAnd_acc_ret (BigAnd_acc_imp
                                        (BigAnd_acc_imp_to_HOL_state (p1 @ p2) s));
     \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
   \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using BigAnd_acc_IMP_Minus_correct_function
  by (auto simp: BigAnd_acc_IMP_Minus_correct_time)
    (meson BigAnd_acc_IMP_Minus_correct_effects set_mono_prefix)                        

end
