\<^marker>\<open>creator Mohammad Abdulaziz, Florian Keßler\<close>

theory Primitives_IMP_Minus
  imports "HOL-Library.Nat_Bijection" Primitives IMP_Minus.Call_By_Prefixes
begin
subsection \<open>Multiplication\<close>

record mul_state = mul_a::nat mul_b::nat mul_c::nat

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
  by  (relation "measure (\<lambda>s. mul_b s)") (auto simp: mul_state_upd_def Let_def split: if_splits)

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
  by  (relation "measure (\<lambda>(t, s). mul_b s)") (auto simp: mul_state_upd_def Let_def split: if_splits)

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

lemma mul_IMP_minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) mul_IMP_minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
     \<lbrakk>t = (mul_imp_time 0 (mul_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) mul_c_str) = mul_c (mul_imp (mul_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. p1 @ v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v) \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using mul_IMP_minus_correct_time mul_IMP_minus_correct_function mul_IMP_minus_correct_effects
  by auto

subsection \<open>Encoding and decoding natural numbers\<close>

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

lemma triangle_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) triangle_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
     \<lbrakk>t = (triangle_imp_time 0 (triangle_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) triangle_triangle_str) = triangle_triangle (triangle_imp (triangle_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. p1 @ v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v) \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using triangle_IMP_Minus_correct_time triangle_IMP_Minus_correct_function
        triangle_IMP_Minus_correct_effects 
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

lemma prod_encode_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) prod_encode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
     \<lbrakk>t = (prod_encode_imp_time 0 (prod_encode_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) prod_encode_ret_str) = prod_encode_ret (prod_encode_imp (prod_encode_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. p1 @ v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v) \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using prod_encode_IMP_Minus_correct_time prod_encode_IMP_Minus_correct_function
        prod_encode_IMP_Minus_correct_effects 
  by auto

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
  by  (relation "measure (\<lambda>s. prod_decode_aux_m s)")  (auto simp: prod_decode_aux_state_upd_def Let_def split: if_splits)

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
  by  (relation "measure (\<lambda>(t, s). prod_decode_aux_m s)")  (auto simp: prod_decode_aux_state_upd_def Let_def split: if_splits)

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

subsection \<open>Head and tail of lists\<close>

record hd_state = hd_xs::nat hd_ret::nat

abbreviation "hd_prefix \<equiv> ''hd.''"
abbreviation "hd_xs_str \<equiv> ''xs''"
abbreviation "hd_ret_str \<equiv> ''hd_ret''"

definition "hd_state_upd s \<equiv>
      let
        prod_decode_m' = hd_xs s - 1;
        prod_decode_fst_ret' = 0;
        prod_decode_snd_ret' = 0;
        prod_decode_state = \<lparr>prod_decode_m = prod_decode_m', prod_decode_fst_ret = prod_decode_fst_ret', prod_decode_snd_ret = prod_decode_snd_ret'\<rparr>;
        prod_decode_ret = prod_decode_imp prod_decode_state;
        hd_ret' = prod_decode_fst_ret prod_decode_ret;
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
  by (subst hd_imp.simps) (auto simp: prod_decode_imp_correct hd_nat_def fst_nat_def hd_imp.simps hd_state_upd_def Let_def split: if_splits)[1]

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
        prod_decode_state = \<lparr>prod_decode_m = prod_decode_m', prod_decode_fst_ret = prod_decode_fst_ret', prod_decode_snd_ret = prod_decode_snd_ret'\<rparr>;
        prod_decode_ret = prod_decode_imp prod_decode_state;
        t = t + prod_decode_imp_time 0 prod_decode_state;
        hd_ret' = prod_decode_fst_ret prod_decode_ret;
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
        (prod_decode_prefix @ prod_decode_m_str) ::= ((V hd_xs_str) \<ominus> (N 1));;
        \<comment> \<open>prod_decode_fst_ret' = 0;\<close>
        (prod_decode_prefix @ prod_decode_fst_ret_str) ::= (A (N 0));;
        \<comment> \<open>prod_decode_snd_ret' = 0;\<close>
        (prod_decode_prefix @ prod_decode_snd_ret_str) ::= (A (N 0));;
        \<comment> \<open>prod_decode_state = \<lparr>prod_decode_m = prod_decode_m', prod_decode_fst_ret = prod_decode_fst_ret', prod_decode_snd_ret = prod_decode_snd_ret'\<rparr>;\<close>
        \<comment> \<open>prod_decode_ret = prod_decode_imp prod_decode_state;\<close>
        invoke_subprogram prod_decode_prefix prod_decode_IMP_Minus;;
        \<comment> \<open>hd_ret' = prod_decode_fst_ret prod_decode_ret;\<close>
        (hd_ret_str) ::= (A (V (prod_decode_prefix @ prod_decode_fst_ret_str)))
  )"

definition "hd_imp_to_HOL_state p s =
  \<lparr>hd_xs = (s (add_prefix p hd_xs_str)), hd_ret = (s (add_prefix p hd_ret_str))\<rparr>"

lemma hd_IMP_Minus_correct_function: 
  "(invoke_subprogram p hd_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p hd_ret_str) = hd_ret (hd_imp (hd_imp_to_HOL_state p s))"
  apply(simp only: hd_IMP_Minus_def hd_imp.simps com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  apply(erule prod_decode_IMP_Minus_correct[where vars = "{p @ hd_xs_str}"])
   apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: hd_state_upd_def Let_def hd_imp_to_HOL_state_def)[1]
  apply(auto simp: prod_decode_imp_to_HOL_state_def)[1]
  done

lemma hd_IMP_Minus_correct_time: 
  "(invoke_subprogram p hd_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = hd_imp_time 0 (hd_imp_to_HOL_state p s)"
  apply(simp only: hd_IMP_Minus_def hd_imp_time.simps com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  apply(erule prod_decode_IMP_Minus_correct[where vars = "{p @ hd_xs_str}"])
   apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: hd_state_upd_def Let_def hd_imp_to_HOL_state_def)[1]
  apply(auto simp: prod_decode_imp_to_HOL_state_def)[1]
  done

lemma hd_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ hd_pref) hd_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> v \<in> vars \<Longrightarrow> \<not> (set hd_pref \<subseteq> set v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma hd_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) hd_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    (\<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v));
     \<lbrakk>t = (hd_imp_time 0 (hd_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) hd_ret_str) = hd_ret (hd_imp (hd_imp_to_HOL_state (p1 @ p2) s));
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
        prod_decode_state = \<lparr>prod_decode_m = prod_decode_m', prod_decode_fst_ret = prod_decode_fst_ret', prod_decode_snd_ret = prod_decode_snd_ret'\<rparr>;
        prod_decode_ret = prod_decode_imp prod_decode_state;
        tl_ret' = prod_decode_snd_ret prod_decode_ret;
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
        prod_decode_state = \<lparr>prod_decode_m = prod_decode_m', prod_decode_fst_ret = prod_decode_fst_ret', prod_decode_snd_ret = prod_decode_snd_ret'\<rparr>;
        prod_decode_ret = prod_decode_imp prod_decode_state;
        t = t + prod_decode_imp_time 0 prod_decode_state;
        tl_ret' = prod_decode_snd_ret prod_decode_ret;
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
        (prod_decode_prefix @ prod_decode_m_str) ::= ((V tl_xs_str) \<ominus> (N 1));;
        \<comment> \<open>prod_decode_snd_ret' = 0;\<close>
        (prod_decode_prefix @ prod_decode_fst_ret_str) ::= (A (N 0));;
        \<comment> \<open>prod_decode_snd_ret' = 0;\<close>
        (prod_decode_prefix @ prod_decode_snd_ret_str) ::= (A (N 0));;
        \<comment> \<open>prod_decode_state = \<lparr>prod_decode_m = prod_decode_m', prod_decode_snd_ret = prod_decode_snd_ret', prod_decode_snd_ret = prod_decode_snd_ret'\<rparr>;\<close>
        \<comment> \<open>prod_decode_ret = prod_decode_imp prod_decode_state;\<close>
        invoke_subprogram prod_decode_prefix prod_decode_IMP_Minus;;
        \<comment> \<open>tl_ret' = prod_decode_snd_ret prod_decode_ret;\<close>
        (tl_ret_str) ::= (A (V (prod_decode_prefix @ prod_decode_snd_ret_str)))
  )"

definition "tl_imp_to_HOL_state p s =
  \<lparr>tl_xs = (s (add_prefix p tl_xs_str)), tl_ret = (s (add_prefix p tl_ret_str))\<rparr>"

lemma tl_IMP_Minus_correct_function: 
  "(invoke_subprogram p tl_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p tl_ret_str) = tl_ret (tl_imp (tl_imp_to_HOL_state p s))"
  apply(simp only: tl_IMP_Minus_def tl_imp.simps com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  apply(erule prod_decode_IMP_Minus_correct[where vars = "{p @ tl_xs_str}"])
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
  apply(erule prod_decode_IMP_Minus_correct[where vars = "{p @ tl_xs_str}"])
   apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: tl_state_upd_def Let_def tl_imp_to_HOL_state_def)[1]
  apply(auto simp: prod_decode_imp_to_HOL_state_def)[1]
  done

lemma tl_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ tl_pref) tl_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> v \<in> vars \<Longrightarrow> \<not> (set tl_pref \<subseteq> set v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma tl_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) tl_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    (\<And>v. v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v));
     \<lbrakk>t = (tl_imp_time 0 (tl_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) tl_ret_str) = tl_ret (tl_imp (tl_imp_to_HOL_state (p1 @ p2) s));
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
  by  (relation "measure (\<lambda>s. length_xs s)")
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
  by  (relation "measure (\<lambda>(t,s). length_xs s)")
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

lemma length_IMP_Minus_correct:
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

lemma cons_IMP_Minus_correct:
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
  by  (relation "measure (\<lambda>s. append_xs s)")
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
  by  (relation "measure (\<lambda>(t,s). append_xs s)")
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

lemma append_IMP_Minus_correct:
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

lemma AND_neq_zero_IMP_Minus_correct:
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

lemma OR_neq_zero_IMP_Minus_correct:
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