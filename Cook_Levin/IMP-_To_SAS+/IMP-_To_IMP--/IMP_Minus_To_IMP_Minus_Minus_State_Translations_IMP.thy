theory IMP_Minus_To_IMP_Minus_Minus_State_Translations_IMP
  imports Primitives_IMP_Minus
          IMP_Minus_To_IMP_Minus_Minus_State_Translations_nat
          IMP_Minus.Com
begin

record n_hashes_state =
  n_hashes_acc::nat
  n_hashes_n::nat

abbreviation "n_hashes_prefix \<equiv> ''n_hashes.''"
abbreviation "n_hashes_acc_str \<equiv> ''acc''"
abbreviation "n_hashes_n_str \<equiv> ''n''"

lemma pound_encode_val: "encode_char (CHR ''#'') = 35" by eval

definition "n_hashes_state_upd s \<equiv>
      let
        cons_h' = 35;
        cons_t' = n_hashes_acc s;
        cons_ret' = 0;
        cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
        cons_ret_state = cons_imp cons_state;
        n_hashes_acc' = cons_ret cons_ret_state;
        n_hashes_n' = n_hashes_n s - 1;
        ret = \<lparr>n_hashes_acc = n_hashes_acc', n_hashes_n = n_hashes_n'\<rparr>
      in
        ret
"

function n_hashes_imp:: "n_hashes_state \<Rightarrow> n_hashes_state" where
  "n_hashes_imp s = 
  (if n_hashes_n s \<noteq> 0
   then
    (let next_iteration = n_hashes_imp (n_hashes_state_upd s)
      in next_iteration)
  else
    (let ret = s in ret)
  )"
  by simp+
termination by (relation "measure (\<lambda>s. n_hashes_n s)") (simp add: n_hashes_state_upd_def)+

declare n_hashes_imp.simps [simp del]

lemma n_hashes_imp_correct:
  "n_hashes_acc (n_hashes_imp s)
    = IMP_Minus_To_IMP_Minus_Minus_State_Translations_nat.n_hashes_acc
        (n_hashes_acc s) (n_hashes_n s)"
proof (induction s rule: n_hashes_imp.induct)
  case (1 s)
  then show ?case
    apply(subst n_hashes_imp.simps)
    by (auto simp: n_hashes_state_upd_def Let_def)
      (metis Suc_pred cons_imp_correct cons_state.simps(1) cons_state.simps(2)
        n_hashes_acc.simps(2) pound_encode_val)
qed 

function n_hashes_imp_time:: "nat \<Rightarrow> n_hashes_state \<Rightarrow> nat" where
  "n_hashes_imp_time t s =
  (if n_hashes_n s \<noteq> 0
   then
    (let
        cons_h' = 35;
        t = t + 2;
        cons_t' = n_hashes_acc s;
        t = t + 2;
        cons_ret' = 0;
        t = t + 2;
        cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;
        cons_ret_state = cons_imp cons_state;
        t = t + cons_imp_time 0 cons_state;
        n_hashes_acc' = cons_ret cons_ret_state;
        t = t + 2;
        n_hashes_n' = n_hashes_n s - 1;
        t = t + 2;
        next_iteration = n_hashes_imp_time t (n_hashes_state_upd s)
     in next_iteration)
  else
    (let
        t = t + 2;
        ret = t
     in ret)
  )"
  by auto
termination
  by (relation "measure (\<lambda>(t,s). n_hashes_n s)") (simp add: n_hashes_state_upd_def)+

lemmas [simp del] = n_hashes_imp_time.simps

lemma foo:"n_hashes_n s = 0 \<Longrightarrow> n_hashes_imp_time t s = t + 2"
  by(subst n_hashes_imp_time.simps) simp

lemma n_hashes_imp_time_acc: "(n_hashes_imp_time (Suc t) s) = Suc (n_hashes_imp_time t s)"
  by (induction t s rule: n_hashes_imp_time.induct)
    ((subst (1 2) n_hashes_imp_time.simps); (simp add: n_hashes_state_upd_def))

lemma n_hashes_imp_time_acc_2: "(n_hashes_imp_time x s) = x + (n_hashes_imp_time 0 s)"
  by (induction x arbitrary: s) (simp add: n_hashes_imp_time_acc)+


\<comment> \<open>Split IMP- command improve parsing time again.\<close>
abbreviation "n_hashes_IMP_Minus_1 \<equiv>
        \<comment> \<open>cons_h' = 35;\<close>
        ((cons_prefix @ cons_h_str) ::= (A (N 35)));;
        \<comment> \<open>cons_t' = n_hashes_acc s;\<close>
        ((cons_prefix @ cons_t_str) ::= (A (V n_hashes_acc_str)));;
        \<comment> \<open>cons_ret' = 0;\<close>
        ((cons_prefix @ cons_ret_str) ::= (A (N 0)));;
        \<comment> \<open>cons_state = \<lparr>cons_h = cons_h', cons_t = cons_t', cons_ret = cons_ret'\<rparr>;\<close>
        \<comment> \<open>cons_ret_state = cons_imp cons_state;\<close>
        (invoke_subprogram cons_prefix cons_IMP_Minus)"

definition n_hashes_IMP_Minus where
  "n_hashes_IMP_Minus \<equiv>
    (
    WHILE n_hashes_n_str \<noteq>0 DO
          n_hashes_IMP_Minus_1;;
          \<comment> \<open>n_hashes_acc' = cons_ret cons_ret_state;\<close>
          ((n_hashes_acc_str) ::= (A (V (cons_prefix @ cons_ret_str))));;
          \<comment> \<open>n_hashes_n' = n_hashes_n s - 1\<close>
          ((n_hashes_n_str) ::= (Sub (V n_hashes_n_str) (N 1)))
    )"

definition "n_hashes_imp_to_HOL_state p s =
  \<lparr>n_hashes_acc = (s (add_prefix p n_hashes_acc_str)),
   n_hashes_n = (s (add_prefix p n_hashes_n_str))\<rparr>"

lemma n_hashes_IMP_Minus_correct_function:
  "(invoke_subprogram p n_hashes_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p n_hashes_acc_str)
      = n_hashes_state.n_hashes_acc (n_hashes_imp (n_hashes_imp_to_HOL_state p s))"
  apply(induction "n_hashes_imp_to_HOL_state p s" arbitrary: s s' t rule: n_hashes_imp.induct)
  apply(subst n_hashes_imp.simps)
  apply(simp only: n_hashes_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  apply(erule While_tE)
  sorry

end