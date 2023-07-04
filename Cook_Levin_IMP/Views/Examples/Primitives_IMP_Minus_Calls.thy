\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Primitives_IMP_Minus_Calls
  imports
    Compile_HOL_to_IMP_Minus_Calls
    IMP_Minus_Views.Let_To_IMP_Minus_Calls_Locale
    IMP_Minus_Views.Let_To_IMP_Minus_Calls_Tactics
begin

unbundle Com.no_com_syntax
unbundle IMP_Calls.com'_syntax

ML\<open>
  structure LT = Let_To_IMP_Minus_Calls_Tactics
  structure SCL = State_Cook_Levin_IMP_Minus_Calls
\<close>

subsection \<open>Division\<close>

fun divide_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "divide_acc x y acc =
    (if y \<noteq> 0
    then if x - (y - 1) \<noteq> 0
      then divide_acc (x - y) y (acc + 1)
      else acc
    else acc)"

declare divide_acc.simps[simp del]

lemma "divide_acc x y acc = acc + x div y"
  by (induction x arbitrary: acc rule: less_induct; subst divide_acc.simps)
  (auto simp: le_div_geq)

local_setup \<open>define_HOL_to_IMP_Minus_Calls lookup_fn @{context}
  @{thm divide_acc.simps[THEN eq_reflection]}\<close>

lemma HOL_to_IMP_Minus_Calls_induct:
  assumes imp_run: "(WHILE b\<noteq>0 DO c, ss) \<Rightarrow>'\<^bsup>t\<^esup> sf"
  and "ss b \<noteq> 0"
  and f_step: "\<And>s t s'. (c, s) \<Rightarrow>'\<^bsup>t\<^esup> s' \<Longrightarrow> s' b \<noteq> 0 \<Longrightarrow> f (fstate s) = f (step (fstate s))"
  and correspond_base: "\<And>s t s'. (c, s) \<Rightarrow>'\<^bsup>t\<^esup> s' \<Longrightarrow> s' b = 0 \<Longrightarrow> fstate s' = f (fstate s)"
  and correspond_step: "\<And>s t s'. (c, s) \<Rightarrow>'\<^bsup>t\<^esup> s' \<Longrightarrow> s' b \<noteq> 0 \<Longrightarrow> fstate s' = step (fstate s)"
  shows "fstate sf = f (fstate ss)"
using assms(1,2)
proof (induction "WHILE b\<noteq>0 DO c" "ss" t sf rule: big_step_t'_induct)
  case (WhileTrue' s1 t1 s2 t2 s3 t3)
  show ?case
  proof (cases "s2 b = 0")
    case True
    with WhileTrue' have "s2 = s3" by auto
    with correspond_base True WhileTrue' show ?thesis by auto
  next
    case False
    with correspond_step WhileTrue' have "step (fstate s1) = fstate s2" by auto
    moreover from False f_step WhileTrue' have "f (fstate s1) = f (step (fstate s1))"
      by auto
    ultimately have "f (fstate s1) = f (fstate s2)" by simp
    with False WhileTrue' show ?thesis by simp
  qed
qed simp

corollary HOL_to_IMP_Minus_Calls_induct':
  assumes imp_run: "(b ::= A (N 1);; WHILE b\<noteq>0 DO c, ss) \<Rightarrow>'\<^bsup>t\<^esup> sf"
  and b_irrelevant: "\<And>s n. fstate (s(b := n)) = fstate s"
  and f_step: "\<And>s t s'. (c, s) \<Rightarrow>'\<^bsup>t\<^esup> s' \<Longrightarrow> s' b \<noteq> 0 \<Longrightarrow> f (fstate s) = f (step (fstate s))"
  and correspond_base: "\<And>s t s'. (c, s) \<Rightarrow>'\<^bsup>t\<^esup> s' \<Longrightarrow> s' b = 0 \<Longrightarrow> fstate s' = f (fstate s)"
  and correspond_step: "\<And>s t s'. (c, s) \<Rightarrow>'\<^bsup>t\<^esup> s' \<Longrightarrow> s' b \<noteq> 0 \<Longrightarrow> fstate s' = step (fstate s)"
  shows "fstate sf = f (fstate ss)"
proof -
  from imp_run obtain t where b: "(WHILE b\<noteq>0 DO c, ss(b := 1)) \<Rightarrow>'\<^bsup>t\<^esup> sf" by auto
  then have "fstate sf = f (fstate (ss(b := 1)))"
    by (rule HOL_to_IMP_Minus_Calls_induct[where ?f=f and ?step=step]) (auto intro: assms)
  with b_irrelevant show ?thesis by simp
qed

definition "divide_acc_keys \<equiv> {''divide_acc_x'', ''divide_acc_y'', ''divide_acc_acc''}"

fun divide_acc_state :: "(string \<Rightarrow> nat) \<Rightarrow> (string \<Rightarrow> nat)" where
  "divide_acc_state s =
    (let x = ''divide_acc_x''; y = ''divide_acc_y''; acc = ''divide_acc_acc'' in
    if s y \<noteq> 0
    then if s x - (s y - 1) \<noteq> 0
      then divide_acc_state (s(x := (s x - s y), y := s y, acc := s acc + 1))
      else s
    else s)"
  termination
  oops

lemma
  "(divide_acc_IMP_Minus_Calls, s) \<Rightarrow>'\<^bsup>t\<^esup> s' \<Longrightarrow>
  s' ret = divide_acc_uncurried (divide_acc_args s)"
  apply (tactic \<open>LT.start_tac @{thm divide_acc_IMP_Minus_Calls_def} @{context} 1\<close>)
(* HOL_to_IMP_Minus_Calls_induct[where ?P="\<lambda>s. divide_acc (s ''divide_acc_x'') (s ''divide_acc_y'') (s ''divide_acc_acc'')"] *)
  (* apply (erule HOL_to_IMP_Minus_Calls_induct[where ?P="\<lambda>s. divide_acc (s ''divide_acc_x'') (s ''divide_acc_y'') (s ''divide_acc_acc'')"]) *)
  (* apply (simp add: divide_acc.simps)
  apply (rule conjI)
  apply (tactic \<open>LT.step_update_state_tac [] @{context} 1\<close>)+
  subgoal
  apply (tactic \<open>View_Util.thin_tacs (1 upto 39) 1\<close>)
  apply simp
  apply (subst (2) divide_acc.simps)
  apply (tactic \<open>SCL.rewrite_all_state_app_tac' View_Util.subst_first_asm_tac @{context} 1\<close>)
  apply (tactic \<open>SCL.rewrite_all_state_app_tac' View_Util.subst_first_tac @{context} 1\<close>)
  apply (tactic \<open>LT.finish_tac @{thm refl} @{context} 1\<close>) *)
  oops

definition "divide_tail x y \<equiv> divide_acc x y 0"

subsection \<open>Modulo\<close>

fun modulo :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "modulo x y =
    (if y \<noteq> 0
    then if x - (y - 1) \<noteq> 0
      then modulo (x - y) y
      else x
    else x)"

declare modulo.simps[simp del]

lemma "modulo x y = x mod y"
  by (induction x rule: less_induct; subst modulo.simps)
  (auto simp: le_mod_geq)

local_setup \<open>define_HOL_to_IMP_Minus_Calls lookup_fn @{context}
  @{thm modulo.simps[THEN eq_reflection]}\<close>
thm modulo_IMP_Minus_Calls_def

subsection \<open>Multiplication\<close>

fun multiply_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "multiply_acc x y acc = (if y \<noteq> 0
    then
      let
        r = modulo y 2;
        acc = if r \<noteq> 0 then acc + x else acc;
        x = x + x;
        y = divide_tail y 2
      in multiply_acc x y acc
    else acc)"
  termination by lexicographic_order

declare multiply_acc.simps[simp del]

lemma "multiply_acc x y acc = acc + x * y"
proof (induction y arbitrary: x acc rule: nat_less_induct)
  fix x y acc
  presume IH: "\<And>x y' acc. y' < y \<Longrightarrow> multiply_acc x y' acc = acc + x * y'"
  show "multiply_acc x y acc = acc + x * y"
  proof (cases y)
    case (Suc y')
    then have y_div_2_lt: "y div 2 < y" by auto
    show ?thesis
    proof (cases "y mod 2 = 0")
      case True
      with Suc have "multiply_acc x y acc = multiply_acc (x + x) (y div 2) acc"
        by (simp add: multiply_acc.simps) metis
      also with y_div_2_lt have "... = acc + (x + x) * (y div 2)" by (intro IH) auto
      also with True have "... = acc + x * y" by auto
      finally show ?thesis .
    next
      case False
        with Suc have "multiply_acc x y acc = multiply_acc (x + x) (y div 2) (acc + x)"
          by (simp add: multiply_acc.simps) metis
        also with y_div_2_lt have "... = acc + x + (x + x) * (y div 2)" by (intro IH) auto
        also with Suc False have "... = acc + x * y"
          by simp
          (metis One_nat_def add_diff_cancel_left' minus_mod_eq_div_mult mult.assoc mult.commute mult_2 plus_1_eq_Suc)
        finally show ?thesis .
      qed
  qed (simp add: multiply_acc.simps)
qed simp



(* lemma elemof_IMP_Minus_loop_body_correct_time:
  "(invoke_subprogram p elemof_IMP_loop_body, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = elemof_state_upd_time 0 (elemof_imp_to_HOL_state p s)"
  by (tactic \<open>HEADGOAL (Let_To_IMP_Minus_Tactics.IMP_Minus_run_finish_tac'
    @{thm elemof_state_upd_time_def} @{thm elemof_IMP_loop_body_def}
    @{thm elemof_imp_to_HOL_state_def}
    [(@{thm tl_IMP_Minus_correct}, @{thm tl_imp_to_HOL_state_def})]
    @{cterm "elemof_IMP_vars"} @{cterm p}
    @{context})\<close>)

interpretation A : Let_To_IMP_Minus where
  cond_var = elemof_while_cond and
  cond_let = elemof_imp_compute_loop_condition and
  body_let = elemof_state_upd and
  base_let = elemof_imp_after_loop and
  loop_let = elemof_imp and
  cond_imp = elemof_IMP_init_while_cond and
  body_imp = elemof_IMP_loop_body and
  base_imp = elemof_IMP_after_loop and
  imp_to_let_state = elemof_imp_to_HOL_state and
  vars = elemof_IMP_vars
  apply unfold_locales
  subgoal by (simp add: elemof_imp_to_HOL_state_def)
  subgoal by auto
  subgoal by (auto simp: elemof_complete_simps)
  subgoal for s t s' p
    apply (tactic \<open>HEADGOAL (Let_To_IMP_Minus_Tactics.IMP_Minus_run_finish_tac'
      @{thm elemof_state_upd_def} @{thm elemof_IMP_loop_body_def}
      @{thm elemof_imp_to_HOL_state_def}
      [(@{thm tl_IMP_Minus_correct}, @{thm tl_imp_to_HOL_state_def})]
      @{cterm "elemof_IMP_vars"} @{cterm p}
      @{context})\<close>)
    done
  subgoal for s t s' p
    apply (tactic \<open>HEADGOAL (Let_To_IMP_Minus_Tactics.IMP_Minus_run_finish_tac (resolve0_tac @{thms conjI})
      @{thm elemof_imp_compute_loop_condition_def} @{thm elemof_IMP_init_while_cond_def}
      @{thm elemof_imp_to_HOL_state_def}
      [
        (@{thm hd_IMP_Minus_correct}, @{thm hd_imp_to_HOL_state_def}),
        (@{thm NOTEQUAL_neq_zero_IMP_Minus_correct}, @{thm NOTEQUAL_neq_zero_imp_to_HOL_state_def}),
        (@{thm AND_neq_zero_IMP_Minus_correct}, @{thm AND_neq_zero_imp_to_HOL_state_def})
      ]
      @{cterm "elemof_IMP_vars"} @{cterm p}
      @{context})\<close>)
    done
  using elemof_imp.induct elemof_imp.simps by auto *)

end
