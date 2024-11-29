\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Datatypes
  imports
    HOL_To_IMP_Minus_Arithmetics
begin

context HOL_To_HOL_Nat
begin

paragraph \<open>Pairs\<close>

function_compile_nat fst_def
function_compile_nat snd_def

end

context HOL_Nat_To_IMP_Minus
begin

thm Pair_nat_def
compile_nat Pair_nat_def
HOL_To_IMP_Minus_correct Pair_nat by cook

context
  fixes xs and xs' :: "'a :: compile_nat * 'b :: compile_nat"
  assumes rels: "Rel_nat xs xs'"
begin
  term HTHN.fst_nat
  print_statement HTHN.fst_nat_eq_unfolded
  print_statement HTHN.fst_nat_eq_unfolded[OF rels, unfolded case_list_nat_def]
end

end

paragraph \<open>Lists\<close>

context HOL_To_HOL_Nat
begin

fun rev_acc :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_acc [] acc = acc" |
  "rev_acc (x # xs) acc = rev_acc xs (x # acc)"
declare rev_acc.simps[simp del]

lemma rev_acc_eq_rev_append [simp]: "rev_acc xs ys = List.rev xs @ ys"
  by (induction xs ys rule: rev_acc.induct) (auto simp: rev_acc.simps)

case_of_simps rev_acc_eq : rev_acc.simps
function_compile_nat rev_acc_eq
print_theorems

end

context HOL_Nat_To_IMP_Minus
begin

compile_nat Cons_nat_def
HOL_To_IMP_Minus_correct Cons_nat by cook

compile_nat Nil_nat_def
HOL_To_IMP_Minus_correct Nil_nat by cook

(* FIXME: we could use the equation without unfolding case_list_nat_def if we prove
congruence lemmas for case_list_nat (otherwise the function package cannot prove termination) *)
lemmas rev_acc_nat_eq = HOL_To_HOL_Nat.rev_acc_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat rev_acc_nat_eq

thm eq_if_natify_eq
(*automatically generated theorems*)
thm Rel_nat_destruct_Cons
thm HOL_To_HOL_Nat_Basics.Rel_nat_list
thm Rel_nat_compile_nat
lemmas fst_nat_eq_if_Rel_nat_list = rel_funD[OF Rel_nat_eq_fst_nat_case_list]
thm Rel_nat_eq_fst_nat_case_list

lemma check_first_nat_ccontradictionE:
  assumes "fst_nat n = m"
  and "fst_nat n = k"
  obtains "fst_nat n = m" "k = m"
  using assms by simp

lemma check_first_nat_ccontradictionE':
  assumes "fst_nat n \<noteq> m"
  and "fst_nat n = k"
  obtains "fst_nat n \<noteq> m" "k \<noteq> m"
  using assms by simp

(*
Save reference to eq_unfolded in Symtab (\<rightarrow> under long name),
When saving in Termtab the types are instantiated weirdly
and the thm is not found
*)

HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.rev_acc_nat
  oops

(* Findings:
 - For introduction over multiple variable we need to apply the search for
    contradiction multiple times
 - Problem mit if-placement siehe count_acc Beispiel *)

lemma rev_acc_cor:
  assumes "Rel_nat (s ''rev_acc_nat.args.x'') (x :: 'a list)"
  assumes "Rel_nat (s ''rev_acc_nat.args.xa'') (xa :: 'a list)"
  shows "terminates_with_res_IMP_Minus (tailcall_to_IMP_Minus rev_acc_nat_IMP_tailcall) s ''rev_acc_nat.ret''
    (HTHN.rev_acc_nat TYPE('a :: compile_nat) (s ''rev_acc_nat.args.x'') (s ''rev_acc_nat.args.xa''))"
  using assms apply -
  apply (rule terminates_with_res_IMP_Minus_if_terminates_with_res_IMP_TailcallI)
    apply (subst rev_acc_nat_IMP_tailcall_def; simp)
  apply (subst rev_acc_nat_IMP_tailcall_def; simp)
  apply (induction "x" "xa" arbitrary: s rule: HTHN.rev_acc.induct)
  (*case []*)
  apply (subst (2) rev_acc_nat_IMP_tailcall_def, rule terminates_with_res_IMP_Tailcall_start)
   apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
    (*check the retrieved condition for a contradiction (needs to be built into the IF tactic*)
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption (*needs a smarter method*)
    apply simp
  apply (subst HTHN.rev_acc_nat_eq_unfolded)
  apply (assumption, assumption)
  apply (subst case_list_nat_def)
  apply (split if_splits; intro impI conjI; simp)
  apply (tactic \<open>HT.finish_non_tail_tac @{context} 1\<close>)
    (*we need to derive a contradiction*)
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption
    apply simp
  (*case x#xs*)
  apply (subst (2) rev_acc_nat_IMP_tailcall_def, rule terminates_with_res_IMP_Tailcall_start)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
    (*we need to derive a contradiction*)
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption
    apply simp
    (*check the retrievied condition for a contradiction*)
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption
    apply simp
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
  apply (subst HTHN.rev_acc_nat_eq_unfolded)
  apply (assumption, assumption)
  apply (subst case_list_nat_def)
  apply (split if_splits; intro impI conjI; simp)
  (*apply IH; prove side-conditions*)
  sorry

HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.rev_acc_nat
  using rev_acc_cor by blast

end

context HOL_To_HOL_Nat
begin
definition "rev2 xs \<equiv> rev_acc xs []"
function_compile_nat rev2_def
print_theorems

lemma rev_acc_Nil_Nil: "rev_acc [] [] = []"
  by simp

fun rev_test :: "'a list \<Rightarrow> nat list" where
  "rev_test [] = (if rev_acc [] ([]::'a list) = [] then [] else [Suc 0])"
| "rev_test xs = (if rev_acc xs [] = [] then [] else [Suc (Suc 0)])"
declare rev_acc.simps[simp del]
(* Try around with this function *)

case_of_simps rev_test_eq : rev_test.simps
function_compile_nat rev_test_eq
print_theorems

end

context HOL_Nat_To_IMP_Minus
begin

compile_nat HOL_To_HOL_Nat.rev2_nat_eq_unfolded

lemma "Rel_nat Nil_nat Nil"
  by (rule Rel_nat_Nil_nat)
thm Rel_nat_Nil_nat

thm STATE_interp_update_retrieve_key_eq_if

(* STATE_interp_retreive_key_eq_tac *)

HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.rev2_nat
  apply (rule terminates_with_res_IMP_Minus_if_terminates_with_res_IMP_TailcallI)
    apply (subst rev2_nat_IMP_tailcall_def; simp)
   apply (subst rev2_nat_IMP_tailcall_def; simp)
    (* No induction for defs *)
  apply (subst (2) rev2_nat_IMP_tailcall_def, rule terminates_with_res_IMP_Tailcall_start)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)

  (* Do step tac for tCall manually *)

  (* Split tSeq *)
  apply (tactic \<open>HOL_Nat_To_IMP_Tailcalls_Tactics.terminates_with_res_tSeq_tac @{context} 1\<close>)

  (* Apply tCall rule and apply correctness \<rightarrow> need to proof Rel_nat(s) *)
  apply (rule terminates_with_tCallI)
    apply (rule rev_acc_nat_IMP_Minus_imp_minus_correct)

  (* First rewrite state to actually result, afterwards use focused transfer prover *)
  apply (rule Rel_nat_rewrite_lhs)
  apply (tactic \<open>SUT.STATE_interp_retrieve_key_eq_tac (simp_tac @{context}) @{context} 1\<close>)
  apply (tactic \<open>HOL_Nat_To_IMP_Minus_Tactics_Base.transfer_foc_tac @{context} 1\<close>)

  (* Short version *)
  apply (tactic \<open>HOL_Nat_To_IMP_Minus_Tactics_Base.rel_condition_tac @{context} 1\<close>)

  apply (tactic \<open>SUT.STATE_interp_update_eq_STATE_interp_fun_upd (HOL_Nat_To_IMP_Tactics_Base.simp_update_tac @{context}) @{context} 1\<close>)
  
  apply (tactic \<open>HT.finish_non_tail_tac @{context} 1\<close>)

  (*
  using HTHN.rev2_nat_eq_unfolded HTHN.rev_acc_nat_eq_unfolded
  by fastforce *)

  apply transfer
  apply simp
  sorry

(* FIXME: we could use the equation without unfolding case_list_nat_def if we prove
congruence lemmas for case_list_nat (otherwise the function package cannot prove termination) *)
lemmas rev_test_nat_eq = HOL_To_HOL_Nat.rev_test_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat rev_test_nat_eq

HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.rev_test_nat
  apply (rule terminates_with_res_IMP_Minus_if_terminates_with_res_IMP_TailcallI)
    apply (subst rev_test_nat_IMP_tailcall_def; simp)
   apply (subst rev_test_nat_IMP_tailcall_def; simp)
  apply (induction y arbitrary: s rule: HTHN.rev_test.induct)
  (* case [] *)
  apply (subst (2) rev_test_nat_IMP_tailcall_def, rule terminates_with_res_IMP_Tailcall_start)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
  subgoal for s
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)

    (* Do step tac for tCall manually *)
    (* Split tSeq *)
    apply (tactic \<open>HOL_Nat_To_IMP_Tailcalls_Tactics.terminates_with_res_tSeq_tac @{context} 1\<close>)
  
    (* Apply tCall rule and apply correctness \<rightarrow> need to proof Rel_nat(s) *)
    apply (rule terminates_with_tCallI)
    apply (rule rev_acc_nat_IMP_Minus_imp_minus_correct)
  
    (* Always need to evaluate state, works more or less automatically *)
    using Rel_nat_Nil_nat (* Basic relations in simpset? *)
    apply (simp add: STATE_interp_update_retrieve_key_eq_if)
    using Rel_nat_Nil_nat (* Basic relations in simpset? *)
    apply (simp add: STATE_interp_update_retrieve_key_eq_if)
  
    apply (tactic \<open>SUT.STATE_interp_update_eq_STATE_interp_fun_upd (HOL_Nat_To_IMP_Tactics_Base.simp_update_tac @{context}) @{context} 1\<close>)

    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.finish_non_tail_tac @{context} 1\<close>)
    (* Apply transfer here *)
    subgoal
      sorry

    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.finish_non_tail_tac @{context} 1\<close>)
    (* First apply transfer then find a contradiction *)

    (* stupid sledgehammer: *)
    using Rel_nat_Nil_nat fst_nat_eq_if_Rel_nat_list rev_acc_nat_eq
    by force

    (* Find contradiction *)
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption (*needs a smarter method*)
   apply simp
  (* case (_#_) *)
  apply (subst (2) rev_test_nat_IMP_tailcall_def, rule terminates_with_res_IMP_Tailcall_start)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
    (* Find contradiction *)
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption (*needs a smarter method*)
    apply simp
  subgoal for x xs s
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)

    (* Do step tac for tCall manually *)
    (* Split tSeq *)
    apply (tactic \<open>HOL_Nat_To_IMP_Tailcalls_Tactics.terminates_with_res_tSeq_tac @{context} 1\<close>)
  
    (* Apply tCall rule and apply correctness \<rightarrow> need to proof Rel_nat(s) *)
    apply (rule terminates_with_tCallI)
    apply (rule rev_acc_nat_IMP_Minus_imp_minus_correct)
  
    (* Always need to evaluate state, works more or less automatically *)
    apply (simp add: STATE_interp_update_retrieve_key_eq_if)
    subgoal sorry

    using Rel_nat_Nil_nat (* Basic relations in simpset? *)
    apply (simp add: STATE_interp_update_retrieve_key_eq_if)
  
    apply (tactic \<open>SUT.STATE_interp_update_eq_STATE_interp_fun_upd (HOL_Nat_To_IMP_Tactics_Base.simp_update_tac @{context}) @{context} 1\<close>)

    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
     apply (tactic \<open>HT.finish_non_tail_tac @{context} 1\<close>)
    (* Apply transfer \<rightarrow> find contradiction *)
    subgoal
      sorry

    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.finish_non_tail_tac @{context} 1\<close>)
    (* Apply transfer *)

    (* Stupid sledgehammer proof *)
    by (smt (z3) Rel_nat_destruct_Cons(1) Rel_nat_suc_nat
        \<open>\<And>ya. Rel_nat (s ''rev_test_nat.args.x'') (x # xs) \<Longrightarrow> fst_nat (s ''rev_test_nat.args.x'') \<noteq> 0 \<Longrightarrow> Rel_nat (Cons_nat (fst_nat (snd_nat (s ''rev_test_nat.args.x''))) (snd_nat (snd_nat (s ''rev_test_nat.args.x'')))) ya\<close>
        left_uniqueD left_unique_Rel_nat n_not_Suc_n rel_funD)
  sorry

  

end

context HOL_To_HOL_Nat
begin

fun length_acc :: "'a list \<Rightarrow> nat \<Rightarrow> nat" where
  "length_acc [] acc = acc" |
  "length_acc (_ # xs) acc = length_acc xs (Suc acc)"
declare length_acc.simps[simp del]

lemma length_acc_eq_length_add [simp]: "length_acc xs n = List.length xs + n"
  by (induction xs n rule: length_acc.induct) (auto simp: length_acc.simps)

case_of_simps length_acc_eq : length_acc.simps
function_compile_nat length_acc_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas length_acc_nat_eq = HTHN.length_acc_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat length_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.length_acc_nat
  oops

lemma "Rel_nat (s ''length_acc_nat.args.x'') (y::'a list) \<Longrightarrow>
       Rel_nat (s ''length_acc_nat.args.xa'') (ya::nat) \<Longrightarrow>
    terminates_with_res_IMP_Minus (tailcall_to_IMP_Minus length_acc_nat_IMP_tailcall)
      s ''length_acc_nat.ret''
     (HTHN.length_acc_nat TYPE('a::compile_nat) (s ''length_acc_nat.args.x'') (s ''length_acc_nat.args.xa''))"
  apply (rule terminates_with_res_IMP_Minus_if_terminates_with_res_IMP_TailcallI)
    apply (subst length_acc_nat_IMP_tailcall_def; simp)
  apply (subst length_acc_nat_IMP_tailcall_def; simp)
  apply (induction "y" "ya" arbitrary: s rule: HTHN.length_acc.induct)
  (*case []*)
  apply (subst (2) length_acc_nat_IMP_tailcall_def, rule terminates_with_res_IMP_Tailcall_start)
   apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
    (*check the retrieved condition for a contradiction (needs to be built into the IF tactic*)
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption (*needs a smarter method*)
    apply simp
  apply (subst HTHN.length_acc_nat_eq_unfolded)
  apply (assumption, assumption)
  apply (subst case_list_nat_def)
  apply (split if_splits; intro impI conjI; simp)
  apply (tactic \<open>HT.finish_non_tail_tac @{context} 1\<close>)
    (*we need to derive a contradiction*)
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption
    apply simp
  (*case x#xs*)
  apply (subst (2) length_acc_nat_IMP_tailcall_def, rule terminates_with_res_IMP_Tailcall_start)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
    (*we need to derive a contradiction*)
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption
    apply simp
    (*check the retrievied condition for a contradiction*)
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption
    apply simp
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
  apply (subst HTHN.length_acc_nat_eq_unfolded)
  apply (assumption, assumption)
  apply (subst case_list_nat_def)
  apply (split if_splits; intro impI conjI; simp)
  sorry
end

context HOL_To_HOL_Nat
begin

fun zip_acc :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "zip_acc [] _ acc = acc" |
  "zip_acc _ [] acc = acc" |
  "zip_acc (x # xs) (y # ys) acc = zip_acc xs ys ((x, y) # acc)"
declare zip_acc.simps[simp del]

lemma rev_zip_acc_eq_rev_append_zip [simp]: "rev (zip_acc xs ys zs) = rev zs @ List.zip xs ys"
  by (induction xs ys zs rule: zip_acc.induct) (auto simp: zip_acc.simps)

case_of_simps zip_acc_eq : zip_acc.simps
function_compile_nat zip_acc_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas zip_acc_nat_eq = HTHN.zip_acc_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat zip_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.zip_acc_nat
  sorry

lemma "Rel_nat (s ''zip_acc_nat.args.x'') (y::'a list) \<Longrightarrow>
    Rel_nat (s ''zip_acc_nat.args.xa'') (ya::'b list) \<Longrightarrow>
    Rel_nat (s ''zip_acc_nat.args.xb'') (yb::('a * 'b) list) \<Longrightarrow>
    terminates_with_res_IMP_Minus (tailcall_to_IMP_Minus zip_acc_nat_IMP_tailcall)
      s ''zip_acc_nat.ret''
     (HTHN.zip_acc_nat TYPE('a::compile_nat) TYPE('b::compile_nat)
       (s ''zip_acc_nat.args.x'') (s ''zip_acc_nat.args.xa'') (s ''zip_acc_nat.args.xb''))"
  apply (rule terminates_with_res_IMP_Minus_if_terminates_with_res_IMP_TailcallI)
   apply (subst zip_acc_nat_IMP_tailcall_def; simp)
   apply (subst zip_acc_nat_IMP_tailcall_def; simp)
  apply (induction y ya yb arbitrary: s rule: HTHN.zip_acc.induct)
  (*case [] _*)
  apply (subst (2) zip_acc_nat_IMP_tailcall_def, rule terminates_with_res_IMP_Tailcall_start)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
    (*check the retrieved condition for a contradiction (needs to be built into the IF tactic*)
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption (*needs a smarter method*)
    apply simp
  apply (subst HTHN.zip_acc_nat_eq_unfolded)
    apply (assumption, assumption, assumption)
    apply (subst case_list_nat_def)
    apply (split if_splits; intro impI conjI; simp)
    apply (tactic \<open>HT.finish_non_tail_tac @{context} 1\<close>)
    (*we need to derive a contradiction*)
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
     apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption
    apply simp
  (* case _ []*)
  apply (subst (2) zip_acc_nat_IMP_tailcall_def, rule terminates_with_res_IMP_Tailcall_start)
   apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
      (*check first case \<rightarrow> find contradiction*)
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption (*needs a smarter method*)
    apply simp
   apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
     apply assumption (*needs a smarter method*)
  subgoal for v
    sorry

    (* Need to apply the search for contradiction multiple times ! *)
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption
    apply simp

  (*case x#xs*)
  apply (subst (2) zip_acc_nat_IMP_tailcall_def, rule terminates_with_res_IMP_Tailcall_start)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
    (*we need to derive a contradiction*)
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption
    apply simp
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
    (*check the retrievied condition for a contradiction*)
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption
    apply simp
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
    subgoal for v
      sorry
    done

end


context HOL_To_HOL_Nat
begin

fun count_acc :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat" where
  "count_acc a [] n = n"
| "count_acc a (x#xs) n = (if x = a then count_acc a xs (Suc n) else count_acc a xs n)"
declare count_acc.simps[simp del]

case_of_simps count_acc_eq : count_acc.simps
function_compile_nat count_acc_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas count_acc_nat_eq = HTHN.count_acc_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat count_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.count_acc_nat
  oops

lemma count_acc_cor: "Rel_nat (s ''count_acc_nat.args.x'') (y::'a) \<Longrightarrow>
    Rel_nat (s ''count_acc_nat.args.xa'') (ya::'a list) \<Longrightarrow>
    Rel_nat (s ''count_acc_nat.args.xb'') (yb::nat) \<Longrightarrow>
    terminates_with_res_IMP_Minus
     (tailcall_to_IMP_Minus count_acc_nat_IMP_tailcall) s
     ''count_acc_nat.ret''
     (HTHN.count_acc_nat TYPE('a::compile_nat)
       (s ''count_acc_nat.args.x'')
       (s ''count_acc_nat.args.xa'')
       (s ''count_acc_nat.args.xb''))"
  apply (rule terminates_with_res_IMP_Minus_if_terminates_with_res_IMP_TailcallI)
   apply (subst count_acc_nat_IMP_tailcall_def; simp)
   apply (subst count_acc_nat_IMP_tailcall_def; simp)
  apply (induction y ya yb arbitrary: s rule: HTHN.count_acc.induct)
  (* case [] *)
  apply (subst (2) count_acc_nat_IMP_tailcall_def, rule terminates_with_res_IMP_Tailcall_start)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
    (* correct case *)
    apply (subst HTHN.count_acc_nat_eq_unfolded)
    apply (assumption, assumption, assumption)
    apply (subst case_list_nat_def)
    apply (split if_splits; intro impI conjI; simp)
    apply (tactic \<open>HT.finish_non_tail_tac @{context} 1\<close>)
    (* wrong case *)
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption
    apply simp
  (* case x#xs *)
  apply (subst (2) count_acc_nat_IMP_tailcall_def, rule terminates_with_res_IMP_Tailcall_start)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption
    apply simp
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
    apply (subst HTHN.count_acc_nat_eq_unfolded)
    apply (assumption, assumption, assumption)
    apply (subst case_list_nat_def)
    apply (split if_splits; intro impI conjI; simp)
    subgoal for v
    sorry
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
    apply (subst HTHN.count_acc_nat_eq_unfolded)
    apply (assumption, assumption, assumption)
    apply (subst case_list_nat_def)
    apply (split if_splits; intro impI conjI; simp)
    subgoal for v
    sorry
  done

HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.count_acc_nat
  using count_acc_cor by blast

end


context HOL_To_HOL_Nat
begin

fun count_acc2 :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat" where
  "count_acc2 a [] n = n"
| "count_acc2 a (x#xs) n = count_acc2 a xs (if x = a then Suc n else n)"
declare count_acc2.simps[simp del]

case_of_simps count_acc2_eq : count_acc2.simps
function_compile_nat count_acc2_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas count_acc2_nat_eq = HTHN.count_acc2_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat count_acc2_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.count_acc2_nat
  oops

lemma count_acc2_cor: "Rel_nat (s ''count_acc2_nat.args.x'') (y::'a) \<Longrightarrow>
    Rel_nat (s ''count_acc2_nat.args.xa'') (ya::'a list) \<Longrightarrow>
    Rel_nat (s ''count_acc2_nat.args.xb'') (yb::nat) \<Longrightarrow>
    terminates_with_res_IMP_Minus
     (tailcall_to_IMP_Minus count_acc2_nat_IMP_tailcall) s
     ''count_acc2_nat.ret''
     (HTHN.count_acc2_nat TYPE('a::compile_nat)
       (s ''count_acc2_nat.args.x'')
       (s ''count_acc2_nat.args.xa'')
       (s ''count_acc2_nat.args.xb''))"
  apply (rule terminates_with_res_IMP_Minus_if_terminates_with_res_IMP_TailcallI)
   apply (subst count_acc2_nat_IMP_tailcall_def; simp)
   apply (subst count_acc2_nat_IMP_tailcall_def; simp)
  apply (induction y ya yb arbitrary: s rule: HTHN.count_acc.induct)
  (* case [] *)
  apply (subst (2) count_acc2_nat_IMP_tailcall_def, rule terminates_with_res_IMP_Tailcall_start)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
    (* correct case *)
    apply (subst HTHN.count_acc2_nat_eq_unfolded)
    apply (assumption, assumption, assumption)
    apply (subst case_list_nat_def)
    apply (split if_splits; intro impI conjI; simp)
    apply (tactic \<open>HT.finish_non_tail_tac @{context} 1\<close>)
    (* wrong case *)
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption
    apply simp
  (* case x#xs *)
  apply (subst (2) count_acc2_nat_IMP_tailcall_def, rule terminates_with_res_IMP_Tailcall_start)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
    apply (erule check_first_nat_ccontradictionE check_first_nat_ccontradictionE')
    apply (rule fst_nat_eq_if_Rel_nat_list)
    apply assumption
    apply simp
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
  sorry

HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.count_acc2_nat
  using count_acc2_cor by blast


end