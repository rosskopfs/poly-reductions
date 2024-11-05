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

(*
lemmas fst_nat_eq_unfolded = HTHN.fst_nat_eq_unfolded[simplified case_prod_nat_def]
compile_nat fst_nat_eq_unfolded
HOL_To_IMP_Minus_correct fst_nat
  sorry


lemmas snd_nat_eq_unfolded = HTHN.snd_nat_eq_unfolded[simplified case_prod_nat_def]
compile_nat snd_nat_eq_unfolded
HOL_To_IMP_Minus_correct snd_nat
  sorry
*)

(* Problem: We have obtained an unconditional equation. However, we
still have to prove it to be related to the original HOL function.
TODO: how to prove the two functions to be related? Currently, we are
missing the right lemmas to make it automatic. *)
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

thm natify_eq_eq
(*automatically generated theorems*)
thm Rel_nat_destruct_Cons_nat
thm HOL_To_HOL_Nat_Basics.Rel_nat_list
thm fst_nat_eq_if_Rel_nat_list

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

(* manual does not work directly as "x" and "xs" are not available *)
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.rev_acc_nat
  sorry

lemma
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
  oops

  thm HTHN.rev_acc_nat_eq_unfolded
  thm Rel_nat_destruct_Cons_nat


lemma fst_nat_natify_Nil: "fst_nat (natify []) = 0"
  by (simp add: Nil_nat_def natify_list.simps)
lemma fst_nat_natify_Cons: "fst_nat (natify (x#xs)) = 1"
  by (simp add: Cons_nat_def natify_list.simps)

thm HTHN.rev_acc.induct
lemma
  assumes "s ''rev_acc_nat.args.x'' = natify x"
    and   "s ''rev_acc_nat.args.xa'' = natify xa"
   shows  "terminates_with_res_IMP_Minus (tailcall_to_IMP_Minus rev_acc_nat_IMP_tailcall) s
     ''rev_acc_nat.ret''
     (natify (HTHN.rev_acc x xa))"
  using assms apply -
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
proof (induction x xa arbitrary: s rule: HTHN.rev_acc.induct)
  case (1 acc)
  show ?case apply -
    apply (rule terminates_with_res_IMP_Tailcall_start)
    apply (subst (2) rev_acc_nat_IMP_tailcall_def)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    using 1 apply -
     apply (tactic \<open>HT.finish_non_tail_tac @{context} 1\<close>)
    by (simp add: fst_nat_natify_Nil 1)
next
  case (2 x xs acc)
  (* Ugly but quite helpful *)
  let ?S = "(STATE (interp_state (update_state (update_state (update_state (update_state (update_state (update_state (update_state (update_state (update_state (update_state (update_state (update_state (update_state (update_state (update_state (update_state (update_state (update_state (update_state (update_state (update_state (State s)
        ''.args.0'' (s ''rev_acc_nat.args.x'')) ''.args.1'' (s ''rev_acc_nat.args.xa'')) ''fst_nat.args.m'' (s ''rev_acc_nat.args.x''))
        ''fst_nat.ret'' (fst_nat (s ''rev_acc_nat.args.x''))) ''eq.args.x'' (fst_nat (s ''rev_acc_nat.args.x''))) ''eq.args.y'' 0)
        ''eq.ret'' (natify (fst_nat (s ''rev_acc_nat.args.x'') = 0))) ''.If.7'' (natify (fst_nat (s ''rev_acc_nat.args.x'') = 0)))
        ''snd_nat.args.m'' (s ''rev_acc_nat.args.x'')) ''snd_nat.ret'' (snd_nat (s ''rev_acc_nat.args.x''))) ''snd_nat.args.m'' (snd_nat (s ''rev_acc_nat.args.x'')))
        ''snd_nat.ret'' (snd_nat (snd_nat (s ''rev_acc_nat.args.x'')))) ''rev_acc_nat.args.x'' (snd_nat (snd_nat (s ''rev_acc_nat.args.x''))))
        ''snd_nat.args.m'' (s ''rev_acc_nat.args.x'')) ''snd_nat.ret'' (snd_nat (s ''rev_acc_nat.args.x''))) ''fst_nat.args.m'' (snd_nat (s ''rev_acc_nat.args.x'')))
        ''fst_nat.ret'' (fst_nat (snd_nat (s ''rev_acc_nat.args.x''))))
        ''Cons_nat.args.x'' (fst_nat (snd_nat (s ''rev_acc_nat.args.x'')))) ''Cons_nat.args.xa'' (s ''rev_acc_nat.args.xa'')) ''Cons_nat.ret'' (Cons_nat (fst_nat (snd_nat (s ''rev_acc_nat.args.x''))) (s ''rev_acc_nat.args.xa'')))
        ''rev_acc_nat.args.xa'' (Cons_nat (fst_nat (snd_nat (s ''rev_acc_nat.args.x''))) (s ''rev_acc_nat.args.xa'')))))"
  have x: "?S ''rev_acc_nat.args.x'' = natify xs"
    using 2(2) by (auto simp: STATE_interp_update_retrieve_key_eq_if Cons_nat_def natify_list.simps)
  have xa: "?S ''rev_acc_nat.args.xa'' = natify (x#acc)"
    using 2
    by (simp add: STATE_interp_update_retrieve_key_eq_if Cons_nat_def natify_list.simps)
  show ?case apply -
    apply (rule terminates_with_res_IMP_Tailcall_start)
    apply (subst (2) rev_acc_nat_IMP_tailcall_def)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)
    apply (simp add: fst_nat_natify_Cons 2)
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
    using 2(1)[of ?S, OF x xa]
    by (simp add: terminates_with_res_tTailI)
qed

end

context HOL_To_HOL_Nat
begin

lemma rev_eq_rev_acc_nil: "List.rev xs = rev_acc xs []" by simp

end

experiment
begin
interpretation HOL_To_HOL_Nat .
function_compile_nat rev_eq_rev_acc_nil
(*We couldn't use 'unconditional_nat' this way since the synthesised definition uses an auxiliary
function (rev_acc_nat) with TYPE('a) arguments.*)
print_statement rev_nat_eq_unfolded
end

context HOL_To_HOL_Nat
begin

(*we can fix this by registering the relatedness theorem of the unconditional rev_acc_nat function
to transfer instead*)
declare HNTIM.related_rev_acc_nat_unconditional[transfer_rule]
  and rev_acc_related_transfer[transfer_rule del] (*deletion is optional*)
function_compile_nat rev_eq_rev_acc_nil
print_statement rev_nat_eq_unfolded
end

context HOL_Nat_To_IMP_Minus
begin

unconditional_nat HTHN.rev_nat_eq_unfolded
declare rev_nat_unconditional.simps[simp del]
compile_nat rev_nat_unconditional.simps
HOL_To_IMP_Minus_correct rev_nat_unconditional by cook

(*TODO: derive these theorems automatically*)
lemma related_rev_nat_unconditional [transfer_rule]:
  "(Rel_nat ===> Rel_nat) rev_nat_unconditional rev"
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
unconditional_nat length_acc_nat_eq
declare length_acc_nat_unconditional.simps[simp del]
compile_nat length_acc_nat_unconditional.simps
HOL_To_IMP_Minus_correct length_acc_nat_unconditional by (cook mode = tailcall)

lemma related_length_acc_nat_unconditional [transfer_rule]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) length_acc_nat_unconditional HTHN.length_acc"
  sorry

end

context HOL_To_HOL_Nat
begin

(*introduce a definition because List.length is just an abbreviation*)
definition length where "length xs \<equiv> length_acc xs 0"

lemma length_eq_length [simp]: "length = List.length"
  unfolding length_def by simp

declare HNTIM.related_length_acc_nat_unconditional[transfer_rule]
function_compile_nat length_def

end

context HOL_Nat_To_IMP_Minus
begin

unconditional_nat HTHN.length_nat_eq_unfolded
declare length_nat_unconditional.simps[simp del]
compile_nat length_nat_unconditional.simps
HOL_To_IMP_Minus_correct length_nat_unconditional by cook

lemma related_length_nat_unconditional [transfer_rule]:
  "(Rel_nat ===> Rel_nat) length_nat_unconditional length"
  sorry

end

context HOL_To_HOL_Nat
begin

lemma append_eq_rev_acc_rev: "List.append xs ys = rev_acc (rev xs) ys"
  by simp

(*for some reason, transfer needs the lemma below instead of the existing, point-free version to
synthesise the right definition*)
(* declare HNTIM.related_rev_nat_unconditional[transfer_rule] *)

lemma related_rev_nat_unconditional [transfer_rule]:
  assumes "Rel_nat xs ys"
  shows "Rel_nat (HNTIM.rev_nat_unconditional xs) (rev ys)"
  by (fact rel_funD[OF HNTIM.related_rev_nat_unconditional assms])

(* schematic_goal
  assumes [transfer_rule]: "Rel_nat f xs"
  assumes [transfer_rule]: "Rel_nat g ys"
  shows "Rel_nat
    (HNTIM.rev_acc_nat_unconditional (HNTIM.rev_nat_unconditional f) g)
    (rev_acc (rev xs) ys)"
  by transfer_prover *)

function_compile_nat append_eq_rev_acc_rev

end

context HOL_Nat_To_IMP_Minus
begin

unconditional_nat HTHN.append_nat_eq_unfolded
declare append_nat_unconditional.simps[simp del]
compile_nat append_nat_unconditional.simps
HOL_To_IMP_Minus_correct append_nat_unconditional by cook

lemma related_append_nat_unconditional [transfer_rule]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) append_nat_unconditional append"
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
unconditional_nat zip_acc_nat_eq
declare zip_acc_nat_unconditional.simps [simp del]
compile_nat zip_acc_nat_unconditional.simps
HOL_To_IMP_Minus_correct zip_acc_nat_unconditional by (cook mode = tailcall)

lemma related_zip_acc_nat_unconditional [transfer_rule]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat ===> Rel_nat) zip_acc_nat_unconditional HTHN.zip_acc"
  sorry

end

context HOL_To_HOL_Nat
begin

lemma zip_eq_rev_zip_acc_nil: "List.zip xs ys = rev (zip_acc xs ys [])"
  by simp

(*TODO: why is this needed?*)
declare
  HNTIM.related_zip_acc_nat_unconditional[THEN rel_funD, THEN rel_funD, THEN rel_funD,transfer_rule]

(*TODO: something is quite slow here*)
function_compile_nat zip_eq_rev_zip_acc_nil

end

context HOL_Nat_To_IMP_Minus
begin

unconditional_nat HTHN.zip_nat_eq_unfolded
declare zip_nat_unconditional.simps [simp del]
compile_nat zip_nat_unconditional.simps
HOL_To_IMP_Minus_correct zip_nat_unconditional by cook

lemma related_zip_nat_unconditional [transfer_rule]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) zip_nat_unconditional List.zip"
  sorry

end

end
