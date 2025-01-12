theory Playground
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

compile_nat Pair_nat_def
HOL_To_IMP_Minus_correct Pair_nat by cook

end

paragraph \<open>Lists\<close>

context HOL_To_HOL_Nat
begin

fun rev_acc :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_acc [] acc = acc" |
  "rev_acc (x # xs) acc = rev_acc xs (x # acc)"
declare rev_acc.simps[simp del]

lemma rev_acc_eq_rev_append: "rev_acc xs ys = List.rev xs @ ys"
  by (induction xs ys rule: rev_acc.induct) (auto simp: rev_acc.simps)

case_of_simps rev_acc_eq : rev_acc.simps
function_compile_nat rev_acc_eq

lemma rev_eq_rev_acc_nil: "rev xs = rev_acc xs []"
  unfolding rev_acc_eq_rev_append by simp

function_compile_nat rev_eq_rev_acc_nil

lemma append_eq_rev_acc_rev: "append xs ys = rev_acc (rev xs) ys"
  by (auto simp: rev_acc_eq_rev_append)

function_compile_nat append_eq_rev_acc_rev

end

context HOL_Nat_To_IMP_Minus
begin

compile_nat Cons_nat_def
HOL_To_IMP_Minus_correct Cons_nat by cook

compile_nat Nil_nat_def
HOL_To_IMP_Minus_correct Nil_nat by cook

lemmas rev_acc_nat_eq = HTHN.rev_acc_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat rev_acc_nat_eq

lemma rev_acc_cor:
  assumes "Rel_nat (s ''rev_acc_nat.args.x'') (x :: 'a list)"
  assumes "Rel_nat (s ''rev_acc_nat.args.xa'') (xa :: 'a list)"
  shows "terminates_with_res_IMP_Minus (tailcall_to_IMP_Minus rev_acc_nat_IMP_tailcall) s ''rev_acc_nat.ret''
    (HOL_To_HOL_Nat.rev_acc_nat TYPE('a :: compile_nat) (s ''rev_acc_nat.args.x'') (s ''rev_acc_nat.args.xa''))"
  using assms apply -
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  apply (induction "x" "xa" arbitrary: s rule: HTHN.rev_acc.induct)
  (*case []*)
  apply (tactic \<open>HT.start_run_finish_case_tac
    HT.get_IMP_def HT.get_imp_minus_correct HB.get_HOL_eqs @{context} 1\<close>)
  (*case x # xs*)
  apply (tactic \<open>HT.start_case_tac HT.get_IMP_def @{context} 1\<close>)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
  apply (tactic \<open>HT.run_HOL_fun_tac HB.get_HOL_eqs @{context} 1\<close>)
  (*FIXME: why isn't run_HOL_fun_tac splitting?*)
  apply ((split if_split | succeed); intro conjI impI)
  apply ((simp add: HOL_To_IMP_finish_simps | succeed); ((elim notE; assumption) | succeed))
  apply ((simp add: HOL_To_IMP_finish_simps | succeed); ((elim notE; assumption) | succeed))
  (*apply IH*)
  sorry

HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.rev_acc_nat
  using rev_acc_cor by auto

compile_nat HTHN.rev_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.rev_nat by cook

compile_nat HTHN.append_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.append_nat by cook

end

context HOL_To_HOL_Nat
begin

fun rev_test :: "'a list \<Rightarrow> nat list" where
  "rev_test [] = (if rev_acc [] ([]::'a list) = [] then [] else [Suc 0])"
| "rev_test xs = (if rev_acc xs [] = [] then [] else [Suc (Suc 0)])"
declare rev_acc.simps[simp del]

case_of_simps rev_test_eq : rev_test.simps
function_compile_nat rev_test_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas rev_test_nat_eq = HOL_To_HOL_Nat.rev_test_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat rev_test_nat_eq

HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.rev_test_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  apply (induction y arbitrary: s rule: HTHN.rev_test.induct)
  (* case [] *)
  apply (tactic \<open>HT.start_case_tac HT.get_IMP_def @{context} 1\<close>)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
  apply (tactic \<open>HT.finish_tac HB.get_HOL_eqs @{context} 1\<close>)
  apply ((split if_split | succeed); intro conjI impI)
  apply ((simp add: HOL_To_IMP_finish_simps | succeed); ((elim notE; assumption) | succeed))
  apply ((simp add: HOL_To_IMP_finish_simps | succeed); ((elim notE; assumption) | succeed))
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
  apply (tactic \<open>HT.finish_tac HB.get_HOL_eqs @{context} 1\<close>)
  (* case (_#_) *)
  supply Rel_nat_destruct_Cons[Rel_nat_related]
  apply (tactic \<open>HT.start_run_finish_case_tac
    HT.get_IMP_def HT.get_imp_minus_correct HB.get_HOL_eqs @{context} 1\<close>)
  done

end

context HOL_To_HOL_Nat
begin

fun length_acc :: "'a list \<Rightarrow> nat \<Rightarrow> nat" where
  "length_acc [] acc = acc" |
  "length_acc (_ # xs) acc = length_acc xs (Suc acc)"
declare length_acc.simps[simp del]

lemma length_acc_eq_length_add: "length_acc xs n = length xs + n"
  by (induction xs n rule: length_acc.induct) (auto simp: length_acc.simps)

case_of_simps length_acc_eq : length_acc.simps
(*FIXME: transfer synthesis picks wrong variable in the case of natural numbers*)
function_compile_nat length_acc_eq

lemma length_acc_nat_eq_unfolded':
  assumes "Rel_nat x (y :: 'a list)"
  and "Rel_nat xa (ya :: nat)"
  shows "length_acc_nat TYPE('a :: compile_nat) x xa =
    case_list_nat xa (\<lambda>x2ba x1ba. length_acc_nat TYPE('a) x1ba (Suc xa)) x"
proof -
  from assms have "xa = ya" by (auto simp: Rel_nat_nat_eq_eq)
  with length_acc_nat_eq_unfolded[OF assms] show ?thesis by blast
qed

lemma length_eq_length_acc_zero: "length xs = length_acc xs 0"
  by (simp add: length_acc_eq_length_add)

function_compile_nat length_eq_length_acc_zero

end

context HOL_Nat_To_IMP_Minus
begin

lemmas length_acc_nat_eq = HTHN.length_acc_nat_eq_unfolded'[simplified case_list_nat_def]
compile_nat length_acc_nat_eq

lemma length_acc_nat_cor: "Rel_nat (s ''length_acc_nat.args.x'') (y::'a list) \<Longrightarrow>
       Rel_nat (s ''length_acc_nat.args.xa'') (ya::nat) \<Longrightarrow>
    terminates_with_res_IMP_Minus (tailcall_to_IMP_Minus length_acc_nat_IMP_tailcall)
      s ''length_acc_nat.ret''
     (HTHN.length_acc_nat TYPE('a::compile_nat) (s ''length_acc_nat.args.x'') (s ''length_acc_nat.args.xa''))"
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  apply (induction "y" "ya" arbitrary: s rule: HTHN.length_acc.induct)
  (*case []*)
  apply (tactic \<open>HT.start_run_finish_case_tac
    HT.get_IMP_def HT.get_imp_minus_correct
    (fn _ => fn _ => SOME @{thms HTHN.length_acc_nat_eq_unfolded'}) @{context} 1\<close>)
  (*case x#xs*)
  apply (tactic \<open>HT.start_case_tac HT.get_IMP_def @{context} 1\<close>)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
  apply (tactic \<open>HT.run_HOL_fun_tac
    (fn _ => fn _ => SOME @{thms HTHN.length_acc_nat_eq_unfolded'}) @{context} 1\<close>)
  apply ((split if_split | succeed); intro conjI impI)
  apply ((simp add: HOL_To_IMP_finish_simps | succeed); ((elim notE; assumption) | succeed))
  apply ((simp add: HOL_To_IMP_finish_simps | succeed); ((elim notE; assumption) | succeed))
  (*apply IH*)
  sorry

HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.length_acc_nat
  using length_acc_nat_cor by blast

end

context HOL_To_HOL_Nat
begin

fun zip_acc :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "zip_acc [] _ acc = acc" |
  "zip_acc _ [] acc = acc" |
  "zip_acc (x # xs) (y # ys) acc = zip_acc xs ys ((x, y) # acc)"
declare zip_acc.simps[simp del]

lemma rev_zip_acc_eq_rev_append_zip [simp]: "rev (zip_acc xs ys zs) = rev zs @ zip xs ys"
  by (induction xs ys zs rule: zip_acc.induct) (auto simp: zip_acc.simps)

case_of_simps zip_acc_eq : zip_acc.simps
function_compile_nat zip_acc_eq

lemma zip_req_rev_zip_acc_nil: "zip xs ys = rev (zip_acc xs ys [])"
  by (simp add: rev_zip_acc_eq_rev_append_zip)

function_compile_nat zip_req_rev_zip_acc_nil

end

context HOL_Nat_To_IMP_Minus
begin

lemmas zip_acc_nat_eq = HTHN.zip_acc_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat zip_acc_nat_eq

lemma zip_acc_nat_cor: "Rel_nat (s ''zip_acc_nat.args.x'') (y::'a list) \<Longrightarrow>
    Rel_nat (s ''zip_acc_nat.args.xa'') (ya::'b list) \<Longrightarrow>
    Rel_nat (s ''zip_acc_nat.args.xb'') (yb::('a * 'b) list) \<Longrightarrow>
    terminates_with_res_IMP_Minus (tailcall_to_IMP_Minus zip_acc_nat_IMP_tailcall)
      s ''zip_acc_nat.ret''
     (HTHN.zip_acc_nat TYPE('a::compile_nat) TYPE('b::compile_nat)
       (s ''zip_acc_nat.args.x'') (s ''zip_acc_nat.args.xa'') (s ''zip_acc_nat.args.xb''))"
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  apply (induction y ya yb arbitrary: s rule: HTHN.zip_acc.induct)
  (*case [] _*)
  apply (tactic \<open>HT.start_run_finish_case_tac
    HT.get_IMP_def HT.get_imp_minus_correct HB.get_HOL_eqs @{context} 1\<close>)
  (* case _ []*)
  apply (tactic \<open>HT.start_run_finish_case_tac
    HT.get_IMP_def HT.get_imp_minus_correct HB.get_HOL_eqs @{context} 1\<close>)
  (*case x#xs*)
  apply (tactic \<open>HT.start_case_tac HT.get_IMP_def @{context} 1\<close>)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
  apply (tactic \<open>HT.run_HOL_fun_tac HB.get_HOL_eqs @{context} 1\<close>)
  (*FIXME: why isn't run_HOL_fun_tac splitting?*)
  apply ((split if_split | succeed); intro conjI impI)
  apply ((simp add: HOL_To_IMP_finish_simps | succeed); ((elim notE; assumption) | succeed))
  apply ((simp add: HOL_To_IMP_finish_simps | succeed); ((elim notE; assumption) | succeed))
  (*apply the IH*)
  sorry

HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.zip_acc_nat
  using zip_acc_nat_cor by blast

end

context HOL_To_HOL_Nat
begin

fun count_acc :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat" where
  "count_acc a [] n = n"
| "count_acc a (x#xs) n = count_acc a xs (if x = a then Suc n else n)"
declare count_acc.simps[simp del]

case_of_simps count_acc_eq : count_acc.simps
function_compile_nat count_acc_eq

lemma count_acc_nat_eq_unfolded':
  assumes "Rel_nat (x::nat) (y::'a::compile_nat)"
  assumes "Rel_nat (xa::nat) (ya::'a::compile_nat list)"
  assumes "Rel_nat (xb::nat) (yb::nat)"
  shows "count_acc_nat TYPE('a::compile_nat) x xa xb =
    case_list_nat xb (\<lambda>(x3ba::nat) x2ca::nat. count_acc_nat TYPE('a::compile_nat) x x2ca
      (if x3ba = x then Suc xb else xb)) xa"
proof -
  from assms have "xb = yb" by (auto simp: Rel_nat_nat_eq_eq)
  with count_acc_nat_eq_unfolded[OF assms] show ?thesis by auto
qed

end

context HOL_Nat_To_IMP_Minus
begin

lemmas count_acc_nat_eq = HTHN.count_acc_nat_eq_unfolded'[simplified case_list_nat_def]
compile_nat count_acc_nat_eq

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
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  apply (induction y ya yb arbitrary: s rule: HTHN.count_acc.induct)
  (* case [] *)
  apply (tactic \<open>HT.start_run_finish_case_tac
    HT.get_IMP_def HT.get_imp_minus_correct
    (fn _ => fn _ => SOME @{thms HTHN.count_acc_nat_eq_unfolded'}) @{context} 1\<close>)
  (* case x#xs *)
  apply (tactic \<open>HT.start_case_tac HT.get_IMP_def @{context} 1\<close>)
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
  apply (tactic \<open>HT.run_HOL_fun_tac HB.get_HOL_eqs @{context} 1\<close>)
  apply ((split if_split | succeed); intro conjI impI)
  apply ((simp add: HOL_To_IMP_finish_simps | succeed); ((elim notE; assumption) | succeed))
  apply ((simp add: HOL_To_IMP_finish_simps | succeed); ((elim notE; assumption) | succeed))
  (*apply the IH*)
  defer
  apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
  apply (tactic \<open>HT.run_HOL_fun_tac HB.get_HOL_eqs @{context} 1\<close>)
  apply ((split if_split | succeed); intro conjI impI)
  apply ((simp add: HOL_To_IMP_finish_simps | succeed); ((elim notE; assumption) | succeed))
  apply ((simp add: HOL_To_IMP_finish_simps | succeed); ((elim notE; assumption) | succeed))
  (*apply the IH*)
  sorry

HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.count_acc_nat
  using count_acc_cor by blast

end

end