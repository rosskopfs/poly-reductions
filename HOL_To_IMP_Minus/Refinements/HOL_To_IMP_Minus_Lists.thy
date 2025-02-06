\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Jonas Stahl"\<close>
theory HOL_To_IMP_Minus_Lists
  imports
    HOL_To_IMP_Minus_Pairs
begin

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

declare Rel_nat_selector_list[Rel_nat]

compile_nat Cons_nat_def
HOL_To_IMP_Minus_correct Cons_nat by cook

compile_nat Nil_nat_def
HOL_To_IMP_Minus_correct Nil_nat by cook

lemmas rev_acc_nat_eq = HTHN.rev_acc_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat rev_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.rev_acc_nat by cook

compile_nat HTHN.rev_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.rev_nat by cook

compile_nat HTHN.append_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.append_nat by cook

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
function_compile_nat length_acc_eq

definition length where "length (xs :: 'a list) \<equiv> List.length xs"

lemma list_length_eq_length: "List.length = length"
  unfolding length_def by simp

lemma length_eq_length_acc_zero: "length xs = length_acc xs 0"
  by (simp add: length_acc_eq_length_add list_length_eq_length)

function_compile_nat length_eq_length_acc_zero

end

context HOL_Nat_To_IMP_Minus
begin

lemmas length_acc_nat_eq = HTHN.length_acc_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat length_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.length_acc_nat by cook

compile_nat HTHN.length_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.length_nat by cook

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

HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.zip_acc_nat by cook

compile_nat HTHN.zip_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.zip_nat by cook

end

context HOL_To_HOL_Nat
begin

fun count_acc :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat" where
  "count_acc a [] n = n"
| "count_acc a (x#xs) n = count_acc a xs (if x = a then Suc n else n)"
declare count_acc.simps[simp del]

case_of_simps count_acc_eq : count_acc.simps
function_compile_nat count_acc_eq

definition "count x xs \<equiv> count_acc x xs 0"
function_compile_nat count_def

end

context HOL_Nat_To_IMP_Minus
begin

lemmas count_acc_nat_eq = HTHN.count_acc_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat count_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.count_acc_nat by cook

compile_nat HTHN.count_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.count_nat by cook

end

context HOL_To_HOL_Nat
begin

fun map_acc :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'b list"  where
  "map_acc f [] acc = rev acc"
| "map_acc f (x#xs) acc = map_acc f xs (f x # acc)"
declare map_acc.simps[simp del]

lemma map_acc_eq_rev_append_map: "map_acc f xs acc = rev acc @ map f xs"
  by (induction xs arbitrary: acc) (auto simp: map_acc.simps)

case_of_simps map_acc_eq : map_acc.simps

lemma map_eq_map_acc_nil: "map f xs = map_acc f xs []"
  by (simp add: map_acc_eq_rev_append_map)

fun filter_acc :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"  where
  "filter_acc p [] acc = rev acc"
| "filter_acc p (x#xs) acc = filter_acc p xs (case p x of True \<Rightarrow> x # acc | False \<Rightarrow> acc)"
declare filter_acc.simps[simp del]

lemma filter_acc_eq_rev_append_map: "filter_acc p xs acc = rev acc @ filter p xs"
  by (induction xs arbitrary: acc) (simp_all add: filter_acc.simps)

case_of_simps filter_acc_eq : filter_acc.simps

lemma filter_eq_filter_acc_nil: "filter p xs = filter_acc p xs []"
  by (simp add: filter_acc_eq_rev_append_map)

fun enumerate_acc :: "nat \<Rightarrow> 'a list \<Rightarrow> (nat \<times> 'a) list \<Rightarrow> (nat \<times> 'a) list"  where
  "enumerate_acc i [] acc = rev acc"
| "enumerate_acc i (x#xs) acc = enumerate_acc (Suc i) xs ((i, x) # acc)"
declare enumerate_acc.simps[simp del]

lemma enumerate_acc_eq_rev_append_enumerate: "enumerate_acc i xs acc = rev acc @ enumerate i xs"
  by (induction xs arbitrary: acc i) (auto simp add: enumerate_acc.simps)

case_of_simps enumerate_acc_eq : enumerate_acc.simps
function_compile_nat enumerate_acc_eq

lemma enumerate_eq_enumerate_acc_nil: "enumerate f xs = enumerate_acc f xs []"
  by (simp add: enumerate_acc_eq_rev_append_enumerate)

function_compile_nat enumerate_eq_enumerate_acc_nil

end

context HOL_Nat_To_IMP_Minus
begin

lemmas enumerate_acc_nat_eq = HTHN.enumerate_acc_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat enumerate_acc_nat_eq

HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.enumerate_acc_nat by cook

compile_nat HTHN.enumerate_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.enumerate_nat by cook

end

context HOL_To_HOL_Nat
begin

definition "map_pair_acc x = map_acc (Pair x)"
lemmas map_pair_acc_eq = map_acc_eq[of "Pair x" for x, folded map_pair_acc_def]
function_compile_nat map_pair_acc_eq

fun product_acc :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list"  where
  "product_acc [] _ acc = acc"
| "product_acc (x#xs) ys acc =  product_acc xs ys (acc @ map_pair_acc x ys [])"
declare product_acc.simps[simp del]

lemma product_acc_eq_append_product: "product_acc xs ys acc = acc @ List.product xs ys"
  by (induction xs arbitrary: acc)
    (simp_all add: product_acc.simps map_pair_acc_def map_eq_map_acc_nil)

case_of_simps product_acc_eq : product_acc.simps
function_compile_nat product_acc_eq

lemma product_eq_product_acc_nil: "List.product xs ys = product_acc xs ys []"
  by (simp add: product_acc_eq_append_product)

function_compile_nat product_eq_product_acc_nil

end

context HOL_Nat_To_IMP_Minus
begin

lemmas map_pair_acc_nat_eq = HTHN.map_pair_acc_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat map_pair_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_pair_acc_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction "Pair y :: 'b \<Rightarrow> _" _ _ arbitrary: s rule: HOL_To_HOL_Nat.map_acc.induct)
  (tactic \<open>HT.start_run_finish_case_tac HT.get_IMP_def HT.get_imp_minus_correct
    HB.get_HOL_eqs @{context} 1\<close>)+

lemmas product_acc_nat_eq = HTHN.product_acc_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat product_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.product_acc_nat by cook

lemmas product_nat_eq = HTHN.product_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat product_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.product_nat by cook

end

context HOL_To_HOL_Nat
begin

fun concat_acc :: "'a list list \<Rightarrow> 'a list \<Rightarrow> 'a list"  where
  "concat_acc [] acc = acc"
| "concat_acc (x#xs) acc = concat_acc xs (acc @ x)"
declare concat_acc.simps[simp del]

lemma concat_acc_eq_append_concat: "concat_acc xs acc = acc @ concat xs"
  by (induction xs arbitrary: acc) (simp_all add: concat_acc.simps)

case_of_simps concat_acc_eq : concat_acc.simps
function_compile_nat concat_acc_eq

lemma concat_eq_concat_acc_nil: "concat xs = concat_acc xs []"
  by (simp add: concat_acc_eq_append_concat)
function_compile_nat concat_eq_concat_acc_nil

end

context HOL_Nat_To_IMP_Minus
begin

lemmas concat_acc_nat_eq = HTHN.concat_acc_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat concat_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.concat_acc_nat by (cook mode = induction)

lemmas concat_nat_eq = HTHN.concat_nat_eq_unfolded
compile_nat concat_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.concat_nat by cook

end

context HOL_To_HOL_Nat
begin

fun ListMem' :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"  where
  "ListMem' a [] = False"
| "ListMem' a (x#xs) = (if a = x then True else ListMem' a xs)"
declare ListMem'.simps[simp del]

lemma ListMem'_eq_ListMem: "ListMem' x ys = ListMem x ys"
  by (induction ys) (simp_all add: ListMem'.simps ListMem_iff)

case_of_simps ListMem_eq[unfolded ListMem'_eq_ListMem] : ListMem'.simps
function_compile_nat ListMem_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas ListMem_nat_eq = HTHN.ListMem_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat ListMem_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.ListMem_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction ya arbitrary: s)
    (tactic \<open>HT.start_run_finish_case_tac HT.get_IMP_def HT.get_imp_minus_correct
    HB.get_HOL_eqs @{context} 1\<close>)+

end

context HOL_To_HOL_Nat
begin

fun remdups_acc :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"  where
  "remdups_acc [] acc = rev acc"
| "remdups_acc (x#xs) acc = remdups_acc xs (case ListMem x xs of True \<Rightarrow> acc | False \<Rightarrow> (x # acc))"
declare remdups_acc.simps[simp del]

lemma remdups_acc_eq_rev_append_remdups: "remdups_acc xs acc = rev acc @ remdups xs"
  by (induction xs arbitrary: acc) (simp_all add: remdups_acc.simps ListMem_iff)

case_of_simps remdups_acc_eq : remdups_acc.simps
function_compile_nat remdups_acc_eq

lemma remdups_eq_remdups_acc_nil: "remdups xs = remdups_acc xs []"
  by (simp add: remdups_acc_eq_rev_append_remdups)
function_compile_nat remdups_eq_remdups_acc_nil

end

context HOL_Nat_To_IMP_Minus
begin

lemmas remdups_acc_nat_eq = HTHN.remdups_acc_nat_eq_unfolded[simplified case_list_nat_def case_bool_nat_def]
compile_nat remdups_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.remdups_acc_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  apply (induction y ya arbitrary: s rule: HTHN.remdups_acc.induct)
  subgoal by  (tactic \<open>HT.start_run_finish_case_tac HT.get_IMP_def HT.get_imp_minus_correct
    HB.get_HOL_eqs @{context} 1\<close>)
  subgoal for x xs acc s
    apply (cases "ListMem x xs")
    apply (tactic \<open>HT.start_case_tac HT.get_IMP_def @{context} 1\<close>)
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 1\<close>)+
    apply (tactic \<open>HT.run_step_tac HT.get_imp_minus_correct @{context} 2\<close>)+
    apply (tactic \<open>HT.run_HOL_fun_tac HB.get_HOL_eqs @{context} 1\<close>)
    apply (tactic \<open>HT.run_HOL_fun_tac HB.get_HOL_eqs @{context} 2\<close>)
    apply auto
    apply (tactic \<open>HT.finish_tail_tac @{context} 1\<close>)
    apply (tactic \<open>HT.finish_tail_tac @{context} 2\<close>)+
    apply (smt (verit) False_nat_eq_zero HOL_To_HOL_Nat.ListMem_nat_eq_unfolded HOL_To_HOL_Nat.Rel_nat_ListMem_nat_unfolded
        Rel_nat_selector_list(1,2) rewrite_ne_zero_if_Rel_nat)+
    done
done

lemmas remdups_nat_eq = HTHN.remdups_nat_eq_unfolded
compile_nat remdups_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.remdups_nat by cook

end

context HOL_To_HOL_Nat
begin

fun list_all' :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"  where
  "list_all' p [] = True"
| "list_all' p (x#xs) = (case p x of True \<Rightarrow> list_all' p xs | False \<Rightarrow> False)"

lemma list_all'_eq_list_all: "list_all' p xs = list_all p xs"
  by (induction xs) (simp_all split: bool.split)

case_of_simps list_all_eq[unfolded list_all'_eq_list_all] : list_all'.simps

end

end