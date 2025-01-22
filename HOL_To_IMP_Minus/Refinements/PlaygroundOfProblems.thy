theory PlaygroundOfProblems
  imports
    Playground
begin

context HOL_To_HOL_Nat
begin

paragraph \<open>fixed map\<close>

definition "square (n::nat) = n * n"
function_compile_nat square_def

fun tmap_rev_square :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "tmap_rev_square [] ys = ys"
| "tmap_rev_square (x#xs) ys = tmap_rev_square xs (square x # ys)"
declare tmap_rev_square.simps[simp del]
case_of_simps tmap_rev_square_eq : tmap_rev_square.simps
function_compile_nat tmap_rev_square_eq

lemma tmap_rev_square_Nil': "rev (map square xs) @ ys = (tmap_rev_square xs ys)"
  apply (induction xs arbitrary: ys)
  apply (auto simp: tmap_rev_square.simps)
  by (metis append.right_neutral append_Cons
      append_eq_append_conv2 same_append_eq)

lemma tmap_rev_square_Nil: "map square xs = rev (tmap_rev_square xs [])"
  using tmap_rev_square_Nil'[of xs "[]"] rev_swap by auto

definition "tmap_square xs = rev (tmap_rev_square xs [])"
function_compile_nat tmap_square_def

end

context HOL_Nat_To_IMP_Minus
begin

compile_nat HTHN.square_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.square_nat by cook

lemmas tmap_rev_acc_square_nat_eq = HTHN.tmap_rev_square_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat tmap_rev_acc_square_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.tmap_rev_square_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  apply (induction y ya arbitrary: s rule: HTHN.tmap_rev_square.induct)
  (*case []*)
  apply (tactic \<open>HT.start_run_finish_case_tac
    HT.get_IMP_def HT.get_imp_minus_correct HB.get_HOL_eqs @{context} 1\<close>)
  (*case x # xs*)

  (*
  supply Rel_nat_destruct_Cons[Rel_nat]
  apply (tactic \<open>HT.start_run_finish_case_tac
    HT.get_IMP_def HT.get_imp_minus_correct HB.get_HOL_eqs @{context} 1\<close>) *)
  apply (tactic \<open>HT.start_case_tac HT.get_IMP_def @{context} 1\<close>)
  apply (tactic \<open>HT.run_tac HT.get_imp_minus_correct @{context} 1\<close>)

  (*
  apply (tactic \<open>HT.finish_tac HB.get_HOL_eqs @{context} 1\<close>) *)
  apply (tactic \<open>HT.run_HOL_fun_tac HB.get_HOL_eqs @{context} 1\<close>)
  supply Rel_nat_destruct_Cons[Rel_nat]

  (* FIXME does not terminate
  apply (tactic \<open>HT.finish_tail_tac @{context} 1\<close>) *)
  sorry

compile_nat HTHN.tmap_square_nat_eq_unfolded
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.tmap_square_nat
  by cook

end

paragraph \<open>binary tree\<close>
datatype 'a btree = Leaf 'a | Node "'a btree" "'a btree"
datatype_compile_nat btree

context HOL_To_HOL_Nat
begin

fun mirror :: "'a btree \<Rightarrow> 'a btree" where
  "mirror (Leaf a) = Leaf a"
| "mirror (Node l r) = Node (mirror r) (mirror l)"
declare mirror.simps[simp del]
case_of_simps mirror_eq : mirror.simps
function_compile_nat mirror_eq


function tbfold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a btree list \<Rightarrow> 'b \<Rightarrow> 'b" where
  "tbfold f [] b = b"
| "tbfold f (x#xs) b = (case x of Leaf a \<Rightarrow> tbfold f xs (f a b)
    | Node l r \<Rightarrow> tbfold f (l#r#xs) b)"
  by pat_completeness auto

lemma dummerhelper: "fold (\<lambda>a. (+) (size a)) (xs::('a::size) list) i
                      < fold (\<lambda>a. (+) (size a)) xs (Suc i)"
  by (induction xs arbitrary: i) auto
termination
  by (relation "measure (\<lambda>(f, ts, acc). fold (\<lambda>a b. size a + b) ts 0)")
    (simp add: dummerhelper | simp add: field_simps dummerhelper)+

declare tbfold.simps[simp del]
case_of_simps tbfold_eq : tbfold.simps
(* FIXME quite slow *)
function_compile_nat tbfold_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas mirror_nat_eq = HTHN.mirror_nat_eq_unfolded[simplified case_list_nat_def]
(*
compile_nat mirror_nat_eq *)

lemmas tbfold_nat_eq = HTHN.tbfold_nat_eq_unfolded[simplified case_list_nat_def]
(*
compile_nat tbfold_nat_eq *)

end

paragraph \<open>ab tree\<close>
datatype ('a, 'b) abTree = abLeaf 'a | abNode "('a, 'b) abTree" 'b "('a, 'b) abTree"
datatype_compile_nat abTree

context HOL_To_HOL_Nat
begin

fun abfold :: "('a \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('a,'b) abTree \<Rightarrow> 'c \<Rightarrow> 'c" where
  "abfold f g (abLeaf a) c = f a c"
| "abfold f g (abNode l b r) c = abfold f g r (g b (abfold f g l c))"
declare abfold.simps[simp del]
case_of_simps abfold_eq : abfold.simps
(* FIXME does not terminate or too slow for my machine
function_compile_nat abfold_eq *)

end

context HOL_Nat_To_IMP_Minus
begin

(*
lemmas abfold_nat_eq = HTHN.abfold_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat abfold_nat_eq

HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.abfold_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  apply (induction y ya arbitrary: s rule: HTHN.abfold.induct)
  apply (tactic \<open>HT.start_run_finish_case_tac
    HT.get_IMP_def HT.get_imp_minus_correct HB.get_HOL_eqs @{context} 1\<close>)
  apply (tactic \<open>HT.start_run_finish_case_tac
    HT.get_IMP_def HT.get_imp_minus_correct HB.get_HOL_eqs @{context} 1\<close>)
  apply (tactic \<open>HT.start_run_finish_case_tac
    HT.get_IMP_def HT.get_imp_minus_correct HB.get_HOL_eqs @{context} 1\<close>)
  done
*)

end

end