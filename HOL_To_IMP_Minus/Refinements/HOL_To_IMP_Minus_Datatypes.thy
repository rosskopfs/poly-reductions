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

compile_nat Pair_nat_def
HOL_To_IMP_Minus_correct Pair_nat by cook

lemmas fst_nat_eq_unfolded = HTHN.fst_nat_eq_unfolded[simplified case_prod_nat_def]
unconditional_nat fst_nat_eq_unfolded
declare fst_nat_unconditional.simps[simp del]
compile_nat fst_nat_unconditional.simps
HOL_To_IMP_Minus_correct fst_nat_unconditional by cook

(* Problem: We have obtained an unconditional equation. However, we
still have to prove it to be related to the original HOL function.
TODO: how to prove the two functions to be related? Currently, we are
missing the right lemmas to make it automatic. *)
context
  fixes xs and xs' :: "'a :: compile_nat * 'b :: compile_nat"
  assumes rels: "Rel_nat xs xs'"
begin
  print_statement HTHN.fst_nat_eq_unfolded
  print_statement HTHN.fst_nat_eq_unfolded[OF rels, unfolded case_list_nat_def]
end

lemmas snd_nat_eq_unfolded = HTHN.snd_nat_eq_unfolded[simplified case_prod_nat_def]
unconditional_nat snd_nat_eq_unfolded
declare snd_nat_unconditional.simps[simp del]
compile_nat snd_nat_unconditional.simps
HOL_To_IMP_Minus_correct snd_nat_unconditional by cook

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

end

context HOL_Nat_To_IMP_Minus
begin

compile_nat Cons_nat_def
HOL_To_IMP_Minus_correct Cons_nat by cook

compile_nat Nil_nat_def
HOL_To_IMP_Minus_correct Nil_nat by cook

(* FIXME: we could use the equation without unfolding case_list_nat_def if we prove
congruence lemmas for case_list_nat (otherwise the function package cannot prove termination) *)
lemmas rev_acc_nat_eq = HTHN.rev_acc_nat_eq_unfolded[simplified case_list_nat_def]
unconditional_nat rev_acc_nat_eq
declare rev_acc_nat_unconditional.simps[simp del]
compile_nat rev_acc_nat_unconditional.simps
HOL_To_IMP_Minus_correct rev_acc_nat_unconditional by (cook mode = tailcall)

(*Manual attempt to prove the relatedness to HOL function*)
lemma natify_list_simps_Nil: "natify [] = Nil_nat"
  by (subst natify_list.simps) simp

lemma natify_list_simps_Cons: "natify (x # xs) = Cons_nat (natify x) (natify xs)"
  by (subst natify_list.simps) simp

(* we would need these elimination/destruction lemmas to automate the proofs *)
lemma Rel_nat_NilE:
  assumes rel: "Rel_nat xs []"
  obtains "xs = Nil_nat"
  (* this proof is not "optimal", but can hopefully be mechanically derived for each constructor *)
  apply standard
  apply (subst rel[simplified Rel_nat_iff_eq_natify])
    apply (subst natify_list_simps_Nil)
    apply (rule refl)
   apply ((rule Rel_nat_natify_self)+)?
  done

lemma Rel_nat_ConsE:
  assumes rel: "Rel_nat xs (y # ys)"
  obtains z zs where "xs = Cons_nat z zs" "Rel_nat z y" "Rel_nat zs ys"
  apply standard
  apply (subst rel[simplified Rel_nat_iff_eq_natify])
    apply (subst natify_list_simps_Cons)
    apply (rule refl)
   apply ((rule Rel_nat_natify_self)+)?
  done

lemma Rel_nat_NilD:
  assumes "Rel_nat xs []"
  shows "xs = Nil_nat"
  using assms Rel_nat_NilE by blast

lemma Rel_nat_ConsD:
  assumes "Rel_nat xs (y # ys)"
  shows "\<exists>z zs. xs = Cons_nat z zs \<and> Rel_nat z y \<and> Rel_nat zs ys"
  using assms Rel_nat_ConsE by blast

(* probably(?) best approach: use induction on the original function's definition *)
lemma related_rev_acc_nat_unconditional:
  fixes xs acc and xs' acc' :: "('a :: compile_nat) list"
  assumes rels: "Rel_nat xs xs'" "Rel_nat acc acc'"
  shows "Rel_nat (rev_acc_nat_unconditional xs acc) (HTHN.rev_acc xs' acc')"
  using assms
  apply (induction xs' acc' arbitrary: xs acc rule: HTHN.rev_acc.induct)

  apply (subst HTHN.rev_acc.simps)
  apply (frule Rel_nat_NilD Rel_nat_ConsD; (elim exE)?)
  apply hypsubst
  apply (subst rev_acc_nat_unconditional.simps)
  apply (simp (no_asm) add: Nil_nat_def Cons_nat_def,
   (simp (no_asm) only: flip: Nil_nat_def Cons_nat_def)?)

  apply (subst HTHN.rev_acc.simps)
  apply (frule Rel_nat_NilD Rel_nat_ConsD; (elim conjE exE)?)
  apply hypsubst
  apply (subst rev_acc_nat_unconditional.simps)
  apply (simp (no_asm) add: Nil_nat_def Cons_nat_def,
   (simp (no_asm) only: flip: Nil_nat_def Cons_nat_def)?)
  subgoal premises p
    apply (urule p(1))
    apply (insert p(2-))
    apply (metis Rel_nat_Cons_nat rel_funD)
    apply (metis Rel_nat_Cons_nat rel_funD)
    done
  done

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
