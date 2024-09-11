\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Datatypes
  imports
    HOL_To_IMP_Minus_Arithmetics
begin

locale HOL_To_HOL_Nat =
  notes transport_eq_id.partial_equivalence_rel_equivalenceI[per_intro del]
  and transport_eq_restrict_id.partial_equivalence_rel_equivalence[per_intro del]
begin

fun rev_tail_aux :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"rev_tail_aux [] acc = acc" |
"rev_tail_aux (x # xs) acc = rev_tail_aux xs (x # acc)"

lemma rev_tail_aux_eq_rev_append [simp]: "rev_tail_aux xs acc = rev xs @ acc"
  by (induction xs arbitrary: acc) auto

case_of_simps rev_tail_aux_eq_case : rev_tail_aux.simps
function_compile_nat rev_tail_aux_eq_case
print_theorems
definition "rev_tail xs \<equiv> rev_tail_aux xs []"

lemma rev_tail_eq_rev [simp]: "rev_tail xs = rev xs"
  unfolding rev_tail_def by simp

end

context HOL_To_IMP_Minus
begin

compile_nat Nil_nat_def
HOL_To_IMP_Minus_correct Nil_nat by cook
compile_nat Cons_nat_def
HOL_To_IMP_Minus_correct Cons_nat by cook

(*problem: only got a conditional equation. We have to specify an unconditional one and prove it to
be related to the original HOL function*)
context
  fixes xs ys and xs' ys' :: "('a :: compile_nat) list"
  assumes rels: "Rel_nat xs xs'" "Rel_nat ys ys'"
begin
term HOL_To_HOL_Nat.rev_tail_aux_nat
print_statement HOL_To_HOL_Nat.rev_tail_aux_nat_eq_unfolded
print_statement HOL_To_HOL_Nat.rev_tail_aux_nat_eq_unfolded[OF rels, unfolded case_list_nat_def]
end

(*FIXME: we could use the equation without unfolding case_list_nat_def if we prove congruence lemmas
for case_list_nat (otherwise the function package cannot prove termination)*)
fun rev_tail_aux_nat' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "rev_tail_aux_nat' xs acc = (if fst_nat xs = 0 then acc else
    rev_tail_aux_nat' (snd_nat (snd_nat xs)) (Cons_nat (fst_nat (snd_nat xs)) acc))"
declare rev_tail_aux_nat'.simps[simp del]

compile_nat rev_tail_aux_nat'.simps
HOL_To_IMP_Minus_correct rev_tail_aux_nat' by (cook mode = tailcall)

(*TODO: how to prove the two functions to be related? Currently, we are missing the right lemmas to
make it automatic*)
lemma Rel_nat_NilE:
  assumes "Rel_nat xs []"
  obtains "xs = Nil_nat"
  using assms
  apply (subst (asm) Rel_nat_iff_eq_natify)
  apply (subst (asm) natify_list.simps)
  apply (simp (no_asm_use))
  by assumption

lemma Rel_nat_ConsE:
  assumes "Rel_nat xs (y # ys)"
  obtains z zs where "xs = Cons_nat z zs" "Rel_nat z y" "Rel_nat zs ys"
  using assms
  (* apply (subst (asm) (3) Rel_nat_iff_eq_natify)
  apply (subst (asm) natify_list.simps)
  apply (simp (no_asm_use))
  by assumption *)
  sorry

lemma Rel_nat_NilD:
  assumes "Rel_nat xs []"
  shows "xs = Nil_nat"
  using assms Rel_nat_NilE by blast

lemma Rel_nat_ConsD:
  assumes "Rel_nat xs (y # ys)"
  shows "\<exists>z zs. xs = Cons_nat z zs \<and> Rel_nat z y \<and> Rel_nat zs ys"
  using assms Rel_nat_ConsE by blast

(*probably best approach: use induction on the original function's definition*)
lemma
  fixes xs acc and xs' acc' :: "('a :: compile_nat) list"
  assumes rels: "Rel_nat xs xs'" "Rel_nat acc acc'"
  shows "Rel_nat (rev_tail_aux_nat' xs acc) (HOL_To_HOL_Nat.rev_tail_aux xs' acc')"
  using assms
  apply (induction xs' acc' arbitrary: xs acc rule: HOL_To_HOL_Nat.rev_tail_aux.induct)

  apply (subst HOL_To_HOL_Nat.rev_tail_aux.simps)
  apply (frule Rel_nat_NilD Rel_nat_ConsD; (elim exE)?)
  apply hypsubst
  apply (subst rev_tail_aux_nat'.simps)
  apply (simp (no_asm) add: Nil_nat_def Cons_nat_def,
   (simp (no_asm) only: flip: Nil_nat_def Cons_nat_def)?)

  apply (subst HOL_To_HOL_Nat.rev_tail_aux.simps)
  apply (frule Rel_nat_NilD Rel_nat_ConsD; (elim conjE exE)?)
  apply hypsubst
  apply (subst rev_tail_aux_nat'.simps)
  apply (simp (no_asm) add: Nil_nat_def Cons_nat_def,
   (simp (no_asm) only: flip: Nil_nat_def Cons_nat_def)?)
  subgoal premises p
    apply (rule p(1))
    apply (insert p(2-))
    apply (metis Rel_nat_Cons_nat rel_funD)
    apply (metis Rel_nat_Cons_nat rel_funD)
    done
  done

end

end
