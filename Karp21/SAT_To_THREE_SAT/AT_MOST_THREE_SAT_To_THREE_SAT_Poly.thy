theory AT_MOST_THREE_SAT_To_THREE_SAT_Poly
  imports
    AT_MOST_THREE_SAT_To_THREE_SAT
    Poly_Library
begin

definition "aux_fold_fn ≡ (λ acc x. (to_at_least_3_clause (remdups x) (snd acc) @ (fst acc), snd acc + 1))"
fun at_most_three_sat_to_three_sat_aux_fold where
  "at_most_three_sat_to_three_sat_aux_fold xs i = fst (List.foldl aux_fold_fn ([], i) xs)"

lemma three_sat_aux_acc:
  "fst (List.foldl aux_fold_fn (acc, i) xs) = fst (List.foldl aux_fold_fn ([], i) xs) @ acc"
apply (induction xs arbitrary: acc i)
unfolding aux_fold_fn_def
by simp (metis (no_types, lifting) append.right_neutral append_assoc foldl_Cons fst_conv snd_conv)

lemma at_most_three_sat_to_three_sat_aux_fold_eq:
  "at_most_three_sat_to_three_sat_aux xs i = at_most_three_sat_to_three_sat_aux_fold xs i"
apply (induction xs i rule: at_most_three_sat_to_three_sat_aux.induct)
apply simp_all
using three_sat_aux_acc[symmetric]
unfolding aux_fold_fn_def
by auto

definition "mop_list_to_set xs ≡ REST [ set xs ↦ length xs ]"

(* remdups in O(n), to_at_least_3_clause is constant *)
definition "mop_aux_fold_fn x acc ≡ REST [ (to_at_least_3_clause (remdups x) (snd acc) @ (fst acc), snd acc + 1) ↦ length x ]"
definition "mop_transl_list_list_list_set l ≡ REST [ transl_list_list_list_set l ↦ length l ]"
definition "mop_at_most_three_sat_to_three_sat_list F ≡ nfoldli (V F) (λ_. True) mop_aux_fold_fn ([], 0)"

definition "at_most_three_sat_to_three_sat_list_poly ≡ λ F. do {
  F' ← mop_list_to_set F;
  b ← mop_for_all_set F' (λ cls. at_most_n_clause_list 3 cls) (λ_. 1);
  if b then do {
    (l, _) ← mop_at_most_three_sat_to_three_sat_list F;
    s ← mop_transl_list_list_list_set l;
    RETURNT s
  } else RETURNT [{}]
}"

(* definition "size_AT_MOST_THREE_SAT xs ≡ 3 * length xs" *)
(* definition "size_AT_MOST_THREE_SAT ≡ sum_list o (map length)" *)
definition "size_AT_MOST_THREE_SAT ≡ sum_list o (map (λ l. if length l = 0 then 1 else length l))"
definition "size_THREE_SAT xs ≡ 3 * length xs "

definition "at_most_three_sat_to_three_sat_space n ≡ 8 * n"
definition "at_most_three_sat_to_three_sat_time n ≡ n + n * n + n"

lemma
  "size_THREE_SAT (at_most_three_sat_to_three_sat F) ≤ at_most_three_sat_to_three_sat_space (size_AT_MOST_THREE_SAT F)"
unfolding size_THREE_SAT_def size_AT_MOST_THREE_SAT_def
  at_most_three_sat_to_three_sat_def transl_list_list_list_set_def
  at_most_three_sat_to_three_sat_list_def
  at_most_three_sat_to_three_sat_space_def
apply (induction F)
apply fastforce
subgoal for a F
proof (cases a)
  case Nil
  then show ?thesis
  sorry
next
  case (Cons a list)
  then show ?thesis sorry
qed
done

end

