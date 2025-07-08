theory AT_MOST_THREE_SAT_To_THREE_SAT_Poly
  imports
    AT_MOST_THREE_SAT_To_THREE_SAT
    Poly_Library
    Polynomial_Reductions
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

(* remdups xs in O(length xs), to_at_least_3_clause is constant *)
definition "mop_at_most_three_sat_to_three_sat_list' F ≡
    REST [ at_most_three_sat_to_three_sat_aux (V F) 0 ↦ sum_list (map (λl. length l + 1) F) * sum_list (map (λl. length l + 1) F) ]"
definition "mop_transl_list_list_list_set l ≡ REST [ transl_list_list_list_set l ↦ sum_list (map length l) ]"

(* definition "mop_aux_fold_fn x acc ≡ REST [ (to_at_least_3_clause (remdups x) (snd acc) @ (fst acc), snd acc + 1) ↦ length x ]"  *)
(* definition "mop_at_most_three_sat_to_three_sat_list F ≡ nfoldli (V F) (λ_. True) mop_aux_fold_fn ([], 0)" *)
(* definition "at_most_three_sat_to_three_sat_poly ≡ λ F. do { *)
(*   F' ← mop_list_to_set F; *)
(*   b ← mop_set_for_all F' (λ cls. at_most_n_clause_list 3 cls) (λ_. 1); *)
(*   if b then do { *)
(*     (l, _) ← mop_at_most_three_sat_to_three_sat_list F; *)
(*     s ← mop_transl_list_list_list_set l; *)
(*     RETURNT s *)
(*   } else RETURNT [{}] *)
(* }" *)

definition "at_most_three_sat_to_three_sat_poly ≡ λ F. do {
  F' ← mop_list_to_set F;
  b ← mop_set_for_all F' (λ cls. at_most_n_clause_list 3 cls) (λ_. 1);
  if b then do {
    l ← mop_at_most_three_sat_to_three_sat_list' F;
    s ← mop_transl_list_list_list_set l;
    RETURNT s
  } else RETURNT [{}]
}"

definition "size_AT_MOST_THREE_SAT xs ≡ sum_list (map length xs) + length xs"
definition "size_THREE_SAT xs ≡ 3 * length xs"

definition "at_most_three_sat_to_three_sat_space n ≡ 24 * n + 3"
definition "at_most_three_sat_to_three_sat_time n ≡ 27 * n + n * n"

lemma len_to_at_least_3_clause: "length (to_at_least_3_clause x i) ≤ 8"
by (induction x i rule: to_at_least_3_clause.induct) auto

lemma len_at_most_three_sat_to_three_sat: "length (at_most_three_sat_to_three_sat_aux F i) ≤ 8 * (length F)"
apply (induction F i rule: at_most_three_sat_to_three_sat_aux.induct)
apply simp_all
by (metis add.commute add_le_mono len_to_at_least_3_clause)

lemma length_aux_inner:
  assumes "∀ x ∈ set (xs). card (set x) ≤ 3"
  shows "∀ x ∈ set (at_most_three_sat_to_three_sat_aux xs i). length x = 3"
  using assms
  proof (induction xs arbitrary: i)
    case (Cons a xs)
    then have "length (remdups a) = card (set a)" using card_set
      by metis
    also have "... ≤ 3" using Cons by force
    finally have "∀ x' ∈ set (to_at_least_3_clause (remdups a) i). length x' = 3"
      using Cons length_to_at_least_3_clause_exact by blast
    then show ?case using Cons by auto
  qed simp

lemma at_most_three_sat_to_three_sat_size:
  "size_THREE_SAT (at_most_three_sat_to_three_sat F) ≤ at_most_three_sat_to_three_sat_space (size_AT_MOST_THREE_SAT F)"
unfolding size_THREE_SAT_def size_AT_MOST_THREE_SAT_def
  at_most_three_sat_to_three_sat_def transl_list_list_list_set_def
  at_most_three_sat_to_three_sat_list_def
  at_most_three_sat_to_three_sat_space_def
  subgoal
  proof (cases "at_most_n_sat_list 3 F")
    case True
    have "length (at_most_three_sat_to_three_sat_aux (V F) 0) ≤ 8 * (length (V F))"
      using len_at_most_three_sat_to_three_sat by blast
    moreover have "length (V F) = length F" by simp
    ultimately show ?thesis by simp
  next
    case False
    then show ?thesis by simp
  qed
done

lemma at_most_three_sat_to_three_sat_refines:
  "at_most_three_sat_to_three_sat_poly F \<le>
   SPEC (\<lambda>y. y = at_most_three_sat_to_three_sat F) (\<lambda>_. at_most_three_sat_to_three_sat_time (size_AT_MOST_THREE_SAT F))"
  unfolding SPEC_def
  unfolding at_most_three_sat_to_three_sat_poly_def at_most_three_sat_to_three_sat_def
            at_most_three_sat_to_three_sat_list_def
            at_most_three_sat_to_three_sat_time_def size_AT_MOST_THREE_SAT_def
            mop_set_for_all_def mop_at_most_three_sat_to_three_sat_list'_def
            mop_transl_list_list_list_set_def mop_list_to_set_def
            transl_list_list_list_set_def
            (* at_most_three_sat_to_three_sat_aux_fold_def *)
  apply(rule T_specifies_I)
  apply(vcg' \<open>-\<close> rules: T_SPEC)
  apply (simp_all add: at_most_n_sat_list_def at_most_n_clause_list_def of_nat_eq_enat)
  subgoal
  proof -
    assume assms: "∀x∈set F. card (set x) ≤ 3"

    let ?len = "length F"
    let ?aux_list = "at_most_three_sat_to_three_sat_aux (V F) 0"
    let ?sum_list = "sum_list (map length ?aux_list)"
    let ?sum = "∑l←F. Suc (length l)"

    have a: "card (set F) ≤ ?len"
      using card_length by blast

    have "∀ x ∈ set (V F). card (set x) ≤ 3"
      using assms by simp (meson List.finite_set card_image_le le_trans)

    then have "∀ x ∈ set ?aux_list. length x = 3"
      using length_aux_inner assms by blast
    then have "map length ?aux_list = map (λ_. 3) ?aux_list" by simp
    then have "?sum_list = sum_list (map (λ_. 3) ?aux_list)" by argo
    also have "... = 3 * length ?aux_list"
      by (simp add: sum_list_triv)
    finally have b: "?sum_list ≤ 24 * ?len" using len_at_most_three_sat_to_three_sat
      by (metis length_map mult.assoc mult_le_mono2)

    have c: "?sum * ?sum = (?len + sum_list (map length F)) * (?len + sum_list (map length F))"
      by (simp add: sum_list_Suc algebra_simps)

    from a b c have "card (set F) + ?sum * ?sum + ?sum_list ≤
      26 * ?len + (?len + sum_list (map length F)) * (?len + sum_list (map length F))"
      by simp

    then show ?thesis
      by (simp add: algebra_simps)
  qed
  apply (rule impI conjI, fast)
  using card_length[of F] by force


theorem at_most_three_sat_to_three_sat_ispolyred:
  "ispolyred at_most_three_sat_to_three_sat_poly at_most_three_sat_list three_sat size_AT_MOST_THREE_SAT size_THREE_SAT"
unfolding ispolyred_def
apply(rule exI[where x=at_most_three_sat_to_three_sat])
apply(rule exI[where x=at_most_three_sat_to_three_sat_time])
apply(rule exI[where x=at_most_three_sat_to_three_sat_space])
apply safe
  subgoal using at_most_three_sat_to_three_sat_refines by blast
  subgoal using at_most_three_sat_to_three_sat_size by blast
  subgoal unfolding poly_def at_most_three_sat_to_three_sat_time_def apply(rule exI[where x=2]) by auto
  subgoal unfolding poly_def at_most_three_sat_to_three_sat_space_def apply(rule exI[where x=1]) by auto
  subgoal using is_reduction_at_most_three_sat_to_three_sat .
done

end

