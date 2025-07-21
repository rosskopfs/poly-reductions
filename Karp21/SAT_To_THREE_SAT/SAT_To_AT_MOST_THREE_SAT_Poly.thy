
theory SAT_To_AT_MOST_THREE_SAT_Poly
  imports
    SAT_To_AT_MOST_THREE_SAT
    Poly_Library
    Polynomial_Reductions
begin

definition "mop_sat_to_at_most_three_sat_aux xs i ≡
  REST [ sat_to_at_most_three_sat_aux xs i ↦ sum_list (map (λxs. length xs^3) xs) ]"

definition "sat_to_at_most_three_sat_poly ≡ λ F. do {
  res ← mop_sat_to_at_most_three_sat_aux (V F) 0;
  RETURNT res
}"

definition "size_SAT xs ≡ sum_list (map length xs) + length xs"
definition "size_AT_MOST_THREE_SAT xs ≡ sum_list (map length xs) + length xs"

definition "sat_to_at_most_three_sat_size n ≡ n^3"
definition "sat_to_at_most_three_sat_time n ≡ n^3"

lemma length_bound_to_at_most_3_clause: "length (to_at_most_3_clause xs i j) ≤ (1 + length xs^2)"
proof (induction xs i j rule: to_at_most_3_clause.induct)
  case (1 a b c d rest i j)
  let ?rec = "length (to_at_most_3_clause (Neg (RU (i, j))#c#d#rest) i (j + 1))"
  from 1 have IH: "?rec ≤ 1 + (3 + length rest)^2" by (simp add: numeral_Bit1)
  have "length (to_at_most_3_clause (a # b # c # d # rest) i j) = 3 + ?rec + length rest" by simp
  also have "... ≤ 4 + (3 + length rest)^2 + length rest" using IH by simp
  also have "... = 13 + 7 * length rest + length rest^2" by algebra
  also have "... ≤ 17 + 8 * length rest + length rest^2" by linarith
  also have "... = 1 + (4 + length rest)^2" by algebra
  finally show ?case
    by (metis ab_semigroup_add_class.add_ac(1) length_Cons nat_1_add_1 numeral_Bit0 plus_1_eq_Suc)
qed simp_all

lemma sat_to_at_most_three_sat_size:
  "size_AT_MOST_THREE_SAT (sat_to_at_most_three_sat xs) ≤ sat_to_at_most_three_sat_size (size_SAT xs)"
unfolding sat_to_at_most_three_sat_size_def size_SAT_def size_AT_MOST_THREE_SAT_def sat_to_at_most_three_sat_def
sorry

lemma sum_pow3_leq: "(x :: nat)^3 + y^3 ≤ (x + y)^3"
proof -
  have "(x + y)^3 = (x^3 + 3 * x^2 * y + 3 * x * y^2 + y^3)"
    by algebra
  then show ?thesis by simp
qed

lemma sum_list_pow_3: "sum_list (map (λxs. (f::'a ⇒ nat) xs^3) xs) ≤ (sum_list (map f xs))^3"
proof (induction xs)
  case (Cons a xs)
  then have "(∑xs←a # xs. f xs ^ 3) = f a ^ 3 + (∑xs←xs. f xs ^ 3)" by force
  also have "... ≤ f a ^ 3 + (sum_list (map f xs))^3" using Cons by force
  also have "... ≤ (f a + sum_list (map f xs))^3" using sum_pow3_leq by fast
  finally show ?case by auto
qed simp

lemma sat_to_at_most_three_sat_refines:
  "sat_to_at_most_three_sat_poly F \<le>
   SPEC (\<lambda>y. y = sat_to_at_most_three_sat F) (\<lambda>_. sat_to_at_most_three_sat_time (size_SAT F))"
  unfolding SPEC_def sat_to_at_most_three_sat_poly_def mop_sat_to_at_most_three_sat_aux_def
            size_SAT_def sat_to_at_most_three_sat_time_def sat_to_at_most_three_sat_def
  apply(rule T_specifies_I)
  apply(vcg' \<open>-\<close> rules: T_SPEC)
  apply simp
  subgoal proof -
    have "sum_list (map (((λxs. length xs ^ 3) ∘∘ map) (map_lit RV)) F) = sum_list (map (λxs. length xs ^ 3) F)"
      by (simp add: comp_def)
    then show ?thesis using sum_list_pow_3[of length F]
      by (metis (mono_tags, lifting) le_add1 le_trans sum_pow3_leq)
  qed
  done


end
