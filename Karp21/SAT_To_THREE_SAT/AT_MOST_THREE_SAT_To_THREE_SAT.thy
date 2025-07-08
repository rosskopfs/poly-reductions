theory AT_MOST_THREE_SAT_To_THREE_SAT
  imports
    SAT_To_AT_MOST_THREE_SAT
begin

section "The Reduction"

fun to_at_least_3_clause where
  "to_at_least_3_clause [] i = [
     [Pos (RU (i, 0)), Pos (RU (i, 1)), Pos (RU (i, 2))],
     [Pos (RU (i, 0)), Pos (RU (i, 1)), Neg (RU (i, 2))],
     [Pos (RU (i, 0)), Neg (RU (i, 1)), Pos (RU (i, 2))],
     [Pos (RU (i, 0)), Neg (RU (i, 1)), Neg (RU (i, 2))],
     [Neg (RU (i, 0)), Pos (RU (i, 1)), Pos (RU (i, 2))],
     [Neg (RU (i, 0)), Pos (RU (i, 1)), Neg (RU (i, 2))],
     [Neg (RU (i, 0)), Neg (RU (i, 1)), Pos (RU (i, 2))],
     [Neg (RU (i, 0)), Neg (RU (i, 1)), Neg (RU (i, 2))]]"
| "to_at_least_3_clause [x] i = [ [x, Pos (RU (i, 0)), Pos (RU (i, 1))],
                                  [x, Pos (RU (i, 0)), Neg (RU (i, 1))],
                                  [x, Neg (RU (i, 0)), Pos (RU (i, 1))],
                                  [x, Neg (RU (i, 0)), Neg (RU (i, 1)) ]]"
| "to_at_least_3_clause [x, y] i = [[x,y, Pos (RU (i, 0))], [x,y, Neg (RU (i, 0))]]"
| "to_at_least_3_clause xs i = [xs]"


fun at_most_three_sat_to_three_sat_aux where
  "at_most_three_sat_to_three_sat_aux (x#xs) i =
    at_most_three_sat_to_three_sat_aux xs (i + 1) @ to_at_least_3_clause (remdups x) i"
| "at_most_three_sat_to_three_sat_aux [] i = []"

definition "at_most_three_sat_to_three_sat_list F \<equiv> if at_most_n_sat_list 3 F
  then (at_most_three_sat_to_three_sat_aux (V F) 0)
  else [[]]"

definition "at_most_three_sat_to_three_sat F \<equiv>
  transl_list_list_list_set (at_most_three_sat_to_three_sat_list F)"

section "Soundness"

subsection "sub-functions are sound"

lemma to_at_least_3_clause_sound:
  assumes  "models_list \<sigma> [cls]"
  shows "models_list \<sigma> (to_at_least_3_clause cls i)"
  using assms
  by (induction rule: to_at_least_3_clause.induct)
  (auto simp add: models_list_iff_ball_models_clause models_clause_list_def)

lemma remdups_models: "models_list \<sigma> [remdups cls] \<longleftrightarrow> models_list \<sigma> [cls]"
  by (auto simp add: models_list_iff_ball_models_clause models_clause_list_def)

lemma at_most_three_sat_to_three_sat_aux_sound:
  assumes "models_list \<sigma> F"
  shows "models_list \<sigma> (at_most_three_sat_to_three_sat_aux F i)"
  using assms remdups_models
  by (induction F i rule: at_most_three_sat_to_three_sat_aux.induct)
  (frule models_cons[THEN iffD1], auto intro!: to_at_least_3_clause_sound simp: models_append)

subsection "clause length is 3"

lemma length_to_at_least_3_clause_exact:
  assumes "length cls \<le>  3"
  shows "\<forall>x \<in> set (to_at_least_3_clause cls i). length x = 3"
  using assms
  by (cases "(cls, i)" rule: to_at_least_3_clause.cases) auto

lemma to_at_least_3_distinct:
  assumes "\<forall>i j. RU (i, j) \<notin> vars_cls cls" "distinct cls"
  and "x \<in> set (to_at_least_3_clause cls i)"
  shows "distinct x"
  using assms
  by (cases "(cls, i)" rule: to_at_least_3_clause.cases)
      (auto simp add: vars_cls_def, auto)

lemma cards_at_most_three_sat_to_three_sat_aux:
  assumes "at_most_n_sat_list 3 F"  "\<forall>i j. RU (i, j) \<notin> vars F"
  shows "\<forall>x \<in> set (map set (at_most_three_sat_to_three_sat_aux F i)). card x = 3"
  using assms unfolding at_most_n_sat_list_def at_most_n_clause_list_def
  by (induction F i rule: at_most_three_sat_to_three_sat_aux.induct)
  (auto intro!: remdups_id_iff_distinct[THEN iffD2, THEN arg_cong, THEN trans, of _ length]
               simp add: vars_def length_remdups_card_conv[symmetric]
  ,metis distinct_remdups  to_at_least_3_distinct[of "remdups x" for x]
                list.set_map set_remdups vars_cls_def,
   use le_trans length_to_at_least_3_clause_exact in blast)

lemma at_most_three_sat_to_three_sat_card:
  assumes "at_most_n_sat_list 3 F"
  shows "is_n_sat 3 (at_most_three_sat_to_three_sat F)"
proof -
  have *: "at_most_n_sat_list 3 (V F)"
    using assms unfolding at_most_n_sat_list_def at_most_n_clause_list_def
    by auto (metis List.finite_set card_image_le order_trans)
  moreover have "\<forall>i j. RU (i, j) \<notin> vars (V F)" by (auto simp add: vars_def vars_cls_def)
  ultimately show ?thesis by (intro is_n_satI)
    (auto simp: assms at_most_three_sat_to_three_sat_list_def at_most_three_sat_to_three_sat_def
      cards_at_most_three_sat_to_three_sat_aux transl_list_list_list_set_def)
qed

subsection "The reduction is sound"

lemma at_most_three_sat_to_three_sat_sound:
  assumes "F \<in> at_most_three_sat_list"
  shows "at_most_three_sat_to_three_sat F \<in> three_sat"
  using assms at_most_three_sat_to_three_sat_card models_V
    at_most_three_sat_to_three_sat_aux_sound[THEN models_list_models[THEN iffD1]]
  unfolding at_most_three_sat_to_three_sat_def
    at_most_three_sat_list_def at_most_three_sat_list_pred_def
    sat_list_pred_def three_sat_def
    at_most_three_sat_to_three_sat_list_def transl_list_list_list_set_def
  by (smt (verit, best) three_sat_predI mem_Collect_eq sat_predI)

section "Completeness"

lemma to_at_least_3_clause_complete:
  assumes "models_list \<sigma> (to_at_least_3_clause cls i)"
  shows  "models_list \<sigma> [cls]"
  using assms unfolding models_list_iff_ball_models_clause  models_clause_list_def
  by (cases "(cls,i)" rule: to_at_least_3_clause.cases) force+

lemma at_most_three_sat_to_three_sat_aux_complete:
  assumes "models_list \<sigma> (at_most_three_sat_to_three_sat_aux F i)"
  shows  "models_list \<sigma> F"
  using assms remdups_models
by (induction F i rule: at_most_three_sat_to_three_sat_aux.induct)
(rule models_cons[THEN iffD2], auto simp: models_append,
      use to_at_least_3_clause_complete in blast)

lemma at_most_three_sat_to_three_sat_complete:
  assumes "at_most_three_sat_to_three_sat F \<in> three_sat"
  shows "F \<in> at_most_three_sat_list"
  using assms  at_most_three_sat_to_three_sat_aux_complete models_V models_list_models
  unfolding models_list_iff_ball_models_clause models_clause_list_def
    at_most_three_sat_to_three_sat_def three_sat_def sat_def
    at_most_three_sat_to_three_sat_list_def transl_list_list_list_set_def
  apply (cases "at_most_n_sat_list 3 F")
  apply (smt (z3) at_most_three_sat_list_def at_most_three_sat_list_predI
    at_most_three_sat_to_three_sat_aux_complete
    mem_Collect_eq models_V models_list_models sat_list_predI sat_pred_def three_sat_def
    three_sat_pred_def)
  by fastforce

section "Conclusion"

theorem is_reduction_at_most_three_sat_to_three_sat:
  "is_reduction at_most_three_sat_to_three_sat at_most_three_sat_list three_sat"
  using at_most_three_sat_to_three_sat_sound at_most_three_sat_to_three_sat_complete
  by (intro is_reductionI) auto

end
