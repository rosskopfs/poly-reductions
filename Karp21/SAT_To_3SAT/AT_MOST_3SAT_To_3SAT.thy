theory AT_MOST_3SAT_To_3SAT
imports "SAT_To_AT_MOST_3SAT" "../Reductions"
begin

section "The Reduction"

fun to_at_least_3_clause where
  "to_at_least_3_clause [] i = [
     [Pos (u (i,0)), Pos (u (i,1)), Pos (u (i,2))],
     [Pos (u (i,0)), Pos (u (i,1)), Neg (u (i,2))],
     [Pos (u (i,0)), Neg (u (i,1)), Pos (u (i,2))],
     [Pos (u (i,0)), Neg (u (i,1)), Neg (u (i,2))],
     [Neg (u (i,0)), Pos (u (i,1)), Pos (u (i,2))],
     [Neg (u (i,0)), Pos (u (i,1)), Neg (u (i,2))],
     [Neg (u (i,0)), Neg (u (i,1)), Pos (u (i,2))],
     [Neg (u (i,0)), Neg (u (i,1)), Neg (u (i,2))]]"
| "to_at_least_3_clause [x] i = [ [x, Pos (u (i,0)), Pos (u (i,1))],
                                  [x, Pos (u (i,0)), Neg (u (i,1))],
                                  [x, Neg (u (i,0)), Pos (u (i,1))],
                                  [x, Neg (u (i,0)), Neg (u (i,1)) ]]"
| "to_at_least_3_clause [x, y] i = [[x,y, Pos (u (i,0))], [x,y, Neg (u (i,0))]]"
| "to_at_least_3_clause xs i = [xs]"


fun at_most_3sat_to_3sat_aux where
  "at_most_3sat_to_3sat_aux (x#xs) i = (to_at_least_3_clause (remdups x) i) 
                                 @ (at_most_3sat_to_3sat_aux xs (i+1))"
| "at_most_3sat_to_3sat_aux [] i = []"


definition at_most_3sat_to_3sat where
  "at_most_3sat_to_3sat F  = (if (\<forall>cls \<in> set F. length cls \<le> 3)
                              then map set (at_most_3sat_to_3sat_aux (V F) 0)
                              else [{}]) "


section "Soundness"

subsection "sub-functions are sound"

lemma to_at_least_3_clause_sound:
  assumes  "\<sigma> \<Turnstile>\<^sub>l [cls]"
  shows "\<sigma> \<Turnstile>\<^sub>l to_at_least_3_clause cls i"
  using assms
  by (induction rule: to_at_least_3_clause.induct)
     (auto simp add: models_def)

lemma remdups_models:
  shows  "\<sigma> \<Turnstile>\<^sub>l [remdups cls] \<longleftrightarrow> \<sigma> \<Turnstile>\<^sub>l [cls]"
  by (auto simp add: models_def)

lemma at_most_3sat_to_3sat_aux_sound:
  assumes  "\<sigma> \<Turnstile>\<^sub>l F"
  shows "\<sigma> \<Turnstile>\<^sub>l at_most_3sat_to_3sat_aux F i"
  using assms remdups_models 
  by (induction F i rule: at_most_3sat_to_3sat_aux.induct)
      (frule models_cons[THEN iffD1],
       auto intro!: to_at_least_3_clause_sound 
            simp add: models_append)

subsection "clause length is 3"

lemma length_to_at_least_3_clause_exact:
  assumes "length cls \<le>  3"
  shows "\<forall>x \<in> set (to_at_least_3_clause cls i). length x = 3"
  using assms 
  by (cases "(cls, i)" rule: to_at_least_3_clause.cases) auto 

lemma to_at_least_3_distinct:
  assumes "\<forall>i j. u (i, j) \<notin> vars_cls cls" "distinct cls"
          "x \<in> set (to_at_least_3_clause cls i)"
  shows "distinct x"
  using assms 
  by (cases "(cls, i)" rule: to_at_least_3_clause.cases)
      (auto simp add: vars_cls_def, auto)
lemma cards_at_most_3sat_to_3sat_aux:
  assumes "\<forall>cls \<in> set F. length cls \<le> 3"  "\<forall>i j. u (i, j) \<notin> vars F"
  shows "\<forall>x \<in> set (map set (at_most_3sat_to_3sat_aux F i)). card x = 3"
  using assms   
  by (induction F i rule: at_most_3sat_to_3sat_aux.induct)
  (auto intro!: remdups_id_iff_distinct[THEN iffD2, THEN arg_cong, THEN trans, of _ length]
          
               simp add: vars_def length_remdups_card_conv[symmetric]
  ,metis distinct_remdups  to_at_least_3_distinct[of "remdups x" for x]  
                list.set_map set_remdups vars_cls_def,
   use le_trans length_to_at_least_3_clause_exact in blast)


lemma at_most_3sat_to_3sat_card:
  assumes "\<forall>cls\<in>set F. length cls \<le> 3"
  shows "\<forall>cls\<in>set (at_most_3sat_to_3sat F). card cls = 3"
proof -
  have *: "\<forall>cls\<in>set (V F). length cls \<le> 3"
    using assms by simp
  moreover have "\<forall>i j. u (i, j) \<notin> vars (V F)"
    by (auto simp add: vars_def vars_cls_def)
  ultimately show ?thesis
    by (metis assms at_most_3sat_to_3sat_def cards_at_most_3sat_to_3sat_aux)
qed

subsection "The reduction is sound"

lemma at_most_3sat_to_3sat_sound:
  assumes "F \<in> AT_MOST_3SAT"
  shows "at_most_3sat_to_3sat F \<in> three_cnf_sat"
  using assms at_most_3sat_to_3sat_card
        models_V sat_def
        at_most_3sat_to_3sat_aux_sound[THEN models_list_models[THEN iffD1]]
  unfolding AT_MOST_3SAT_def at_most_3sat_to_3sat_def   
  by (intro three_cnf_satI) fastforce+


section "Completeness"

lemma to_at_least_3_clause_complete:
  assumes "\<sigma> \<Turnstile>\<^sub>l to_at_least_3_clause cls i"
  shows  "\<sigma> \<Turnstile>\<^sub>l [cls]"
  using assms
  unfolding models_def lift_def
  by (cases "(cls,i)" rule: to_at_least_3_clause.cases) force+


lemma at_most_3sat_to_3sat_aux_complete:
  assumes "\<sigma> \<Turnstile>\<^sub>l at_most_3sat_to_3sat_aux F i"
  shows  "\<sigma> \<Turnstile>\<^sub>l F"
  using assms remdups_models 
  by (induction F i rule: at_most_3sat_to_3sat_aux.induct)
     (rule models_cons[THEN iffD2],
      auto simp add: models_append,
      use to_at_least_3_clause_complete in blast)

lemma at_most_3sat_to_3sat_complete:
  assumes "at_most_3sat_to_3sat F \<in> three_cnf_sat"
  shows "F \<in> AT_MOST_3SAT"
  using assms  at_most_3sat_to_3sat_aux_complete models_V models_list_models
  unfolding AT_MOST_3SAT_def at_most_3sat_to_3sat_def
            three_cnf_sat_def  sat_def 
  by (cases "\<forall>cls\<in>set F. length cls \<le> 3") (auto,fastforce)

section "Conclusion"

theorem  is_reduction_at_most_3sat_to_3sat:
  "is_reduction at_most_3sat_to_3sat AT_MOST_3SAT three_cnf_sat"
  unfolding is_reduction_def 
  using at_most_3sat_to_3sat_sound at_most_3sat_to_3sat_complete
  by auto

  
end