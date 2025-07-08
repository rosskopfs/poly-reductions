theory SAT_To_AT_MOST_THREE_SAT
  imports
    SAT_List_Definition
    Reductions
begin

section "Helper Functions"

fun var where
  "var (Pos a) = a"
| "var (Neg a) = a"

definition "vars_cls cls \<equiv> set (map var cls)"

definition "vars F = \<Union>(set (map vars_cls F))"

lemma var_map_lit [simp]: "var (map_lit f x) = f (var x)" for x
  by (cases x) (auto)

lemma vars_cons: "vars (x # xs) =  (vars_cls x) \<union> (vars xs)"
  by (simp add: vars_def)

lemma var_flip [simp]: "var (flip_lit d) = var d"
  by (cases d) auto

lemma vars_append: "vars (a@b) = vars a \<union> vars b"
  by (simp add: vars_def)

lemma models_list_models: "models_list \<sigma> F = \<sigma> \<Turnstile> (map set F)"
  unfolding models_list_def models_def by auto

lemma models_cong:
  assumes "\<forall>x \<in> vars F. \<sigma>1 x = \<sigma>2 x"
  and "models_list \<sigma>2 F"
  shows "models_list \<sigma>1 F"
proof (unfold models_list_iff_ball_models_clause, intro ballI)
  fix cls assume "cls \<in> set F"
  then obtain l where "(\<sigma>2\<up>) l" "l \<in> set cls"
    using \<open>models_list \<sigma>2 F\<close> unfolding models_list_iff_ball_models_clause by auto
  moreover then have "var l \<in> vars F"
    using \<open>cls \<in> set F\<close>  vars_def vars_cls_def by fastforce
  ultimately have "(\<sigma>1\<up>) l" using assms(1) by (cases l) auto
  then show "models_clause_list \<sigma>1 cls" using \<open>l \<in> set cls\<close> by blast
qed

lemma models_cons:
  "models_list \<sigma> (x # xs) \<longleftrightarrow> models_list \<sigma> [x] \<and> models_list \<sigma> xs"
  unfolding models_list_iff_ball_models_clause by auto

lemma models_append:
  shows "models_list \<sigma> (a @ b) \<longleftrightarrow> models_list \<sigma> a \<and> models_list \<sigma> b"
  unfolding models_list_iff_ball_models_clause by auto

section "The Reduction"

datatype 'a red = RV 'a | RU "nat \<times> nat"

fun to_at_most_3_clause where
  "to_at_most_3_clause (a # b # c # d # rest) i j =
    to_at_most_3_clause (Neg (RU (i, j)) # c # d # rest) i (j+1) @
    [a, b, Pos (RU (i, j))] # map (\<lambda>l. [Pos (RU (i, j)), flip_lit l]) (c # d # rest)"
| "to_at_most_3_clause xs i j = [xs]"

fun sat_to_at_most_three_sat_aux where
  "sat_to_at_most_three_sat_aux (x # xs) i =
    (sat_to_at_most_three_sat_aux xs (i+1)) @ (to_at_most_3_clause x i 0)"
| "sat_to_at_most_three_sat_aux [] i = []"

abbreviation V  where
  "V F \<equiv> map (map (map_lit RV)) F"

definition sat_to_at_most_three_sat where
  "sat_to_at_most_three_sat F  = sat_to_at_most_three_sat_aux (V F) 0"

lemma vars_to_at_most_3_clause:
  "vars (to_at_most_3_clause cls i j) \<subseteq> (vars_cls cls \<union> {RU (i,k) |k. True})"
  by (induction j rule: to_at_most_3_clause.induct)
     (auto simp add: vars_cls_def vars_def)

lemma vars_sat_to_at_most_three_sat_aux:
  "vars (sat_to_at_most_three_sat_aux F i) \<subseteq> (vars F \<union> {RU (k,j) |k j. k \<ge> i})"
  by (induction rule: sat_to_at_most_three_sat_aux.induct)
  (auto intro!: vars_to_at_most_3_clause[THEN subset_trans] simp: vars_cons vars_append)

lemma models_V: "sat_list_pred (V F) \<longleftrightarrow> sat_list_pred F"
proof (intro iffI)
  assume "sat_list_pred (V F)"
  then obtain \<sigma> where "models_list \<sigma> (V F)" by blast
  let ?\<sigma> = "\<lambda>x. \<sigma> (RV x)"
  have "(?\<sigma>\<up>) x = (\<sigma>\<up>) (map_lit RV x)" for x by (cases x) auto
  then have "models_list ?\<sigma> F" using \<open>models_list \<sigma> (V F)\<close>
    unfolding models_list_iff_ball_models_clause by force
  then show "sat_list_pred F" by blast
next
  assume "sat_list_pred F"
  then obtain \<sigma> where "models_list \<sigma> F" by blast
  let ?\<sigma> = "case_red \<sigma> (\<lambda>x. True)"
  have "(?\<sigma>\<up>) (map_lit RV x) = (\<sigma>\<up>) x" for x by (cases x) auto
  then have "models_list ?\<sigma> (V F)" using \<open>models_list \<sigma> F\<close>
    unfolding models_list_iff_ball_models_clause  models_clause_list_def by auto
  then show "sat_list_pred (V F)" by blast
qed

section "Soundness"

lemma to_at_most_3_clause_sound:
  assumes "models_list \<sigma> [cls]"
  and "vars_cls cls \<inter> {RU (i, k)|k. k \<ge> j} = {}"
  shows "\<exists>\<sigma>'. (\<forall>x \<in> -{RU (i, k) |k. k \<ge> j}. \<sigma>' x = \<sigma> x)
    \<and> models_list \<sigma>' (to_at_most_3_clause cls i j)"
using assms
proof (induction arbitrary: \<sigma> rule: to_at_most_3_clause.induct )
  case (1 a b c d rest i j)
  let ?tail = "c # d # rest"
  define \<sigma>1 where "\<sigma>1 = \<sigma>(RU (i, j) := models_list \<sigma> [?tail])"
  have "models_list \<sigma>1 [?tail]" if "models_list \<sigma> [?tail]"
    using that 1 models_list_iff_ball_models_clause
    by (intro models_cong[of _ \<sigma>1 \<sigma>])
    (auto simp add: \<sigma>1_def vars_def vars_cls_def)
  then have "models_list \<sigma>1 [Neg (RU (i, j)) # ?tail]"
    by (cases "models_list \<sigma> [?tail]")
    (auto simp add: models_list_iff_ball_models_clause models_clause_list_def \<sigma>1_def)
  moreover have "vars_cls (Neg (RU (i, j)) # ?tail) \<inter> {RU (i, k) |k. j + 1 \<le> k} = {}"
    using 1(3) by (auto simp add: vars_cls_def)
  ultimately obtain \<sigma>' where \<sigma>'_def: "(\<forall>x\<in>- {RU (i, k) |k. j + 1 \<le> k}. \<sigma>' x = \<sigma>1 x) \<and>
      models_list \<sigma>' (to_at_most_3_clause (Neg (RU (i, j)) # ?tail) i (j + 1))"
    using 1 by fastforce
  moreover then have "\<sigma>' x = \<sigma> x" if "x \<in>- {RU (i, k) |k. j \<le> k}" for x
    using that by (cases "x = RU (i, j)", auto simp add: \<sigma>1_def) force
  moreover have "models_list \<sigma>' [[Pos (RU (i, j)), flip_lit l]]" if "l \<in> set (?tail)" for l
  proof (intro models_cong[of _ \<sigma>' \<sigma>1])
    show "models_list \<sigma>1 [[Pos (RU (i, j)), flip_lit l]]"
    proof (cases "models_list \<sigma> [?tail]")
      case False
      then have "\<not> (\<sigma>\<up>) l"
        using that by (auto simp add: models_list_iff_ball_models_clause)
      moreover have "var l \<noteq> RU (i, j)"
        using 1(3) that
        by (auto simp add: vars_cls_def)
      ultimately show ?thesis
        by (cases l) (auto simp add: models_list_iff_ball_models_clause \<sigma>1_def)
    qed(auto simp add: \<sigma>1_def models_list_iff_ball_models_clause)
    have "vars [[Pos (RU (i, j)), flip_lit l]] \<subseteq> -{RU (i, k) |k. j + 1 \<le> k}"
      using that 1(3)
      by(auto simp add: vars_def vars_cls_def)
    then show "\<forall>x\<in>vars [[Pos (RU (i, j)), flip_lit l]]. \<sigma>' x = \<sigma>1 x"
      using \<sigma>'_def  by blast
  qed
  moreover have "models_list \<sigma>' [[a, b, Pos (RU (i, j))]]"
  proof (intro models_cong[of _ \<sigma>' \<sigma>1])
    have "models_list \<sigma>1 [[a,b]]" if "\<not>(models_list \<sigma> [?tail])"
      using 1(3) that 1(2)
      by (intro models_cong[of _ \<sigma>1 \<sigma>])
      (auto simp add: models_list_iff_ball_models_clause models_clause_list_def
        \<sigma>1_def vars_def vars_cls_def)
    then show "models_list \<sigma>1 [[a, b, Pos (RU (i, j))]]"
      by (cases "models_list \<sigma> [?tail]")
      (auto simp add: models_list_iff_ball_models_clause models_clause_list_def \<sigma>1_def)
    have "vars [[a, b, Pos (RU (i, j))]]  \<subseteq> -{RU (i, k) |k. j + 1 \<le> k}"
      using 1(3)
      by(auto simp add: vars_def vars_cls_def)
    then show "\<forall>x\<in>vars[[a, b, Pos (RU (i, j))]]. \<sigma>' x = \<sigma>1 x"
      using \<sigma>'_def  by blast
  qed
  ultimately show ?case
    using \<sigma>'_def unfolding models_list_iff_ball_models_clause by (intro exI[of _ \<sigma>']) auto
qed auto

lemma sat_to_at_most_three_sat_aux_sound:
  assumes "models_list \<sigma> F"
  and "vars F \<inter> RU ` UNIV = {}"
  shows "\<exists>\<sigma>'. models_list \<sigma>' (sat_to_at_most_three_sat_aux F i) \<and>
    (\<forall>x \<in> -{RU (k, j) |k j. k \<ge> i}. \<sigma>' x = \<sigma> x)"
using assms
proof (induct F i  rule: sat_to_at_most_three_sat_aux.induct )
  case (1 x xs i)
  then obtain \<sigma>ih where \<sigma>ih_models: "models_list \<sigma>ih (sat_to_at_most_three_sat_aux xs (i + 1))"
    and \<sigma>ih_\<sigma>:  "(\<forall>x \<in> -{RU (k, j) |k j. k \<ge> (i+1)}. \<sigma>ih x = \<sigma> x)"
    unfolding models_list_iff_ball_models_clause by (auto simp add: vars_cons)
  moreover have "vars_cls x \<subseteq>  -{RU (k, j) |k j. k \<ge> (i+1)}"
    using 1(3) vars_cons unfolding vars_cls_def
    by fastforce
  ultimately have "models_list \<sigma>ih [x]"
    using 1 by(intro models_cong[of _ \<sigma>ih \<sigma>])
    (auto simp: vars_cons vars_def models_list_iff_ball_models_clause vars_cls_def)
  moreover have "vars_cls x \<inter> {RU (i, k) |k. 0 \<le> k} = {}"
    using 1 by (auto simp add: vars_def)
  ultimately obtain \<sigma>' where  \<sigma>'_def: "(\<forall>x \<in> -{RU (i, k) |k. 0 \<le> k}. \<sigma>' x = \<sigma>ih x) \<and>
    models_list \<sigma>' (to_at_most_3_clause x i 0)"
    using to_at_most_3_clause_sound[of \<sigma>ih] by iprover
  moreover have "vars (sat_to_at_most_three_sat_aux xs (i + 1)) \<subseteq>  -{RU (i, k) |k. True}"
    using 1 by (intro vars_sat_to_at_most_three_sat_aux[THEN subset_trans])
    (auto simp add: vars_cons)
  ultimately have "models_list \<sigma>' (sat_to_at_most_three_sat_aux xs (i + 1))" using \<sigma>ih_models
    by (intro models_cong[of _ \<sigma>' \<sigma>ih]) auto
  moreover have "\<forall>x \<in> -{RU (k, j) |k j. k \<ge> i}. \<sigma>' x = \<sigma> x"
    using \<sigma>ih_\<sigma> \<sigma>'_def by force
  ultimately show ?case
    using \<sigma>'_def unfolding models_list_iff_ball_models_clause
    by (intro exI[of _ \<sigma>']) auto
qed auto

lemma sat_to_3_sat_sound:
  assumes "F \<in> sat_list"
  shows "sat_to_at_most_three_sat F \<in> at_most_three_sat_list"
proof -
  obtain \<sigma> where "models_list \<sigma> (V F)" using assms models_V by fastforce
  moreover have "vars (V F) \<inter> RU ` UNIV = {}" by (auto simp add: vars_def vars_cls_def)
  ultimately have "sat_list_pred (sat_to_at_most_three_sat F)"
    unfolding sat_to_at_most_three_sat_def using sat_to_at_most_three_sat_aux_sound by blast
  moreover {
    have "length cls \<le> 3" if "cls \<in>  set (to_at_most_3_clause x i j)" for cls x i j
      using that
      by (induction x i j rule: to_at_most_3_clause.induct) auto
    then have "length cls \<le> 3" if "cls \<in> set (sat_to_at_most_three_sat_aux G i)" for cls G i
      using that
      by (induction G i rule: sat_to_at_most_three_sat_aux.induct) auto
    then have "at_most_n_clause_list 3 cls" if "cls \<in> set (sat_to_at_most_three_sat F)" for cls
      by (metis at_most_n_clause_list_iff_le_list_card card_length list_card_def order_trans
      sat_to_at_most_three_sat_def that)
  }
  ultimately show ?thesis
    unfolding at_most_three_sat_list_def by auto
qed

section "Completness"

lemma to_at_most_3_clause_complete:
  assumes "models_list \<sigma> (to_at_most_3_clause cls i j)"
  shows "models_list \<sigma> [cls]"
  using assms
proof(induction cls i j rule:to_at_most_3_clause.induct)
  case (1 a b c d rest i j)
  then show ?case
    by (cases "\<sigma> (u (i, j))")
    (auto simp add: models_list_iff_ball_models_clause models_clause_list_def)
qed auto

lemma sat_to_at_most_three_sat_aux_complete:
  assumes "models_list \<sigma> (sat_to_at_most_three_sat_aux F i)"
  shows "models_list \<sigma> F"
  using assms to_at_most_3_clause_complete
  by (induction F i rule:sat_to_at_most_three_sat_aux.induct)
     (rule models_cons[THEN iffD2], auto simp add: models_append)

lemma sat_to_3_sat_complete:
  assumes "sat_to_at_most_three_sat F \<in> at_most_three_sat_list"
  shows "F \<in> sat_list"
  using assms sat_to_at_most_three_sat_aux_complete sat_list_def models_V
  unfolding at_most_three_sat_list_def sat_to_at_most_three_sat_def
  by fast

section "Conclusion"

theorem is_reduction_sat_to_at_most_three_sat:
  "is_reduction sat_to_at_most_three_sat sat_list at_most_three_sat_list"
  using sat_to_3_sat_sound sat_to_3_sat_complete
  by (intro is_reductionI) auto

end
