theory SAT_To_AT_MOST_3SAT
imports "SAT_To_SATL" "../Reductions"
begin

section "AT_MOST_3SAT Definition"

definition AT_MOST_3SAT where
  "AT_MOST_3SAT  = {F. sat\<^sub>l F \<and> (\<forall>cls \<in> set F. length cls \<le> 3)}"


section "The Reduction
"
datatype 'a red = v 'a | u "nat \<times> nat"

fun to_at_most_3_clause where
  "to_at_most_3_clause (a#b#c#d#rest) i j =  [a,b,Pos (u (i,j))] #  to_at_most_3_clause (Neg (u (i,j))#c#d#rest) i (j+1)
                                                                 @ map (\<lambda>l. [Pos (u(i,j)), flip l]) (c#d#rest)"
| "to_at_most_3_clause xs i j = [xs]"

fun sat_to_at_most_3sat_aux where
  "sat_to_at_most_3sat_aux (x#xs) i = (to_at_most_3_clause x i 0)  @ (sat_to_at_most_3sat_aux xs (i+1))"
| "sat_to_at_most_3sat_aux [] i = []"

abbreviation V  where
  "V F \<equiv> map (map (map_lit v)) F"

definition sat_to_at_most_3sat where
  "sat_to_at_most_3sat F  = sat_to_at_most_3sat_aux (V F) 0"


section "reduction helper lemmas"

lemma vars_to_at_most_3_clause:
    "vars (to_at_most_3_clause cls i j) \<subseteq> (vars_cls cls \<union> {u (i,k) |k. True})"
  by (induction j rule: to_at_most_3_clause.induct)
     (auto simp add: vars_cls_def vars_def)

lemma vars_sat_to_at_most_3sat_aux:
    "vars (sat_to_at_most_3sat_aux F i) \<subseteq> (vars F \<union> {u (k,j) |k j. k \<ge> i})"
  by (induction rule: sat_to_at_most_3sat_aux.induct)
     (auto intro!: vars_to_at_most_3_clause[THEN subset_trans] 
           simp: vars_cons vars_append)

lemma models_V:
  shows "sat\<^sub>l (V F) \<longleftrightarrow> sat\<^sub>l F"
proof 
  assume "\<exists>\<sigma>. \<sigma> \<Turnstile>\<^sub>l V F"
  then obtain \<sigma> where "\<sigma> \<Turnstile>\<^sub>l V F" 
    by blast
  let ?\<sigma> = "\<lambda>x. \<sigma> (v x)"
  have "(?\<sigma>\<up>) x = (\<sigma>\<up>) (map_lit v x)" for x
    by (cases x) (auto simp add: lift_def)
  then have "?\<sigma> \<Turnstile>\<^sub>l F" using \<open>\<sigma> \<Turnstile>\<^sub>l V F\<close>
    by (auto simp add: models_def)
  then show "\<exists>\<sigma>. \<sigma> \<Turnstile>\<^sub>l  F" 
    by blast
next
  assume "\<exists>\<sigma>. \<sigma> \<Turnstile>\<^sub>l F"
  then obtain \<sigma> where "\<sigma> \<Turnstile>\<^sub>l  F" 
    by blast
  let ?\<sigma> = "case_red \<sigma> (\<lambda>x. True)"
  have "(?\<sigma>\<up>) (map_lit v x) = (\<sigma>\<up>) x" for x
    by (cases x)(auto simp add: lift_def)
  then have "?\<sigma> \<Turnstile>\<^sub>l V F"
    using \<open>\<sigma> \<Turnstile>\<^sub>l F\<close> 
    by (auto simp add: models_def)
 then show "\<exists>\<sigma>. \<sigma> \<Turnstile>\<^sub>l  V F" 
    by blast
qed

section "Soundness"
  
lemma to_at_most_3_clause_sound:
  assumes  "\<sigma> \<Turnstile>\<^sub>l [cls]"
           "vars_cls cls \<inter> {u (i, k)|k. k \<ge> j} = {}"          
  shows "\<exists>\<sigma>'. (\<forall>x \<in> -{u (i,k) |k. k \<ge> j}. \<sigma>' x = \<sigma> x)
              \<and> \<sigma>' \<Turnstile>\<^sub>l to_at_most_3_clause cls i j"
  using assms
proof (induction arbitrary: \<sigma> rule: to_at_most_3_clause.induct )
  case (1 a b c d rest i j)
  (* we create an assignment that satisfies the IH *)
  define \<sigma>1 where "\<sigma>1 = \<sigma>(u (i,j) := \<sigma> \<Turnstile>\<^sub>l [c#d#rest])"
  
  have "\<sigma>1 \<Turnstile>\<^sub>l [c#d#rest]" if "\<sigma> \<Turnstile>\<^sub>l[c#d#rest]"
    using that 1(3) 
    by (intro models_cong[of _ \<sigma>1 \<sigma>])
       (auto simp add: \<sigma>1_def vars_def vars_cls_def)
  then have "\<sigma>1 \<Turnstile>\<^sub>l [Neg (u (i, j)) # c # d # rest]"
       by (cases "\<sigma> \<Turnstile>\<^sub>l [c#d#rest]")
          (auto simp add: models_def \<sigma>1_def lift_def)
   moreover have "vars_cls (Neg (u (i, j)) # c # d # rest) \<inter> {u (i, k) |k. j + 1 \<le> k} = {}"
    using 1(3)
    by (auto simp add: vars_cls_def)
  ultimately obtain \<sigma>' where  
    \<sigma>'_def: "(\<forall>x\<in>- {u (i, k) |k. j + 1 \<le> k}. \<sigma>' x = \<sigma>1 x) \<and>
                    \<sigma>' \<Turnstile>\<^sub>l to_at_most_3_clause (Neg (u (i, j)) # c # d # rest) i (j + 1)"
    using 1 by fastforce
  moreover then have "\<sigma>' x = \<sigma> x" if "x \<in>- {u (i, k) |k. j \<le> k}" for x
    using that
    by (cases "x = u (i,j)", auto simp add: \<sigma>1_def) force  
  moreover have "\<sigma>' \<Turnstile>\<^sub>l [[Pos (u(i,j)), flip l]]" if "l \<in> set (c # d # rest)" for l
  proof (intro models_cong[of _ \<sigma>' \<sigma>1])
    show"\<sigma>1 \<Turnstile>\<^sub>l [[Pos (u(i,j)), flip l]]" 
    proof (cases "\<sigma> \<Turnstile>\<^sub>l [c#d#rest]")
      case False
      then have "\<not> (\<sigma>\<up>) l"
        using that
        by (auto simp add: models_def)
      moreover have "var l \<noteq> u (i, j)"
        using 1(3) that
        by (auto simp add: vars_cls_def)
      ultimately show ?thesis
        by (cases l) (auto simp add: models_def \<sigma>1_def lift_def)
    qed(auto simp add: \<sigma>1_def models_def lift_def)

    have "vars [[Pos (u (i, j)), flip l]] \<subseteq> -{u (i, k) |k. j + 1 \<le> k}"
      using that 1(3)
      by(auto simp add: vars_def vars_cls_def)
    then show "\<forall>x\<in>vars [[Pos (u (i, j)), flip l]]. \<sigma>' x = \<sigma>1 x"
      using \<sigma>'_def  by blast
  qed

  moreover have "\<sigma>' \<Turnstile>\<^sub>l [[a, b, Pos (u (i, j))]]" 
  proof (intro models_cong[of _ \<sigma>' \<sigma>1])
    have "\<sigma>1 \<Turnstile>\<^sub>l [[a,b]]" if "\<not>\<sigma> \<Turnstile>\<^sub>l[c#d#rest]"
      using 1(3) that 1(2) 
      by (intro models_cong[of _ \<sigma>1 \<sigma>])
        (auto simp add: models_def \<sigma>1_def vars_def vars_cls_def)
    then show "\<sigma>1 \<Turnstile>\<^sub>l [[a, b, Pos (u (i, j))]]"
       by (cases "\<sigma> \<Turnstile>\<^sub>l [c#d#rest]")
          (auto simp add: models_def \<sigma>1_def lift_def)
    
     have "vars [[a, b, Pos (u (i, j))]]  \<subseteq> -{u (i, k) |k. j + 1 \<le> k}"
      using 1(3)
      by(auto simp add: vars_def vars_cls_def)
     then show "\<forall>x\<in>vars[[a, b, Pos (u (i, j))]]. \<sigma>' x = \<sigma>1 x"
      using \<sigma>'_def  by blast
  qed
  
  ultimately show ?case
    using \<sigma>'_def unfolding models_def
    by (intro exI[of _ \<sigma>']) auto
qed(auto)


lemma sat_to_at_most_3sat_aux_sound:
  assumes "\<sigma> \<Turnstile>\<^sub>l F"
          "vars F \<inter> u ` UNIV = {}"
  shows "\<exists>\<sigma>'. \<sigma>' \<Turnstile>\<^sub>l (sat_to_at_most_3sat_aux F i)
             \<and> (\<forall>x \<in> -{u (k,j) |k j. k \<ge> i}. \<sigma>' x = \<sigma> x)"
  using assms 
proof (induct F i  rule: sat_to_at_most_3sat_aux.induct )
  case (1 x xs i)
  then obtain \<sigma>ih where \<sigma>ih_models: "\<sigma>ih \<Turnstile>\<^sub>l sat_to_at_most_3sat_aux xs (i + 1)"
                  and   \<sigma>ih_\<sigma>:  "(\<forall>x \<in> -{u (k,j) |k j. k \<ge> (i+1)}. \<sigma>ih x = \<sigma> x)"
    unfolding models_def 
    by (auto simp add: vars_cons)
  moreover have "vars_cls x \<subseteq>  -{u (k,j) |k j. k \<ge> (i+1)}"
    using 1(3) vars_cons unfolding vars_cls_def 
    by fastforce
  ultimately have "\<sigma>ih \<Turnstile>\<^sub>l [x]" 
    using 1
    by(intro models_cong[of _ \<sigma>ih \<sigma>])
      (auto simp: vars_cons vars_def models_def vars_cls_def)
  moreover have "vars_cls x \<inter> {u (i, k) |k. 0 \<le> k} = {}"
    using 1 by (auto simp add: vars_def)
  ultimately obtain \<sigma>' where  \<sigma>'_def: "(\<forall>x \<in> -{u (i,k) |k. 0 \<le> k}. \<sigma>' x = \<sigma>ih x)
                         \<and> \<sigma>' \<Turnstile>\<^sub>l to_at_most_3_clause x i 0"
    using to_at_most_3_clause_sound[of \<sigma>ih]
    by presburger (* try0, no other methods *)
  moreover have "vars (sat_to_at_most_3sat_aux xs (i + 1)) \<subseteq>  -{u (i,k) |k. True}"
    using 1
    by (intro vars_sat_to_at_most_3sat_aux[THEN subset_trans])
       (auto simp add: vars_cons)
  ultimately have "\<sigma>' \<Turnstile>\<^sub>l sat_to_at_most_3sat_aux xs (i + 1)" using \<sigma>ih_models
    by (intro models_cong[of _ \<sigma>' \<sigma>ih]) auto
  moreover have "\<forall>x \<in> -{u (k,j) |k j. k \<ge> i}. \<sigma>' x = \<sigma> x"
    using \<sigma>ih_\<sigma> \<sigma>'_def 
    by force   
  ultimately show ?case 
    using \<sigma>'_def unfolding models_def
    by (intro exI[of _ \<sigma>']) auto
qed (auto)


lemma sat_to_3_sat_sound:
  assumes "F \<in> SAT\<^sub>l"
  shows "sat_to_at_most_3sat F \<in> AT_MOST_3SAT"
proof -
  obtain \<sigma> where "\<sigma> \<Turnstile>\<^sub>l V F"
    using SAT\<^sub>l_def assms models_V 
    by fastforce
  moreover have "vars (V F) \<inter> u ` UNIV = {}"
    by (auto simp add: vars_def vars_cls_def)
  ultimately have "sat\<^sub>l (sat_to_at_most_3sat F)"
    unfolding  sat_to_at_most_3sat_def
    using sat_to_at_most_3sat_aux_sound by blast
  moreover{
    have "length cls \<le> 3" if "cls \<in>  set (to_at_most_3_clause x i j)" for cls x i j
      using that
      by (induction x i j rule: to_at_most_3_clause.induct) auto
    then have "length cls \<le> 3" if "cls \<in> set (sat_to_at_most_3sat_aux G i)" for cls G i
      using that
      by (induction G i rule: sat_to_at_most_3sat_aux.induct) auto
    then have "length cls \<le> 3" if "cls \<in> set (sat_to_at_most_3sat F)" for cls
      by (metis sat_to_at_most_3sat_def that)
  }
  ultimately show ?thesis
    using AT_MOST_3SAT_def  
    by blast
qed

section "Completness"

lemma to_at_most_3_clause_complete:
  assumes  "\<sigma> \<Turnstile>\<^sub>l to_at_most_3_clause cls i j"                
  shows "\<sigma> \<Turnstile>\<^sub>l [cls]"
  using assms
proof(induction cls i j rule:to_at_most_3_clause.induct)
  case (1 a b c d rest i j)
  then show ?case 
    by (cases "\<sigma> (u (i,j))")
       (auto simp add: models_def lift_def)
qed (auto)

lemma sat_to_at_most_3sat_aux_complete:
  assumes "\<sigma> \<Turnstile>\<^sub>l sat_to_at_most_3sat_aux F i"                
  shows "\<sigma> \<Turnstile>\<^sub>l F"
  using assms to_at_most_3_clause_complete
  by (induction F i rule:sat_to_at_most_3sat_aux.induct)
     (rule models_cons[THEN iffD2], auto simp add: models_append)


lemma sat_to_3_sat_complete:
  assumes "sat_to_at_most_3sat F \<in> AT_MOST_3SAT"
  shows  "F \<in> SAT\<^sub>l"
  using assms sat_to_at_most_3sat_aux_complete SAT\<^sub>l_def models_V 
  unfolding AT_MOST_3SAT_def sat_to_at_most_3sat_def SAT\<^sub>l_def 
  by fast

section "Conclusion"

theorem  is_reduction_sat_to_at_most_3sat:
  "is_reduction sat_to_at_most_3sat SAT\<^sub>l AT_MOST_3SAT"
  unfolding is_reduction_def 
  using sat_to_3_sat_sound sat_to_3_sat_complete
  by auto

end