\<^marker>\<open>creator Florian Keßler\<close>

section \<open>IMP-- Subprograms\<close>

theory IMP_Minus_Minus_Subprograms
  imports IMP_Minus_Minus_Small_StepT
begin

text \<open>We give functions that enumerate all subprograms of an IMP-- program, that is, all 
  computations that could be reached during the execution of an IMP-- program. Note that this is 
  a purely syntactical definition, i.e. we also take into account executions that are actually 
  impossible to reach due to the semantics of IMP--. We show completeness of this definition,
  i.e. if a IMP-- program can reach a certain computation, than that computation is contained in
  our definition. \<close>

fun all_subprograms :: "com \<Rightarrow> com list" where
"all_subprograms (SKIP) = [SKIP]" |
"all_subprograms (Assign v b) = [(Assign v b), SKIP]" |
"all_subprograms (c1 ;; c2) = (map (\<lambda> c. c ;; c2) (all_subprograms c1)) @ all_subprograms c1 
  @ all_subprograms c2" |
"all_subprograms (If v c1 c2) = [(If v c1 c2)] @ all_subprograms c1 @ all_subprograms c2" |
"all_subprograms (While v c) = [(While v c), SKIP] @ all_subprograms c @ 
  (map (\<lambda> x. x ;; (While v c)) (all_subprograms c))"

definition enumerate_subprograms :: "com \<Rightarrow> com list" where
"enumerate_subprograms c = remdups (all_subprograms c)"

fun all_variables :: "com \<Rightarrow> vname list" where
"all_variables (SKIP) = []" |
"all_variables (Assign v _) = [ v ]" |
"all_variables (c1 ;; c2) = []" |
"all_variables (If vs c1 c2) = vs" |
"all_variables (While vs c) = vs"

definition enumerate_variables :: "com \<Rightarrow> vname list" where
"enumerate_variables c = remdups (concat (map all_variables (enumerate_subprograms c)))"

lemma enumerate_variables_distinct: "distinct (enumerate_variables c)" 
  by (auto simp: enumerate_variables_def)

lemma set_enumerate_variables_seq: "set (enumerate_variables (c1 ;; c2)) = 
  set (enumerate_variables c1) \<union> set (enumerate_variables c2)" 
  by(auto simp: enumerate_variables_def enumerate_subprograms_def)

lemma set_enumerate_variables_if: "set (enumerate_variables (IF vs\<noteq>0 THEN c1 ELSE c2))
  = set vs \<union> set (enumerate_variables c1) \<union> set (enumerate_variables c2)"
  by(auto simp: enumerate_variables_def enumerate_subprograms_def)

lemma set_enumerate_variables_while: "set (enumerate_variables (WHILE vs\<noteq>0 DO c))
  = set vs \<union> set (enumerate_variables c)"
  by(auto simp: enumerate_variables_def enumerate_subprograms_def)

lemma enumerate_variables_assign[simp]: "enumerate_variables (x1 ::= x2) = [x1]"
  by(auto simp: enumerate_variables_def enumerate_subprograms_def)                  

lemma enumerate_variables_SKIP[simp]: "enumerate_variables SKIP = []"
  by(auto simp: enumerate_variables_def enumerate_subprograms_def)                  

declare enumerate_subprograms_def[simp] 

lemma c_in_all_subprograms_c[simp]: "c \<in> set (enumerate_subprograms c)" 
  by (induction c) auto

lemma enumerate_variables_all_variables[simp]: "x \<in> set (all_variables c) \<Longrightarrow> x \<in> set (enumerate_variables c)"
  using c_in_all_subprograms_c by (auto simp: enumerate_variables_def)

lemma enumerate_subprograms_complete_step: "(c1, s1) \<rightarrow> (c2, s2) 
  \<Longrightarrow> c2 \<in> set (enumerate_subprograms c1)"
apply (induction c1 s1 c2 s2 rule: small_step_induct)
  using c_in_all_subprograms_c apply(auto)
done

lemma enumerate_subprograms_transitive: "c2 \<in> set (enumerate_subprograms c1) \<Longrightarrow> 
  c3 \<in> set (enumerate_subprograms c2) \<Longrightarrow> c3 \<in> set (enumerate_subprograms c1)"
proof (induction c1 arbitrary: c2 c3 rule: all_subprograms.induct)
  case (4 v c4 c5)
  then have "(c2 = (If v c4 c5)) \<or> (c2 \<in> set (all_subprograms c4)) 
              \<or> (c2 \<in> set (all_subprograms c5))"
      by (metis Un_iff all_subprograms.simps append.simps append.simps enumerate_subprograms_def set_ConsD set_append set_remdups)
  then show ?case
  proof (elim disjE)
    assume "c2 \<in> set (all_subprograms c5)" 
    then show ?thesis using 4 by auto
  next
    assume "c2 \<in> set (all_subprograms c4)"
    then show ?thesis using 4 by auto
  next
    assume "c2 = (If v c4 c5)"
    then show ?thesis using 4 by auto
  qed
next
  case (5 v c)
  then have "c2 \<in> set (all_subprograms (While v c))" by (metis enumerate_subprograms_def set_remdups)
  then have "c2 \<in> set ([While v c, SKIP] @ all_subprograms c @ map (\<lambda> x. x ;; (While v c)) (all_subprograms c))" 
    by (metis all_subprograms.simps enumerate_subprograms_def map_eq_conv set_append set_remdups) 
  then have "(c2 = (While v c)) \<or> c2 = SKIP \<or> (c2 \<in> set (all_subprograms c)) 
              \<or> (c2 \<in> set (map (\<lambda> x. x ;; (While v c)) (all_subprograms c)))" by simp
  then show ?case
  proof (elim disjE)
    assume "c2 = (While v c)"
    then show ?thesis using 5 by auto
  next
    assume "c2 = SKIP"
    then show ?thesis using 5 by auto
  next
    assume "c2 \<in> set (all_subprograms c)"
    then show ?thesis using 5 
      by (metis Un_iff all_subprograms.simps enumerate_subprograms_def set_append set_remdups)
  next
    assume "c2 \<in> set (map (\<lambda> x. x ;; (While v c)) (all_subprograms c))"
    then obtain c' where *: "c2 = c' ;; (While v c) \<and> c' \<in> set (all_subprograms c)" by auto
    then have "c3 \<in> set (map (\<lambda> x. x ;; (While v c)) (all_subprograms c')) \<or> c3 \<in> set (all_subprograms c')
      \<or> c3 \<in> set (all_subprograms (While v c))" using 5 by auto
    then show ?thesis
    proof (elim disjE)
      assume "c3 \<in> set (map (\<lambda> x. x ;; (While v c)) (all_subprograms c'))"
      then have "c3 \<in> set (map (\<lambda> x. x ;; (While v c)) (all_subprograms c))" using * 5 by auto
      then show ?thesis by auto
    next
      assume "c3 \<in> set (all_subprograms c')"
      then have "c3 \<in> set (all_subprograms c)" using * 5 by auto
      then show ?thesis by auto
    next
      assume "c3 \<in> set (all_subprograms (While v c))"
      then show ?thesis using 5 by (metis enumerate_subprograms_def set_remdups)
    qed
  qed
qed auto

lemma enumerate_subprograms_complete: "(c1, s1)\<rightarrow>\<^bsup>t\<^esup> (c2, s2)
  \<Longrightarrow>  c2 \<in> set (enumerate_subprograms c1)"
proof(induction t arbitrary: c1 s1 c2 s2)
  case 0
  then show ?case using c_in_all_subprograms_c by auto
next
  case (Suc t)
  then obtain c1' s1' where "((c1, s1) \<rightarrow> (c1', s1')) \<and> ((c1', s1')\<rightarrow>\<^bsup>t\<^esup> (c2, s2))" by auto
  then show ?case using enumerate_subprograms_transitive Suc enumerate_subprograms_complete_step 
    by blast
qed

lemma SKIP_in_enumerate_subprograms[simp]: "SKIP \<in> set (enumerate_subprograms c)" 
  by (induction c rule: all_subprograms.induct) auto

lemma enumerate_subprograms_enumerate_variables: "c' \<in> set (enumerate_subprograms c) 
  \<Longrightarrow> set (enumerate_variables c') \<subseteq> set (enumerate_variables c)" 
 by (auto simp: enumerate_variables_def) 
     (metis enumerate_subprograms_def enumerate_subprograms_transitive set_remdups)

lemma step_doesnt_add_variables: "(c1, s1) \<rightarrow> (c2, s2) \<Longrightarrow> c1 \<in> set (enumerate_subprograms c)
  \<Longrightarrow> dom s1 = set (enumerate_variables c)
  \<Longrightarrow> dom s2 = set (enumerate_variables c)"
proof (induction c1 s1  c2 s2 rule: small_step_induct)
  case (Assign x a s)
  have "x \<in> set (enumerate_variables (x ::= a))" by simp
  then have "x \<in> set (enumerate_variables c)" 
    using Assign enumerate_subprograms_enumerate_variables by fastforce
  thus ?case using Assign by(auto simp: dom_def)
next
  case (Seq2 c\<^sub>1 s c\<^sub>1' s' c\<^sub>2)
  have "c\<^sub>1 \<in> set (enumerate_subprograms (c\<^sub>1 ;; c\<^sub>2))" using c_in_all_subprograms_c by simp
  then have "c\<^sub>1 \<in> set (enumerate_subprograms c)" 
    using Assign Seq2 enumerate_subprograms_transitive by blast
  then show ?case using Seq2 by auto
qed auto


lemma small_step_fun_restrict_variables: 
  "set (enumerate_variables c1) \<subseteq> S \<Longrightarrow> small_step_fun (c1, s1 |` S) 
    = (fst (small_step_fun (c1, s1)), snd (small_step_fun (c1, s1)) |` S)" 
  apply(induction c1 arbitrary: S)
  using subsetD by(fastforce simp: set_enumerate_variables_seq 
      set_enumerate_variables_if set_enumerate_variables_while)+

lemma small_step_fun_doesnt_add_variables:
  "set (enumerate_variables c1) \<subseteq> S 
  \<Longrightarrow> set (enumerate_variables (fst (small_step_fun (c1, s1)))) \<subseteq> S"
  apply(induction c1)
  by(auto simp: set_enumerate_variables_seq 
      set_enumerate_variables_if set_enumerate_variables_while)

lemma t_small_step_fun_restrict_variables: 
  "set (enumerate_variables c1) \<subseteq> S \<Longrightarrow> t_small_step_fun t (c1, s1 |` S) 
    = (fst (t_small_step_fun t (c1, s1)), snd (t_small_step_fun t (c1, s1)) |` S)" 
  apply(induction t arbitrary: c1 s1)
  by(auto simp: small_step_fun_restrict_variables small_step_fun_doesnt_add_variables)

end