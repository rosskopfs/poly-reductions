theory XC_Definition
  imports "../Polynomial_Reductions"
          "HOL-Library.Disjoint_Sets"
          "Poly_Reductions_Lib.SAT_Definition"
begin

subsection "Exact cover definitions"

definition "exact_cover_alter_def \<equiv> 
   {(X, S). finite X \<and> \<Union>S \<subseteq> X \<and>
    (\<exists>S' \<subseteq> S. \<forall>x \<in> X. \<exists>s \<in> S'. x \<in> s \<and> (\<forall>t \<in> S'. s \<noteq> t \<longrightarrow> x \<notin> t))}"

definition "exact_cover \<equiv> {(X, S). finite X \<and> \<Union>S \<subseteq> X \<and> (\<exists>S' \<subseteq> S. \<Union>S' = X \<and> disjoint S')}"

lemma exact_cover_alter_def_eq: "(X, S) \<in> exact_cover_alter_def \<longleftrightarrow> (X, S) \<in> exact_cover"
proof (standard, goal_cases)
  assume 1: "(X, S) \<in> exact_cover_alter_def"
  hence "\<Union>S \<subseteq> X" unfolding exact_cover_alter_def_def 
    by blast
  from 1 obtain S' where s_def: "S' \<subseteq> S" "\<forall>x \<in> X. \<exists>s \<in> S'. x \<in> s \<and> (\<forall>t \<in> S'. s \<noteq> t \<longrightarrow> x \<notin> t)"
    unfolding exact_cover_alter_def_def 
    by blast 
  hence "\<forall>x \<in> X. \<exists>s \<in> S'. x \<in> s" 
    by blast   
  then have "X \<subseteq> \<Union>S'" 
    by blast 
  moreover have "\<Union>S' \<subseteq> X" 
    using \<open>S' \<subseteq> S\<close> \<open>\<Union>S \<subseteq> X\<close> 
    by blast 
  ultimately have "X = \<Union>S'" 
    by simp 
  have "disjoint S'"
  proof (rule disjointI)
    fix a b 
    assume ab_def: "a \<in> S'" "b \<in> S'" "a \<noteq> b"

    with s_def have 
      "\<forall>x \<in> X. x \<in> a \<longrightarrow> x \<notin> b" 
      "\<forall>x \<in> X. x \<in> b \<longrightarrow> x \<notin> a"
       by metis+ 
    hence "\<forall>x\<in>X. x \<notin> a \<inter> b" 
      by blast 
    moreover from \<open>\<Union>S' \<subseteq> X\<close> have "\<forall>x \<in> a \<inter> b. x \<in> X"
      using ab_def 
      by blast
    ultimately show "a \<inter> b = {}" 
      by blast
  qed

  from 1 have "finite X"
    unfolding exact_cover_alter_def_def
    by blast
  with \<open>X = \<Union>S'\<close> \<open>disjoint S'\<close> \<open>S' \<subseteq> S\<close> \<open>\<Union>S \<subseteq> X\<close> 
  show "(X, S) \<in> exact_cover"
    unfolding exact_cover_def 
    by blast
next
  assume 2:"(X, S) \<in> exact_cover"
  then have "\<Union>S \<subseteq> X" "finite X"
    unfolding exact_cover_def 
    by blast+
  from 2 obtain S' where S'_def: "S' \<subseteq> S" "\<Union>S' = X" "disjoint S'"
    unfolding exact_cover_def 
    by blast 
  have "\<forall>x \<in> X. \<exists>s \<in> S'. x \<in> s \<and> (\<forall>t \<in> S'. s \<noteq> t \<longrightarrow> x \<notin> t)"
  proof 
    fix x 
    assume "x \<in> X"
    then obtain s where "s \<in> S'" "x \<in> s" 
      using S'_def 
      by blast
    moreover then have "\<forall>t \<in> S'. s \<noteq> t \<longrightarrow> x \<notin> t"
      using disjointD[OF \<open>disjoint S'\<close>] 
      by blast
    ultimately show "\<exists>s \<in> S'. x \<in> s \<and> (\<forall>t \<in> S'. s \<noteq> t \<longrightarrow> x \<notin> t)"
      by blast
  qed 
  then show "(X, S) \<in> exact_cover_alter_def" 
    using \<open>\<Union>S \<subseteq> X\<close> \<open>S' \<subseteq> S\<close> \<open>finite X\<close>
    unfolding exact_cover_alter_def_def 
    by blast
qed

definition cover :: "'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
"cover S' X \<longleftrightarrow> \<Union>S' = X \<and> disjoint S'"

lemma exact_cover_I: "\<lbrakk>S' \<subseteq> S; \<Union>S \<subseteq> X; cover S' X; finite X\<rbrakk> \<Longrightarrow> (X, S) \<in> exact_cover"
  unfolding exact_cover_def cover_def 
  by blast

lemma exact_cover_D: "\<lbrakk>(X, S) \<in> exact_cover; \<Union>S \<subseteq> X\<rbrakk> \<Longrightarrow> (\<exists>S' \<subseteq> S. cover S' X)"
  unfolding exact_cover_def cover_def 
  by blast

definition
  "cnf_sat \<equiv> {F. sat F \<and> (\<forall>cls \<in> set F. finite cls)}"
end 
