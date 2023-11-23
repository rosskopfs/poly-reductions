theory SS_To_SS_List
  imports XC_To_SS_aux

begin

section "subset sum to number partition"

subsection "subset_sum to subset_sum under nat and list"

definition "generate_func S \<equiv> (SOME f. (if S = {} then bij_betw f S {} else bij_betw f S {1..card S}))"

definition "ss_to_ss_indeces \<equiv> (\<lambda>(S, w, B). if finite S then ((generate_func S) ` S, (\<lambda>x. w (inv_into S (generate_func S) x)), B) else ({}, id, 1))"

definition ss_indeces_to_ss_list :: "nat set \<times> (nat \<Rightarrow> nat) \<times> nat \<Rightarrow> nat list \<times> nat" where 
"ss_indeces_to_ss_list \<equiv> (\<lambda>(S, w, B). if (finite S \<and> S = {1..card S}) then (map w (sorted_list_of_set S), B) else ([], 1))"

paragraph ss_to_ss_indeces_complete

lemma ss_to_ss_indeces_sound_aux:
assumes "(S, w, B) \<in> subset_sum"
shows "((generate_func S) ` S, (\<lambda>x. w (inv_into S (generate_func S) x)), B) \<in> subset_sum_indeces"
proof -
  let ?f = "(generate_func S)"
  from assms have "finite S"
    unfolding subset_sum_def 
    by blast 
  hence "\<exists>f. (if S = {} then bij_betw f S {} else bij_betw f S {1..card S})"
    using bij_exist
    by blast 
  hence "bij_betw ?f S (if S = {} then {} else {1..card S})"
    unfolding generate_func_def
    using someI_ex[of "\<lambda>f. (if S = {} then bij_betw f S {} else bij_betw f S {1..card S})"]
    by presburger
  hence *: "?f ` S = (if S = {} then {} else {1..card S})" "inj_on ?f S"
    unfolding bij_betw_def
    by blast+
  hence **: "?f ` S = (if ?f ` S = {} then {} else {1..card (?f ` S)})" "finite (?f ` S)"
    by auto

  from assms obtain S' where S'_def: "S' \<subseteq> S" "finite S'" "sum w S' = B"
    unfolding subset_sum_def is_subset_sum_def
    using finite_subset 
    by blast
  with *(2) have ***: "inj_on ?f S'" "?f ` S' \<subseteq> ?f ` S"
    unfolding inj_on_def
    by auto

  have "\<forall>x\<in> S. (inv_into S ?f (?f x)) = x"
    using inv_into_f_f[OF *(2)]
    by blast
  hence "\<forall>x\<in> S. w (inv_into S ?f (?f x)) = w x"
    by fastforce
  with S'_def have "\<forall>x\<in> S'. w (inv_into S ?f (?f x)) = w x"
    by blast
  hence "sum (\<lambda>x. w (inv_into S ?f x)) (?f ` S') = sum w S'"
    using sum.reindex_cong[OF ***(1), of _ "(\<lambda>x. w (inv_into S ?f x))" w]
    by blast
  with S'_def(3) have "sum (\<lambda>x. w (inv_into S ?f x)) (?f ` S') = B"
    by blast
  with ** ***(2) show ?thesis 
    unfolding subset_sum_indeces_def
    by blast
qed 

lemma ss_to_ss_indeces_complete_aux:
assumes "finite S"
  "((generate_func S) ` S, (\<lambda>x. w (inv_into S (generate_func S) x)), B) \<in> subset_sum_indeces"
shows "(S, w, B) \<in> subset_sum" 
proof -
  let ?f = "(generate_func S)"
  from assms have "\<exists>f. (if S = {} then bij_betw f S {} else bij_betw f S {1..card S})"
    using bij_exist
    by blast 
  hence bij_orig:"bij_betw ?f S (if S = {} then {} else {1..card S})"
    unfolding generate_func_def
    using someI_ex[of "\<lambda>f. (if S = {} then bij_betw f S {} else bij_betw f S {1..card S})"]
    by presburger
  hence *:"?f ` S = (if S = {} then {} else {1..card S})" "inj_on ?f S"
    unfolding bij_betw_def
    by blast+

  from bij_orig have "bij_betw (inv_into S ?f) (if S = {} then {} else {1..card S}) S"
    using bij_betw_inv_into
    by blast
  hence **: "(inv_into S ?f) ` (if S = {} then {} else {1..card S}) = S" "inj_on (inv_into S ?f) (if S = {} then {} else {1..card S})"
    unfolding bij_betw_def
    by blast+
  
  from assms have prems: "finite (?f ` S)" "?f ` S = (if (?f ` S) = {} then {} else {1..card (?f ` S)})" 
    "(\<exists>S' \<subseteq> ?f ` S. sum (\<lambda>x. w ((inv_into S ?f) x)) S' = B)"
    unfolding subset_sum_indeces_def
    by blast+
  from assms(1) prems(3) obtain S' where S'_def: "sum (\<lambda>x. w ((inv_into S ?f) x)) S' = B" "S' \<subseteq> ?f ` S" "finite S'"
    using finite_subset 
    by blast+
  with * have "((inv_into S ?f) ` S') \<subseteq> ((inv_into S ?f) ` (?f ` S))" 
    unfolding inj_on_def
    by fast
  moreover from * have "((inv_into S ?f) ` (?f ` S)) = S"
    by fastforce
  ultimately have **:"((inv_into S ?f) ` S') \<subseteq> S"
    by argo
  moreover from S'_def(2) have "inj_on (inv_into S ?f) S'"
    using inj_on_inv_into
    by blast
  ultimately have "sum w ((inv_into S ?f) ` S') = sum (\<lambda>x. w ((inv_into S ?f) x)) S'"
    using sum.reindex_cong
    by metis
  with S'_def have "sum w ((inv_into S ?f) ` S') = B"
    by blast
  with ** assms(1) show ?thesis 
    unfolding subset_sum_def is_subset_sum_def
    by blast
qed 

paragraph ss_indeces_to_ss_list  

lemma list_indexing:
assumes "sorted_wrt (<) xs" "set xs = {k + 1..k + length xs}" "i < length xs"
shows "xs!i = i + k + 1"
using assms proof (induction xs arbitrary: i k)
  case (Cons a xs)
  from Cons(2) have "\<forall>x \<in> set (a # xs). a \<le> x" 
    by auto
  moreover from Cons(3) have "a \<in> {k+1..k + length (a # xs)}" 
    by auto 
  ultimately have "a = k + 1"
    using Cons(3)
    by fastforce
  
  from Cons have xs_prems: "sorted_wrt (<) xs" "a \<notin> set xs"
   by auto
  with Cons(3) have "set xs = {k+1..k + length (a # xs)} - {a}"
    by auto 
  with \<open>a = k + 1\<close> have "set xs = {k+2..k+length (a # xs)}"
    by fastforce
  with xs_prems(1) have "j < length xs \<Longrightarrow> xs ! j = j + k + 2" for j 
    using Cons(1)
    by simp
  hence "\<lbrakk>j > 0; j < length xs + 1\<rbrakk> \<Longrightarrow> (a # xs) ! j = j + k + 1" for j
    by simp
  moreover with \<open>a = k + 1\<close> have "(a # xs) ! 0 = k + 1"
    by simp
  ultimately show ?case 
    using Cons(4)
    apply (cases "i > 0")
    by auto
qed auto

lemma ss_indeces_to_ss_list_sound_aux:
assumes "(S, w, B) \<in> subset_sum_indeces"
shows "(map w (sorted_list_of_set S), B) \<in> subset_sum_list"
proof -
  from assms have prems: "finite S" "S = (if S = {} then {} else {1..card S})" "(\<exists>S'\<subseteq>S. sum w S' = B)"
    unfolding subset_sum_indeces_def
    by auto
  then obtain S' where S'_def: "S' \<subseteq> S" "sum w S' = B"
    by blast
  let ?as = "map w (sorted_list_of_set S)"  
  let ?xs = "map (\<lambda>x. of_bool (x \<in> S')) (sorted_list_of_set S)"

  have xs_prop: "length ?xs = length ?as" "\<forall>i < length ?xs. ?xs!i \<in> {0, 1}"
    by simp+
  
  have *: "w x * (\<lambda>x. of_bool (x \<in> S')) x = (if x \<in> S' then w x else 0)" for x
    unfolding of_bool_def
    by auto
  have **:"(sorted_wrt (<) (sorted_list_of_set S))"
    by auto

  have "i < length (sorted_list_of_set S) \<longrightarrow> (sorted_list_of_set S)!i = i+1" for i 
    using list_indexing[OF **, of 0 i] prems(2)
    apply (cases "S = {}")
    using prems(1) by force+ 
  hence ***: "\<forall>i < length (sorted_list_of_set S). (sorted_list_of_set S)!i = i+1"
    by blast
  
  have "(\<Sum>i < length ?as. ?as!i * ?xs!i) 
    = (\<Sum>i < length (sorted_list_of_set S). ?as!i * ?xs!i)"
    by simp
  also have "... = (\<Sum>i < length (sorted_list_of_set S). 
    w ((sorted_list_of_set S)!i) * (\<lambda>x. of_bool (x \<in> S')) ((sorted_list_of_set S)!i))"
    by force 
  also have "... = (\<Sum>i < length (sorted_list_of_set S). 
    w (i+1) * (\<lambda>x. of_bool (x \<in> S')) (i + 1))"
    using ***
    by fastforce
  also have "... = (\<Sum>i < length (sorted_list_of_set S). 
  if i+1 \<in> S' then w (i+1) else 0)"
    using *
    by presburger
  also have "... = (\<Sum>i < card S. (\<lambda>x. if x \<in> S' then w x else 0) (i+1) )"
    by fastforce
  also have "... = (\<Sum>x \<in> S. if x \<in> S' then w x else 0)"
    proof (cases "S = {}")
      case False
      with prems(2) have "S = {1..card S}"
        by force  
      then show ?thesis
        using sum.atLeast1_atMost_eq[of "(\<lambda>x. if x \<in> S' then w x else 0)" "card S"]
        by (metis (no_types, lifting) One_nat_def add.commute plus_1_eq_Suc sum.cong) 
    qed auto
  also have "... = sum w S'"
    using S'_def(1) prems(1) finite_subset
    by (smt (verit) DiffE sum.mono_neutral_cong_left)
  also have "... = B"
    using S'_def 
    by simp 
  finally have "(\<Sum>i < length ?as. ?as!i * ?xs!i) = B"
    by blast
  with xs_prop show ?thesis
    unfolding subset_sum_list_def
    by fastforce
qed 

lemma ss_indeces_to_ss_list_complete_aux:
assumes "finite S" "S = {1..card S}"  "(map w (sorted_list_of_set S), B) \<in> subset_sum_list"
shows "(S, w, B) \<in> subset_sum_indeces"
proof -
  let ?as = "map w (sorted_list_of_set S)"
  from assms(3) obtain xs where xs_def:
  "(\<forall>i<length xs. xs!i \<in> {0,1})" "(\<Sum>i<length ?as. ?as!i * xs!i) = B" "length xs = length ?as"
    unfolding subset_sum_list_def 
    by blast
  with assms(1) obtain S' where S'_def: "S' = {i \<in> S. xs!(i-1) = 1}"
    by blast
  hence "S' \<subseteq> S"
    by blast

   have *: "w x * (\<lambda>x. of_bool (x \<in> S')) x = (if x \<in> S' then w x else 0)" for x
    unfolding of_bool_def
    by auto
  have **:"(sorted_wrt (<) (sorted_list_of_set S))"
    by auto

  have "i < length (sorted_list_of_set S) \<longrightarrow> (sorted_list_of_set S)!i = i+1" for i 
    using list_indexing[OF **, of 0 i] assms(2)
    apply (cases "S = {}")
    using assms(1) by force+ 
  hence ***: "\<forall>i < length (sorted_list_of_set S). (sorted_list_of_set S)!i = i+1"
    by blast
  

  have ****: "xs = map (\<lambda>x. of_bool (x \<in> S')) (sorted_list_of_set S)"
    proof -
      let ?ys = "(sorted_list_of_set S)"
      let ?zs = "map (\<lambda>x. of_bool (x \<in> S')) (sorted_list_of_set S)"

      have "\<forall>i < length ?ys. ?ys ! i \<notin> S' \<longrightarrow> xs ! i \<noteq> 1"
        using S'_def *** assms(2) 
        by auto
      moreover have "\<forall>i < length ?ys. ?ys ! i \<in> S' \<longrightarrow> xs ! i = 1"
        using S'_def ***
        by simp
      ultimately have "\<forall>i < length ?ys. if ?ys ! i \<in> S' then xs ! i = 1 else xs ! i = 0"
        using xs_def(1, 3)
        by auto
      moreover have "\<forall>i < length ?ys. if ?ys ! i \<in> S' then ?zs ! i = 1 else ?zs ! i = 0"
        unfolding of_bool_def
        by force 
      ultimately have "\<forall>i < length ?ys. ?zs ! i = xs ! i"
        by auto 
      then show  "xs = ?zs"
        using xs_def(3) 
        by (simp add: nth_equalityI)
    qed 
  
  have "(\<Sum>i < length ?as. ?as!i * xs!i) 
    = (\<Sum>i < length (sorted_list_of_set S). ?as!i * xs!i)"
    by simp
  also have "... = (\<Sum>i < length (sorted_list_of_set S). 
    w ((sorted_list_of_set S)!i) * (\<lambda>x. of_bool (x \<in> S')) ((sorted_list_of_set S)!i))"
    using S'_def ****
    by auto
  also have "... = (\<Sum>i < length (sorted_list_of_set S). 
    w (i+1) * (\<lambda>x. of_bool (x \<in> S')) (i + 1))"
    using ***
    by fastforce
  also have "... = (\<Sum>i < length (sorted_list_of_set S). 
  if i+1 \<in> S' then w (i+1) else 0)"
    using *
    by presburger
  also have "... = (\<Sum>i < card S. (\<lambda>x. if x \<in> S' then w x else 0) (i+1) )"
    by fastforce
  also have "... = (\<Sum>x \<in> S. if x \<in> S' then w x else 0)"
    proof (cases "S = {}")
      case False
      with assms(2) have "S = {1..card S}"
        by force  
      then show ?thesis
        using sum.atLeast1_atMost_eq[of "(\<lambda>x. if x \<in> S' then w x else 0)" "card S"]
        by (metis (no_types, lifting) One_nat_def add.commute plus_1_eq_Suc sum.cong) 
    qed auto
  also have "... = sum w S'"
    using \<open>S' \<subseteq> S\<close> assms(1) finite_subset
    by (smt (verit) DiffE sum.mono_neutral_cong_left)
  finally have "sum w S' = B"
    using xs_def(2)
    by argo
  with assms(1-2) \<open>S' \<subseteq> S\<close> show ?thesis 
    unfolding subset_sum_indeces_def
    by auto
qed 

subsection "the summary"

lemma ss_to_ss_indeces_sound:
assumes "(S, w, B) \<in> subset_sum"
shows "ss_to_ss_indeces (S, w, B) \<in> subset_sum_indeces"
proof (cases "finite S")
  case True
  with assms show ?thesis
    unfolding ss_to_ss_indeces_def
    using ss_to_ss_indeces_sound_aux
    by auto
next
  case False
  with assms show ?thesis
    unfolding subset_sum_def 
    by blast
qed

lemma ss_to_ss_indeces_complete:
assumes "ss_to_ss_indeces (S, w, B) \<in> subset_sum_indeces"
shows "(S, w, B) \<in> subset_sum"
proof (cases "finite S")
  case True
  with assms show ?thesis
    unfolding ss_to_ss_indeces_def
    using ss_to_ss_indeces_complete_aux
    by auto
next
  case False
  with assms show ?thesis
    unfolding subset_sum_indeces_def ss_to_ss_indeces_def
    by auto
qed

theorem is_reduction_ss_to_ss_indeces:
"is_reduction ss_to_ss_indeces subset_sum subset_sum_indeces"
unfolding is_reduction_def
using ss_to_ss_indeces_sound ss_to_ss_indeces_complete
by fastforce

lemma ss_indeces_to_ss_list_sound:
assumes "(S, w, B) \<in> subset_sum_indeces"
shows "ss_indeces_to_ss_list (S, w, B) \<in> subset_sum_list"
proof (cases "finite S \<and> S = {1..card S}")
  case True
  from assms have "(S, w, B) \<in> subset_sum_indeces"
    unfolding subset_sum_indeces_def
    by auto
  hence "(S, \<lambda>x. w x, B) \<in> subset_sum_indeces"
    unfolding subset_sum_indeces_def 
    by auto
  hence "(map w (sorted_list_of_set S), B) \<in> subset_sum_list"
    using ss_indeces_to_ss_list_sound_aux[of S w B]
    by fastforce
  with True 
  show ?thesis  
    unfolding ss_indeces_to_ss_list_def 
    by auto
next
  case False
  from assms have "S = {} \<or> (finite S \<and> S = {1..card S})"
    unfolding subset_sum_indeces_def
    by force
  with False have "False"
    by fastforce
  then show ?thesis
    by blast
qed

lemma ss_indeces_to_ss_list_complete:
assumes "ss_indeces_to_ss_list (S, w, B) \<in> subset_sum_list" 
shows "(S, w, B) \<in> subset_sum_indeces"
proof (cases "finite S \<and> S = {1..card S}")
  case True
  with assms have "(S, w, B) \<in> subset_sum_indeces"
    using ss_indeces_to_ss_list_complete_aux
    unfolding ss_indeces_to_ss_list_def
    by simp
  then show ?thesis
    unfolding subset_sum_indeces_def
    by blast
next
  case False
  hence "ss_indeces_to_ss_list (S, w, B) = ([], 1)"
    unfolding ss_indeces_to_ss_list_def
    by auto
  moreover have "([], 1) \<notin> subset_sum_list"
    unfolding subset_sum_list_def
    by fastforce 
  ultimately show ?thesis
    using assms 
    by argo 
qed

theorem is_reduction_ss_indeces_to_ss_list:
"is_reduction ss_indeces_to_ss_list subset_sum_indeces subset_sum_list"
unfolding is_reduction_def 
using ss_indeces_to_ss_list_sound ss_indeces_to_ss_list_complete
unfolding comp_def 
by auto

end 