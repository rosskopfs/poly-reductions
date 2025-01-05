theory  XC_To_SS_aux
  imports "../SAT_To_XC/XC_Definition"
begin

section "subset sum"

definition is_subset_sum :: "'a set * ('a \<Rightarrow> nat) * nat \<Rightarrow> bool" where
"is_subset_sum SS \<equiv> 
  (case SS of (S, w, B) => (sum w S = B))"

definition "subset_sum \<equiv> {(S, w, B) | S w B. finite S \<and> (\<exists>S' \<subseteq> S. is_subset_sum (S', w, B))}"

definition "size_SS \<equiv> (\<lambda>(S, w, B). card S)"

definition "subset_sum_indeces \<equiv> {(S, w, B). finite S \<and> S = (if S = {} then {} else {1..card S}) \<and> (\<exists>S' \<subseteq> S. sum w S' = B)}"

definition "size_ss_indeces \<equiv> \<lambda>(S, w, B). card S + 2"

definition subset_sum_list :: "((nat list) * nat) set" where
  "subset_sum_list \<equiv> {(as,s). (\<exists>xs::nat list. 
    (\<forall>i<length xs. xs!i \<in> {0,1}) \<and> (\<Sum>i<length as. as!i * xs!i) = s \<and> length xs = length as)}"


definition"size_ss_list \<equiv> \<lambda>(as, s). length as + 1"

(*construction via a bijective function, a preliminary lemma that 
there is a bijective function from a finite set to a finite natural number interval
from 0 to the cardinality of the set*)

subsection "contruction of a bijective function"

find_theorems "\<exists>f. bij_betw f _ _"

lemma bij_exist: 
  "finite S \<Longrightarrow> \<exists>f. (if S = {} then bij_betw f S {} else bij_betw f S {1..card S})"
proof (induction S rule: finite_induct)
  case (insert x F)
  then obtain f where 
    f_def: "if F = {} then bij_betw f F {} else bij_betw f F {1..card F}"
    by blast
  then show ?case
  proof (cases "F = {}")
  case True
    then have "insert x F = {x}"
      by argo
    moreover with True have "card (insert x F) = 1"
      using card_insert_if[OF insert(1), of x]
      by fastforce
    ultimately have "bij_betw (f (x:=1)) (insert x F) {1..card (insert x F)}"
      unfolding bij_betw_def inj_on_def 
      by auto

    moreover from True f_def have "bij_betw f F {}"
      by argo
    ultimately show ?thesis 
      by auto
  next
    case False
    with f_def have "bij_betw f F {1..card F}"
      by argo
    hence "inj_on f F" "f ` F = {1..card F}"
      unfolding bij_betw_def 
      by blast+
    moreover from insert have "card (insert x F) = card F + 1"
      using card_insert_if[OF insert(1), of x]
      by force 
    ultimately have "f(x := card F + 1) ` insert x F = {1..card (insert x F)}"
      using insert(2) 
      apply (auto, force)
      by (metis atLeastAtMost_iff imageI le_Suc_eq)    
    moreover have "inj_on (f(x := card F + 1)) (insert x F)"
      using \<open>inj_on f F\<close> unfolding inj_on_def
      proof (safe, goal_cases)
        case (1 a b)
        from 1(3) insert(2) \<open>f ` F = {1..card F}\<close> 
        have "(f(x := card F + 1)) b \<in> {1..card F}"
          by auto
        with False have "(f(x := card F + 1)) b \<noteq> card F + 1"
          using card_0_eq[OF insert(1)]
          by auto 
        
        with 1(2) have "False"
          by force
        then show ?case
          by blast
      next
        case (2 a b)
        from 2(3) insert(2) \<open>f ` F = {1..card F}\<close> 
        have "(f(x := card F + 1)) a \<in> {1..card F}"
          by auto
        with False have "(f(x := card F + 1)) a \<noteq> card F + 1"
          using card_0_eq[OF insert(1)]
          by auto 
        
        with 2(2) have "False"
          by force
        then show ?case
          by blast
      next
        case (3 a b)
        from 3(3) 3(4) insert(2) have 
        "(f(x := card F + 1)) a = f a" "(f(x := card F + 1)) b = f b"
          by auto
        with 3 show ?case
          by metis
      qed

    ultimately have "bij_betw (f(x := card F + 1)) (insert x F) {1..card (insert x F)}"
      unfolding bij_betw_def
      by blast

    moreover from insert have "insert x F \<noteq> {}"
      by blast
    ultimately show ?thesis 
      by metis
  qed
qed (auto simp add: bij_betw_def inj_on_def)

(* moved from weight *)

definition "subset_sum_int_list \<equiv> {(as,s). (\<exists>xs::int list. 
    (\<forall>i<length xs. xs!i \<in> {0,1}) \<and> (\<Sum>i<length as. as!i * xs!i) = s \<and> length xs = length as)}"

definition "ss_lift_to_int \<equiv> (\<lambda>(as, s). ((map int as), int s))"

definition "size_ss_int_list \<equiv> \<lambda>(as, s). length as + 1"


subsection "a type lifting from natural numbers to integers for subset sum"

lemma subset_sum_nat_to_int_sound:
assumes "(as, s) \<in> subset_sum_list"
shows "(map int as, int s) \<in> subset_sum_int_list"
proof -
  from assms obtain xs where 
  "(\<forall>i<length xs. xs!i \<in> {0,1}) \<and> (\<Sum>i<length as. as!i * xs!i) = s \<and> length xs = length as"
    unfolding subset_sum_list_def
    by blast 
  hence "(\<forall>i<length (map int xs).(map int xs)! i \<in> {0,1}) 
    \<and> (\<Sum>i<length (map int as). (map int as)! i * (map int xs) ! i) = int s 
    \<and> length (map int xs) = length (map int as)"
    by force
  then show ?thesis
    unfolding subset_sum_int_list_def
    by blast
qed 

lemma subset_sum_nat_to_int_complete:
assumes "(map int as, int s) \<in> subset_sum_int_list"
shows "(as, s) \<in> subset_sum_list"
proof -
  from assms obtain xs where xs_def:
  "(\<forall>i<length xs. xs ! i \<in> {0,1})"
    "(\<Sum>i<length (map int as). (map int as)! i * xs ! i) = int s"
    "length xs = length (map int as)"
    unfolding subset_sum_int_list_def
    by fast 
  from this(1) have "\<exists>ys. map int ys = xs"
    proof (induction xs)
      case (Cons a xs)
      then obtain ys where "map int ys = xs"
        by fastforce 
      moreover from Cons(2) have "a = 1 \<or> a = 0"
        by auto
      ultimately have "map int ((if a = 1 then 1 :: nat else 0 )# ys) = a # xs"
        by fastforce
      then show ?case
        by metis
    qed simp
  then obtain ys where "map int ys = xs"
    by blast
  with xs_def have "(\<forall>i<length ys. ys! i \<in> {0,1}) 
    \<and> (\<Sum>i<length as. as! i * ys ! i) = s 
    \<and> length ys = length as"
    by (auto, smt (verit) of_nat_eq_iff of_nat_mult of_nat_sum sum.cong)
  then show ?thesis 
    unfolding subset_sum_list_def
    by blast
qed 

lemma is_reduction_ss_lift_to_int:
"is_reduction ss_lift_to_int subset_sum_list subset_sum_int_list"
  unfolding is_reduction_def ss_lift_to_int_def
  using subset_sum_nat_to_int_sound subset_sum_nat_to_int_complete
  by auto



section "the type lifting between definitions is polynomial"

definition "ss_lift_to_int_alg x \<equiv> 
  do {
    RETURNT (ss_lift_to_int x)
  }"

definition "ss_lift_to_int_space n = n"
definition "ss_lift_to_int_time n = n"

subsection "proof"

lemma ss_lift_to_int_size:
"size_ss_int_list (ss_lift_to_int x) \<le> ss_lift_to_int_space (size_ss_list x)"
by (auto simp add: size_ss_int_list_def ss_lift_to_int_def 
  ss_lift_to_int_space_def size_ss_list_def split: prod.splits)

lemma ss_lift_to_int_refines:
"ss_lift_to_int_alg x \<le> SPEC (\<lambda>y. y = ss_lift_to_int x) (\<lambda>_. ss_lift_to_int_time (size_ss_list x))"
unfolding SPEC_def 
unfolding ss_lift_to_int_alg_def ss_lift_to_int_def 
apply (rule T_specifies_I)
apply (vcg' \<open>-\<close> rules: T_SPEC)
by auto

theorem ss_lift_to_int_is_polyred:
  "ispolyred ss_lift_to_int_alg subset_sum_list subset_sum_int_list size_ss_list size_ss_int_list"
unfolding ispolyred_def
  apply (rule exI[where x=ss_lift_to_int])
  apply (rule exI[where x=ss_lift_to_int_time])
  apply (rule exI[where x=ss_lift_to_int_space])
  apply safe
  subgoal
    using ss_lift_to_int_refines 
    by blast 
  subgoal 
    using ss_lift_to_int_size 
    by blast 
  subgoal 
    unfolding poly_def ss_lift_to_int_time_def 
    apply (intro exI[where x=2])
    by auto 
  subgoal 
    unfolding poly_def ss_lift_to_int_space_def 
    apply (intro exI[where x=2])
    by auto 
  subgoal 
    using is_reduction_ss_lift_to_int
    by blast 
  done 



end 