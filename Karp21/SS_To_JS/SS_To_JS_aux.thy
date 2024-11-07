theory  SS_To_JS_aux
  imports Main  "HOL-Combinatorics.List_Permutation"  "../XC_To_SS/XC_To_SS_aux" 

begin

(* defintion from karp 1972 *)
definition job_sequencing :: "((nat list) * (nat list) * (nat list) * nat) set" where
  "job_sequencing \<equiv> {(Ts, Ds, Ps, k). (length Ts = length Ds) \<and> (length Ts = length Ps) \<and>
    (\<exists>\<pi>::nat list. 
      (perm \<pi> [0..<length Ts])  \<and>
      (\<Sum>j<length Ts. (if (\<Sum>i<j+1. Ts!(\<pi>!i)) > Ds!(\<pi>!j) 
         then Ps!(\<pi>!j) 
         else 0)) \<le>  k)}"


lemma job_seq_cert:
  assumes "perm \<pi> [0..<length Ts]"
    "(length Ts = length Ds) \<and> (length Ts = length Ps)"
    "(\<Sum>j<length Ts. (if (\<Sum>i<j+1. Ts!(\<pi>!i)) > Ds!(\<pi>!j) 
         then Ps!(\<pi>!j) 
         else 0)) \<le> k"
  shows "(Ts, Ds, Ps, k) \<in> job_sequencing"
  using SS_To_JS_aux.job_sequencing_def assms by blast

lemma subset_sum_list_cert:
  assumes "(\<forall>i<length xs. xs!i \<in> {0,1})"
          "(\<Sum>i<length as. as!i * xs!i) = s"
          "length xs = length as"
  shows "(as,s)\<in> subset_sum_list"
  using subset_sum_list_def assms by blast


(* reduction *)

definition NOT_JOB_SEQ_EXAMPLE :: "nat list \<times> nat list \<times> nat list \<times> nat" where
  "NOT_JOB_SEQ_EXAMPLE \<equiv> ([1], [0], [1], 0)"

definition ss_list_to_job_seq :: "nat list \<times> nat \<Rightarrow> nat list \<times> nat list \<times> nat list \<times> nat" where
  "ss_list_to_job_seq \<equiv> \<lambda>(ws, B). (if sum_list ws \<ge> B then 
             (ws, replicate (length ws) B, ws, (sum_list ws - B))
            else NOT_JOB_SEQ_EXAMPLE)"

lemma example_not_in_job_sequencing:
  "NOT_JOB_SEQ_EXAMPLE \<notin> job_sequencing"
  unfolding NOT_JOB_SEQ_EXAMPLE_def
proof
  assume "([1], [0], [1], 0) \<in> job_sequencing"
  then obtain \<pi> where
    "perm \<pi> [0..<1]"
    and "(\<Sum>j<length [1]. (if (\<Sum>i<j+1. [1]!(\<pi>!i)) > [0::nat]!(\<pi>!j)
             then [1]!(\<pi>!j) else 0)) \<le> (0::nat)" 
     unfolding job_sequencing_def by auto
  then have "(1::nat) < 0" by auto
  then show False by simp
qed


(* helper lemmas *)
lemma sum_nth_sum_set:
  fixes f::"nat\<Rightarrow>nat"
  shows "distinct xs \<Longrightarrow> (\<Sum>i<length xs. f (xs!i)) = (\<Sum>i \<in> set xs.  f i)"
  by (simp add: bij_betw_nth sum.reindex_bij_betw)

lemma sum_lt_split:
  fixes f::"nat\<Rightarrow>nat"
  assumes "a \<le> b"
  shows  "(\<Sum>i<b. f i) = (\<Sum>i<a. f i) + (\<Sum>i=a..<b. f i)"
  using sum.atLeastLessThan_concat[OF le0 assms,of f, symmetric]
        lessThan_atLeast0 by presburger

lemma nth_append_in_set:
  "i \<ge> length xs \<and> i < length (xs@ys) \<Longrightarrow> (xs@ys)!i \<in> set ys"
  by (metis append_eq_conv_conj in_set_drop_conv_nth)

(* there exists a solution that chooses all zero elements *)
lemma subset_solution_with_zeros:
  assumes "(ws, B) \<in> subset_sum_list"
  shows "\<exists>xs. 
          length xs = length ws \<and>
          (\<forall>i < length xs. xs!i \<in> {0, 1}) \<and>
          ((\<Sum>i<length ws. ws!i * xs!i) = B) \<and>
          (\<forall>i. i <length ws \<and> xs!i = 0 \<longrightarrow> ws!i > 0)"
proof -
  from assms obtain xs_orig where
    xs_orig_def: "length xs_orig = length ws"
                 "\<forall>i<length xs_orig. xs_orig!i \<in> {0, 1}"
                 "(\<Sum>i<length ws. ws!i * xs_orig!i) = B"
    unfolding subset_sum_list_def by blast

  define xs where "xs \<equiv> map (\<lambda>i. if ws!i = 0 then 1 else xs_orig!i) [0..<length ws]"

  have xs_length: "length xs = length ws"
    by (simp add: xs_def)

  moreover have xs_is_choice_vector: "\<forall>i<length xs. xs!i \<in> {0, 1}"
    using xs_def xs_orig_def by auto

  moreover have xs_subset_sum: "(\<Sum>i<length ws. ws!i * xs!i) = B"
  proof -
    have "(\<Sum>i<length ws. ws!i * xs!i) =
            (\<Sum>i<length ws. ws!i * (if ws!i = 0 then 1 else xs_orig!i))"
      by (intro sum.cong, simp, simp add: xs_def)
    also have "... = (\<Sum>i<length ws. ws!i * xs_orig!i)"
      by (intro sum.cong) auto
    finally show ?thesis  using xs_orig_def(3) by simp
  qed

  moreover have xs_zero_implies_ws_pos: "\<forall>i. i <length ws \<and> xs!i = 0 \<longrightarrow> ws!i > 0"
   using xs_def zero_neq_one by fastforce
  ultimately show ?thesis  by blast
qed

lemma total_sum_ge_goal:
  assumes "(ws,B) \<in> subset_sum_list"
  shows "sum_list ws \<ge> B"
proof -
  from assms obtain xs where
    xs_orig_def: "length xs = length ws"
                 "\<forall>i<length xs. xs!i \<in> {0, 1}"
                 "(\<Sum>i<length ws. ws!i * xs!i) = B"
    unfolding subset_sum_list_def by blast
  have "(\<Sum>i<length ws. ws!i) \<ge> (\<Sum>i<length ws. ws!i * xs!i)"
    using xs_orig_def by (intro sum_mono) fastforce
  then show ?thesis by (simp add: atLeast0LessThan sum_list_sum_nth xs_orig_def)
qed


lemma nth_injective_permutation:
  assumes "perm \<pi> [0..<k]"
  shows  "inj_on ((!) \<pi>)  {..<k}"
  unfolding inj_on_def
  using distinct_upt perm_distinct_iff assms
  by (metis diff_zero distinct_Ex1 length_upt lessThan_iff nth_mem size_mset)

lemma sum_perm_sum_list:
  assumes "perm \<pi> [0..<length xs]"
  shows "(\<Sum>j<length xs. xs!(\<pi>!j)) = sum_list xs"
proof -
  have set_pi:  "{..<length xs} = set \<pi>"
    using atLeastLessThan_upt perm_set_eq assms atLeast_upt by blast
  have length_pi: "length xs = length \<pi>"
    by (metis assms diff_zero length_upt size_mset)
  have "sum_list xs = (\<Sum>j<length xs. xs!j)"
    by (simp add: lessThan_atLeast0 sum.list_conv_set_nth)
  also have "... = (\<Sum>j<length xs. xs!(\<pi>!j))"
  proof (intro sum.reindex_cong[of "((!)\<pi>)"])
    show "inj_on ((!) \<pi>) {..<length xs}"   using assms nth_injective_permutation by blast
    show "{..<length xs} = (!) \<pi> ` {..<length xs}" using nth_image_indices
      by (subst set_pi, subst length_pi, subst atLeast0LessThan[of "length \<pi>", symmetric], auto)
    show "\<And>x. x \<in> {..<length xs} \<Longrightarrow> xs ! (\<pi> ! x) = xs ! (\<pi> ! x)" by auto
  qed
  finally show ?thesis by auto
qed

lemma nth_perm_less_less:
  assumes "perm \<pi> [0..<k]"
  shows "j < k \<Longrightarrow> \<pi> ! j < k"
  by (metis assms atLeastLessThan_iff length_upt minus_nat.diff_0 nth_mem 
      set_mset_mset set_upt size_mset)

(* proof *)
lemma ss_list_to_job_seq_sound:
  assumes "(ws, B) \<in> subset_sum_list"
  shows "ss_list_to_job_seq (ws, B) \<in> job_sequencing"
proof -
 
  from subset_solution_with_zeros[OF assms] obtain xs where
         xs_length: "length xs = length ws"
    and  xs_is_choice_vector: "\<forall>i<length xs. xs!i \<in> {0, 1}"
    and  xs_subset_sum: "(\<Sum>i<length ws. ws!i * xs!i) = B" 
    and  zeros_chosen: "\<forall>i. i <length ws \<and> xs!i = 0 \<longrightarrow> ws!i > 0"
    by blast

 (* job_sequencing: task times, penalties, and deadlines using ws and B *)
  let ?Ts = "ws"
  let ?Ps = "ws"
  let ?Ds = "replicate (length ws) B"
  let ?chosen = "[i \<leftarrow> [0..<length ws]. xs!i = 1]"
  let ?non_chosen = "[i \<leftarrow> [0..<length ws]. xs!i = 0]"
  let ?\<pi> = "?chosen @ ?non_chosen"
  let ?k = "(sum_list ws - B)"

  (* properties of \<pi> *)
  have "distinct ?\<pi>"  by fastforce
  moreover have pi_set: "set ?\<pi> = set [0..<length ?Ts]" using xs_length xs_is_choice_vector
    using not_less_eq by (auto,blast)
  ultimately have pi_perm: "perm ?\<pi> [0..<length ?Ts]" using distinct_upt set_eq_iff_mset_eq_distinct 
    by blast
  have same_length: "length ?\<pi> = length ?Ts" 
    using perm_length[OF pi_perm] length_upt[of "0" "length ?Ts"] 
    by presburger

  (* sum of penalties for \<pi> is at most k *) 
  moreover have sum_le_k: "(\<Sum>j<length ?Ts. (if (\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j)
                                             then ?Ps!(?\<pi>!j) else 0)) \<le>  ?k"
  proof -
    (* we show that the chosen jobs have total penalty 0 because they sum to the deadline B
       while the rest cause a total penalty of exactly k *)
    let ?n1 = "length ?chosen"
    have n1_small: "?n1 \<le> length ws" 
      by (metis diff_le_self le_trans length_filter_le length_upt)
    
    have all_deadlines_B: "?Ds!(?\<pi>!j) = B" if "j < length ?Ts" for j
      using that nth_perm_less_less[OF pi_perm] by (intro List.nth_replicate)

    have sum_chosen: "(\<Sum>i<?n1. ?Ts!(?\<pi>!i)) = B"
    proof -
      have "(\<Sum>i\<in>set ?chosen. ws!i) = (\<Sum>i<length ws. if xs!i = 1 then ws!i else 0)"
        using sum.inter_filter[of "{..<length ws}"] by auto
      also have "... = (\<Sum>i<length ws. ws!i * xs!i)"
        using xs_is_choice_vector xs_length by (intro sum.cong) auto
      finally show ?thesis using xs_subset_sum sum_nth_sum_set by auto
    qed

    (* chosen jobs do not cause a penalty *)
    have sum_penalties_chosen: "(\<Sum>j<?n1. (if (\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j)
             then ?Ps!(?\<pi>!j)
             else 0)) = 0"
      apply (intro sum.neutral ballI if_not_P, simp only: lessThan_iff) subgoal for x
      using all_deadlines_B[of x] n1_small sum_chosen 
            sum_lt_split[of "x+1" "?n1" "\<lambda>i. ?Ts!(?\<pi>!i)"]    
      by linarith.
                           
    (* every non_chosen job exceeds the deadline *)
    moreover have overdue: "(\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j)" 
                  if j_leq_len: "j < length ?Ts" and "j \<ge> ?n1" for j
    proof -
      have "?Ts!(?\<pi>!i) > 0" if "i \<in> {?n1..j}" for i 
      proof - 
        from that have i_bound: "?n1 \<le> i \<and> i < length ?Ts" 
          by (meson atLeastAtMost_iff j_leq_len order.strict_trans1)
        then have "(?\<pi> ! i) \<in> set ?non_chosen" 
          using nth_append_in_set[of "?chosen"] same_length by presburger
        then have "xs!(?\<pi> ! i) = 0" by (simp add: xs_length)
        thus ?thesis using i_bound nth_perm_less_less[OF pi_perm] zeros_chosen by blast
      qed
      then have "(\<Sum>i=?n1..<j+1. ?Ts!(?\<pi>!i)) > 0"
        using sum_pos[of "{?n1..j}" "\<lambda>i. ?Ts!(?\<pi>!i)"] that by fastforce
      thus ?thesis using sum_lt_split[of "?n1" "j + 1"] that(2) trans_le_add1
        by (subst all_deadlines_B[OF that(1)], subst sum_chosen[symmetric], presburger)
    qed
    
    (* therefore the non-chosen jobs cause penalty k *)
    moreover have "(\<Sum>j = ?n1..<length ?Ts. (if (\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j)
                                             then ?Ps!(?\<pi>!j) else 0)) = ?k"
     using overdue sum.ivl_cong[of "?n1" "?n1" "length ?Ts" "length ?Ts"
                              "\<lambda>j. (if (\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j) then ?Ps!(?\<pi>!j) else 0)"
                              "\<lambda>j. ?Ps!(?\<pi>!j)"]  
           sum_lt_split n1_small sum_chosen sum_perm_sum_list[OF pi_perm]
     by presburger
  
    ultimately show ?thesis using sum_lt_split n1_small by presburger
  qed
  ultimately show ?thesis unfolding ss_list_to_job_seq_def
    using job_seq_cert[OF pi_perm] assms total_sum_ge_goal by auto
qed

(* complete *)
lemma ss_list_to_job_seq_complete:
  assumes "ss_list_to_job_seq(ws,B) \<in> job_sequencing"
  shows "(ws, B) \<in> subset_sum_list"
proof (cases "sum_list ws \<ge> B")
  case False
  then show ?thesis  using assms example_not_in_job_sequencing
    by (simp add: ss_list_to_job_seq_def)
next
  case True
  from assms True obtain \<pi> C where
    \<pi>_perm: "perm \<pi> [0..<length ws]"
    and C_def: "C = (\<lambda>j. (\<Sum>i < j + 1. ws!(\<pi>!i)))" 
    and total_penalty: "(\<Sum>j<length ws. (if C j > (replicate (length ws) B)!(\<pi>!j) then ws!(\<pi>!j) else 0)) 
                        \<le> (sum_list ws - B)"
    and len_eq: "length ws = length ws \<and> length ws = length ws"
    unfolding job_sequencing_def ss_list_to_job_seq_def 
    by auto

  define EARLY where "EARLY = {j. j < length ws \<and> C j \<le> B}"
  define LATE  where "LATE = {j. j < length ws \<and> C j > B}"
  have C_leq: "C j = (\<Sum>i \<le>j. ws!(\<pi>!i))" for j 
    unfolding C_def by (intro sum.cong) auto
  have C_increasing: "\<And>i j. i \<le> j \<and> j < length ws \<longrightarrow> C i \<le> C j"
     by (simp add: sum_mono2 C_leq)

  have sum_early_le_B: "(\<Sum>j\<in>EARLY. ws!(\<pi>!j)) \<le> B"
  proof (cases "EARLY = {}")
    case True
    then show ?thesis by auto
  next
    case False
    thm Max_in
    have "Max EARLY \<in> EARLY" using False EARLY_def 
      by (intro Max_in) fast 
    moreover then have "EARLY = {j. j \<le> Max EARLY}"
      using C_increasing EARLY_def by fastforce
    ultimately show ?thesis using C_increasing EARLY_def by (auto simp add: C_leq atMost_def)
  qed

  moreover have "sum_list ws = (\<Sum>j\<in>EARLY. ws!(\<pi>!j)) + (\<Sum>j\<in>LATE. ws!(\<pi>!j))"
  proof -
    have "sum_list ws = (\<Sum>j<length ws. ws!(\<pi>!j))"  using sum_perm_sum_list[OF \<pi>_perm] by presburger
    moreover have "EARLY \<union> LATE = {j. j < length ws}" and "EARLY \<inter> LATE = {}" 
      using EARLY_def LATE_def by auto      
    ultimately show ?thesis by (simp add: lessThan_def sum_Un_eq)
  qed

  moreover have "(\<Sum>j\<in>LATE. ws!(\<pi>!j)) \<le> sum_list ws - B"
  proof -
    have "(replicate (length ws) B) !(\<pi>!j) = B" if "j < length ws" for j 
      using nth_perm_less_less[OF \<pi>_perm that] by (intro List.nth_replicate)
    then show ?thesis using LATE_def total_penalty
       sum.inter_filter[of "{..<length ws}" "\<lambda>j. ws!(\<pi>!j)"]  by force
  qed

  ultimately have sum_early_eq_B: "(\<Sum>j\<in>EARLY. ws!(\<pi>!j)) = B" using True 
    by linarith
    
  define S where "S = ((!) \<pi>) ` EARLY"

  have S_subset: "S \<subseteq> {..<length ws}"
    using nth_perm_less_less[OF \<pi>_perm]
    unfolding S_def EARLY_def by blast
  
  have sum_S_eq_B: "(\<Sum>j\<in>S. ws!j) = B"
  proof -
    have "inj_on ((!) \<pi>) EARLY"
      using nth_injective_permutation[OF \<pi>_perm] unfolding EARLY_def
      by (simp add: Collect_mono inj_on_subset lessThan_def)
    then have "(\<Sum>j\<in>S. ws!j) = (\<Sum>j\<in>EARLY. ws!(\<pi>!j))" using S_def
      by (intro sum.reindex_cong[of "((!) \<pi>)"])  auto
    then show ?thesis using sum_early_eq_B   by blast
  qed

  define xs where "xs = map (\<lambda>i. if i \<in> S then (1::nat) else 0) [0..<length ws]"
  show ?thesis 
  proof (rule subset_sum_list_cert[of xs])
    show "length xs = length ws" by (simp add: xs_def)
    show  "\<forall>i<length xs. xs!i \<in> {0, 1}"  using xs_def by auto
    show "(\<Sum>i<length ws. ws!i * xs!i) = B"
    proof -
     have "(\<Sum>i<length ws. ws!i * xs!i) = (\<Sum>i<length ws. if i \<in> S then ws!i else 0)"
        using xs_def by (intro sum.cong) auto
     also have "... =  sum ((!) ws) {x \<in> {..<length ws}. x \<in> S}" 
        using  sum.inter_filter[of "{..<length ws}" "(!) ws"] by auto
     also have "... = (\<Sum>i\<in>S. ws!i)"  using S_subset by (intro sum.cong) auto
     finally show ?thesis using sum_S_eq_B  by blast
   qed
  qed
qed

theorem is_reduction_ss_list_to_job_seq:
  "is_reduction ss_list_to_job_seq subset_sum_list job_sequencing"
  unfolding is_reduction_def 
  using ss_list_to_job_seq_sound ss_list_to_job_seq_complete
  by auto
end