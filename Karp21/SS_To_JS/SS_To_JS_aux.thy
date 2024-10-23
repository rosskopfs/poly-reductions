theory  SS_To_JS_aux
  imports Main  "HOL-Combinatorics.List_Permutation"  "../XC_To_SS/XC_To_SS_aux" 

begin


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
 using SS_To_JS_aux.job_sequencing_def assms(1,2,3) by blast

lemma subset_sum_list_cert:
  assumes "(\<forall>i<length xs. xs!i \<in> {0,1})"
          "(\<Sum>i<length as. as!i * xs!i) = s"
          "length xs = length as"
        shows "(as,s)\<in> subset_sum_list"
  using subset_sum_list_def assms(1,2,3) by blast


(* reduction *)
definition ss_list_to_job_seq :: "nat list \<times> nat \<Rightarrow> nat list \<times> nat list \<times> nat list \<times> nat" where
  "ss_list_to_job_seq \<equiv> \<lambda>(ws, B). (if sum_list ws \<ge> B then 
             (ws, replicate (length ws) B, ws, (sum_list ws - B))
            else ([1],[0],[1],0))"



(* helper lemmas *)
lemma sum_nth_sum_set:
  fixes f::"nat\<Rightarrow>nat"
  shows "distinct xs \<Longrightarrow> (\<Sum>i<length xs. f (xs!i)) = (\<Sum>i \<in> set xs.  f i)"
  by (simp add: bij_betw_nth sum.reindex_bij_betw)

lemma nth_append_in_set:
  "i \<ge> length xs \<and> i < length (xs@ys) \<Longrightarrow> (xs@ys)!i \<in> set ys"
  by (metis append_eq_conv_conj in_set_drop_conv_nth)

lemma sum_nth_sum_set_append:
  fixes f::"nat \<Rightarrow> nat"
  assumes "distinct ys"
  shows "(\<Sum>i=length xs..<length (xs @ ys). f ((xs @ ys)!i)) = (\<Sum>i \<in> set ys. f i)"
proof -
  have "(\<Sum>i=length xs..<length ys  + length xs. f ((xs@ys)!i)) = 
             (\<Sum>i=0..< length ys. f ((xs@ys)!(i+length xs))) "
    using sum.shift_bounds_nat_ivl[of "\<lambda>i. f ((xs@ys)!i)" "0" "length xs" "length ys"]
    by simp
  also have "\<dots> = (\<Sum>j=0..<length ys. f (ys!j))"
    by (metis add.commute nth_append_length_plus)
  also have "\<dots> = sum_list (map f ys)"
    by (simp add: assms atLeast0LessThan sum_list_distinct_conv_sum_set sum_nth_sum_set)
  also have "\<dots> = (\<Sum> x \<in> set ys. f x)"
    using assms sum_list_distinct_conv_sum_set by blast
  finally show ?thesis   by (simp add: add.commute)
qed


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

  (* Define xs where xs!i = if ws!i = 0 then 1 else xs_orig!i *)
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
    proof -
      have "ws!i * (if ws!i = 0 then 1 else xs_orig!i) = ws!i * xs_orig!i" for i
        by (cases "ws!i = 0") auto
      then show ?thesis by (intro sum.cong) auto
    qed
    also have "... = B"
      using xs_orig_def(3) by simp
    finally show ?thesis .
  qed

  moreover have xs_zero_implies_ws_pos: "\<forall>i. i <length ws \<and> xs!i = 0 \<longrightarrow> ws!i > 0"
   using xs_def zero_neq_one by fastforce
  ultimately show ?thesis
    by blast
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
  have "sum_list ws = (\<Sum>i<length ws. ws!i)"
    by (simp add: atLeast0LessThan sum_list_sum_nth)
  also have  "... \<ge> (\<Sum>i<length ws. ws!i * xs!i)"
     using xs_orig_def by (intro sum_mono) fastforce
  finally show ?thesis using xs_orig_def by auto
qed


lemma example_not_in_job_sequencing:
  "([1::nat], [0::nat], [1::nat], 0) \<notin> job_sequencing"
proof
  assume js: "([1], [0], [1], 0) \<in> job_sequencing"
  then have ex_\<pi>: "\<exists>\<pi>. perm \<pi> [0..<length [1]] \<and> (\<Sum>j<length [1::nat]. (if (\<Sum>i<j+1. [1::nat]!(\<pi>!i)) > [0]!(\<pi>!j)
             then [1::nat]!(\<pi>!j)
             else 0)) \<le> 0"
    unfolding job_sequencing_def by auto
   from ex_\<pi> obtain \<pi> where
    \<pi>_perm: "perm \<pi> [0..<1]"
    and total_penalty: "(\<Sum>j<length [1]. (if (\<Sum>i<j+1. [1]!(\<pi>!i)) > [0::nat]!(\<pi>!j)
             then [1::nat]!(\<pi>!j)
             else 0)) \<le> (0::nat)" 
    by auto
   from \<pi>_perm have "\<pi> = [0]"
    by simp
   have "(\<Sum>j<length [1]. (if (\<Sum>i<j+1. [1::nat]!(\<pi>!i)) > [0::nat]!(\<pi>!j)
             then [1::nat]!(\<pi>!j)
             else (0::nat))) =   (if (\<Sum>i<0+1. [1::nat]!(\<pi>!i)) > [0::nat]!(\<pi>!0)
             then [1::nat]!(\<pi>!0)
             else (0::nat))"
     by auto
   also have  "... = (if (\<Sum>i<0+1. [1::nat]!([0]!i)) > [0::nat]!([0]!0)
             then [1::nat]!([0]!0)
             else (0::nat))" 
     using \<open>\<pi> = [0]\<close> by blast
   also have "... = (1::nat)"   by simp
   finally have "1 \<le> (0::nat)" using total_penalty 
   by (metis (mono_tags, lifting))
    then show False  by simp
qed

lemma nth_injective_permutation:
  assumes "perm \<pi> [0..<k]"
  shows  "inj_on ((!) \<pi>)  {..<k}"
proof
  fix i j
  assume "i \<in> {..<k}" and "j \<in> {..<k}" and "\<pi> ! i = \<pi> ! j"
  moreover from `perm \<pi> [0..<k]`  have "distinct \<pi>"
    using distinct_upt perm_distinct_iff by blast 
  ultimately have "i = j"
     by (metis assms diff_zero distinct_Ex1 length_upt lessThan_iff nth_mem size_mset)
  thus "i = j" by simp
qed

lemma sum_perm_sum_list:
  assumes "perm \<pi> [0..<length xs]"
  shows "(\<Sum>j<length xs. xs!(\<pi>!j)) = sum_list xs"
proof -
  have set_pi: "set \<pi> =  {..<length xs}"
    using atLeastLessThan_upt perm_set_eq assms atLeast_upt by blast
  have length_pi: "length \<pi>  = length xs"
    by (metis assms diff_zero length_upt size_mset)
  have "sum_list xs = (\<Sum>j<length xs. xs!j)"
    by (simp add: lessThan_atLeast0 sum.list_conv_set_nth)
  also have "... = (\<Sum>j<length xs. xs!(\<pi>!j))"
  proof (intro sum.reindex_cong[of "((!)\<pi>)"])
    show "inj_on ((!) \<pi>) {..<length xs}"   using assms nth_injective_permutation by blast
    have " {..<length xs} = (!) \<pi> ` {0..<length \<pi>}"
      using  nth_image_indices  set_pi by auto
    also have "... = (!) \<pi> ` {..<length \<pi>}" 
      using arg_cong[OF atLeast0LessThan] by blast
    finally show  "{..<length xs} = (!) \<pi> ` {..<length xs}" using length_pi by auto
    then show "\<And>x. x \<in> {..<length xs} \<Longrightarrow> xs ! (\<pi> ! x) = xs ! (\<pi> ! x)" by auto
  qed
  finally show ?thesis by auto
qed


(* proof *)
lemma ss_list_to_job_seq_sound:
  assumes "(ws, B) \<in> subset_sum_list"
  shows "ss_list_to_job_seq (ws, B) \<in> job_sequencing"
proof -
 
  from subset_solution_with_zeros[OF assms] obtain xs where
           xs_length: "length xs = length ws"
          and xs_is_choice_vector: "\<forall>i<length xs. xs!i \<in> {0, 1}"
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
  have "distinct ?\<pi>" by auto
  moreover have pi_set: "set ?\<pi> = set [0..<length ?Ts]" using xs_length xs_is_choice_vector
    using not_less_eq by (auto,blast)
  ultimately have pi_perm: "perm ?\<pi> [0..<length ?Ts]" using distinct_upt set_eq_iff_mset_eq_distinct 
    by blast
  have same_length: "length ?\<pi> = length [0..<length ?Ts]" 
    using perm_length pi_perm by blast
  have pi_index: "\<And>j. j < length ws \<Longrightarrow> ?\<pi> ! j < length ws"
    by (metis atLeastLessThan_iff diff_zero length_upt nth_mem pi_set same_length set_upt)

  (* sum of penalties for \<pi> is at most k *) 
  moreover have sum_le_k: "(\<Sum>j<length ?Ts. (if (\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j)
             then ?Ps!(?\<pi>!j)
             else 0)) \<le>  ?k"
  proof -
    (* we show that the chosen elements have total penalty 0 while the 
      rest cause a total penalty of exactly k *)
    let ?n1 = "length ?chosen"
    have n1_small: "?n1 \<le> length ws" 
      by (metis diff_le_self le_trans length_filter_le length_upt)
    
    have all_deadlines_B: "\<And>j. j <  length ?Ts \<Longrightarrow> ?Ds!(?\<pi>!j) = B"
      using pi_index  by (intro List.nth_replicate)

    have sum_chosen_set: "(\<Sum>i\<in>set ?chosen. ws!i) = B"
    proof -
      have "(\<Sum>i\<in>set ?chosen. ws!i) = (\<Sum>i<length ws. if xs!i = 1 then ws!i else 0)"
        using sum.inter_filter[of "{..<length ws}"] by auto
      also have "... = (\<Sum>i<length ws. ws!i * xs!i)"
        using xs_is_choice_vector xs_length by (intro sum.cong) auto
      finally show ?thesis using xs_subset_sum by presburger
    qed
    then have sum_chosen: "(\<Sum>i<?n1. ?Ts!(?\<pi>!i)) =  B"
      using sum_nth_sum_set  by auto


    have sum_penalties_chosen: "(\<Sum>j<?n1. (if (\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j)
             then ?Ps!(?\<pi>!j)
             else 0)) = 0"
    proof -
       have "\<And>j. j < ?n1 \<Longrightarrow> (\<Sum>i \<le> j. ?Ts ! (?\<pi> ! i)) \<le>  ?Ds!(?\<pi>!j)"
       proof -
         fix j assume j_chosen: "j < ?n1"
         then have "(\<Sum>i \<le> j. ?Ts ! (?\<pi> ! i)) \<le> (\<Sum>i < ?n1. ?Ts ! (?\<pi> ! i))"
           by (meson Iic_subset_Iio_iff bot_nat_0.extremum finite_lessThan sum_mono2)
         then have "(\<Sum>i \<le> j. ?Ts ! (?\<pi> ! i)) \<le> B" using sum_chosen by auto
         then show "(\<Sum>i \<le> j. ?Ts ! (?\<pi> ! i)) \<le>  ?Ds!(?\<pi>!j)" 
           using all_deadlines_B 
           by (metis (no_types, lifting) j_chosen n1_small order_less_le_trans)
       qed
       then have "\<And>j. j < ?n1 \<Longrightarrow>  (if (\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j)
             then ?Ps!(?\<pi>!j)
             else 0) = 0"
         by (metis Suc_eq_plus1 lessThan_Suc_atMost linorder_not_less)
       then show ?thesis by fastforce
     qed

    (* all non_chosen jobs have strictly positive job durations *) 
    have geq_n1_strict_pos: "\<And>j. j < length ?Ts \<and> j \<ge> ?n1 \<Longrightarrow>
                                 ?Ts ! (?\<pi> ! j) > 0"
    proof -
      fix j assume j_bound: "j < length ?Ts \<and> j \<ge> ?n1"
      then have j_non_chosen: "(?\<pi> ! j) \<in> set ?non_chosen" using nth_append_in_set same_length
        by (metis diff_zero length_upt)
      then have "xs!(?\<pi> ! j) = 0" by (simp add: xs_length)
      thus "?Ts ! (?\<pi> ! j) > 0" using  j_bound pi_index zeros_chosen by blast
    qed
    (* every non_chosen job exceeds the deadline *)
    moreover have overdew:"\<And>j. j < length ?Ts \<and> j \<ge> ?n1 \<Longrightarrow> (\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j)"
    proof -
      fix j assume j_bound: "j < length ?Ts \<and> j \<ge> ?n1"
      then have "(\<Sum>i<j+1. ?Ts!(?\<pi>!i)) = (\<Sum>i<?n1. ?Ts!(?\<pi>!i)) + (\<Sum>i=?n1..j. ?Ts!(?\<pi>!i))"
        using sum.atLeastLessThan_concat
        by (metis Suc_eq_plus1 atLeast0LessThan atLeastAtMost_upt le0 le_SucI set_upt)
      moreover have "(\<Sum>i=?n1..j. ?Ts!(?\<pi>!i)) > 0"
      proof -
        have "\<And>i. i \<in> {?n1..j} \<Longrightarrow> ?Ts!(?\<pi>!i) > 0"
          using j_bound geq_n1_strict_pos by simp
        thus ?thesis 
           using sum_pos[of "{?n1..j}" "\<lambda>i. ?Ts!(?\<pi>!i)"] j_bound  by fastforce
       qed
      ultimately have "(\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > (\<Sum>i<?n1. ?Ts!(?\<pi>!i))"
        by linarith
      then show "(\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j)" using sum_chosen all_deadlines_B j_bound by presburger
    qed


    moreover have sum_penalties_non_chosen: "(\<Sum>j = ?n1..<length ?Ts. (if (\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j)
             then ?Ps!(?\<pi>!j)
             else 0))=  ?k"
    proof -
      have "(\<Sum>j = ?n1..<length ?Ts. (if (\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j)
             then ?Ps!(?\<pi>!j)
             else 0)) = (\<Sum>j = ?n1..<length ?Ts. ?Ps!(?\<pi>!j))"  
        using sum.ivl_cong overdew   by force
      also have "... =  (\<Sum>i\<in>set ?non_chosen. ws!i)"
        using sum_nth_sum_set_append[of "?non_chosen"]
        by (metis List.distinct_filter distinct_upt length_map map_nth same_length)
      moreover have "... = (sum_list ws - B)"
      proof -
        have "sum_list ws = (\<Sum>i\<in>set ?chosen. ws!i) + (\<Sum>i\<in>set ?non_chosen. ws!i)"
          by (metis (no_types, lifting) \<open>distinct ?\<pi>\<close> \<open>set ?\<pi> = set [0..<length ws]\<close> distinct_filter distinct_upt  map_append map_nth sum_list_append sum_list_distinct_conv_sum_set)
        then have "sum_list ws - B = (\<Sum>i\<in>set ?non_chosen. ws!i)" using sum_chosen_set by arith
        thus ?thesis by presburger
      qed
      then show ?thesis using calculation by presburger
    qed
    moreover have "(\<Sum>j<length ?Ts. (if (\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j)
             then ?Ps!(?\<pi>!j)
             else 0)) = (\<Sum>j<?n1. (if (\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j)
             then ?Ps!(?\<pi>!j)
             else 0)) +
            (\<Sum>j = ?n1..<length ?Ts. (if (\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j)
             then ?Ps!(?\<pi>!j)
             else 0))" 
      using sum.atLeastLessThan_concat[where ?n = "?n1" and ?p = "length ?Ts" and ?m = "0", OF zero_le n1_small]
      atLeast0LessThan 
      by (metis (no_types, lifting))
    ultimately show ?thesis
      using sum_penalties_chosen by linarith
  qed
  moreover have "sum_list ws \<ge> B" using assms total_sum_ge_goal by auto
  ultimately show ?thesis unfolding ss_list_to_job_seq_def
    using job_seq_cert[OF pi_perm] 
    by simp
qed

(* complete *)
lemma ss_list_to_job_seq_complete:
  assumes "(Ts, Ds, Ps, k) \<in> job_sequencing"
      "ss_list_to_job_seq(ws,B) = (Ts, Ds, Ps, k)"
    shows "(ws, B) \<in> subset_sum_list"
proof (cases "sum_list ws \<ge> B")
  case False
  then have "ss_list_to_job_seq(ws,B) = ([1],[0], [1], 0)"
    using False unfolding ss_list_to_job_seq_def by auto
  then show ?thesis  using assms(1,2) example_not_in_job_sequencing by argo
next
  case True
  from assms(1) obtain \<pi> where
    \<pi>_perm: "perm \<pi> [0..<length Ts]"
    and total_penalty: "(\<Sum>j<length Ts. (if (\<Sum>i<j+1. Ts!(\<pi>!i)) > Ds!(\<pi>!j)
             then Ps!(\<pi>!j)
             else 0)) \<le>  k"
    and len_eq: "length Ts = length Ds \<and> length Ts = length Ps"
    unfolding job_sequencing_def by blast

  from assms(2) have
    Ts_def: "Ts = ws"
    and Ds_def: "Ds = replicate (length ws) B"
    and Ps_def: "Ps = ws"
    and k_def: "k = sum_list ws - B"
    unfolding ss_list_to_job_seq_def using True by auto

  define C where "C j = (\<Sum>i\<le>j. Ts!(\<pi>!i))" for j
  define EARLY where "EARLY = {j. j < length Ts \<and> C j \<le> B}"
  define LATE  where "LATE = {j. j < length Ts \<and> C j > B}"

  have C_increasing: "\<And>i j. i \<le> j \<and> j < length Ts \<longrightarrow> C i \<le> C j"
    unfolding C_def by (simp add: sum_mono2)

  have sum_early_le_B: "(\<Sum>j\<in>EARLY. Ts!(\<pi>!j)) \<le> B"
  proof (cases "EARLY = {}")
    case True
    then show ?thesis by auto
  next
    case False
    let ?M = "Max EARLY" 
    have "?M \<in> EARLY" using False 
      by (metis EARLY_def Max_in finite_Collect_conjI finite_Collect_less_nat)
    have "EARLY = {j. j \<le> ?M}"
    proof
      show "EARLY \<subseteq> {j. j \<le> ?M}" 
        using EARLY_def by force
      show "{j. j \<le> ?M} \<subseteq> EARLY"
      proof
        fix j assume "j \<in> {j. j \<le> ?M}"
        then have "j \<le> ?M" by auto
        have "C ?M \<le> B" using False 
          using EARLY_def \<open>Max EARLY \<in> EARLY\<close> by blast
        moreover have "C j \<le> C ?M"
          using C_increasing EARLY_def False \<open>j \<le> Max EARLY\<close> by auto
        ultimately have "C j \<le> B" by linarith
        thus "j \<in> EARLY" 
          using EARLY_def \<open>Max EARLY \<in> EARLY\<close> \<open>j \<le> Max EARLY\<close> dual_order.strict_trans2 by blast
      qed
    qed
    then have "(\<Sum>j\<in>EARLY. Ts!(\<pi>!j)) = C ?M"
      by (simp add: C_def atMost_def)
    then show ?thesis  using EARLY_def \<open>Max EARLY \<in> EARLY\<close> by auto
  qed
  
  have sum_total: "sum_list ws = (\<Sum>j\<in>EARLY. Ts!(\<pi>!j)) + (\<Sum>j\<in>LATE. Ts!(\<pi>!j))"
  proof -
    have "EARLY \<union> LATE = {j. j < length Ts}" using EARLY_def LATE_def by auto
    moreover have "EARLY \<inter> LATE = {}" using EARLY_def LATE_def by auto
    ultimately have "(\<Sum>j<length Ts. Ts!(\<pi>!j)) = (\<Sum>j\<in>EARLY. Ts!(\<pi>!j)) + (\<Sum>j\<in>LATE. Ts!(\<pi>!j))"
      using sum.union_disjoint  by (simp add: lessThan_def sum_Un_eq)
    moreover have "(\<Sum>j<length Ts. Ts!(\<pi>!j)) = sum_list ws"
      using Ts_def \<pi>_perm  sum_perm_sum_list by blast
    ultimately show ?thesis by auto
  qed

  have sum_late_le: "(\<Sum>j\<in>LATE. Ts!(\<pi>!j)) \<le> sum_list ws - B"
  proof -
    have "\<And>j. j < length Ts \<Longrightarrow> Ds!(\<pi>!j) = B" unfolding Ds_def Ts_def
      by (metis Ds_def Ts_def \<pi>_perm in_set_replicate len_eq length_map list.set_map map_nth nth_map nth_mem set_mset_mset size_mset)
    then have "(\<Sum>j<length Ts. (if (\<Sum>i<j+1. Ts!(\<pi>!i)) > Ds!(\<pi>!j)
             then Ps!(\<pi>!j)
             else 0))
          = (\<Sum>j<length ws. (if C j > B
             then ws !(\<pi>!j)
             else 0))" 
      unfolding Ps_def Ts_def C_def
      using lessThan_Suc_atMost by force
    also have "... = (\<Sum>j\<in>{x \<in> {..<length ws}. C x > B}. Ts!(\<pi>!j))" unfolding Ts_def 
      using sum.inter_filter[of "{..<length ws}" "\<lambda>j. ws!(\<pi>!j)", OF finite_lessThan]
      by auto
    also have "... = (\<Sum>j\<in>LATE. Ts!(\<pi>!j))" using LATE_def Ts_def by auto
    finally show ?thesis using total_penalty k_def by auto
  qed
  have sum_early_ge_B: "(\<Sum>j\<in>EARLY. Ts!(\<pi>!j)) \<ge> B"
  proof -
    from sum_total have "sum_list ws = (\<Sum>j\<in>EARLY. Ts!(\<pi>!j)) + (\<Sum>j\<in>LATE. Ts!(\<pi>!j))" .
    then have "(\<Sum>j\<in>EARLY. Ts!(\<pi>!j)) = sum_list ws - (\<Sum>j\<in>LATE. Ts!(\<pi>!j))" by simp
    moreover  have "... \<ge> sum_list ws - (sum_list ws - B)" using sum_late_le by simp
    ultimately show ?thesis using True  by auto
  qed

  from sum_early_le_B sum_early_ge_B have sum_early_eq_B: "(\<Sum>j\<in>EARLY. Ts!(\<pi>!j)) = B"
    by simp

  define S where "S = ((!) \<pi>) ` EARLY"
  have S_subset: "S \<subseteq> {..<length ws}"
  proof
   fix x
   assume "x \<in> S"
   then obtain i where "i \<in> EARLY" and "x = \<pi> ! i"
    using S_def by auto
   then have  "i \<in> {..<length ws}"
    using `i \<in> EARLY`  using EARLY_def Ts_def by blast
   then have "x \<in> set \<pi>" 
   by (metis Ts_def \<open>x = \<pi> ! i\<close> \<pi>_perm diff_zero length_upt lessThan_iff nth_mem size_mset)
   thus "x \<in> {..<length ws}"
     using Ts_def \<pi>_perm atLeast_upt perm_set_eq by blast
  qed

  have sum_S_eq_B: "(\<Sum>j\<in>S. ws!j) = B"
  proof -
    have "inj_on ((!) \<pi>) EARLY"
     by (metis (no_types, lifting) EARLY_def \<pi>_perm atLeast_upt distinct_map distinct_upt inj_on_nth length_map map_nth mem_Collect_eq nth_injective_permutation size_mset)
    then have "(\<Sum>j\<in>S. ws!j) = (\<Sum>j\<in>EARLY. ws!(\<pi>!j))" using S_def
      by (intro sum.reindex_cong[of "((!) \<pi>)"])  auto
    also have "... = B" using Ts_def sum_early_eq_B by simp
    finally show ?thesis .
  qed

  define xs where "xs = map (\<lambda>i. if i \<in> S then (1::nat) else 0) [0..<length ws]"
  have xs_length: "length xs = length ws"
    by (simp add: xs_def)

  moreover have xs_binary: "\<forall>i<length xs. xs!i \<in> {0, 1}"
    using xs_def by auto

  moreover have xs_subset_sum: "(\<Sum>i<length ws. ws!i * xs!i) = B"
  proof -
    have "(\<Sum>i<length ws. ws!i * xs!i) = (\<Sum>i\<in>S. ws!i)"
    proof -
      have "(\<Sum>i<length ws. ws!i * xs!i) = (\<Sum>i<length ws. if i \<in> S then ws!i else 0)"
        using xs_def by (intro sum.cong) auto
      also have "... =  sum ((!) ws) {x \<in> {..<length ws}. x \<in> S}" using  sum.inter_filter[of "{..<length ws}" "(!) ws"] by auto
      also have "... = (\<Sum>i\<in>S. ws!i)"  using S_subset by (intro sum.cong,auto)
      finally show ?thesis by auto
    qed
    then show ?thesis using sum_S_eq_B by simp
  qed
  ultimately show ?thesis using subset_sum_list_cert[of xs] by auto

qed

