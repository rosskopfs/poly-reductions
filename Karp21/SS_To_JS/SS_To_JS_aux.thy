theory  SS_To_JS_aux
  imports Main  "HOL-Combinatorics.List_Permutation"  "../XC_To_SS/XC_To_SS_aux" 

begin


definition job_sequencing :: "((int list) * (int list) * (int list) * nat) set" where
  "job_sequencing \<equiv> {(Ts, Ds, Ps, k). (length Ts = length Ds) \<and> (length Ts = length Ps) \<and>
    (\<exists>\<pi>::nat list. 
      (perm \<pi> [0..<length Ts])  \<and>
      (\<Sum>j<length Ts. (if (\<Sum>i<j+1. Ts!(\<pi>!i)) > Ds!(\<pi>!j) 
         then Ps!(\<pi>!j) 
         else 0)) \<le> int k)}"


lemma job_seq_cert:
  assumes "perm \<pi> [0..<length Ts]"
    "(length Ts = length Ds) \<and> (length Ts = length Ps)"
    "(\<Sum>j<length Ts. (if (\<Sum>i<j+1. Ts!(\<pi>!i)) > Ds!(\<pi>!j) 
         then Ps!(\<pi>!j) 
         else 0)) \<le> int k"
  shows "(Ts, Ds, Ps, k) \<in> job_sequencing"
 using SS_To_JS_aux.job_sequencing_def assms(1,2,3) by blast

lemma subset_sum_list_cert:
  assumes "(\<forall>i<length xs. xs!i \<in> {0,1})"
          "(\<Sum>i<length as. as!i * xs!i) = s"
          "length xs = length as"
        shows "(as,s)\<in> subset_sum_list"
  using subset_sum_list_def assms(1,2,3) by blast


(* reduction *)
definition ss_list_to_job_seq :: "nat list \<times> nat \<Rightarrow> int list \<times> int list \<times> int list \<times> nat" where
  "ss_list_to_job_seq \<equiv> \<lambda>(ws, B). (ws, replicate (length ws) B, ws, (sum_list ws - B))"



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
  shows "distinct ys \<Longrightarrow> (\<Sum>i=length xs..<length (xs@ys). f ((xs@ys)!i)) = (\<Sum>i \<in> set ys. f i)"
proof -
  assume "distinct ys"
  also have "(\<Sum>i=length xs..<length ys  + length xs. f ((xs@ys)!i)) = 
             (\<Sum>i=0..< length ys. f ((xs@ys)!(i+length xs))) "
    using sum.shift_bounds_nat_ivl[of "\<lambda>i. f ((xs@ys)!i)" "0" "length xs" "length ys"]
    by simp
  then show ?thesis 
    by (smt (z3) add.commute atLeast_upt calculation length_append nth_append_length_plus set_upt sum.cong sum_nth_sum_set)
qed

(* proof *)

lemma ss_list_to_job_seq_sound:
  assumes "(ws, B) \<in> subset_sum_list"
  shows "ss_list_to_job_seq (ws, B) \<in> job_sequencing"
proof -
  from assms obtain xs_orig where
    xs_orig_def: "length xs_orig = length ws" "\<forall>i<length xs_orig. xs_orig!i \<in> {0, 1}"
    "(\<Sum>i<length ws. ws!i * xs_orig!i) = B"
    unfolding subset_sum_list_def by blast

  (* define a new solution xs that chooses all 0 elements too *)
  define xs where "xs = map (\<lambda>i. if ws!i = 0 then 1 else xs_orig!i) [0..<length ws]"
  have xs_length: "length xs = length ws" by (simp add: xs_def)
  have xs_is_choice_vector: "\<forall>i<length xs. xs!i \<in> {0, 1}"
    using xs_def xs_orig_def(1,2) by auto
  have xs_subset_sum: "(\<Sum>i<length ws. ws!i * xs!i) = B"
    by (smt (verit, best) atLeast_upt map_eq_conv map_nth mult_is_0 sum.cong xs_def xs_length xs_orig_def(3))
 
 (* job_sequencing: task times, penalties, and deadlines using ws and B *)
  let ?Ts = "map int ws"
  let ?Ps = "map int ws"
  let ?Ds = "map int (replicate (length ws) B)"
  let ?chosen = "[i \<leftarrow> [0..<length ws]. xs!i = 1]"
  let ?non_chosen = "[i \<leftarrow> [0..<length ws]. xs!i = 0]"
  let ?\<pi> = "?chosen @ ?non_chosen"
  let ?k = "(sum_list ws - B)"

  (* properties of \<pi> *)
  have same_length: "length ?\<pi> = length [0..<length ?Ts]" using xs_def
  proof -
    have "length ?\<pi> = length [i. i \<leftarrow> [0..<length ws], xs!i = 1 \<or> xs!i = 0]"
      by (induction ws) auto
    then have "length ?\<pi> = length [i. i \<leftarrow> [0..<length xs], xs!i = 1 \<or> xs!i = 0]" using xs_def by simp
    also have "[i. i \<leftarrow> [0..<length xs], xs!i = 1 \<or> xs!i = 0] = [i. i \<leftarrow> [0..<length xs]]"
      using xs_is_choice_vector
      by (smt (verit) add_0 concat_map_singleton insertE length_map map_equality_iff map_nth nth_upt singletonD)
    then show ?thesis using calculation by (simp add: xs_length)
  qed
  have "distinct ?\<pi>" by auto
  also have "set ?\<pi> = set [0..<length ?Ts]" using xs_def xs_orig_def
    using not_less_eq by (auto,blast)
  then have pi_perm: "perm ?\<pi> [0..<length ?Ts]" using distinct_upt set_eq_iff_mset_eq_distinct calculation
    by blast


  moreover have all_length_same: "length ?Ts = length ?Ds \<and> length ?Ts = length ?Ps"
    by simp

  (* sum of penalties for \<pi> is at most k *) 
  moreover have sum_le_k: "(\<Sum>j<length ?Ts. (if (\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j)
             then ?Ps!(?\<pi>!j)
             else 0)) \<le> int ?k"
  proof -
    (* we show that the chosen elements have total penalty 0 while the 
      rest cause a total penalty of exactly k *)
    let ?n1 = "length ?chosen"

    have sum_chosen_set: "(\<Sum>i\<in>set ?chosen. ws!i) = B"
    proof -
      have "(\<Sum>i\<in>set ?chosen. ws!i) = (\<Sum>i<length ws. if xs!i = 1 then ws!i else 0)"
       using sum.inter_filter[of "{..<length ws}"] by auto
      also have "... = (\<Sum>i<length ws. ws!i * xs!i)"
      proof -
        have "\<forall>i < length ws. (if xs!i = 1 then ws!i else 0) = ws!i * xs!i"
          using xs_is_choice_vector xs_length by fastforce
        then show ?thesis by (intro sum.cong) auto
      qed
      then show ?thesis using calculation xs_subset_sum by presburger
    qed
    have sum_chosen: "(\<Sum>i<?n1. ?Ts!(?\<pi>!i)) = int B"
    proof -
      have "?\<pi>!i = ?chosen!i" if "i<?n1" for i
        using that by simp
      then have "(\<Sum>i<?n1. ?Ts!(?\<pi>!i)) = (\<Sum>i<?n1. ?Ts!(?chosen!i))"
        by simp
      also have "... = int (\<Sum>i<?n1. ws!(?chosen!i))"
      proof (induction "?chosen")
        case Nil
        then show ?case by auto
      next
        case (Cons a x)
        then show ?case
          by (smt (verit, ccfv_SIG) atLeast_upt filter_nth_ex_nth in_set_conv_nth length_map map_nth nth_map of_nat_sum sum.cong)
      qed
      also have "... = (\<Sum>i \<in> set ?chosen. ws!i)" using sum_nth_sum_set by auto
      then show ?thesis using sum_chosen_set calculation by auto
    qed
   
    
    have sum_penalties_chosen: "(\<Sum>j<?n1. (if (\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j)
             then ?Ps!(?\<pi>!j)
             else 0)) = 0"
    proof -
       have "\<And>j. j < ?n1 \<Longrightarrow> (\<Sum>i \<le> j. ?Ts ! (?\<pi> ! i)) \<le>  ?Ds!(?\<pi>!j)"
       proof -
         fix j assume j_chosen: "j < ?n1"
         have non_neg: "\<And>j. j < length ?\<pi> \<Longrightarrow> (?Ts ! (?\<pi> ! j)) \<ge> 0"
           by (smt (verit, ccfv_threshold) \<open>set ?\<pi> = set [0..<length ?Ts]\<close> in_set_conv_nth length_map map_nth nth_map nth_mem of_nat_0_le_iff)
         have "(\<Sum>i \<le> j. ?Ts ! (?\<pi> ! i)) + (\<Sum>i = j + 1..<?n1. ?Ts ! (?\<pi> ! i)) = (\<Sum>i < ?n1. ?Ts ! (?\<pi> ! i))"
           using `j < ?n1` by (metis Suc_eq_plus1 atLeast0LessThan atMost_iff bot_nat_0.extremum lessThan_Suc_atMost lessThan_iff linorder_not_less sum.atLeastLessThan_concat)
         moreover have "(\<Sum>i = j + 1..<?n1. ?Ts ! (?\<pi> ! i)) \<ge> 0"
           by (smt (verit, best) atLeastLessThan_iff le_trans length_filter_le length_map less_le_not_le linorder_not_le non_neg same_length sum_nonneg)
         ultimately have "(\<Sum>i \<le> j. ?Ts ! (?\<pi> ! i)) \<le> (\<Sum>i < ?n1. ?Ts ! (?\<pi> ! i))"
           by arith
         then show "j < ?n1 \<Longrightarrow> (\<Sum>i \<le> j. ?Ts ! (?\<pi> ! i)) \<le>  ?Ds!(?\<pi>!j)"
           by (smt (verit) j_chosen all_length_same filter_nth_ex_nth in_set_replicate length_map map_nth nth_append_first nth_map nth_mem sum_chosen)
       qed
       then have "\<And>j. j < ?n1 \<Longrightarrow>  (if (\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j)
             then ?Ps!(?\<pi>!j)
             else 0) = 0"
         by (metis Suc_eq_plus1 lessThan_Suc_atMost linorder_not_less)
       then show ?thesis by fastforce
     qed

    (* all non_chosen jobs have strictly positive task time *) 
    have geq_n1_strict_pos: "\<And>j. j < length ?Ts \<and> j \<ge> ?n1 \<Longrightarrow>
                                 ?Ts ! (?\<pi> ! j) > 0"
    proof -
      fix j assume j_bound: "j < length ?Ts \<and> j \<ge> ?n1"
      then have j_non_chosen: "(?\<pi> ! j) \<in> set ?non_chosen" using nth_append_in_set same_length
        by (metis diff_zero length_upt)
      then have "xs!(?\<pi> ! j) = 0" by (simp add: xs_length)
      moreover have "ws!(?\<pi> ! j) \<noteq> 0"
      proof (rule ccontr)
           assume "\<not> ws!(?\<pi> ! j) \<noteq> 0"
           then have "ws!(?\<pi> ! j) = 0"
             by simp
           then have "xs!(?\<pi> ! j) = 1"
             using \<open>(?\<pi> ! j) \<in> set ?non_chosen\<close> xs_def by fastforce
           thus False   using calculation by linarith
      qed
      then have "int (ws ! (?\<pi> ! j)) > 0" using  calculation by auto
      also have "(?\<pi> ! j) < length ws" using j_bound  j_non_chosen by force
      then show "?Ts ! (?\<pi> ! j) > 0" using nth_map[of "?\<pi> ! j" ws int] j_bound 
        using \<open>int (ws ! (?\<pi> ! j)) > 0\<close> by linarith
    qed
    (* every non_chosen job exceeds the deadline *)
    moreover have "\<And>j. j < length ?Ts \<and> j \<ge> ?n1 \<Longrightarrow> (\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j)"
    proof -
      fix j assume j_bound: "j < length ?Ts \<and> j \<ge> ?n1"
      then have "(\<Sum>i<j+1. ?Ts!(?\<pi>!i)) = (\<Sum>i<?n1. ?Ts!(?\<pi>!i)) + (\<Sum>i=?n1..j. ?Ts!(?\<pi>!i))"
        using sum.atLeastLessThan_concat
        by (metis Suc_eq_plus1 atLeast0LessThan atLeastAtMost_upt le0 le_SucI set_upt)
      moreover have "(\<Sum>i=?n1..j. ?Ts!(?\<pi>!i)) > 0"
      proof -
        have "\<And>i. i \<in> {?n1..j} \<Longrightarrow> ?Ts!(?\<pi>!i) > 0"
          using j_bound geq_n1_strict_pos by simp
        then have "(\<Sum>i=?n1..j. ?Ts!(?\<pi>!i)) > 0"
          using sum_pos[of "{?n1..j}" "\<lambda>i. ?Ts!(?\<pi>!i)"] j_bound by auto
        thus ?thesis .
      qed
      ultimately have "(\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > (\<Sum>i<?n1. ?Ts!(?\<pi>!i))"
        by linarith
      then show "(\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j)" using sum_chosen
        by (smt (verit, ccfv_SIG) \<open>set ?\<pi> = set [0..<length ?Ts]\<close> all_length_same in_set_replicate j_bound length_map list.set_map map_nth map_replicate nth_map nth_mem same_length)
    qed


    moreover have sum_penalties_non_chosen: "(\<Sum>j = ?n1..<length ?Ts. (if (\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j)
             then ?Ps!(?\<pi>!j)
             else 0))= int ?k"
    proof -
      have "(\<Sum>j = ?n1..<length ?Ts. (if (\<Sum>i<j+1. ?Ts!(?\<pi>!i)) > ?Ds!(?\<pi>!j)
             then ?Ps!(?\<pi>!j)
             else 0)) = (\<Sum>j = ?n1..<length ?Ts. ?Ps!(?\<pi>!j))"   by (smt (verit) calculation(2) sum.ivl_cong)
      also have "...     = (\<Sum>j=?n1..<length ?Ts. int (ws!(?\<pi>!j)))"
          using nth_map
          by (smt (verit, ccfv_SIG) \<open>set ?\<pi> = set [0..<length ?Ts]\<close> atLeastLessThan_iff length_map map_nth nth_mem same_length set_upt sum.cong)
      also have "... = int (\<Sum>j=?n1..<length ?Ts. ws!(?\<pi>!j))" by auto
      also have "... = int (\<Sum>i\<in>set ?non_chosen. ws!i)"
        using sum_nth_sum_set_append[of "?non_chosen"]
        by (metis List.distinct_filter distinct_upt length_map map_nth same_length)
      moreover have "... = int (sum_list ws - B)"
      proof -
        have "sum_list ws = (\<Sum>i\<in>set ?chosen. ws!i) + (\<Sum>i\<in>set ?non_chosen. ws!i)"
          by (metis (no_types, lifting) \<open>distinct ?\<pi>\<close> \<open>set ?\<pi> = set [0..<length (map int ws)]\<close> distinct_filter distinct_upt length_map map_append map_nth sum_list_append sum_list_distinct_conv_sum_set)
        then have "sum_list ws - B = (\<Sum>i\<in>set ?non_chosen. ws!i)" using sum_chosen_set by arith
        thus ?thesis by presburger
      qed
      then show ?thesis using calculation by presburger
    qed
    ultimately show ?thesis
        by (smt (verit, del_insts) atLeast_upt bot_nat_0.extremum length_filter_le length_map map_nth order_refl set_upt sum.atLeastLessThan_concat sum_penalties_chosen)
  qed
  ultimately show ?thesis unfolding ss_list_to_job_seq_def
    using job_seq_cert[of "?\<pi>"]
    by auto
qed

(* draft *)
lemma ss_list_to_job_seq_complete:
  assumes "(Ts, Ds, Ps, k) \<in> job_sequencing"
      "ss_list_to_job_seq(ws,B) = (Ts, Ds, Ps, k)"
    shows "(ws, B) \<in> subset_sum_list"
proof -
  from assms(1) obtain \<pi> where
    \<pi>_perm: "perm \<pi> [0..<length Ts]"
    and total_penalty: "(\<Sum>j<length Ts. (if (\<Sum>i<j+1. Ts!(\<pi>!i)) > Ds!(\<pi>!j)
             then Ps!(\<pi>!j)
             else 0)) \<le> int k"
    and len_eq: "length Ts = length Ds \<and> length Ts = length Ps"
    unfolding job_sequencing_def by blast

  from assms(2) have
    Ts_def: "Ts = map int ws"
    and Ds_def: "Ds = map int (replicate (length ws) B)"
    and Ps_def: "Ps = map int ws"
    and k_def: "k = sum_list ws - B"
    unfolding ss_list_to_job_seq_def by auto

  define C where "C j = (\<Sum>i<j+1. Ts!(\<pi>!i))" for j
  define EARLY where "EARLY = {j. j < length Ts \<and> C j \<le> int B}"
  define LATE  where "LATE = {j. j < length Ts \<and> C j>  int B}"

  have sum_early_less: "(\<Sum>j\<in>EARLY. Ts!(\<pi>!j)) \<le>  int B"
    sorry
  have sum_total: "sum_list ws =  (\<Sum>j\<in>EARLY. Ts!(\<pi>!j)) + (\<Sum>j\<in>LATE. Ts!(\<pi>!j)) "
    sorry 
  have sum_late : "(\<Sum>j\<in>LATE. Ts!(\<pi>!j))  \<le> sum_list ws - B"
    sorry
  have "(\<Sum>j\<in>EARLY. Ts!(\<pi>!j)) \<ge> B"
  proof -
    have "(\<Sum>j\<in>LATE. Ts!(\<pi>!j)) =  sum_list ws -  (\<Sum>j\<in>EARLY. Ts!(\<pi>!j))"
      sorry
    then have "sum_list ws -  (\<Sum>j\<in>EARLY. Ts!(\<pi>!j)) \<le> sum_list ws - B"
      sorry
    then show ?thesis sorry
  qed
  then have "(\<Sum>j\<in>EARLY. Ts!(\<pi>!j)) = B"  using sum_early_less by linarith
  define S where "S = {\<pi>!j | j. j \<in> EARLY}"
  have "(\<Sum>j\<in>S. ws!j) = B" sorry
  define xs where "xs = map (\<lambda>i. if i \<in> S then 1::nat else 0) [0..<length ws]"
  have "(\<Sum>i<length ws. ws!i * xs!i) = B" 
  proof -
    have "S \<subseteq> {..<length ws}" sorry
    then have "(\<Sum>j\<in>S. ws!j) = (\<Sum>j<length ws. if j \<in> S then ws!j else 0)"
      using  sum.inter_filter[of "{..<length ws}" "(!) ws"]   by (simp add: sum.mono_neutral_cong_left)
    then show ?thesis
    by (smt (verit, best) \<open>sum ((!) ws) S = B\<close> add_cancel_left_left atLeast_upt diff_zero in_set_conv_nth length_upt mult.right_neutral mult_is_0 nth_map nth_upt sum.cong xs_def)
  qed     
  then show ?thesis  using subset_sum_list_cert[of "xs" ws B] xs_def
      by auto
qed

