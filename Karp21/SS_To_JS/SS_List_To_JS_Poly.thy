theory SS_List_To_JS_Poly
  imports
    SS_To_JS
begin

section "Costs"

definition size_job_seq where
  "size_job_seq = (\<lambda> (ps, ds, ws, k).  length ps + length ds + length ws + 1)"

definition ss_list_to_job_seq_time :: "nat \<Rightarrow> nat" where
  "ss_list_to_job_seq_time n = 2 * n"

definition ss_list_to_job_seq_space :: "nat \<Rightarrow> nat" where
  "ss_list_to_job_seq_space n = 3 * n + 1"

subsection "First Refinement"

text \<open>we assume that one can add a list and replicate a value in time of length of the list\<close>
definition mop_sum_list where
  "mop_sum_list ws \<equiv> SPECT [sum_list ws \<mapsto>  length ws]"

definition mop_replicate_B  where
  "mop_replicate_B ws B \<equiv> SPECT [replicate (length ws) B \<mapsto> length ws]"

definition ss_list_to_job_seq_alg :: "(nat list \<times> nat) \<Rightarrow> (nat list \<times> nat list \<times> nat list \<times> nat) nrest" where
  "ss_list_to_job_seq_alg \<equiv> \<lambda>(ws, B).
    do {
      s \<leftarrow> mop_sum_list ws;
      if s \<ge> B
      then do {
        ds \<leftarrow> mop_replicate_B ws B;
        RETURNT (ws, ds, ws, s - B)
      }
      else RETURNT NOT_JOB_SEQ_EXAMPLE
    }"

subsubsection "Proofs"

lemma ss_list_to_job_seq_refines:
  "ss_list_to_job_seq_alg P
\<le> SPEC (\<lambda>y. y = ss_list_to_job_seq P) (\<lambda>_. ss_list_to_job_seq_time (size_ss_list P))"
unfolding SPEC_def ss_list_to_job_seq_alg_def ss_list_to_job_seq_def
          mop_sum_list_def  mop_replicate_B_def
apply(rule T_specifies_I)
apply(vcg' \<open>-\<close> rules: T_SPEC )
by (auto simp add: ss_list_to_job_seq_time_def size_ss_list_def)

lemma ss_list_to_job_seq_size:
  "size_job_seq (ss_list_to_job_seq (ws, B)) \<le> ss_list_to_job_seq_space (size_ss_list (ws, B))"
  unfolding ss_list_to_job_seq_def size_job_seq_def ss_list_to_job_seq_space_def size_ss_list_def
            NOT_JOB_SEQ_EXAMPLE_def
  by force


theorem ss_list_to_job_seq_is_polyred:
  "ispolyred ss_list_to_job_seq_alg subset_sum_list job_sequencing size_ss_list size_job_seq"
  using ss_list_to_job_seq_size  is_reduction_ss_list_to_job_seq  poly_cmult poly_linear
        ss_list_to_job_seq_refines
  by (intro ispolyredI[where ?time_f  = ss_list_to_job_seq_time  and
                             ?space_f = ss_list_to_job_seq_space],
      unfold ss_list_to_job_seq_time_def ss_list_to_job_seq_space_def) fast+


subsection "Second Refinement"

text \<open>we relax the assumptions to:
     -  we can add two numbers in constant time
     -  we can add a constant to front in constant time\<close>

definition mop_add where
  "mop_add a b \<equiv> SPECT [a + b \<mapsto> 1]"

definition mop_const_cons where
  "mop_const_cons c _ xs \<equiv> SPECT [ (c # xs) \<mapsto> 1]"

definition ss_list_to_job_seq_alg2 :: "(nat list \<times> nat) \<Rightarrow> (nat list \<times> nat list \<times> nat list \<times> nat) nrest" where
  "ss_list_to_job_seq_alg2 \<equiv> \<lambda>(ws, B).
    do {
      s \<leftarrow> nfoldli ws (\<lambda>_. True) mop_add 0;
      if s \<ge> B
      then do {
        ds \<leftarrow>  nfoldli ws (\<lambda>_. True) (mop_const_cons B) [];
        RETURNT (ws, ds, ws, s - B)
      }
      else RETURNT NOT_JOB_SEQ_EXAMPLE
    }"


lemma sum_list_linear:
  "nfoldli (P:: nat list)(\<lambda>_. True) mop_add k
   \<le> SPEC (\<lambda>y. y = (sum_list P) + k) (\<lambda>_. length P)"
proof (induction P arbitrary: k )
  case Nil
  then show ?case
    by (simp add: inresT_SPEC pw_le_iff)
next
  case (Cons x xs)
  have "mop_add x k = SPECT [x + k \<mapsto> 1]"
    by (simp add:  mop_add_def)
  moreover have "nfoldli xs (\<lambda>_. True) mop_add (x + k)
                 \<le> SPEC (\<lambda>y. y =  sum_list xs + (x + k)) (\<lambda>_. length xs)"
    using Cons.IH[of "x + k"] by simp
  ultimately have *: "nfoldli (x # xs) (\<lambda>_. True) mop_add k \<le> do {
    s1 \<leftarrow> SPECT [x + k \<mapsto> 1];
    y \<leftarrow> SPEC (\<lambda>y. y =  sum_list xs + s1) (\<lambda>_. length xs);
    RETURNT y
  }"
    using bindT_mono' Cons by fastforce
  moreover have "do {
            s1 \<leftarrow> SPECT [k + x \<mapsto> 1];
            y \<leftarrow> SPEC (\<lambda>y. y = sum_list xs + s1) (\<lambda>_. length xs );
            RETURNT y
          } \<le> SPEC (\<lambda>y. y = sum_list (x#xs) + k) (\<lambda>_. length xs + 1)"
      unfolding SPEC_def
      apply (vcg)
      unfolding bindT_def
      by (auto simp add: add.commute le_fun_def one_enat_def)
  ultimately show ?case
    by (simp add: SPEC_def add.commute)
qed

lemma replicate_linear:
  "nfoldli P (\<lambda>_. True) (mop_const_cons B) k
   \<le> SPEC (\<lambda>y. y = (replicate (length P) B)@k) (\<lambda>_. length P)"
proof (induction P arbitrary: k )
  case Nil
  then show ?case
    by (simp add: inresT_SPEC pw_le_iff)
next
  case (Cons x xs)
  have "mop_const_cons B x k = SPECT [B # k \<mapsto> 1]"
    by (simp add:  mop_const_cons_def)
  moreover have "nfoldli xs (\<lambda>_. True) (mop_const_cons B) (B#k)
                 \<le> SPEC (\<lambda>y. y = (replicate (length xs) B)@(B#k)) (\<lambda>_. length xs)"
    using Cons.IH[of "B#k"] by simp
  ultimately have *: "nfoldli (x#xs) (\<lambda>_. True) (mop_const_cons B) k \<le> do {
    s1 \<leftarrow> SPECT [B # k \<mapsto> 1];
    y \<leftarrow> SPEC (\<lambda>y. y = (replicate (length xs) B)@s1) (\<lambda>_. length xs);
    RETURNT y
  }"
    using bindT_mono' Cons
    by fastforce
  moreover have "do {
            s1 \<leftarrow> SPECT [B # k \<mapsto> 1];
            y \<leftarrow> SPEC (\<lambda>y. y = (replicate (length xs) B)@s1) (\<lambda>_. length xs);
            RETURNT y
          } \<le> SPEC (\<lambda>y. y = (replicate (length (x#xs)) B)@k) (\<lambda>_. length xs + 1)"
      unfolding SPEC_def
      apply (vcg)
      unfolding bindT_def
      by (simp add: le_fun_def one_enat_def replicate_app_Cons_same)
    ultimately show ?case
      by (simp add: SPEC_def)
qed

lemma ss_list_to_job_seq_alg2_refines:
  "ss_list_to_job_seq_alg2 P
   \<le> ss_list_to_job_seq_alg P "
  unfolding ss_list_to_job_seq_alg2_def
            ss_list_to_job_seq_alg_def SPEC_def
            mop_sum_list_def mop_replicate_B_def
  apply (refine_mono)
  by (auto intro!: sum_list_linear[where ?k =0, simplified, THEN ord_le_eq_trans]
                   replicate_linear[where ?k ="[]", simplified, THEN ord_le_eq_trans]
           simp add:SPEC_def fun_upd_def)

end