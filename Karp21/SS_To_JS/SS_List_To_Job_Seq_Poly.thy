theory SS_List_To_Job_Seq_Poly
  imports "../Polynomial_Reductions"
          "../XC_To_SS/XC_To_SS_aux"
         SS_To_JS_aux
begin

section "The reduction from subset sum list to job sequence is polynomial"


subsection "Algorithm Definition"

definition mop_sum_list where
  "mop_sum_list ws \<equiv> SPECT [sum_list ws \<mapsto> length ws]"
                        
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

subsection "Time and Space Definitions"

definition ss_list_to_job_seq_time :: "nat \<Rightarrow> nat" where
  "ss_list_to_job_seq_time n = 2*n" 

definition ss_list_to_job_seq_space :: "nat \<Rightarrow> nat" where
  "ss_list_to_job_seq_space n = 3 * n + 1"

definition size_job_seq where
  "size_job_seq = (\<lambda> (ps, ds, ws, k).  length ps + length ds + length ws + 1)"

subsection "Proofs"

lemma ss_list_to_job_seq_refines:
  "ss_list_to_job_seq_alg (ws, B) \<le> SPEC (\<lambda>y. y = ss_list_to_job_seq (ws, B)) (\<lambda>_. ss_list_to_job_seq_time (size_ss_list (ws, B)))"
unfolding SPEC_def 
unfolding ss_list_to_job_seq_alg_def ss_list_to_job_seq_def 
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
  unfolding ispolyred_def
  apply(rule exI[where x=ss_list_to_job_seq])
  apply(rule exI[where x=ss_list_to_job_seq_time])
  apply(rule exI[where x=ss_list_to_job_seq_space])
  apply (safe)
  subgoal by (simp add: ss_list_to_job_seq_refines)
  subgoal by (simp add: ss_list_to_job_seq_size)
  subgoal using poly_cmult poly_linear ss_list_to_job_seq_time_def by presburger
  subgoal using ss_list_to_job_seq_space_def poly_add poly_cmult poly_const poly_linear
    by presburger
  using is_reduction_ss_list_to_job_seq by blast

end