theory IMP_Minus_To_SAT
  imports "IMP_Minus_To_SAS_Plus" "Verified_SAT_Based_AI_Planning.SAT_Solve_SAS_Plus"
    "Cook_Levin" "IMP_Minus.Max_Constant"
begin

section \<open>Translation from IMP- to SAT\<close>

text \<open>In this theory the translations `from IMP- to SAS+`
      and `SAS+ to SAT` are composed and the `main_lemma` for
      the Cook_Levin theorem is proven correct.\<close>


subsection \<open>The partial steps:\<close>

text \<open>theorems about the translation from IMP- to SAS+\<close>
thm SAS_Plus_to_IMP_Minus_correctness

thm IMP_Minus_to_SAS_Plus_correctness


text \<open>theorem about the translation from SAS+ to SAT\<close>
thm sas_plus_problem_has_serial_solution_iff

(* TODO: use that *)
term Sema.sat


subsection \<open>Putting things together\<close>

text \<open>Putting things together works in three steps:
  \<^item> first we put together the transformations on the HOL level
  \<^item> then we synthesize a IMP- program that refines the HOL algorithm
  \<^item> then we instantiate the Cook_Levin locale\<close>

subsubsection \<open>Putting things together on the HOL level\<close>

definition encode_sat :: "_ \<Rightarrow> nat"  where
  "encode_sat F = undefined"


lemma valid_problem: "is_valid_problem_sas_plus (IMP_Minus_to_SAS_Plus c I r G t)"
  using SAS_Plus_Plus_To_SAS_Plus_valid[OF imp_minus_minus_to_sas_plus_valid]
  by (auto simp: IMP_Minus_to_SAS_Plus_def Let_def)

lemma while_program_has_model:
  assumes 
    "I \<subseteq>\<^sub>m Some \<circ> s1"
    "finite (range s1)"
    (*Mohammad: The next assumption has to be fixed in IMP_Minus_to_SAS_Plus_correctness*)
    "Max (range s1) < r"
    "G \<subseteq>\<^sub>m Some \<circ> s2"
    "(c, s1) \<Rightarrow>\<^bsup> t \<^esup> s2"
    "t \<le> t'"
  shows 
  (*Mohammad: there is still a problem with this theorem, namely, the generated formula is still
              parameterised by the specific running time 't'.
              This can only be fixed by generalising IMP_Minus_to_SAS_Plus_correctness *)
  "\<exists>\<A>. \<A> \<Turnstile> \<Phi>\<^sub>\<forall> (\<phi> prob_with_noop (IMP_Minus_to_SAS_Plus c I r G t'))
                100 * (max_input_bits c I r + t' + 1) * (t' - 1) +
                   (max_input_bits c I r + t' + 2) *
                      (num_variables c + 2) + 52"
  (is "\<exists>_. _ \<Turnstile> \<Phi>\<^sub>\<forall> _ (?b::nat)")
proof-
  obtain plan where plan:
    "length plan \<le> ?b"
    "SAS_Plus_Semantics.is_serial_solution_for_problem (IMP_Minus_to_SAS_Plus c I r G t') plan"
    using assms(6) le_trans IMP_Minus_to_SAS_Plus_correctness[OF assms(1-5)]
    by (smt group_cancel.add1 one_add_one)
  thus ?thesis
    using sas_plus_problem_has_serial_solution_iff_ii'[OF valid_problem plan(2,1)]
    by auto
qed

lemma if_there_is_model_then_program_terminates:
  assumes 
    "dom I \<subseteq> set (Max_Constant.all_variables c)"
    "dom G \<subseteq> set (Max_Constant.all_variables c)"
    "Max (ran G) < 2 ^ (t + max_input_bits c I r)"
    (* Mohammad: The following assumption cannot be true for many verifiers. s1 has to depend on I 
                 , otherwise the assumption is vacuous.*)
    "\<And>s1. I \<subseteq>\<^sub>m Some \<circ> s1 \<Longrightarrow> \<exists>s2. \<exists>t' \<le> t. (c, s1) \<Rightarrow>\<^bsup>t'\<^esup> s2"
    "\<A> \<Turnstile> \<Phi>\<^sub>\<forall> (\<phi> prob_with_noop (IMP_Minus_to_SAS_Plus c I r G t))
            100 * (max_input_bits c I r + t + 1) * (t - 1) +
               (max_input_bits c I r + t + 2) *
                  (num_variables c + 2) + 52"
  shows "\<exists>s1 s2 t'. t' \<le> t \<and> I \<subseteq>\<^sub>m Some \<circ> s1 \<and> G \<subseteq>\<^sub>m Some \<circ> s2 \<and> (c, s1)  \<Rightarrow>\<^bsup>t'\<^esup> s2"
proof-
  obtain plan
    where "SAS_Plus_Semantics.is_serial_solution_for_problem (IMP_Minus_to_SAS_Plus c I r G t) plan"
    using sas_plus_problem_has_serial_solution_iff_i'[OF valid_problem assms(5)]    
    by rule
  thus ?thesis
    using assms
    by(auto intro: SAS_Plus_to_IMP_Minus_correctness)
qed

definition t' ::"(nat \<Rightarrow> nat) \<Rightarrow> (nat\<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
  where "t' pt p_cer x = (make_mono pt) (bit_length x + (make_mono p_cer) (bit_length x)) + 1"

 definition imp_to_sat :: "Com.com \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat\<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> sat_plan_formula" where
    "imp_to_sat c pt p_cer x =
      (let I = (Map.empty)(''input'' \<mapsto> x); 
          G = (Map.empty)(''input'' \<mapsto> 0);
          guess_range = x + 1 + 2 * 2 ^ (p_cer (bit_length x));
          max_bits = max_input_bits c I guess_range
      in
        \<Phi>\<^sub>\<forall> (\<phi> prob_with_noop (IMP_Minus_to_SAS_Plus c I guess_range G (t' pt p_cer x)))
           100 * (max_bits + (t' pt p_cer x) + 1) * ((t' pt p_cer  x) - 1) +
             (max_bits + (t' pt p_cer x) + 2) * (num_variables c + 2) + 52)"

lemma main_lemma_hol:
  fixes c pt p_cer in_lang
  assumes "poly pt"
  assumes "poly p_cer"
  assumes verifier_tbounded:
  (*Mohammad: I don't think we need the time to bounded by the cert length since the cert length
              is bounded by input length.*)
    "\<And>s. \<exists>t s'. (c, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and>
                   t \<le> pt (bit_length (s ''input''))"
  assumes verifier_terminates: 
          (*"\<And>x z. \<forall>s. s ''input'' = x \<and> s ''certificate'' = z \<longrightarrow>
                         (\<exists>t s'. (c, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = in_lang x)"*)
          (*Mohammad: The TM needs no access to the certificate since it is non-deterministic, i.e. it can
            assume it is guessed.*)
          (*Mohammad: The computation output should depend on the state, otherwise the theorem
                      statement does not hold*)
          (*Mohammad: We need to specify what it means for c to be a verifier for the certificates*)
          "\<And>x s. \<lbrakk>in_lang x = 0 ; s ''input'' = x\<rbrakk> \<Longrightarrow>
                    (\<exists>z t s'. bit_length z \<le> p_cer (bit_length x) \<and>
                              (c, s(''certificate'' := z)) \<Rightarrow>\<^bsup> t \<^esup> s' \<and>
                              s' ''input'' = in_lang x)"
          "\<And>x s s' t. \<lbrakk>in_lang x \<noteq> 0; s ''input'' = x; (c, s) \<Rightarrow>\<^bsup> t \<^esup> s'\<rbrakk> \<Longrightarrow>
                         s' ''input'' = in_lang x"
  assumes verifier_has_registers:
    "''input'' \<in> set (Max_Constant.all_variables c)"
  shows "\<exists>t_red s_red.
         poly t_red 
       \<and> poly s_red
       \<and> (\<forall>x. \<exists>f.  bit_length (encode_sat f) \<le> s_red ( bit_length x ) \<and> imp_to_sat c pt p_cer x = f
                   \<and> (Sema.sat {f}  \<longleftrightarrow> in_lang x = 0))"
proof -
  define t''::"(char list \<Rightarrow> nat) \<Rightarrow> nat" where
    "t'' s = (make_mono pt) (bit_length (s ''input''))" for s


  have t_bound: "\<exists>t s'. (c, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> t \<le> t'' s" for s
    using verifier_tbounded[of s] order.trans
    by (auto 5 1 simp: t''_def)


  text\<open>Upper bound on the time\<close>

  have t_bound_2: "\<exists>s' t. t \<le> t' pt p_cer  x \<and> (c, s) \<Rightarrow>\<^bsup> t \<^esup> s'"
    if "s ''input'' = x"
    for s x
  proof-    
    obtain t s' where 
      "(c, s) \<Rightarrow>\<^bsup> t \<^esup> s'"
      "t \<le> pt (bit_length (s ''input''))"
      using verifier_tbounded
      by blast+
    have "t'' s \<le> t' pt p_cer (s ''input'')"
      by (auto simp: t'_def t''_def le_make_mono order_trans
               intro!: le_SucI monoD[OF mono_make_mono])
    hence "t \<le> t' pt p_cer (s ''input'')"
      using t_bound \<open>(c, s) \<Rightarrow>\<^bsup> t \<^esup> s'\<close>
      by (smt bigstepT_the_cost less_le_trans not_le)
    thus ?thesis
      using \<open>(c, s) \<Rightarrow>\<^bsup> t \<^esup> s'\<close> that
      by auto
  qed

  have "Sema.sat {imp_to_sat c pt p_cer x}"
    if init: "in_lang x = 0"
    for x
  proof-
    define s where "s \<equiv> (\<lambda>_. 0) (''input'' := x)"
    have "s ''input'' = x"
      by (auto simp add: s_def)
    then obtain z t s'
      where "bit_length z \<le> p_cer (bit_length x)"
            "(c, s(''certificate'' := z)) \<Rightarrow>\<^bsup> t \<^esup> s'"
            "s' ''input'' = in_lang x"
      using verifier_terminates(1)[of x s, OF init]
      by auto
    moreover hence "t'' (s(''certificate'' := z)) \<le> t' pt p_cer x"
      by (auto simp: \<open>s ''input'' = x\<close> t'_def t''_def bit_length_def le_make_mono order_trans
               intro!: le_SucI monoD[OF mono_make_mono])
    hence "t \<le> t' pt p_cer x"
      using t_bound \<open>(c, s(''certificate'' := z)) \<Rightarrow>\<^bsup> t \<^esup> s'\<close>
      by (smt bigstepT_the_cost less_le_trans not_le)
    moreover have "[''input'' \<mapsto> x] \<subseteq>\<^sub>m Some \<circ> s(''certificate'' := z)"
      by (auto simp: s_def map_le_def)
    moreover have "finite (range (s(''certificate'' := z)))"
      by (auto simp: image_def s_def)
    moreover have "z \<le> 2 * 2 ^ p_cer (Discrete.log x)"
      using \<open>bit_length z \<le> p_cer (bit_length x)\<close>
      apply(simp add: bit_length_def)
      by (metis le_iff_add log_exp2_ge mult.commute not_less power_of_two_increase_exponent_le)
    ultimately have "\<exists>\<A>. \<A> \<Turnstile> imp_to_sat c pt p_cer x"
      unfolding Sema.sat_def imp_to_sat_def Let_def
      by (fastforce simp add: s_def bit_length_def map_le_def init
                    intro!: while_program_has_model[of _ "s(''certificate'' := z)" _ _ s' _ t])
    thus ?thesis
      by (auto simp: Sema.sat_def)
  qed

  moreover have "in_lang x = 0"
    if "Sema.sat {imp_to_sat c pt p_cer x}"
    for x
  proof-
    obtain \<A> where "\<A> \<Turnstile> imp_to_sat c pt p_cer x"
      using \<open>Sema.sat {imp_to_sat c pt p_cer x}\<close>
      by (auto simp: Sema.sat_def)
    hence "\<exists>s1 s2 t''. t'' \<le> t' pt p_cer  x \<and> [''input'' \<mapsto> x] \<subseteq>\<^sub>m Some \<circ> s1 \<and>
                       [''input'' \<mapsto> 0] \<subseteq>\<^sub>m Some \<circ> s2 \<and> (c, s1) \<Rightarrow>\<^bsup> t'' \<^esup> s2"
      apply(intro if_there_is_model_then_program_terminates 
                    [where \<A> = \<A> and r = "x + 1 + 2 * 2 ^ (p_cer (bit_length x))"])
      using verifier_has_registers
      by (auto simp: map_le_def imp_to_sat_def Let_def intro: t_bound_2 )
    then obtain s1 s2 t'' 
      where "t'' \<le> t' pt p_cer x" "[''input'' \<mapsto> x] \<subseteq>\<^sub>m Some \<circ> s1"
            "[''input'' \<mapsto> 0] \<subseteq>\<^sub>m Some \<circ> s2" "(c, s1) \<Rightarrow>\<^bsup> t'' \<^esup> s2"
      by auto
    moreover hence "s2 ''input'' = 0" "s1 ''input'' = x"
      by (auto simp: map_le_def)
    ultimately show "in_lang x = 0"
      using verifier_terminates(2)
      by fastforce
  qed

  ultimately show ?thesis
    sorry
qed

definition decode_sat :: "nat \<Rightarrow> nat three_sat" where
  "decode_sat n = undefined"

interpretation encode_decode_sat encode_sat decode_sat
  sorry

subsubsection \<open>Synthesizing the IMP- Program\<close>

lemma main_lemma_synth : 
  fixes c pt p_cer
  assumes "poly pt"
  assumes "poly p_cer"
  assumes "\<forall>s. \<exists>t. Ex (big_step_t (c, s) t) \<and> t \<le> 
                      pt (bit_length (s ''input'') + bit_length (s ''certificate''))"
  assumes "\<forall>x z. \<exists>r. \<forall>s. s ''input'' = x \<and> s ''certificate'' = z \<longrightarrow>
                         (\<exists>t s'. (c, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = r)"
  shows "\<exists>imp_to_sat t_red s_red.
         poly t_red 
       \<and> poly s_red
       \<and> (\<forall>s t s'. (imp_to_sat,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s ''certificate'' = s' ''certificate'')
       \<and> (\<forall>x. \<exists>f.    bit_length f \<le> s_red ( bit_length x )
                   \<and> (\<forall>s. s ''input'' = x \<longrightarrow> (\<exists>t s'. (imp_to_sat,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> 
                                          s' ''input'' = f \<and> t \<le> t_red(bit_length x)))
                   \<and> ( f \<in> IMP_SAT \<longleftrightarrow>
                                        (\<exists>z. bit_length z \<le> p_cer (bit_length x) \<and>
                                                      (\<forall>s t s'. s ''input'' = x 
                                                      \<and> s ''certificate'' = z 
                                                      \<and>(c, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s' ''input'' = 0))
                                        )
                      )"
  sorry


subsubsection \<open>Instantiating the Cook_Levin locale\<close>

(*interpretation Cook_Levin_assumes_Main_lemma encode_sat decode_sat
  apply standard
  by (fact main_lemma_synth) 
   
term strict_sorted*)

end