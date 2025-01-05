theory THREE_SAT_To_IS_poly
  imports "../Polynomial_Reductions" "THREE_SAT_To_IS"
begin

definition "size_IS = (\<lambda>(E,k). card E)"

subsubsection \<open>\<open>3CNF-SAT\<close> To \<open>Independent Set\<close>\<close>

definition "mop_list_length xs = SPECT [ length xs \<mapsto> 1 ]"
definition "mop_set_empty_set = REST [ {} \<mapsto> 1]"

definition "add_first_part F S = 
  SPECT [ S \<union> {{(l1, i), (l2, i)} | l1 l2 i. i < length F \<and> l1 \<in> F ! i \<and> l2 \<in> F ! i \<and> l1 \<noteq> l2} \<mapsto> 3 * length F]"

      
definition "add_second_part F S = 
  SPECT [ S \<union> {{(l1, i), (l2, j)} | l1 l2 i j.
      i < length F \<and> j < length F \<and> l1 \<in> F ! i \<and> l2 \<in> F ! j \<and> conflict l1 l2}
       \<mapsto> 3 * length F * length F]"



definition sat_to_is :: "'a lit set list \<Rightarrow> (('a lit \<times> nat) set set \<times> nat) nrest" where 
  "sat_to_is = (\<lambda>F. do {
      b \<leftarrow> SPECT [ (\<forall>cls \<in> set F. card cls = 3) \<mapsto> 1];
      if b then
        do {
          l \<leftarrow> mop_list_length F; 
          S \<leftarrow> mop_set_empty_set;
          S \<leftarrow> add_first_part F S;
          S \<leftarrow> add_second_part F S;
          RETURNT ( S, l)
        }
      else RETURNT ( {}, 1 )
    })"

definition "size_SAT xs = length xs"
definition "sat_to_is_time n = 3 + 3 * n + 3 * n * n"

lemma sat_to_is_refines:
  "sat_to_is F \<le> SPEC (\<lambda>y. y = sat_is F) (\<lambda>_. sat_to_is_time (size_SAT F))"
  unfolding SPEC_def
  unfolding sat_to_is_def sat_is_def   
      mop_list_length_def mop_set_empty_set_def add_first_part_def
      add_second_part_def
  apply(rule T_specifies_I) 
  apply(vcg' \<open>-\<close> rules: T_SPEC )
  by (auto simp: sat_to_is_time_def size_SAT_def one_enat_def)

definition "sat_to_is_space n = 9 * n + 9 * n * n"


lemma paf2: "{f l1 l2 i j |l1 l2 i j. i < k \<and> g l1 l2 i j} 
    = (\<Union>i \<in> {..<k::nat}. {f l1 l2 i j |l1 l2 j. g l1 l2 i j}) "
  by auto

lemma paf: "{f l1 l2 i |l1 l2 i. i < j \<and> g l1 l2 i} 
    = (\<Union>i \<in> {..<j::nat}. {f l1 l2 i |l1 l2. g l1 l2 i})"
  by auto 

lemma brr:
  shows "{{f l1, g l2} |l1 l2. l1 \<in> X \<and> l2 \<in> Y \<and> h l1 l2} \<subseteq> (\<Union>x \<in> X. \<Union>y \<in> Y. {{f x, g y}})"
  (is "?lhs \<subseteq> ?rhs")
proof -
  have "?lhs \<subseteq> {{f l1, g l2} |l1 l2. l1 \<in> X \<and> l2 \<in> Y}" by auto
  also have "\<dots> = (\<Union>x \<in> X. {{f x, g l2} |l2. l2 \<in> Y})" by auto
  also have "\<dots> = ?rhs" by auto
  finally show ?thesis .
qed


lemma aaa: "\<forall>x\<in>X. card x = 3 \<Longrightarrow> x\<in>X \<Longrightarrow> finite x" 
  using zero_neq_numeral by fastforce  


lemma upperbounding_card3: "\<forall>x\<in>X. card x = 3 \<Longrightarrow> x\<in>X \<Longrightarrow> y\<in>X \<Longrightarrow> 
        card {{f l1, g l2} |l1 l2. l1 \<in> x \<and> l2 \<in> y \<and> h l1 l2} \<le> 9"

      apply(rule order.trans)
       apply(rule card_mono) defer
        apply(rule brr)
   apply(rule order.trans)
    apply(rule card_Union_le_sum_card)     
       apply(rule order.trans) apply(rule sum_image_le)
      subgoal using aaa by auto
        apply simp  apply(rule order.trans)
      apply(rule sum_mono[where g="\<lambda>_. 3"]) apply simp 
        apply(rule order.trans) apply(rule card_Union_le_sum_card)
       apply(rule order.trans) apply(rule sum_image_le) 
      subgoal using aaa by auto
         apply simp apply simp apply simp 
      apply(rule finite_Union)
       apply (rule finite_imageI) using aaa by auto 



lemma sat_to_is_size: "size_IS (sat_is p) \<le> sat_to_is_space (size_SAT p)" 
  apply(auto simp: size_IS_def sat_is_def sat_to_is_space_def size_SAT_def)
  apply(rule order.trans[OF card_Un_le])
  apply(rule add_mono)
  subgoal
    apply(subst paf)
    apply(rule order.trans) apply(rule card_Union_le_sum_card) apply simp
    apply(rule order.trans)
     apply(rule sum_image_le) apply simp
     apply simp
    apply(rule order.trans) apply(rule sum_mono[where g="(\<lambda>_. 9)"] )
    subgoal for i apply simp
      apply(rule upperbounding_card3) by auto
    apply simp
    done

  subgoal
    apply(subst paf2)
    apply(subst paf)
    apply(rule order.trans) apply(rule  card_Union_le_sum_card) apply simp
    apply(rule order.trans)
     apply(rule sum_image_le) apply simp apply simp
    apply(rule order.trans)
     apply(rule sum_mono[where g="\<lambda>_. 9 * length p"])
    subgoal apply simp
    apply(rule order.trans) apply(rule card_Union_le_sum_card) apply simp
    apply(rule order.trans)
       apply(rule sum_image_le) apply simp apply simp
      apply(rule order.trans)
       apply(rule sum_mono[where g="\<lambda>_. 9"])
      subgoal
        apply simp apply(rule upperbounding_card3) by auto  
      apply simp done  
    subgoal apply simp done
    done
  done
  


theorem sat_to_is_ispolyred: "ispolyred sat_to_is three_cnf_sat independent_set size_SAT size_IS" 
  unfolding ispolyred_def
  apply(rule exI[where x=sat_is])
  apply(rule exI[where x=sat_to_is_time])
  apply(rule exI[where x=sat_to_is_space])
  apply(safe)
  subgoal using sat_to_is_refines by blast
  subgoal using sat_to_is_size  by blast 
  subgoal unfolding poly_def sat_to_is_time_def apply(rule exI[where x=2]) by auto
  subgoal unfolding poly_def sat_to_is_space_def apply(rule exI[where x=2]) by auto
  subgoal using is_reduction_sat_is .
  done


end