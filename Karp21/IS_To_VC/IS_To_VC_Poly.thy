theory IS_To_VC_Poly
  imports
    IS_To_VC
    THREE_SAT_To_IS_Poly
begin

definition "size_VC = (\<lambda>(E,k). card E)"

subsubsection \<open>\<open>Independent Set\<close> To \<open>Vertex Cover\<close>\<close>

paragraph \<open>A trivial implementation\<close>

text \<open>Here we assume that we have an operation that returns
      the size of the set of vertices.\<close>

definition "mop_get_vertices E = REST [ (\<Union> E)  \<mapsto> 2 * card E + 1]"

definition "mop_get_vertices_card E = REST [(card (\<Union> E)) \<mapsto> 2 * card E + 2]"

text \<open>Then we can easily give an abstract algorithm for the reduction:\<close>

definition "is_to_vc = (\<lambda>(E,k).
          do {
            s \<leftarrow> mop_get_vertices_card E;
            if k > s  then
              RETURNT (E,k)
            else
              RETURNT (E, s-k)
          })"

definition "vc_time n = 2 * n + 2"
definition "vc_space n = n"


lemma is_to_vc_refines:
  "is_to_vc vc \<le> SPEC (\<lambda>y. y = is_vc vc) (\<lambda>_. vc_time (size_IS vc))"
  unfolding is_to_vc_def is_vc_def SPEC_def mop_get_vertices_card_def
  apply(rule T_specifies_I)
  apply(vcg' \<open>-\<close>)
  by (auto simp: size_IS_def size_VC_def vc_time_def vc_space_def)

lemma is_to_vc_size:
  "size_VC (is_vc a) \<le> vc_space (size_IS a)"
  apply(cases a)
  by (auto simp: is_vc_def size_IS_def size_VC_def vc_time_def vc_space_def)

thm is_reduction_is_vc


text \<open>And we show that it actually is a polynomial reduction:\<close>

theorem is_to_vc_ispolyred: "ispolyred is_to_vc independent_set vertex_cover size_IS size_VC"
  unfolding ispolyred_def
  apply(rule exI[where x=is_vc])
  apply(rule exI[where x=vc_time])
  apply(rule exI[where x=vc_space])
  apply(safe)
  subgoal using is_to_vc_refines by blast
  subgoal using is_to_vc_size  by blast
  subgoal unfolding poly_def vc_time_def apply(rule exI[where x=1]) by auto
  subgoal unfolding poly_def vc_space_def apply(rule exI[where x=1]) by simp
  subgoal using is_reduction_is_vc .
  done



paragraph \<open>A more fine grained algorith\<close>

text \<open>now we assume to only have more fine grained basic operations.\<close>

text \<open>This setup is actually unrealistic, it is hard to imagine a datastructure with
  constant insertion and constant cardinality query.
     TODO: make cost of insert linear in size of S\<close>

definition "mop_set_insert S s = REST [insert s S \<mapsto> 1]"

definition "mop_set_card S  = REST [card S \<mapsto> 1]"



text \<open>Now we want to work on lists of tuples to represent the Edge set:\<close>

definition "R_edge_set_tuple_list = {(xs,E) |xs E. ((\<lambda>(a,b). {a,b}) ` (set xs) = E \<and> distinct xs
           \<and> inj_on (\<lambda>(a,b). {a,b}) (set xs)  )}"
text \<open>here the constraint @{term inj_on} means, that the edge list xs
       does not contain any loops ( (a,a) ),
        or both symmetric edges ( (a,b)\<in>set xs \<and> (b,a)\<in>set xs )\<close>


text \<open>we can restate the specification to get the cardinality of the set of vertices given
      an edge list, and that it refines the operation @{term mop_get_vertices_card}\<close>

definition "mop_get_vertices_card' xs = REST [(card (\<Union> ((\<lambda>(a,b). {a,b}) ` (set xs)))) \<mapsto> 2 * length xs + 2]"

lemma mop_get_vertices_card_data_refine:
  assumes "(xs,E)\<in>R_edge_set_tuple_list"
  shows "mop_get_vertices_card' xs \<le> mop_get_vertices_card E"
proof -
  from assms have E: "E = (\<lambda>(a,b). {a,b}) ` (set xs)"
     and *: "distinct xs""inj_on (\<lambda>(a,b). {a,b}) (set xs)"
    unfolding R_edge_set_tuple_list_def by auto
  have **: "card E = length xs"
    by(simp add: card_image distinct_card E *)
  show ?thesis
    unfolding mop_get_vertices_card'_def mop_get_vertices_card_def
    unfolding ** by(simp add: E)
qed

text \<open>now let's implement getting the cardinality of V with the basic set operations\<close>

definition "mop_get_vertices' es = SPECT [\<Union> ((\<lambda>(a,b). {a,b}) ` (set es)) \<mapsto> 2 * length es + 1]"

definition get_vertices where
  "get_vertices es =
    do { S \<leftarrow> mop_set_empty_set;
      S' \<leftarrow> nfoldli es (\<lambda>_. True)
            (\<lambda>(a,b) S. do {
                  S \<leftarrow> mop_set_insert S a;
                  S \<leftarrow> mop_set_insert S b;
                  RETURNT S })

        S;
      RETURNT S'
  }"


lemma get_vertices_refine:
  "get_vertices xs \<le> mop_get_vertices' xs"
proof -
  let ?I = "\<lambda>(xs::('b*'b)list) ys (S::'b set).  S = \<Union> ((\<lambda>(a,b). {a,b}) ` (set xs))"

  show ?thesis
  unfolding get_vertices_def mop_get_vertices'_def
  apply(rule T_specifies_I)
  apply(subst nfoldliIE_def[symmetric, where I="?I" and E=2])
  unfolding mop_set_empty_set_def
  apply(vcg' -)
  apply(rule nfoldliIE_rule[THEN T_specifies_rev, THEN T_conseq4, where P2="?I xs []" ])
       apply simp
  subgoal
    apply(rule T_specifies_I)
    unfolding mop_set_insert_def
    apply(vcg' -)
    apply auto unfolding Some_le_emb'_conv
    by auto
     apply simp
    apply simp
  apply (rule order.refl)
  unfolding mop_set_card_def
  apply (vcg' -) apply auto unfolding Some_le_emb'_conv Some_eq_emb'_conv
   apply (auto simp add: one_enat_def)
  done
qed

definition get_vertices_card :: "('b*'b) list \<Rightarrow> nat nrest" where
  "get_vertices_card es = do {
      V \<leftarrow> get_vertices es;
      n \<leftarrow> mop_set_card V;
      RETURNT n
    }"

thm get_vertices_refine[unfolded mop_get_vertices'_def,
                THEN T_specifies_rev, THEN T_conseq4]

lemma get_vertices_card_refine:
  "get_vertices_card xs \<le> mop_get_vertices_card' xs"
  unfolding get_vertices_card_def mop_get_vertices_card'_def
  apply(rule T_specifies_I)
  apply(vcg' - rules: get_vertices_refine[unfolded mop_get_vertices'_def,
                THEN T_specifies_rev, THEN T_conseq4])
  unfolding mop_set_card_def
  apply (vcg' -) unfolding Some_le_emb'_conv Some_eq_emb'_conv
  by (auto simp add: one_enat_def split: if_splits)


lemma get_vertices_card_data_refine:
  assumes "(xs,E)\<in>R_edge_set_tuple_list"
  shows "get_vertices_card xs \<le>  (mop_get_vertices_card E)"
  apply(rule order.trans)
  apply(rule   get_vertices_card_refine)
  apply(rule mop_get_vertices_card_data_refine)
  by fact

text \<open>now we can give a refined algorithm, only using the fine grained operations:\<close>

definition "is_to_vc2 = (\<lambda>(xs,k).
          do {
            s \<leftarrow> get_vertices_card xs;
            if k > s  then
              RETURNT (xs,k)
            else
              RETURNT (xs, s-k)
          })"


lemma R_reintro: "A \<le>   B \<Longrightarrow> A \<le> \<Down>Id B" by simp

term " prod_rel R_edge_set_tuple_list Id"
lemma is_to_vc2_refines:
  "((xs,k),(E,k)) \<in> R_edge_set_tuple_list \<times>\<^sub>r Id
     \<Longrightarrow> is_to_vc2 (xs,k) \<le> \<Down> (R_edge_set_tuple_list \<times>\<^sub>r Id) (is_to_vc (E,k))"
  unfolding is_to_vc_def is_to_vc2_def
  apply (refine_rcg get_vertices_card_data_refine[THEN R_reintro] )
  subgoal by (auto simp: prod_rel_def_internal)
  subgoal by (auto simp: prod_rel_def_internal)
  subgoal by (auto simp: RETURNT_refine prod_rel_def_internal)
  subgoal by(auto intro!: RETURNT_refine simp: prod_rel_def_internal)
  done
lemma is_to_vc2_refines':
  "(i',i) \<in> R_edge_set_tuple_list \<times>\<^sub>r Id
     \<Longrightarrow> is_to_vc2 i' \<le> \<Down> (R_edge_set_tuple_list \<times>\<^sub>r Id) (is_to_vc i)"
  unfolding is_to_vc_def is_to_vc2_def
  apply (refine_rcg get_vertices_card_data_refine[THEN R_reintro] )
  subgoal by (auto simp: prod_rel_def_internal)
  subgoal by (auto simp: prod_rel_def_internal)
  subgoal by (auto simp: RETURNT_refine prod_rel_def_internal)
  subgoal by(auto intro!: RETURNT_refine simp: prod_rel_def_internal)
  done


thm ispolyredd_refine[OF is_to_vc_ispolyred[THEN ispolyredd_generalizes_ispolyredD] is_to_vc2_refines' ]
    is_to_vc2_refines

text \<open>Finally we can show that the new algorithm also is a polynomial reduction acting on
      lists of tuples instead of an abstract edge set\<close>

theorem "ispolyredd is_to_vc2
       (R_edge_set_tuple_list \<times>\<^sub>r nat_rel) (R_edge_set_tuple_list \<times>\<^sub>r nat_rel)
        independent_set vertex_cover size_IS size_VC"
  unfolding independent_set_def vertex_cover_def
  apply(rule ispolyredd_refine[OF is_to_vc_ispolyred[THEN ispolyredd_generalizes_ispolyredD], simplified])
  apply(rule is_to_vc2_refines' ) .


end