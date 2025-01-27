subsection\<open>The reduction from \<open>3CNF-SAT\<close> To \<open>Set Cover\<close> is polynomial\<close>
theory THREE_COL_To_CHRN_Poly
  imports
    Polynomial_Reductions
    THREE_COL_To_CHRN
begin

definition "size_nodes_of_three_col = (\<lambda>(E). card (\<Union>E))"
definition "size_chrN = (\<lambda>(E,k). card E)"
definition "mop_set_empty_set = REST [ {} \<mapsto> 1]"
definition "mop_amount_nodes E = SPECT [ card (\<Union>(E))+3 \<mapsto> 1 ]"

definition "translate_graph E S=
  SPECT [ S \<union> {{(v1::nat,0::nat),(v2,0)}|v1 v2. {v1,v2}\<in> E} \<mapsto> card (\<Union>E) * card (\<Union>E)]"

definition "add_complete_graph E S =
  SPECT [ S \<union> {{(0::nat,k),(0::nat,k')}|k k'. k \<in> {1..(card (\<Union>E))} \<and> k' \<in> {1..(card (\<Union>E))} \<and> k \<noteq> k'} \<mapsto>
          ((card (\<Union>E)) * ((card (\<Union>E))-1)) div 2]"

definition "connect_graphs E S =
  SPECT [ S \<union> {{(v1,0::nat),(0::nat,k)}|v1 k. v1\<in> (\<Union> E) \<and> k \<in> {1..(card (\<Union>E))}} \<mapsto> card (\<Union>E) * card (\<Union>E)]"

definition three_col_to_chrn ::
  "nat set set \<Rightarrow> (((nat \<times> nat) set set) \<times> nat) nrest" where
  "three_col_to_chrn = (\<lambda>E. do {
      b \<leftarrow> SPECT [ ugraph E \<mapsto> 1];
      if b then
        do {
          k \<leftarrow> mop_amount_nodes E;
          S \<leftarrow> mop_set_empty_set;
          S \<leftarrow> translate_graph E S;
          S \<leftarrow> add_complete_graph E S;
          S \<leftarrow> connect_graphs E S;
          RETURNT (S,k)
        }
      else RETURNT (({},0))
    })"


(*FIXME: wrong size function*)
definition "size_SAT xs = length xs"
definition "three_col_to_chrn_time n =  1 + 1 + 1 + (n*n)+ (n*n) + (n*n)"
definition "three_col_to_chrn_space n = (n*n)+ (n*n) + (n*n)"


lemma finite_chrn_split1:
"finite (\<Union>E) \<Longrightarrow> finite {{(v1, 0), (v2, 0)} |v1 v2. v1 \<in> \<Union> E \<and> v2 \<in> \<Union> E} "
proof -
  assume asms: "finite (\<Union>E)"
  let ?S = "(((\<Union>E)\<times>{0}) \<times> (\<Union> E\<times> {0}))"
  from asms show ?thesis by (fastforce intro: finite_surj[where A = "?S"])
qed


lemma chro_part_sml_card: " (x::nat) * (x - 1) div 2 + x \<le> x* x"
  by (metis div_le_dividend le_square mult.comm_neutral
      ordered_cancel_comm_monoid_diff_class.le_diff_conv2 right_diff_distrib')

lemma three_col_to_chrn_refines:
  "three_col_to_chrn E \<le> SPEC (\<lambda>y. y = THREE_COL_To_CHRN.three_col_to_chrn E) (\<lambda>_. enat (three_col_to_chrn_time
    (size_nodes_of_three_col E)))"
  unfolding SPEC_def
  unfolding three_col_to_chrn_time_def three_col_to_chrn_def THREE_COL_To_CHRN.three_col_to_chrn_def
       mop_amount_nodes_def mop_set_empty_set_def translate_graph_def add_complete_graph_def connect_graphs_def
  apply(rule T_specifies_I)
  apply(vcg' \<open>-\<close> rules: T_SPEC )
  apply (auto simp: size_nodes_of_three_col_def one_enat_def ugraph_def)
  by (metis diff_le_self div_le_dividend le_trans right_diff_distrib')


lemma chrNgraph_size_eval:"size_chrN (THREE_COL_To_CHRN.three_col_to_chrn E) \<le>card (\<Union> E) * card (\<Union> E) +
                                                        card (\<Union> E) * card (\<Union> E) +
                                                        card (\<Union> E) * card (\<Union> E)"
proof (cases "ugraph E")
  case T:True
  define E_trans where E_trans_def:"E_trans= {{(v1::nat,0::nat),(v2,0)}|v1 v2. {v1,v2}\<in> E}"
  define connect where connect_def:"connect= {{(v1,0),(0,k)}|v1 k. v1\<in> (\<Union> E) \<and> k \<in> {1..(card (\<Union>E))}}"
  define graph_complete where graph_complete_def:"graph_complete=
    {{(0::nat,k),(0,k')}|k k'. k \<in> {1..(card (\<Union>E))} \<and> k' \<in> {1..(card (\<Union>E))} \<and> k \<noteq> k'}"

  from T have size_split:"size_chrN (THREE_COL_To_CHRN.three_col_to_chrn E) = card (
              E_trans \<union>
              connect \<union>
              graph_complete)"
    unfolding THREE_COL_To_CHRN.three_col_to_chrn_def size_chrN_def graph_complete_def connect_def E_trans_def
    by simp

  from T have finiteNodes:"finite (\<Union>E)"
    unfolding ugraph_def
    using finite_Union by fastforce


  from T chromatik_finite1 have fin1: "finite E_trans"
    unfolding E_trans_def
    by blast

  from finiteNodes chromatik_finite2 have fin2: "finite connect"
    unfolding connect_def
    by blast

  from finiteNodes chromatik_finite3 have fin3: "finite graph_complete"
    unfolding graph_complete_def
    by blast

  from chromatik_card1 T have card1:"card E_trans = card E"
    unfolding E_trans_def
    by blast

  from chromatik_card3 finiteNodes have card2:"card connect = card (\<Union>E) * card (\<Union>E)"
    unfolding connect_def
    by blast

  from chromatik_card4 finiteNodes have card3:"card graph_complete = card (\<Union>E) * (card (\<Union>E)-1) div 2"
    unfolding graph_complete_def
    by blast

  have "\<And>e. e\<in>connect \<Longrightarrow> e\<notin> E_trans"
  proof -
    fix e
    assume "e\<in> connect"
    from this obtain k where k_def:"(0,k)\<in> e \<and> k \<in>{1..card (\<Union> E)} "
      unfolding connect_def
      by blast
    have "\<forall> e'\<in> E_trans. \<forall> a b. (a,b) \<in> e'  \<longrightarrow> b = 0"
      unfolding E_trans_def
      by blast
    from this k_def have "\<forall>e'\<in>E_trans. (0, k) \<notin> e'"
      by auto
    from k_def this show "e\<notin> E_trans"
      by blast
  qed

  from this have disjoint1:"E_trans \<inter> connect = {}"
    by blast

  have disjoint2:"E_trans \<inter> graph_complete = {}"
    unfolding E_trans_def graph_complete_def
    by fastforce


  have "\<And>e. e\<in>connect \<Longrightarrow> e\<notin> graph_complete"
  proof -
    fix e
    assume "e\<in> connect"
    from this obtain v where v_def:"(v,0)\<in> e \<and> v \<in> (\<Union> E) "
      unfolding connect_def
      by blast
    have "\<forall> e'\<in> graph_complete. \<forall> a b. (a,b) \<in> e'  \<longrightarrow> b \<in> {1..card (\<Union> E)}"
      unfolding graph_complete_def
      by blast
    from this v_def have "\<forall>e'\<in>graph_complete. (v, 0) \<notin> e'"
      by auto
    from v_def this show "e\<notin> graph_complete"
      by blast
  qed

  from this have disjoint3:"connect \<inter> graph_complete = {}"
    by blast

  from disjoint1 disjoint2 disjoint3 fin1 fin2 fin3 have
    " card (E_trans \<union> connect \<union> graph_complete) =
      card E_trans + card connect + card graph_complete"
    by (simp add: card_Un_disjoint inf_sup_distrib2)

  from this size_split card1 card2 card3 have split_card:
    "size_chrN (THREE_COL_To_CHRN.three_col_to_chrn E) = card E +
                                   (card (\<Union> E) * card (\<Union> E)) +
                                   (card (\<Union> E) * (card (\<Union> E) - 1) div 2)"
    by presburger


  define E_complete where E_complete_def: "E_complete = {{(v1::nat,0::nat),(v2,0)}|v1 v2. v1\<in> \<Union>E \<and> v2\<in> \<Union>E}"

  have E_complete_card:"finite (\<Union> E) \<Longrightarrow> card E_complete = (card (\<Union>E) * (card (\<Union>E)-1) div 2) + card (\<Union>E)"
  unfolding E_complete_def
  proof (induction "card (\<Union>E)" arbitrary: E)
    case 0
    from this have "\<Union>E = {}"
      by simp
    show ?case
      by (simp add: \<open>\<Union> E = {}\<close>)
  next
    case (Suc x)
    from Suc(2) have "\<Union>E \<noteq> {}"
      by fastforce
    from this Suc(2) Suc(3) obtain E' v where E'_def:
      "\<Union>E = \<Union>E' \<union> {v} \<and> \<Union>E' \<inter> {v} = {}"
      unfolding ugraph_def
      by (metis Int_empty_right Int_insert_right_if0
          Un_empty_right Un_insert_right all_not_in_conv
          ccpo_Sup_singleton mk_disjoint_insert)
    from E'_def Suc(2) have E'_card:"card (\<Union>E') = x"
      using Suc.prems by auto
    from Suc(3) E'_def have finE':"finite (\<Union>E')"
      by simp
    define graph where graph_def: "graph = {{(v1, 0::nat), (v2, 0)} |v1 v2. v1 \<in> \<Union> E \<and> v2 \<in> \<Union> E}"
    define split1 where split1_def: "split1 = {{(v1, 0::nat), (v2, 0)} |v1 v2. v1 \<in> \<Union> E' \<and> v2 \<in> \<Union> E'}"
    define split2 where split2_def: "split2 = {{(v1, 0::nat), (v2, 0)} |v1 v2. v1 \<in> \<Union> E' \<and> v2 =v}"
    define split3 where split3_def: "split3 = {{(v1, 0::nat), (v2, 0)} |v1 v2. v1 = v \<and> v2 \<in> \<Union> E'}"
    define split4 where split4_def: "split4 = {{(v1, 0::nat), (v2, 0)} |v1 v2. v1 = v \<and> v2 = v}"

    from split2_def have split2_def': "split2 = {{(v1, 0::nat), (v, 0)} |v1. v1 \<in> \<Union> E'}"
      by fastforce
    from split3_def have split3_def': "split3 = {{(v, 0::nat), (v2, 0)} |v2. v2 \<in> \<Union> E'}"
      by fastforce
    from split2_def' split3_def' have sp2sp3_eq:"split2 = split3"
      by blast
    from split4_def have split4_def':"split4 = {{(v, 0::nat), (v, 0)}}"
      by blast

    define split_step where split_step_def:
      "split_step = {{(v1, 0::nat), (v2, 0)} |v1 v2. (v1 \<in> \<Union>E' \<or> v1 = v) \<and> (v2 \<in> \<Union>E' \<or> v2 = v)}"
    from E'_def have "{{(v1, 0), (v2, 0)} |v1 v2. v1 \<in> \<Union>E \<and> v2 \<in> \<Union>E} =
                  {{(v1, 0), (v2, 0)} |v1 v2. (v1 \<in> \<Union>E' \<or> v1 = v) \<and> (v2 \<in> \<Union>E' \<or> v2 = v)}"
      by auto
    from this have sp_1:" graph = split_step"
      unfolding split_step_def graph_def
      by blast

    have sp_2:"split_step =
          {{(v1, 0::nat), (v2, 0)} |v1 v2. v1 \<in> \<Union> E' \<and> v2 \<in> \<Union> E'} \<union>
          {{(v1, 0::nat), (v2, 0)} |v1 v2. v1 \<in> \<Union> E' \<and> v2 =v} \<union>
          {{(v1, 0::nat), (v2, 0)} |v1 v2. v1 = v \<and> v2 \<in> \<Union> E'} \<union>
          {{(v1, 0::nat), (v2, 0)} |v1 v2. v1 = v \<and> v2 = v}"
      unfolding split_step_def
      by fast

    from sp_1 sp_2 have "graph = split1 \<union> split2 \<union> split3 \<union> split4"
      by (simp add: split1_def split2_def split3_def split4_def)

    from this sp2sp3_eq have graph_split:
      "graph = split1 \<union> split2 \<union> split4"
      by auto

    from Suc(1)[where E= E'] finE' E'_card split1_def have card1:
      "card split1 = (card (\<Union>E') * (card (\<Union>E')-1) div 2) + card (\<Union>E')"
      by auto
    from split2_def' have card2: "card split2 = card (\<Union>E')"
      using card_one_para2 finE' sp2sp3_eq split3_def' by fastforce
    have card3: "card split4 = 1"
      unfolding split4_def
      by force
    from E'_def have vNotinE'nodes:"v\<notin> \<Union>E'"
      by blast
    have "\<And>e. e\<in>split2 \<Longrightarrow> e\<notin> split1"
    proof -
      fix e
      assume "e\<in> split2"
      from this have vIn_e:"(v,0)\<in> e"
        unfolding split2_def'
        by blast
      have "\<forall> e'\<in> split1. \<forall>v'.(v',0) \<in> e' \<longrightarrow> v'\<in>\<Union>E'"
        unfolding split1_def
        by blast
      from this vNotinE'nodes have "\<forall>e'\<in>split1. (v, 0) \<notin> e'"
        by blast
      from vIn_e this show "e\<notin> split1"
        by blast
    qed
    from this have disjoint1: "split1 \<inter> split2 = {}"
      by blast

    from vNotinE'nodes have disjoint2: "split1 \<inter> split4 = {}"
      unfolding split1_def split4_def'
      by simp

    from vNotinE'nodes have disjoint3: "split2 \<inter> split4 = {}"
      unfolding split2_def split4_def'
      by simp

    from finE' have fin1: "finite split1"
      unfolding split1_def
      using finite_chrn_split1
      by blast

    from finE' have fin2: "finite split2"
      unfolding split2_def'
    proof -
      have "\<forall>f N. finite {r. \<exists>n. (r::(nat \<times> nat) set) = f (n::nat) \<and> n \<in> N} \<or> infinite N"
        by force
      then show "finite {{(n, 0::nat), (v, 0)} |n. n \<in> \<Union> E'}"
        by (meson finE')
    qed

    have fin3: "finite split4"
      unfolding split4_def'
      by blast

    from graph_split disjoint1 disjoint2 disjoint3 fin1 fin2 fin3 have
      "card graph = card split1 + card split2 + card split4"
      by (simp add: card_Un_disjoint inf_sup_distrib2)

    from this card1 card2 card3 E'_card have "card graph = (x * (x-1) div 2 + x) + x + 1"
      by argo


    from this have card_graph:"card graph =  ((x * (x-1)) + 2 *x) div 2 + Suc x"
      by simp
    have "((x * (x-1)) + 2 *x) = x* (x +1)"
      by (auto simp : right_diff_distrib')
    from this card_graph have "card graph = ((Suc x) * (x)) div 2 + Suc x"
      by simp
    from this Suc(2) show ?case
      unfolding graph_def
      by (metis diff_Suc_1)
  qed



  have finE_complete:"finite E_complete"
    unfolding E_complete_def
    using finiteNodes finite_chrn_split1 by blast

  have subset1:"E_trans \<subseteq> E_complete"
    unfolding E_complete_def E_trans_def
    by blast


  from finiteNodes subset1 E_complete_card card1 have chrN_card_sml1:
    "card E \<le> card (\<Union> E) * (card (\<Union> E) - 1) div 2 + card (\<Union> E)"
  proof -
    from subset1 finE_complete have "card E_trans \<le> card E_complete"
      using Finite_Set.card_mono
      by blast
    from this card1 E_complete_card finiteNodes show ?thesis
      by metis
  qed

  have chrN_card_sml2:"card (\<Union> E) * (card (\<Union> E) - 1) div 2 + card (\<Union> E) \<le> card (\<Union> E)* card (\<Union> E) "
    using chro_part_sml_card
    by blast

  from chrN_card_sml1 chrN_card_sml2 have chrN_card_sml3:"card E \<le>  card (\<Union> E)* card (\<Union> E)"
    by linarith

  from split_card chrN_card_sml3 show ?thesis
    apply auto
    by (metis One_nat_def add_le_mono div_le_dividend mult.commute mult_eq_if trans_le_add2)
next
  case False
  from this have "size_chrN (THREE_COL_To_CHRN.three_col_to_chrn E) = card {}"
    unfolding THREE_COL_To_CHRN.three_col_to_chrn_def size_chrN_def by simp
  then show ?thesis by simp
qed


lemma three_col_to_chrn_size:
  "size_chrN (THREE_COL_To_CHRN.three_col_to_chrn E) \<le> three_col_to_chrn_space (size_nodes_of_three_col E)"
  using chrNgraph_size_eval
  unfolding three_col_to_chrn_space_def size_nodes_of_three_col_def
  by blast

theorem three_col_to_chrn_ispolyred: "ispolyred three_col_to_chrn three_colorability chromatic_number size_nodes_of_three_col size_chrN"
  unfolding ispolyred_def
  apply(rule exI[where x=THREE_COL_To_CHRN.three_col_to_chrn])
  apply(rule exI[where x=three_col_to_chrn_time])
  apply(rule exI[where x=three_col_to_chrn_space])
  apply(safe)
  subgoal using three_col_to_chrn_refines
    by simp
  subgoal using three_col_to_chrn_size
    by simp
  subgoal unfolding poly_def three_col_to_chrn_time_def apply(rule exI[where x=2]) by auto
  subgoal unfolding poly_def three_col_to_chrn_space_def apply(rule exI[where x=2]) by auto
  using is_reduction_three_col_chrn
  apply (simp add:is_reduction_def)
done

end