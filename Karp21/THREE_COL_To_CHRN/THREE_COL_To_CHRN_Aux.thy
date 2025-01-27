theory THREE_COL_To_CHRN_Aux
  imports
    THREE_SAT_To_THREE_COL
begin

lemma nodes_different: "ugraph E \<Longrightarrow> {{(v1, 0), (v2, 0)} | v1 v2. {v1, v2} \<in> E} =
  {{(v1, 0), (v2, 0)} |v1 v2. {v1, v2} \<in> E \<and> v1 \<noteq> v2} "
  unfolding ugraph_def
  by fastforce

lemma nodes_different2:"ugraph E \<Longrightarrow>  {{(v1, 0), (v2, 0)} |v1 v2. {v1, v2} \<in> E} \<subseteq>
  {{(v1, 0), (v2, 0)} |v1 v2. v1\<in>(\<Union>E) \<and> v2\<in>(\<Union>E) \<and> v1 \<noteq> v2}"
  unfolding ugraph_def
  by (smt Collect_mono_iff Sup_upper card_2_iff doubleton_eq_iff insert_subset)

lemma chromatik_card2:"ugraph E \<Longrightarrow> (\<forall>e\<in>{{(v1, 0), (v2, 0)} |v1 v2. {v1, v2} \<in> E}. card e = 2)"
proof -
  assume asms: "ugraph E"
  from asms have "\<forall> v1 v2. {v1, v2} \<in> E \<longrightarrow> v1 \<noteq> v2"
    unfolding ugraph_def
    by auto
  from this have "\<forall> v1 v2. {v1, v2} \<in> E \<longrightarrow> (v1, 0) \<noteq> (v2, 0)"
    by blast
  from this show ?thesis by force
qed

lemma card_one_para: "card {{(ca, cb), (cc, k)} |k. k \<in> {1..x}} = x"
  by (subst Setcompr_eq_image[of "\<lambda>k. {(ca, cb), (cc, k)}"],
      intro card_image[THEN trans],auto simp add:  inj_on_def doubleton_eq_iff)

lemma card_one_para2: "finite (\<Union>E) \<Longrightarrow> card {{(ca, cb), (v, cc)} |v. v \<in> (\<Union>E)} = card (\<Union>E)"
  by (subst Setcompr_eq_image[of "\<lambda>v. {(ca, cb), (v, cc)}"],
      intro card_image ,auto simp add:  inj_on_def doubleton_eq_iff)

lemma chromatik_card1:"ugraph E \<Longrightarrow> card {{(v1, 0::nat), (v2, 0)} |v1 v2. {v1, v2} \<in> E} =  card E"
proof (induction "card E" arbitrary: E)
  case zero:0
  then show ?case
  proof (cases "E = {}")
    case True
    then show ?thesis
      by simp
  next
    case False
    from this zero(1) have E_infin:"infinite E"
      by fastforce
    from this zero(2) have "False" unfolding ugraph_def
      by blast
    from this show ?thesis
      by simp
  qed
next
  case (Suc x)
  from Suc(2) have E_fin:"finite E"
    using card.infinite by fastforce
  from Suc(2) have "E \<noteq> {}"
    by auto
  from this Suc(2) Suc(3) obtain E' ver1 ver2 where E'_def:
    "E = E' \<union> {{ver1,ver2}} \<and> E' \<inter> {{ver1,ver2}} = {}"
    unfolding ugraph_def
    by (metis Int_empty_right Int_insert_right_if0 Un_empty_right
        Un_insert_right card_2_iff equals0I mk_disjoint_insert)
  from this Suc(2) have E'_card:"card E' = x"
    by (metis Un_empty_right Un_insert_right Zero_not_Suc card.infinite
        card_insert_disjoint disjoint_insert(2) finite_Un old.nat.inject)
  from E'_def E_fin have E'_fin:"finite E'"
    by blast
  from E'_def have E'subE:"E' \<subseteq> E"
    by blast
  from this Suc(3) E'_fin have E'_ugraph:"ugraph E'" unfolding ugraph_def
    by blast
  define E'split1 where E'split1_def: "E'split1 = {{(v1, 0::nat), (v2, 0)} |v1 v2. {v1, v2} \<in> E'}"
  define E'split2 where E'split2_def: "E'split2 = {{(ver1, 0::nat), (ver2, 0)}}"
  from E'_ugraph Suc(1)[where E = E'] E'_card E'split1_def have cardspliteq:"card E'split1 = card E'"
    by blast
  from this E'split1_def have split_fin:"finite E'split1"
    using E'_fin card.infinite by fastforce
  from E'split2_def have cardspliteq2:"card E'split2 = 1"
    by simp

  from E'split2_def have split_fin2:"finite E'split2"
    by blast
  from E'_def have graph_split:"{{(v1, 0::nat), (v2, 0)} |v1 v2. {v1, v2} \<in> E} = E'split1 \<union> E'split2"
    by (auto simp: E'split1_def E'split2_def)
  from E'_def have "E'split1 \<inter> E'split2 = {}"
    apply (simp add: E'split1_def E'split2_def)
    by (metis Pair_inject doubleton_eq_iff)
  from this split_fin split_fin2 card_Un_disjoint have
                   "card (E'split1 \<union> E'split2) = card E'split1 + card E'split2"
    by blast
  from this graph_split have
                   "card {{(v1, 0::nat), (v2, 0)} |v1 v2. {v1, v2} \<in> E} =
                    card E'split1 + card E'split2"
    by presburger
  from this cardspliteq2 cardspliteq have "card {{(v1, 0::nat), (v2, 0)} |v1 v2. {v1, v2} \<in> E} = card E' + 1"
    by argo
  from this E'_card Suc(2)  show ?case
    by presburger
qed

lemma split_nats: "k \<in> {1.. (Suc x)} \<longleftrightarrow> k \<in> {1..(x)} \<or> k = Suc x"
  using le_Suc_eq by auto

lemma finite_chrn1:
"finite (\<Union>E) \<Longrightarrow> finite {{(v1, 0), (0, Suc x)} |v1. v1 \<in> \<Union> E} "
proof -
  assume asms: "finite (\<Union>E)"
  let ?S = "(((\<Union>E)\<times>{0}) \<times> ({0}\<times> {Suc x}))"
  from asms show ?thesis by (fastforce intro: finite_surj[where A = "?S"])
qed


lemma card_para2: "finite (\<Union>E) \<Longrightarrow> card {{(v1, 0), (0, Suc x)} |v1. v1 \<in> \<Union> E} = card (\<Union>E)"
proof (induction "card (\<Union>E)" arbitrary: E)
  case zero:0
  then show ?case
  proof (cases "(\<Union>E) = {}")
    case True
    from this zero show ?thesis
      by (smt card_0_eq card.infinite empty_Collect_eq empty_iff)
  next
    case False
    from this zero(1) have "infinite (\<Union>E)"
      by force
    from this zero(2) have "False"
      by blast
    then show ?thesis by simp
  qed
next
  case (Suc n)
  from Suc(2) have "\<Union>E \<noteq> {}"
    by fastforce
  from this Suc(2) Suc(3) obtain E' v where E'_def:
    "\<Union>E = \<Union>E' \<union> {v} \<and> \<Union>E' \<inter> {v} = {}"
    unfolding ugraph_def
    by (metis Int_empty_right Int_insert_right_if0
        Un_empty_right Un_insert_right all_not_in_conv
        ccpo_Sup_singleton mk_disjoint_insert)
  from E'_def Suc(2) have E'_card:"card (\<Union>E') = n"
    using Suc.prems by auto
  from E'_def have fin_E':"finite (\<Union>E')"
    using Suc.prems by auto

  define split1 where split1_def: " split1 = {{(v1, 0), (0, Suc x)} |v1. v1 \<in> \<Union> E'}"
  define split2 where split2_def: " split2 = {{(v, 0), (0, Suc x)}}"
  from split1_def fin_E' have fin1:"finite split1" using finite_chrn1
    by blast
  from split2_def have fin2:"finite split2"
    by blast
  from E'_def split1_def split2_def have split_dis:"split1 \<inter> split2 = {}"
    by fastforce
  from split1_def fin_E' Suc(1) E'_card have split1_card:"card split1 = n"
    by blast
  from split1_def split2_def E'_def have "{{(v1, 0), (0, Suc x)} |v1. v1 \<in> \<Union> E} = split1 \<union> split2 "
    by auto
  from this fin1 fin2 split_dis have "card {{(v1, 0), (0, Suc x)} |v1. v1 \<in> \<Union> E} = card split1 + card split2"
    using card_Un_disjoint
    by fastforce
  from this split1_card Suc(2) split2_def show ?case
    by simp
qed


lemma chromatik_card3:"finite (\<Union>E) \<Longrightarrow>
  card {{(v1, 0), (0, k)} |v1 k. v1\<in> (\<Union> E) \<and> k \<in> {1..(card (\<Union>E))}} =  card (\<Union>E) * card (\<Union>E)"
proof (induction "card (\<Union> E)" arbitrary: E)
  case zero:0
  then show ?case
  proof (cases "\<Union> E = {}")
    case True
    from this zero show ?thesis
      by auto
  next
    case False
    from this zero(1) have E_infin:"infinite (\<Union> E)"
      by fastforce
    from this zero(2) have "False" unfolding ugraph_def
      using finite_Union by fastforce
    from this show ?thesis
      by simp
  qed
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
  define split1 where split1_def: "split1 = {{(v1, 0::nat), (0, k)} |v1 k. (v1\<in> (\<Union> E') \<and> (k \<in> {1..(x)}))}"
  define split2 where split2_def: "split2 = {{(v, 0::nat), (0, k)} |k. ((k \<in> {1..(x)}))}"
  define split3 where split3_def: "split3 = {{(v1, 0::nat), (0, Suc x)} |v1. (v1\<in> (\<Union> E'))}"
  define split4 where split4_def: "split4 = {{(v, 0::nat), (0, Suc x)}}"
  from E'_def have fin_E':"finite (\<Union>E')"
    using Suc.prems by auto
  from this Suc(1)[where E = E'] E'_card split1_def have split1_card:"card split1 =x*x"
    by blast
  from fin_E' split2_def E'_card have split2_card:"card split2 = x"
    using card_one_para
    by fast
  from fin_E' split3_def E'_card have split3_card:"card split3 = x"
    using card_para2
    by blast
  from split4_def have split4_card:"card split4 = 1"
    by simp
  from split1_def split2_def split3_def split4_def have disjoint1:"(split1 \<union> split2) \<inter> (split3 \<union> split4) = {}"
    by auto
  from  E'_def have disjoint2:"split1 \<inter> split2 = {}"
    apply (simp add: split1_def split2_def)
    by (auto simp: doubleton_eq_iff)
  from E'_def have disjoint3:"split3 \<inter> split4 = {}"
    apply (simp add: split3_def split4_def)
    by fast

  from fin_E' split1_def split1_card have fin1:"finite split1"
    by auto

   from split2_def split2_card have fin2:"finite split2"
     by simp

   from fin_E' split3_def split3_card have fin3:"finite split3"
     by (smt E'_card card_0_eq card.infinite empty_Collect_eq empty_iff finite.emptyI)

  from split4_def split4_card have fin4:"finite split4"
    by blast


  from E'_def Suc(2) have step1:"{{(v1, 0), (0, k)} |v1 k. v1\<in> (\<Union> E) \<and> k \<in> {1..(card (\<Union>E))}} =
        {{(v1, 0), (0, k)} |v1 k. (v1\<in> (\<Union> E') \<or> v1 = v) \<and> (k \<in> {1..Suc(x)}) }"
    by auto
  from E'_def have "{{(v1, 0), (0, k)} |v1 k. (v1\<in> (\<Union> E') \<or> v1 = v) \<and> (k \<in> {1..Suc(x)}) } =
        {{(v1, 0), (0, k)} |v1 k. (v1\<in> (\<Union> E') \<and> (k \<in> {1..(x)}))} \<union>
        {{(v1, 0), (0, k)} |v1 k. (v1 = v \<and> (k \<in> {1..(x)}))}\<union>
        {{(v1, 0), (0, k)} |v1 k. (v1\<in> (\<Union> E') \<and> (k = Suc x))}\<union>
        {{(v1, 0), (0, k)} |v1 k. (v1 = v \<and> (k = Suc x))}"
    using split_nats[where x= x]
    by fast
  from this split1_def split2_def split3_def split4_def have
        "{{(v1, 0), (0, k)} |v1 k. (v1\<in> (\<Union> E') \<or> v1 = v) \<and> (k \<in> {1..Suc(x)}) } =
        split1 \<union> split2 \<union> split3 \<union> split4"
    by simp
  from this fin1 fin2 fin3 fin4 disjoint1 disjoint2 disjoint3 have
       "card {{(v1, 0), (0, k)} |v1 k. (v1\<in> (\<Union> E') \<or> v1 = v) \<and> (k \<in> {1..Suc(x)}) } =
        card split1 + card split2 + card split3 + card split4"
    using card_Un_disjoint
    by (metis (no_types, lifting) Suc_eq_plus1 Un_assoc add_Suc_right finite_UnI split4_card)
  from this split1_card split2_card split3_card split4_card have
    "card {{(v1, 0), (0, k)} |v1 k. (v1\<in> (\<Union> E') \<or> v1 = v) \<and> (k \<in> {1..Suc(x)}) } = x * x + x + x +1 "
    by argo
  from this have
    "card {{(v1, 0), (0, k)} |v1 k. (v1\<in> (\<Union> E') \<or> v1 = v) \<and> (k \<in> {1..Suc(x)}) } = Suc x * Suc x"
    by simp

  from this Suc(2) show ?case
    using step1 by auto
qed


lemma card_additional_nodes:"card {{(0::nat, n)} |n. n \<in> {1..x}} = x"
proof (induction x)
  case 0
  then show ?case
    by simp
next
  case (Suc x)
  define step1 where step1_def:"step1= {{(0::nat, n)} |n. n \<in> {1..x}}"
  define step2 where step2_def:"step2= {{(0::nat, n)} |n. n = Suc x}"
  from step1_def step2_def have un:"{{(0::nat, n)} |n. n \<in> {1..Suc x}} = (step1 \<union> step2)"
    by force
  from step1_def Suc have card1:"card step1 = x"
    by blast
  from step2_def have card2:"card step2 = 1"
    by auto
  from card1 step1_def have fin1: "finite step1"
    by auto
  from card2 step2_def have fin2: "finite step2"
    by auto
  from step1_def step2_def have disjoint:"step1 \<inter> step2 = {}"
    by simp
  from disjoint un fin1 fin2 have "card {{(0::nat, n)} |n. n \<in> {1..Suc x}} = card step1 + card step2"
    using card_Un_disjoint[where A = step1 and B = step2]
    by presburger
  from this card1 card2 show ?case
    by presburger
qed




lemma finite_chrn2:
"finite {{(0::nat, k), (0, k')} |k k'. ((k \<in> {1..x::nat}\<and>k' \<in> {1..x} \<and> k \<noteq> k'))}"
proof -
  let ?S = "(({0}\<times>{1..x}) \<times> ({0}\<times> {1..x}))"
  show ?thesis by (fastforce intro: finite_surj[where A = "?S"])
qed






lemma chromatik_card4:"
  card {{(0::nat, k), (0::nat, k')} |k k'. k \<in> {1..x} \<and> k' \<in> {1..x} \<and> k \<noteq> k'} =
  (x * (x-1)) div 2"
proof (induction "x")
  case zero:0
  then show ?case
    by auto
next
  case (Suc x)
  define graph where graph_def: "graph = {{(0::nat, k), (0, k')} |k k'. k \<in> {1..Suc x} \<and> k' \<in> {1..Suc x} \<and> k \<noteq> k'}"
  define split1 where split1_def: "split1 = {{(0::nat, k), (0, k')} |k k'. ((k \<in> {1..x}\<and>k' \<in> {1..x} \<and> k \<noteq> k'))}"
  define split2 where split2_def: "split2 = {{(0::nat, k), (0, k')} |k k'. ((k \<in> {1..x} \<and> k' = Suc x \<and> k \<noteq> k'))}"
  define split3 where split3_def: "split3 = {{(0::nat, k), (0, k')} |k k'. ((k = Suc x \<and> k' \<in> {1..x} \<and> k \<noteq> k'))}"
  define split4 where split4_def: "split4 = {{(0::nat, k), (0, k')} |k k'. ((k = Suc x \<and> k' = Suc x \<and> k \<noteq> k'))}"
  from split2_def have split2_def': "split2 = {{(0::nat, k), (0, Suc x)} |k . k \<in> {1..x}}"
    by fastforce
  from split3_def have split3_def': "split3 = {{(0::nat, k), (0, Suc x)} |k . k \<in> {1..x}}"
    by fastforce
  from split2_def' split3_def' have sp2sp3_eq:"split2 = split3"
    by argo
  from split4_def have sp4_empty:"split4 = {}"
    by blast

  define split_step where split_step_def:
      "split_step = {{(0::nat, k), (0, k')} |k k'. (k \<in> {1..x} \<or> k = Suc x) \<and> (k' \<in> {1..x} \<or> k' = Suc x)\<and> k \<noteq> k'}"
  from split_step_def graph_def have sp_1:" graph =
          split_step"
    by fastforce
  from split_step_def have sp_2:"split_step =
        {{(0, k), (0, k')} |k k'. ((k \<in> {1..x}\<and>k' \<in> {1..x} \<and> k \<noteq> k'))} \<union>
        {{(0, k), (0, k')} |k k'. ((k \<in> {1..x} \<and> k' = Suc x \<and> k \<noteq> k'))} \<union>
        {{(0, k), (0, k')} |k k'. ((k = Suc x \<and> k' \<in> {1..x} \<and> k \<noteq> k'))} \<union>
        {{(0, k), (0, k')} |k k'. ((k = Suc x \<and> k' = Suc x \<and> k \<noteq> k'))}"
    by auto
  from sp_1 sp_2 have "graph = split1 \<union> split2 \<union> split3 \<union> split4"
    by (simp add: split1_def split2_def split3_def split4_def)

  from this sp2sp3_eq sp4_empty have graph_split:
    "graph = split1 \<union> split2"
    by auto

  from split1_def Suc have split1_card:"card split1 = (x * (x-1)) div 2"
    by simp

  from split2_def have split2_card:"card split2 = x"
  proof -
    from split2_def have "split2 = {{(0::nat, k), (0, Suc x)} |k.  (k \<in> {1..x} )}"
      by fastforce
    from this have "split2 = {{(0, Suc x), (0::nat, k)} |k.  (k \<in> {1..x} )}"
      by blast
    from this show "card split2 = x"
      using card_one_para[where ca = "0::nat" and cb = "Suc x" and cc = "0::nat" and x= x] by simp
  qed

  have disjoint:"split1 \<inter> split2 = {}"
    apply (simp add: split1_def split2_def)
    by (auto simp: doubleton_eq_iff)

  have fin1:"finite split1"
    using finite_chrn2
    by (simp add: split1_def)
  have fin2: "finite split2"
    by (simp add: split2_def)

  from graph_split fin1 fin2 disjoint have
    " card graph =
      card split1 + card split2 "
    using card_Un_disjoint[where A = split1 and B = split2] by simp

  from this split1_card split2_card have " card graph =
      (x * (x-1)) div 2 + x "
    by argo

  from this have " card graph =
      ((x * (x-1)) + (2*x)) div 2"
    by simp
  from this show ?case
    by (metis add.commute diff_Suc_1 graph_def left_add_twice mult.commute mult_Suc mult_eq_if)
qed



lemma connection_card:"card {{(0::nat, k), (0::nat, k')} |
                        k k'. k \<in> {1..(card (\<Union>E))} \<and>
                              k' \<in> {1..(card (\<Union>E))} \<and> k \<noteq> k'} =
                              ((card (\<Union>E)) * ((card (\<Union>E))-1)) div 2"
  using chromatik_card4
  by blast

lemma chromatik_finite1:"ugraph E \<Longrightarrow>
  finite {{(v1, 0::nat), (v2, 0)} |v1 v2. {v1, v2} \<in> E}"
proof -
  assume asms: "ugraph E"
  from this have "card {{(v1, 0::nat), (v2, 0)} |v1 v2. {v1, v2} \<in> E} = card E"
    by (simp add: chromatik_card1)
  from this asms show ?thesis unfolding ugraph_def
    using card.infinite by fastforce
qed


lemma chromatik_finite2:"finite (\<Union>E) \<Longrightarrow>
  finite {{(v1, 0), (0, k)} |v1 k. v1\<in> (\<Union> E) \<and> k \<in> {1..(card (\<Union>E))}}"
proof -
  assume asms: "finite (\<Union>E)"
  from this have "card {{(v1, 0), (0, k)} |v1 k. v1\<in> (\<Union> E) \<and> k \<in> {1..(card (\<Union>E))}} = card (\<Union>E) * card (\<Union>E)"
    using chromatik_card3
    by blast
  from this asms show ?thesis
    using card.infinite not_finite_existsD by fastforce
qed





lemma chromatik_finite3:"finite (\<Union>E) \<Longrightarrow>
  finite {{(0::nat, k), (0, k')} |k k'. k \<in> {1..card (\<Union> E)} \<and> k' \<in> {1..card (\<Union> E)} \<and> k \<noteq> k'}"
proof (cases "card (\<Union>E) = 0")
  case True
  from True show ?thesis
    by auto
next
  case F1:False
  then show ?thesis
  proof (cases "card (\<Union>E) = 1")
    case True
    then show ?thesis
      by simp
  next
    case F2:False

    obtain x where x_def:"x = card (\<Union>E)"
      by blast
    from this F1 F2 have x_greater_one:"1 < x"
      by linarith
    from this have card_greater_zero:"(x * (x-1)) div 2 > 0"
      by (metis divisors_zero mod2_gr_0 mod_eq_self_iff_div_eq_0
          nat_1_eq_mult_iff nat_neq_iff not_gr0 not_one_less_zero zero_less_diff)
    from x_def have "card {{(0::nat, k), (0, k')} |k k'. k \<in> {1..card (\<Union> E)} \<and> k' \<in> {1..card (\<Union> E)} \<and> k \<noteq> k'} =
      (x * (x-1)) div 2"
      using chromatik_card4
      by blast

    from this card_greater_zero have
      "card {{(0::nat, k), (0::nat, k')} |k k'. k \<in> {1..card (\<Union> E)} \<and> k' \<in> {1..card (\<Union> E)} \<and> k \<noteq> k'} > 0"
      by presburger
    from this show ?thesis
      using Finite_Set.card_ge_0_finite
      by blast
  qed
qed


end
