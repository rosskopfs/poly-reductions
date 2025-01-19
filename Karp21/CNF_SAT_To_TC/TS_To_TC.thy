theory TS_To_TC
  imports Main "TS_To_TC_Aux"
begin

subsection \<open>Preliminaries\<close>

definition
  "is_colorable E c_Sets  \<equiv>   (ugraph E) \<and> (\<Union> E  = \<Union> c_Sets) \<and>
                              (\<forall>c \<in> c_Sets. \<forall>c' \<in> c_Sets. (c \<noteq> c') \<longrightarrow> (c\<inter>c' = {})) \<and>
                              (\<forall>c \<in> c_Sets. \<forall>v \<in> c. \<forall>v' \<in> c. {v,v'}\<notin> E )"

definition
  "is_k_colorable E k c_Sets \<equiv> is_colorable E c_Sets \<and> card c_Sets = k"

definition
 "three_colorability \<equiv> {E. \<exists>c_Sets. is_k_colorable E 3 c_Sets}"

(*
The construction of the graph consists of three parts.

The constant part has three nodes (True-Node, False-Node, Help-Node).
(Nodes start with 0 ------ (0,False,0,_) )

In the second Part, there are 2 nodes for each variable in the cnf formula.
(Nodes start with 1 ------ (1,?literal_is_positive,?literal_name ,_) )

The third part consists of an "or-gadget" with 6 nodes for each clause in the cnf formula
(Nodes start with 2 ------ (2,False,?ith_clause,?ith_node_in_gadget) )
*)
abbreviation "false_node == (0::nat,False,0::nat,0::nat)"
abbreviation "true_node == (0::nat,False,0::nat,1::nat)"
abbreviation "help_node == (0::nat,False,0::nat,2::nat)"

definition
  "sat_tc F \<equiv> if (\<forall>cls \<in> set F. card cls = 3) then (
  {{false_node, true_node},{true_node, help_node},{false_node, help_node}} \<union>
  {{help_node,(1, True,  var l,0)}| l. (l\<in>(\<Union> (set F)))} \<union>
  {{help_node,(1, False,  var l,0)}| l. (l\<in>(\<Union> (set F)))} \<union>
  {{(1, False, var l,0),(1, True , var l,0)}|l . l\<in>(\<Union> (set F))} \<union>
  \<Union>{{{(1,tolit l1 = Pos,var l1,0),(2,False,i,0)},
      {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)},
      {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}}|
      l1 l2 l3 i . i < length F \<and> {l1,l2,l3} = F ! i \<and> sorted_list_of_set (F!i) = [l1,l2,l3]} \<union>
  {{(2,False,i,0),( 2,False,i,1)} | i. i < length F} \<union>
  {{(2,False,i,0),( 2,False,i,3)} | i. i < length F} \<union>
  {{(2,False,i,1),( 2,False,i,3)} | i. i < length F} \<union>
  {{(2,False,i,3),( 2,False,i,4)} | i. i < length F} \<union>
  {{(2,False,i,2),( 2,False,i,4)} | i. i < length F} \<union>
  {{(2,False,i,2),( 2,False,i,5)} | i. i < length F} \<union>
  {{(2,False,i,4),( 2,False,i,5)} | i. i < length F} \<union>
  {{(2,False,i,5),false_node} |  i. i < length F}\<union>
  {{(2,False,i,5),help_node} |  i. i < length F}
)else{{(0,False,0,0)}}"



subsection \<open>Three sat to three colorability lemmas\<close>

lemma sat_tc_ugraph:
  "F \<in> three_cnf_sat \<Longrightarrow> ugraph (sat_tc F)"
  unfolding ugraph_def sat_tc_def three_cnf_sat_def
  using finite1 finite2 finite3 finite4
  by auto



lemma choice3: "card S = 3 \<Longrightarrow> \<exists> x y z. S = {x,y,z} "
by (metis card_Suc_eq numeral_3_eq_3)

lemma choiceClause_help: "card (C::nat lit set ) = 3 \<Longrightarrow> \<exists> x y z. C = {x,y,z} \<and> x < y \<and> y < z"
  by (smt card_2_iff choice3 insert_absorb2 insert_commute is_singletonI is_singleton_altdef
      neqE numeral_One numeral_eq_iff semiring_norm(86) semiring_norm(89))

lemma choiceClause: "card (C::nat lit set ) = 3 \<Longrightarrow> \<exists> x y z. C = {x,y,z} \<and> sorted [x,y,z]"
  by (meson choiceClause_help less_imp_le sorted1 sorted2)


lemma ithGadget: "F' @ [a] = F \<Longrightarrow>
    length F' = x \<Longrightarrow> {{(2::nat, False, i, z::nat), (2, False, i, y)} |i. i < length F} =
                      {{(2, False, i, z), (2, False, i, y)} |i. i < length F'} \<union>
                      {{(2, False, i, z), (2, False, i, y)} |i. i = x}"
  by fastforce

lemma ithGadget2: "F' @ [a] = F \<Longrightarrow>
    length F' = x \<Longrightarrow> {{(2::nat, False, i, z::nat), (0, False, y', y)} |i. i < length F} =
                      {{(2, False, i, z), (0, False, y', y)} |i. i < length F'} \<union>
                      {{(2, False, i, z), (0, False, y', y)} |i. i = x}"
  by fastforce

lemma card_dif_elements: "S = {x,y,z} \<Longrightarrow> card S = 3 \<Longrightarrow> x \<noteq> y"
  by (metis card_2_iff insert_absorb2 is_singletonI is_singleton_altdef
      numeral_One numeral_eq_iff semiring_norm(86) semiring_norm(89))




subsection \<open>from three sat to three colorability\<close>

lemma cnfTo3Color: "F \<in> three_cnf_sat \<Longrightarrow> sat_tc F = E \<Longrightarrow> \<sigma> \<Turnstile> F \<Longrightarrow>
                    (\<exists> c_Sets c0 c1 c2. (is_k_colorable E 3 c_Sets \<and>
                    c_Sets = {c0,c1,c2} \<and>
                    false_node \<in> c0 \<and>
                    true_node \<in> c1 \<and>
                    help_node \<in> c2 \<and>
                    {(1, (\<sigma>\<up>) (Pos (var l)),  var l,0)| l. (l\<in>(\<Union> (set F)))} \<subseteq>  c1 \<and>
                    {(1, \<not>(\<sigma>\<up>) (Pos (var l)),  var l,0)| l. (l\<in>(\<Union> (set F)))} \<subseteq>  c0 \<and>
                    {(2,False,i,5) |  i. i < length F} \<subseteq> c1)) "
proof (induction "length F" arbitrary: E F \<sigma>)
  case 0
  from this have F_empty:"F = []" by auto
  from this have var_empty:"{(1, (\<sigma>\<up>) l, var l, 0) |l. l \<in> \<Union> (set F)} = {}" by auto
  from F_empty 0 have E_def_empty:
                          "E = {{false_node,true_node},
                               {true_node,help_node},
                               {false_node,help_node}}"
                                unfolding sat_tc_def by auto
    obtain c0' c1' c2' where color1: "  c0' = {false_node} \<and>
                                        c1' = {true_node} \<and>
                                        c2' = {help_node}" by auto
    from this have con1: "false_node \<in> c0' \<and> true_node \<in> c1' \<and> help_node \<in> c2'" by auto
    from F_empty have con2: "{(1,  (\<sigma>\<up>) (Pos (var l)),  var l,0)| l. (l\<in>(\<Union> (set F)))} \<subseteq>  c1'"
      by simp
    from F_empty have con3: "{(1, \<not> (\<sigma>\<up>) (Pos (var l)),  var l,0)| l. (l\<in>(\<Union> (set F)))} \<subseteq>  c0'"
      by simp
    from F_empty have con4: "{(2,False,i,5) |  i. i < length F} \<subseteq> c1'"
      by simp
    obtain c_Sets' where color2: "c_Sets' = {c0', c1', c2'}" by auto
    from this color1 E_def_empty have complete1:"\<Union>E = \<Union>c_Sets'" by auto
    from color1 color2 have emptyConjun1:"(\<forall>c\<in>c_Sets'. \<forall>c'\<in>c_Sets'. c \<noteq> c' \<longrightarrow> c \<inter> c' = {})" by auto
    from color1 color2 E_def_empty have sound1: "(\<forall>c\<in>c_Sets'. \<forall>v\<in>c. \<forall>v'\<in>c. {v, v'} \<notin> E)" by auto
    from color1 color2 have card1: "card c_Sets' = 3" by auto
    from E_def_empty have E_ugraph:"ugraph E" unfolding ugraph_def by auto
    from this complete1 emptyConjun1 sound1 card1 have " is_k_colorable E 3 c_Sets'"
      by (simp add: is_colorable_def is_k_colorable_def)
    from this color2 con1 con2 con3 con4 show ?case
      by blast
next
  case (Suc x)
    (*--------------------------------------*)
    (*Initial definitions for induction step*)
    (*--------------------------------------*)
    from Suc(3) Suc(4) sat_tc_ugraph have E_ugraph:"ugraph E"
      by blast
    from Suc(2) obtain F' a where F'_def:"F' @ [a]= F "
      by (metis append.right_neutral append_eq_conv_conj id_take_nth_drop lessI)
    from this Suc(3) have F'cnf:"F' \<in> three_cnf_sat"
      using cnf_remove_clause by auto
    from F'_def have F'_def_rev: "F = F' @ [a]"
      by simp
    from F'_def Suc(3) have a_card:"card a = 3" by fastforce
    from this obtain lit1 lit2 lit3 where lit_def:" a = {lit1, lit2 , lit3} \<and> sorted [lit1, lit2, lit3]"
      using choiceClause
      by presburger
    from this a_card have lit_unequ:"lit1 \<noteq> lit2 \<and> lit2 \<noteq> lit3 \<and> lit1 \<noteq> lit3"
      by (metis card_dif_elements insert_commute)
    from this lit_def a_card have sortedListOfLit:
      "sorted_list_of_set a = [lit1, lit2, lit3]"
      by auto
    from lit_unequ lit_def have lit_strict_sorted:"strict_sorted [lit1 ,lit2, lit3]"
      by auto
    from lit_def have lit_def_1:"a = {lit1, lit2 , lit3}" by simp
    from lit_def have lit_def_2:"sorted [lit1, lit2, lit3]" by simp
    from F'_def Suc(2) have F'_length:"length F' = x" by auto
    from this F'_def Suc(2) have x_def: "F ! x = a"by force
    define E' where E'_def:"E' = sat_tc F'"
    from Suc(5) F'_def Suc(3) have  ass:"\<sigma> \<Turnstile> F'"
      by (metis (mono_tags, lifting) butlast_snoc in_set_butlastD models_def)
    from F'cnf F'_length Suc(1)[where F = F'] ass have c_sets_exist:"
      \<exists>c_Sets c0 c1 c2.
         is_k_colorable E' 3 c_Sets \<and>
         c_Sets = {c0, c1, c2} \<and>
         false_node \<in> c0 \<and>
         true_node \<in> c1 \<and>
         help_node \<in> c2 \<and>
         {(1,(\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F')} \<subseteq> c1 \<and>
         {(1, \<not>(\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F')} \<subseteq> c0 \<and>
         {(2, False, i, 5) |i. i < length F'} \<subseteq> c1"
      unfolding E'_def
      by auto
    from this have E'_colorable:"E' \<in> three_colorability" unfolding three_colorability_def
      by fast

    (*--------------------------------------*)
    (*--Split E in subgraphs E' and E_diff--*)
    (*--------------------------------------*)

    from F'_def have diff1:" {{help_node, (1, True, var l, 0)} | l.  l \<in> \<Union> (set F)} =
                      {{help_node, (1, True, var l, 0)} | l.   l \<in> \<Union> (set F')} \<union>
                       {{help_node, (1, True, var l, 0)} |l.   l \<in>  a}"
      by fastforce

    from F'_def have diff1_2:" {{help_node, (1, False, var l, 0)} | l.  l \<in> \<Union> (set F)} =
                      {{help_node, (1, False, var l, 0)} | l.   l \<in> \<Union> (set F')} \<union>
                       {{help_node, (1, False, var l, 0)} |l.   l \<in>  a}"
      by fastforce

    from F'_def have diff2:"{{(1::nat, False, var l, 0::nat), (1, True, var l, 0)} |l. l \<in> \<Union> (set F)} =
                      {{(1, False, var l, 0), (1, True, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
                      {{(1, False, var l, 0), (1, True, var l, 0)} |l. l \<in> a}"
      by fastforce

    from a_card lit_def_1 lit_def_2 have diff3:"
            \<Union> {{{(1::nat, (tolit l1 = Pos), var l1, 0::nat), (2, False, i, 0)},
                  {(1, (tolit l2 = Pos), var l2, 0), (2, False, i, 1)},
                  {(1, (tolit l3 = Pos), var l3, 0), (2, False, i, 2)}} |
                l1 l2 l3 i. i < length F \<and> {l1, l2, l3} = (F ! i) \<and> sorted_list_of_set (F!i) = [l1,l2,l3]}
            =
              \<Union> {{  {(1, (tolit l1 = Pos), var l1, 0), (2, False, i, 0)},
                {(1, (tolit l2 = Pos), var l2, 0), (2, False, i, 1)},
                 {(1, (tolit l3 = Pos), var l3, 0), (2, False, i, 2)}} |
                l1 l2 l3 i. i < length F' \<and> {l1, l2, l3} = F' ! i \<and> sorted_list_of_set (F'  !i) = [l1,l2,l3]}
            \<union>
             {  {(1, (tolit lit1 = Pos), var lit1, 0), (2, False, x, 0)},
                {(1, (tolit lit2 = Pos), var lit2, 0), (2, False, x, 1)},
                 {(1, (tolit lit3 = Pos), var lit3, 0), (2, False, x, 2)}}"
      using clause_split_union[where c = a and F = F' and lita = lit1 and litb = lit2 and litc = lit3]
      by (simp add: F'_def_rev F'_length)

    from F'_def F'_length have "{{(2::nat, False, i, 0::nat), (2, False, i, 1)} |i. i < length F} =
                                {{(2::nat, False, i, 0::nat), (2, False, i, 1)} |i. i < length F'} \<union>
                                {{(2::nat, False, i, 0::nat), (2, False, i, 1)} |i. i = x}"
      using ithGadget[where F' = F' and a = a and x = x and F = F and y = "(1::nat)" and z= "(0::nat)"]
      by simp

    from Suc(2) have F_length:"length F = Suc x" by auto

    from F'_def F'_length F_length have diffGadget:"
      {{(2::nat, False, i, 0::nat), (2, False, i, 1)} |i. i < length F} \<union>
      {{(2, False, i, 0), (2, False, i, 3)} |i. i < length F} \<union>
      {{(2, False, i, 1), (2, False, i, 3)} |i. i < length F} \<union>
      {{(2, False, i, 3), (2, False, i, 4)} |i. i < length F} \<union>
      {{(2, False, i, 2), (2, False, i, 4)} |i. i < length F} \<union>
      {{(2, False, i, 2), (2, False, i, 5)} |i. i < length F} \<union>
      {{(2, False, i, 4), (2, False, i, 5)} |i. i < length F} \<union>
      {{(2, False, i, 5), false_node} |i. i < length F} \<union>
      {{(2, False, i, 5), help_node} |i. i < length F} =

      {{(2::nat, False, i, 0::nat), (2, False, i, 1)} |i. i < length F'} \<union>
      {{(2, False, i, 0), (2, False, i, 3)} |i. i < length F'} \<union>
      {{(2, False, i, 1), (2, False, i, 3)} |i. i < length F'} \<union>
      {{(2, False, i, 3), (2, False, i, 4)} |i. i < length F'} \<union>
      {{(2, False, i, 2), (2, False, i, 4)} |i. i < length F'} \<union>
      {{(2, False, i, 2), (2, False, i, 5)} |i. i < length F'} \<union>
      {{(2, False, i, 4), (2, False, i, 5)} |i. i < length F'} \<union>
      {{(2, False, i, 5), false_node} |i. i < length F'} \<union>
      {{(2, False, i, 5), help_node} |i. i < length F'}
      \<union>
      {{(2::nat, False, i, 0::nat), (2, False, i, 1)} |i. i = x} \<union>
      {{(2, False, i, 0), (2, False, i, 3)} |i. i = x} \<union>
      {{(2, False, i, 1), (2, False, i, 3)} |i. i = x} \<union>
      {{(2, False, i, 3), (2, False, i, 4)} |i. i = x} \<union>
      {{(2, False, i, 2), (2, False, i, 4)} |i. i = x} \<union>
      {{(2, False, i, 2), (2, False, i, 5)} |i. i = x} \<union>
      {{(2, False, i, 4), (2, False, i, 5)} |i. i = x} \<union>
      {{(2, False, i, 5), false_node} |i. i = x} \<union>
      {{(2, False, i, 5), help_node} |i. i = x} "
      using ithGadget[where F' = F' and a = a and x = x and F = F and y = "(1::nat)" and z= "(0::nat)"]
      using ithGadget[where F' = F' and a = a and x = x and F = F and y = "(3::nat)" and z= "(0::nat)"]
      using ithGadget[where F' = F' and a = a and x = x and F = F and y = "(3::nat)" and z= "(1::nat)"]
      using ithGadget[where F' = F' and a = a and x = x and F = F and y = "(4::nat)" and z= "(3::nat)"]
      using ithGadget[where F' = F' and a = a and x = x and F = F and y = "(4::nat)" and z= "(2::nat)"]
      using ithGadget[where F' = F' and a = a and x = x and F = F and y = "(5::nat)" and z= "(2::nat)"]
      using ithGadget[where F' = F' and a = a and x = x and F = F and y = "(5::nat)" and z= "(4::nat)"]
      using ithGadget2
        [where F' = F' and a = a and x = x and F = F and y = "(0::nat)" and  y'= "(0::nat)" and z= "(5::nat)"]
      using ithGadget2
        [where F' = F' and a = a and x = x and F = F and y = "(2::nat)" and  y'= "(0::nat)" and z= "(5::nat)"]
      by simp

      from diff1 diff2 diff3 diff1_2 have diffvar:"
          {{help_node, (1, True, var l, 0)} |l. l \<in> \<Union> (set F)} \<union>
          {{help_node, (1, False, var l, 0)} |l. l \<in> \<Union> (set F)} \<union>
          {{(1, False, var l, 0), (1, True, var l, 0)} |l. l \<in> \<Union> (set F)} \<union>
          \<Union> {{  {(1, tolit l1 = Pos, var l1, 0), (2, False, i, 0)},
                {(1, tolit l2 = Pos, var l2, 0), (2, False, i, 1)},
                {(1, tolit l3 = Pos, var l3, 0), (2, False, i, 2)}} |
                 l1 l2 l3 i. i < length F \<and> {l1, l2, l3} = F ! i \<and> sorted_list_of_set (F!i) = [l1,l2,l3]} =
          {{help_node, (1, True, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          {{help_node, (1, False, var l, 0)} |l. l \<in>  \<Union> (set F')} \<union>
          {{(1, False, var l, 0), (1, True, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          \<Union> {{{(1, tolit l1 = Pos, var l1, 0), (2, False, i, 0)},
               {(1, tolit l2 = Pos, var l2, 0), (2, False, i, 1)},
               {(1, tolit l3 = Pos, var l3, 0), (2, False, i, 2)}} |
              l1 l2 l3 i. i < length F' \<and> {l1, l2, l3} = F' ! i \<and> sorted_list_of_set (F'!i) = [l1,l2,l3]} \<union>
          {{help_node, (1, True, var l, 0)} |l. l \<in> a} \<union>
          {{help_node, (1, False, var l, 0)} |l. l \<in> a} \<union>
          {{(1, False, var l, 0), (1, True, var l, 0)} |l. l \<in> a} \<union>
          {{(1, (tolit lit1 = Pos), var lit1, 0), (2, False, x, 0)},
          {(1, (tolit lit2 = Pos), var lit2, 0), (2, False, x, 1)},
          {(1, (tolit lit3 = Pos), var lit3, 0), (2, False, x, 2)}}"
        by auto

      define E_diff where E_diff_def:"E_diff =
                      {{help_node, (1, True, var l, 0)} |l. l \<in> a} \<union>
                      {{help_node, (1, False, var l, 0)} |l. l \<in> a} \<union>
                      {{(1, False, var l, 0), (1, True, var l, 0)} |l. l \<in> a} \<union>
                      {{(1, (tolit lit1 = Pos), var lit1, 0), (2, False, x, 0)},
                        {(1, (tolit lit2 = Pos), var lit2, 0), (2, False, x, 1)},
                        {(1, (tolit lit3 = Pos), var lit3, 0), (2, False, x, 2)}} \<union>
                      {{(2, False, i, 0), (2, False, i, 1)} |i. i = x} \<union>
                      {{(2, False, i, 0), (2, False, i, 3)} |i. i = x} \<union>
                      {{(2, False, i, 1), (2, False, i, 3)} |i. i = x} \<union>
                      {{(2, False, i, 3), (2, False, i, 4)} |i. i = x} \<union>
                      {{(2, False, i, 2), (2, False, i, 4)} |i. i = x} \<union>
                      {{(2, False, i, 2), (2, False, i, 5)} |i. i = x} \<union>
                      {{(2, False, i, 4), (2, False, i, 5)} |i. i = x} \<union>
                      {{(2, False, i, 5), false_node} |i. i = x} \<union>
                      {{(2, False, i, 5), help_node} |i. i = x}"

    have E_def2:" E=  E' \<union> E_diff"
    proof -
      from Suc(3) Suc(4) have E_def_graph:"E = {{false_node, true_node}, {true_node, help_node},
           {false_node, help_node}} \<union>
          {{help_node, (1, True, var l, 0)} |l. l \<in> \<Union> (set F)} \<union>
          {{help_node, (1, False, var l, 0)} |l. l \<in> \<Union> (set F)} \<union>
          {{(1, False, var l, 0), (1, True, var l, 0)} |l. l \<in> \<Union> (set F)} \<union>
          \<Union> {{{(1, tolit l1 = Pos, var l1, 0), (2, False, i, 0)}, {(1, tolit l2 = Pos, var l2, 0), (2, False, i, 1)},
               {(1, tolit l3 = Pos, var l3, 0), (2, False, i, 2)}} |
              l1 l2 l3 i. i < length F \<and> {l1, l2, l3} = F ! i \<and> sorted_list_of_set (F!i) = [l1,l2,l3]} \<union>
          {{(2, False, i, 0), (2, False, i, 1)} |i. i < length F} \<union>
          {{(2, False, i, 0), (2, False, i, 3)} |i. i < length F} \<union>
          {{(2, False, i, 1), (2, False, i, 3)} |i. i < length F} \<union>
          {{(2, False, i, 3), (2, False, i, 4)} |i. i < length F} \<union>
          {{(2, False, i, 2), (2, False, i, 4)} |i. i < length F} \<union>
          {{(2, False, i, 2), (2, False, i, 5)} |i. i < length F} \<union>
          {{(2, False, i, 4), (2, False, i, 5)} |i. i < length F} \<union>
          {{(2, False, i, 5), false_node} |i. i < length F} \<union>
          {{(2, False, i, 5), help_node} |i. i < length F} "
        unfolding sat_tc_def by force
      define E_var where E_var_def:"E_var = {{false_node, true_node}, {true_node, help_node},
           {(0::nat, False, 0, 0::nat), help_node}} \<union>
          {{help_node, (1, True, var l, 0)} |l. l \<in> \<Union> (set F)} \<union>
          {{help_node, (1, False, var l, 0)} |l. l \<in> \<Union> (set F)} \<union>
          {{(1, False, var l, 0), (1, True, var l, 0)} |l. l \<in> \<Union> (set F)} \<union>
          \<Union> {{{(1, tolit l1 = Pos, var l1, 0), (2, False, i, 0)}, {(1, tolit l2 = Pos, var l2, 0), (2, False, i, 1)},
               {(1, tolit l3 = Pos, var l3, 0), (2, False, i, 2)}} |
              l1 l2 l3 i. i < length F \<and> {l1, l2, l3} = F ! i \<and> sorted_list_of_set (F!i) = [l1,l2,l3]}"
      define E_gadget where E_gadget_def:"E_gadget =
          {{(2::nat, False, i, 0::nat), (2, False, i, 1)} |i. i < length F} \<union>
          {{(2, False, i, 0), (2, False, i, 3)} |i. i < length F} \<union>
          {{(2, False, i, 1), (2, False, i, 3)} |i. i < length F} \<union>
          {{(2, False, i, 3), (2, False, i, 4)} |i. i < length F} \<union>
          {{(2, False, i, 2), (2, False, i, 4)} |i. i < length F} \<union>
          {{(2, False, i, 2), (2, False, i, 5)} |i. i < length F} \<union>
          {{(2, False, i, 4), (2, False, i, 5)} |i. i < length F} \<union>
          {{(2, False, i, 5), false_node} |i. i < length F} \<union>
          {{(2, False, i, 5), help_node} |i. i < length F}"
      from E_var_def E_gadget_def E_def_graph have equ1:"E = E_var \<union> E_gadget"
        by fastforce
      from E'_def F'cnf have E'_def_graph:"E' =
          {{false_node, true_node}, {true_node, help_node},
          {false_node, help_node}} \<union>
          {{help_node, (1, True, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          {{help_node, (1, False, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          {{(1, False, var l, 0), (1, True, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          \<Union> {{{(1, tolit l1 = Pos, var l1, 0), (2, False, i, 0)}, {(1, tolit l2 = Pos, var l2, 0), (2, False, i, 1)},
               {(1, tolit l3 = Pos, var l3, 0), (2, False, i, 2)}} |
              l1 l2 l3 i. i < length F' \<and> {l1, l2, l3} = F' ! i \<and> sorted_list_of_set (F'!i) = [l1,l2,l3]} \<union>
          {{(2, False, i, 0), (2, False, i, 1)} |i. i < length F'} \<union>
          {{(2, False, i, 0), (2, False, i, 3)} |i. i < length F'} \<union>
          {{(2, False, i, 1), (2, False, i, 3)} |i. i < length F'} \<union>
          {{(2, False, i, 3), (2, False, i, 4)} |i. i < length F'} \<union>
          {{(2, False, i, 2), (2, False, i, 4)} |i. i < length F'} \<union>
          {{(2, False, i, 2), (2, False, i, 5)} |i. i < length F'} \<union>
          {{(2, False, i, 4), (2, False, i, 5)} |i. i < length F'} \<union>
          {{(2, False, i, 5), false_node} |i. i < length F'} \<union>
          {{(2, False, i, 5), help_node} |i. i < length F'} "
        unfolding sat_tc_def by auto
      define E'_var where E'_var_def:"E'_var = {{false_node, true_node}, {true_node, help_node},
           {(0::nat, False, 0, 0::nat), help_node}} \<union>
          {{help_node, (1, True, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          {{help_node, (1, False, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          {{(1, False, var l, 0), (1, True, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          \<Union> {{{(1, tolit l1 = Pos, var l1, 0), (2, False, i, 0)}, {(1, tolit l2 = Pos, var l2, 0), (2, False, i, 1)},
               {(1, tolit l3 = Pos, var l3, 0), (2, False, i, 2)}} |
              l1 l2 l3 i. i < length F' \<and> {l1, l2, l3} = F' ! i \<and> sorted_list_of_set (F'!i) = [l1,l2,l3]}"
      define E'_gadget where E'_gadget_def:"E'_gadget =
          {{(2::nat, False, i, 0::nat), (2, False, i, 1)} |i. i < length F'} \<union>
          {{(2, False, i, 0), (2, False, i, 3)} |i. i < length F'} \<union>
          {{(2, False, i, 1), (2, False, i, 3)} |i. i < length F'} \<union>
          {{(2, False, i, 3), (2, False, i, 4)} |i. i < length F'} \<union>
          {{(2, False, i, 2), (2, False, i, 4)} |i. i < length F'} \<union>
          {{(2, False, i, 2), (2, False, i, 5)} |i. i < length F'} \<union>
          {{(2, False, i, 4), (2, False, i, 5)} |i. i < length F'} \<union>
          {{(2, False, i, 5), false_node} |i. i < length F'} \<union>
          {{(2, False, i, 5), help_node} |i. i < length F'}"
      from E'_var_def E'_gadget_def E'_def_graph have equ2:"E' = E'_var \<union> E'_gadget"
        by fastforce
      define E_diff_var where E_diff_var_def:"E_diff_var =
                      {{help_node, (1, True, var l, 0)} |l. l \<in> a} \<union>
                      {{help_node, (1, False, var l, 0)} |l. l \<in> a} \<union>
                      {{(1, False, var l, 0), (1, True, var l, 0)} |l. l \<in> a} \<union>
                      {{(1, (tolit lit1 = Pos), var lit1, 0), (2, False, x, 0)},
                        {(1, (tolit lit2 = Pos), var lit2, 0), (2, False, x, 1)},
                        {(1, (tolit lit3 = Pos), var lit3, 0), (2, False, x, 2)}}"
      define E_diff_gadget where E_diff_gadget_def:"E_diff_gadget =
                      {{(2::nat, False, i, 0::nat), (2, False, i, 1)} |i. i = x} \<union>
                      {{(2, False, i, 0), (2, False, i, 3)} |i. i = x} \<union>
                      {{(2, False, i, 1), (2, False, i, 3)} |i. i = x} \<union>
                      {{(2, False, i, 3), (2, False, i, 4)} |i. i = x} \<union>
                      {{(2, False, i, 2), (2, False, i, 4)} |i. i = x} \<union>
                      {{(2, False, i, 2), (2, False, i, 5)} |i. i = x} \<union>
                      {{(2, False, i, 4), (2, False, i, 5)} |i. i = x} \<union>
                      {{(2, False, i, 5), false_node} |i. i = x} \<union>
                      {{(2, False, i, 5), help_node} |i. i = x}"
      have equ3:"E_diff = E_diff_var \<union> E_diff_gadget"
        unfolding E_diff_var_def E_diff_gadget_def E_diff_def
        by simp
      from diffvar have equ_var:"E_var = E'_var \<union> E_diff_var"
        unfolding E_var_def E'_var_def E_diff_var_def
        by auto
      from diffGadget have equ_gadget:
        "E_gadget = E'_gadget \<union> E_diff_gadget"
        unfolding E_gadget_def E'_gadget_def E_diff_gadget_def
        by auto
      from equ_gadget equ_var equ1 equ2 equ3 show "E = E' \<union> E_diff"
        by fast
    qed

    (*--------------------------------------*)
    (*----Define nodes of E_diff------------*)
    (*--------------------------------------*)

    define E_diff_v where E_diff_v_def:"E_diff_v ={help_node,false_node,
                                      (1, True, var lit1, 0),
                                      (1, False, var lit1, 0),
                                      (1, True, var lit2, 0),
                                      (1, False, var lit2, 0),
                                      (1, True, var lit3, 0),
                                      (1, False, var lit3, 0),
                                      (2, False, x, 0),
                                      (2, False, x, 1),
                                      (2, False, x, 2),
                                      (2, False, x, 3),
                                      (2, False, x, 4),
                                      (2, False, x, 5)}"
    have "\<Union> E_diff = E_diff_v"
    proof -
      define E_diff_1 where E_diff_1_def:"E_diff_1 = {{help_node, (1, True, var l, 0)} |l. l \<in> a}"
      from lit_def_1 have diff1ToV: "\<Union> E_diff_1 =
      {help_node , (Suc 0, True, var lit1, 0), (Suc 0, True, var lit2, 0), (Suc 0, True, var lit3, 0)}"
        unfolding E_diff_1_def
        by auto
      define E_diff_2 where E_diff_2_def:"E_diff_2 = {{help_node, (1, False, var l, 0)} |l. l \<in> a}"
      from lit_def_1 have diff2ToV:"\<Union> E_diff_2 =
      {help_node , (Suc 0, False, var lit1, 0), (Suc 0, False, var lit2, 0), (Suc 0, False, var lit3, 0)}"
        unfolding E_diff_2_def
        by auto
      define E_diff_3 where E_diff_3_def:
        "E_diff_3 = {{(1::nat, False, var l, 0::nat), (1, True, var l, 0)} |l. l \<in> a}"
      define E_diff_3_v where E_diff_3_v_def: "E_diff_3_v =
            {(1::nat, True, var lit1, 0::nat), (1, True, var lit2, 0), (1, True, var lit3, 0),
            (1, False, var lit1, 0), (1, False, var lit2, 0), (1, False, var lit3, 0)}"

      from  lit_def_1  have diff3ToV:"\<Union> E_diff_3 =  E_diff_3_v"
        unfolding E_diff_3_def E_diff_3_v_def
        by auto
      define E_diff_4 where E_diff_4_def: "E_diff_4 =
                      {{(1::nat, (tolit lit1 = Pos), var lit1, 0::nat), (2, False, x, 0)},
                        {(1, (tolit lit2 = Pos), var lit2, 0), (2, False, x, 1)},
                        {(1, (tolit lit3 = Pos), var lit3, 0), (2, False, x, 2)}} \<union>
                      {{(2, False, i, 0), (2, False, i, 1)} |i. i = x} \<union>
                      {{(2, False, i, 0), (2, False, i, 3)} |i. i = x} \<union>
                      {{(2, False, i, 1), (2, False, i, 3)} |i. i = x} \<union>
                      {{(2, False, i, 3), (2, False, i, 4)} |i. i = x} \<union>
                      {{(2, False, i, 2), (2, False, i, 4)} |i. i = x} \<union>
                      {{(2, False, i, 2), (2, False, i, 5)} |i. i = x} \<union>
                      {{(2, False, i, 4), (2, False, i, 5)} |i. i = x} \<union>
                      {{(2, False, i, 5), false_node} |i. i = x} \<union>
                      {{(2, False, i, 5), help_node} |i. i = x}"
      define litToGadget_v where litToGadget_v_def:"litToGadget_v =
                                      {(1::nat, (tolit lit1 = Pos), var lit1, 0::nat),
                                      (1::nat, (tolit lit2 = Pos), var lit2, 0::nat),
                                      (1::nat, (tolit lit3 = Pos), var lit3, 0::nat)}"
      define gadget_v where gadget_v_def : "gadget_v = {help_node,false_node,
                                      (2, False, x, 0),
                                      (2, False, x, 1),
                                      (2, False, x, 2),
                                      (2, False, x, 3),
                                      (2, False, x, 4),
                                      (2, False, x, 5)} "
      define E_diff_4_v where E_diff_4_v_def:"E_diff_4_v = gadget_v \<union> litToGadget_v"
      have diff4ToV:"\<Union> E_diff_4 = E_diff_4_v"
        unfolding E_diff_4_def E_diff_4_v_def litToGadget_v_def gadget_v_def
        by auto
      define E_diff_34_v where E_diff_34_v_def: "E_diff_34_v = \<Union> E_diff_4 \<union> \<Union> E_diff_3"

      have "litToGadget_v \<union> E_diff_3_v =  E_diff_3_v"
        unfolding litToGadget_v_def E_diff_3_v_def
        by auto
      from this have "E_diff_4_v \<union> E_diff_3_v =gadget_v \<union> E_diff_3_v"
        unfolding E_diff_4_v_def
        by blast

      from this diff4ToV diff3ToV E_diff_34_v_def have "
          E_diff_34_v =gadget_v \<union> E_diff_3_v "
        by simp
      from this gadget_v_def E_diff_3_v_def have union3and4:"E_diff_34_v = {help_node,false_node,
                                      (1, True, var lit1, 0),
                                      (1, False, var lit1, 0),
                                      (1, True, var lit2, 0),
                                      (1, False, var lit2, 0),
                                      (1, True, var lit3, 0),
                                      (1, False, var lit3, 0),
                                      (2, False, x, 0),
                                      (2, False, x, 1),
                                      (2, False, x, 2),
                                      (2, False, x, 3),
                                      (2, False, x, 4),
                                      (2, False, x, 5)}"
        by auto
      have
            "E_diff= E_diff_1 \<union> E_diff_2 \<union> E_diff_3 \<union> E_diff_4"
        unfolding E_diff_def E_diff_1_def E_diff_2_def E_diff_3_def E_diff_4_def
        by simp
      from this E_diff_34_v_def have "\<Union>E_diff= \<Union>E_diff_1 \<union> \<Union>E_diff_2 \<union> E_diff_34_v"
        by auto
      from this union3and4 diff1ToV diff2ToV E_diff_v_def show ?thesis
        by force
    qed

    define E_diff_v_gadget where E_diff_v_gadget_def:"E_diff_v_gadget =
                                     {(2::nat, False, x, 0::nat),
                                      (2, False, x, 1),
                                      (2, False, x, 2),
                                      (2, False, x, 3),
                                      (2, False, x, 4),
                                      (2, False, x, 5)}"
    define E_diff_v_var where E_diff_v_var_def: "E_diff_v_var =
                                     {(1::nat, True, var lit1, 0::nat),
                                      (1, False, var lit1, 0),
                                      (1, True, var lit2, 0),
                                      (1, False, var lit2, 0),
                                      (1, True, var lit3, 0),
                                      (1, False, var lit3, 0) }"
    define E_diff_v_main where E_diff_v_main_def:
      "E_diff_v_main ={help_node,false_node} "
    have E_diff_v_def2:
      "E_diff_v = E_diff_v_main  \<union> E_diff_v_var \<union> E_diff_v_gadget"
      unfolding E_diff_v_main_def E_diff_v_var_def E_diff_v_gadget_def E_diff_v_def
      by auto

    (*-------------------------------------------------------------------------------------------*)
    (*-Obtain colors of E' and split nodes from E_diff_v_main and E_diff_v_var into these colors-*)
    (*-------------------------------------------------------------------------------------------*)
    from c_sets_exist obtain c0' c1' c2' c_Sets'  where c_sets'_def:"
      is_k_colorable E' 3 c_Sets' \<and>
      c_Sets' = {c0', c1', c2'} \<and>
      false_node \<in> c0' \<and>
      true_node \<in> c1' \<and>
      help_node \<in> c2' \<and>
      {(1,(\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F')} \<subseteq> c1' \<and>
      {(1,\<not>(\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F')} \<subseteq> c0' \<and>
      {(2, False, i, 5) |i. i < length F'} \<subseteq> c1'"
      by presburger
    from F'cnf have E_diff_v_main_subset:"E_diff_v_main \<subseteq> \<Union> E'"
      unfolding sat_tc_def E_diff_v_main_def E'_def by auto
    have E_diff_v_gadget_E'_empty:
      "E_diff_v_gadget \<inter> \<Union> E' = {} "
    proof -
      define E'_main where E'_main_def: "E'_main =
            {{(0::nat, False, 0::nat, 0::nat), true_node},
            {true_node, help_node},
            {false_node, help_node}}"
      define E'_var where E'_var_def: "E'_var =
          {{help_node, (1, True, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          {{help_node, (1, False, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          {{(1, False, var l, 0), (1, True, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          \<Union> {{{(1, tolit l1 = Pos, var l1, 0), (2, False, i, 0)}, {(1, tolit l2 = Pos, var l2, 0), (2, False, i, 1)},
               {(1, tolit l3 = Pos, var l3, 0), (2, False, i, 2)}} |
              l1 l2 l3 i. i < length F' \<and> {l1, l2, l3} = F' ! i \<and> sorted_list_of_set (F'!i) = [l1,l2,l3]}"
      define E'_gadget where E'_gadget_def: "E'_gadget =
          {{(2::nat, False, i, 0::nat), (2, False, i, 1)} |i. i < length F'} \<union>
          {{(2, False, i, 0), (2, False, i, 3)} |i. i < length F'} \<union>
          {{(2, False, i, 1), (2, False, i, 3)} |i. i < length F'} \<union>
          {{(2, False, i, 3), (2, False, i, 4)} |i. i < length F'} \<union>
          {{(2, False, i, 2), (2, False, i, 4)} |i. i < length F'} \<union>
          {{(2, False, i, 2), (2, False, i, 5)} |i. i < length F'} \<union>
          {{(2, False, i, 4), (2, False, i, 5)} |i. i < length F'} \<union>
          {{(2, False, i, 5), false_node} |i. i < length F'} \<union>
          {{(2, False, i, 5), help_node} |i. i < length F'}"
      from F'cnf have  E'_split:
        "E' =E'_main \<union> E'_var \<union> E'_gadget"
        unfolding sat_tc_def E'_def E'_main_def E'_var_def E'_gadget_def by auto
      have diffGadgetEmpty1: "E_diff_v_gadget \<inter> \<Union> E'_main = {}"
        unfolding E_diff_v_gadget_def E'_main_def
        by simp
      from F'_length have diffGadgetEmpty2:"E_diff_v_gadget \<inter> \<Union>E'_var = {}"
        unfolding E_diff_v_gadget_def E'_var_def
        by fastforce
      from F'_length have diffGadgetEmpty3:"E_diff_v_gadget \<inter> \<Union> E'_gadget = {}"
        unfolding E_diff_v_gadget_def E'_gadget_def
        by fastforce
      from E'_split diffGadgetEmpty1 diffGadgetEmpty2 diffGadgetEmpty3 show ?thesis
        by fast
    qed
    from this have E_diff_v_gadget_E'_empty2:"\<And>v.\<And>v'. v\<in>E_diff_v_gadget \<Longrightarrow> {v,v'} \<notin> E'"
      by blast
    from this have E_diff_v_gadget_E'_empty3:"\<And>v.\<And>v'. v\<in>E_diff_v_gadget \<Longrightarrow> {v',v} \<notin> E'"
      by (simp add: insert_commute)
    define c1'withvars where c1'withvars_def:"c1'withvars = c1' \<union>
                            { (1, (\<sigma>\<up>) (Pos (var lit1)), var lit1, 0),
                              (1, (\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                              (1, (\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) }"
    define c0'withvars where c0'withvars_def:"c0'withvars = c0' \<union>
                            { (1, \<not>(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0),
                              (1, \<not>(\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                              (1, \<not>(\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) }"
    have E_diff_v_var_equ:
        "c0' \<union> c1' \<union> E_diff_v_var = c1'withvars \<union> c0'withvars"
      unfolding c0'withvars_def  c1'withvars_def E_diff_v_var_def
      by auto

    (*--------------------------------------*)
    (*-Prerequisite of the case distinction-*)
    (*--------------------------------------*)

    from c_sets'_def have c_sets'_complete:"\<Union> E' = \<Union> c_Sets'"
      unfolding is_k_colorable_def is_colorable_def
      by fastforce
    from E_diff_v_main_subset c_sets'_complete c_sets'_def have "E_diff_v_main \<subseteq>  c0'\<union> c1'\<union> c2'"
      by auto
    from E'_def F'cnf F'_length have newGadgetNotInE':"\<forall>y. \<forall>z. (2::nat,y,x,z) \<notin> \<Union> E'"
      unfolding sat_tc_def by fastforce
    from newGadgetNotInE' E_diff_v_gadget_def c_sets'_complete c_sets'_def have gadget_c0'_empty:
      "E_diff_v_gadget \<inter> c0' = {}"
      by simp
    from newGadgetNotInE' E_diff_v_gadget_def c_sets'_complete c_sets'_def have gadget_c1'_empty:
      "E_diff_v_gadget \<inter> c1' = {}"
      by simp
    from newGadgetNotInE' E_diff_v_gadget_def c_sets'_complete c_sets'_def have gadget_c2'_empty:
      "E_diff_v_gadget \<inter> c2' = {}"
      by simp
    from c_sets'_def have "c0' \<noteq> c1'" using card_dif_elements unfolding is_k_colorable_def
      by fast
    from this c_sets'_def have c0'c1'_empty:"c0' \<inter> c1' = {}" unfolding is_k_colorable_def is_colorable_def
      by simp
    from c_sets'_def have "c0' \<noteq> c2'" using card_dif_elements unfolding is_k_colorable_def
      by (metis insert_commute)
    from this c_sets'_def have c0'c2'_empty:"c0' \<inter> c2' = {}" unfolding is_k_colorable_def is_colorable_def
      by simp
    from c_sets'_def have "c1' \<noteq> c2'" using card_dif_elements unfolding is_k_colorable_def
      by (metis insert_commute)
    from this c_sets'_def have c1'c2'_empty:"c1' \<inter> c2' = {}" unfolding is_k_colorable_def is_colorable_def
      by simp


    from c_sets'_def have var_in_c1':"\<And>lit .(  var lit \<in>  var  ` \<Union> (set F') \<Longrightarrow>
                             (1::nat, (\<sigma>\<up>) (Pos (var lit)), var lit, 0::nat) \<in> c1')"
      by fastforce

    from E'_def F'cnf have var_NotIn_E':"\<And>lit .( var lit \<notin> var ` \<Union> (set F') \<Longrightarrow>
                             (1::nat, (\<sigma>\<up>) (Pos (var lit)) , var lit, 0::nat) \<notin> \<Union>E')"
    proof -
      fix l
      assume asmNotIn:"var l \<notin> var ` \<Union> (set F')"
      define E'_main where E'_main_def: "E'_main =
            {{(0::nat, False, 0::nat, 0::nat), true_node},
            {true_node, help_node},
            {false_node, help_node}}"
      define E'_var where E'_var_def: "E'_var =
          {{help_node, (1, True, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          {{help_node, (1, False, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          {{(1, False, var l, 0), (1, True, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          \<Union> {{{(1, tolit l1 = Pos, var l1, 0), (2, False, i, 0)}, {(1, tolit l2 = Pos, var l2, 0), (2, False, i, 1)},
               {(1, tolit l3 = Pos, var l3, 0), (2, False, i, 2)}} |
              l1 l2 l3 i. i < length F' \<and> {l1, l2, l3} = F' ! i \<and> sorted_list_of_set (F'!i) = [l1,l2,l3]}"
      define  E'_gadget where E'_gadget_def: "E'_gadget =
          {{(2::nat, False, i, 0::nat), (2, False, i, 1)} |i. i < length F'} \<union>
          {{(2, False, i, 0), (2, False, i, 3)} |i. i < length F'} \<union>
          {{(2, False, i, 1), (2, False, i, 3)} |i. i < length F'} \<union>
          {{(2, False, i, 3), (2, False, i, 4)} |i. i < length F'} \<union>
          {{(2, False, i, 2), (2, False, i, 4)} |i. i < length F'} \<union>
          {{(2, False, i, 2), (2, False, i, 5)} |i. i < length F'} \<union>
          {{(2, False, i, 4), (2, False, i, 5)} |i. i < length F'} \<union>
          {{(2, False, i, 5), false_node} |i. i < length F'} \<union>
          {{(2, False, i, 5), help_node} |i. i < length F'}"
      from F'cnf have  E'_split:
          "E' =E'_main \<union> E'_var \<union> E'_gadget"
         unfolding sat_tc_def E'_def E'_main_def E'_var_def E'_gadget_def
         by auto
      from E'_main_def have NotInMain:"(1::nat, (\<sigma>\<up>) (Pos (var l)), var l, 0::nat) \<notin> \<Union>E'_main"
         by auto
       from E'_gadget_def have NotInGadget:"(1::nat, (\<sigma>\<up>) (Pos (var l)), var l, 0::nat) \<notin> \<Union>E'_gadget"
         by force

      define varToGadgetV where varToGadgetV_def: "varToGadgetV =
              (\<Union> {{{(1::nat, tolit l1 = Pos, var l1, 0::nat), (2, False, i, 0)},
                   {(1, tolit l2 = Pos, var l2, 0), (2, False, i, 1)},
                   {(1, tolit l3 = Pos, var l3, 0), (2, False, i, 2)}} |
              l1 l2 l3 i. i < length F' \<and> {l1, l2, l3} = F' ! i \<and> sorted_list_of_set (F'!i) = [l1,l2,l3]})"
      have "E'_var = {{help_node, (1, True, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
         {{help_node, (1, False, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
         {{(1, False, var l, 0), (1, True, var l, 0)} |l. l \<in> \<Union> (set F')}\<union> varToGadgetV"
         unfolding E'_var_def varToGadgetV_def
         by fast
      from this have E'_var_def2: "\<Union> E'_var =
          \<Union>{{help_node, (1, True, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          \<Union>{{help_node, (1, False, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          \<Union>{{(1, False, var l, 0), (1, True, var l, 0)} |l. l \<in> \<Union> (set F')}\<union>
          \<Union>varToGadgetV "
         by simp

      define varToGadgetNodes where varToGadgetNodes_def: "varToGadgetNodes =
         {(1::nat, tolit l = Pos, var l, 0::nat)| l. l \<in> \<Union> (set F') } \<union>
         {(2, False, i, 0) | i. i< length F'}\<union>
         {(2, False, i, 1) | i. i< length F'}\<union>
         {(2, False, i, 2) | i. i< length F'}"
      from this have 1:" \<Union> (\<Union> {{{(1::nat, tolit l1 = Pos, var l1, 0::nat), (2, False, i, 0)},
          {(1, tolit l2 = Pos, var l2, 0), (2, False, i, 1)},
          {(1, tolit l3 = Pos, var l3, 0), (2, False, i, 2)}} |
          l1 l2 l3 i. i < length F' \<and> {l1, l2, l3} = F' ! i \<and>
          sorted_list_of_set (F'!i) = [l1,l2,l3]}) \<subseteq>
          varToGadgetNodes"
        by fastforce
      from this varToGadgetV_def have subsetGadgetNodes:"\<Union> varToGadgetV \<subseteq>  varToGadgetNodes" by simp
      from asmNotIn varToGadgetNodes_def have 2:"(1::nat,(\<sigma>\<up>)(Pos (var l)), var l, 0::nat) \<notin> varToGadgetNodes"
        by auto
      define part1 where part1_def:
        "part1 = \<Union> {{help_node, (1, True, var l, 0)} |l. l \<in> \<Union> (set F')}"
      define part2 where part2_def:
        "part2 = \<Union>{{help_node, (1, False, var l, 0)} |l. l \<in> \<Union> (set F')}"
      define part3 where part3_def:
        "part3 = \<Union>{{(1::nat, False, var l, 0::nat), (1, True, var l, 0)} |l. l \<in> \<Union> (set F')}"
      define part4 where part4_def:
        "part4 = \<Union>varToGadgetV"
      from part4_def 2 subsetGadgetNodes have NotIn4:"(1::nat, (\<sigma>\<up>)(Pos (var l)), var l, 0::nat) \<notin> part4 "
        by blast
      from part1_def asmNotIn  have NotIn1:"(1::nat, (\<sigma>\<up>)(Pos (var l)), var l, 0::nat) \<notin> part1"
        by auto
      from part2_def asmNotIn have NotIn2:"(1::nat, (\<sigma>\<up>)(Pos (var l)), var l, 0::nat) \<notin> part2"
        by auto
      from part3_def  asmNotIn have NotIn3:"(1::nat, (\<sigma>\<up>)(Pos (var l)), var l, 0::nat) \<notin> part3"
        by auto
      from E'_var_def2 part1_def part2_def part3_def part4_def have
        "\<Union>E'_var = part1 \<union> part2 \<union> part3 \<union> part4"
        by simp
      from this NotIn4 NotIn1 NotIn2 NotIn3 have "(1::nat, (\<sigma>\<up>)(Pos (var l)), var l, 0::nat) \<notin> \<Union>E'_var"
        by blast
      from this NotInGadget NotInMain E'_split show "(1::nat, (\<sigma>\<up>)(Pos (var l)), var l, 0::nat) \<notin> \<Union>E'"
        by blast
    qed

    from this c_sets'_def have assOfc0Nodes:"\<And>lit .(1::nat, (\<sigma>\<up>) (Pos (var lit)), var lit, 0::nat) \<notin> c0'"
    proof -
      fix l :: "nat lit"
      show "(1::nat, (\<sigma>\<up>) (Pos (var l)), var l, 0::nat) \<notin> c0'"
      proof (cases "var l \<in>  var  ` \<Union> (set F')")
        case True
        from this var_in_c1' have "(1::nat, (\<sigma>\<up>) (Pos (var l)), var l, 0::nat) \<in> c1'"
          by simp
        from this c0'c1'_empty show ?thesis
          by blast
      next
        case False
        from this var_NotIn_E' have "(1::nat, (\<sigma>\<up>) (Pos (var l)), var l, 0::nat) \<notin> \<Union>E'"
          by simp
        from this c_sets'_complete have "(1::nat, (\<sigma>\<up>) (Pos (var l)), var l, 0::nat) \<notin> \<Union> c_Sets'"
          by argo
        from this c_sets'_def show ?thesis
          by simp
      qed
    qed

    from c_sets'_def have var_in_c0':"\<And>lit .(  var lit \<in>  var  ` \<Union> (set F') \<Longrightarrow>
                             (1::nat, \<not>(\<sigma>\<up>) (Pos (var lit)), var lit, 0::nat) \<in> c0')"
      by fastforce

    from E'_def F'cnf have var_NotIn_E'2:"\<And>lit .( var lit \<notin> var ` \<Union> (set F') \<Longrightarrow>
                             (1::nat, \<not>(\<sigma>\<up>) (Pos (var lit)) , var lit, 0::nat) \<notin> \<Union>E')"
    proof -
      fix l
      assume asmNotIn:"var l \<notin> var ` \<Union> (set F')"
      define E'_main where E'_main_def: "E'_main =
            {{(0::nat, False, 0::nat, 0::nat), true_node},
            {true_node, help_node},
            {false_node, help_node}}"
      define E'_var where E'_var_def: "E'_var =
          {{help_node, (1, True, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          {{help_node, (1, False, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          {{(1, False, var l, 0), (1, True, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          \<Union> {{{(1, tolit l1 = Pos, var l1, 0), (2, False, i, 0)},
               {(1, tolit l2 = Pos, var l2, 0), (2, False, i, 1)},
               {(1, tolit l3 = Pos, var l3, 0), (2, False, i, 2)}} |
              l1 l2 l3 i. i < length F' \<and> {l1, l2, l3} = F' ! i \<and> sorted_list_of_set (F'!i) = [l1,l2,l3]}"
      define E'_gadget where E'_gadget_def: "E'_gadget =
          {{(2::nat, False, i, 0::nat), (2, False, i, 1)} |i. i < length F'} \<union>
          {{(2, False, i, 0), (2, False, i, 3)} |i. i < length F'} \<union>
          {{(2, False, i, 1), (2, False, i, 3)} |i. i < length F'} \<union>
          {{(2, False, i, 3), (2, False, i, 4)} |i. i < length F'} \<union>
          {{(2, False, i, 2), (2, False, i, 4)} |i. i < length F'} \<union>
          {{(2, False, i, 2), (2, False, i, 5)} |i. i < length F'} \<union>
          {{(2, False, i, 4), (2, False, i, 5)} |i. i < length F'} \<union>
          {{(2, False, i, 5), false_node} |i. i < length F'} \<union>
          {{(2, False, i, 5), help_node} |i. i < length F'}"
      from F'cnf have  E'_split:
          "E' =E'_main \<union> E'_var \<union> E'_gadget"
        unfolding sat_tc_def E'_def E'_main_def E'_var_def E'_gadget_def
        by auto
      have NotInMain:"(1::nat,  \<not>(\<sigma>\<up>) (Pos (var l)), var l, 0::nat) \<notin> \<Union>E'_main"
        unfolding E'_main_def
        by auto
      have NotInGadget:"(1::nat,\<not>(\<sigma>\<up>) (Pos (var l)), var l, 0::nat) \<notin> \<Union>E'_gadget"
        unfolding E'_gadget_def
        by force
      define varToGadgetV where varToGadgetV_def: "varToGadgetV =
              (\<Union> {{{(1::nat, tolit l1 = Pos, var l1, 0::nat), (2, False, i, 0)},
                   {(1, tolit l2 = Pos, var l2, 0), (2, False, i, 1)},
                   {(1, tolit l3 = Pos, var l3, 0), (2, False, i, 2)}} |
              l1 l2 l3 i. i < length F' \<and> {l1, l2, l3} = F' ! i \<and> sorted_list_of_set (F'!i) = [l1,l2,l3]})"
      from this E'_var_def have "E'_var = {{help_node, (1, True, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          {{help_node, (1, False, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          {{(1, False, var l, 0), (1, True, var l, 0)} |l. l \<in> \<Union> (set F')}\<union> varToGadgetV"
         by fast
      from this have E'_var_def2: "\<Union> E'_var =
          \<Union>{{help_node, (1, True, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          \<Union>{{help_node, (1, False, var l, 0)} |l. l \<in> \<Union> (set F')} \<union>
          \<Union>{{(1, False, var l, 0), (1, True, var l, 0)} |l. l \<in> \<Union> (set F')}\<union>
          \<Union>varToGadgetV "
         by simp
      define varToGadgetNodes where varToGadgetNodes_def: "varToGadgetNodes =
            {(1::nat, tolit l = Pos, var l, 0::nat)| l. l \<in> \<Union> (set F') } \<union> {(2, False, i, 0) | i. i< length F'}
            \<union>  {(2, False, i, 1) | i. i< length F'} \<union> {(2, False, i, 2) | i. i< length F'}"
      from this have 1:" \<Union> (\<Union> {{{(1::nat, tolit l1 = Pos, var l1, 0::nat), (2, False, i, 0)},
                   {(1, tolit l2 = Pos, var l2, 0), (2, False, i, 1)},
                   {(1, tolit l3 = Pos, var l3, 0), (2, False, i, 2)}} |
              l1 l2 l3 i. i < length F' \<and> {l1, l2, l3} = F' ! i \<and> sorted_list_of_set (F'!i) = [l1,l2,l3]}) \<subseteq>
           varToGadgetNodes"
        by fastforce
      from this varToGadgetV_def have subsetGadgetNodes:"\<Union> varToGadgetV \<subseteq>  varToGadgetNodes" by simp
      from asmNotIn varToGadgetNodes_def have 2:"(1::nat,\<not>(\<sigma>\<up>)(Pos (var l)), var l, 0::nat) \<notin> varToGadgetNodes"
        by auto
      define part1 where part1_def:
        "part1 = \<Union> {{help_node, (1, True, var l, 0)} |l. l \<in> \<Union> (set F')}"
      define part2 where part2_def:
        "part2 = \<Union>{{help_node, (1, False, var l, 0)} |l. l \<in> \<Union> (set F')}"
      define part3 where part3_def:
        "part3 = \<Union>{{(1::nat, False, var l, 0::nat), (1, True, var l, 0)} |l. l \<in> \<Union> (set F')}"
      define part4 where part4_def:
        "part4 = \<Union>varToGadgetV"
      from part4_def 2 subsetGadgetNodes have NotIn4:"(1::nat,\<not>(\<sigma>\<up>)(Pos (var l)), var l, 0::nat) \<notin> part4 "
        by blast
      from part1_def asmNotIn  have NotIn1:"(1::nat,\<not>(\<sigma>\<up>)(Pos (var l)), var l, 0::nat) \<notin> part1"
        by auto
      from part2_def asmNotIn have NotIn2:"(1::nat,\<not>(\<sigma>\<up>)(Pos (var l)), var l, 0::nat) \<notin> part2"
        by auto
      from part3_def  asmNotIn have NotIn3:"(1::nat,\<not>(\<sigma>\<up>)(Pos (var l)), var l, 0::nat) \<notin> part3"
        by auto
      from E'_var_def2 part1_def part2_def part3_def part4_def have
        "\<Union>E'_var = part1 \<union> part2 \<union> part3 \<union> part4"
        by simp
      from this NotIn4 NotIn1 NotIn2 NotIn3 have "(1::nat, \<not>(\<sigma>\<up>)(Pos (var l)), var l, 0::nat) \<notin> \<Union>E'_var"
        by blast
      from this NotInGadget NotInMain E'_split show "(1::nat, \<not>(\<sigma>\<up>)(Pos (var l)), var l, 0::nat) \<notin> \<Union>E'"
        by blast
    qed

    from this c_sets'_def have assOfc1Nodes:"\<And>lit . (1::nat, \<not>(\<sigma>\<up>) (Pos (var lit)), var lit, 0::nat) \<notin> c1'"
    proof -
      fix l :: "nat lit"
      show "(1::nat,\<not>(\<sigma>\<up>) (Pos (var l)), var l, 0::nat) \<notin> c1'"
      proof (cases "var l \<in>  var  ` \<Union> (set F')")
        case True
        from this var_in_c0' have "(1::nat,\<not>(\<sigma>\<up>) (Pos (var l)), var l, 0::nat) \<in> c0'"
          by simp
        from this c0'c1'_empty show ?thesis
          by blast
      next
        case False
        from this var_NotIn_E'2 have "(1::nat,\<not>(\<sigma>\<up>) (Pos (var l)), var l, 0::nat) \<notin> \<Union>E'"
          by simp
        from this c_sets'_complete have "(1::nat,\<not>(\<sigma>\<up>) (Pos (var l)), var l, 0::nat) \<notin> \<Union> c_Sets'"
          by argo
        from this c_sets'_def show ?thesis
          by simp
      qed
    qed

    from this c_sets'_def have assOfc2Nodes1:"\<And>lit . (1::nat, (\<sigma>\<up>) (Pos (var lit)), var lit, 0::nat) \<notin> c2'"
    proof -
      fix l :: "nat lit"
      show "(1::nat, (\<sigma>\<up>) (Pos (var l)), var l, 0::nat) \<notin> c2'"
      proof (cases "var l \<in>  var  ` \<Union> (set F')")
        case True
        from this var_in_c1' have "(1::nat, (\<sigma>\<up>) (Pos (var l)), var l, 0::nat) \<in> c1'"
          by simp
        from this c1'c2'_empty show ?thesis
          by blast
      next
        case False
        from this var_NotIn_E' have "(1::nat, (\<sigma>\<up>) (Pos (var l)), var l, 0::nat) \<notin> \<Union>E'"
          by simp
        from this c_sets'_complete have "(1::nat, (\<sigma>\<up>) (Pos (var l)), var l, 0::nat) \<notin> \<Union> c_Sets'"
          by argo
        from this c_sets'_def show ?thesis
          by simp
      qed
    qed


    from this c_sets'_def have assOfc2Nodes2:"\<And>lit . (1::nat, \<not>(\<sigma>\<up>) (Pos (var lit)), var lit, 0::nat) \<notin> c2'"
    proof -
      fix l :: "nat lit"
      show "(1::nat,\<not>(\<sigma>\<up>) (Pos (var l)), var l, 0::nat) \<notin> c2'"
      proof (cases "var l \<in>  var  ` \<Union> (set F')")
        case True
        from this var_in_c0' have "(1::nat,\<not>(\<sigma>\<up>) (Pos (var l)), var l, 0::nat) \<in> c0'"
          by simp
        from this c0'c2'_empty show ?thesis
          by blast
      next
        case False
        from this var_NotIn_E'2 have "(1::nat,\<not>(\<sigma>\<up>) (Pos (var l)), var l, 0::nat) \<notin> \<Union>E'"
          by simp
        from this c_sets'_complete have "(1::nat,\<not>(\<sigma>\<up>) (Pos (var l)), var l, 0::nat) \<notin> \<Union> c_Sets'"
          by argo
        from this c_sets'_def show ?thesis
          by simp
      qed
    qed

    from assOfc1Nodes assOfc0Nodes assOfc2Nodes1 assOfc2Nodes2 have assOfVarNodes:"\<And>lit. (
              (1::nat, (\<sigma>\<up>) (Pos (var lit)), var lit, 0::nat) \<notin> c0' \<and>
              (1::nat, \<not>(\<sigma>\<up>) (Pos (var lit)), var lit, 0::nat) \<notin> c1'\<and>
              (1::nat, (\<sigma>\<up>) (Pos (var lit)), var lit, 0::nat) \<notin> c2' \<and>
              (1::nat, \<not>(\<sigma>\<up>) (Pos (var lit)), var lit, 0::nat) \<notin> c2')"
      by blast

    from this c_sets'_def have neg_var_edge_notin_E':"\<And>lit1 . \<And>lit2.
              { (1::nat, \<not>(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                (1::nat, \<not>(\<sigma>\<up>) (Pos (var lit2)), var lit2, 0::nat)} \<notin> E'"
    proof -
      fix lit1 :: "nat lit"
      fix lit2 :: "nat lit"
      show "{ (1::nat, \<not>(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                (1::nat, \<not>(\<sigma>\<up>) (Pos (var lit2)), var lit2, 0::nat)} \<notin> E'"
      proof (cases "var lit1 \<in>  var  ` \<Union> (set F') \<and> var lit2 \<in>  var  ` \<Union> (set F') ")
        case T1:True
        from this var_in_c0' have lit1_in_c0':"(1::nat,\<not>(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat) \<in> c0'"
          by simp
        from T1 var_in_c0' have lit2_in_c0':"(1::nat,\<not>(\<sigma>\<up>) (Pos (var lit2)), var lit2, 0::nat) \<in> c0'"
          by simp

        from lit1_in_c0' lit2_in_c0' c_sets'_def show ?thesis unfolding is_k_colorable_def is_colorable_def
          by fastforce
      next
        case F1:False
        then show ?thesis
        proof (cases "var lit1 \<in>  var  ` \<Union> (set F')")
          case T2:True
          from this F1 have "var lit2 \<notin> var ` \<Union> (set F')"
            by blast
          from this var_NotIn_E'2 have "(1::nat,\<not>(\<sigma>\<up>) (Pos (var lit2)), var lit2, 0::nat) \<notin> \<Union>E'"
          by simp
          then show ?thesis
            by blast
        next
          case F2:False
          from this var_NotIn_E'2 have "(1::nat,\<not>(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat) \<notin> \<Union>E'"
          by simp
          then show ?thesis
            by blast
        qed
      qed
    qed

    from this c_sets'_def have pos_var_edge_notin_E':"\<And>lit1 . \<And>lit2.
              { (1::nat, (\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                (1::nat, (\<sigma>\<up>) (Pos (var lit2)), var lit2, 0::nat)} \<notin> E'"
    proof -
      fix lit1 :: "nat lit"
      fix lit2 :: "nat lit"
      show "{ (1::nat, (\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                (1::nat, (\<sigma>\<up>) (Pos (var lit2)), var lit2, 0::nat)} \<notin> E'"
      proof (cases "var lit1 \<in>  var  ` \<Union> (set F') \<and> var lit2 \<in>  var  ` \<Union> (set F') ")
        case T1:True
        from this var_in_c1' have lit1_in_c1':"(1::nat,(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat) \<in> c1'"
          by simp
        from T1 var_in_c1' have lit2_in_c1':"(1::nat,(\<sigma>\<up>) (Pos (var lit2)), var lit2, 0::nat) \<in> c1'"
          by simp
        from lit1_in_c1' lit2_in_c1' c_sets'_def show ?thesis unfolding is_k_colorable_def is_colorable_def
          by fastforce
      next
        case F1:False
        then show ?thesis
        proof (cases "var lit1 \<in>  var  ` \<Union> (set F')")
          case T2:True
          from this F1 have "var lit2 \<notin> var ` \<Union> (set F')"
            by blast
          from this var_NotIn_E' have "(1::nat, (\<sigma>\<up>) (Pos (var lit2)), var lit2, 0::nat) \<notin> \<Union>E'"
          by simp
          then show ?thesis
            by blast
        next
          case F2:False
          from this var_NotIn_E' have "(1::nat,(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat) \<notin> \<Union>E'"
          by simp
          then show ?thesis
            by blast
        qed
      qed
    qed



    have neg_var_c0'_edge_notin_E'1:"\<And>lit1 . \<And>v. v\<in> c0' \<Longrightarrow>
              { (1::nat, \<not>(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),v} \<notin> E'"
    proof -
      fix lit1 :: "nat lit"
      fix v :: "nat \<times> bool \<times> nat \<times> nat"
      assume asm1:"v\<in> c0'"
      show "{ (1::nat, \<not>(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),v} \<notin> E'"
      proof (cases "var lit1 \<in>  var  ` \<Union> (set F')")
        case T1:True
        from this var_in_c0' have lit1_in_c0':"(1::nat,\<not>(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat) \<in> c0'"
          by simp
        from lit1_in_c0' asm1 c_sets'_def show ?thesis unfolding is_k_colorable_def is_colorable_def
          by fastforce
      next
        case F1:False
        from this var_NotIn_E'2 have "(1::nat,\<not>(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat) \<notin> \<Union>E'"
          by simp
        then show ?thesis
          by blast
      qed
    qed

    from this have neg_var_c0'_edge_notin_E'2:"\<And>lit1 . \<And>v. v\<in> c0' \<Longrightarrow>
              {v, (1::nat, \<not>(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat)} \<notin> E'"
      by (simp add: insert_commute)

    have pos_var_c1'_edge_notin_E'1:"\<And>lit1 . \<And>v. v\<in> c1' \<Longrightarrow>
              { (1::nat, (\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),v} \<notin> E'"
    proof -
      fix lit1 :: "nat lit"
      fix v :: "nat \<times> bool \<times> nat \<times> nat"
      assume asm1:"v\<in> c1'"
      show "{ (1::nat, (\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),v} \<notin> E'"
      proof (cases "var lit1 \<in>  var  ` \<Union> (set F')")
        case T1:True
        from this var_in_c1' have lit1_in_c1':"(1::nat,(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat) \<in> c1'"
          by simp
        from lit1_in_c1' asm1 c_sets'_def show ?thesis unfolding is_k_colorable_def is_colorable_def
          by fastforce
      next
        case F1:False
        from this var_NotIn_E' have "(1::nat,(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat) \<notin> \<Union>E'"
          by simp
        then show ?thesis
          by blast
      qed
    qed

    from this have pos_var_c1'_edge_notin_E'2:"\<And>lit1 . \<And>v. v\<in> c1' \<Longrightarrow>
              {v, (1::nat, (\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat)} \<notin> E'"
      by (simp add: insert_commute)


    from E'_colorable have edge_card1_notin_E': "\<And>lit1.
              {(1::nat, \<not>(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat)} \<notin> E'" unfolding three_colorability_def
    is_k_colorable_def is_colorable_def ugraph_def
      by fastforce

    from E'_colorable have edge_card1_notin_E'_2: "\<And>lit1.
              {(1::nat, (\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat)} \<notin> E'" unfolding three_colorability_def
    is_k_colorable_def is_colorable_def ugraph_def
      by fastforce

    from c_sets'_def have c0'iscolor:"\<And>v. \<And>v'. v\<in>c0' \<Longrightarrow> v'\<in>c0' \<Longrightarrow> {v, v'} \<notin> E'"
      unfolding is_k_colorable_def is_colorable_def
      by fastforce

    from c_sets'_def have c1'iscolor:"\<And>v. \<And>v'. v\<in>c1' \<Longrightarrow> v'\<in>c1' \<Longrightarrow> {v, v'} \<notin> E'"
      unfolding is_k_colorable_def is_colorable_def
      by fastforce

    from c_sets'_def have c2'iscolor:"\<And>v. \<And>v'. v\<in>c2' \<Longrightarrow> v'\<in>c2' \<Longrightarrow> {v, v'} \<notin> E'"
      unfolding is_k_colorable_def is_colorable_def
      by fastforce

    have toliteq:"\<And>lit. (\<sigma>\<up>) lit \<Longrightarrow> (\<sigma>\<up>) (Pos (var lit)) = (tolit lit = Pos)"
    proof -
      fix l :: "nat lit"
      assume asm1:"(\<sigma>\<up>) l"
      show "(\<sigma>\<up>) (Pos (var l)) = (tolit l = Pos)"
      proof (cases "tolit l = Pos")
        case True
        from this have "(tolit l = Pos)"
          by simp
        from this asm1 show ?thesis
          by (metis tolit.elims var.simps(1))
      next
        case False
        from this asm1 show ?thesis
          by (metis lit.simps(5) lit.simps(6) tolit.elims var.simps(2) models_lit_def)
      qed
    qed

    have toliteqNeg:"\<And>lit. \<not>(\<sigma>\<up>) lit \<Longrightarrow> \<not>(\<sigma>\<up>) (Pos (var lit)) = (tolit lit = Pos)"
    proof -
      fix l :: "nat lit"
      assume asm1:"\<not>(\<sigma>\<up>) l"
      show "\<not>(\<sigma>\<up>) (Pos (var l)) = (tolit l = Pos)"
      proof (cases "tolit l = Pos")
        case True
        from this have "(tolit l = Pos)"
          by simp
        from this asm1 show ?thesis
          by (metis tolit.elims var.simps(1))
      next
        case False
        from this asm1 show ?thesis
          by (metis lit.simps(5) lit.simps(6) tolit.elims var.simps(2) models_lit_def)
      qed
    qed


    have toliteq2:"\<And>l1. \<And>l2.
          (\<sigma>\<up>) l1 \<Longrightarrow>
          (\<sigma>\<up>) l2 \<Longrightarrow>
          ((tolit l2 = Pos) = (tolit l1 = Pos) \<or> var l2 \<noteq> var l1)"
      by (metis toliteq)

    from gadget_c0'_empty have gadget_c0'_empty2:"(\<forall>v'\<in>c0'. \<forall>v\<in> E_diff_v_gadget. v' \<noteq> v)"
      by blast

    from gadget_c1'_empty have gadget_c1'_empty2:"(\<forall>v'\<in>c1'. \<forall>v\<in> E_diff_v_gadget. v' \<noteq> v)"
      by blast

    from gadget_c2'_empty have gadget_c2'_empty2:"(\<forall>v'\<in>c2'. \<forall>v\<in> E_diff_v_gadget. v' \<noteq> v)"
      by blast

    from assOfVarNodes have trueVarNodesNotinc0':
      "\<And>l. (\<sigma>\<up>) l \<Longrightarrow> \<forall>v\<in>c0'. v \<noteq> (1, tolit l = Pos, var l, 0)"
    proof -
      fix l
      assume asm1:"(\<sigma>\<up>) l"
      from this toliteq have "(tolit l = Pos) = (\<sigma>\<up>) (Pos (var l))"
        by simp
      from this assOfVarNodes show "\<forall>v\<in>c0'.  v \<noteq> (1, tolit l = Pos, var l, 0)"
        by auto
    qed

    from assOfVarNodes have FalseVarNodesNotinc1':
      "\<And>l. \<not>(\<sigma>\<up>) l \<Longrightarrow> \<forall>v\<in>c1'. v \<noteq> (1, tolit l = Pos, var l, 0)"
    proof -
      fix l
      assume asm1:"\<not>(\<sigma>\<up>) l"
      from this toliteqNeg  have "(tolit l = Pos) = (\<not> (\<sigma>\<up>) (Pos (var l)))"
        by blast
      from this assOfVarNodes show "\<forall>v\<in>c1'.  v \<noteq> (1, tolit l = Pos, var l, 0)"
        by auto
    qed

    have toliteq3:"\<And>l. \<And>l1.  \<And>l2.  l1 \<in> a \<Longrightarrow> l2 \<in> a \<Longrightarrow> ((\<sigma>\<up>) l1) = ((\<sigma>\<up>) l2) \<Longrightarrow>
         (tolit l1 = Pos \<and> var l1 = var l \<longrightarrow> tolit l2 = Pos \<or> var l2 \<noteq> var l) \<and>
         (tolit l1 \<noteq> Pos \<and> var l1 = var l \<longrightarrow> tolit l2 = Pos \<longrightarrow> var l2 \<noteq> var l) \<or>
         l \<notin> a"
    proof -
      fix l :: "(nat lit)"
      fix l1 :: "(nat lit)"
      fix l2 :: "(nat lit)"
      assume asms: "l1 \<in> a" "l2 \<in> a" "(\<sigma>\<up>) l1 = (\<sigma>\<up>) l2"
      show "(tolit l1 = Pos \<and> var l1 = var l \<longrightarrow> tolit l2 = Pos \<or> var l2 \<noteq> var l) \<and>
         (tolit l1 \<noteq> Pos \<and> var l1 = var l \<longrightarrow> tolit l2 = Pos \<longrightarrow> var l2 \<noteq> var l) \<or>
         l \<notin> a"
      proof (cases "l \<notin> a")
        case True
        then show ?thesis
          by force
      next
        case False
        then have "l \<in> a"
          by simp
        from this asms have "
        (tolit l1 = Pos \<and> var l1 = var l \<longrightarrow> tolit l2 = Pos \<or> var l2 \<noteq> var l) \<and>
        (tolit l1 \<noteq> Pos \<and> var l1 = var l \<longrightarrow> tolit l2 = Pos \<longrightarrow> var l2 \<noteq> var l)"
          using models_lit_def by (smt lit.simps(5) lit.simps(6) var.elims)
        then show ?thesis
          by blast
      qed
    qed

    from this have toliteq3_2:"\<And>l. \<And>l1.  \<And>l2.  l1 \<in> a \<Longrightarrow> l2 \<in> a \<Longrightarrow> ((\<sigma>\<up>) l1) = ((\<sigma>\<up>) l2) \<Longrightarrow>
         (tolit l1 \<noteq> Pos \<and> var l1 = var l \<longrightarrow> tolit l2 = Pos \<longrightarrow> var l2 \<noteq> var l) \<and>
         (tolit l1 = Pos \<and> var l1 = var l \<longrightarrow> tolit l2 = Pos \<or> var l2 \<noteq> var l) \<or> l \<notin> a"
      by blast


    have helpCnotinc0':"\<And>v. v\<in>c0' \<Longrightarrow>v \<noteq> help_node"
    proof -
      fix v
      assume asm:"v\<in> c0'"
      from c_sets'_def have "help_node \<in> c2'"
        by blast
      from this c0'c2'_empty have "help_node \<notin> c0'"
        by blast
      from this asm show "v \<noteq> help_node"
        by auto
    qed

    have helpCnotinc1':"\<And>v. v\<in>c1' \<Longrightarrow>v \<noteq> help_node"
    proof -
      fix v
      assume asm:"v\<in> c1'"
      from c_sets'_def have "help_node \<in> c2'"
        by blast
      from this c1'c2'_empty have "help_node \<notin> c1'"
        by blast
      from this asm show "v \<noteq> help_node"
        by auto
    qed

    have falseCnotinc1':"\<And>v. v\<in>c1' \<Longrightarrow>v \<noteq> false_node"
    proof -
      fix v
      assume asm:"v\<in> c1'"
      from c_sets'_def have "false_node \<in> c0'"
        by blast
      from this c0'c1'_empty have "false_node \<notin> c1'"
        by blast
      from this asm show "v \<noteq> false_node"
        by auto
    qed

    have varnotinc2':"\<And>v. \<And>l. v\<in>c2' \<Longrightarrow>v \<noteq> (Suc 0, tolit l = Pos, var l, 0)"
    proof -
      fix v l
      assume asm:"v\<in> c2'"
      from this asm
        assOfVarNodes
        show "v \<noteq> (Suc 0, tolit l = Pos, var l, 0)"
          by (smt One_nat_def old.prod.inject)
      qed


    from this assOfVarNodes have true_varnotinc2':"\<And>v. \<And>l. v\<in>c2' \<Longrightarrow>v \<noteq> (Suc 0, True, var l, 0)"
      by (metis (mono_tags) One_nat_def)
    from this assOfVarNodes have false_varnotinc2':"\<And>v. \<And>l. v\<in>c2' \<Longrightarrow>v \<noteq> (Suc 0, False, var l, 0)"
      by (metis (mono_tags) One_nat_def)


    have trueVarNodesNotinc0'_2:"\<And>lit. \<And>v. \<And>l. lit \<in> a \<Longrightarrow> v\<in>c0' \<Longrightarrow> (\<sigma>\<up>) lit \<Longrightarrow>
            (tolit lit = Pos \<and> var lit = var l \<longrightarrow> v \<noteq> (Suc 0, True, var l, 0)) \<and>
            (tolit lit \<noteq> Pos \<and> var lit = var l \<longrightarrow> v \<noteq> (Suc 0, False, var l, 0))\<or> l\<notin>a"
    proof -
      fix lit
      fix l
      fix v
      assume asm: "lit \<in> a" "v \<in> c0'" "(\<sigma>\<up>) lit"
      show "(tolit lit = Pos \<and> var lit = var l \<longrightarrow> v \<noteq> (Suc 0, True, var l, 0)) \<and>
            (tolit lit \<noteq> Pos \<and> var lit = var l \<longrightarrow> v \<noteq> (Suc 0, False, var l, 0)) \<or> l\<notin>a"
      proof -
        from asm trueVarNodesNotinc0' have step1:
          "(tolit lit = Pos \<and> var lit = var l \<longrightarrow> v \<noteq> (Suc 0, True, var l, 0))"
          by fastforce
        from this asm trueVarNodesNotinc0' have step2:
          "(tolit lit \<noteq> Pos \<and> var lit = var l \<longrightarrow> v \<noteq> (Suc 0, False, var l, 0))"
          by fastforce
        from step1 step2 show ?thesis
          by blast
      qed
    qed

   have trueVarNodesNotinc1'_2:"\<And>lit. \<And>v. \<And>l. lit \<in> a \<Longrightarrow> v\<in>c1' \<Longrightarrow> (\<sigma>\<up>) lit \<Longrightarrow>
            (tolit lit \<noteq> Pos \<and> var lit = var l \<longrightarrow> v \<noteq> (Suc 0, True, var l, 0)) \<and>
            (tolit lit = Pos \<and> var lit = var l \<longrightarrow> v \<noteq> (Suc 0, False, var l, 0)) \<or>l\<notin>a"
    proof -
      fix lit
      fix l
      fix v
      assume asm: "lit \<in> a" "v \<in> c1'" "(\<sigma>\<up>) lit"
      show "(tolit lit \<noteq> Pos \<and> var lit = var l \<longrightarrow> v \<noteq> (Suc 0, True, var l, 0))\<and>
            (tolit lit = Pos \<and> var lit = var l \<longrightarrow> v \<noteq> (Suc 0, False, var l, 0)) \<or> l\<notin>a"
      proof -
        from asm have step1:
          "(tolit lit = Pos \<and> var lit = var l \<longrightarrow> v \<noteq> (Suc 0, False, var l, 0))"
          by (metis (mono_tags, lifting) One_nat_def assOfc1Nodes toliteq)
        from this asm trueVarNodesNotinc0' have step2:
          "(tolit lit \<noteq> Pos \<and> var lit = var l \<longrightarrow> v \<noteq> (Suc 0, True, var l, 0))"
          by (metis (mono_tags, lifting) One_nat_def assOfc1Nodes toliteq)
        from step1 step2 show ?thesis
          by blast
      qed
    qed

    from trueVarNodesNotinc0'_2 have trueVarNodesNotinc0'_3:"\<And>lit. \<And>v. \<And>l. lit \<in> a \<Longrightarrow> v\<in>c0' \<Longrightarrow> (\<sigma>\<up>) lit \<Longrightarrow>
            (v = (Suc 0, False, var l, 0) \<longrightarrow> tolit lit = Pos \<or> var lit \<noteq> var l) \<and>
            (v = (Suc 0, True, var l, 0) \<longrightarrow> tolit lit = Pos \<longrightarrow> var lit \<noteq> var l)\<or> l\<notin>a"
      by blast

    from trueVarNodesNotinc1'_2 have trueVarNodesNotinc1'_3:"\<And>lit. \<And>v. \<And>l. lit \<in> a \<Longrightarrow> v\<in>c1' \<Longrightarrow> (\<sigma>\<up>) lit \<Longrightarrow>
            (v = (Suc 0, False, var l, 0) \<longrightarrow> tolit lit = Pos \<longrightarrow> var lit \<noteq> var l) \<and>
            (v = (Suc 0, True, var l, 0) \<longrightarrow> tolit lit = Pos \<or> var lit \<noteq> var l) \<or> l\<notin>a"
      by blast
    have c0'iscolor_lit1:"(1, False, var lit1, 0) \<in> c0' \<Longrightarrow> (1, True, var lit1, 0) \<in> c0' \<Longrightarrow> False"
      by (metis (full_types) assOfVarNodes)
    have c0'iscolor_lit2:"(1, False, var lit2, 0) \<in> c0' \<Longrightarrow> (1, True, var lit2, 0) \<in> c0' \<Longrightarrow> False"
      by (metis (full_types) assOfVarNodes)
    have c0'iscolor_lit3:"(1, False, var lit3, 0) \<in> c0' \<Longrightarrow> (1, True, var lit3, 0) \<in> c0' \<Longrightarrow> False"
      by (metis (full_types) assOfVarNodes)
    have c1'iscolor_lit1:"(1, False, var lit1, 0) \<in> c1' \<Longrightarrow> (1, True, var lit1, 0) \<in> c1' \<Longrightarrow> False"
      by (metis (full_types) assOfVarNodes)
    have c1'iscolor_lit2:"(1, False, var lit2, 0) \<in> c1' \<Longrightarrow> (1, True, var lit2, 0) \<in> c1' \<Longrightarrow> False"
      by (metis (full_types) assOfVarNodes)
    have c1'iscolor_lit3:"(1, False, var lit3, 0) \<in> c1' \<Longrightarrow> (1, True, var lit3, 0) \<in> c1' \<Longrightarrow> False"
      by (metis (full_types) assOfVarNodes)


    (*--------------------------------------*)
    (*--------Case distinction--------------*)
    (*--------------------------------------*)

    (*Cases are only differ in the definition of c0 c1 c2.
      The nodes of the x-th gadget is split into the three colors.
      The distribution is dependent on \<sigma> and the assigned truth value of the literals of the clause a.
      After the first cases the six following cases are similar. *)
    have "\<exists>c_Sets c0 c1 c2.
       is_k_colorable E 3 c_Sets \<and>
       c_Sets = {c0, c1, c2} \<and>
       false_node \<in> c0 \<and>
       true_node \<in> c1 \<and>
       help_node \<in> c2 \<and>
       {(1, (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F)} \<subseteq> c1 \<and>
       {(1, \<not> (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F)} \<subseteq> c0 \<and>
       {(2, False, i, 5) |i. i < length F} \<subseteq> c1"
    proof (cases "(\<sigma>\<up>) lit1")
      case l1:True
      then show ?thesis
      proof (cases "(\<sigma>\<up>) lit2")
        case l2:True
        then show ?thesis
        proof (cases "(\<sigma>\<up>) lit3")
          case l3:True
          define c0 where c0_def:"c0 = c0'withvars \<union> {(2::nat, False, x, 0::nat),(2, False, x, 2)} "
          define c1 where c1_def:"c1 = c1'withvars \<union> {(2::nat, False, x, 3::nat),(2, False, x, 5)} "
          define c2 where c2_def:"c2 = c2' \<union> {(2::nat, False, x, 1::nat),(2, False, x, 4)}"
          define c_sets where c_sets_def: "c_sets = {c0, c1 ,c2}"
          from c1_def c1'withvars_def c2_def c0_def c0'withvars_def c_sets'_def have mainInCsets:
            "false_node \<in> c0 \<and>
             true_node \<in> c1 \<and>
             help_node \<in> c2 "
            by fastforce
          from gadget_c0'_empty gadget_c1'_empty l1 l2 l3 E_diff_v_gadget_def
            c0'c1'_empty c0_def c1_def c0'withvars_def c1'withvars_def assOfVarNodes
            have c0c1_empty:"c0 \<inter> c1 = {}"
            apply simp
            by metis
          from gadget_c0'_empty E_diff_v_gadget_def c0_def c2_def c0'withvars_def c0'c2'_empty
              gadget_c2'_empty assOfVarNodes
            have c0c2_empty:"c0 \<inter> c2 = {}"
            by simp
          from gadget_c1'_empty E_diff_v_gadget_def c1_def c2_def c1'withvars_def c1'c2'_empty
              gadget_c2'_empty assOfVarNodes
            have c1c2_empty:"c1 \<inter> c2 = {}"
            by simp

          have varInc1:
            "{(1, (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F)} \<subseteq> c1"
          proof -
            from c1_def c1'withvars_def c_sets'_def  have c1_subset1:
              "{(1, (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F')} \<subseteq> c1"
              by blast
            from c1_def c1'withvars_def  have c1_subset2:
              "{ (1::nat, (\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                                (1, (\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, (\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) } \<subseteq> c1"
              by blast
            from F'_def lit_def_1 have "{(1::nat, (\<sigma>\<up>) (Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F)} =
                              {(1::nat, (\<sigma>\<up>)(Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F')} \<union>
                              { (1::nat, (\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                                (1, (\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, (\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) }"
              by force
            from this c1_subset1 c1_subset2 show ?thesis
              by simp
          qed

          have varInc0:
            "{(1, \<not> (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F)} \<subseteq> c0"
          proof -
            from c0_def c0'withvars_def c_sets'_def  have c0_subset1:
              "{(1, \<not> (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F')} \<subseteq> c0"
              by blast
            from c0_def c0'withvars_def  have c0_subset2:
              "{ (1::nat, \<not>(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) } \<subseteq> c0"
              by blast
            from F'_def lit_def_1 have "{(1::nat, \<not>(\<sigma>\<up>) (Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F)} =
                              {(1::nat, \<not>(\<sigma>\<up>)(Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F')} \<union>
                              { (1::nat, \<not>(\<sigma>\<up>)(Pos (var lit1)), var lit1, 0::nat),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) }"
              by fastforce
            from this c0_subset1 c0_subset2 show ?thesis
              by auto
          qed

          have finalNodeInc1:
            "{(2, False, i, 5) |i. i < length F} \<subseteq> c1"
          proof -
            from c1_def c1'withvars_def c_sets'_def  have c1_subset3:
              "{(2, False, i, 5) |i. i < length F'} \<subseteq> c1"
              by blast
            from c1_def c1'withvars_def c_sets'_def  have c1_subset4:
              "{(2, False, x, 5)} \<subseteq> c1"
              by blast
            from F'_def F'_length have "{(2, False, i, 5) |i. i < length F} =
                                      {(2, False, i, 5) |i. i < length F'} \<union>
                                      {(2, False, x, 5)}"
              by fastforce
            from this c1_subset3 c1_subset4 show ?thesis
              by blast
          qed


          have c_sets_complete:"\<Union> E = \<Union> c_sets"
          proof -
            from E_diff_v_var_equ E_diff_v_def2 have E_diff_v_c0'c1'c2'_equ:"E_diff_v \<union>  c0' \<union> (c1' \<union> c2') =
              E_diff_v_main \<union> c1'withvars \<union> c0'withvars \<union> E_diff_v_gadget \<union> c2'"
              by blast
            from c_sets'_def have "
                false_node \<in> c0' \<and>
                true_node \<in> c1' \<and>
                help_node \<in> c2' "
               by simp
             from this l1 l2 l3 c0_def c1_def c2_def E_diff_v_main_def
               E_diff_v_gadget_def c1'withvars_def c0'withvars_def have
              "E_diff_v_main \<union> c1'withvars \<union> c0'withvars \<union> E_diff_v_gadget \<union> c2' = c0 \<union> (c1 \<union> c2)"
               by auto
            from this c_sets_def c_sets'_def E_diff_v_c0'c1'c2'_equ have
                "E_diff_v \<union>  \<Union> c_Sets' = \<Union> c_sets"
              by auto
            from this E_def2 c_sets'_complete show ?thesis
              by (simp add: Un_commute \<open>\<Union> E_diff = E_diff_v\<close>)
          qed


          from c_sets_def c1c2_empty c0c2_empty c0c1_empty have
            c_sets_sound:"(\<forall>c\<in>c_sets. \<forall>c'\<in>c_sets. c \<noteq> c' \<longrightarrow> c \<inter> c' = {})"
            by blast


          have c_sets_three_color:" card c_sets = 3"
          proof -
            from c0c1_empty c0_def c1_def have c0c1notEq:"c0 \<noteq> c1"
              by blast
            from c0c2_empty c0_def c2_def have c0c2notEq:"c0 \<noteq> c2"
              by blast
            from c1c2_empty c1_def c2_def have c1c2notEq:"c1 \<noteq> c2"
              by blast
            from c0c1notEq c0c2notEq c1c2notEq c_sets_def show ?thesis
              by simp
          qed


          have c0iscolor:
              "(\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E)"
          proof -
            from c0_def c0'withvars_def doubleton_eq_iff E_diff_v_gadget_E'_empty2
              E_diff_v_gadget_E'_empty3 E_diff_v_gadget_def neg_var_edge_notin_E'
              neg_var_c0'_edge_notin_E'1 neg_var_c0'_edge_notin_E'2 edge_card1_notin_E' c0'iscolor
            have c0_color_E':
                "(\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E')" by simp
            from c0'iscolor_lit1 c0'iscolor_lit2 c0'iscolor_lit3 have "\<forall>v\<in>c0'. \<forall>v'\<in>c0'.
              \<forall>l. (v = (1, False, var l, 0) \<longrightarrow> v' \<noteq> (1, True, var l, 0)) \<and>
              (v = (1, True, var l, 0) \<longrightarrow> v' \<noteq> (1, False, var l, 0)) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3"
              by blast
            from this l1 l2 l3  toliteq toliteq2 trueVarNodesNotinc0' toliteq3  helpCnotinc0'
                trueVarNodesNotinc0'_2 trueVarNodesNotinc0'_3
            have c0_color_E_diff:
                "(\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E_diff)"
              by (simp add: c0_def c0'withvars_def E_diff_def  doubleton_eq_iff
                    gadget_c0'_empty2 E_diff_v_gadget_def lit_def)
            from  c0_color_E_diff c0_color_E' E_def2 show ?thesis
              by blast
          qed

          have c1iscolor:
              "(\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E)"
          proof -
            from c1_def c1'withvars_def doubleton_eq_iff E_diff_v_gadget_E'_empty2
              E_diff_v_gadget_E'_empty3 E_diff_v_gadget_def pos_var_edge_notin_E'
              pos_var_c1'_edge_notin_E'1 pos_var_c1'_edge_notin_E'2 edge_card1_notin_E'_2 c1'iscolor
            have c1_color_E':
                "(\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E')" by simp
            from c1'iscolor_lit1 c1'iscolor_lit2 c1'iscolor_lit3 have "\<forall>v\<in>c1'. \<forall>v'\<in>c1'.
              \<forall>l. (v = (1, False, var l, 0) \<longrightarrow> v' \<noteq> (1, True, var l, 0)) \<and>
              (v = (1, True, var l, 0) \<longrightarrow> v' \<noteq> (1, False, var l, 0)) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3"
              by blast
            from this l1 l2 l3  toliteq toliteqNeg toliteq3_2 helpCnotinc1'
                trueVarNodesNotinc1'_2 trueVarNodesNotinc1'_3 FalseVarNodesNotinc1' falseCnotinc1'
            have c1_color_E_diff:
                "(\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E_diff)"
              by (simp add: c1_def c1'withvars_def E_diff_def  doubleton_eq_iff
                    gadget_c1'_empty2 E_diff_v_gadget_def lit_def)
            from c1_color_E_diff c1_color_E' E_def2 show ?thesis
              by blast
          qed


          have c2iscolor:
              "(\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E)"
          proof -
            from c2_def doubleton_eq_iff E_diff_v_gadget_E'_empty2
              E_diff_v_gadget_E'_empty3 E_diff_v_gadget_def pos_var_edge_notin_E'
              pos_var_c1'_edge_notin_E'1 pos_var_c1'_edge_notin_E'2 edge_card1_notin_E'_2 c2'iscolor
            have c2_color_E':
                "(\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E')" by simp
            from l1 l2 l3  toliteq toliteqNeg toliteq2 trueVarNodesNotinc0' toliteq3  toliteq3_2 helpCnotinc1'
                trueVarNodesNotinc1'_2 trueVarNodesNotinc1'_3 FalseVarNodesNotinc1' falseCnotinc1' varnotinc2'
                false_varnotinc2' true_varnotinc2'
            have c2_color_E_diff:
                "(\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E_diff)"
              by (simp add: c2_def E_diff_def  doubleton_eq_iff
                    gadget_c2'_empty2 E_diff_v_gadget_def lit_def)
            from c2_color_E_diff c2_color_E' E_def2 show ?thesis
              by blast
          qed

          from c0iscolor c1iscolor c2iscolor have iscolor: "(\<forall>c\<in>c_sets. \<forall>v\<in>c. \<forall>v'\<in>c. {v, v'} \<notin> E)"
            using c_sets_def by blast

          from E_ugraph c_sets_complete c_sets_sound iscolor c_sets_three_color have E_three_colorable:
            "is_k_colorable E 3 c_sets" unfolding is_k_colorable_def is_colorable_def
          by blast

          from E_three_colorable c_sets_def mainInCsets varInc1 varInc0 finalNodeInc1 show ?thesis
            by blast
        next
          case l3:False
          define c0 where c0_def:"c0 = c0'withvars \<union> {(2::nat, False, x, 0::nat),(2, False, x, 4)} "
          define c1 where c1_def:"c1 = c1'withvars \<union> {(2::nat, False, x, 3::nat),(2, False, x, 5)} "
          define c2 where c2_def:"c2 = c2' \<union> {(2::nat, False, x, 1::nat),(2, False, x, 2)}"
          define c_sets where c_sets_def: "c_sets = {c0, c1 ,c2}"
          from c1_def c1'withvars_def c2_def c0_def c0'withvars_def c_sets'_def have mainInCsets:
            " false_node \<in> c0 \<and>
              true_node \<in> c1 \<and>
              help_node \<in> c2 "
            by fastforce
          from gadget_c0'_empty gadget_c1'_empty l1 l2 l3 E_diff_v_gadget_def
            c0'c1'_empty c0_def c1_def c0'withvars_def c1'withvars_def assOfVarNodes
            have c0c1_empty:"c0 \<inter> c1 = {}"
            apply simp
            by metis
          from gadget_c0'_empty E_diff_v_gadget_def c0_def c2_def c0'withvars_def c0'c2'_empty
              gadget_c2'_empty assOfVarNodes
            have c0c2_empty:"c0 \<inter> c2 = {}"
            by simp
          from gadget_c1'_empty E_diff_v_gadget_def c1_def c2_def c1'withvars_def c1'c2'_empty
              gadget_c2'_empty assOfVarNodes
            have c1c2_empty:"c1 \<inter> c2 = {}"
            by simp

          have varInc1:
            "{(1, (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F)} \<subseteq> c1"
          proof -
            from c1_def c1'withvars_def c_sets'_def  have c1_subset1:
              "{(1, (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F')} \<subseteq> c1"
              by blast
            from c1_def c1'withvars_def  have c1_subset2:
              "{ (1::nat, (\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                                (1, (\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, (\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) } \<subseteq> c1"
              by blast
            from F'_def lit_def_1 have "{(1::nat, (\<sigma>\<up>) (Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F)} =
                              {(1::nat, (\<sigma>\<up>)(Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F')} \<union>
                              { (1::nat, (\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                                (1, (\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, (\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) }"
              by force
            from this c1_subset1 c1_subset2 show ?thesis
              by simp
          qed

          have varInc0:
            "{(1, \<not> (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F)} \<subseteq> c0"
          proof -
            from c0_def c0'withvars_def c_sets'_def  have c0_subset1:
              "{(1, \<not> (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F')} \<subseteq> c0"
              by blast
            from c0_def c0'withvars_def  have c0_subset2:
              "{ (1::nat, \<not>(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) } \<subseteq> c0"
              by blast
            from F'_def lit_def_1 have "{(1::nat, \<not>(\<sigma>\<up>) (Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F)} =
                              {(1::nat, \<not>(\<sigma>\<up>)(Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F')} \<union>
                              { (1::nat, \<not>(\<sigma>\<up>)(Pos (var lit1)), var lit1, 0::nat),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) }"
              by fastforce
            from this c0_subset1 c0_subset2 show ?thesis
              by auto
          qed

          have finalNodeInc1:
            "{(2, False, i, 5) |i. i < length F} \<subseteq> c1"
          proof -
            from c1_def c1'withvars_def c_sets'_def  have c1_subset3:
              "{(2, False, i, 5) |i. i < length F'} \<subseteq> c1"
              by blast

            from c1_def c1'withvars_def c_sets'_def  have c1_subset4:
              "{(2, False, x, 5)} \<subseteq> c1"
              by blast

            from F'_def F'_length have "{(2, False, i, 5) |i. i < length F} =
                                      {(2, False, i, 5) |i. i < length F'} \<union>
                                      {(2, False, x, 5)}"
              by fastforce
            from this c1_subset3 c1_subset4 show ?thesis
              by blast
          qed


          have c_sets_complete:"\<Union> E = \<Union> c_sets"
          proof -
            from E_diff_v_var_equ E_diff_v_def2 have E_diff_v_c0'c1'c2'_equ:"E_diff_v \<union>  c0' \<union> (c1' \<union> c2') =
              E_diff_v_main \<union> c1'withvars \<union> c0'withvars \<union> E_diff_v_gadget \<union> c2'"
              by blast
            from c_sets'_def have "
                false_node \<in> c0' \<and>
                true_node \<in> c1' \<and>
                help_node \<in> c2' "
               by simp
             from this l1 l2 l3 c0_def c1_def c2_def E_diff_v_main_def
               E_diff_v_gadget_def c1'withvars_def c0'withvars_def have
              "E_diff_v_main \<union> c1'withvars \<union> c0'withvars \<union> E_diff_v_gadget \<union> c2' = c0 \<union> (c1 \<union> c2)"
               by auto
            from this c_sets_def c_sets'_def E_diff_v_c0'c1'c2'_equ have
                "E_diff_v \<union>  \<Union> c_Sets' = \<Union> c_sets"
              by auto
            from this E_def2 c_sets'_complete show ?thesis
              by (simp add: \<open>\<Union> E_diff = E_diff_v\<close> sup_commute)
          qed


          from c_sets_def c1c2_empty c0c2_empty c0c1_empty have
            c_sets_sound:"(\<forall>c\<in>c_sets. \<forall>c'\<in>c_sets. c \<noteq> c' \<longrightarrow> c \<inter> c' = {})"
            by blast


          have c_sets_three_color:" card c_sets = 3"
          proof -
            from c0c1_empty c0_def c1_def have c0c1notEq:"c0 \<noteq> c1"
              by blast
            from c0c2_empty c0_def c2_def have c0c2notEq:"c0 \<noteq> c2"
              by blast
            from c1c2_empty c1_def c2_def have c1c2notEq:"c1 \<noteq> c2"
              by blast
            from c0c1notEq c0c2notEq c1c2notEq c_sets_def show ?thesis
              by simp
          qed


          have c0iscolor:
              "(\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E)"
          proof -
            from c0_def c0'withvars_def doubleton_eq_iff E_diff_v_gadget_E'_empty2
              E_diff_v_gadget_E'_empty3 E_diff_v_gadget_def neg_var_edge_notin_E'
              neg_var_c0'_edge_notin_E'1 neg_var_c0'_edge_notin_E'2 edge_card1_notin_E' c0'iscolor
            have c0_color_E':
                "(\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E')" by simp
            have step1:"((\<sigma>\<up>) (Pos (var lit3)) = (tolit lit1 = Pos) \<or> var lit3 \<noteq> var lit1) \<and>
              ((\<sigma>\<up>) (Pos (var lit3)) = (tolit lit1 = Pos) \<or> var lit3 \<noteq> var lit1)"
              using l1 toliteq
              by metis
            have step2:"(\<forall>l. (tolit lit1 = Pos \<and> var lit1 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit3)) \<or> var lit3 \<noteq> var l) \<and>
              (tolit lit1 \<noteq> Pos \<and> var lit1 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit3)) \<longrightarrow> var lit3 \<noteq> var l) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step1
              by metis
            have step3:"(\<forall>l. (tolit lit2 = Pos \<and> var lit2 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit3)) \<or> var lit3 \<noteq> var l) \<and>
              (tolit lit2 \<noteq> Pos \<and> var lit2 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit3)) \<longrightarrow> var lit3 \<noteq> var l) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using l2 toliteq by fastforce
            have step4:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> tolit lit1 = Pos \<or> var lit1 \<noteq> var l) \<and>
              (\<not> (\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> tolit lit1 = Pos \<longrightarrow> var lit1 \<noteq> var l) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step2 by blast
            have step5:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> tolit lit2 = Pos \<or> var lit2 \<noteq> var l) \<and>
              (\<not> (\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> tolit lit2 = Pos \<longrightarrow> var lit2 \<noteq> var l) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step3  by blast
            have step6:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var l))) \<and>
              (\<not> (\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> \<not> (\<sigma>\<up>) (Pos (var l))) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by fastforce
            have step7:"(\<forall>v'\<in>c0'.
              \<forall>l. ((\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
              (\<not> (\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by (metis (full_types) One_nat_def assOfc0Nodes)
            have step8:"(\<forall>v\<in>c0'.
              (\<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> (\<sigma>\<up>) (Pos (var lit3)) \<or> var lit3 \<noteq> var l) \<and>
              (v = (Suc 0, True, var l, 0) \<longrightarrow> (\<sigma>\<up>) (Pos (var lit3)) \<longrightarrow> var lit3 \<noteq> var l) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) \<and>
              (\<forall>v'\<in>c0'.
              \<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
              (v = (Suc 0, True, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3))"
              using c0'iscolor_lit1 c0'iscolor_lit2 step7
              by auto
            from l1 l2 l3  toliteq toliteq2 trueVarNodesNotinc0' toliteq3  helpCnotinc0'
                trueVarNodesNotinc0'_2 trueVarNodesNotinc0'_3
                step1 step2 step3 step4 step5 step6 step7 step8
            have c0_color_E_diff:
                "(\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E_diff)"
              by (simp add: c0_def c0'withvars_def E_diff_def  doubleton_eq_iff
                    gadget_c0'_empty2 E_diff_v_gadget_def lit_def)
            from  c0_color_E_diff c0_color_E' E_def2 show ?thesis
              by blast
          qed

          have c1iscolor:
              "(\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E)"
          proof -
            from c1_def c1'withvars_def doubleton_eq_iff E_diff_v_gadget_E'_empty2
              E_diff_v_gadget_E'_empty3 E_diff_v_gadget_def pos_var_edge_notin_E'
              pos_var_c1'_edge_notin_E'1 pos_var_c1'_edge_notin_E'2 edge_card1_notin_E'_2 c1'iscolor
            have c1_color_E':
                "(\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E')" by simp
            from c1'iscolor_lit1 c1'iscolor_lit2 c1'iscolor_lit3 have "\<forall>v\<in>c1'. \<forall>v'\<in>c1'.
              \<forall>l. (v = (1, False, var l, 0) \<longrightarrow> v' \<noteq> (1, True, var l, 0)) \<and>
              (v = (1, True, var l, 0) \<longrightarrow> v' \<noteq> (1, False, var l, 0)) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3"
              by blast
            have step1:"(\<forall>l. (tolit lit1 \<noteq> Pos \<and> var lit1 = var l \<longrightarrow> tolit lit3 = Pos \<or> var lit3 \<noteq> var l) \<and>
                (tolit lit1 = Pos \<and> var lit1 = var l \<longrightarrow> tolit lit3 = Pos \<longrightarrow> var lit3 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using l1 l3 toliteq toliteqNeg by fastforce
            have step2:"
                (\<forall>l. (tolit lit2 \<noteq> Pos \<and> var lit2 = var l \<longrightarrow> tolit lit3 = Pos \<or> var lit3 \<noteq> var l) \<and>
                (tolit lit2 = Pos \<and> var lit2 = var l \<longrightarrow> tolit lit3 = Pos \<longrightarrow> var lit3 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using l2 l3 toliteq toliteqNeg by fastforce
            have step3:"
                (\<forall>l. (tolit lit3 = Pos \<and> var lit3 = var l \<longrightarrow> tolit lit1 = Pos \<longrightarrow> var lit1 \<noteq> var l) \<and>
                (tolit lit3 \<noteq> Pos \<and> var lit3 = var l \<longrightarrow> tolit lit1 = Pos \<or> var lit1 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step1 by blast
            have step4:"
                (\<forall>l. (tolit lit3 = Pos \<and> var lit3 = var l \<longrightarrow> tolit lit2 = Pos \<longrightarrow> var lit2 \<noteq> var l) \<and>
                (tolit lit3 \<noteq> Pos \<and> var lit3 = var l \<longrightarrow> tolit lit2 = Pos \<or> var lit2 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step2 by auto
            have step5:"(\<forall>v'\<in>c1'.
                \<forall>l. (tolit lit3 = Pos \<and> var lit3 = var l \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                (tolit lit3 \<noteq> Pos \<and> var lit3 = var l \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by (smt FalseVarNodesNotinc1' One_nat_def l3)
            have step6:"(\<forall>v\<in>c1'.
                \<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> tolit lit3 = Pos \<or> var lit3 \<noteq> var l) \<and>
                (v = (Suc 0, True, var l, 0) \<longrightarrow> tolit lit3 = Pos \<longrightarrow> var lit3 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step5 by blast
            have step7:"\<forall>v\<in>c1'.  \<forall>v'\<in>c1'.
                      \<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                      (v = (Suc 0, True, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                      l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3"
              using c1'iscolor_lit1 c1'iscolor_lit2 c1'iscolor_lit3 by auto
            from this l1 l2 l3  toliteq toliteqNeg toliteq3_2 helpCnotinc1'
                trueVarNodesNotinc1'_2 trueVarNodesNotinc1'_3 FalseVarNodesNotinc1' falseCnotinc1'
                step1 step2 step3 step4 step5 step6 step7
            have c1_color_E_diff:
                "(\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E_diff)"
              by (simp add: c1_def c1'withvars_def E_diff_def  doubleton_eq_iff
                    gadget_c1'_empty2 E_diff_v_gadget_def lit_def)
            from c1_color_E_diff c1_color_E' E_def2 show ?thesis
              by blast
          qed


          have c2iscolor:
              "(\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E)"
          proof -
            from c2_def doubleton_eq_iff E_diff_v_gadget_E'_empty2
              E_diff_v_gadget_E'_empty3 E_diff_v_gadget_def pos_var_edge_notin_E'
              pos_var_c1'_edge_notin_E'1 pos_var_c1'_edge_notin_E'2 edge_card1_notin_E'_2 c2'iscolor
            have c2_color_E':
                "(\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E')" by simp


            from l1 l2 l3  toliteq toliteqNeg toliteq2 trueVarNodesNotinc0' toliteq3  toliteq3_2 helpCnotinc1'
                trueVarNodesNotinc1'_2 trueVarNodesNotinc1'_3 FalseVarNodesNotinc1' falseCnotinc1' varnotinc2'
                false_varnotinc2' true_varnotinc2'
            have c2_color_E_diff:
                "(\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E_diff)"
              by (simp add: c2_def E_diff_def  doubleton_eq_iff
                    gadget_c2'_empty2 E_diff_v_gadget_def lit_def)
            from c2_color_E_diff c2_color_E' E_def2 show ?thesis
              by blast
          qed

          from c0iscolor c1iscolor c2iscolor have iscolor: "(\<forall>c\<in>c_sets. \<forall>v\<in>c. \<forall>v'\<in>c. {v, v'} \<notin> E)"
            using c_sets_def by blast

          from E_ugraph c_sets_complete c_sets_sound iscolor c_sets_three_color have E_three_colorable:
            "is_k_colorable E 3 c_sets" unfolding is_k_colorable_def is_colorable_def
          by blast


          from E_three_colorable c_sets_def mainInCsets varInc1 varInc0 finalNodeInc1 show ?thesis
            by blast
        qed
      next
        case l2:False
        then show ?thesis
        proof (cases "(\<sigma>\<up>) lit3")
          case l3:True
          define c0 where c0_def:"c0 = c0'withvars \<union> {(2::nat, False, x, 0::nat),(2, False, x, 2)} "
          define c1 where c1_def:"c1 = c1'withvars \<union> {(2::nat, False, x, 3::nat),(2, False, x, 5)} "
          define c2 where c2_def:"c2 = c2' \<union> {(2::nat, False, x, 1::nat),(2, False, x, 4)}"
          define c_sets where c_sets_def: "c_sets = {c0, c1 ,c2}"
          from c1_def c1'withvars_def c2_def c0_def c0'withvars_def c_sets'_def have mainInCsets:
            " false_node \<in> c0 \<and>
              true_node \<in> c1 \<and>
              help_node \<in> c2 "
            by fastforce
          from gadget_c0'_empty gadget_c1'_empty l1 l2 l3 E_diff_v_gadget_def
            c0'c1'_empty c0_def c1_def c0'withvars_def c1'withvars_def assOfVarNodes
            have c0c1_empty:"c0 \<inter> c1 = {}"
            apply simp
            by metis
          from gadget_c0'_empty E_diff_v_gadget_def c0_def c2_def c0'withvars_def c0'c2'_empty
              gadget_c2'_empty assOfVarNodes
            have c0c2_empty:"c0 \<inter> c2 = {}"
            by simp
          from gadget_c1'_empty E_diff_v_gadget_def c1_def c2_def c1'withvars_def c1'c2'_empty
              gadget_c2'_empty assOfVarNodes
            have c1c2_empty:"c1 \<inter> c2 = {}"
            by simp



          have varInc1:
            "{(1, (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F)} \<subseteq> c1"
          proof -
            from c1_def c1'withvars_def c_sets'_def  have c1_subset1:
              "{(1, (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F')} \<subseteq> c1"
              by blast
            from c1_def c1'withvars_def  have c1_subset2:
              "{ (1::nat, (\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                                (1, (\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, (\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) } \<subseteq> c1"
              by blast
            from F'_def lit_def_1 have "{(1::nat, (\<sigma>\<up>) (Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F)} =
                              {(1::nat, (\<sigma>\<up>)(Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F')} \<union>
                              { (1::nat, (\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                                (1, (\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, (\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) }"
              by force
            from this c1_subset1 c1_subset2 show ?thesis
              by simp
          qed

          have varInc0:
            "{(1, \<not> (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F)} \<subseteq> c0"
          proof -
            from c0_def c0'withvars_def c_sets'_def  have c0_subset1:
              "{(1, \<not> (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F')} \<subseteq> c0"
              by blast
            from c0_def c0'withvars_def  have c0_subset2:
              "{ (1::nat, \<not>(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) } \<subseteq> c0"
              by blast
            from F'_def lit_def_1 have "{(1::nat, \<not>(\<sigma>\<up>) (Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F)} =
                              {(1::nat, \<not>(\<sigma>\<up>)(Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F')} \<union>
                              { (1::nat, \<not>(\<sigma>\<up>)(Pos (var lit1)), var lit1, 0::nat),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) }"
              by fastforce
            from this c0_subset1 c0_subset2 show ?thesis
              by auto
          qed

          have finalNodeInc1:
            "{(2, False, i, 5) |i. i < length F} \<subseteq> c1"
          proof -
            from c1_def c1'withvars_def c_sets'_def  have c1_subset3:
              "{(2, False, i, 5) |i. i < length F'} \<subseteq> c1"
              by blast

            from c1_def c1'withvars_def c_sets'_def  have c1_subset4:
              "{(2, False, x, 5)} \<subseteq> c1"
              by blast

            from F'_def F'_length have "{(2, False, i, 5) |i. i < length F} =
                                      {(2, False, i, 5) |i. i < length F'} \<union>
                                      {(2, False, x, 5)}"
              by fastforce
            from this c1_subset3 c1_subset4 show ?thesis
              by blast
          qed


          have c_sets_complete:"\<Union> E = \<Union> c_sets"
          proof -
            from E_diff_v_var_equ E_diff_v_def2 have E_diff_v_c0'c1'c2'_equ:"E_diff_v \<union>  c0' \<union> (c1' \<union> c2') =
              E_diff_v_main \<union> c1'withvars \<union> c0'withvars \<union> E_diff_v_gadget \<union> c2'"
              by blast
            from c_sets'_def have "
                false_node \<in> c0' \<and>
                true_node \<in> c1' \<and>
                help_node \<in> c2' "
               by simp
             from this l1 l2 l3 c0_def c1_def c2_def E_diff_v_main_def
               E_diff_v_gadget_def c1'withvars_def c0'withvars_def have
              "E_diff_v_main \<union> c1'withvars \<union> c0'withvars \<union> E_diff_v_gadget \<union> c2' = c0 \<union> (c1 \<union> c2)"
               by auto


            from this c_sets_def c_sets'_def E_diff_v_c0'c1'c2'_equ have
                "E_diff_v \<union>  \<Union> c_Sets' = \<Union> c_sets"
              by auto
            from this E_def2 c_sets'_complete show ?thesis
            by (simp add: \<open>\<Union> E_diff = E_diff_v\<close> sup_commute)
          qed


          from c_sets_def c1c2_empty c0c2_empty c0c1_empty have
            c_sets_sound:"(\<forall>c\<in>c_sets. \<forall>c'\<in>c_sets. c \<noteq> c' \<longrightarrow> c \<inter> c' = {})"
            by blast


          have c_sets_three_color:" card c_sets = 3"
          proof -
            from c0c1_empty c0_def c1_def have c0c1notEq:"c0 \<noteq> c1"
              by blast
            from c0c2_empty c0_def c2_def have c0c2notEq:"c0 \<noteq> c2"
              by blast
            from c1c2_empty c1_def c2_def have c1c2notEq:"c1 \<noteq> c2"
              by blast
            from c0c1notEq c0c2notEq c1c2notEq c_sets_def show ?thesis
              by simp
          qed


          have c0iscolor:
              "(\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E)"
          proof -
            from c0_def c0'withvars_def doubleton_eq_iff E_diff_v_gadget_E'_empty2
              E_diff_v_gadget_E'_empty3 E_diff_v_gadget_def neg_var_edge_notin_E'
              neg_var_c0'_edge_notin_E'1 neg_var_c0'_edge_notin_E'2 edge_card1_notin_E' c0'iscolor
            have c0_color_E':
                "(\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E')" by simp
            have step1:"((\<sigma>\<up>) (Pos (var lit2)) = (tolit lit1 = Pos) \<or> var lit2 \<noteq> var lit1) \<and>
                ((\<sigma>\<up>) (Pos (var lit2)) = (tolit lit3 = Pos) \<or> var lit2 \<noteq> var lit3) \<and>
                ((\<sigma>\<up>) (Pos (var lit2)) = (tolit lit1 = Pos) \<or> var lit2 \<noteq> var lit1) \<and>
                ((\<sigma>\<up>) (Pos (var lit2)) = (tolit lit3 = Pos) \<or> var lit2 \<noteq> var lit3) "
              using l1 l3 toliteq by fastforce
            have step2:"(\<forall>l. (tolit lit1 = Pos \<and> var lit1 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit2)) \<or> var lit2 \<noteq> var l) \<and>
                (tolit lit1 \<noteq> Pos \<and> var lit1 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit2)) \<longrightarrow> var lit2 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step1
              by metis
            have step3:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> tolit lit1 = Pos \<or> var lit1 \<noteq> var l) \<and>
                (\<not> (\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> tolit lit1 = Pos \<longrightarrow> var lit1 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step1
              by metis
            have step4:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var l))) \<and>
                (\<not> (\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> \<not> (\<sigma>\<up>) (Pos (var l))) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) "
              by fastforce
            have step5:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> tolit lit3 = Pos \<or> var lit3 \<noteq> var l) \<and>
                (\<not> (\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> tolit lit3 = Pos \<longrightarrow> var lit3 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step1
              by metis
            have step6:"(\<forall>v'\<in>c0'.
                \<forall>l. ((\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                (\<not> (\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by (metis (full_types) One_nat_def assOfc0Nodes)
            have step7:"(\<forall>l. (tolit lit3 = Pos \<and> var lit3 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit2)) \<or> var lit2 \<noteq> var l) \<and>
                (tolit lit3 \<noteq> Pos \<and> var lit3 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit2)) \<longrightarrow> var lit2 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) "
              using step5
              by blast
            have step8:"(\<forall>v\<in>c0'.
                (\<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> (\<sigma>\<up>) (Pos (var lit2)) \<or> var lit2 \<noteq> var l) \<and>
                (v = (Suc 0, True, var l, 0) \<longrightarrow> (\<sigma>\<up>) (Pos (var lit2)) \<longrightarrow> var lit2 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) \<and>
                (\<forall>v'\<in>c0'.
                \<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                (v = (Suc 0, True, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3))"
              using c0'iscolor_lit1 c0'iscolor_lit3 step6 by auto

            from l1 l2 l3  toliteq toliteq2 trueVarNodesNotinc0' toliteq3  helpCnotinc0'
                trueVarNodesNotinc0'_2 trueVarNodesNotinc0'_3 step1 step2 step3
                step4 step5 step6 step7 step8
            have c0_color_E_diff:
                "(\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E_diff)"
              by (simp add: c0_def c0'withvars_def E_diff_def  doubleton_eq_iff
                    gadget_c0'_empty2 E_diff_v_gadget_def lit_def)
            from  c0_color_E_diff c0_color_E' E_def2 show ?thesis
              by blast
          qed

          have c1iscolor:
              "(\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E)"
          proof -
            from c1_def c1'withvars_def doubleton_eq_iff E_diff_v_gadget_E'_empty2
              E_diff_v_gadget_E'_empty3 E_diff_v_gadget_def pos_var_edge_notin_E'
              pos_var_c1'_edge_notin_E'1 pos_var_c1'_edge_notin_E'2 edge_card1_notin_E'_2 c1'iscolor
            have c1_color_E':
                "(\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E')" by simp

            have step1:"(\<forall>l. (tolit lit1 \<noteq> Pos \<and> var lit1 = var l \<longrightarrow> tolit lit2 = Pos \<or> var lit2 \<noteq> var l) \<and>
                (tolit lit1 = Pos \<and> var lit1 = var l \<longrightarrow> tolit lit2 = Pos \<longrightarrow> var lit2 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using l1 l2 toliteq toliteqNeg by fastforce
            have step2:"(\<forall>l. (tolit lit2 = Pos \<and> var lit2 = var l \<longrightarrow> tolit lit1 = Pos \<longrightarrow> var lit1 \<noteq> var l) \<and>
                (tolit lit2 \<noteq> Pos \<and> var lit2 = var l \<longrightarrow> tolit lit1 = Pos \<or> var lit1 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step1 by blast
            have step3:"(\<forall>l. (tolit lit2 = Pos \<and> var lit2 = var l \<longrightarrow> tolit lit3 = Pos \<longrightarrow> var lit3 \<noteq> var l) \<and>
                (tolit lit2 \<noteq> Pos \<and> var lit2 = var l \<longrightarrow> tolit lit3 = Pos \<or> var lit3 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using l2 l3 toliteq toliteqNeg by fastforce
            have step4:"(\<forall>v'\<in>c1'.
                \<forall>l. (tolit lit2 = Pos \<and> var lit2 = var l \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                (tolit lit2 \<noteq> Pos \<and> var lit2 = var l \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by (smt FalseVarNodesNotinc1' One_nat_def l2)
            have step5:"(\<forall>l. (tolit lit3 \<noteq> Pos \<and> var lit3 = var l \<longrightarrow> tolit lit2 = Pos \<or> var lit2 \<noteq> var l) \<and>
                (tolit lit3 = Pos \<and> var lit3 = var l \<longrightarrow> tolit lit2 = Pos \<longrightarrow> var lit2 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step3 by blast
            have step6:"(\<forall>v\<in>c1'.
                (\<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> tolit lit2 = Pos \<or> var lit2 \<noteq> var l) \<and>
                (v = (Suc 0, True, var l, 0) \<longrightarrow> tolit lit2 = Pos \<longrightarrow> var lit2 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) \<and>
                (\<forall>v'\<in>c1'.
                \<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                (v = (Suc 0, True, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3))"
              using c1'iscolor_lit1 c1'iscolor_lit3 step4 by auto

            from l1 l2 l3  toliteq toliteqNeg toliteq3_2 helpCnotinc1'
                trueVarNodesNotinc1'_2 trueVarNodesNotinc1'_3 FalseVarNodesNotinc1' falseCnotinc1'
                step1 step2 step3 step4 step5 step6
            have c1_color_E_diff:
                "(\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E_diff)"
              by (simp add: c1_def c1'withvars_def E_diff_def  doubleton_eq_iff
                    gadget_c1'_empty2 E_diff_v_gadget_def lit_def)
            from c1_color_E_diff c1_color_E' E_def2 show ?thesis
              by blast
          qed


          have c2iscolor:
              "(\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E)"
          proof -
            from c2_def doubleton_eq_iff E_diff_v_gadget_E'_empty2
              E_diff_v_gadget_E'_empty3 E_diff_v_gadget_def pos_var_edge_notin_E'
              pos_var_c1'_edge_notin_E'1 pos_var_c1'_edge_notin_E'2 edge_card1_notin_E'_2 c2'iscolor
            have c2_color_E':
                "(\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E')" by simp


            from l1 l2 l3  toliteq toliteqNeg toliteq2 trueVarNodesNotinc0' toliteq3  toliteq3_2 helpCnotinc1'
                trueVarNodesNotinc1'_2 trueVarNodesNotinc1'_3 FalseVarNodesNotinc1' falseCnotinc1' varnotinc2'
                false_varnotinc2' true_varnotinc2'
            have c2_color_E_diff:
                "(\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E_diff)"
              by (simp add: c2_def E_diff_def  doubleton_eq_iff
                    gadget_c2'_empty2 E_diff_v_gadget_def lit_def)
            from c2_color_E_diff c2_color_E' E_def2 show ?thesis
              by blast
          qed

          from c0iscolor c1iscolor c2iscolor have iscolor: "(\<forall>c\<in>c_sets. \<forall>v\<in>c. \<forall>v'\<in>c. {v, v'} \<notin> E)"
            using c_sets_def by blast

          from E_ugraph c_sets_complete c_sets_sound iscolor c_sets_three_color have E_three_colorable:
            "is_k_colorable E 3 c_sets" unfolding is_k_colorable_def is_colorable_def
          by blast

          from E_three_colorable c_sets_def mainInCsets varInc1 varInc0 finalNodeInc1 show ?thesis
            by blast
        next
          case l3:False
          define c0 where c0_def:"c0 = c0'withvars \<union> {(2::nat, False, x, 0::nat),(2, False, x, 4)} "
          define c1 where c1_def:"c1 = c1'withvars \<union> {(2::nat, False, x, 3::nat),(2, False, x, 5)} "
          define c2 where c2_def:"c2 = c2' \<union> {(2::nat, False, x, 1::nat),(2, False, x, 2)}"
          define c_sets where c_sets_def: "c_sets = {c0, c1 ,c2}"
          from c1_def c1'withvars_def c2_def c0_def c0'withvars_def c_sets'_def have mainInCsets:
            " false_node \<in> c0 \<and>
              true_node \<in> c1 \<and>
              help_node \<in> c2 "
            by fastforce
          from gadget_c0'_empty gadget_c1'_empty l1 l2 l3 E_diff_v_gadget_def
            c0'c1'_empty c0_def c1_def c0'withvars_def c1'withvars_def assOfVarNodes
            have c0c1_empty:"c0 \<inter> c1 = {}"
            apply simp
            by metis
          from gadget_c0'_empty E_diff_v_gadget_def c0_def c2_def c0'withvars_def c0'c2'_empty
              gadget_c2'_empty assOfVarNodes
            have c0c2_empty:"c0 \<inter> c2 = {}"
            by simp
          from gadget_c1'_empty E_diff_v_gadget_def c1_def c2_def c1'withvars_def c1'c2'_empty
              gadget_c2'_empty assOfVarNodes
            have c1c2_empty:"c1 \<inter> c2 = {}"
            by simp



          have varInc1:
            "{(1, (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F)} \<subseteq> c1"
          proof -
            from c1_def c1'withvars_def c_sets'_def  have c1_subset1:
              "{(1, (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F')} \<subseteq> c1"
              by blast
            from c1_def c1'withvars_def  have c1_subset2:
              "{ (1::nat, (\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                                (1, (\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, (\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) } \<subseteq> c1"
              by blast
            from F'_def lit_def_1 have "{(1::nat, (\<sigma>\<up>) (Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F)} =
                              {(1::nat, (\<sigma>\<up>)(Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F')} \<union>
                              { (1::nat, (\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                                (1, (\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, (\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) }"
              by force
            from this c1_subset1 c1_subset2 show ?thesis
              by simp
          qed

          have varInc0:
            "{(1, \<not> (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F)} \<subseteq> c0"
          proof -
            from c0_def c0'withvars_def c_sets'_def  have c0_subset1:
              "{(1, \<not> (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F')} \<subseteq> c0"
              by blast
            from c0_def c0'withvars_def  have c0_subset2:
              "{ (1::nat, \<not>(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) } \<subseteq> c0"
              by blast
            from F'_def lit_def_1 have "{(1::nat, \<not>(\<sigma>\<up>) (Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F)} =
                              {(1::nat, \<not>(\<sigma>\<up>)(Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F')} \<union>
                              { (1::nat, \<not>(\<sigma>\<up>)(Pos (var lit1)), var lit1, 0::nat),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) }"
              by fastforce
            from this c0_subset1 c0_subset2 show ?thesis
              by auto
          qed

          have finalNodeInc1:
            "{(2, False, i, 5) |i. i < length F} \<subseteq> c1"
          proof -
            from c1_def c1'withvars_def c_sets'_def  have c1_subset3:
              "{(2, False, i, 5) |i. i < length F'} \<subseteq> c1"
              by blast

            from c1_def c1'withvars_def c_sets'_def  have c1_subset4:
              "{(2, False, x, 5)} \<subseteq> c1"
              by blast

            from F'_def F'_length have "{(2, False, i, 5) |i. i < length F} =
                                      {(2, False, i, 5) |i. i < length F'} \<union>
                                      {(2, False, x, 5)}"
              by fastforce
            from this c1_subset3 c1_subset4 show ?thesis
              by blast
          qed


          have c_sets_complete:"\<Union> E = \<Union> c_sets"
          proof -
            from E_diff_v_var_equ E_diff_v_def2 have E_diff_v_c0'c1'c2'_equ:"E_diff_v \<union>  c0' \<union> (c1' \<union> c2') =
              E_diff_v_main \<union> c1'withvars \<union> c0'withvars \<union> E_diff_v_gadget \<union> c2'"
              by blast
            from c_sets'_def have "
                false_node \<in> c0' \<and>
                true_node \<in> c1' \<and>
                help_node \<in> c2' "
               by simp
             from this l1 l2 l3 c0_def c1_def c2_def E_diff_v_main_def
               E_diff_v_gadget_def c1'withvars_def c0'withvars_def have
              "E_diff_v_main \<union> c1'withvars \<union> c0'withvars \<union> E_diff_v_gadget \<union> c2' = c0 \<union> (c1 \<union> c2)"
               by auto


            from this c_sets_def c_sets'_def E_diff_v_c0'c1'c2'_equ have
                "E_diff_v \<union>  \<Union> c_Sets' = \<Union> c_sets"
              by auto
            from this E_def2 c_sets'_complete show ?thesis
            by (simp add: \<open>\<Union> E_diff = E_diff_v\<close> sup_commute)
          qed


          from c_sets_def c1c2_empty c0c2_empty c0c1_empty have
            c_sets_sound:"(\<forall>c\<in>c_sets. \<forall>c'\<in>c_sets. c \<noteq> c' \<longrightarrow> c \<inter> c' = {})"
            by blast


          have c_sets_three_color:" card c_sets = 3"
          proof -
            from c0c1_empty c0_def c1_def have c0c1notEq:"c0 \<noteq> c1"
              by blast
            from c0c2_empty c0_def c2_def have c0c2notEq:"c0 \<noteq> c2"
              by blast
            from c1c2_empty c1_def c2_def have c1c2notEq:"c1 \<noteq> c2"
              by blast
            from c0c1notEq c0c2notEq c1c2notEq c_sets_def show ?thesis
              by simp
          qed


          have c0iscolor:
              "(\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E)"
          proof -
            from c0_def c0'withvars_def doubleton_eq_iff E_diff_v_gadget_E'_empty2
              E_diff_v_gadget_E'_empty3 E_diff_v_gadget_def neg_var_edge_notin_E'
              neg_var_c0'_edge_notin_E'1 neg_var_c0'_edge_notin_E'2 edge_card1_notin_E' c0'iscolor
            have c0_color_E':
                "(\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E')" by simp
            have step1:"((\<sigma>\<up>) (Pos (var lit2)) = (tolit lit1 = Pos) \<or> var lit2 \<noteq> var lit1) \<and>
                ((\<sigma>\<up>) (Pos (var lit3)) = (tolit lit1 = Pos) \<or> var lit3 \<noteq> var lit1) \<and>
                ((\<sigma>\<up>) (Pos (var lit2)) = (tolit lit1 = Pos) \<or> var lit2 \<noteq> var lit1) \<and>
                ((\<sigma>\<up>) (Pos (var lit3)) = (tolit lit1 = Pos) \<or> var lit3 \<noteq> var lit1) "
              using l1 toliteq
              by force
            have step2:"(\<forall>l. (tolit lit1 = Pos \<and> var lit1 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit2)) \<or> var lit2 \<noteq> var l) \<and>
                 (tolit lit1 \<noteq> Pos \<and> var lit1 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit2)) \<longrightarrow> var lit2 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step1
              by metis
            have step3:"(\<forall>l. (tolit lit1 = Pos \<and> var lit1 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit3)) \<or> var lit3 \<noteq> var l) \<and>
                 (tolit lit1 \<noteq> Pos \<and> var lit1 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit3)) \<longrightarrow> var lit3 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step1
              by metis
            have step4:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> tolit lit1 = Pos \<or> var lit1 \<noteq> var l) \<and>
                 (\<not> (\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> tolit lit1 = Pos \<longrightarrow> var lit1 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step1
              by metis
            have step5:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var l))) \<and>
                 (\<not> (\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> \<not> (\<sigma>\<up>) (Pos (var l))) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by metis
            have step6:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit3)) \<or> var lit3 \<noteq> var l) \<and>
                 (\<not> (\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit3)) \<longrightarrow> var lit3 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by metis
            have step7:"(\<forall>v'\<in>c0'.
                \<forall>l. ((\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                    (\<not> (\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                    l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by (metis (full_types) One_nat_def assOfc0Nodes)

            have step8:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> tolit lit1 = Pos \<or> var lit1 \<noteq> var l) \<and>
                 (\<not> (\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> tolit lit1 = Pos \<longrightarrow> var lit1 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step3
              by blast
            have step9:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit2)) \<or> var lit2 \<noteq> var l) \<and>
                 (\<not> (\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit2)) \<longrightarrow> var lit2 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by metis
            have step10:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var l))) \<and>
                 (\<not> (\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> \<not> (\<sigma>\<up>) (Pos (var l))) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by fastforce
            have step11:"(\<forall>v'\<in>c0'.
                \<forall>l. ((\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                    (\<not> (\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                    l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by (metis (full_types) One_nat_def assOfc0Nodes)
            have step12:"(\<forall>v\<in>c0'.
                (\<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> (\<sigma>\<up>) (Pos (var lit2)) \<or> var lit2 \<noteq> var l) \<and>
                     (v = (Suc 0, True, var l, 0) \<longrightarrow> (\<sigma>\<up>) (Pos (var lit2)) \<longrightarrow> var lit2 \<noteq> var l) \<or>
                     l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) \<and>
                (\<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> (\<sigma>\<up>) (Pos (var lit3)) \<or> var lit3 \<noteq> var l) \<and>
                     (v = (Suc 0, True, var l, 0) \<longrightarrow> (\<sigma>\<up>) (Pos (var lit3)) \<longrightarrow> var lit3 \<noteq> var l) \<or>
                     l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) \<and>
                (\<forall>v'\<in>c0'.
                    \<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                        (v = (Suc 0, True, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                        l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)) "
              by (smt One_nat_def c0'iscolor_lit1 step11 step7)

            from l1 l2 l3  toliteq toliteq2 trueVarNodesNotinc0' toliteq3  helpCnotinc0'
                trueVarNodesNotinc0'_2 trueVarNodesNotinc0'_3 step1 step2 step3 step4 step5 step6
                step7 step8 step9 step10 step11 step12
            have c0_color_E_diff:
                "(\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E_diff)"
              by (simp add: c0_def c0'withvars_def E_diff_def  doubleton_eq_iff
                    gadget_c0'_empty2 E_diff_v_gadget_def lit_def)
            from  c0_color_E_diff c0_color_E' E_def2 show ?thesis
              by blast
          qed

          have c1iscolor:
              "(\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E)"
          proof -
            from c1_def c1'withvars_def doubleton_eq_iff E_diff_v_gadget_E'_empty2
              E_diff_v_gadget_E'_empty3 E_diff_v_gadget_def pos_var_edge_notin_E'
              pos_var_c1'_edge_notin_E'1 pos_var_c1'_edge_notin_E'2 edge_card1_notin_E'_2 c1'iscolor
            have c1_color_E':
                "(\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E')" by simp

            have step1:"(\<forall>l. (tolit lit1 \<noteq> Pos \<and> var lit1 = var l \<longrightarrow> tolit lit2 = Pos \<or> var lit2 \<noteq> var l) \<and>
                 (tolit lit1 = Pos \<and> var lit1 = var l \<longrightarrow> tolit lit2 = Pos \<longrightarrow> var lit2 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) "

              using l1 l2 toliteq toliteqNeg by fastforce
            have step2:" (\<forall>l. (tolit lit1 \<noteq> Pos \<and> var lit1 = var l \<longrightarrow> tolit lit3 = Pos \<or> var lit3 \<noteq> var l) \<and>
                 (tolit lit1 = Pos \<and> var lit1 = var l \<longrightarrow> tolit lit3 = Pos \<longrightarrow> var lit3 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) "
              using l1 l3 toliteq toliteqNeg by fastforce
            have step3:" (\<forall>l. (tolit lit2 = Pos \<and> var lit2 = var l \<longrightarrow> tolit lit1 = Pos \<longrightarrow> var lit1 \<noteq> var l) \<and>
                 (tolit lit2 \<noteq> Pos \<and> var lit2 = var l \<longrightarrow> tolit lit1 = Pos \<or> var lit1 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step1 by blast
            have step4:" (\<forall>l. (tolit lit2 = Pos \<and> var lit2 = var l \<longrightarrow> tolit lit3 = Pos \<or> var lit3 \<noteq> var l) \<and>
                 (tolit lit2 \<noteq> Pos \<and> var lit2 = var l \<longrightarrow> tolit lit3 = Pos \<longrightarrow> var lit3 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by (metis l2 l3 toliteqNeg)
            have step5:" (\<forall>v'\<in>c1'.
                \<forall>l. (tolit lit2 = Pos \<and> var lit2 = var l \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                    (tolit lit2 \<noteq> Pos \<and> var lit2 = var l \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                    l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by (metis (mono_tags, lifting) One_nat_def assOfVarNodes l2 toliteqNeg)
            have step6:" (\<forall>l. (tolit lit3 = Pos \<and> var lit3 = var l \<longrightarrow> tolit lit1 = Pos \<longrightarrow> var lit1 \<noteq> var l) \<and>
                 (tolit lit3 \<noteq> Pos \<and> var lit3 = var l \<longrightarrow> tolit lit1 = Pos \<or> var lit1 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step2 by blast
            have step7:" (\<forall>l. (tolit lit3 = Pos \<and> var lit3 = var l \<longrightarrow> tolit lit2 = Pos \<or> var lit2 \<noteq> var l) \<and>
                 (tolit lit3 \<noteq> Pos \<and> var lit3 = var l \<longrightarrow> tolit lit2 = Pos \<longrightarrow> var lit2 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step4 by auto
            have step8:" (\<forall>v'\<in>c1'.
                \<forall>l. (tolit lit3 = Pos \<and> var lit3 = var l \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                    (tolit lit3 \<noteq> Pos \<and> var lit3 = var l \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                    l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by (smt FalseVarNodesNotinc1' One_nat_def l3)
            have step9:" (\<forall>v\<in>c1'.
                (\<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> tolit lit2 = Pos \<or> var lit2 \<noteq> var l) \<and>
                     (v = (Suc 0, True, var l, 0) \<longrightarrow> tolit lit2 = Pos \<longrightarrow> var lit2 \<noteq> var l) \<or>
                     l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) \<and>
                (\<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> tolit lit3 = Pos \<or> var lit3 \<noteq> var l) \<and>
                     (v = (Suc 0, True, var l, 0) \<longrightarrow> tolit lit3 = Pos \<longrightarrow> var lit3 \<noteq> var l) \<or>
                     l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) \<and>
                (\<forall>v'\<in>c1'.
                    \<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                        (v = (Suc 0, True, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                        l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3))"
              by (smt One_nat_def c1'iscolor_lit1 step5 step8)
            from l1 l2 l3  toliteq toliteqNeg toliteq3_2 helpCnotinc1'
                trueVarNodesNotinc1'_2 trueVarNodesNotinc1'_3 FalseVarNodesNotinc1' falseCnotinc1'
                step1 step2 step3 step4 step5 step6 step7 step8 step9
            have c1_color_E_diff:
                "(\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E_diff)"
              by (simp add: c1_def c1'withvars_def E_diff_def  doubleton_eq_iff
                    gadget_c1'_empty2 E_diff_v_gadget_def lit_def)
            from c1_color_E_diff c1_color_E' E_def2 show ?thesis
              by blast
          qed

          have c2iscolor:
              "(\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E)"
          proof -
            from c2_def doubleton_eq_iff E_diff_v_gadget_E'_empty2
              E_diff_v_gadget_E'_empty3 E_diff_v_gadget_def pos_var_edge_notin_E'
              pos_var_c1'_edge_notin_E'1 pos_var_c1'_edge_notin_E'2 edge_card1_notin_E'_2 c2'iscolor
            have c2_color_E':
                "(\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E')" by simp
            from l1 l2 l3  toliteq toliteqNeg toliteq2 trueVarNodesNotinc0' toliteq3  toliteq3_2 helpCnotinc1'
                trueVarNodesNotinc1'_2 trueVarNodesNotinc1'_3 FalseVarNodesNotinc1' falseCnotinc1' varnotinc2'
                false_varnotinc2' true_varnotinc2'
            have c2_color_E_diff:
                "(\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E_diff)"
              by (simp add: c2_def E_diff_def  doubleton_eq_iff
                    gadget_c2'_empty2 E_diff_v_gadget_def lit_def)
            from c2_color_E_diff c2_color_E' E_def2 show ?thesis
              by blast
          qed

          from c0iscolor c1iscolor c2iscolor have iscolor: "(\<forall>c\<in>c_sets. \<forall>v\<in>c. \<forall>v'\<in>c. {v, v'} \<notin> E)"
            using c_sets_def by blast

          from E_ugraph c_sets_complete c_sets_sound iscolor c_sets_three_color have E_three_colorable:
            "is_k_colorable E 3 c_sets" unfolding is_k_colorable_def is_colorable_def
          by blast

          from E_three_colorable c_sets_def mainInCsets varInc1 varInc0 finalNodeInc1 show ?thesis
            by blast
        qed
      qed
    next
      case l1:False
      then show ?thesis
      proof (cases "(\<sigma>\<up>) lit2"  )
        case l2:True
        then show ?thesis
        proof (cases "(\<sigma>\<up>) lit3"  )
          case l3:True
          define c0 where c0_def:"c0 = c0'withvars \<union> {(2::nat, False, x, 2::nat),(2, False, x, 3)} "
          define c1 where c1_def:"c1 = c1'withvars \<union> {(2::nat, False, x, 0::nat),(2, False, x, 5)} "
          define c2 where c2_def:"c2 = c2' \<union> {(2::nat, False, x, 1::nat),(2, False, x, 4)}"
          define c_sets where c_sets_def: "c_sets = {c0, c1 ,c2}"
          from c1_def c1'withvars_def c2_def c0_def c0'withvars_def c_sets'_def have mainInCsets:
            " false_node \<in> c0 \<and>
              true_node \<in> c1 \<and>
              help_node \<in> c2 "
            by fastforce
          from gadget_c0'_empty gadget_c1'_empty l1 l2 l3 E_diff_v_gadget_def
            c0'c1'_empty c0_def c1_def c0'withvars_def c1'withvars_def assOfVarNodes
            have c0c1_empty:"c0 \<inter> c1 = {}"
            apply simp
            by metis
          from gadget_c0'_empty E_diff_v_gadget_def c0_def c2_def c0'withvars_def c0'c2'_empty
              gadget_c2'_empty assOfVarNodes
            have c0c2_empty:"c0 \<inter> c2 = {}"
            by simp
          from gadget_c1'_empty E_diff_v_gadget_def c1_def c2_def c1'withvars_def c1'c2'_empty
              gadget_c2'_empty assOfVarNodes
            have c1c2_empty:"c1 \<inter> c2 = {}"
            by simp

          have varInc1:
            "{(1, (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F)} \<subseteq> c1"
          proof -
            from c1_def c1'withvars_def c_sets'_def  have c1_subset1:
              "{(1, (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F')} \<subseteq> c1"
              by blast
            from c1_def c1'withvars_def  have c1_subset2:
              "{ (1::nat, (\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                                (1, (\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, (\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) } \<subseteq> c1"
              by blast
            from F'_def lit_def_1 have "{(1::nat, (\<sigma>\<up>) (Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F)} =
                              {(1::nat, (\<sigma>\<up>)(Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F')} \<union>
                              { (1::nat, (\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                                (1, (\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, (\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) }"
              by force
            from this c1_subset1 c1_subset2 show ?thesis
              by simp
          qed

          have varInc0:
            "{(1, \<not> (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F)} \<subseteq> c0"
          proof -
            from c0_def c0'withvars_def c_sets'_def  have c0_subset1:
              "{(1, \<not> (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F')} \<subseteq> c0"
              by blast
            from c0_def c0'withvars_def  have c0_subset2:
              "{ (1::nat, \<not>(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) } \<subseteq> c0"
              by blast
            from F'_def lit_def_1 have "{(1::nat, \<not>(\<sigma>\<up>) (Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F)} =
                              {(1::nat, \<not>(\<sigma>\<up>)(Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F')} \<union>
                              { (1::nat, \<not>(\<sigma>\<up>)(Pos (var lit1)), var lit1, 0::nat),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) }"
              by fastforce
            from this c0_subset1 c0_subset2 show ?thesis
              by auto
          qed

          have finalNodeInc1:
            "{(2, False, i, 5) |i. i < length F} \<subseteq> c1"
          proof -
            from c1_def c1'withvars_def c_sets'_def  have c1_subset3:
              "{(2, False, i, 5) |i. i < length F'} \<subseteq> c1"
              by blast

            from c1_def c1'withvars_def c_sets'_def  have c1_subset4:
              "{(2, False, x, 5)} \<subseteq> c1"
              by blast

            from F'_def F'_length have "{(2, False, i, 5) |i. i < length F} =
                                      {(2, False, i, 5) |i. i < length F'} \<union>
                                      {(2, False, x, 5)}"
              by fastforce
            from this c1_subset3 c1_subset4 show ?thesis
              by blast
          qed


          have c_sets_complete:"\<Union> E = \<Union> c_sets"
          proof -
            from E_diff_v_var_equ E_diff_v_def2 have E_diff_v_c0'c1'c2'_equ:"E_diff_v \<union>  c0' \<union> (c1' \<union> c2') =
              E_diff_v_main \<union> c1'withvars \<union> c0'withvars \<union> E_diff_v_gadget \<union> c2'"
              by blast
            from c_sets'_def have "
                false_node \<in> c0' \<and>
                true_node \<in> c1' \<and>
                help_node \<in> c2' "
               by simp
             from this l1 l2 l3 c0_def c1_def c2_def E_diff_v_main_def
               E_diff_v_gadget_def c1'withvars_def c0'withvars_def have
              "E_diff_v_main \<union> c1'withvars \<union> c0'withvars \<union> E_diff_v_gadget \<union> c2' = c0 \<union> (c1 \<union> c2)"
               by auto


            from this c_sets_def c_sets'_def E_diff_v_c0'c1'c2'_equ have
                "E_diff_v \<union>  \<Union> c_Sets' = \<Union> c_sets"
              by auto
            from this E_def2 c_sets'_complete show ?thesis
            by (simp add: \<open>\<Union> E_diff = E_diff_v\<close> sup_commute)
          qed


          from c_sets_def c1c2_empty c0c2_empty c0c1_empty have
            c_sets_sound:"(\<forall>c\<in>c_sets. \<forall>c'\<in>c_sets. c \<noteq> c' \<longrightarrow> c \<inter> c' = {})"
            by blast


          have c_sets_three_color:" card c_sets = 3"
          proof -
            from c0c1_empty c0_def c1_def have c0c1notEq:"c0 \<noteq> c1"
              by blast
            from c0c2_empty c0_def c2_def have c0c2notEq:"c0 \<noteq> c2"
              by blast
            from c1c2_empty c1_def c2_def have c1c2notEq:"c1 \<noteq> c2"
              by blast
            from c0c1notEq c0c2notEq c1c2notEq c_sets_def show ?thesis
              by simp
          qed


          have c0iscolor:
              "(\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E)"
          proof -
            from c0_def c0'withvars_def doubleton_eq_iff E_diff_v_gadget_E'_empty2
              E_diff_v_gadget_E'_empty3 E_diff_v_gadget_def neg_var_edge_notin_E'
              neg_var_c0'_edge_notin_E'1 neg_var_c0'_edge_notin_E'2 edge_card1_notin_E' c0'iscolor
            have c0_color_E':
                "(\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E')" by simp
            have step1:"((\<sigma>\<up>) (Pos (var lit1)) = (tolit lit3 = Pos) \<or> var lit1 \<noteq> var lit3)"
              using l3 toliteq by metis
            have step2:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var l))) \<and>
                 (\<not> (\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> \<not> (\<sigma>\<up>) (Pos (var l))) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by force
            have step3:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> tolit lit2 = Pos \<or> var lit2 \<noteq> var l) \<and>
                 (\<not> (\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> tolit lit2 = Pos \<longrightarrow> var lit2 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using l2 toliteq by metis
            have step4:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> tolit lit3 = Pos \<or> var lit3 \<noteq> var l) \<and>
                 (\<not> (\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> tolit lit3 = Pos \<longrightarrow> var lit3 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step1 by fastforce
            have step5:"(\<forall>v'\<in>c0'.
                \<forall>l. ((\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                    (\<not> (\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                    l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) "
              by (metis (full_types) One_nat_def assOfc0Nodes)
            have step6:"(\<forall>l. (tolit lit2 = Pos \<and> var lit2 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit1)) \<or> var lit1 \<noteq> var l) \<and>
                 (tolit lit2 \<noteq> Pos \<and> var lit2 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit1)) \<longrightarrow> var lit1 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step3 by blast
            have step7:"(\<forall>l. (tolit lit3 = Pos \<and> var lit3 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit1)) \<or> var lit1 \<noteq> var l) \<and>
                 (tolit lit3 \<noteq> Pos \<and> var lit3 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit1)) \<longrightarrow> var lit1 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) "
              using step4 by blast
            have step8:"(\<forall>v\<in>c0'.
                (\<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> (\<sigma>\<up>) (Pos (var lit1)) \<or> var lit1 \<noteq> var l) \<and>
                     (v = (Suc 0, True, var l, 0) \<longrightarrow> (\<sigma>\<up>) (Pos (var lit1)) \<longrightarrow> var lit1 \<noteq> var l) \<or>
                     l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) \<and>
                (\<forall>v'\<in>c0'.
                    \<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                        (v = (Suc 0, True, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                        l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3))"
              using c0'iscolor_lit2 c0'iscolor_lit3 step5 by auto
            from l1 l2 l3  toliteq toliteq2 trueVarNodesNotinc0' toliteq3  helpCnotinc0'
                trueVarNodesNotinc0'_2 trueVarNodesNotinc0'_3 step1 step2 step3 step4 step5
                step6 step7 step8
            have c0_color_E_diff:
                "(\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E_diff)"
              by (simp add: c0_def c0'withvars_def E_diff_def  doubleton_eq_iff
                    gadget_c0'_empty2 E_diff_v_gadget_def lit_def)
            from  c0_color_E_diff c0_color_E' E_def2 show ?thesis
              by blast
          qed

          have c1iscolor:
              "(\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E)"
          proof -
            from c1_def c1'withvars_def doubleton_eq_iff E_diff_v_gadget_E'_empty2
              E_diff_v_gadget_E'_empty3 E_diff_v_gadget_def pos_var_edge_notin_E'
              pos_var_c1'_edge_notin_E'1 pos_var_c1'_edge_notin_E'2 edge_card1_notin_E'_2 c1'iscolor
            have c1_color_E':
                "(\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E')" by simp
            have step1:"((tolit lit2 = Pos) = (tolit lit1 \<noteq> Pos) \<or> var lit2 \<noteq> var lit1) \<and>
              ((tolit lit3 = Pos) = (tolit lit1 \<noteq> Pos) \<or> var lit3 \<noteq> var lit1) \<and>
              ((tolit lit2 = Pos) = (tolit lit1 \<noteq> Pos) \<or> var lit2 \<noteq> var lit1)\<and>
              ((tolit lit3 = Pos) = (tolit lit1 \<noteq> Pos) \<or> var lit3 \<noteq> var lit1)"
              using l1 l2 l3 toliteq toliteqNeg by fastforce
            have step2:"(\<forall>l. (tolit lit1 = Pos \<and> var lit1 = var l \<longrightarrow> tolit lit2 = Pos \<longrightarrow> var lit2 \<noteq> var l) \<and>
              (tolit lit1 \<noteq> Pos \<and> var lit1 = var l \<longrightarrow> tolit lit2 = Pos \<or> var lit2 \<noteq> var l) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step1
              by metis
            have step3:"(\<forall>l. (tolit lit1 = Pos \<and> var lit1 = var l \<longrightarrow> tolit lit3 = Pos \<longrightarrow> var lit3 \<noteq> var l) \<and>
              (tolit lit1 \<noteq> Pos \<and> var lit1 = var l \<longrightarrow> tolit lit3 = Pos \<or> var lit3 \<noteq> var l) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step1
              by metis
            have step4:"(\<forall>v'\<in>c1'.
              \<forall>l. (tolit lit1 = Pos \<and> var lit1 = var l \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
              (tolit lit1 \<noteq> Pos \<and> var lit1 = var l \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) "
              by (smt FalseVarNodesNotinc1' One_nat_def l1)
            have step5:"(\<forall>l. (tolit lit2 \<noteq> Pos \<and> var lit2 = var l \<longrightarrow> tolit lit1 = Pos \<or> var lit1 \<noteq> var l) \<and>
              (tolit lit2 = Pos \<and> var lit2 = var l \<longrightarrow> tolit lit1 = Pos \<longrightarrow> var lit1 \<noteq> var l) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step1 by metis

            have step6:"(\<forall>l. (tolit lit3 \<noteq> Pos \<and> var lit3 = var l \<longrightarrow> tolit lit1 = Pos \<or> var lit1 \<noteq> var l) \<and>
              (tolit lit3 = Pos \<and> var lit3 = var l \<longrightarrow> tolit lit1 = Pos \<longrightarrow> var lit1 \<noteq> var l) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step1
              by metis
            have step7:"(\<forall>v\<in>c1'.
              (\<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> tolit lit1 = Pos \<or> var lit1 \<noteq> var l) \<and>
              (v = (Suc 0, True, var l, 0) \<longrightarrow> tolit lit1 = Pos \<longrightarrow> var lit1 \<noteq> var l) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) \<and>
              (\<forall>v'\<in>c1'.
              \<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
              (v = (Suc 0, True, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3))"
              using c1'iscolor_lit2 c1'iscolor_lit3 step4
              by auto
            from l1 l2 l3  toliteq toliteqNeg toliteq3_2 helpCnotinc1'
                trueVarNodesNotinc1'_2 trueVarNodesNotinc1'_3 FalseVarNodesNotinc1' falseCnotinc1'
                step1 step2 step3 step4 step5 step6 step7
            have c1_color_E_diff:
                "(\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E_diff)"
              by (simp add: c1_def c1'withvars_def E_diff_def  doubleton_eq_iff
                    gadget_c1'_empty2 E_diff_v_gadget_def lit_def)
            from c1_color_E_diff c1_color_E' E_def2 show ?thesis
              by blast
          qed


          have c2iscolor:
              "(\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E)"
          proof -
            from c2_def doubleton_eq_iff E_diff_v_gadget_E'_empty2
              E_diff_v_gadget_E'_empty3 E_diff_v_gadget_def pos_var_edge_notin_E'
              pos_var_c1'_edge_notin_E'1 pos_var_c1'_edge_notin_E'2 edge_card1_notin_E'_2 c2'iscolor
            have c2_color_E':
                "(\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E')" by simp


            from l1 l2 l3  toliteq toliteqNeg toliteq2 trueVarNodesNotinc0' toliteq3  toliteq3_2 helpCnotinc1'
                trueVarNodesNotinc1'_2 trueVarNodesNotinc1'_3 FalseVarNodesNotinc1' falseCnotinc1' varnotinc2'
                false_varnotinc2' true_varnotinc2'
            have c2_color_E_diff:
                "(\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E_diff)"
              by (simp add: c2_def E_diff_def  doubleton_eq_iff
                    gadget_c2'_empty2 E_diff_v_gadget_def lit_def)
            from c2_color_E_diff c2_color_E' E_def2 show ?thesis
              by blast
          qed

          from c0iscolor c1iscolor c2iscolor have iscolor: "(\<forall>c\<in>c_sets. \<forall>v\<in>c. \<forall>v'\<in>c. {v, v'} \<notin> E)"
            using c_sets_def by blast

          from E_ugraph c_sets_complete c_sets_sound iscolor c_sets_three_color have E_three_colorable:
            "is_k_colorable E 3 c_sets" unfolding is_k_colorable_def is_colorable_def
          by blast

          from E_three_colorable c_sets_def mainInCsets varInc1 varInc0 finalNodeInc1 show ?thesis
            by blast
        next
          case l3:False
          define c0 where c0_def:"c0 = c0'withvars \<union> {(2::nat, False, x, 1::nat),(2, False, x, 4)} "
          define c1 where c1_def:"c1 = c1'withvars \<union> {(2::nat, False, x, 3::nat),(2, False, x, 5)} "
          define c2 where c2_def:"c2 = c2' \<union> {(2::nat, False, x, 0::nat),(2, False, x, 2)}"
          define c_sets where c_sets_def: "c_sets = {c0, c1 ,c2}"
          from c1_def c1'withvars_def c2_def c0_def c0'withvars_def c_sets'_def have mainInCsets:
            " false_node \<in> c0 \<and>
              true_node \<in> c1 \<and>
              help_node \<in> c2 "
            by fastforce
          from gadget_c0'_empty gadget_c1'_empty l1 l2 l3 E_diff_v_gadget_def
            c0'c1'_empty c0_def c1_def c0'withvars_def c1'withvars_def assOfVarNodes
            have c0c1_empty:"c0 \<inter> c1 = {}"
            apply simp
            by metis
          from gadget_c0'_empty E_diff_v_gadget_def c0_def c2_def c0'withvars_def c0'c2'_empty
              gadget_c2'_empty assOfVarNodes
            have c0c2_empty:"c0 \<inter> c2 = {}"
            by simp
          from gadget_c1'_empty E_diff_v_gadget_def c1_def c2_def c1'withvars_def c1'c2'_empty
              gadget_c2'_empty assOfVarNodes
            have c1c2_empty:"c1 \<inter> c2 = {}"
            by simp



          have varInc1:
            "{(1, (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F)} \<subseteq> c1"
          proof -
            from c1_def c1'withvars_def c_sets'_def  have c1_subset1:
              "{(1, (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F')} \<subseteq> c1"
              by blast
            from c1_def c1'withvars_def  have c1_subset2:
              "{ (1::nat, (\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                                (1, (\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, (\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) } \<subseteq> c1"
              by blast
            from F'_def lit_def_1 have "{(1::nat, (\<sigma>\<up>) (Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F)} =
                              {(1::nat, (\<sigma>\<up>)(Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F')} \<union>
                              { (1::nat, (\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                                (1, (\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, (\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) }"
              by force
            from this c1_subset1 c1_subset2 show ?thesis
              by simp
          qed

          have varInc0:
            "{(1, \<not> (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F)} \<subseteq> c0"
          proof -
            from c0_def c0'withvars_def c_sets'_def  have c0_subset1:
              "{(1, \<not> (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F')} \<subseteq> c0"
              by blast
            from c0_def c0'withvars_def  have c0_subset2:
              "{ (1::nat, \<not>(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) } \<subseteq> c0"
              by blast
            from F'_def lit_def_1 have "{(1::nat, \<not>(\<sigma>\<up>) (Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F)} =
                              {(1::nat, \<not>(\<sigma>\<up>)(Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F')} \<union>
                              { (1::nat, \<not>(\<sigma>\<up>)(Pos (var lit1)), var lit1, 0::nat),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) }"
              by fastforce
            from this c0_subset1 c0_subset2 show ?thesis
              by auto
          qed

          have finalNodeInc1:
            "{(2, False, i, 5) |i. i < length F} \<subseteq> c1"
          proof -
            from c1_def c1'withvars_def c_sets'_def  have c1_subset3:
              "{(2, False, i, 5) |i. i < length F'} \<subseteq> c1"
              by blast

            from c1_def c1'withvars_def c_sets'_def  have c1_subset4:
              "{(2, False, x, 5)} \<subseteq> c1"
              by blast

            from F'_def F'_length have "{(2, False, i, 5) |i. i < length F} =
                                      {(2, False, i, 5) |i. i < length F'} \<union>
                                      {(2, False, x, 5)}"
              by fastforce
            from this c1_subset3 c1_subset4 show ?thesis
              by blast
          qed


          have c_sets_complete:"\<Union> E = \<Union> c_sets"
          proof -
            from E_diff_v_var_equ E_diff_v_def2 have E_diff_v_c0'c1'c2'_equ:"E_diff_v \<union>  c0' \<union> (c1' \<union> c2') =
              E_diff_v_main \<union> c1'withvars \<union> c0'withvars \<union> E_diff_v_gadget \<union> c2'"
              by blast
            from c_sets'_def have "
                false_node \<in> c0' \<and>
                true_node \<in> c1' \<and>
                help_node \<in> c2' "
               by simp
             from this l1 l2 l3 c0_def c1_def c2_def E_diff_v_main_def
               E_diff_v_gadget_def c1'withvars_def c0'withvars_def have
              "E_diff_v_main \<union> c1'withvars \<union> c0'withvars \<union> E_diff_v_gadget \<union> c2' = c0 \<union> (c1 \<union> c2)"
               by auto


            from this c_sets_def c_sets'_def E_diff_v_c0'c1'c2'_equ have
                "E_diff_v \<union>  \<Union> c_Sets' = \<Union> c_sets"
              by auto
            from this E_def2 c_sets'_complete show ?thesis
            by (simp add: \<open>\<Union> E_diff = E_diff_v\<close> sup_commute)
          qed


          from c_sets_def c1c2_empty c0c2_empty c0c1_empty have
            c_sets_sound:"(\<forall>c\<in>c_sets. \<forall>c'\<in>c_sets. c \<noteq> c' \<longrightarrow> c \<inter> c' = {})"
            by blast


          have c_sets_three_color:" card c_sets = 3"
          proof -
            from c0c1_empty c0_def c1_def have c0c1notEq:"c0 \<noteq> c1"
              by blast
            from c0c2_empty c0_def c2_def have c0c2notEq:"c0 \<noteq> c2"
              by blast
            from c1c2_empty c1_def c2_def have c1c2notEq:"c1 \<noteq> c2"
              by blast
            from c0c1notEq c0c2notEq c1c2notEq c_sets_def show ?thesis
              by simp
          qed


          have c0iscolor:
              "(\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E)"
          proof -
            from c0_def c0'withvars_def doubleton_eq_iff E_diff_v_gadget_E'_empty2
              E_diff_v_gadget_E'_empty3 E_diff_v_gadget_def neg_var_edge_notin_E'
              neg_var_c0'_edge_notin_E'1 neg_var_c0'_edge_notin_E'2 edge_card1_notin_E' c0'iscolor
            have c0_color_E':
                "(\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E')" by simp
            have step1:"((\<sigma>\<up>) (Pos (var lit1)) = (tolit lit2 = Pos) \<or> var lit1 \<noteq> var lit2) \<and>
            ((\<sigma>\<up>) (Pos (var lit3)) = (tolit lit2 = Pos) \<or> var lit3 \<noteq> var lit2) \<and>
            ((\<sigma>\<up>) (Pos (var lit1)) = (tolit lit2 = Pos) \<or> var lit1 \<noteq> var lit2) \<and>
            ((\<sigma>\<up>) (Pos (var lit3)) = (tolit lit2 = Pos) \<or> var lit3 \<noteq> var lit2)"
              using l2 toliteq by fastforce
            have step2:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var l))) \<and>
                 (\<not> (\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> \<not> (\<sigma>\<up>) (Pos (var l))) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by fastforce
            have step3:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> tolit lit2 = Pos \<or> var lit2 \<noteq> var l) \<and>
                 (\<not> (\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> tolit lit2 = Pos \<longrightarrow> var lit2 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step1 by metis
            have step4:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit3)) \<or> var lit3 \<noteq> var l) \<and>
                 (\<not> (\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit3)) \<longrightarrow> var lit3 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) "
              by force
            have step5:"(\<forall>v'\<in>c0'.
                \<forall>l. ((\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                    (\<not> (\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                    l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by (metis (full_types) One_nat_def assOfc0Nodes)
            have step6:"(\<forall>l. (tolit lit2 = Pos \<and> var lit2 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit1)) \<or> var lit1 \<noteq> var l) \<and>
                 (tolit lit2 \<noteq> Pos \<and> var lit2 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit1)) \<longrightarrow> var lit1 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step1 by metis
            have step7:"(\<forall>l. (tolit lit2 = Pos \<and> var lit2 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit3)) \<or> var lit3 \<noteq> var l) \<and>
                 (tolit lit2 \<noteq> Pos \<and> var lit2 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit3)) \<longrightarrow> var lit3 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step1 by metis
            have step8:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit1)) \<or> var lit1 \<noteq> var l) \<and>
                 (\<not> (\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit1)) \<longrightarrow> var lit1 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by force
            have step9:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> tolit lit2 = Pos \<or> var lit2 \<noteq> var l) \<and>
                 (\<not> (\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> tolit lit2 = Pos \<longrightarrow> var lit2 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) "
              using step7 by blast
            have step10:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var l))) \<and>
                 (\<not> (\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> \<not> (\<sigma>\<up>) (Pos (var l))) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by fastforce
            have step11:"(\<forall>v'\<in>c0'.
                \<forall>l. ((\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                    (\<not> (\<sigma>\<up>) (Pos (var lit3)) \<and> var lit3 = var l \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                    l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by (metis (full_types) One_nat_def assOfc0Nodes)
            have step12:"(\<forall>v\<in>c0'.
                (\<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> (\<sigma>\<up>) (Pos (var lit1)) \<or> var lit1 \<noteq> var l) \<and>
                     (v = (Suc 0, True, var l, 0) \<longrightarrow> (\<sigma>\<up>) (Pos (var lit1)) \<longrightarrow> var lit1 \<noteq> var l) \<or>
                     l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) \<and>
                (\<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> (\<sigma>\<up>) (Pos (var lit3)) \<or> var lit3 \<noteq> var l) \<and>
                     (v = (Suc 0, True, var l, 0) \<longrightarrow> (\<sigma>\<up>) (Pos (var lit3)) \<longrightarrow> var lit3 \<noteq> var l) \<or>
                     l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) \<and>
                (\<forall>v'\<in>c0'.
                    \<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                        (v = (Suc 0, True, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                        l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3))"
              by (smt One_nat_def c0'iscolor_lit2 step11 step5)
            from l1 l2 l3  toliteq toliteq2 trueVarNodesNotinc0' toliteq3  helpCnotinc0'
                trueVarNodesNotinc0'_2 trueVarNodesNotinc0'_3 step1 step2 step3 step4 step5
                step6 step7 step8 step9 step10 step11 step12
            have c0_color_E_diff:
                "(\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E_diff)"
              by (simp add: c0_def c0'withvars_def E_diff_def  doubleton_eq_iff
                    gadget_c0'_empty2 E_diff_v_gadget_def lit_def)
            from  c0_color_E_diff c0_color_E' E_def2 show ?thesis
              by blast
          qed

          have c1iscolor:
              "(\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E)"
          proof -
            from c1_def c1'withvars_def doubleton_eq_iff E_diff_v_gadget_E'_empty2
              E_diff_v_gadget_E'_empty3 E_diff_v_gadget_def pos_var_edge_notin_E'
              pos_var_c1'_edge_notin_E'1 pos_var_c1'_edge_notin_E'2 edge_card1_notin_E'_2 c1'iscolor
            have c1_color_E':
                "(\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E')" by simp

            have step1:"(\<forall>l. (tolit lit1 = Pos \<and> var lit1 = var l \<longrightarrow> tolit lit2 = Pos \<longrightarrow> var lit2 \<noteq> var l) \<and>
              (tolit lit1 \<noteq> Pos \<and> var lit1 = var l \<longrightarrow> tolit lit2 = Pos \<or> var lit2 \<noteq> var l) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using l1 l2 toliteq toliteqNeg by fastforce

            have step2:
              "(\<forall>l. (tolit lit1 = Pos \<and> var lit1 = var l \<longrightarrow> tolit lit3 = Pos \<or> var lit3 \<noteq> var l) \<and>
              (tolit lit1 \<noteq> Pos \<and> var lit1 = var l \<longrightarrow> tolit lit3 = Pos \<longrightarrow> var lit3 \<noteq> var l) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by (metis l1 l3 toliteqNeg)
            have step3:"
              (\<forall>v'\<in>c1'.
              \<forall>l. (tolit lit1 = Pos \<and> var lit1 = var l \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
              (tolit lit1 \<noteq> Pos \<and> var lit1 = var l \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) "
              by (smt FalseVarNodesNotinc1' One_nat_def l1)
            have step4:"
              (\<forall>l. (tolit lit2 \<noteq> Pos \<and> var lit2 = var l \<longrightarrow> tolit lit1 = Pos \<or> var lit1 \<noteq> var l) \<and>
              (tolit lit2 = Pos \<and> var lit2 = var l \<longrightarrow> tolit lit1 = Pos \<longrightarrow> var lit1 \<noteq> var l) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
            using step1 by auto
            have step5:"(\<forall>l. (tolit lit2 \<noteq> Pos \<and> var lit2 = var l \<longrightarrow> tolit lit3 = Pos \<or> var lit3 \<noteq> var l) \<and>
              (tolit lit2 = Pos \<and> var lit2 = var l \<longrightarrow> tolit lit3 = Pos \<longrightarrow> var lit3 \<noteq> var l) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) "
            using l2 l3 toliteq toliteqNeg by fastforce
            have step6:"(\<forall>l. (tolit lit3 = Pos \<and> var lit3 = var l \<longrightarrow> tolit lit1 = Pos \<or> var lit1 \<noteq> var l) \<and>
              (tolit lit3 \<noteq> Pos \<and> var lit3 = var l \<longrightarrow> tolit lit1 = Pos \<longrightarrow> var lit1 \<noteq> var l) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
            using step2 by blast
            have step7:"(\<forall>l. (tolit lit3 = Pos \<and> var lit3 = var l \<longrightarrow> tolit lit2 = Pos \<longrightarrow> var lit2 \<noteq> var l) \<and>
              (tolit lit3 \<noteq> Pos \<and> var lit3 = var l \<longrightarrow> tolit lit2 = Pos \<or> var lit2 \<noteq> var l) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
            using step5 by blast
            have step8:"
              (\<forall>v'\<in>c1'.
              \<forall>l. (tolit lit3 = Pos \<and> var lit3 = var l \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
              (tolit lit3 \<noteq> Pos \<and> var lit3 = var l \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
            by (metis (mono_tags, lifting) One_nat_def assOfVarNodes l3 toliteqNeg)
            have"
              (\<forall>v\<in>c1'.
              (\<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> tolit lit1 = Pos \<or> var lit1 \<noteq> var l) \<and>
              (v = (Suc 0, True, var l, 0) \<longrightarrow> tolit lit1 = Pos \<longrightarrow> var lit1 \<noteq> var l) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) \<and>
              (\<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> tolit lit3 = Pos \<or> var lit3 \<noteq> var l) \<and>
              (v = (Suc 0, True, var l, 0) \<longrightarrow> tolit lit3 = Pos \<longrightarrow> var lit3 \<noteq> var l) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) \<and>
              (\<forall>v'\<in>c1'.
              \<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
              (v = (Suc 0, True, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
              l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3))"
            by (smt One_nat_def c1'iscolor_lit2 step3 step8)
            from l1 l2 l3  toliteq toliteqNeg toliteq3_2 helpCnotinc1'
                trueVarNodesNotinc1'_2 trueVarNodesNotinc1'_3 FalseVarNodesNotinc1' falseCnotinc1'
                step1 step2 step3 step4 step5 step6 step7 step8 this
            have c1_color_E_diff:
                "(\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E_diff)"
              by (simp add: c1_def c1'withvars_def E_diff_def  doubleton_eq_iff
                    gadget_c1'_empty2 E_diff_v_gadget_def lit_def)
            from c1_color_E_diff c1_color_E' E_def2 show ?thesis
              by blast
          qed


          have c2iscolor:
              "(\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E)"
          proof -
            from c2_def doubleton_eq_iff E_diff_v_gadget_E'_empty2
              E_diff_v_gadget_E'_empty3 E_diff_v_gadget_def pos_var_edge_notin_E'
              pos_var_c1'_edge_notin_E'1 pos_var_c1'_edge_notin_E'2 edge_card1_notin_E'_2 c2'iscolor
            have c2_color_E':
                "(\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E')" by simp
            from l1 l2 l3  toliteq toliteqNeg toliteq2 trueVarNodesNotinc0' toliteq3  toliteq3_2 helpCnotinc1'
                trueVarNodesNotinc1'_2 trueVarNodesNotinc1'_3 FalseVarNodesNotinc1' falseCnotinc1' varnotinc2'
                false_varnotinc2' true_varnotinc2'
            have c2_color_E_diff:
                "(\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E_diff)"
              by (simp add: c2_def E_diff_def  doubleton_eq_iff
                    gadget_c2'_empty2 E_diff_v_gadget_def lit_def)
            from c2_color_E_diff c2_color_E' E_def2 show ?thesis
              by blast
          qed

          from c0iscolor c1iscolor c2iscolor have iscolor: "(\<forall>c\<in>c_sets. \<forall>v\<in>c. \<forall>v'\<in>c. {v, v'} \<notin> E)"
            using c_sets_def by blast

          from E_ugraph c_sets_complete c_sets_sound iscolor c_sets_three_color have E_three_colorable:
            "is_k_colorable E 3 c_sets" unfolding is_k_colorable_def is_colorable_def
          by blast

          from E_three_colorable c_sets_def mainInCsets varInc1 varInc0 finalNodeInc1 show ?thesis
            by blast
        qed
      next
        case l2:False
        then show ?thesis
        proof (cases "(\<sigma>\<up>) lit3"  )
          case l3:True
          define c0 where c0_def:"c0 = c0'withvars \<union> {(2::nat, False, x, 2::nat),(2, False, x, 3)} "
          define c1 where c1_def:"c1 = c1'withvars \<union> {(2::nat, False, x, 0::nat),(2, False, x, 5)} "
          define c2 where c2_def:"c2 = c2' \<union> {(2::nat, False, x, 1::nat),(2, False, x, 4)}"
          define c_sets where c_sets_def: "c_sets = {c0, c1 ,c2}"
          from c1_def c1'withvars_def c2_def c0_def c0'withvars_def c_sets'_def have mainInCsets:
            " false_node \<in> c0 \<and>
              true_node \<in> c1 \<and>
              help_node \<in> c2 "
            by fastforce
          from gadget_c0'_empty gadget_c1'_empty l1 l2 l3 E_diff_v_gadget_def
            c0'c1'_empty c0_def c1_def c0'withvars_def c1'withvars_def assOfVarNodes
            have c0c1_empty:"c0 \<inter> c1 = {}"
            apply simp
            by metis
          from gadget_c0'_empty E_diff_v_gadget_def c0_def c2_def c0'withvars_def c0'c2'_empty
              gadget_c2'_empty assOfVarNodes
            have c0c2_empty:"c0 \<inter> c2 = {}"
            by simp
          from gadget_c1'_empty E_diff_v_gadget_def c1_def c2_def c1'withvars_def c1'c2'_empty
              gadget_c2'_empty assOfVarNodes
            have c1c2_empty:"c1 \<inter> c2 = {}"
            by simp



          have varInc1:
            "{(1, (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F)} \<subseteq> c1"
          proof -
            from c1_def c1'withvars_def c_sets'_def  have c1_subset1:
              "{(1, (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F')} \<subseteq> c1"
              by blast
            from c1_def c1'withvars_def  have c1_subset2:
              "{ (1::nat, (\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                                (1, (\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, (\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) } \<subseteq> c1"
              by blast
            from F'_def lit_def_1 have "{(1::nat, (\<sigma>\<up>) (Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F)} =
                              {(1::nat, (\<sigma>\<up>)(Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F')} \<union>
                              { (1::nat, (\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                                (1, (\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, (\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) }"
              by force
            from this c1_subset1 c1_subset2 show ?thesis
              by simp
          qed

          have varInc0:
            "{(1, \<not> (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F)} \<subseteq> c0"
          proof -
            from c0_def c0'withvars_def c_sets'_def  have c0_subset1:
              "{(1, \<not> (\<sigma>\<up>) (Pos (var l)), var l, 0) |l. l \<in> \<Union> (set F')} \<subseteq> c0"
              by blast
            from c0_def c0'withvars_def  have c0_subset2:
              "{ (1::nat, \<not>(\<sigma>\<up>) (Pos (var lit1)), var lit1, 0::nat),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) } \<subseteq> c0"
              by blast
            from F'_def lit_def_1 have "{(1::nat, \<not>(\<sigma>\<up>) (Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F)} =
                              {(1::nat, \<not>(\<sigma>\<up>)(Pos (var l)), (var l)::nat, 0::nat) |l. l \<in> \<Union> (set F')} \<union>
                              { (1::nat, \<not>(\<sigma>\<up>)(Pos (var lit1)), var lit1, 0::nat),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit2)), var lit2, 0),
                                (1, \<not>(\<sigma>\<up>) (Pos (var lit3)), var lit3, 0) }"
              by fastforce
            from this c0_subset1 c0_subset2 show ?thesis
              by auto
          qed

          have finalNodeInc1:
            "{(2, False, i, 5) |i. i < length F} \<subseteq> c1"
          proof -
            from c1_def c1'withvars_def c_sets'_def  have c1_subset3:
              "{(2, False, i, 5) |i. i < length F'} \<subseteq> c1"
              by blast

            from c1_def c1'withvars_def c_sets'_def  have c1_subset4:
              "{(2, False, x, 5)} \<subseteq> c1"
              by blast

            from F'_def F'_length have "{(2, False, i, 5) |i. i < length F} =
                                      {(2, False, i, 5) |i. i < length F'} \<union>
                                      {(2, False, x, 5)}"
              by fastforce
            from this c1_subset3 c1_subset4 show ?thesis
              by blast
          qed


          have c_sets_complete:"\<Union> E = \<Union> c_sets"
          proof -
            from E_diff_v_var_equ E_diff_v_def2 have E_diff_v_c0'c1'c2'_equ:"E_diff_v \<union>  c0' \<union> (c1' \<union> c2') =
              E_diff_v_main \<union> c1'withvars \<union> c0'withvars \<union> E_diff_v_gadget \<union> c2'"
              by blast
            from c_sets'_def have "
                false_node \<in> c0' \<and>
                true_node \<in> c1' \<and>
                help_node \<in> c2' "
               by simp
             from this l1 l2 l3 c0_def c1_def c2_def E_diff_v_main_def
               E_diff_v_gadget_def c1'withvars_def c0'withvars_def have
              "E_diff_v_main \<union> c1'withvars \<union> c0'withvars \<union> E_diff_v_gadget \<union> c2' = c0 \<union> (c1 \<union> c2)"
               by auto


            from this c_sets_def c_sets'_def E_diff_v_c0'c1'c2'_equ have
                "E_diff_v \<union>  \<Union> c_Sets' = \<Union> c_sets"
              by auto
            from this E_def2 c_sets'_complete show ?thesis
            by (simp add: \<open>\<Union> E_diff = E_diff_v\<close> sup_commute)
          qed


          from c_sets_def c1c2_empty c0c2_empty c0c1_empty have
            c_sets_sound:"(\<forall>c\<in>c_sets. \<forall>c'\<in>c_sets. c \<noteq> c' \<longrightarrow> c \<inter> c' = {})"
            by blast


          have c_sets_three_color:" card c_sets = 3"
          proof -
            from c0c1_empty c0_def c1_def have c0c1notEq:"c0 \<noteq> c1"
              by blast
            from c0c2_empty c0_def c2_def have c0c2notEq:"c0 \<noteq> c2"
              by blast
            from c1c2_empty c1_def c2_def have c1c2notEq:"c1 \<noteq> c2"
              by blast
            from c0c1notEq c0c2notEq c1c2notEq c_sets_def show ?thesis
              by simp
          qed


          have c0iscolor:
              "(\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E)"
          proof -
            from c0_def c0'withvars_def doubleton_eq_iff E_diff_v_gadget_E'_empty2
              E_diff_v_gadget_E'_empty3 E_diff_v_gadget_def neg_var_edge_notin_E'
              neg_var_c0'_edge_notin_E'1 neg_var_c0'_edge_notin_E'2 edge_card1_notin_E' c0'iscolor
            have c0_color_E':
                "(\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E')" by simp
            have step1:"((\<sigma>\<up>) (Pos (var lit1)) = (tolit lit3 = Pos) \<or> var lit1 \<noteq> var lit3) \<and>
                  ((\<sigma>\<up>) (Pos (var lit2)) = (tolit lit3 = Pos) \<or> var lit2 \<noteq> var lit3) \<and>
                  ((\<sigma>\<up>) (Pos (var lit1)) = (tolit lit3 = Pos) \<or> var lit1 \<noteq> var lit3) \<and>
                  ((\<sigma>\<up>) (Pos (var lit2)) = (tolit lit3 = Pos) \<or> var lit2 \<noteq> var lit3)"
              using l3 toliteq by fastforce
            have step2:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var l))) \<and>
                 (\<not> (\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> \<not> (\<sigma>\<up>) (Pos (var l))) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by fastforce
            have step3:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit2)) \<or> var lit2 \<noteq> var l) \<and>
                 (\<not> (\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit2)) \<longrightarrow> var lit2 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by force
            have step4:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> tolit lit3 = Pos \<or> var lit3 \<noteq> var l) \<and>
                 (\<not> (\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> tolit lit3 = Pos \<longrightarrow> var lit3 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step1 by metis
            have step5:"(\<forall>v'\<in>c0'.
                \<forall>l. ((\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                    (\<not> (\<sigma>\<up>) (Pos (var lit1)) \<and> var lit1 = var l \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                    l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) "
              by (metis (full_types) One_nat_def assOfc0Nodes)
            have step6:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit1)) \<or> var lit1 \<noteq> var l) \<and>
                 (\<not> (\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit1)) \<longrightarrow> var lit1 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by metis
            have step7:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var l))) \<and>
                 (\<not> (\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> \<not> (\<sigma>\<up>) (Pos (var l))) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by fastforce
            have step8:"(\<forall>l. ((\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> tolit lit3 = Pos \<or> var lit3 \<noteq> var l) \<and>
                 (\<not> (\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> tolit lit3 = Pos \<longrightarrow> var lit3 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) "
              using step1 by metis
            have step9:"(\<forall>v'\<in>c0'.
                \<forall>l. ((\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                    (\<not> (\<sigma>\<up>) (Pos (var lit2)) \<and> var lit2 = var l \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                    l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by (metis (full_types) One_nat_def assOfc0Nodes)
            have step10:"(\<forall>l. (tolit lit3 = Pos \<and> var lit3 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit1)) \<or> var lit1 \<noteq> var l) \<and>
                 (tolit lit3 \<noteq> Pos \<and> var lit3 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit1)) \<longrightarrow> var lit1 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) "
              using step4 by blast
            have step11:"(\<forall>l. (tolit lit3 = Pos \<and> var lit3 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit2)) \<or> var lit2 \<noteq> var l) \<and>
                 (tolit lit3 \<noteq> Pos \<and> var lit3 = var l \<longrightarrow> (\<sigma>\<up>) (Pos (var lit2)) \<longrightarrow> var lit2 \<noteq> var l) \<or>
                 l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step8 by blast
            have step12:"(\<forall>v\<in>c0'.
                (\<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> (\<sigma>\<up>) (Pos (var lit1)) \<or> var lit1 \<noteq> var l) \<and>
                     (v = (Suc 0, True, var l, 0) \<longrightarrow> (\<sigma>\<up>) (Pos (var lit1)) \<longrightarrow> var lit1 \<noteq> var l) \<or>
                     l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) \<and>
                (\<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> (\<sigma>\<up>) (Pos (var lit2)) \<or> var lit2 \<noteq> var l) \<and>
                     (v = (Suc 0, True, var l, 0) \<longrightarrow> (\<sigma>\<up>) (Pos (var lit2)) \<longrightarrow> var lit2 \<noteq> var l) \<or>
                     l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) \<and>
                (\<forall>v'\<in>c0'.
                    \<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                        (v = (Suc 0, True, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                        l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3))"
              by (smt One_nat_def c0'iscolor_lit3 step5 step9)
            from l1 l2 l3  toliteq toliteq2 trueVarNodesNotinc0' toliteq3  helpCnotinc0'
                trueVarNodesNotinc0'_2 trueVarNodesNotinc0'_3 step1 step2 step3 step4 step5 step6
                step6 step7 step8 step9 step10 step11 step12
            have c0_color_E_diff:
                "(\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E_diff)"
              by (simp add: c0_def c0'withvars_def E_diff_def  doubleton_eq_iff
                    gadget_c0'_empty2 E_diff_v_gadget_def lit_def)
            from  c0_color_E_diff c0_color_E' E_def2 show ?thesis
              by blast
          qed

          have c1iscolor:
              "(\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E)"
          proof -
            from c1_def c1'withvars_def doubleton_eq_iff E_diff_v_gadget_E'_empty2
              E_diff_v_gadget_E'_empty3 E_diff_v_gadget_def pos_var_edge_notin_E'
              pos_var_c1'_edge_notin_E'1 pos_var_c1'_edge_notin_E'2 edge_card1_notin_E'_2 c1'iscolor
            have c1_color_E':
                "(\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E')"
              by simp
            have step1:"((tolit lit2 = Pos) = (tolit lit1 = Pos) \<or> var lit2 \<noteq> var lit1) \<and>
                ((tolit lit3 = Pos) = (tolit lit1 \<noteq> Pos) \<or> var lit3 \<noteq> var lit1)"
              by (metis l1 l2 l3 toliteq toliteqNeg)
            have step2:"
                (\<forall>l. (tolit lit1 = Pos \<and> var lit1 = var l \<longrightarrow> tolit lit2 = Pos \<or> var lit2 \<noteq> var l) \<and>
                (tolit lit1 \<noteq> Pos \<and> var lit1 = var l \<longrightarrow> tolit lit2 = Pos \<longrightarrow> var lit2 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using step1 by auto
            have step3:"   (\<forall>l. (tolit lit1 = Pos \<and> var lit1 = var l \<longrightarrow> tolit lit3 = Pos \<longrightarrow> var lit3 \<noteq> var l) \<and>
                (tolit lit1 \<noteq> Pos \<and> var lit1 = var l \<longrightarrow> tolit lit3 = Pos \<or> var lit3 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) "
              using step1 by auto
            have step4:" (\<forall>v'\<in>c1'.
                \<forall>l. (tolit lit1 = Pos \<and> var lit1 = var l \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                (tolit lit1 \<noteq> Pos \<and> var lit1 = var l \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              by (smt FalseVarNodesNotinc1' One_nat_def l1)
            have step5:"((tolit lit2 = Pos) = (tolit lit1 = Pos) \<or> var lit2 \<noteq> var lit1) "
              by (simp add: step1)
            have step6:"(\<forall>l. (tolit lit2 = Pos \<and> var lit2 = var l \<longrightarrow> tolit lit1 = Pos \<or> var lit1 \<noteq> var l) \<and>
                (tolit lit2 \<noteq> Pos \<and> var lit2 = var l \<longrightarrow> tolit lit1 = Pos \<longrightarrow> var lit1 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) "
              using step2 by auto
            have step7:  " (\<forall>l. (tolit lit2 = Pos \<and> var lit2 = var l \<longrightarrow> tolit lit3 = Pos \<longrightarrow> var lit3 \<noteq> var l) \<and>
                (tolit lit2 \<noteq> Pos \<and> var lit2 = var l \<longrightarrow> tolit lit3 = Pos \<or> var lit3 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3)"
              using l2 l3 toliteq toliteqNeg by fastforce
            have step8:"(\<forall>v'\<in>c1'.
                \<forall>l. (tolit lit2 = Pos \<and> var lit2 = var l \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                (tolit lit2 \<noteq> Pos \<and> var lit2 = var l \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) "
              by (smt FalseVarNodesNotinc1' One_nat_def l2)
            have step9:"((tolit lit3 = Pos) = (tolit lit1 \<noteq> Pos) \<or> var lit3 \<noteq> var lit1) "
              by (simp add: step1)
            have step10:"(\<forall>l. (tolit lit3 \<noteq> Pos \<and> var lit3 = var l \<longrightarrow> tolit lit1 = Pos \<or> var lit1 \<noteq> var l) \<and>
                (tolit lit3 = Pos \<and> var lit3 = var l \<longrightarrow> tolit lit1 = Pos \<longrightarrow> var lit1 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) "
              using step9 by auto
            have step11:"(\<forall>l. (tolit lit3 \<noteq> Pos \<and> var lit3 = var l \<longrightarrow> tolit lit2 = Pos \<or> var lit2 \<noteq> var l) \<and>
                (tolit lit3 = Pos \<and> var lit3 = var l \<longrightarrow> tolit lit2 = Pos \<longrightarrow> var lit2 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) "
              using step7 by blast
            have step12:"(\<forall>v\<in>c1'.
                (\<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> tolit lit1 = Pos \<or> var lit1 \<noteq> var l) \<and>
                (v = (Suc 0, True, var l, 0) \<longrightarrow> tolit lit1 = Pos \<longrightarrow> var lit1 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) \<and>
                (\<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> tolit lit2 = Pos \<or> var lit2 \<noteq> var l) \<and>
                (v = (Suc 0, True, var l, 0) \<longrightarrow> tolit lit2 = Pos \<longrightarrow> var lit2 \<noteq> var l) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3) \<and>
                (\<forall>v'\<in>c1'.
                \<forall>l. (v = (Suc 0, False, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, True, var l, 0)) \<and>
                (v = (Suc 0, True, var l, 0) \<longrightarrow> v' \<noteq> (Suc 0, False, var l, 0)) \<or>
                l \<noteq> lit1 \<and> l \<noteq> lit2 \<and> l \<noteq> lit3))"
              by (smt One_nat_def c1'iscolor_lit3 step4 step8)
            from l1 l2 l3  toliteq toliteqNeg toliteq3_2 helpCnotinc1'
                trueVarNodesNotinc1'_2 trueVarNodesNotinc1'_3 FalseVarNodesNotinc1' falseCnotinc1'
                step1 step2 step3 step4 step5 step6 step7 step8 step9 step10 step11 step12
            have c1_color_E_diff:
                "(\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E_diff)"
              by (simp add: c1_def c1'withvars_def E_diff_def  doubleton_eq_iff
                    gadget_c1'_empty2 E_diff_v_gadget_def lit_def)
            from c1_color_E_diff c1_color_E' E_def2 show ?thesis
              by blast
          qed


          have c2iscolor:
              "(\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E)"
          proof -
            from c2_def doubleton_eq_iff E_diff_v_gadget_E'_empty2
              E_diff_v_gadget_E'_empty3 E_diff_v_gadget_def pos_var_edge_notin_E'
              pos_var_c1'_edge_notin_E'1 pos_var_c1'_edge_notin_E'2 edge_card1_notin_E'_2 c2'iscolor
            have c2_color_E':
                "(\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E')" by simp


            from l1 l2 l3  toliteq toliteqNeg toliteq2 trueVarNodesNotinc0' toliteq3  toliteq3_2 helpCnotinc1'
                trueVarNodesNotinc1'_2 trueVarNodesNotinc1'_3 FalseVarNodesNotinc1' falseCnotinc1' varnotinc2'
                false_varnotinc2' true_varnotinc2'
            have c2_color_E_diff:
                "(\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E_diff)"
              by (simp add: c2_def E_diff_def  doubleton_eq_iff
                    gadget_c2'_empty2 E_diff_v_gadget_def lit_def)
            from c2_color_E_diff c2_color_E' E_def2 show ?thesis
              by blast
          qed

          from c0iscolor c1iscolor c2iscolor have iscolor: "(\<forall>c\<in>c_sets. \<forall>v\<in>c. \<forall>v'\<in>c. {v, v'} \<notin> E)"
            using c_sets_def by blast

          from E_ugraph c_sets_complete c_sets_sound iscolor c_sets_three_color have E_three_colorable:
            "is_k_colorable E 3 c_sets" unfolding is_k_colorable_def is_colorable_def
          by blast

          from E_three_colorable c_sets_def mainInCsets varInc1 varInc0 finalNodeInc1 show ?thesis
            by blast
        next
          case l3:False
          from l1 l2 l3 F'_def lit_def have "\<not>\<sigma> \<Turnstile> F"
            by (intro notI; elim modelsE)
            (metis Un_insert_right empty_iff insert_iff list.simps models_clause_def set_append)
          from this Suc(5) have "False"
            by simp
          then show ?thesis
            by force
        qed
      qed
    qed
  then show ?case
    by simp
qed


(*three colorability implies clause has three literals *)

lemma sat_tc_card3:"sat_tc F \<in> three_colorability \<Longrightarrow> \<forall>cls\<in>set F. card cls = 3"
  proof (cases " (\<forall>cls \<in> set F. card cls = 3)")
    case True
    then show ?thesis
      by blast
  next
    case False
    assume asms: "sat_tc F \<in> three_colorability"
    from False have "sat_tc F = {{(0,False,0,0)}}" unfolding sat_tc_def
      by presburger
    from this have "\<not> ugraph (sat_tc F)" unfolding ugraph_def
      by simp
    from this asms have "False" unfolding three_colorability_def is_k_colorable_def is_colorable_def
      by blast
    then show ?thesis
      by simp
  qed






(*three colorability implies satisfying assignment*)

lemma sat_tc_models:"sat_tc F \<in> three_colorability \<Longrightarrow> \<exists>\<sigma>. \<sigma> \<Turnstile> F"
proof (cases F)
  case Nil
  then show ?thesis by fastforce
next
  case (Cons a list)
  assume asms:"sat_tc F \<in> three_colorability"
  from this have F_cls_card_3:"\<forall>cls\<in>set F. card cls = 3"
    using sat_tc_card3
    by presburger
  define E where E_sat_tc_def:"E = sat_tc F"
  from this asms have E_colorable:"E : three_colorability"
    by simp
  define E_gadget where E_gadget_def:"E_gadget =
      {{(2::nat,False,i,0::nat),( 2,False,i,1)} | i. i < length F} \<union>
      {{(2,False,i,0),( 2,False,i,3)} | i. i < length F} \<union>
      {{(2,False,i,1),( 2,False,i,3)} | i. i < length F} \<union>
      {{(2,False,i,3),( 2,False,i,4)} | i. i < length F} \<union>
      {{(2,False,i,2),( 2,False,i,4)} | i. i < length F} \<union>
      {{(2,False,i,2),( 2,False,i,5)} | i. i < length F} \<union>
      {{(2,False,i,4),( 2,False,i,5)} | i. i < length F} \<union>
      {{(2,False,i,5),false_node} |  i. i < length F}\<union>
      {{(2,False,i,5),help_node} |  i. i < length F}"
  define E_var_to_gadget where E_var_to_gadget_def:"E_var_to_gadget =
        \<Union>{{{(1::nat,tolit l1 = Pos,var l1,0::nat),(2,False,i,0)},
          {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)},
          {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}}|
          l1 l2 l3 i . i < length F \<and> {l1,l2,l3} = F ! i \<and> sorted_list_of_set (F!i) = [l1,l2,l3]}"
  define E_var where E_var_def:"E_var =
      {{help_node,(1, True,  var l,0)}| l. (l\<in>(\<Union> (set F)))} \<union>
      {{help_node,(1, False,  var l,0)}| l. (l\<in>(\<Union> (set F)))} \<union>
      {{(1, False, var l,0),(1, True , var l,0)}|l . l\<in>(\<Union> (set F))}"
  define E_main where E_main_def:"E_main = { {false_node, true_node},
        {true_node, help_node},
        {false_node, help_node}}"

  from E_sat_tc_def F_cls_card_3 have E_def: "E =
      { {false_node, true_node},
        {true_node, help_node},
        {false_node, help_node}} \<union>
      {{help_node,(1, True,  var l,0)}| l. (l\<in>(\<Union> (set F)))} \<union>
      {{help_node,(1, False,  var l,0)}| l. (l\<in>(\<Union> (set F)))} \<union>
      {{(1, False, var l,0),(1, True , var l,0)}|l . l\<in>(\<Union> (set F))} \<union>
      \<Union>{{{(1,tolit l1 = Pos,var l1,0),(2,False,i,0)},
          {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)},
          {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}}|
          l1 l2 l3 i . i < length F \<and> {l1,l2,l3} = F ! i \<and> sorted_list_of_set (F!i) = [l1,l2,l3]} \<union>
      {{(2,False,i,0),( 2,False,i,1)} | i. i < length F} \<union>
      {{(2,False,i,0),( 2,False,i,3)} | i. i < length F} \<union>
      {{(2,False,i,1),( 2,False,i,3)} | i. i < length F} \<union>
      {{(2,False,i,3),( 2,False,i,4)} | i. i < length F} \<union>
      {{(2,False,i,2),( 2,False,i,4)} | i. i < length F} \<union>
      {{(2,False,i,2),( 2,False,i,5)} | i. i < length F} \<union>
      {{(2,False,i,4),( 2,False,i,5)} | i. i < length F} \<union>
      {{(2,False,i,5),false_node} |  i. i < length F}\<union>
      {{(2,False,i,5),help_node} |  i. i < length F}"
    unfolding sat_tc_def
    by argo

  have E_def2:"E = E_main \<union> E_var \<union> E_var_to_gadget \<union> E_gadget"
    by (auto simp:E_def E_main_def E_var_def E_var_to_gadget_def E_gadget_def)

  from E_def E_colorable
  have "\<exists> csets c0 c1 c2. is_k_colorable E 3 csets \<and>
                  csets = {c0,c1,c2} \<and>
                  false_node \<in> c0 \<and>
                  true_node \<in> c1 \<and>
                  help_node \<in> c2 \<and>
                  {(2, False, i, 5) |i. i < length F} \<subseteq> c1"
  proof -
    from E_colorable obtain csets' where csets'_def:"
                           is_k_colorable E 3 csets'"
      unfolding  three_colorability_def is_colorable_def
      by blast
    from this have csets'_card:"card csets' = 3" unfolding is_k_colorable_def
      by blast

    from csets'_def have csets'_complete:"\<Union>E = \<Union> csets'" unfolding  is_k_colorable_def is_colorable_def
      by simp
    from this E_def have F_in_csets':"false_node \<in> \<Union> csets'"
      by blast
    from csets'_complete E_def have T_in_csets':"true_node \<in> \<Union> csets'"
      by blast
    from csets'_complete E_def have H_in_csets':"help_node \<in> \<Union> csets'"
      by blast
    from csets'_card F_in_csets' obtain c0' where c0'_def:" c0' \<in> csets' \<and>
                                                false_node \<in> c0'"
      by blast
    from T_in_csets' obtain c1' where c1'_def: " c1' \<in> csets' \<and>
                                                true_node \<in> c1'"
      by blast
    from H_in_csets' obtain c2' where c2'_def: " c2' \<in> csets' \<and>
                                                help_node \<in> c2'"
      by blast
    from E_def have main_in_E:"{ {false_node, true_node},
        {true_node, help_node},
        {false_node, help_node}} \<subseteq> E"
      by blast
    from c0'_def main_in_E csets'_def have T_not_in_c0':"true_node \<notin> c0'"
      unfolding is_k_colorable_def is_colorable_def
      by force
    from c0'_def main_in_E csets'_def have H_not_in_c0':"help_node \<notin> c0'"
      unfolding is_k_colorable_def is_colorable_def
      by force
    from c2'_def main_in_E csets'_def have T_not_in_c2':"true_node \<notin> c2'"
      unfolding is_k_colorable_def is_colorable_def
      by force
    from T_not_in_c0' c1'_def have c0'c1'noteq:"c1' \<noteq> c0'"
      by fast
    from H_not_in_c0' c2'_def have c0'c2'noteq:"c2' \<noteq> c0'"
      by blast
    from T_not_in_c2' c1'_def have c1'c2'noteq:"c2' \<noteq> c1'"
      by blast

    from csets'_card have fin1:"finite csets'"
      using card.infinite by fastforce
    have fin2:"finite {c0', c1', c2'}"
      by blast
    from csets'_card c0'c1'noteq c0'c2'noteq c1'c2'noteq have card2:
      "card {c0', c1', c2'} = card csets'"
      by simp
    from c0'_def c1'_def c2'_def have "{c0', c1', c2'} \<subseteq> csets'"
      by blast
    from fin1 fin2 card2 this have csets'_def2:"csets' = {c0', c1', c2'}"
      using card_subset_eq
      by metis

    from csets'_complete E_def have gadgetNode_in_csets':"{(2, False, i, 5) |i. i < length F} \<subseteq> \<Union> csets'"
      by blast
    from E_def have F_to_gadget_in_E:"{{(2,False,i,5),false_node} |  i. i < length F} \<subseteq> E"
      by fast
    from csets'_def c0'_def have "\<forall>v\<in>c0'. \<forall>v'\<in>c0'. {v, v'} \<notin> E"
      unfolding is_k_colorable_def is_colorable_def
      by meson
    from this c0'_def F_to_gadget_in_E have c0'inter_empty:"{(2, False, i, 5) |i. i < length F} \<inter> c0' = {}"
      by blast
    from E_def have H_to_gadget_in_E:"{{(2,False,i,5),help_node} |  i. i < length F} \<subseteq> E"
      by fast
    from csets'_def c2'_def have "\<forall>v\<in>c2'. \<forall>v'\<in>c2'. {v, v'} \<notin> E"
      unfolding is_k_colorable_def is_colorable_def
      by meson
    from this c2'_def H_to_gadget_in_E have c2'inter_empty:"{(2, False, i, 5) |i. i < length F} \<inter> c2' = {}"
      by blast
    from c0'inter_empty c2'inter_empty gadgetNode_in_csets' csets'_def2 have
      "{(2, False, i, 5) |i. i < length F} \<subseteq> c1'"
      by auto
    from this csets'_def2 c0'_def c1'_def c2'_def show ?thesis
      using csets'_def by auto
  qed
  from this obtain csets c0 c1 c2 where csets_def:"is_k_colorable E 3 csets \<and>
                  csets = {c0,c1,c2} \<and>
                  false_node \<in> c0 \<and>
                  true_node \<in> c1 \<and>
                  help_node \<in> c2 \<and>
                  {(2, False, i, 5) |i. i < length F} \<subseteq> c1"
    by auto
  from csets_def have csets_def2:"csets = {c0,c1,c2}"
    by simp
  from csets_def have  F_in_c0:"false_node \<in> c0"
    by blast
  from csets_def have  T_in_c1:"true_node \<in> c1"
    by blast
  from csets_def have  H_in_c2:"help_node \<in> c2"
    by blast
  from csets_def have csets_is_color:"(\<forall>c\<in>csets. \<forall>v\<in>c. \<forall>v'\<in>c. {v, v'} \<notin> E)"
    unfolding is_k_colorable_def is_colorable_def
    by argo
  from csets_is_color csets_def2 have c0_iscolor: "\<forall>v\<in>c0. \<forall>v'\<in>c0. {v, v'} \<notin> E" by simp
  from csets_is_color csets_def2 have c1_iscolor: "\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E" by simp
  from csets_is_color csets_def2 have c2_iscolor: "\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E" by simp

  from csets_def have csets_complete:"\<Union> E = \<Union>csets" unfolding is_k_colorable_def is_colorable_def
    by fast
  from E_def have "{{(1, False, var l,0),(1, True , var l,0)}|l . l\<in>(\<Union> (set F))} \<subseteq> E"
    by fast
  from this have "{(1, b, var l,0)|b l . l\<in>(\<Union> (set F)) \<and> (b= True\<or> b= False)} \<subseteq> \<Union> E"
    by blast
  from this csets_complete have "{(1, b, var l,0)|b l . l\<in>(\<Union> (set F)) \<and> (b= True\<or> b= False)} \<subseteq> \<Union>csets"
    by simp
  from this have var_in_csets:"\<forall>v \<in> {(1, b, var l,0)|b l . l\<in>(\<Union> (set F)) \<and> (b= True\<or> b= False)}. v\<in>  \<Union>csets"
    by blast
  from E_def have "{{help_node, (1, True, var l, 0)} |l. l \<in> \<Union> (set F)} \<subseteq> E"
    by fast
  from this have var_to_help_v:"\<forall>v \<in> {(1, True, var l,0)|l . l\<in>(\<Union> (set F))}. {help_node,v} \<in> E"
    by blast
  from E_def have "{{help_node, (1, False, var l, 0)} |l. l \<in> \<Union> (set F)} \<subseteq> E"
    by fast
  from this have "\<forall>v \<in> {(1, False, var l,0)|l . l\<in>(\<Union> (set F))}. {help_node,v} \<in> E"
    by blast
  from this var_to_help_v have "\<forall>v \<in> {(1, b, var l,0)|b l . l\<in>(\<Union> (set F)) \<and> (b= True\<or> b= False)}.
                  {help_node,v} \<in> E"
    by blast
  from this H_in_c2 csets_is_color csets_def2 have "
    \<forall>v \<in> {(1, b, var l,0)|b l . l\<in>(\<Union> (set F)) \<and> (b= True\<or> b= False)}. v \<notin>  c2"
    by (meson singletonI subset_eq subset_insertI)
  from this var_in_csets csets_def2 have
    "\<forall>v \<in> {(1, b, var l,0)|b l . l\<in>(\<Union> (set F)) \<and> (b= True\<or> b= False)}. v\<in> c0 \<union> c1"
    by blast
  from this have var_in_c0c1:"\<forall>l\<in>(\<Union> (set F)). (1, tolit l = Pos, var l,0) \<in> c1 \<or>  (1, tolit l = Pos, var l,0) \<in> c0"
    by blast

  fix \<sigma> :: "nat \<Rightarrow> bool"
  define \<sigma> where \<sigma>_def:"\<sigma>  = (\<lambda>n. ((1,True, n,0) \<in> c1))"

  from this have in_to_sigma:"\<And>l. l\<in>\<Union>(set F) \<Longrightarrow> ((1, tolit l = Pos, var l,0) \<in> c1) \<Longrightarrow>(\<sigma>\<up>) l"
  proof-
    fix l
    assume asms:"(1, tolit l = Pos, var l,0) \<in> c1" "l\<in>\<Union>(set F)"
    from this show "(\<sigma>\<up>) l"
    proof (cases "tolit l = Pos")
      case True
      from asms this have "(1, True, var l,0) \<in> c1"
        by simp
      from this True \<sigma>_def show ?thesis
        by (metis lit.simps(5) tolit.simps(2) var.elims models_lit_def)
    next
      case False
      from this have "tolit l = Neg"
        by (meson tolit.elims)
      from this have l_is_neg:"\<exists>x. l = Neg x"
        by (metis tolit.elims)
      from E_def have var_edges_in_E:"{{(1, False, var l,0),(1, True , var l,0)}|l . l\<in>(\<Union> (set F))} \<subseteq> E"
        by fast
      from asms(2) E_def have "{(1, False, var l,0),(1, True, var l,0)} \<in>
          {{(1, False, var l,0),(1, True , var l,0)}|l . l\<in>(\<Union> (set F))}"
        by blast
      from this var_edges_in_E have l_F_T_edge_in_E:"{(1, False, var l,0),(1, True, var l,0)} \<in> E"
        by blast
      from asms False have "(1, False, var l,0) \<in> c1"
        by simp
      from this l_F_T_edge_in_E c1_iscolor asms(2) have "(1, True, var l,0) \<notin> c1"
        by blast
      from this asms \<sigma>_def l_is_neg show ?thesis by auto
    qed
  qed

  have "\<And>cls i. cls = (F! i) \<Longrightarrow> i < length F \<Longrightarrow> \<exists>l\<in>cls. (\<sigma>\<up>) l"
  proof -
    fix cls i
    assume asms:"cls = F ! i" "i < length F"
    from this show "\<exists>l\<in>cls. (\<sigma>\<up>) l"
    proof -
      from asms have cls_in_F:"cls\<in> set F"
        by simp
      from this F_cls_card_3 have cls_card:"card cls = 3"
        by blast
      from this obtain lit1 lit2 lit3 where lit_def:"cls = {lit1, lit2, lit3} \<and> sorted[lit1,lit2,lit3]" using choice3
        by (meson choiceClause)
      from lit_def have lit_def2:"cls = {lit1, lit2, lit3}"
        by simp
      from lit_def asms(1) cls_card have lit_def3:"sorted_list_of_set (F ! i) = [lit1, lit2, lit3]"
        using sorted_strictsorted_lits4
        by metis
      from lit_def cls_in_F have lits_in_F:"{lit1, lit2, lit3} \<subseteq> \<Union> (set F)"
        by blast

      from asms(2) E_gadget_def have cls_gadget_in_E_gadget:"{
        {(2::nat,False,i,0::nat),(2,False,i,1)},
        {(2, False, i, 0), (2, False, i, 3)},
        {(2, False, i, 1), (2, False, i, 3)},
        {(2, False, i, 3), (2, False, i, 4)},
        {(2, False, i, 2), (2, False, i, 4)},
        {(2, False, i, 2), (2, False, i, 5)},
        {(2, False, i, 4), (2, False, i, 5)}}
        \<subseteq> E_gadget"
        by auto
      from asms lit_def2 lit_def3 have
        "{{(1, tolit lit1 = Pos, var lit1,0),(2, False, i, 0)},
          {(1, tolit lit2 = Pos, var lit2,0),(2, False, i, 1)},
          {(1, tolit lit3 = Pos, var lit3,0),(2, False, i, 2)}}
         \<subseteq> E_var_to_gadget"
        by (auto simp: E_var_to_gadget_def) blast+

      from this cls_gadget_in_E_gadget have cls_edges_in_E:"{
        {(1::nat, tolit lit1 = Pos, var lit1,0::nat),(2, False, i, 0)},
        {(1, tolit lit2 = Pos, var lit2,0),(2, False, i, 1)},
        {(1, tolit lit3 = Pos, var lit3,0),(2, False, i, 2)},
        {(2 ,False, i, 0), (2, False, i, 1)},
        {(2, False, i, 0), (2, False, i, 3)},
        {(2, False, i, 1), (2, False, i, 3)},
        {(2, False, i, 3), (2, False, i, 4)},
        {(2, False, i, 2), (2, False, i, 4)},
        {(2, False, i, 2), (2, False, i, 5)},
        {(2, False, i, 4), (2, False, i, 5)}}\<subseteq> E"
        by (simp add: E_def2)

      from this csets_complete have cls_nodes_in_csets:"
        {(1::nat, tolit lit1 = Pos, var lit1,0::nat),
        (1, tolit lit2 = Pos, var lit2,0),
        (1, tolit lit3 = Pos, var lit3,0),
        (2, False, i, 0),
        (2, False, i, 1),
        (2, False, i, 2),
        (2, False, i, 3),
        (2, False, i, 4),
        (2, False, i, 5)}\<subseteq> \<Union>csets"
        by auto

      have "((1, tolit lit1 = Pos, var lit1,0) \<in> c1) \<or>
            ((1, tolit lit2 = Pos, var lit2,0) \<in> c1) \<or>
            ((1, tolit lit3 = Pos, var lit3,0) \<in> c1)"
      proof (cases "((1, tolit lit1 = Pos, var lit1,0) \<in> c1)")
        case True
        then show ?thesis by simp
      next
        case F1:False
        then show ?thesis
        proof (cases "((1, tolit lit2 = Pos, var lit2,0) \<in> c1)")
          case True
          then show ?thesis by simp
        next
          case F2:False
          then show ?thesis
          proof (cases "((1, tolit lit3 = Pos, var lit3,0) \<in> c1)")
            case True
            then show ?thesis by simp
          next
            case F3:False
            from F1 var_in_c0c1 lits_in_F have lit1_in_c0:"(1, tolit lit1 = Pos, var lit1, 0) \<in> c0"
              by fast
            from F2 var_in_c0c1 lits_in_F have lit2_in_c0:"(1, tolit lit2 = Pos, var lit2, 0) \<in> c0"
              by fast
            from F3 var_in_c0c1 lits_in_F have lit3_in_c0:"(1, tolit lit3 = Pos, var lit3, 0) \<in> c0"
              by fast
            from this cls_edges_in_E c0_iscolor have g2_notin_c0:"(2, False, i, 2) \<notin> c0"
              by force
            from csets_def asms(2) have g5_in_c1:"(2, False, i, 5) \<in> c1"
              by blast
            from this cls_edges_in_E c1_iscolor have g2_notin_c1:"(2, False, i, 2) \<notin> c1"
              by force
            from g2_notin_c1 g2_notin_c0 cls_nodes_in_csets csets_def2 have g2_in_c2:"(2, False, i, 2) \<in> c2"
              by blast
            from this cls_edges_in_E c2_iscolor have g4_notin_c2:"(2, False, i, 4) \<notin> c2"
              by force
            from g5_in_c1 cls_edges_in_E c1_iscolor have g4_notin_c1:"(2, False, i, 4) \<notin> c1"
              by force
            from g4_notin_c2 g4_notin_c1 cls_nodes_in_csets csets_def2 have g4_in_c0:"(2, False, i, 4) \<in> c0"
              by blast


            from g4_in_c0 cls_edges_in_E c0_iscolor have g3_notin_c0:"(2, False, i, 3) \<notin> c0"
              by force

            show ?thesis
            proof (cases "(2, False, i, 3) \<in> c1")
              case g3_in_c1:True
              from g3_in_c1 cls_edges_in_E c1_iscolor have g0_notin_c1:"(2, False, i, 0) \<notin> c1"
                by force
              from lit1_in_c0 cls_edges_in_E c0_iscolor have g0_notin_c0:"(2, False, i, 0) \<notin> c0"
                by force
              from g0_notin_c0 g0_notin_c1 cls_nodes_in_csets csets_def2 have g0_in_c2:"(2, False, i, 0) \<in> c2"
                by blast


              from g0_in_c2 cls_edges_in_E c2_iscolor have g1_notin_c2:"(2, False, i, 1) \<notin> c2"
                by force
              from lit2_in_c0 cls_edges_in_E c0_iscolor have g1_notin_c0:"(2, False, i, 1) \<notin> c0"
                by force
              from g3_in_c1 cls_edges_in_E c1_iscolor have g1_notin_c1:"(2, False, i, 1) \<notin> c1"
                by force
              from g1_notin_c0 g1_notin_c1 g1_notin_c2 cls_nodes_in_csets csets_def2 have "False"
                by blast
              then show ?thesis by simp
            next
              case g3_notin_c1:False

              from g3_notin_c1 g3_notin_c0 cls_nodes_in_csets csets_def2 have g3_in_c2:"(2, False, i, 3) \<in> c2"
                by blast


              from g3_in_c2 cls_edges_in_E c2_iscolor have g0_notin_c2:"(2, False, i, 0) \<notin> c2"
                by force
              from lit1_in_c0 cls_edges_in_E c0_iscolor have g0_notin_c0:"(2, False, i, 0) \<notin> c0"
                by force
              from g0_notin_c0 g0_notin_c2 cls_nodes_in_csets csets_def2 have g0_in_c1:"(2, False, i, 0) \<in> c1"
                by blast


              from g0_in_c1 cls_edges_in_E c1_iscolor have g1_notin_c1:"(2, False, i, 1) \<notin> c1"
                by force
              from lit2_in_c0 cls_edges_in_E c0_iscolor have g1_notin_c0:"(2, False, i, 1) \<notin> c0"
                by force
              from g3_in_c2 cls_edges_in_E c2_iscolor have g1_notin_c2:"(2, False, i, 1) \<notin> c2"
                by force
              from g1_notin_c0 g1_notin_c1 g1_notin_c2 cls_nodes_in_csets csets_def2 have "False"
                by blast
              then show ?thesis by simp
            qed
          qed
        qed
      qed
      from this \<sigma>_def in_to_sigma lits_in_F have "(\<sigma>\<up>) lit1 \<or> (\<sigma>\<up>) lit2 \<or> (\<sigma>\<up>) lit3" by auto
      from this lit_def show ?thesis by blast
    qed
  qed
  from this have "\<And>cls. cls \<in> set F \<Longrightarrow>  \<exists>l\<in>cls. (\<sigma>\<up>) l"
    by (metis in_set_conv_nth)
  from this have "\<sigma> \<Turnstile> F" by fastforce
  then show ?thesis by fast
qed

(*reduction three cnf sat to three colorability*)

theorem is_reduction_sat_tc:
  "is_reduction sat_tc three_cnf_sat three_colorability"
  unfolding is_reduction_def
proof safe
  fix F :: "nat lit set list"
  assume 1:"F \<in> three_cnf_sat"
  then obtain \<sigma> where ass:"\<sigma> \<Turnstile> F" by auto
  from \<open>F \<in> _\<close> have fin_1: "finite (\<Union> (set F))" by (force intro: card_ge_0_finite)
  obtain E where E_def:"sat_tc F = E"
    by simp
  from this 1 have graph:"ugraph E" using sat_tc_ugraph
    by blast
  from E_def 1 ass have "E\<in> three_colorability"  using cnfTo3Color[where F = F]
    unfolding three_colorability_def by fastforce
  from this E_def show "sat_tc F \<in> three_colorability" by auto
next
  fix F :: "nat lit set list"
  obtain E where E_def:"sat_tc F = E"
    by simp
  assume E_3c:"sat_tc F \<in> three_colorability"

  from this have F_3_card:"\<forall>cls\<in>set F. card cls = 3"
    using sat_tc_card3
    by blast

  from E_3c have "\<exists>\<sigma>. \<sigma> \<Turnstile> F "
    using sat_tc_models
    by simp

  from this F_3_card show "F \<in> three_cnf_sat" by auto
qed

end