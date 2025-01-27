theory THREE_SAT_To_THREE_COL_Poly
  imports
    Polynomial_Reductions
    THREE_SAT_To_THREE_COL
begin

definition "size_3C = (\<lambda>(E). card E)"
definition "max_amount_clauses xs = card (\<Union> (set xs))"
definition "mop_set_insert S s = REST [insert s S \<mapsto> 1]"
definition "mop_set_card S  = REST [card S \<mapsto> 1]"
definition "mop_set_empty_set = REST [ {} \<mapsto> 1]"

definition "mop_list_length xs = SPECT [ length xs \<mapsto> 1 ]"

definition "add_main_part F S =
  SPECT [ S \<union> { {(0::nat,False,0::nat,0::nat), (0,False,0,1)},
                {(0,False,0,1), (0,False,0,2)},
                {(0,False,0,0), (0,False,0,2)}} \<mapsto> 3]"

definition "add_posLitToH_part F S =
  SPECT [ S \<union> {{(0,False,0,2),(1, True,  var l,0)}| l. (l\<in>(\<Union> (set F)))} \<mapsto> 3 * length F]"

definition "add_negLitToH_part F S =
  SPECT [ S \<union> {{(0,False,0,2),(1, False,  var l,0)}| l. (l\<in>(\<Union> (set F)))} \<mapsto> 3 * length F]"

definition "add_posToNeg_part F S =
  SPECT [ S \<union> {{(1, False, var l,0),(1, True , var l,0)}|l . l\<in>(\<Union> (set F))} \<mapsto> 3 * length F]"

definition "add_litToGadget_part F S =
  SPECT [ S \<union> \<Union>{{{(1,tolit l1 = Pos,var l1,0),(2,False,i,0)},
      {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)},
      {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}}|
      l1 l2 l3 i . i < length F \<and> {l1,l2,l3} = F ! i \<and> sorted_list_of_set (F!i) = [l1,l2,l3]} \<mapsto> 3 * length F]"

definition "add_gadget_part1 F S =
  SPECT [ S \<union> {{(2,False,i,0),( 2,False,i,1)} | i. i < length F} \<mapsto> length F]"

definition "add_gadget_part2 F S =
  SPECT [ S \<union> {{(2,False,i,0),( 2,False,i,3)} | i. i < length F}  \<mapsto> length F]"

definition "add_gadget_part3 F S =
  SPECT [ S \<union> {{(2,False,i,1),( 2,False,i,3)} | i. i < length F} \<mapsto> length F]"

definition "add_gadget_part4 F S =
  SPECT [ S \<union> {{(2,False,i,3),( 2,False,i,4)} | i. i < length F} \<mapsto> length F]"

definition "add_gadget_part5 F S =
  SPECT [ S \<union> {{(2,False,i,2),( 2,False,i,4)} | i. i < length F} \<mapsto> length F]"

definition "add_gadget_part6 F S =
  SPECT [ S \<union> {{(2,False,i,2),( 2,False,i,5)} | i. i < length F} \<mapsto> length F]"

definition "add_gadget_part7 F S =
  SPECT [ S \<union> {{(2,False,i,4),( 2,False,i,5)} | i. i < length F} \<mapsto> length F]"

definition "add_gadgetToF_part F S =
  SPECT [ S \<union> {{(2,False,i,5),(0,False,0,0)} |  i. i < length F} \<mapsto> length F]"

definition "add_gadgetToH_part F S =
  SPECT [ S \<union> {{(2,False,i,5),(0,False,0,2)} |  i. i < length F} \<mapsto> length F]"





definition sat_to_three_col ::
  "nat lit set list \<Rightarrow> (nat \<times> bool \<times> nat \<times> nat) set set nrest" where
  "sat_to_three_col = (\<lambda>F. do {
      b \<leftarrow> SPECT [ (\<forall>cls \<in> set F. card cls = 3) \<mapsto> 1];
      if b then
        do {
          S \<leftarrow> mop_set_empty_set;
          S \<leftarrow> add_main_part F S;
          S \<leftarrow> add_posLitToH_part F S;
          S \<leftarrow> add_negLitToH_part F S;
          S \<leftarrow> add_posToNeg_part F S;
          S \<leftarrow> add_litToGadget_part F S;
          S \<leftarrow> add_gadget_part1 F S;
          S \<leftarrow> add_gadget_part2 F S;
          S \<leftarrow> add_gadget_part3 F S;
          S \<leftarrow> add_gadget_part4 F S;
          S \<leftarrow> add_gadget_part5 F S;
          S \<leftarrow> add_gadget_part6 F S;
          S \<leftarrow> add_gadget_part7 F S;
          S \<leftarrow> add_gadgetToF_part F S;
          S \<leftarrow> add_gadgetToH_part F S;
          RETURNT (S)
        }
      else RETURNT ({{(0,False,0,0)}})
    })"


definition "size_SAT xs = length xs"
definition "sat_to_three_col_time n =  1 + 1 + 3 +
                                  3 * n + 3 * n + 3 * n + 3 * n +
                                  n + n + n + n + n + n + n + n + n"
definition "sat_to_three_col_space n = 3 + 3 * n + 3 * n + 3 * n + 3 * n +
                                  n + n + n + n + n + n + n + n + n"






lemma sat_to_three_col_refines:
  "sat_to_three_col F \<le> SPEC (\<lambda>y. y = sat_three_col F) (\<lambda>_. enat (sat_to_three_col_time (size_SAT F)))"
  unfolding SPEC_def
  unfolding sat_to_three_col_def sat_three_col_def
      mop_list_length_def mop_set_empty_set_def add_main_part_def add_posLitToH_part_def
      add_negLitToH_part_def add_posToNeg_part_def add_litToGadget_part_def
      add_gadget_part1_def add_gadget_part2_def add_gadget_part3_def add_gadget_part4_def
      add_gadget_part5_def add_gadget_part6_def add_gadget_part7_def
      add_gadgetToF_part_def add_gadgetToH_part_def
  apply(rule T_specifies_I)
  apply(vcg' \<open>-\<close> rules: T_SPEC )
  apply(auto simp: sat_to_three_col_time_def size_SAT_def one_enat_def)
  by (simp add: add.assoc eval_nat_numeral(3) numeral_Bit0 numeral_eq_enat)



lemma three_elements_card:"S={x,y,z} \<Longrightarrow> card S \<le> 3"
proof (cases "x=y")
  assume asms: "S={x,y,z}"
  case t1:True
  then show ?thesis
  proof (cases "y= z")
    case t2:True
    from t1 t2 asms show ?thesis
      by simp
  next
    case False
    from t1 this asms show ?thesis
      by simp
  qed
next
  assume asms: "S={x,y,z}"
  case f1: False
  then show ?thesis
  proof (cases "y= z")
    case t2:True
    from f1 t2 asms show ?thesis by simp
  next
    case f2:False
    from this f1 asms  show ?thesis
    proof (cases "x= z")
      case True
      from this f1 f2 asms show ?thesis
        by (simp add: insert_commute)
    next
      case False
      from this f1 f2 asms show ?thesis
        by simp
    qed
  qed
qed

lemma card_E_var:"\<forall>cls\<in>set F. card cls = 3 \<Longrightarrow> card {{(a,b,c,d),(e,f,var l,g)}| l. (l\<in>(\<Union> (set F)))} \<le> 3 * length F"
proof (induction F)
  case Nil
  then show ?case by simp
next
  case (Cons x F)
  from this have x_card:"card x = 3"
    by simp
  from this obtain l1 l2 l3 where lit_def:"l1\<in> x \<and> l2\<in> x \<and> l3\<in> x \<and> l1 \<noteq> l2 \<and> l1 \<noteq> l3 \<and> l2 \<noteq> l3"
    using choice3
    by (smt card_dif_elements insertI1 insert_absorb2 insert_commute)
  from Cons(2) have "\<forall>cls\<in>set F. card cls = 3"
    by simp
  from lit_def x_card have x_def: "x= {l1,l2,l3}"
    using choice3 by auto
  define part1 where part1_def:"part1 = {{(a, b, c, d), (e, f, var l, g)} |l. l \<in> \<Union> (set (F))}"
  define part2 where part2_def:"part2 = {{(a, b, c, d), (e, f, var l, g)} |l. l \<in> x}"

  have "part2 = { {(a, b, c, d), (e, f, var l1, g)},
                  {(a, b, c, d), (e, f, var l2, g)},
                  {(a, b, c, d), (e, f, var l3, g)}}"
    by (auto simp: x_def part2_def)
  from this have card_part2:"card part2 \<le> 3"
    by (simp add: three_elements_card)
  from part1_def part2_def have "{{(a, b, c, d), (e, f, var l, g)} |l. l \<in> \<Union> (set (x # F))} =
        part1 \<union> part2"
    by auto
  from this have "card {{(a, b, c, d), (e, f, var l, g)} |l. l \<in> \<Union> (set (x # F))} \<le> card part1 + card part2"
    using card_Un_le
    by force
  from this Cons part1_def card_part2 have
    "card {{(a, b, c, d), (e, f, var l, g)} |l. l \<in> \<Union> (set (x # F))} \<le> 3*length F + 3"
    by simp
  then show ?case by simp
qed

lemma card_E_var2:"\<forall>cls\<in>set F. card cls = 3 \<Longrightarrow> card {{(a,b,var l,d),(e,f,var l,g)}| l. (l\<in>(\<Union> (set F)))} \<le> 3 * length F"
proof (induction F)
  case Nil
  then show ?case by simp
next
  case (Cons x F)
  from this have x_card:"card x = 3"
    by simp
  from this obtain l1 l2 l3 where lit_def:"l1\<in> x \<and> l2\<in> x \<and> l3\<in> x \<and> l1 \<noteq> l2 \<and> l1 \<noteq> l3 \<and> l2 \<noteq> l3"
    using choice3
    by (smt card_dif_elements insertI1 insert_absorb2 insert_commute)
  from Cons(2) have "\<forall>cls\<in>set F. card cls = 3"
    by simp
  from lit_def x_card have x_def: "x= {l1,l2,l3}"
    using choice3 by auto
  define part1 where part1_def:"part1 = {{(a, b, var l, d), (e, f, var l, g)} |l. l \<in> \<Union> (set (F))}"
  define part2 where part2_def:"part2 = {{(a, b, var l, d), (e, f, var l, g)} |l. l \<in> x}"

  have "part2 = { {(a, b, var l1, d), (e, f, var l1, g)},
                  {(a, b, var l2, d), (e, f, var l2, g)},
                  {(a, b, var l3, d), (e, f, var l3, g)}}"
    by (auto simp: x_def part2_def)
  from this have card_part2:"card part2 \<le> 3"
    by (simp add: three_elements_card)
  from part1_def part2_def have "{{(a, b, var l, d), (e, f, var l, g)} |l. l \<in> \<Union> (set (x # F))} =
        part1 \<union> part2"
    by auto
  from this have "card {{(a, b, var l, d), (e, f, var l, g)} |l. l \<in> \<Union> (set (x # F))} \<le> card part1 + card part2"
    using card_Un_le
    by force
  from this Cons part1_def card_part2 have
    "card {{(a, b, var l, d), (e, f, var l, g)} |l. l \<in> \<Union> (set (x # F))} \<le> 3*length F + 3"
    by simp
  then show ?case by simp
qed


lemma card_varToGadget:"\<forall>cls\<in>set F. card cls = 3 \<Longrightarrow>card (\<Union>{{{(1::nat,tolit l1 = Pos,var l1,0::nat),(2,False,i,0)},
      {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)},
      {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}}|
      l1 l2 l3 i . i < length F \<and> {l1,l2,l3} = F ! i \<and> sorted_list_of_set (F!i) = [l1,l2,l3]}) \<le> 3 * length F"
proof (induction F rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc c F)
  from this have F_cls_3card:"\<forall>cls\<in>set F. card cls = 3"
    by fastforce
  from snoc(2) have card_c:"card c = 3"
    by force
  from this obtain l1 l2 l3 where lit_def:"c= {l1,l2,l3} \<and> sorted [l1,l2,l3]"
    using choiceClause by blast
  define c_part where c_part_def:"c_part =
    {{(1::nat, tolit l1 = Pos, var l1, 0::nat), (2, False, length F, 0)},
     {(1, tolit l2 = Pos, var l2, 0), (2, False, length F, 1)},
     {(1, tolit l3 = Pos, var l3, 0), (2, False, length F, 2)}}"
  from c_part_def have c_part_card:"card c_part \<le> 3"
    by (simp add: three_elements_card)
  from c_part_def card_c lit_def have split:"
    \<Union> {{{(1, tolit l1 = Pos, var l1, 0), (2, False, i, 0)}, {(1, tolit l2 = Pos, var l2, 0), (2, False, i, 1)},
        {(1, tolit l3 = Pos, var l3, 0), (2, False, i, 2)}} |
        l1 l2 l3 i.
        i < length (F @ [c]) \<and> {l1, l2, l3} = (F @ [c]) ! i \<and> sorted_list_of_set ((F @ [c]) ! i) = [l1, l2, l3]} =
    \<Union> {{{(1, tolit l1 = Pos, var l1, 0), (2, False, i, 0)}, {(1, tolit l2 = Pos, var l2, 0), (2, False, i, 1)},
         {(1, tolit l3 = Pos, var l3, 0), (2, False, i, 2)}} |
        l1 l2 l3 i. i < length F \<and> {l1, l2, l3} = F ! i \<and> sorted_list_of_set (F ! i) = [l1, l2, l3]} \<union> c_part"
    using clause_split_union[where F = F and c= c and lita = l1 and litb = l2 and litc = l3]
    by fast
  from this have "card (\<Union> {{{(1::nat, tolit l1 = Pos, var l1, 0::nat), (2, False, i, 0)},
                            {(1, tolit l2 = Pos, var l2, 0), (2, False, i, 1)},
                            {(1, tolit l3 = Pos, var l3, 0), (2, False, i, 2)}} |
        l1 l2 l3 i. i < length F \<and> {l1, l2, l3} = F ! i \<and> sorted_list_of_set (F ! i) = [l1, l2, l3]} \<union> c_part) \<le>
                  card (\<Union> {{{(1::nat, tolit l1 = Pos, var l1, 0::nat), (2, False, i, 0)},
                            {(1, tolit l2 = Pos, var l2, 0), (2, False, i, 1)},
                            {(1, tolit l3 = Pos, var l3, 0), (2, False, i, 2)}} |
        l1 l2 l3 i. i < length F \<and> {l1, l2, l3} = F ! i \<and> sorted_list_of_set (F ! i) = [l1, l2, l3]}) + card c_part"
    using card_Un_le
    by fast
  from this snoc(1) c_part_card F_cls_3card have "
        card (\<Union> {{{(1::nat, tolit l1 = Pos, var l1, 0::nat), (2, False, i, 0)},
                            {(1, tolit l2 = Pos, var l2, 0), (2, False, i, 1)},
                            {(1, tolit l3 = Pos, var l3, 0), (2, False, i, 2)}} |
        l1 l2 l3 i. i < length F \<and> {l1, l2, l3} = F ! i \<and> sorted_list_of_set (F ! i) = [l1, l2, l3]} \<union> c_part)
        \<le> 3*length F + 3"  by simp
  from this split show ?case
    by auto
qed

lemma card_gadget:"card {{(a,b,i,c),(d,e,i,f)} |i. i < length F} \<le> length F"
proof (induction F rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  from this have "{{(a, b, i, c), (d, e, i, f)} |i. i < length (xs @ [x])} =
                  {{(a, b, i, c), (d, e, i, f)} |i. i < length xs \<or> i = length xs}"
    by fastforce
  from this have "{{(a, b, i, c), (d, e, i, f)} |i. i < length (xs @ [x])} =
                  {{(a, b, i, c), (d, e, i, f)} |i. i < length xs} \<union>
                  {{(a, b, i, c), (d, e, i, f)} |i. i = length xs}"
    by auto
  from this have "card {{(a, b, i, c), (d, e, i, f)} |i. i < length (xs @ [x])} \<le>
                  card {{(a, b, i, c), (d, e, i, f)} |i. i < length xs} +
                  card {{(a, b, i, c), (d, e, i, f)} |i. i = length xs}"
    using card_Un_le
    by smt
  from this snoc show ?case
    by simp
qed


lemma card_gadget2:"card {{(a,b,i,c),(d,e,f,g)} |i. i < length F} \<le> length F"
proof (induction F rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  from this have "{{(a, b, i, c), (d, e, f, g)} |i. i < length (xs @ [x])} =
                  {{(a, b, i, c), (d, e, f, g)} |i. i < length xs \<or> i = length xs}"
    by fastforce
  from this have "{{(a, b, i, c), (d, e, f, g)} |i. i < length (xs @ [x])} =
                  {{(a, b, i, c), (d, e, f, g)} |i. i < length xs} \<union>
                  {{(a, b, i, c), (d, e, f, g)} |i. i = length xs}"
    by auto
  from this have "card {{(a, b, i, c), (d, e, f, g)} |i. i < length (xs @ [x])} \<le>
                  card {{(a, b, i, c), (d, e, f, g)} |i. i < length xs} +
                  card {{(a, b, i, c), (d, e, f, g)} |i. i = length xs}"
    using card_Un_le
    by smt
  from this snoc show ?case
    by simp
qed

lemma E_graph_card:"\<forall>cls\<in>set F. card cls = 3 \<Longrightarrow> card (
      {{(0::nat,False,0,0::nat), (0,False,0,1)}, {(0,False,0,1), (0,False,0,2)}, {(0,False,0,0), (0,False,0,2)}} \<union>
      {{(0,False,0,2),(1, True,  var l,0)}| l. (l\<in>(\<Union> (set F)))} \<union>
      {{(0,False,0,2),(1, False,  var l,0)}| l. (l\<in>(\<Union> (set F)))} \<union>
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
      {{(2,False,i,5),(0,False,0,0)} |  i. i < length F}\<union>
      {{(2,False,i,5),(0,False,0,2)} |  i. i < length F}) \<le> 21 * length F + 3"
proof -
  assume asms: "\<forall>cls\<in>set F. card cls = 3"
  define E where E_def:"E =
    {{(0::nat,False,0,0::nat), (0,False,0,1)}, {(0,False,0,1), (0,False,0,2)}, {(0,False,0,0), (0,False,0,2)}} \<union>
      {{(0,False,0,2),(1, True,  var l,0)}| l. (l\<in>(\<Union> (set F)))} \<union>
      {{(0,False,0,2),(1, False,  var l,0)}| l. (l\<in>(\<Union> (set F)))} \<union>
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
      {{(2,False,i,5),(0,False,0,0)} |  i. i < length F}\<union>
      {{(2,False,i,5),(0,False,0,2)} |  i. i < length F}"
  define E_main where E_main_def:"E_main = {{(0::nat,False,0::nat,0::nat), (0,False,0,1)},
              {(0,False,0,1), (0,False,0,2)},
              {(0,False,0,0), (0,False,0,2)}}"
  from this have card1:"card E_main = 3"
    by (simp add: doubleton_eq_iff)
  define E_posLitToH where E_posLitToH_def:"E_posLitToH =
    {{(0::nat,False,0::nat,2::nat),(1, True,  var l,0)}| l. (l\<in>(\<Union> (set F)))}"
  from this asms have card2:"card E_posLitToH \<le> 3*length F" using card_E_var
    by fast
  define E_negLitToH where E_negLitToH_def:"E_negLitToH =
    {{(0::nat,False,0::nat,2::nat),(1, False,  var l,0)}| l. (l\<in>(\<Union> (set F)))}"
  from this asms have card3:"card E_negLitToH \<le> 3*length F" using card_E_var
    by fast
  define E_litTolit where E_litTolit_def:"E_litTolit =
    {{(1::nat, False, var l,0::nat),(1, True , var l,0)}|l . l\<in>(\<Union> (set F))}"
  from this asms have card4:"card E_litTolit \<le> 3*length F" using card_E_var2
    by fast
  define E_litTogadget where E_litTogadget_def:"E_litTogadget =
    \<Union>{{{(1::nat,tolit l1 = Pos,var l1,0::nat),(2,False,i,0)},
    {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)},
    {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}}|
    l1 l2 l3 i . i < length F \<and> {l1,l2,l3} = F ! i \<and> sorted_list_of_set (F!i) = [l1,l2,l3]}"
  from this asms have card5:"card E_litTogadget \<le> 3*length F"
    using card_varToGadget
    by blast
  define gad_part1 where gad_part1_def:"gad_part1 = {{(2::nat,False,i,0::nat),(2,False,i,1)} | i. i < length F}"
  from this asms have card6:"card gad_part1 \<le> length F"
    using card_gadget
    by fast
  define gad_part2 where gad_part2_def:"gad_part2 = {{(2::nat,False,i,0::nat),(2,False,i,3)} |i. i < length F}"
  from this asms have card7:"card gad_part2 \<le> length F"
    using card_gadget
    by fast
  define gad_part3 where gad_part3_def:"gad_part3 = {{(2::nat,False,i,1::nat),(2,False,i,3)} | i. i < length F}"
  from this asms have card8:"card gad_part3 \<le> length F"
    using card_gadget
    by fast
  define gad_part4 where gad_part4_def:"gad_part4 = {{(2::nat,False,i,3::nat),(2,False,i,4)} | i. i < length F}"
  from this asms have card9:"card gad_part4 \<le> length F"
    using card_gadget
    by fast
  define gad_part5 where gad_part5_def:"gad_part5 = {{(2::nat,False,i,2::nat),(2,False,i,4)} | i. i < length F}"
  from this asms have card10:"card gad_part5 \<le> length F"
    using card_gadget
    by fast
  define gad_part6 where gad_part6_def:"gad_part6 = {{(2::nat,False,i,2::nat),(2,False,i,5)} | i. i < length F}"
  from this asms have card11:"card gad_part6 \<le> length F"
    using card_gadget
    by fast
  define gad_part7 where gad_part7_def:"gad_part7 = {{(2::nat,False,i,4::nat),(2,False,i,5)} | i. i < length F}"
  from this asms have card12:"card gad_part7 \<le> length F"
    using card_gadget
    by fast
  define gad_part8 where gad_part8_def:"gad_part8 = {{(2::nat,False,i,5::nat),(0, False, 0, 0)} | i. i < length F}"
  from this asms have card13:"card gad_part8 \<le> length F"
    using card_gadget2
    by fast
  define gad_part9 where gad_part9_def:"gad_part9 = {{(2::nat,False,i,5::nat),(0, False, 0, 2)} | i. i < length F}"
  from this asms have card14:"card gad_part9 \<le> length F"
    using card_gadget2
    by fast

  define E_var2 where E_var2_def:"E_var2 = E_posLitToH \<union> E_negLitToH"
  define E_var3 where E_var3_def:"E_var3 = E_litTolit \<union> E_litTogadget"
  define E_var where E_var_def:"E_var = E_var2 \<union> E_var3"
  define E_main_var where E_main_var_def:"E_main_var = E_var \<union> E_main"
  from E_var2_def have E_var2_card:"card E_var2 \<le> card E_posLitToH + card E_negLitToH"
    using card_Un_le
    by blast
  from E_var3_def have E_var3_card:"card E_var3 \<le> card E_litTolit + card E_litTogadget"
    using card_Un_le
    by blast
  from E_var_def have E_var_card':"card E_var \<le> card E_var2 + card E_var3 "
    using card_Un_le
    by blast
  from E_var_card' E_var2_card E_var3_card have E_var_card:
    "card E_var \<le> card E_posLitToH + card E_negLitToH + card E_litTolit + card E_litTogadget"
    by linarith

  from E_main_var_def have E_main_var_card':"card E_main_var \<le> card E_var + card E_main "
    using card_Un_le
    by blast

  from E_main_var_card' E_var_card have E_main_var_card:"card E_main_var \<le>
    card E_posLitToH + card E_negLitToH + card E_litTolit + card E_litTogadget + card E_main"
    by linarith


  define gad_part12 where gad_part12_def:"gad_part12 = gad_part1 \<union> gad_part2"
  define gad_part34 where gad_part34_def:"gad_part34 = gad_part3 \<union> gad_part4"
  define gad_part56 where gad_part56_def:"gad_part56 = gad_part5 \<union> gad_part6"
  define gad_part78 where gad_part78_def:"gad_part78 = gad_part7 \<union> gad_part8"
  define gad_part1234 where gad_part1234_def:"gad_part1234 = gad_part12 \<union> gad_part34"
  define gad_part5678 where gad_part5678_def:"gad_part5678 = gad_part56 \<union> gad_part78"
  define gad_part1to8 where gad_part1to8_def:"gad_part1to8 = gad_part1234 \<union> gad_part5678"
  define E_gadget where E_gadget_def:"E_gadget = gad_part1to8 \<union> gad_part9"

  from gad_part12_def have gad_part12_card:"card gad_part12 \<le> card gad_part1 + card gad_part2"
    using card_Un_le
    by blast

  from gad_part34_def have gad_part34_card:"card gad_part34 \<le> card gad_part3 + card gad_part4"
    using card_Un_le
    by blast

  from gad_part56_def have gad_part56_card:"card gad_part56 \<le> card gad_part5 + card gad_part6"
    using card_Un_le
    by blast

  from gad_part78_def have gad_part78_card:"card gad_part78 \<le> card gad_part7 + card gad_part8"
    using card_Un_le
    by blast

  from gad_part1234_def have gad_part1234_card:"card gad_part1234 \<le> card gad_part12 + card gad_part34"
    using card_Un_le
    by blast

  from gad_part5678_def have gad_part5678_card:"card gad_part5678 \<le> card gad_part56 + card gad_part78"
    using card_Un_le
    by blast

  from gad_part1to8_def have gad_part1to8_card:"card gad_part1to8 \<le> card gad_part1234 + card gad_part5678"
    using card_Un_le
    by blast

  from E_gadget_def have E_gadget_card':"card E_gadget \<le> card gad_part1to8 + card gad_part9"
    using card_Un_le
    by blast
  from  gad_part12_card gad_part34_card gad_part56_card gad_part78_card
        gad_part1234_card gad_part5678_card gad_part1to8_card E_gadget_card'
  have E_var_card:
    "card E_gadget \<le> card gad_part1 + card gad_part2 + card gad_part3 +
                      card gad_part4 + card gad_part5 + card gad_part6 +
                      card gad_part7 + card gad_part8 + card gad_part9"
    by linarith



  from E_def E_main_def E_posLitToH_def E_negLitToH_def E_litTolit_def E_litTogadget_def
      gad_part1_def gad_part2_def gad_part3_def
      gad_part4_def gad_part5_def gad_part6_def
      gad_part7_def gad_part8_def gad_part9_def
  have "E = E_main \<union> E_posLitToH \<union> E_negLitToH \<union> E_litTolit \<union> E_litTogadget \<union>
            gad_part1 \<union> gad_part2 \<union> gad_part3 \<union>
            gad_part4 \<union> gad_part5 \<union> gad_part6 \<union>
            gad_part7 \<union> gad_part8 \<union> gad_part9 "
    by fast

  from this E_main_var_def E_gadget_def E_var_def E_var2_def E_var3_def gad_part1to8_def
        gad_part1234_def gad_part5678_def gad_part12_def gad_part34_def gad_part56_def gad_part78_def
  have "E =E_main_var \<union> E_gadget"
    by fastforce
  from this have "card E \<le> card E_main_var + card E_gadget"
    using card_Un_le
    by blast

  from this E_var_card E_main_var_card have "card E \<le>
            card E_main + card E_posLitToH + card E_negLitToH + card E_litTolit + card E_litTogadget +
            card gad_part1 + card gad_part2 + card gad_part3 +
            card gad_part4 + card gad_part5 + card gad_part6 +
            card gad_part7 + card gad_part8 + card gad_part9"
    by linarith

  from  this card1 card2 card3 card4 card5 card6 card7
        card8 card9 card10 card11 card12 card13 card14 have
    "card E \<le> 21* length F + 3"
    by linarith
  from this E_def show ?thesis
    by fast
qed



lemma sat_to_three_col_size:
  "size_3C (sat_three_col F) \<le> sat_to_three_col_space (size_SAT F)"
  using E_graph_card
  by (auto simp: size_3C_def sat_three_col_def sat_to_three_col_space_def size_SAT_def)



theorem sat_to_is_ispolyred: "ispolyred sat_to_three_col three_sat three_colorability size_SAT size_3C"
  unfolding ispolyred_def
  apply(rule exI[where x=sat_three_col])
  apply(rule exI[where x=sat_to_three_col_time])
  apply(rule exI[where x=sat_to_three_col_space])
  apply(safe)
  subgoal using sat_to_three_col_refines
    by simp
  subgoal using sat_to_three_col_size
    by simp
  subgoal unfolding poly_def sat_to_three_col_time_def apply(rule exI[where x=2]) by auto
  subgoal unfolding poly_def sat_to_three_col_space_def apply(rule exI[where x=2]) by auto
  using is_reduction_sat_three_col
  apply (simp add: is_reduction_def)
done

end