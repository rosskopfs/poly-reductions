theory SAT_Plan_Base_Nat 
  imports "Verified_SAT_Based_AI_Planning.SAT_Plan_Base" Primitives
begin

definition  encode_state_variable_nat
  :: "nat \<Rightarrow> nat \<Rightarrow> nat\<Rightarrow> nat"
  where "encode_state_variable_nat t k v = ( if v-1 >0  then 1##(0##t##k##0)##0
else 2##(1##(0##t##k##0)##0)##0)"

definition  encode_state_variable_tail
  :: "nat \<Rightarrow> nat \<Rightarrow> nat\<Rightarrow> nat"
  where "encode_state_variable_tail t k v = encode_state_variable_nat t k v"

lemma subtail_encode_state_variable:
"encode_state_variable_tail t k v = encode_state_variable_nat t k v"
  by (simp add: encode_state_variable_tail_def)

lemma sub_encode_state_variable:
  assumes "v \<noteq> None"
  shows "encode_state_variable_nat t k (bool_option_encode v)
        = sat_formula_encode (encode_state_variable t k v)"
  using assms
  apply (auto simp add: encode_state_variable_nat_def 
 encode_state_variable_def 
sub_cons cons0 simp del:list_encode.simps  split:bool.splits)
  done

definition  encode_initial_state_list
  :: "'variable strips_list_problem \<Rightarrow> sat_plan_variable formula" 
  where "encode_initial_state_list \<Pi>
    \<equiv> let I = initial_of \<Pi>
        ; vs = variables_of \<Pi>
      in \<^bold>\<And>(map (\<lambda>v. encode_state_variable 0 (index vs v) (map_list_find I v) \<^bold>\<or> \<bottom>)
    (filter (\<lambda>v. map_list_find I v \<noteq> None) vs))"

lemma sublist_encode_initial_state:
"encode_initial_state_list P = encode_initial_state (strips_list_problem_to_problem P)"
  apply (auto simp add: encode_initial_state_list_def
      encode_initial_state_def sub_map_list_find Let_def
)
  done

fun map_encode_initial_state :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat  \<Rightarrow> nat" where 
"map_encode_initial_state t I vs  xs = (if xs =0 then 0 else ( 4 ## (encode_state_variable_nat t (index_nat vs (hd_nat xs)) (map_list_find_nat I (hd_nat xs)))## (0##0) ## 0) ## map_encode_initial_state t I vs (tl_nat xs))  "

fun map_encode_initial_state_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat  \<Rightarrow> nat" where 
"map_encode_initial_state_acc t I vs acc  xs = (if xs =0 then acc else map_encode_initial_state_acc t I vs (( 4 ## (encode_state_variable_tail t (index_nat vs (hd_nat xs)) (map_list_find_nat I (hd_nat xs)))## (0##0) ## 0) ## acc) (tl_nat xs))  "

lemma  map_encode_initial_state_induct:
"map_encode_initial_state_acc t I vs acc xs = map_acc  (\<lambda>v. 4 ## (encode_state_variable_nat t (index_nat vs v) (map_list_find_nat I v))## (0##0) ## 0) acc xs "
  apply(induct t I vs acc xs rule: map_encode_initial_state_acc.induct)
  apply (auto simp add: subtail_encode_state_variable)
  done

definition map_encode_initial_state_tail ::  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat  \<Rightarrow> nat" where 
"map_encode_initial_state_tail  t I vs xs = reverse_nat ( map_encode_initial_state_acc t I vs 0 xs)"

lemma submap_encode_initial_state:
"map_encode_initial_state t I vs xs = map_nat (\<lambda>v. 4 ## (encode_state_variable_nat t (index_nat vs v) (map_list_find_nat I v))## (0##0) ## 0) xs"
  apply (induct t I vs xs rule: map_encode_initial_state.induct)
  apply (auto)
  done

lemma subtail_map_encode_initial_state:
"map_encode_initial_state_tail  t I vs xs = map_encode_initial_state  t I vs xs"
  using map_encode_initial_state_induct map_encode_initial_state_tail_def 
submap_encode_initial_state subtail_map by presburger


declare map_list_find_nat.simps[simp del]
fun filter_defined :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"filter_defined s n = (if n = 0 then 0 else if map_list_find_nat s (hd_nat n) \<noteq> 0 then (hd_nat n)##filter_defined s (tl_nat n) else filter_defined s (tl_nat n))"

fun filter_defined_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"filter_defined_acc s acc n = (if n = 0 then acc else if map_list_find_nat s (hd_nat n) \<noteq> 0 then filter_defined_acc s ((hd_nat n)##acc) (tl_nat n) else filter_defined_acc s acc (tl_nat n))"

lemma subfilter_defined :
"filter_defined s n = filter_nat (\<lambda>v. map_list_find_nat s v \<noteq> 0) n "
  apply (induct s n rule: filter_defined.induct)
  apply auto
  done

lemma filter_defined_induct:
"filter_defined_acc s acc n = filter_acc (\<lambda>v. map_list_find_nat s v \<noteq> 0) acc n"
  apply( induct s acc n rule:filter_defined_acc.induct)
  apply auto
  done

definition filter_defined_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"filter_defined_tail s n  = reverse_nat (filter_defined_acc s 0 n)"

lemma subtail_filter_defined :
"filter_defined_tail s n  = filter_defined s n  "
  using  filter_defined_tail_def filter_defined_induct subfilter_defined
subtail_filter  by presburger


definition  encode_initial_state_nat
  :: "nat\<Rightarrow> nat" 
  where "encode_initial_state_nat \<Pi>
    \<equiv> let I = nth_nat (Suc (Suc 0)) \<Pi>
        ; vs = nth_nat 0 \<Pi>
      in BigAnd_nat ( map_encode_initial_state 0 I vs
    (filter_defined I  vs))"

definition  encode_initial_state_tail
  :: "nat\<Rightarrow> nat" 
  where "encode_initial_state_tail \<Pi>
    \<equiv> let I = nth_nat (Suc (Suc 0)) \<Pi>
        ; vs = nth_nat 0 \<Pi>
      in BigAnd_tail ( map_encode_initial_state_tail 0 I vs
    (filter_defined_tail I  vs))"

lemma subtail_encode_initial_state:
"encode_initial_state_tail \<Pi> = encode_initial_state_nat \<Pi>"
  using encode_initial_state_nat_def subtail_map_encode_initial_state encode_initial_state_tail_def subtail_BigAnd subtail_filter_defined by presburger

lemma inj_sasp:"inj sas_plus_assignment_encode"
  using sas_plus_assignment_id 
  by (metis inj_onI)

lemma subnat_encode_initial_state_map: 
"map (\<lambda>x. list_encode
                   [4, encode_state_variable_nat 0 (index (P\<^sub>\<V>) x)
                        (option_encode
                          (map_list_find (map (\<lambda>(s, b). (s, bool_encode b)) (P\<^sub>I)) x)),
                    sat_formula_encode \<bottom>])
         (filter (\<lambda>x. map_list_find (P\<^sub>I) x \<noteq> None) (P\<^sub>\<V>))
= 
map (\<lambda>x. list_encode
                   [4, sat_formula_encode (encode_state_variable 0 (index (P\<^sub>\<V>) x)                        
                          (map_list_find  (P\<^sub>I) x)),
                    sat_formula_encode \<bottom>])
         (filter (\<lambda>x. map_list_find (P\<^sub>I) x \<noteq> None) (P\<^sub>\<V>))
"
  apply (induct "(P\<^sub>\<V>)")
   apply (auto simp add: list_encode_eq  map_list_find_map
sub_encode_state_variable 
 simp del:list_encode.simps simp flip: bool_option_encode.simps)
  done

lemma subnat_encode_initial_state:
"encode_initial_state_nat (strips_list_problem_encode P) =
 sat_formula_encode (encode_initial_state_list P) "
  using inj_sasp
  apply (auto simp only: encode_initial_state_nat_def subfilter_defined 
            strips_list_problem_encode.simps Let_def
            strips_assignment_list_encode_def
            sas_plus_assignment_list_encode_def sub_index[of sas_plus_assignment_encode]
            strips_simp submap_encode_initial_state
          sub_nth nth.simps sub_cons cons0 sub_map_list_find_nat
simp flip: map_map
)
  apply (auto simp only: sub_filter sub_map option_encode_0 filter_map comp_def
 map_list_find_map_none
 inj_map_list_find map_map sub_index 
subnat_encode_initial_state_map
simp flip: sat_formula_encode.simps
)
  apply (auto simp only:sub_BigAnd encode_initial_state_list_def Let_def simp flip: map_map  sat_formula_list_encode_def
comp_def[of sat_formula_encode "\<lambda>x. encode_state_variable 0 (index ((P)\<^sub>\<V>) x) (map_list_find ((P)\<^sub>I) x) \<^bold>\<or> \<bottom>"])
  done

definition  encode_goal_state_list
  :: "'variable strips_list_problem \<Rightarrow> nat \<Rightarrow> sat_plan_variable formula" ("\<Phi>\<^sub>G _" 99)
  where "encode_goal_state_list \<Pi> t
    \<equiv> let
      vs = variables_of \<Pi>
      ; G = goal_of \<Pi>
    in \<^bold>\<And>(map (\<lambda>v. encode_state_variable t (index vs v) (map_list_find G v) \<^bold>\<or> \<bottom>)
      (filter (\<lambda>v. map_list_find G v \<noteq> None) vs))"

lemma sublist_encode_goal_state:
"encode_goal_state_list P t = encode_goal_state (strips_list_problem_to_problem P) t"
  apply (auto simp add: encode_goal_state_list_def
      encode_goal_state_def sub_map_list_find Let_def
)
  done

definition  encode_goal_state_nat
  :: "nat\<Rightarrow> nat \<Rightarrow> nat" 
  where "encode_goal_state_nat \<Pi> t
    \<equiv> let G = nth_nat (Suc (Suc (Suc 0))) \<Pi>
        ; vs = nth_nat 0 \<Pi>
      in BigAnd_nat (map_encode_initial_state t G vs
    (filter_defined G vs))"

definition  encode_goal_state_tail
  :: "nat\<Rightarrow> nat \<Rightarrow> nat" 
  where "encode_goal_state_tail \<Pi> t
    \<equiv> let G = nth_nat (Suc (Suc (Suc 0))) \<Pi>
        ; vs = nth_nat 0 \<Pi>
      in BigAnd_tail (map_encode_initial_state_tail t G vs
    (filter_defined_tail G vs))"

lemma subtail_encode_goal_state:
"encode_goal_state_tail P t = encode_goal_state_nat P t"
  using encode_goal_state_nat_def encode_goal_state_tail_def subtail_BigAnd subtail_filter_defined
 subtail_map_encode_initial_state by presburger

lemma subnat_encode_goal_state_map: 
"map (\<lambda>x. list_encode
                   [4, encode_state_variable_nat t (index (P\<^sub>G) x)
                        (option_encode
                          (map_list_find (map (\<lambda>(s, b). (s, bool_encode b)) (P\<^sub>I)) x)),
                    sat_formula_encode \<bottom>])
         (filter (\<lambda>x. map_list_find (P\<^sub>I) x \<noteq> None) (P\<^sub>G))
= 
map (\<lambda>x. list_encode
                   [4, sat_formula_encode (encode_state_variable t (index (P\<^sub>G) x)                        
                          (map_list_find  (P\<^sub>I) x)),
                    sat_formula_encode \<bottom>])
         (filter (\<lambda>x. map_list_find (P\<^sub>I) x \<noteq> None) (P\<^sub>G))
"
  apply (induct "(P\<^sub>G)")
   apply (auto simp add: list_encode_eq  map_list_find_map
sub_encode_state_variable 
 simp del:list_encode.simps simp flip: bool_option_encode.simps)
  done

lemma subnat_encode_goal_state:
"encode_goal_state_nat (strips_list_problem_encode P) t =
 sat_formula_encode (encode_goal_state_list P t) "
  using inj_sasp
  apply (auto simp only: encode_goal_state_nat_def 
            strips_list_problem_encode.simps Let_def
            strips_assignment_list_encode_def
subfilter_defined submap_encode_initial_state
            sas_plus_assignment_list_encode_def sub_index[of sas_plus_assignment_encode]
            strips_simp
          sub_nth nth.simps sub_cons cons0 sub_map_list_find_nat
simp flip: map_map
)
  apply (auto simp only: sub_filter sub_map option_encode_0 filter_map comp_def
 map_list_find_map_none
 inj_map_list_find map_map sub_index 
subnat_encode_goal_state_map
simp flip: sat_formula_encode.simps
)
  apply (auto simp only:sub_BigAnd encode_goal_state_list_def Let_def simp flip: map_map  sat_formula_list_encode_def
comp_def[of sat_formula_encode "\<lambda>x. encode_state_variable t (index ((P)\<^sub>\<V>) x) (map_list_find (((P)\<^sub>G)) x) \<^bold>\<or> \<bottom>"])
  done

definition encode_operator_precondition_list
  :: "'variable strips_list_problem
    \<Rightarrow> nat
    \<Rightarrow> 'variable strips_operator
    \<Rightarrow> sat_plan_variable formula"
  where "encode_operator_precondition_list \<Pi> t op \<equiv> let
      vs = variables_of \<Pi>
      ; ops = strips_list_problem.operators_of \<Pi>
    in \<^bold>\<And>(map (\<lambda>v.
        \<^bold>\<not> (Atom (Operator t (index ops op))) \<^bold>\<or> Atom (State t (index vs v)))
      (strips_operator.precondition_of op))"

lemma sublist_encode_operator_precondition:
"encode_operator_precondition_list \<Pi> t op =
 encode_operator_precondition (strips_list_problem_to_problem \<Pi>) t op"
  apply (auto simp add: encode_operator_precondition_list_def encode_operator_precondition_def)
  done
fun map_encode_operator_precondition :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"map_encode_operator_precondition t ops op vs xs = (if xs = 0 then 0 else 
( 4 ##(2 ## (1## (1 ## t ##(index_nat ops op) ## 0)##0) ## 0 )##  (1##(0 ## t ##(index_nat vs (hd_nat xs)) ## 0)##0) ## 0)
## map_encode_operator_precondition t ops op vs (tl_nat xs)
)"

fun map_encode_operator_precondition_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"map_encode_operator_precondition_acc acc t ops op vs xs = (if xs = 0 then acc else map_encode_operator_precondition_acc (
( 4 ##(2 ## (1## (1 ## t ##(index_nat ops op) ## 0)##0) ## 0 )##  (1##(0 ## t ##(index_nat vs (hd_nat xs)) ## 0)##0) ## 0)
## acc )t ops op vs (tl_nat xs)
)"

lemma map_encode_operator_precondition_induct:
"map_encode_operator_precondition_acc acc t ops op vs xs = map_acc (\<lambda>v.
        4 ##(2 ## (1## (1 ## t ##(index_nat ops op) ## 0)##0) ## 0 )##  (1##(0 ## t ##(index_nat vs v) ## 0)##0) ## 0)
 acc xs
   "
  apply(induct acc t ops op vs xs rule:map_encode_operator_precondition_acc.induct)
  apply (auto) done


lemma submap_encode_operator_precondition:
"map_encode_operator_precondition t ops op vs xs = 
map_nat (\<lambda>v.
        4 ##(2 ## (1## (1 ## t ##(index_nat ops op) ## 0)##0) ## 0 )##  (1##(0 ## t ##(index_nat vs v) ## 0)##0) ## 0) xs
"
  apply (induct t ops op vs xs rule:map_encode_operator_precondition.induct)
  apply auto
  done

definition map_encode_operator_precondition_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
" map_encode_operator_precondition_tail t ops op vs xs = reverse_nat ( map_encode_operator_precondition_acc 0 t ops op vs xs)  "

lemma subtail_map_encode_operator_precondition:
" map_encode_operator_precondition_tail t ops op vs xs =  map_encode_operator_precondition t ops op vs xs"
  using  map_encode_operator_precondition_tail_def  submap_encode_operator_precondition
 map_encode_operator_precondition_induct subtail_map by presburger

definition encode_operator_precondition_nat
  :: "nat
    \<Rightarrow> nat
    \<Rightarrow> nat
    \<Rightarrow> nat"
  where "encode_operator_precondition_nat \<Pi> t op \<equiv> let
      vs = nth_nat 0 \<Pi>
      ; ops = nth_nat (Suc 0) \<Pi>
    in BigAnd_nat (map_encode_operator_precondition t ops op vs
      (nth_nat 0 op))"

definition encode_operator_precondition_tail
  :: "nat
    \<Rightarrow> nat
    \<Rightarrow> nat
    \<Rightarrow> nat"
  where "encode_operator_precondition_tail \<Pi> t op \<equiv> let
      vs = nth_nat 0 \<Pi>
      ; ops = nth_nat (Suc 0) \<Pi>
    in BigAnd_tail (map_encode_operator_precondition_tail t ops op vs
      (nth_nat 0 op))"

lemma subtail_encode_operator_precondition:
"encode_operator_precondition_tail p t op = encode_operator_precondition_nat p t op"
  using encode_operator_precondition_nat_def encode_operator_precondition_tail_def subtail_BigAnd 
subtail_map_encode_operator_precondition by presburger

lemma inj_strips_op: "inj strips_operator_encode"
  using strips_operator_id 
  by (metis injI)
lemma subnat_encode_operator_precondition:
"encode_operator_precondition_nat (strips_list_problem_encode P) t  (strips_operator_encode op)
= sat_formula_encode (encode_operator_precondition_list P t op)"
  apply (auto simp only:encode_operator_precondition_nat_def
          sub_cons cons0 sub_nth nth.simps
submap_encode_operator_precondition
sas_plus_assignment_list_encode_def sub_map
strips_operator_encode.simps strips_list_problem_encode.simps
 simp flip:sat_variable_encode.simps sat_formula_encode.simps
            
)

  apply (auto simp only: map_map comp_def Let_def simp flip: strips_operator_encode.simps
sas_plus_assignment_list_encode_def
)
  using  inj_strips_op inj_sasp
  apply (auto simp only: strips_operator_list_encode_def  sas_plus_assignment_list_encode_def 
sub_index)
  apply (auto simp only: sub_BigAnd 
encode_operator_precondition_list_def
Let_def
 simp flip:map_map sat_formula_list_encode_def
comp_def[of sat_formula_encode 
"\<lambda>x.\<^bold>\<not> (Atom (Operator t (index ((P)\<^sub>\<O>) op))) \<^bold>\<or> Atom (State t (index ((P)\<^sub>\<V>) x))"])
  done

lemma sub_foldr: "foldr (\<^bold>\<and>) xs (\<^bold>\<not>\<bottom>) = BigAnd xs "
  apply (induct xs)
   apply auto
  done
definition  encode_all_operator_preconditions_list
  :: "'variable strips_list_problem
    \<Rightarrow> 'variable strips_operator list
    \<Rightarrow> nat
    \<Rightarrow> sat_plan_variable formula"
  where "encode_all_operator_preconditions_list \<Pi> ops t \<equiv> let
      l = List.product [0..<t] ops
    in BigAnd (map (\<lambda>(t, op). encode_operator_precondition_list \<Pi> t op) l)"

lemma sublist_encode_all_operator_preconditions:
"encode_all_operator_preconditions_list \<Pi> ops t = 
encode_all_operator_preconditions (strips_list_problem_to_problem \<Pi>) ops t"
  apply (auto simp only:encode_all_operator_preconditions_list_def 
encode_all_operator_preconditions_def
        sublist_encode_operator_precondition sub_foldr
)
  done
lemma "(case x of (x1,x2) \<Rightarrow> (case  x of (x1,x2) \<Rightarrow> f x1 x2) (g x1 x2))
= (case x of (x1,x2) \<Rightarrow> f x1 x2 (g x1 x2))"
  by (simp add: prod.case_eq_if)

fun maps_encode_operator_precondition :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"maps_encode_operator_precondition P xs = (if xs = 0 then 0 else 
 (encode_operator_precondition_nat P (fst_nat (hd_nat xs)) (snd_nat (hd_nat xs))) ##(maps_encode_operator_precondition P (tl_nat xs))
)"

lemma submaps_encode_operator_precondition :
"maps_encode_operator_precondition P xs = map_nat (\<lambda>n. encode_operator_precondition_nat P (fst_nat n) (snd_nat n )) xs "
  apply (induct P xs rule:maps_encode_operator_precondition.induct)
  apply auto
  done

fun maps_encode_operator_precondition_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"maps_encode_operator_precondition_acc P acc xs = (if xs = 0 then acc else maps_encode_operator_precondition_acc  P   
 ((encode_operator_precondition_tail P  (fst_nat (hd_nat xs)) (snd_nat (hd_nat xs))) ## acc ) (tl_nat xs)
)"

lemma  maps_encode_operator_precondition_induct:
"maps_encode_operator_precondition_acc P acc xs = map_acc (\<lambda>n. encode_operator_precondition_nat P (fst_nat n) (snd_nat n )) acc xs "
  apply(induct P acc xs rule:maps_encode_operator_precondition_acc.induct)
  apply (auto simp add: subtail_encode_operator_precondition)
  done

definition maps_encode_operator_precondition_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"maps_encode_operator_precondition_tail P  xs = reverse_nat (maps_encode_operator_precondition_acc P 0 xs)"

lemma subtail_maps_encode_operator_precondition:
"maps_encode_operator_precondition_tail P  xs = maps_encode_operator_precondition P xs"
  using maps_encode_operator_precondition_induct maps_encode_operator_precondition_tail_def
 submaps_encode_operator_precondition subtail_map by presburger

definition  encode_all_operator_preconditions_nat
  :: "nat
    \<Rightarrow> nat
    \<Rightarrow> nat
    \<Rightarrow> nat"
  where "encode_all_operator_preconditions_nat \<Pi> ops t \<equiv> let
      l = product_nat (list_less_nat t) ops
    in BigAnd_nat (maps_encode_operator_precondition \<Pi>  l)"

definition  encode_all_operator_preconditions_tail
  :: "nat
    \<Rightarrow> nat
    \<Rightarrow> nat
    \<Rightarrow> nat"
  where "encode_all_operator_preconditions_tail \<Pi> ops t \<equiv> let
      l = product_tail (list_less_tail t) ops
    in BigAnd_tail (maps_encode_operator_precondition_tail \<Pi>  l)"

lemma subtail_encode_all_operator_preconditions:
"encode_all_operator_preconditions_tail \<Pi> ops t = encode_all_operator_preconditions_nat \<Pi> ops t"
  using encode_all_operator_preconditions_nat_def encode_all_operator_preconditions_tail_def
 subtail_BigAnd subtail_list_less subtail_maps_encode_operator_precondition
 subtail_product by presburger

lemma case_prod_simp:"(\<lambda>x. case x of (a,b) \<Rightarrow> f a b) = (\<lambda>(x,y). f x y)"
  by simp

lemma subnat_encode_all_operator_preconditions:
"encode_all_operator_preconditions_nat (strips_list_problem_encode P) (strips_operator_list_encode ops) t
=
sat_formula_encode(encode_all_operator_preconditions_list P ops t)
"
  using list.map_id [of "[0..<t]" ] sub_product[of id  "[0..<t]" strips_operator_encode  ops ]
  apply (auto simp only: encode_all_operator_preconditions_nat_def 
           sub_list_less    strips_operator_list_encode_def
                    Let_def sub_map map_map comp_def 
                    submaps_encode_operator_precondition
              )
  apply (auto simp only: prod.case_eq_if id_def sub_fst fst_conv sub_snd snd_conv
subnat_encode_operator_precondition )
  apply (auto simp only: sub_BigAnd encode_all_operator_preconditions_list_def
Let_def case_prod_beta'
 simp flip: map_map sat_formula_list_encode_def
      comp_def [of sat_formula_encode  "\<lambda>x. encode_operator_precondition_list P (fst x) (snd x) "])
  done

definition  encode_operator_effect_list
  :: "'variable strips_list_problem
    \<Rightarrow> nat
    \<Rightarrow> 'variable strips_operator
    \<Rightarrow> sat_plan_variable formula"
  where "encode_operator_effect_list \<Pi> t op
    \<equiv> let
        vs = variables_of \<Pi>
        ; ops = operators_of \<Pi>
      in \<^bold>\<And>(map (\<lambda>v.
              \<^bold>\<not>(Atom (Operator t (index ops op)))
              \<^bold>\<or> Atom (State (Suc t) (index vs v)))
            (add_effects_of op)
          @ map (\<lambda>v.
              \<^bold>\<not>(Atom (Operator t (index ops op)))
               \<^bold>\<or> \<^bold>\<not> (Atom (State (Suc t) (index vs v))))
            (delete_effects_of op))"

lemma sublist_encode_operator_effect:
"encode_operator_effect_list \<Pi> t op =
encode_operator_effect (strips_list_problem_to_problem \<Pi>) t op"
  apply (auto simp add: encode_operator_effect_list_def encode_operator_effect_def)
  done

fun map_encode_operator_effect::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_encode_operator_effect t ops op vs n = (if n =0 then 0 else 
( 4 ## (2 ## (1 ## (1 ##  t ## (index_nat ops op)## 0) ## 0) ## 0)
              ## (1 ## (0 ## (Suc t) ## (index_nat vs (hd_nat n))## 0) ## 0) ## 0)
## map_encode_operator_effect t ops op vs (tl_nat n) 
)"

fun map_encode_operator_effect_acc::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_encode_operator_effect_acc acc t ops op vs n = (if n =0 then acc else map_encode_operator_effect_acc( 
( 4 ## (2 ## (1 ## (1 ##  t ## (index_nat ops op)## 0) ## 0) ## 0)
              ## (1 ## (0 ## (Suc t) ## (index_nat vs (hd_nat n))## 0) ## 0) ## 0)
## acc) t ops op vs (tl_nat n) 
)"
lemma map_encode_operator_effect_induct:
"map_encode_operator_effect_acc acc t ops op vs n =  map_acc (\<lambda>v.
             4 ## (2 ## (1 ## (1 ##  t ## (index_nat ops op)## 0) ## 0) ## 0)
              ## (1 ## (0 ## (Suc t) ## (index_nat vs v)## 0) ## 0) ## 0)  acc n"
  apply(induct acc t ops op vs n rule: map_encode_operator_effect_acc.induct)
  apply   auto
  done

lemma submap_encode_operator_effect:
"map_encode_operator_effect t ops op vs n = map_nat (\<lambda>v.
             4 ## (2 ## (1 ## (1 ##  t ## (index_nat ops op)## 0) ## 0) ## 0)
              ## (1 ## (0 ## (Suc t) ## (index_nat vs v)## 0) ## 0) ## 0) n"
  apply( induct t ops op vs n rule :map_encode_operator_effect.induct)
  apply (auto)
  done

definition map_encode_operator_effect_tail ::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
" map_encode_operator_effect_tail t ops op vs n = reverse_nat (map_encode_operator_effect_acc 0 t ops op vs n)"

lemma subtail_map_encode_operator_effect :
"map_encode_operator_effect_tail t ops op vs n = map_encode_operator_effect t ops op vs n"
  using  map_encode_operator_effect_tail_def submap_encode_operator_effect 
 map_encode_operator_effect_induct subtail_map by presburger

fun map_encode_operator_effect2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_encode_operator_effect2 t ops op vs n = (if n=0 then 0 else 
( 4 ## (2 ## (1 ## (1 ##  t ## (index_nat ops op)## 0) ## 0) ## 0)
              ## (2 ## (1 ## (0 ## (Suc t) ## (index_nat vs (hd_nat n)) ## 0) ## 0) ## 0) ## 0)
## map_encode_operator_effect2 t ops op vs (tl_nat n) 
)"
lemma submap_encode_operator_effect2:
"map_encode_operator_effect2 t ops op vs n = map_nat (\<lambda>v.
             4 ## (2 ## (1 ## (1 ##  t ## (index_nat ops op)## 0) ## 0) ## 0)
              ## (2 ## (1 ## (0 ## (Suc t) ## (index_nat vs v) ## 0) ## 0) ## 0) ## 0) n "
  apply( induct t ops op vs n rule :map_encode_operator_effect2.induct)
  apply (auto)
  done


fun map_encode_operator_effect2_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_encode_operator_effect2_acc acc t ops op vs n = (if n=0 then acc else
 map_encode_operator_effect2_acc (
( 4 ## (2 ## (1 ## (1 ##  t ## (index_nat ops op)## 0) ## 0) ## 0)
              ## (2 ## (1 ## (0 ## (Suc t) ## (index_nat vs (hd_nat n)) ## 0) ## 0) ## 0) ## 0)
## acc) t ops op vs (tl_nat n) 
)"

lemma map_encode_operator_effect2_induct:
"map_encode_operator_effect2_acc acc t ops op vs n = map_acc (\<lambda>v.
             4 ## (2 ## (1 ## (1 ##  t ## (index_nat ops op)## 0) ## 0) ## 0)
              ## (2 ## (1 ## (0 ## (Suc t) ## (index_nat vs v) ## 0) ## 0) ## 0) ## 0)  acc n "
  apply(induct acc t ops op vs n rule: map_encode_operator_effect2_acc.induct)
  apply auto
  done

definition  map_encode_operator_effect2_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
" map_encode_operator_effect2_tail  t ops op vs n = 
reverse_nat (map_encode_operator_effect2_acc 0 t ops op vs n)"

lemma subtail_map_encode_operator_effect2:
"map_encode_operator_effect2_tail t ops op vs n  = map_encode_operator_effect2 t ops op vs n "
  using  map_encode_operator_effect2_tail_def map_encode_operator_effect2_induct 
 submap_encode_operator_effect2 subtail_map by presburger


definition  encode_operator_effect_nat
  :: "nat
    \<Rightarrow> nat
    \<Rightarrow> nat
    \<Rightarrow> nat"
  where "encode_operator_effect_nat \<Pi> t op
    \<equiv> let
        vs = nth_nat 0 \<Pi>
        ; ops = nth_nat (Suc 0) \<Pi>
      in BigAnd_nat( append_nat  (map_encode_operator_effect t ops op vs
            (nth_nat (Suc 0) op))
          (map_encode_operator_effect2 t ops op vs
            (nth_nat (Suc (Suc 0)) op)))"

definition  encode_operator_effect_tail
  :: "nat
    \<Rightarrow> nat
    \<Rightarrow> nat
    \<Rightarrow> nat"
  where "encode_operator_effect_tail \<Pi> t op
    \<equiv> let
        vs = nth_nat 0 \<Pi>
        ; ops = nth_nat (Suc 0) \<Pi>
      in BigAnd_tail( append_tail  (map_encode_operator_effect_tail t ops op vs
            (nth_nat (Suc 0) op))
          (map_encode_operator_effect2_tail t ops op vs
            (nth_nat (Suc (Suc 0)) op)))"

lemma subtail_encode_operator_effect:
"encode_operator_effect_tail P t op = encode_operator_effect_nat P t op"
  using encode_operator_effect_nat_def encode_operator_effect_tail_def subtail_BigAnd subtail_append
 subtail_map_encode_operator_effect subtail_map_encode_operator_effect2 by presburger

lemma subnat_encode_operator_effect:
"encode_operator_effect_nat (strips_list_problem_encode P) t (strips_operator_encode op) = 
 sat_formula_encode (encode_operator_effect_list P t op)"
  using  inj_strips_op inj_sasp
  apply (auto simp only: encode_operator_effect_nat_def
submap_encode_operator_effect submap_encode_operator_effect2
      sub_cons cons0 sub_index strips_operator_encode.simps sub_nth nth.simps strips_list_problem_encode.simps)

  apply (auto simp only: 
sas_plus_assignment_list_encode_def sub_map
simp flip:strips_operator_encode.simps)
  apply (auto simp only: simp flip: sas_plus_assignment_list_encode_def strips_operator_encode.simps  )
  apply (auto simp only: sub_cons sas_plus_assignment_list_encode_def strips_operator_list_encode_def
      Let_def map_map comp_def sub_index simp flip: sat_variable_encode.simps sat_formula_encode.simps
 )
  apply (auto simp only:sub_append simp flip:  map_append  map_map comp_def [of sat_formula_encode "\<lambda>x. Not (Atom (Operator t (index ((P)\<^sub>\<O>) op))) \<^bold>\<or>
                      Atom (State (Suc t) (index ((P)\<^sub>\<V>) x))" ] comp_def [of sat_formula_encode "\<lambda>x. Not (Atom (Operator t (index ((P)\<^sub>\<O>) op))) \<^bold>\<or>
                     Not ( Atom (State (Suc t) (index ((P)\<^sub>\<V>) x)))" ]

 )
  apply (auto simp only: simp flip: sat_formula_list_encode_def)
  apply (auto simp only: map_append sub_BigAnd encode_operator_effect_list_def Let_def)
  done

definition encode_all_operator_effects_list
  :: "'variable strips_list_problem
    \<Rightarrow> 'variable strips_operator list
    \<Rightarrow> nat
    \<Rightarrow> sat_plan_variable formula"
  where "encode_all_operator_effects_list \<Pi> ops t
    \<equiv> let l = List.product [0..<t] ops
      in BigAnd (map (\<lambda>(t, op). encode_operator_effect_list \<Pi> t op) l)"

lemma sublist_encode_all_operator_effects:
"encode_all_operator_effects_list \<Pi> ops t =
encode_all_operator_effects (strips_list_problem_to_problem \<Pi>) ops t"
  apply (auto simp add: encode_all_operator_effects_list_def encode_all_operator_effects_def
    sub_foldr sublist_encode_operator_effect
)
  done
fun map_encode_all_operator_effects :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_encode_all_operator_effects P xs = (if xs = 0 then 0 
else (encode_operator_effect_nat P (fst_nat (hd_nat xs)) (snd_nat (hd_nat xs))) ##
map_encode_all_operator_effects P (tl_nat xs)
 )"

fun map_encode_all_operator_effects_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_encode_all_operator_effects_acc acc P xs = (if xs = 0 then acc 
else map_encode_all_operator_effects_acc( (encode_operator_effect_tail P (fst_nat (hd_nat xs)) (snd_nat (hd_nat xs))) ##
acc) P (tl_nat xs)
 )"

lemma map_encode_all_operator_effects_induct:
"map_encode_all_operator_effects_acc acc P xs  = map_acc
 (\<lambda>n. encode_operator_effect_nat P (fst_nat n) (snd_nat n)) acc xs "
  apply(induct acc P xs rule:map_encode_all_operator_effects_acc.induct)
  apply (auto simp add:subtail_encode_operator_effect)
  done

definition  map_encode_all_operator_effects_tail:: "nat => nat => nat" where
" map_encode_all_operator_effects_tail P xs = reverse_nat ( map_encode_all_operator_effects_acc 0 P xs)"

lemma submap_encode_all_operator_effects:
"map_encode_all_operator_effects P xs =
map_nat (\<lambda>n. encode_operator_effect_nat P (fst_nat n) (snd_nat n)) xs "
  apply (induct P xs rule:map_encode_all_operator_effects.induct)
  apply auto
  done

lemma subtail_map_encode_all_operator_effects:
" map_encode_all_operator_effects_tail P xs =  map_encode_all_operator_effects P xs"
  using   map_encode_all_operator_effects_tail_def   map_encode_all_operator_effects_induct 
submap_encode_all_operator_effects subtail_map
  by presburger


definition encode_all_operator_effects_nat
  :: "nat
    \<Rightarrow> nat
    \<Rightarrow> nat
    \<Rightarrow> nat"
  where "encode_all_operator_effects_nat P ops t
    \<equiv> let l = product_nat (list_less_nat t) ops
      in BigAnd_nat (map_encode_all_operator_effects P l)"

definition encode_all_operator_effects_tail
  :: "nat
    \<Rightarrow> nat
    \<Rightarrow> nat
    \<Rightarrow> nat"
  where "encode_all_operator_effects_tail P ops t
    \<equiv> let l = product_tail (list_less_tail t) ops
      in BigAnd_tail(map_encode_all_operator_effects_tail P l)"

lemma subtail_encode_all_operator_effects:
"encode_all_operator_effects_tail P ops t = encode_all_operator_effects_nat P ops t"
  using encode_all_operator_effects_nat_def encode_all_operator_effects_tail_def subtail_BigAnd
 subtail_list_less subtail_map_encode_all_operator_effects subtail_product by presburger

lemma subnat_encode_all_operator_effects:
"encode_all_operator_effects_nat (strips_list_problem_encode P) (strips_operator_list_encode ops) t
= 
sat_formula_encode (encode_all_operator_effects_list P ops t)"
using list.map_id [of "[0..<t]" ] sub_product[of id  "[0..<t]" strips_operator_encode  ops ]
  apply (auto simp only: encode_all_operator_effects_nat_def 
submap_encode_all_operator_effects
           sub_list_less    strips_operator_list_encode_def
                    Let_def sub_map map_map comp_def 
                    
              )
  apply (auto simp only: prod.case_eq_if id_def sub_fst fst_conv sub_snd snd_conv
subnat_encode_operator_effect )
  apply (auto simp only: sub_BigAnd encode_all_operator_effects_list_def
Let_def case_prod_beta'
 simp flip: map_map sat_formula_list_encode_def
      comp_def [of sat_formula_encode  "\<lambda>x. encode_operator_effect_list P (fst x) (snd x) "])
  done


definition encode_operators_list
  :: "'variable strips_list_problem \<Rightarrow> nat \<Rightarrow> sat_plan_variable formula"
  where "encode_operators_list \<Pi> t
    \<equiv> let ops = operators_of \<Pi>
      in encode_all_operator_preconditions_list \<Pi> ops t \<^bold>\<and> encode_all_operator_effects_list \<Pi> ops t"

lemma sublist_encode_operators:
"encode_operators_list P t = encode_operators (strips_list_problem_to_problem P) t"
  apply (auto simp add:encode_operators_list_def encode_operators_def sublist_encode_all_operator_preconditions
        sublist_encode_all_operator_effects
 )
  done

definition encode_operators_nat
  :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "encode_operators_nat \<Pi> t
    \<equiv> let ops = nth_nat (Suc 0) \<Pi>
      in 3 ## (encode_all_operator_preconditions_nat \<Pi> ops t) ## (encode_all_operator_effects_nat \<Pi> ops t) ## 0"

definition encode_operators_tail
  :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "encode_operators_tail \<Pi> t
    \<equiv> let ops = nth_nat (Suc 0) \<Pi>
      in 3 ## (encode_all_operator_preconditions_tail \<Pi> ops t) ##
 (encode_all_operator_effects_tail \<Pi> ops t) ## 0"

lemma subtail_encode_operators:
"encode_operators_tail \<Pi> t = encode_operators_nat \<Pi> t"
  by (simp add: encode_operators_nat_def encode_operators_tail_def 
subtail_encode_all_operator_effects subtail_encode_all_operator_preconditions)

lemma subnat_encode_operators:
"encode_operators_nat (strips_list_problem_encode P) t =
sat_formula_encode (encode_operators_list P t)"
  apply (auto simp only: strips_list_problem_encode.simps encode_operators_nat_def
      sub_nth nth.simps
)
  apply (auto simp only:Let_def subnat_encode_all_operator_preconditions 
encode_operators_list_def
subnat_encode_all_operator_effects sub_cons cons0
                    simp flip: strips_list_problem_encode.simps sat_formula_encode.simps )
  done

definition  encode_negative_transition_frame_axiom_list
  :: "'variable strips_list_problem
    \<Rightarrow> nat
    \<Rightarrow> 'variable
    \<Rightarrow> sat_plan_variable formula"
  where "encode_negative_transition_frame_axiom_list \<Pi> t v
    \<equiv> let vs = variables_of \<Pi>
        ; ops = operators_of \<Pi>
        ; deleting_operators = filter (\<lambda>op. ListMem v (delete_effects_of op)) ops
      in \<^bold>\<not>(Atom (State t (index vs v)))
          \<^bold>\<or> (Atom (State (Suc t) (index vs v))
          \<^bold>\<or> \<^bold>\<Or> (map (\<lambda>op. Atom (Operator t (index ops op))) deleting_operators))"

lemma sublist_encode_negative_transition_frame_axiom:
"encode_negative_transition_frame_axiom_list \<Pi> t v = 
encode_negative_transition_frame_axiom (strips_list_problem_to_problem \<Pi>) t v"
  apply (auto simp add:encode_negative_transition_frame_axiom_list_def
encode_negative_transition_frame_axiom_def) done

declare elemof.simps [simp del]
fun filter_del_effects :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"filter_del_effects v ops = (if ops = 0 then 0 else if 
elemof v (nth_nat (Suc (Suc 0)) (hd_nat ops)) \<noteq> 0 then 
(hd_nat ops) ## filter_del_effects v (tl_nat ops) else  filter_del_effects v (tl_nat ops) )"

lemma subfilter_del_effects:
"filter_del_effects v ops = filter_nat (\<lambda>op. elemof v (nth_nat (Suc (Suc 0)) op) \<noteq> 0) ops "
  apply(induct v ops rule:filter_del_effects.induct)
  apply auto
  done

fun filter_del_effects_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"filter_del_effects_acc acc v ops = (if ops = 0 then acc else if 
elemof v (nth_nat (Suc (Suc 0)) (hd_nat ops)) \<noteq> 0 then 
filter_del_effects_acc ((hd_nat ops) ## acc) v (tl_nat ops) else  filter_del_effects_acc
 acc v (tl_nat ops) )"

lemma filter_del_effects_induct :
"filter_del_effects_acc acc v ops = filter_acc 
(\<lambda>op. elemof v (nth_nat (Suc (Suc 0)) op) \<noteq> 0) acc ops "
  apply(induct acc v ops rule:filter_del_effects_acc.induct)
  apply auto
  done

definition filter_del_effects_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"filter_del_effects_tail v ops = reverse_nat (filter_del_effects_acc 0 v ops ) "

lemma subtail_filter_del_effects:
"filter_del_effects_tail v ops = filter_del_effects v ops "
  using filter_del_effects_induct filter_del_effects_tail_def
 subfilter_del_effects subtail_filter by presburger
   
fun map_transition :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_transition t ops xs = (if xs =0 then 0 else 
(1 ## (1 ## t  ## (index_nat ops (hd_nat xs)) ## 0) ## 0) ## map_transition t ops (tl_nat xs)
  )"

fun map_transition_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_transition_acc acc t ops xs = (if xs =0 then acc else map_transition_acc (
(1 ## (1 ## t  ## (index_nat ops (hd_nat xs)) ## 0) ## 0) ## acc) t ops (tl_nat xs)
  )"

lemma map_transition_induct:
"map_transition_acc acc t ops xs = map_acc 
(\<lambda>op. 1 ## (1 ## t  ## (index_nat ops op) ## 0) ## 0) acc xs "
  apply(induct acc t ops xs rule:map_transition_acc.induct)
  apply auto
  done

lemma submap_transition:
"map_transition t ops xs = map_nat (\<lambda>op. 1 ## (1 ## t  ## (index_nat ops op) ## 0) ## 0) xs"
  apply( induct t ops xs rule:map_transition.induct)
  apply auto
  done

definition map_transition_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where 
"map_transition_tail t ops xs = reverse_nat (map_transition_acc 0 t ops xs)"

lemma subtail_map_transition:
"map_transition_tail t ops xs  = map_transition t ops xs "
  using map_transition_induct map_transition_tail_def
 submap_transition subtail_map by presburger

definition  encode_negative_transition_frame_axiom_nat
  :: "nat
    \<Rightarrow> nat
    \<Rightarrow>nat
    \<Rightarrow> nat"
  where "encode_negative_transition_frame_axiom_nat \<Pi> t v
    \<equiv> let vs = nth_nat 0 \<Pi>
        ; ops = nth_nat (Suc 0) \<Pi>
        ; deleting_operators = filter_del_effects v ops
     in   4 ## ( 2 ##(1 ## (0 ## t ## (index_nat vs v) ## 0) ## 0 ) ## 0) ##
          (4 ## (1 ## (0 ## (Suc t) ## (index_nat vs v) ## 0) ## 0 )
          ## (BigOr_nat (map_transition t ops deleting_operators)) ## 0) ## 0"

definition  encode_negative_transition_frame_axiom_tail
  :: "nat
    \<Rightarrow> nat
    \<Rightarrow>nat
    \<Rightarrow> nat"
  where "encode_negative_transition_frame_axiom_tail \<Pi> t v
    \<equiv> let vs = nth_nat 0 \<Pi>
        ; ops = nth_nat (Suc 0) \<Pi>
        ; deleting_operators = filter_del_effects_tail v ops
     in   4 ## ( 2 ##(1 ## (0 ## t ## (index_nat vs v) ## 0) ## 0 ) ## 0) ##
          (4 ## (1 ## (0 ## (Suc t) ## (index_nat vs v) ## 0) ## 0 )
          ## (BigOr_tail (map_transition_tail t ops deleting_operators)) ## 0) ## 0
"
lemma subtail_encode_negative_transition_frame_axiom:
"encode_negative_transition_frame_axiom_tail P t v = encode_negative_transition_frame_axiom_nat P t v"
  using encode_negative_transition_frame_axiom_nat_def
 encode_negative_transition_frame_axiom_tail_def subtail_BigOr
 subtail_filter_del_effects subtail_map_transition by presburger
  
lemma subnat_encode_negative_transition_frame_axiom:
"encode_negative_transition_frame_axiom_nat (strips_list_problem_encode P) t (sas_plus_assignment_encode v) 
= sat_formula_encode (encode_negative_transition_frame_axiom_list P t v)"
  apply (auto simp only:encode_negative_transition_frame_axiom_nat_def  subfilter_del_effects
      strips_list_problem_encode.simps sub_cons cons0
          submap_transition
          sub_nth nth.simps
 )
  using  inj_strips_op inj_sasp
  apply (auto simp only: strips_operator_list_encode_def
sas_plus_assignment_list_encode_def sub_index sub_filter
 Let_def filter_map comp_def sub_elem_of_inj
strips_operator_encode.simps sub_nth nth.simps
sub_map map_map 
      simp flip:  strips_list_problem_encode.simps)
  apply (auto simp only:sub_index simp flip: sas_plus_assignment_list_encode_def
strips_operator_encode.simps sat_variable_encode.simps sat_formula_encode.simps)
  apply (auto simp only: sub_BigOr simp flip: map_map sat_formula_list_encode_def comp_def [of  sat_formula_encode "\<lambda>x. Atom (Operator t (index ((P)\<^sub>\<O>) x))"]
 )
  apply (auto simp only:encode_negative_transition_frame_axiom_list_def Let_def

 simp flip:  sat_formula_encode.simps)
  apply (metis (no_types, lifting) ListMem_iff filter_cong)
  done

definition  encode_positive_transition_frame_axiom_list
  :: "'variable strips_list_problem
    \<Rightarrow> nat
    \<Rightarrow> 'variable
    \<Rightarrow> sat_plan_variable formula"
  where "encode_positive_transition_frame_axiom_list \<Pi> t v
    \<equiv> let vs = variables_of \<Pi>
        ; ops = operators_of \<Pi>
        ; adding_operators = filter (\<lambda>op. ListMem v (add_effects_of op)) ops
      in (Atom (State t (index vs v))
          \<^bold>\<or> (\<^bold>\<not>(Atom (State (Suc t) (index vs v)))
          \<^bold>\<or> \<^bold>\<Or>(map (\<lambda>op. Atom (Operator t (index ops op))) adding_operators)))"

lemma sublist_encode_positive_transition_frame_axiom:
"encode_positive_transition_frame_axiom_list \<Pi> t v = 
encode_positive_transition_frame_axiom (strips_list_problem_to_problem \<Pi>) t v"
  apply (auto simp add:encode_positive_transition_frame_axiom_list_def
encode_positive_transition_frame_axiom_def) done

fun filter_add_effects :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"filter_add_effects v ops = (if ops = 0 then 0 else if 
elemof v (nth_nat (Suc 0) (hd_nat ops)) \<noteq> 0 then 
(hd_nat ops) ## filter_add_effects v (tl_nat ops) else  filter_add_effects v (tl_nat ops) )"

fun filter_add_effects_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"filter_add_effects_acc acc v ops = (if ops = 0 then acc else if  
elemof v (nth_nat (Suc 0) (hd_nat ops)) \<noteq> 0 then  filter_add_effects_acc (
(hd_nat ops) ## acc) v (tl_nat ops) else  filter_add_effects_acc acc v (tl_nat ops) )"

lemma filter_add_effects_induct: 
"filter_add_effects_acc acc v ops = filter_acc  (\<lambda>op. elemof v (nth_nat (Suc 0) op) \<noteq> 0) acc ops  "
  apply(induct acc v ops rule:filter_add_effects_acc.induct)
  apply auto
  done

lemma subfilter_add_effects:
"filter_add_effects v ops = filter_nat (\<lambda>op. elemof v (nth_nat (Suc 0) op) \<noteq> 0) ops "
  apply(induct v ops rule:filter_add_effects.induct)
  apply auto
  done

definition filter_add_effects_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"filter_add_effects_tail v ops  = reverse_nat (filter_add_effects_acc 0 v ops)"

lemma subtail_filter_add_effects:
"filter_add_effects_tail v ops = filter_add_effects v ops"
  using filter_add_effects_induct filter_add_effects_tail_def 
subfilter_add_effects subtail_filter by presburger

definition  encode_positive_transition_frame_axiom_nat
  :: "nat
    \<Rightarrow> nat
    \<Rightarrow> nat
    \<Rightarrow> nat"
  where "encode_positive_transition_frame_axiom_nat \<Pi> t v
    \<equiv> let vs = nth_nat 0 \<Pi>
        ; ops = nth_nat (Suc 0) \<Pi>
        ; adding_operators = filter_add_effects v ops
      in  4 ## (1 ## (0 ## t ## (index_nat vs v) ## 0) ## 0 ) ##
          (4 ## (2 ## (1 ## (0 ## (Suc t) ## (index_nat vs v) ## 0) ## 0 ) ## 0)
          ## (BigOr_nat (map_transition t ops adding_operators)) ## 0) ## 0"

definition  encode_positive_transition_frame_axiom_tail
  :: "nat
    \<Rightarrow> nat
    \<Rightarrow> nat
    \<Rightarrow> nat"
  where "encode_positive_transition_frame_axiom_tail \<Pi> t v
    \<equiv> let vs = nth_nat 0 \<Pi>
        ; ops = nth_nat (Suc 0) \<Pi>
        ; adding_operators = filter_add_effects_tail v ops
      in  4 ## (1 ## (0 ## t ## (index_nat vs v) ## 0) ## 0 ) ##
          (4 ## (2 ## (1 ## (0 ## (Suc t) ## (index_nat vs v) ## 0) ## 0 ) ## 0)
          ## (BigOr_tail (map_transition_tail t ops adding_operators)) ## 0) ## 0"

lemma subtail_encode_positive_transition_frame_axiom:
"encode_positive_transition_frame_axiom_tail P t v = encode_positive_transition_frame_axiom_nat P t v"
  using encode_positive_transition_frame_axiom_nat_def
 encode_positive_transition_frame_axiom_tail_def subtail_BigOr
 subtail_filter_add_effects subtail_map_transition by presburger


lemma subnat_encode_positive_transition_frame_axiom:
"encode_positive_transition_frame_axiom_nat (strips_list_problem_encode P) t (sas_plus_assignment_encode v) 
= sat_formula_encode (encode_positive_transition_frame_axiom_list P t v)"
  apply (auto simp only:encode_positive_transition_frame_axiom_nat_def
      strips_list_problem_encode.simps sub_cons cons0
          sub_nth nth.simps submap_transition subfilter_add_effects
 )
  using  inj_strips_op inj_sasp
  apply (auto simp only: strips_operator_list_encode_def
sas_plus_assignment_list_encode_def sub_index sub_filter
 Let_def filter_map comp_def sub_elem_of_inj
strips_operator_encode.simps sub_nth nth.simps
sub_map map_map 
      simp flip:  strips_list_problem_encode.simps)
  apply (auto simp only:sub_index simp flip: sas_plus_assignment_list_encode_def
strips_operator_encode.simps sat_variable_encode.simps sat_formula_encode.simps)
  apply (auto simp only: sub_BigOr simp flip: map_map sat_formula_list_encode_def comp_def [of  sat_formula_encode "\<lambda>x. Atom (Operator t (index ((P)\<^sub>\<O>) x))"]
 )
  apply (auto simp only:encode_positive_transition_frame_axiom_list_def Let_def

 simp flip:  sat_formula_encode.simps)
  apply (metis (no_types, lifting) ListMem_iff filter_cong)
  done

definition encode_all_frame_axioms_list
  :: "'variable strips_list_problem \<Rightarrow> nat \<Rightarrow> sat_plan_variable formula"
  where "encode_all_frame_axioms_list \<Pi> t
    \<equiv> let l = List.product [0..<t] (variables_of \<Pi>)
      in \<^bold>\<And>(map (\<lambda>(k, v). encode_negative_transition_frame_axiom_list \<Pi> k v) l
            @ map (\<lambda>(k, v). encode_positive_transition_frame_axiom_list \<Pi> k v) l)"

lemma sublist_encode_all_frame_axioms:
" encode_all_frame_axioms_list \<Pi> t =
encode_all_frame_axioms (strips_list_problem_to_problem \<Pi>) t"
  apply (auto simp only: encode_all_frame_axioms_list_def 
encode_all_frame_axioms_def sublist_encode_negative_transition_frame_axiom
sublist_encode_positive_transition_frame_axiom
strips_list_problem_to_problem.simps
strips_list_problem.simps
strips_problem.simps
Let_def) done

fun map_encode_negative ::"nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_encode_negative P xs = (if xs = 0 then 0 else 
( encode_negative_transition_frame_axiom_nat P (fst_nat (hd_nat xs)) (snd_nat (hd_nat xs)))##
map_encode_negative P (tl_nat xs)
)"

lemma submap_encode_negative:
"map_encode_negative P xs =map_nat (\<lambda>n. encode_negative_transition_frame_axiom_nat P (fst_nat n) (snd_nat n)) xs "
  apply (induct P xs rule:map_encode_negative.induct)
  apply auto
  done

fun map_encode_negative_acc ::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_encode_negative_acc acc P xs = (if xs = 0 then acc else  map_encode_negative_acc (
( encode_negative_transition_frame_axiom_tail P (fst_nat (hd_nat xs)) (snd_nat (hd_nat xs)))##
acc) P (tl_nat xs)
)"

lemma  map_encode_negative_induct : 
"map_encode_negative_acc acc P xs = map_acc (\<lambda>n. encode_negative_transition_frame_axiom_nat P (fst_nat n) (snd_nat n)) acc  xs "
  apply(induct acc P xs rule:map_encode_negative_acc.induct)
  apply (auto simp add:subtail_encode_negative_transition_frame_axiom)
  done


definition map_encode_negative_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"map_encode_negative_tail P xs = reverse_nat ( map_encode_negative_acc 0 P xs)"

lemma subtail_map_encode_negative:
"map_encode_negative_tail P xs = map_encode_negative P xs"
  using map_encode_negative_induct map_encode_negative_tail_def
 submap_encode_negative subtail_map by presburger

fun map_encode_positive ::"nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_encode_positive P xs = (if xs = 0 then 0 else 
( encode_positive_transition_frame_axiom_nat P (fst_nat (hd_nat xs)) (snd_nat (hd_nat xs)))##
map_encode_positive P (tl_nat xs)
)"

lemma submap_encode_positive:
"map_encode_positive P xs =map_nat (\<lambda>n. encode_positive_transition_frame_axiom_nat P (fst_nat n) (snd_nat n)) xs "
  apply (induct P xs rule:map_encode_positive.induct)
  apply auto
  done

fun map_encode_positive_acc ::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_encode_positive_acc acc P xs = (if xs = 0 then acc else  map_encode_positive_acc (
( encode_positive_transition_frame_axiom_tail P (fst_nat (hd_nat xs)) (snd_nat (hd_nat xs)))##
acc) P (tl_nat xs)
)"

lemma  map_encode_positive_induct : 
"map_encode_positive_acc acc P xs = map_acc (\<lambda>n. encode_positive_transition_frame_axiom_nat P (fst_nat n) (snd_nat n)) acc  xs "
  apply(induct acc P xs rule:map_encode_positive_acc.induct)
  apply (auto simp add:subtail_encode_positive_transition_frame_axiom)
  done


definition map_encode_positive_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"map_encode_positive_tail P xs = reverse_nat ( map_encode_positive_acc 0 P xs)"

lemma subtail_map_encode_positive:
"map_encode_positive_tail P xs = map_encode_positive P xs"
  using map_encode_positive_induct map_encode_positive_tail_def
 submap_encode_positive subtail_map by presburger


definition encode_all_frame_axioms_nat
  :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "encode_all_frame_axioms_nat \<Pi> t
    \<equiv> let l = product_nat (list_less_nat t) (nth_nat 0 \<Pi>)
      in BigAnd_nat ( append_nat (map_encode_negative \<Pi> l)
            (map_encode_positive \<Pi> l))"

definition encode_all_frame_axioms_tail
  :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "encode_all_frame_axioms_tail \<Pi> t
    \<equiv> let l = product_tail (list_less_tail t) (nth_nat 0 \<Pi>)
      in BigAnd_tail ( append_tail (map_encode_negative_tail \<Pi> l)
            (map_encode_positive_tail \<Pi> l))"

lemma subtail_encode_all_frame_axioms:
"encode_all_frame_axioms_tail \<Pi> t = encode_all_frame_axioms_nat \<Pi> t"
  using encode_all_frame_axioms_nat_def encode_all_frame_axioms_tail_def
 subtail_BigAnd subtail_append subtail_list_less subtail_map_encode_negative 
subtail_map_encode_positive subtail_product by presburger

thm "prod.case_eq_if"
lemma subnat_encode_all_frame_axioms:
"encode_all_frame_axioms_nat (strips_list_problem_encode P) t =
sat_formula_encode (encode_all_frame_axioms_list P t)"
  apply (auto simp only: encode_all_frame_axioms_nat_def submap_encode_negative 
submap_encode_positive 
strips_list_problem_encode.simps sub_nth nth.simps)
  apply (auto simp only: sas_plus_assignment_list_encode_def sub_list_less
          simp flip: strips_list_problem_encode.simps)
  using list.map_id [of "[0..<t]" ] sub_product[of id  "[0..<t]" sas_plus_assignment_encode  "(P)\<^sub>\<V>" ]
  apply (auto simp only: Let_def sub_map map_map comp_def
      prod.case_eq_if sub_fst sub_snd fst_conv snd_conv id_def
      subnat_encode_positive_transition_frame_axiom
       subnat_encode_negative_transition_frame_axiom sub_append
 simp flip: strips_list_problem_encode.simps sas_plus_assignment_list_encode_def)
  apply (auto simp only: case_prod_beta'
encode_all_frame_axioms_list_def Let_def
sub_BigAnd simp flip: sat_formula_list_encode_def map_append  map_map comp_def[of sat_formula_encode "\<lambda>x. encode_negative_transition_frame_axiom_list P (fst x) (snd x)"]
 comp_def[of sat_formula_encode "\<lambda>x. encode_positive_transition_frame_axiom_list P (fst x) (snd x)"]
)
  done

definition  encode_problem_list:: "'variable strips_list_problem \<Rightarrow> nat \<Rightarrow> sat_plan_formula"
  where "encode_problem_list \<Pi> t
    \<equiv> encode_initial_state_list \<Pi>
      \<^bold>\<and> (encode_operators_list \<Pi> t
      \<^bold>\<and> (encode_all_frame_axioms_list \<Pi> t
      \<^bold>\<and> (encode_goal_state_list \<Pi> t)))"

lemma sublist_encode_problem : 
"encode_problem_list \<Pi> t = encode_problem (strips_list_problem_to_problem \<Pi>) t"
  apply (auto simp add: encode_problem_list_def encode_problem_def
      sublist_encode_initial_state sublist_encode_operators sublist_encode_all_frame_axioms
          sublist_encode_goal_state)
  done

definition  encode_problem_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "encode_problem_nat \<Pi> t
    \<equiv> 3 ## (encode_initial_state_nat \<Pi>) ## 
      ( 3 ## (encode_operators_nat \<Pi> t)
        ## (3 ##(encode_all_frame_axioms_nat \<Pi> t)
     ## (encode_goal_state_nat \<Pi> t) ## 0) ## 0) ## 0"

definition  encode_problem_tail:: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "encode_problem_tail \<Pi> t
    \<equiv> 3 ## (encode_initial_state_tail \<Pi>) ## 
      ( 3 ## (encode_operators_tail \<Pi> t)
        ## (3 ##(encode_all_frame_axioms_tail \<Pi> t)
     ## (encode_goal_state_tail \<Pi> t) ## 0) ## 0) ## 0"

lemma subtail_encode_problem:
"encode_problem_tail \<Pi> t = encode_problem_nat \<Pi> t"
  by (simp add: encode_problem_nat_def encode_problem_tail_def subtail_encode_all_frame_axioms 
subtail_encode_goal_state subtail_encode_initial_state subtail_encode_operators)

lemma subnat_encode_problem:
"encode_problem_nat (strips_list_problem_encode P) t
= sat_formula_encode (encode_problem_list P t)"
  apply (auto simp only: encode_problem_nat_def encode_problem_list_def sub_cons cons0 
subnat_encode_initial_state
  subnat_encode_operators
subnat_encode_all_frame_axioms
subnat_encode_goal_state
simp flip: sat_formula_encode.simps )
  done

end