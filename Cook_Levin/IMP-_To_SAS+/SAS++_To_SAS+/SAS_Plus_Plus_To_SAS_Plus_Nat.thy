theory SAS_Plus_Plus_To_SAS_Plus_Nat
  imports   Primitives SAS_Plus_Plus_To_SAS_Plus
begin

definition SAS_Plus_Plus_State_To_SAS_Plus_list:: 
  "(dom \<times> (variable,domain_element) assignment list) \<Rightarrow> 
        (var,dom) assignment list" where
"SAS_Plus_Plus_State_To_SAS_Plus_list is = (Stage, fst is) # 
 map (\<lambda>(x,y). (x,DE y)) (map (\<lambda>(x,y). (Var x, y)) (snd is))"

lemma inj_var: "inj Var"
  by (meson SAS_Plus_Plus_To_SAS_Plus.variable.inject inj_onI)

lemma sublist_SAS_Plus_Plus_State_To_SAS_Plus_apply:
  "map_of (SAS_Plus_Plus_State_To_SAS_Plus_list is) k =
      SAS_Plus_Plus_State_To_SAS_Plus (islist_to_map is) k"
  apply (cases "is")
  apply (cases k)
  apply (auto simp add: SAS_Plus_Plus_State_To_SAS_Plus_list_def  SAS_Plus_Plus_State_To_SAS_Plus_def
        map_comp_def map_of_map simp del:map_map)
  subgoal for a b x
    apply (cases "map_of b x")
     apply auto
    subgoal
    proof -
      assume "k = Var x" "map_of b x = None"
      hence "\<forall>y. (x,y) \<notin> set b"
        using weak_map_of_SomeI by force
      hence "\<forall>y. (Var x, y) \<notin> set (map (\<lambda>(x, y). (Var x, y)) b)"
        by auto
      thus ?thesis
        by (metis (no_types, lifting) imageE map_of_eq_None_iff prod.collapse) 
    qed
    using map_of_mapk_SomeI inj_var by fast
  done

lemma sublist_SAS_Plus_Plus_State_To_SAS_Plus:
  "map_of (SAS_Plus_Plus_State_To_SAS_Plus_list is) =
      SAS_Plus_Plus_State_To_SAS_Plus (islist_to_map is)"
  using sublist_SAS_Plus_Plus_State_To_SAS_Plus_apply by blast

fun map_sasps :: "nat\<Rightarrow>nat" where 
"map_sasps n = (if n = 0 then 0 else (prod_encode (Suc(fst_nat (hd_nat n)) , Suc(Suc(snd_nat (hd_nat n))) ))## map_sasps (tl_nat n))"
fun map_sasps_acc :: "nat \<Rightarrow> nat\<Rightarrow>nat" where 
"map_sasps_acc acc n = (if n = 0 then acc else map_sasps_acc ((prod_encode (Suc(fst_nat (hd_nat n)) , Suc(Suc(snd_nat (hd_nat n))) ))## acc) (tl_nat n))"


lemma submap_sasps:
 "map_sasps  n = map_nat (\<lambda>x. prod_encode (Suc(fst_nat x) , Suc(Suc(snd_nat x)) )) n"
  apply (induct n rule:map_sasps.induct)
  apply auto
  done

lemma map_sasps_induct:
"map_sasps_acc acc n = map_acc  (\<lambda>x. prod_encode (Suc(fst_nat x) , Suc(Suc(snd_nat x)) )) acc n "
  apply(induct acc n rule:map_sasps_acc.induct)
  apply auto
  done

definition map_sasps_tail :: "nat \<Rightarrow> nat" where 
"map_sasps_tail n = reverse_nat (map_sasps_acc 0 n)"

lemma subtail_map_sasps:
"map_sasps_tail n = map_sasps n"
  using map_sasps_tail_def  map_sasps_induct submap_sasps subtail_map
  by presburger

definition SAS_Plus_Plus_State_To_SAS_Plus_nat :: "nat \<Rightarrow> nat" where
"SAS_Plus_Plus_State_To_SAS_Plus_nat is = (prod_encode (0,fst_nat is))##
(map_sasps (snd_nat is))"

definition SAS_Plus_Plus_State_To_SAS_Plus_tail:: "nat \<Rightarrow> nat" where
"SAS_Plus_Plus_State_To_SAS_Plus_tail is = (prod_encode (0,fst_nat is))##
(map_sasps_tail (snd_nat is))"

lemma subtail_SAS_Plus_Plus_State_To_SAS_Plus:
"SAS_Plus_Plus_State_To_SAS_Plus_tail is = SAS_Plus_Plus_State_To_SAS_Plus_nat is"
  apply(auto simp only: SAS_Plus_Plus_State_To_SAS_Plus_tail_def
SAS_Plus_Plus_State_To_SAS_Plus_nat_def
subtail_map_sasps)
  done

lemma subnat_SAS_Plus_Plus_State_To_SAS_Plus:
"SAS_Plus_Plus_State_To_SAS_Plus_nat(islist_encode is) =
    sas_plus_assignment_list_encode (SAS_Plus_Plus_State_To_SAS_Plus_list is)"
  apply (cases "is")
  apply (auto simp only:sas_plus_assignment_list_encode_def)
  apply (auto simp only: islist_encode.simps sas_assignment_list_encode_def
      SAS_Plus_Plus_State_To_SAS_Plus_nat_def sub_cons cons0 sub_map sub_snd
                snd_def sub_fst fst_def map_map comp_def sas_assignment_encode.simps 
                   SAS_Plus_Plus_State_To_SAS_Plus_list_def list.map
                          list_encode_eq submap_sasps
                  simp flip: var_encode.simps dom_encode.simps
                            sas_plus_assignment_encode.simps)
  apply(auto simp add: prod_encode_eq sub_fst sub_snd sas_plus_assignment_list_encode_def comp_def
          Case_def)
  done

lemma sub_SAS_Plus_Plus_State_To_SAS_Plus: 
      "sas_plus_state_decode (SAS_Plus_Plus_State_To_SAS_Plus_nat(islist_encode is))
        = SAS_Plus_Plus_State_To_SAS_Plus (islist_to_map is)"
  using subnat_SAS_Plus_Plus_State_To_SAS_Plus sublist_SAS_Plus_Plus_State_To_SAS_Plus
  by (simp add: sas_plus_assignment_list_id sas_plus_state_decode_def)

fun map_var_de :: "nat \<Rightarrow> nat" where 
"map_var_de n = (if n = 0 then 0 else (prod_encode(Suc (fst_nat (hd_nat n)), Suc (Suc(snd_nat (hd_nat n)))))## map_var_de (tl_nat n) )"

fun map_var_de_acc :: " nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_var_de_acc acc n = (if n = 0 then acc else  map_var_de_acc
((prod_encode(Suc (fst_nat (hd_nat n)), Suc (Suc(snd_nat (hd_nat n)))))## acc) (tl_nat n) )"

lemma submap_var_de :
"map_var_de n = map_nat (\<lambda> x. prod_encode(Suc (fst_nat x), Suc (Suc(snd_nat x)))) n"
  apply (induct n rule: map_var_de.induct)
  apply auto
  done

lemma map_var_de_induct:
"map_var_de_acc acc n = map_acc  (\<lambda> x. prod_encode(Suc (fst_nat x), Suc (Suc(snd_nat x)))) acc n "
  apply (induct acc n rule: map_var_de_acc.induct)
  apply auto
  done

definition map_var_de_tail :: "nat \<Rightarrow> nat" where 
"map_var_de_tail n = reverse_nat (map_var_de_acc 0 n)"

lemma subtail_map_var_de:
"map_var_de_tail n = map_var_de n"
  using map_var_de_tail_def  submap_var_de  map_var_de_induct 
      subtail_map 
  by presburger
      
definition SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_nat:: 
  "nat \<Rightarrow> nat" where
"SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_nat op = 
  ((prod_encode(0,0)) ## (map_var_de (nth_nat 0 op)))##
   (( map_sasps  (nth_nat (Suc 0) op))) ## 0"

definition SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_tail:: 
  "nat \<Rightarrow> nat" where
"SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_tail op = 
  ((prod_encode(0,0)) ## (map_var_de_tail (nth_nat 0 op)))##
   (( map_sasps_tail  (nth_nat (Suc 0) op))) ## 0"

lemma subtail_SAS_Plus_Plus_Operator_To_SAS_Plus_Operator:
"SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_tail op =  SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_nat op"
  apply(auto simp only: SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_tail_def 
SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_nat_def
subtail_map_sasps
subtail_map_var_de)
  done


lemma fst_sas_assignment : "fst_nat (sas_assignment_encode x) = variable_encode (fst x)"
  apply (cases x)
  apply (auto simp add:sub_fst)
  done
lemma snd_sas_assignment : "snd_nat (sas_assignment_encode x) = domain_element_encode (snd x)"
  apply (cases x)
  apply (auto simp add:sub_snd)
  done

lemma sub_SAS_Plus_Plus_Operator_To_SAS_Plus_Operator:
  "SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_nat (operator_encode op) =
    operator_plus_encode (SAS_Plus_Plus_Operator_To_SAS_Plus_Operator op)"
  apply (auto simp only: submap_var_de
          SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_nat_def 
           operator_encode_def sub_nth nth.simps submap_sasps
              sas_assignment_list_encode_def sub_map sub_cons cons0 map_map comp_def
          SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_def
          operator_plus_encode_def sas_plus_operator.simps
            sas_plus_assignment_list_encode_def list.simps 
            sas_plus_assignment_encode.simps var_encode.simps dom_encode.simps
              fst_sas_assignment snd_sas_assignment
         )
  done


definition initialization_operators_list::
    "(variable, domain_element) sas_plus_list_problem \<Rightarrow> operator_plus list" where
"initialization_operators_list  P = 
  concat (map (\<lambda> v. (if v \<in> set (map fst (initial_ofl P)) then [] 
    else map (\<lambda> y. \<lparr> precondition_of = [(Stage, Init)],  effect_of = [(Var v, DE y)]\<rparr>) 
      (thef (map_list_find (range_ofl P) v)))) (variables_ofl P))"

lemma dom_map_of : "dom (map_of x) = set ( map fst x)"
  apply (induct x)
   apply auto
  apply force
  done

lemma sublist_initialization_operators:
"initialization_operators_list  P = initialization_operators (list_problem_to_problem P)"
  apply (auto simp only:initialization_operators_list_def initialization_operators_def 
          dom_map_of sub_map_list_find[of "range_ofl P"] list_problem_to_problem.simps sas_plus_problem.simps) 
  done

fun map_inner :: "nat \<Rightarrow> nat\<Rightarrow>nat" where 
"map_inner v n = (if n = 0 then 0 else ((((prod_encode (0, 1)))##0) ## ((prod_encode (Suc v, Suc (Suc (hd_nat n))))## 0) ## 0) ## map_inner v (tl_nat n) )"

fun map_inner_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat\<Rightarrow>nat" where 
"map_inner_acc v acc n = (if n = 0 then acc else map_inner_acc v (((((prod_encode (0, 1)))##0) ## ((prod_encode (Suc v, Suc (Suc (hd_nat n))))## 0) ## 0) ## acc) (tl_nat n) )"

lemma submap_inner:
"map_inner v n =  map_nat (\<lambda> y. (((prod_encode (0, 1)))##0) ## ((prod_encode (Suc v, Suc (Suc y)))## 0) ## 0) n"
  apply (induct v n rule:map_inner.induct)
  apply auto
  done

lemma map_inner_induct:
"map_inner_acc v acc n = map_acc (\<lambda> y. (((prod_encode (0, 1)))##0) ## ((prod_encode (Suc v, Suc (Suc y)))## 0) ## 0) acc n "
  apply(induct v acc n rule:map_inner_acc.induct)
  apply auto
  done

definition map_inner_tail ::"nat \<Rightarrow> nat \<Rightarrow> nat" where
 "map_inner_tail v n = reverse_nat ( map_inner_acc v 0 n)"

lemma subtail_map_inner:
"map_inner_tail v n = map_inner v n"
  using map_inner_tail_def  map_inner_induct submap_inner
        subtail_map by presburger



fun map_fst :: "nat\<Rightarrow>nat" where 
"map_fst n  = (if n =0 then 0 else (fst_nat (hd_nat n)) ## map_fst (tl_nat n))"

fun map_fst_acc :: "nat \<Rightarrow> nat\<Rightarrow>nat" where 
"map_fst_acc acc n  = (if n =0 then acc else map_fst_acc ((fst_nat (hd_nat n)) ## acc) (tl_nat n))"


lemma submap_fst :
"map_fst n = map_nat fst_nat n"
  apply (induct n rule:map_fst.induct)
  apply auto
  done
lemma map_fst_induct:
"map_fst_acc acc n = map_acc fst_nat acc n"
  apply(induct acc n rule:map_fst_acc.induct)
  apply auto
  done

definition map_fst_tail :: "nat \<Rightarrow> nat" where 
"map_fst_tail n = reverse_nat (map_fst_acc 0 n)"

lemma subtail_map_fst :
"map_fst_tail n = map_fst n"
  using map_fst_tail_def map_fst_induct submap_fst subtail_map 
  by presburger

function map_outer :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"map_outer P n = (if n =0 then 0 else (if elemof (hd_nat n) (map_fst (nth_nat (Suc (Suc 0)) P)) \<noteq> 0 then 0 
    else (map_inner (hd_nat n) 
      (the_nat (map_list_find_nat (nth_nat (Suc (Suc (Suc (Suc 0)))) P) (hd_nat n))))) ## map_outer P (tl_nat n))"
   apply pat_completeness
  apply (auto simp only:)
  done
termination by lexicographic_order

lemma submap_outer: 
"map_outer P n = map_nat (\<lambda> v. (if elemof v (map_fst (nth_nat (Suc (Suc 0)) P)) \<noteq> 0 then 0 
    else map_inner v 
      (the_nat (map_list_find_nat (nth_nat (Suc (Suc (Suc (Suc 0)))) P) v)))) n"
  apply (induct P n rule:map_outer.induct)
  by (metis (no_types, lifting) map_nat.elims map_outer.elims)
declare map_list_find_nat.simps elemof.simps [simp del]

function  map_outer_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"map_outer_acc P acc n = (if n =0 then acc else map_outer_acc P ((if elemof (hd_nat n) (map_fst_tail (nth_nat (Suc (Suc 0)) P)) \<noteq> 0 then 0 
    else (map_inner_tail (hd_nat n) 
      (the_nat (map_list_find_nat (nth_nat (Suc (Suc (Suc (Suc 0)))) P) (hd_nat n))))) ## acc) (tl_nat n))"
  apply pat_completeness
  apply (auto simp only:)
  done
termination by lexicographic_order

lemma map_outer_induct : 
"map_outer_acc P acc n = map_acc (\<lambda> v. (if elemof v (map_fst (nth_nat (Suc (Suc 0)) P)) \<noteq> 0 then 0 
    else map_inner v 
      (the_nat (map_list_find_nat (nth_nat (Suc (Suc (Suc (Suc 0)))) P) v)))) acc n"
  apply(induct P acc n rule:map_outer_acc.induct)
  using subtail_map_fst subtail_map_inner 
  by (metis (no_types, lifting) map_acc.elims map_outer_acc.elims)

definition map_outer_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_outer_tail P  n = reverse_nat (map_outer_acc P  0 n)"


lemma subtail_map_outer:
"map_outer_tail P  n  = map_outer P n "
  using map_outer_tail_def  map_outer_induct submap_outer subtail_map
  by presburger


definition initialization_operators_nat::
    "nat \<Rightarrow> nat" where
"initialization_operators_nat  P = 
  concat_nat (map_outer P (nth_nat 0 P))"

definition initialization_operators_tail::
    "nat \<Rightarrow> nat" where
"initialization_operators_tail  P = 
  concat_tail (map_outer_tail P (nth_nat 0 P))"

lemma subtail_initialization_operators:
"initialization_operators_tail  P = 
initialization_operators_nat  P
"
  apply(simp only: initialization_operators_tail_def initialization_operators_nat_def
      subtail_concat subtail_map_outer)
  done

lemma simp_vdlist_encode: "vdlist_encode = prod_encode o (\<lambda>(x,y). (variable_encode x,list_encode (map domain_element_encode y)))"
  by force

lemma simp_sas_assignment_encode: "sas_assignment_encode = prod_encode o (\<lambda>(x,y). (variable_encode x,domain_element_encode y))"
  by force

lemma map_find_map:"inj f \<Longrightarrow> map_list_find  (map (\<lambda>(x, y). (f x, g (h y))) l) (f x) = 
       (case map_list_find l x of None \<Rightarrow> None | Some y \<Rightarrow> Some (g (h y)))"
  apply (induct l arbitrary:x)
   apply (auto simp add:inj_def)
  done

lemma map_find_map2:"inj f \<Longrightarrow> map_list_find  (map (\<lambda>(x, y). (f x, g y)) l) (f x) = 
       (case map_list_find l x of None \<Rightarrow> None | Some y \<Rightarrow> Some (g  y))"
  apply (rule  map_find_map) apply auto
  done

lemma inj_map_set: "inj f \<Longrightarrow> (f x \<in> set (map f xs)) = ( x \<in> set xs)"
  apply (auto simp add:inj_def)
  done

lemma sub_the_dec: "thef x  = list_decode (the_nat (list_option_encode x))"
  apply (auto simp only: sub_the list_encode_inverse)
  done

lemma sub_thedec_spec: "thef (map_list_find (range_ofl P) x) =
list_decode (the_nat (list_option_encode (map_list_find (range_ofl P) x)))
"
  using sub_the_dec by blast

lemma thef_simps: "thef xs  = (case xs of None \<Rightarrow> [] | Some x \<Rightarrow> x)"
  apply (cases xs)
   apply (auto)
  done

lemma map_nat0:"map_nat f 0 = 0"
  by auto
thm "option.case_distrib"
lemma subnat_initialization_operators:
 "initialization_operators_nat (list_problem_encode P)
  =  list_encode (map operator_plus_encode  (initialization_operators_list P)) "
  apply (auto simp only: initialization_operators_nat_def list_problem_encode_def
                sas_plus_list_problem.simps sub_nth nth.simps sas_assignment_list_encode_def submap_fst
                      submap_inner submap_outer
                          sub_map map_map comp_def fst_sas_assignment sub_elem_of cons0 sub_cons sub_the sub_map_list_find_nat
                          )
  apply (auto simp only:  simp_vdlist_encode sub_map_list_find_nat sub_the 
      initialization_operators_list_def )
  apply (auto simp only: map_map comp_def)
  apply (simp only: flip: comp_def[of variable_encode fst] map_map)

  using variable_inj   apply (auto simp only:  map_find_map inj_map_set if_distrib
          list_encode.simps(1) list.simps)
  apply (auto simp only: sub_map_list_find_nat map_find_map
operator_plus_encode_def map_concat

 simp flip: comp_def[of "prod_encode" "\<lambda>x.(case x of
 (x, y) \<Rightarrow> (variable_encode x, list_encode (map domain_element_encode y)))"] map_map
)
  apply (auto simp only: map_map comp_def if_distrib list.simps operator_plus_encode_def
            sas_plus_operator.simps sas_plus_assignment_list_encode_def
            sas_plus_assignment_encode.simps option.case_distrib thefn.simps option_encode.simps
the_nat.simps zero_diff diff_Suc_1 sub_map map_nat0 if_cancel
 )
  apply (auto simp only: simp flip: list_encode.simps if_distrib  option.case_distrib[of list_encode]
       )
  apply (auto simp only: list_encode.simps ) 
  apply (auto simp only: sub_concat thef_simps simp flip: comp_def[of list_encode "(\<lambda>x. case map_list_find (range_ofl P) x of None \<Rightarrow> []
                    | Some xa \<Rightarrow>
                        if x \<in> set (map fst (initial_ofl P)) then []
                        else map (\<lambda>xa. Suc (prod_encode
    (Suc (prod_encode (prod_encode (0, 1), 0)),
     Suc (prod_encode
           (Suc (prod_encode
                  (prod_encode
                    (Suc (variable_encode x),
                     Suc (Suc (domain_element_encode xa))),
                   0)),
            0)))))
                              xa)"] map_map ) 
  apply (simp only:One_nat_def)
  apply (auto simp only:option.case_distrib list.simps if_cancel var_encode.simps dom_encode.simps)
  done

fun map_init_seq :: "nat \<Rightarrow> nat" where 
"map_init_seq n = (if n = 0 then 0 else ((((prod_encode (0,1))##0) ## 
      ((prod_encode(Suc (fst_nat (hd_nat n)), Suc (Suc (snd_nat (hd_nat n)))))##0) ##0)) ## map_init_seq (tl_nat n))"

fun map_init_seq_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_init_seq_acc  acc n = (if n = 0 then acc else map_init_seq_acc (((((prod_encode (0,1))##0) ## 
      ((prod_encode(Suc (fst_nat (hd_nat n)), Suc (Suc (snd_nat (hd_nat n)))))##0) ##0)) ## acc) (tl_nat n))"

lemma submap_init_seq: 
"map_init_seq n = map_nat (\<lambda>v. (((prod_encode (0,1))##0) ## 
      ((prod_encode(Suc (fst_nat v), Suc (Suc (snd_nat v))))##0) ##0)) n"
  apply (induct n rule:map_init_seq.induct)
  apply auto
  done

lemma map_init_seq_induct:
"map_init_seq_acc  acc n = map_acc  (\<lambda>v. (((prod_encode (0,1))##0) ## 
      ((prod_encode(Suc (fst_nat v), Suc (Suc (snd_nat v))))##0) ##0)) acc n"
  apply(induct acc n rule:map_init_seq_acc.induct)
  apply auto
  done

definition map_init_seq_tail :: "nat \<Rightarrow> nat" where 
"map_init_seq_tail n = reverse_nat (map_init_seq_acc 0 n) "

lemma subtail_map_init_seq:
"map_init_seq_tail n = map_init_seq n"
  using map_init_seq_tail_def map_init_seq_induct
submap_init_seq subtail_map by presburger

definition initialization_sequence_nat:: "nat \<Rightarrow> nat" where
  "initialization_sequence_nat vs = map_init_seq vs"

definition initialization_sequence_tail:: "nat \<Rightarrow> nat" where
  "initialization_sequence_tail vs = map_init_seq_tail vs"

lemma subtail_initialization_sequence:
"initialization_sequence_tail vs = initialization_sequence_nat vs"
  using initialization_sequence_nat_def
 initialization_sequence_tail_def
 subtail_map_init_seq by presburger


lemma sub_initialization_sequence :
  "initialization_sequence_nat (sas_assignment_list_encode vs) =
      list_encode (map operator_plus_encode (initialization_sequence vs)) "
  apply (auto simp only: submap_init_seq initialization_sequence_nat_def cons0
              sub_cons sas_assignment_list_encode_def sub_map map_map comp_def
                fst_sas_assignment snd_sas_assignment)
  apply (auto simp only: initialization_sequence_def map_map comp_def
                    sas_plus_assignment_list_encode_def
              operator_plus_encode_def sas_plus_operator.simps simp flip: var_encode.simps 
                    dom_encode.simps sas_plus_assignment_encode.simps)
  apply auto
  done



definition initial_state_list:: 
  "(variable, domain_element) sas_plus_list_problem \<Rightarrow> (var, dom) assignment list" where
"initial_state_list P = SAS_Plus_Plus_State_To_SAS_Plus_list (Init, 
  map (\<lambda>v. (v, case (map_list_find (initial_ofl P) v) of  Some val \<Rightarrow> val |
        None \<Rightarrow> (the (map_list_find (range_ofl P) v)) ! 0 ) ) (variables_ofl P) 
)"

lemma sublist_initial_state_helper_apply: 
" (\<lambda>v. if v \<in> set ((P)\<^sub>\<V>\<^sub>+)
           then Some
                 (case map_of ((P)\<^sub>I\<^sub>+) v of None \<Rightarrow> the (map_of (range_ofl P) v) ! 0
                  | Some val \<Rightarrow> val)
           else None) k = 
 map_of
       (map (\<lambda>v. (v, case map_of ((P)\<^sub>I\<^sub>+) v of
                      None \<Rightarrow> the (map_of (range_ofl P) v) ! 0 | Some val \<Rightarrow> val))
         ((P)\<^sub>\<V>\<^sub>+)) k
"
  apply (auto)
  subgoal
proof -
  assume a1: "k \<in> set ((P)\<^sub>\<V>\<^sub>+)"
  then have "set ((P)\<^sub>\<V>\<^sub>+) \<noteq> {}"
    by force
  then show "Some (case map_of ((P)\<^sub>I\<^sub>+) k of None \<Rightarrow> the (map_of (range_ofl P) k) ! 0 | Some a \<Rightarrow> a) = map_of (map (\<lambda>b. (b, case map_of ((P)\<^sub>I\<^sub>+) b of None \<Rightarrow> the (map_of (range_ofl P) b) ! 0 | Some a \<Rightarrow> a)) ((P)\<^sub>\<V>\<^sub>+)) k"
    using a1 by (simp add: map_of_from_function_graph_is_some_if)
qed
  by (simp add: map_of_map_restrict)

lemma sublist_initial_state_helper:
"(\<lambda>v. if v \<in> set ((P)\<^sub>\<V>\<^sub>+)
           then Some
                 (case map_of ((P)\<^sub>I\<^sub>+) v of None \<Rightarrow> the (map_of (range_ofl P) v) ! 0
                  | Some val \<Rightarrow> val)
           else None)
=  map_of
       (map (\<lambda>v. (v, case map_of ((P)\<^sub>I\<^sub>+) v of
                      None \<Rightarrow> the (map_of (range_ofl P) v) ! 0 | Some val \<Rightarrow> val))
         ((P)\<^sub>\<V>\<^sub>+))
"
  using  sublist_initial_state_helper_apply by fast


lemma sublist_initial_state:
" map_of (initial_state_list P)  = initial_state (list_problem_to_problem P) "
  apply (auto simp only:initial_state_list_def sublist_SAS_Plus_Plus_State_To_SAS_Plus
  islist_to_map.simps map_of_map  sub_map_list_find sublist_initial_state_helper
  initial_state_def list_problem_to_problem.simps sas_plus_problem.simps
)
  done

lemma map_op:"a # xs = x \<Longrightarrow> map f x = f a # map f xs"
  apply auto
  done
declare map_list_find_nat.simps [simp del]
fun map_initial_state :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_initial_state P n = (if n = 0 then 0 else (prod_encode(hd_nat n, case (map_list_find_nat (nth_nat (Suc (Suc 0))  P) (hd_nat n)) of  Suc val \<Rightarrow> val |
        0 \<Rightarrow> hd_nat (the_nat (map_list_find_nat (nth_nat (Suc (Suc (Suc (Suc 0)))) P) (hd_nat n))))) ## map_initial_state P (tl_nat n))"

fun map_initial_state_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>  nat" where 
"map_initial_state_acc P acc n = (if n = 0 then acc else map_initial_state_acc P ((prod_encode(hd_nat n, case (map_list_find_nat (nth_nat (Suc (Suc 0))  P) (hd_nat n)) of  Suc val \<Rightarrow> val |
        0 \<Rightarrow> hd_nat (the_nat (map_list_find_nat (nth_nat (Suc (Suc (Suc (Suc 0)))) P) (hd_nat n))))) ## acc )(tl_nat n))"

lemma submap_initial_state:
"map_initial_state P n  =  map_nat (\<lambda>v. prod_encode(v, case (map_list_find_nat (nth_nat (Suc (Suc 0))  P) v) of  Suc val \<Rightarrow> val |
        0 \<Rightarrow> hd_nat (the_nat (map_list_find_nat (nth_nat (Suc (Suc (Suc (Suc 0)))) P) v))) ) n "
  apply (induct P n rule:map_initial_state.induct)
  apply auto
  done

lemma map_initial_state_induct: 
"map_initial_state_acc P acc n = map_acc  (\<lambda>v. prod_encode(v, case (map_list_find_nat (nth_nat (Suc (Suc 0))  P) v) of  Suc val \<Rightarrow> val |
        0 \<Rightarrow> hd_nat (the_nat (map_list_find_nat (nth_nat (Suc (Suc (Suc (Suc 0)))) P) v))) ) acc n "
  apply(induct P acc n rule:map_initial_state_acc.induct)
  apply auto
  done

definition map_initial_state_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_initial_state_tail P n = reverse_nat (map_initial_state_acc P 0 n)"

lemma subtail_map_initial_state:
" map_initial_state_tail P n = map_initial_state P n"
  using  map_initial_state_tail_def  map_initial_state_induct submap_initial_state
subtail_map by presburger

declare map_list_find_nat.simps [simp]



definition initial_state_nat::
  "nat \<Rightarrow> nat " where
"initial_state_nat P = SAS_Plus_Plus_State_To_SAS_Plus_nat (prod_encode(1, 
  map_initial_state P (nth_nat 0 P) 
))"


definition initial_state_tail::
  "nat \<Rightarrow> nat " where
"initial_state_tail P = SAS_Plus_Plus_State_To_SAS_Plus_tail (prod_encode(1, 
  map_initial_state_tail P (nth_nat 0 P) 
))"

lemma subtail_initial_state:
"initial_state_tail P = initial_state_nat P"

  using initial_state_nat_def initial_state_tail_def subtail_SAS_Plus_Plus_State_To_SAS_Plus 
subtail_map_initial_state by presburger

lemma option_encode_case: "(case option_encode x of 0 \<Rightarrow>  t | Suc y \<Rightarrow> f y) =
 (case x of None \<Rightarrow> t | Some y \<Rightarrow> f y)  "
  apply (cases x)
   apply auto
  done

lemma some_case_unfold: "f a = Some y \<Longrightarrow> (case f a of None \<Rightarrow> None | Some t \<Rightarrow> Some (g t)) = Some (g y)"
  apply auto
  done


lemma lambda_case_simplifier:
assumes  "\<forall>x \<in> set (variables_ofl P). \<exists>t. map_list_find (range_ofl P) x = Some t \<and> t\<noteq>[]"
shows
" map (\<lambda>x. case map_list_find ((P)\<^sub>I\<^sub>+) x of
                    None \<Rightarrow>
                      prod_encode
                       (variable_encode x,
                        hd_nat
                         (the_nat
                           (option_encode
                             (case map_list_find (range_ofl P) x of None \<Rightarrow> None
                              | Some y \<Rightarrow>
                                  Some
                                   (list_encode (map domain_element_encode y))))))
                    | Some xa \<Rightarrow>
                        prod_encode (variable_encode x, domain_element_encode xa))
           ((P)\<^sub>\<V>\<^sub>+) = 
 map (\<lambda>x. case map_list_find ((P)\<^sub>I\<^sub>+) x of
                    None \<Rightarrow>
                      prod_encode
                       (variable_encode x,
                        hd_nat
                         (the_nat
                           (option_encode
                             (Some
                                   (list_encode (map domain_element_encode  (the (map_list_find (range_ofl P) x) )))))))
                    | Some xa \<Rightarrow>
                        prod_encode (variable_encode x, domain_element_encode xa))
           ((P)\<^sub>\<V>\<^sub>+)
"
 using assms
  apply (induct "((P)\<^sub>\<V>\<^sub>+)" arbitrary: P )
   apply (simp add:  initial_state_list_def 
  sas_assignment_list_encode_def 
 flip:  subnat_SAS_Plus_Plus_State_To_SAS_Plus list_encode.simps(2))
 subgoal for a x P
    apply (auto simp add:eq_commute simp flip: list_encode.simps(2))
    apply (cases "map_list_find (range_ofl P) a ")
     apply simp
   subgoal for t aa
 apply (auto simp only:some_case_unfold option.case  option.the_def sub_thefn thefn.simps sub_hd
              simp flip: sas_assignment_encode.simps )
     done
   subgoal for t aa
     apply (metis (no_types, lifting) option.case_eq_if thef.simps(1) thef.simps(2))
     done
   done
  done

     
lemma lambda_case_simplifier2:
assumes  "\<forall>x \<in> set (variables_ofl P). \<exists>t. map_list_find (range_ofl P) x = Some t \<and> t\<noteq>[]"
shows
"map (\<lambda>x. case map_list_find ((P)\<^sub>I\<^sub>+) x of
                    None \<Rightarrow>
                      prod_encode
                       (variable_encode x,
                        head
                         (map domain_element_encode
                           (the (map_list_find (range_ofl P) x))))
                    | Some xa \<Rightarrow>
                        prod_encode (variable_encode x, domain_element_encode xa))
           ((P)\<^sub>\<V>\<^sub>+)
=
map (\<lambda>x. case map_list_find ((P)\<^sub>I\<^sub>+) x of
                    None \<Rightarrow>
                      prod_encode
                       (variable_encode x,
                        domain_element_encode (hd (
                           (the (map_list_find (range_ofl P) x)))))
                    | Some xa \<Rightarrow>
                        prod_encode (variable_encode x, domain_element_encode xa))
           ((P)\<^sub>\<V>\<^sub>+)

"
 using assms
  apply (induct "((P)\<^sub>\<V>\<^sub>+)" arbitrary: P )
  apply auto
  subgoal for a x P xa 
    apply (cases "map_list_find (range_ofl P) xa")
     apply auto
    subgoal for aa
      apply (metis option.sel sub_head_map)
      done
    done
  done
lemma lambda_case_simplifier3:
assumes  "\<forall>x \<in> set (variables_ofl P). \<exists>t. map_list_find (range_ofl P) x = Some t \<and> t\<noteq>[]"
shows
"map (\<lambda>x. case map_list_find ((P)\<^sub>I\<^sub>+) x of
                    None \<Rightarrow>
                      prod_encode
                       (variable_encode x,
                        domain_element_encode (hd (
                           (the (map_list_find (range_ofl P) x)))))
                    | Some xa \<Rightarrow>
                        prod_encode (variable_encode x, domain_element_encode xa))
           ((P)\<^sub>\<V>\<^sub>+)

=

map (\<lambda>x. case map_list_find ((P)\<^sub>I\<^sub>+) x of
                    None \<Rightarrow>
                      prod_encode
                       (variable_encode x,
                        domain_element_encode (
                           (the (map_list_find (range_ofl P) x))!0))
                    | Some xa \<Rightarrow>
                        prod_encode (variable_encode x, domain_element_encode xa))
           ((P)\<^sub>\<V>\<^sub>+)

"
 using assms
  apply (induct "((P)\<^sub>\<V>\<^sub>+)" arbitrary: P )
  apply auto
  subgoal for a x P xa 
    apply (cases "map_list_find (range_ofl P) xa")
     apply auto
    subgoal for aa
      apply (metis hd_conv_nth option.sel)   
      done
    done
  done  


lemma subnat_initial_state_helper:
  assumes  "\<forall>x \<in> set (variables_ofl P). \<exists>t. map_list_find (range_ofl P) x = Some t \<and> t\<noteq>[]"
  shows "initial_state_nat (list_problem_encode P)
  = sas_plus_assignment_list_encode (initial_state_list P)"
  apply (auto simp only: initial_state_nat_def
 submap_initial_state
  list_problem_encode_def sub_nth nth.simps sas_assignment_list_encode_def 
  sas_assignment_encode.simps sub_map_list_find_nat sub_map map_map comp_def
    simp_sas_assignment_encode simp_vdlist_encode
)
  thm "option.case"
  apply (auto simp only: sub_map_list_find_nat  simp flip: comp_def map_map)
  using variable_inj apply (auto simp only: comp_def map_find_map)
  apply (auto simp add: map_find_map2 
        option.case_distrib)
  apply (auto simp only: option_encode_case sub_the Case_def option.case)
  using assms apply (auto simp only: lambda_case_simplifier) 
  apply (auto simp only:sub_thefn thefn.simps sub_hd initial_state_list_def
        islist_encode.simps dom_encode.simps sas_assignment_list_encode_def
          map_map comp_def sas_assignment_encode.simps option.case_distrib
      simp flip: subnat_SAS_Plus_Plus_State_To_SAS_Plus )
   apply (auto simp only: lambda_case_simplifier2 lambda_case_simplifier3) 
  done

lemma inv_subnat_initial_state:
  assumes "is_valid_problem_sas_plus_plus (list_problem_to_problem P)"
  shows  "\<forall>x \<in> set (variables_ofl P). \<exists>t. map_list_find (range_ofl P) x = Some t \<and> t\<noteq>[]"
proof -
  obtain P' where def: "P' = list_problem_to_problem P" by simp
  then have "sas_plus_problem.variables_of P' = variables_ofl P " by simp
  moreover have "map_of (range_ofl P) = range_of P' " using def by simp
  moreover have "\<forall>x \<in> set (sas_plus_problem.variables_of P'). \<exists>t. (range_of P') x = Some t \<and> t \<noteq> []"
    by (metis assms def is_valid_problem_sas_plus_plus_then(1) option.collapse range_of_not_empty)
  ultimately show ?thesis by (metis sub_map_list_find)
      
qed

lemma subnat_initial_state:
  assumes "is_valid_problem_sas_plus_plus (list_problem_to_problem P)"
  shows "initial_state_nat (list_problem_encode P)
  = sas_plus_assignment_list_encode (initial_state_list P)"
  using assms inv_subnat_initial_state subnat_initial_state_helper
  by fast


definition SAS_Plus_Plus_To_SAS_Plus_list:: "(variable,domain_element)sas_plus_list_problem \<Rightarrow> (var,dom)sas_plus_list_problem" where
"SAS_Plus_Plus_To_SAS_Plus_list P = \<lparr> variables_ofl = Stage # (map Var ((P)\<^sub>\<V>\<^sub>+)),
      operators_ofl = \<lparr> precondition_of = [(Stage, Init)], effect_of = [(Stage, NonInit)]\<rparr> 
        # (initialization_operators_list P) 
        @ (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator ((P)\<^sub>\<O>\<^sub>+)), 
      initial_ofl = initial_state_list P ,
      goal_ofl = SAS_Plus_Plus_State_To_SAS_Plus_list (NonInit, ((P)\<^sub>G\<^sub>+)),
      range_ofl = (Stage, [Init,NonInit])# 
           map  (\<lambda>(x,y). (x, map DE y)) (map (\<lambda>(x,y). (Var x, y)) (range_ofl P))\<rparr>"

lemma sublist_SAS_Plus_Plus_To_SAS_Plus_helper_apply:
"map_of ((Stage, [Init,NonInit])# 
           map  (\<lambda>(x,y). (x, map DE y)) (map (\<lambda>(x,y). (Var x, y)) (range_ofl P))) k
= 
 (((\<lambda>x. Some (map DE x)) \<circ>\<^sub>m (map_of (range_ofl P)) 
        \<circ>\<^sub>m (\<lambda>x. (case x of Var x \<Rightarrow> Some x | Stage \<Rightarrow> None)))(Stage \<mapsto> [Init, NonInit])) k 
"
  apply (cases k)
   apply (auto simp add: map_of_map map_comp_def simp flip: map_map)
  subgoal for x1
    apply (cases "map_of (range_ofl P) x1")
     apply (auto)
    subgoal 
    proof -
      assume asm: "k = Var x1" " map_of (range_ofl P) x1 = None"
      then have "\<forall>y. (x1,y) \<notin>  set (range_ofl P)" 
        using weak_map_of_SomeI by force
      then have "\<forall>y. (Var x1,y) \<notin> set (map (\<lambda>(x, y). (Var x, y)) (range_ofl P)) "
        by auto
      thus " map_of (map (\<lambda>(x, y). (Var x, y)) (range_ofl P)) (Var x1) = None"
        by (meson map_of_SomeD thef.cases)
    qed
    subgoal for a
    proof -
      assume " k = Var x1"  "map_of (range_ofl P) x1 = Some a"
      then  have " map_of (map (\<lambda>(x, y). (Var x, y)) (range_ofl P)) (Var x1) = Some a"
        using map_of_mapk_SomeI inj_var by fast
      thus ?thesis by blast
    qed
    done
  done
lemma sublist_SAS_Plus_Plus_To_SAS_Plus_helper:
"map_of ((Stage, [Init,NonInit])# 
           map  (\<lambda>(x,y). (x, map DE y)) (map (\<lambda>(x,y). (Var x, y)) (range_ofl P)))
= 
 (((\<lambda>x. Some (map DE x)) \<circ>\<^sub>m (map_of (range_ofl P)) 
        \<circ>\<^sub>m (\<lambda>x. (case x of Var x \<Rightarrow> Some x | Stage \<Rightarrow> None)))(Stage \<mapsto> [Init, NonInit]))
"
  using sublist_SAS_Plus_Plus_To_SAS_Plus_helper_apply by fast

       

lemma sublist_SAS_Plus_Plus_To_SAS_Plus:
" list_problem_to_problem (SAS_Plus_Plus_To_SAS_Plus_list P) = 
    SAS_Plus_Plus_To_SAS_Plus (list_problem_to_problem P)"
  apply (auto simp only: SAS_Plus_Plus_To_SAS_Plus_list_def list_problem_to_problem.simps
  sas_plus_problem.simps sas_plus_list_problem.simps)
  apply (auto simp only: sublist_initialization_operators
   sublist_initial_state sublist_SAS_Plus_Plus_State_To_SAS_Plus
        sublist_SAS_Plus_Plus_To_SAS_Plus_helper SAS_Plus_Plus_To_SAS_Plus_def
        sas_plus_problem.simps list_problem_to_problem.simps islist_to_map.simps
        
)
  done
lemma fst_vdlist_simp:"fst_nat (vdlist_encode x) = variable_encode (fst x)"
  apply (cases x)
  apply (auto simp add: sub_fst)
  done

lemma snd_vdlist_simp: "snd_nat (vdlist_encode x) = list_encode (map domain_element_encode (snd x))"
  apply (cases x)
  apply (auto simp add:sub_snd)
  done

fun map_sasp_to_sas_op :: "nat \<Rightarrow> nat" where 
"map_sasp_to_sas_op n = (if n = 0 then 0 else (SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_nat (hd_nat n)) ## map_sasp_to_sas_op (tl_nat n))"

fun map_sasp_to_sas_op_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_sasp_to_sas_op_acc acc n = (if n = 0 then acc else map_sasp_to_sas_op_acc ((SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_tail (hd_nat n)) ## acc) (tl_nat n))"

lemma map_sasp_to_sas_op_induct:
"map_sasp_to_sas_op_acc acc n = map_acc SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_nat acc n"
  apply(induct acc n rule:map_sasp_to_sas_op_acc.induct)
  apply (auto simp add: subtail_SAS_Plus_Plus_Operator_To_SAS_Plus_Operator)
  done

lemma submap_sasp_to_sas_op: 
"map_sasp_to_sas_op n = map_nat SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_nat n "
  apply (induct  n rule: map_sasp_to_sas_op.induct)
  apply auto
  done

definition map_sasp_to_sas_op_tail :: "nat \<Rightarrow> nat" where 
"map_sasp_to_sas_op_tail n = reverse_nat (map_sasp_to_sas_op_acc 0 n)"

lemma subtail_map_sasp_to_sas_op:
"map_sasp_to_sas_op_tail n = map_sasp_to_sas_op n "
  using map_sasp_to_sas_op_tail_def  submap_sasp_to_sas_op  map_sasp_to_sas_op_induct
subtail_map by presburger

fun map_DE :: "nat \<Rightarrow> nat" where 
"map_DE n = (if n = 0 then 0 else (Suc (Suc (hd_nat n))) ## map_DE (tl_nat n))"

fun map_DE_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_DE_acc acc n = (if n = 0 then acc else map_DE_acc ((Suc (Suc (hd_nat n))) ## acc) (tl_nat n))"

lemma submap_DE : "map_DE n =  map_nat (\<lambda>n. Suc (Suc n)) n"
  apply (induct n rule:map_DE.induct)
  apply auto
  done

lemma map_DE_induct : 
"map_DE_acc acc n = map_acc (\<lambda>n. Suc (Suc n)) acc n "
  apply(induct acc n rule:map_DE_acc.induct)
  apply auto
  done

definition map_DE_tail :: "nat \<Rightarrow> nat" where 
"map_DE_tail n = reverse_nat (map_DE_acc 0 n)"

lemma subtail_map_DE:
"map_DE_tail n = map_DE n "
  using map_DE_tail_def  map_DE_induct submap_DE subtail_map
  by presburger

fun map_var :: "nat \<Rightarrow> nat" where 
"map_var n = (if n = 0 then 0 else ( prod_encode(Suc (fst_nat (hd_nat n)), snd_nat (hd_nat n))) ## map_var (tl_nat n) )"

fun map_var_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_var_acc acc n = (if n = 0 then acc else map_var_acc (( prod_encode(Suc (fst_nat (hd_nat n)), snd_nat (hd_nat n))) ## acc) (tl_nat n) )"

lemma map_var_induct:
"map_var_acc acc n = map_acc (\<lambda>n. prod_encode(Suc (fst_nat n), snd_nat n)) acc n"
  apply(induct acc n rule:map_var_acc.induct)
  apply auto
  done

lemma submap_var :
"map_var n = map_nat (\<lambda>n. prod_encode(Suc (fst_nat n), snd_nat n)) n"
  apply (induct n rule:map_var.induct)
  apply auto
  done

definition map_var_tail :: "nat \<Rightarrow> nat" where 
"map_var_tail n = reverse_nat (map_var_acc 0 n)"

lemma subtail_map_var:
"map_var_tail n = map_var n"
  using map_var_tail_def submap_var map_var_induct subtail_map
  by presburger

fun map_var_DE :: "nat \<Rightarrow> nat" where 
"map_var_DE n = (if n = 0 then 0 else (prod_encode(fst_nat (hd_nat n), map_DE (snd_nat (hd_nat n)))) ## map_var_DE (tl_nat n))"

fun map_var_DE_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_var_DE_acc acc n = (if n = 0 then acc else map_var_DE_acc ((prod_encode(fst_nat (hd_nat n), map_DE_tail (snd_nat (hd_nat n)))) ## acc )(tl_nat n))"

lemma map_var_DE_induct:
"map_var_DE_acc acc n = map_acc ( \<lambda>n. prod_encode(fst_nat n, map_DE (snd_nat n))) acc n "
  apply(induct acc n rule:map_var_DE_acc.induct)
  apply (auto simp add:subtail_map_DE)
  done

lemma submap_var_DE:
"map_var_DE n = map_nat  ( \<lambda>n. prod_encode(fst_nat n, map_DE (snd_nat n))) n"
  apply (induct n rule: map_var_DE.induct)
  apply auto
  done
definition map_var_DE_tail :: "nat \<Rightarrow> nat" where 
"map_var_DE_tail n = reverse_nat (map_var_DE_acc 0 n)"

lemma subtail_map_var_DE:
"map_var_DE_tail n = map_var_DE n"
  using map_var_DE_tail_def submap_var_DE map_var_DE_induct
subtail_map by presburger

fun map_Suc :: "nat\<Rightarrow> nat" where 
"map_Suc n = (if n = 0 then 0 else ((Suc (hd_nat n)) ## map_Suc (tl_nat n)))"

fun map_Suc_acc :: "nat \<Rightarrow> nat\<Rightarrow> nat" where 
"map_Suc_acc acc n = (if n = 0 then acc  else map_Suc_acc ((Suc (hd_nat n)) ## acc) (tl_nat n))"

lemma submap_Suc : 
"map_Suc n = map_nat Suc n"
  apply (induct n rule:map_Suc.induct)
  apply auto
  done
lemma map_Suc_induct :
"map_Suc_acc acc n = map_acc Suc acc n"
  apply(induct acc n rule:map_Suc_acc.induct)
  apply auto
  done

definition map_Suc_tail:: "nat\<Rightarrow> nat" where 
"map_Suc_tail n = reverse_nat (map_Suc_acc 0 n)"

lemma subtail_map_Suc:
"map_Suc_tail n = map_Suc n"
  using map_Suc_induct submap_Suc map_Suc_tail_def subtail_map
  by presburger

definition SAS_Plus_Plus_To_SAS_Plus_nat:: " nat \<Rightarrow> nat " where
"SAS_Plus_Plus_To_SAS_Plus_nat P = ((0 ## (map_Suc (nth_nat 0 P)))##
      ( append_nat ((((prod_encode(0,Suc 0))##0) ## ((prod_encode(0,0))##0) ## 0 ) 
        ## (initialization_operators_nat P)) 
        (map_sasp_to_sas_op (nth_nat (Suc 0) P))) ## 
      (initial_state_nat P)  ##
      (SAS_Plus_Plus_State_To_SAS_Plus_nat (prod_encode(0, (nth_nat (Suc (Suc (Suc 0))) P))))##
      ((prod_encode(0, ((Suc 0) ## 0 ##0)))## 
           map_var_DE (map_var (nth_nat (Suc (Suc (Suc (Suc 0)))) P))) ## 0 )"

definition SAS_Plus_Plus_To_SAS_Plus_tail:: " nat \<Rightarrow> nat " where
"SAS_Plus_Plus_To_SAS_Plus_tail P = ((0 ## (map_Suc_tail (nth_nat 0 P)))##
      ( append_tail ((((prod_encode(0,Suc 0))##0) ## ((prod_encode(0,0))##0) ## 0 ) 
        ## (initialization_operators_tail P)) 
        (map_sasp_to_sas_op_tail (nth_nat (Suc 0) P))) ## 
      (initial_state_tail P)  ##
      (SAS_Plus_Plus_State_To_SAS_Plus_tail (prod_encode(0, (nth_nat (Suc (Suc (Suc 0))) P))))##
      ((prod_encode(0, ((Suc 0) ## 0 ##0)))## 
           map_var_DE_tail (map_var_tail (nth_nat (Suc (Suc (Suc (Suc 0)))) P))) ## 0 )"

lemma subtail_SAS_Plus_Plus_To_SAS_Plus:
"SAS_Plus_Plus_To_SAS_Plus_tail P = SAS_Plus_Plus_To_SAS_Plus_nat P"
  using SAS_Plus_Plus_To_SAS_Plus_nat_def
 SAS_Plus_Plus_To_SAS_Plus_tail_def 
subtail_SAS_Plus_Plus_State_To_SAS_Plus 
subtail_append
 subtail_initial_state 
subtail_initialization_operators subtail_map_Suc subtail_map_sasp_to_sas_op subtail_map_var
 subtail_map_var_DE by presburger

lemma lambda_equals: " (\<lambda>x. case x of
                  (x1, x2) \<Rightarrow>
                    prod_encode
                     ((case x of (x1, x2) \<Rightarrow> Pair (Suc (variable_encode x1)))
                       (list_encode
                         (map (\<lambda>x. Suc (Suc (domain_element_encode x))) x2))))
=
      (\<lambda>x. case x of
                  (x1, x2) \<Rightarrow>
                    prod_encode
                     (Suc (variable_encode x1),
                      list_encode
                       (map (\<lambda>x. Suc (Suc (domain_element_encode x))) x2)))
"
  apply auto
  done
lemma subnat_SAS_Plus_Plus_To_SAS_Plus:
 assumes "is_valid_problem_sas_plus_plus (list_problem_to_problem P)"
 shows "SAS_Plus_Plus_To_SAS_Plus_nat (list_problem_encode P)
= list_problem_plus_encode (SAS_Plus_Plus_To_SAS_Plus_list P)"
  using assms
  apply (auto simp only: SAS_Plus_Plus_To_SAS_Plus_nat_def submap_Suc
  cons0 sub_cons sub_nth nth.simps sub_map sub_append submap_DE submap_var submap_var_DE
 submap_sasp_to_sas_op
        subnat_initialization_operators subnat_initial_state
 )
  apply (auto simp only:  list_problem_encode_def sub_nth nth.simps sub_map 
          sub_append map_map comp_def sub_SAS_Plus_Plus_Operator_To_SAS_Plus_Operator
            sub_fst   fst_vdlist_simp  snd_vdlist_simp fst_def sub_snd snd_def
          SAS_Plus_Plus_To_SAS_Plus_list_def sas_plus_list_problem.simps list_problem_plus_encode_def
          list.simps sub_cons var_encode.simps operator_plus_encode_def sas_plus_operator.simps
          sas_plus_assignment_list_encode_def   sas_plus_assignment_encode.simps dom_encode.simps
          map_append
 )
  apply (auto simp only: subnat_SAS_Plus_Plus_State_To_SAS_Plus
          simp flip: dom_encode.simps islist_encode.simps
    
)
  apply (auto simp only: dom_encode.simps islist_encode.simps sas_plus_assignment_list_encode_def
        vdlist_plus_encode.simps prod.case_distrib )
  apply (auto simp add: comp_def  prod.case_distrib lambda_equals simp del:list_encode.simps)
  done

    




  


end