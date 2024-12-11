theory IMP_Minus_To_SAT_Nat 
  imports IMP_Minus_To_SAS_Plus_Nat IMP_Minus_To_SAT SAT_Plan_Base_Nat SAS_Plus_Strips_Nat
          Cook_Levin_IMP.Primitives
begin

fun poly_of :: "nat*nat \<Rightarrow> nat \<Rightarrow> nat" where 
"poly_of (a,0) x = a"|
"poly_of (a,Suc n) x = x * poly_of (a,n) x"

lemma mono_poly_of: "mono (poly_of p)"
  apply (auto simp add:incseq_def)
  apply (cases p)
  subgoal for m n a b
    apply auto
    apply(induct b arbitrary: p)
     apply auto
    using mult_le_mono by presburger
  done

lemma make_mono_mono_apply:"mono f \<Longrightarrow> make_mono f x = f x"
  apply(induct x)
   apply (auto simp add:incseq_def make_mono_def)
  by (simp add: antisym)

lemma make_mono_mono: "mono f \<Longrightarrow> make_mono f =f"
  using make_mono_mono_apply by blast

lemma sub_make_mono: "make_mono (poly_of p) = poly_of p"
  using mono_poly_of  make_mono_mono
  by presburger 
      

definition t'_pair :: "(nat*nat) \<Rightarrow> (nat*nat) \<Rightarrow> nat \<Rightarrow> nat" where 
"t'_pair pt p_cer x = poly_of pt (bit_length x + poly_of p_cer (bit_length x)) + 1"

lemma subpair_t':
"t'_pair pt p_cer x = t' (poly_of pt) (poly_of p_cer) x"
  apply (auto simp add: t'_pair_def t'_def sub_make_mono)
  done
lemma [termination_simp]: "0 < snd_nat p \<Longrightarrow> prod_encode (fst_nat p, snd_nat p - Suc 0) < p"
proof-
  assume asm: "0 < snd_nat p"
  obtain a b where "p = prod_encode(a,b)"
    by (metis prod_decode_aux.cases prod_decode_inverse)
  thus ?thesis using asm apply (auto simp add:sub_fst sub_snd) apply (auto simp add: prod_encode_def)
    by (metis Groups.add_ac(2) Suc_pred add_diff_cancel_left' le_add1 linorder_not_less not_less_eq_eq plus_nat.simps(2) triangle_Suc)
qed
  
fun poly_of_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"poly_of_nat p x = (if snd_nat p = 0 then fst_nat p else x * poly_of_nat (prod_encode (fst_nat p,snd_nat p -1)) x)"

fun poly_of_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"poly_of_acc acc p x = (if snd_nat p = 0 then acc else poly_of_acc  (x *acc) (prod_encode (fst_nat p,snd_nat p -1)) x)"

lemma sub_poly_of: "poly_of_nat (prod_encode p) x = poly_of p x"
  apply (cases p)
  apply (auto simp only:)
  subgoal for a b
    apply (induct b arbitrary:p)
     apply (subst poly_of_nat.simps)
    apply (auto simp add: sub_fst sub_snd simp del:poly_of_nat.simps)
     apply (subst poly_of_nat.simps)
    apply (auto simp add: sub_fst sub_snd simp del:poly_of_nat.simps)
    done
  done


lemma poly_of_induct:
"poly_of_acc acc p x = poly_of_nat (prod_encode (acc,snd_nat p)) x"
proof -

  obtain a n where p_def:"p = prod_encode (a,n)"
    by (metis prod_decode_inverse surj_pair)
   have helper:"\<forall>m acc. poly_of (x * acc,m) x = x * poly_of (acc,m) x"
     apply auto subgoal for m acc
        apply(induct m) apply auto done done
   from p_def show ?thesis apply(auto simp only: sub_snd snd_conv sub_poly_of)
    apply (induct n arbitrary: p  acc a)
     apply(subst poly_of_acc.simps)
     apply(auto simp add: sub_snd simp del: poly_of_acc.simps)
     apply(subst poly_of_acc.simps)
    apply(auto simp add: helper sub_fst sub_snd simp del: poly_of_acc.simps)
     done
    
qed

definition poly_of_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"poly_of_tail p x = poly_of_acc (fst_nat p) p x"

lemma subtail_poly_of:
"poly_of_tail p x = poly_of_nat p x"
  by (metis add.right_neutral add_eq_if poly_of.simps(1)
 poly_of.simps(2) poly_of_induct poly_of_nat.simps poly_of_tail_def sub_poly_of)

definition t'_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"t'_nat pt p_cer x = poly_of_nat pt (bit_length x + poly_of_nat p_cer (bit_length x)) + 1"

definition t'_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"t'_tail pt p_cer x = poly_of_tail pt (bit_length x + poly_of_tail p_cer (bit_length x)) + 1"

lemma subtail_t':
"t'_tail pt p_cer x = t'_nat pt p_cer x"
  using subtail_poly_of t'_nat_def t'_tail_def by presburger

lemma subnat_t': 
"t'_nat (prod_encode pt) (prod_encode p_cer) x = t'_pair pt p_cer x"
  apply (auto simp only:t'_nat_def t'_pair_def sub_poly_of)
  done

definition "empty_sasp_action_nat \<equiv> (0 ## 0 ## 0)"
lemma sub_empty_sasp_action: "empty_sasp_action_nat = operator_plus_encode empty_sasp_action"
  apply (auto simp only:cons0 sub_cons 
        empty_sasp_action_nat_def empty_sasp_action_def operator_plus_encode_def list_encode_eq
            sas_plus_assignment_list_encode_def
        simp flip: list_encode.simps)
   apply auto
  done
definition "empty_sasp_action_tail \<equiv> (0 ## 0 ## 0)"
lemma subtail_empty_sasp_action:
"empty_sasp_action_tail =empty_sasp_action_nat"
  using empty_sasp_action_nat_def empty_sasp_action_tail_def by force


definition
  "prob_with_noop_list \<Pi> \<equiv>
     \<lparr> variables_ofl = variables_ofl \<Pi>,
      operators_ofl = empty_sasp_action # operators_ofl \<Pi>, 
      initial_ofl = initial_ofl \<Pi>,
      goal_ofl = goal_ofl \<Pi>,
      range_ofl = range_ofl \<Pi>\<rparr>"

lemma sublist_prob_with_noop: 
"list_problem_to_problem (prob_with_noop_list \<Pi>) = prob_with_noop  (list_problem_to_problem \<Pi>)"
  apply (auto simp add: prob_with_noop_list_def prob_with_noop_def)
  done

definition prob_with_noop_nat :: "nat \<Rightarrow> nat" where 
  "prob_with_noop_nat p = (nth_nat 0 p) ## ( empty_sasp_action_nat ##  (nth_nat (Suc 0) p))
## (tl_nat (tl_nat p))"

definition prob_with_noop_tail :: "nat \<Rightarrow> nat" where 
  "prob_with_noop_tail p = (nth_nat 0 p) ## ( empty_sasp_action_tail ##  (nth_nat (Suc 0) p))
## (tl_nat (tl_nat p))"


lemma subtail_prob_with_noop:
"prob_with_noop_tail p =prob_with_noop_nat p"
  using prob_with_noop_nat_def prob_with_noop_tail_def subtail_empty_sasp_action by presburger

lemma subnat_prob_with_noop: 
"prob_with_noop_nat (list_problem_plus_encode p) = 
 list_problem_plus_encode (prob_with_noop_list p)"
  apply (auto simp only: prob_with_noop_nat_def sub_cons list_problem_plus_encode_def
            sub_tl tail.simps sub_nth nth.simps prob_with_noop_list_def sas_plus_list_problem.simps
            sub_empty_sasp_action)
  apply auto
  done


definition encode_interfering_operator_pair_exclusion_list
  :: "'variable strips_list_problem
    \<Rightarrow> nat
    \<Rightarrow> 'variable strips_operator
    \<Rightarrow> 'variable strips_operator
    \<Rightarrow> sat_plan_variable formula"
  where "encode_interfering_operator_pair_exclusion_list \<Pi> k op\<^sub>1 op\<^sub>2
    \<equiv> let ops = operators_of \<Pi> in
      \<^bold>\<not>(Atom (Operator k (index ops op\<^sub>1)))
      \<^bold>\<or> \<^bold>\<not>(Atom (Operator k (index ops op\<^sub>2)))"

lemma sublist_encode_interfering_operator_pair_exclusion:
"encode_interfering_operator_pair_exclusion_list \<Pi> k op\<^sub>1 op\<^sub>2
= encode_interfering_operator_pair_exclusion (strips_list_problem_to_problem \<Pi>) k op\<^sub>1 op\<^sub>2
"
  apply (auto simp add:encode_interfering_operator_pair_exclusion_list_def 
encode_interfering_operator_pair_exclusion_def)
  done

definition encode_interfering_operator_pair_exclusion_nat
  :: "nat
    \<Rightarrow> nat
    \<Rightarrow> nat
    \<Rightarrow> nat
    \<Rightarrow> nat"
  where "encode_interfering_operator_pair_exclusion_nat p k o1 o2
    \<equiv> let ops = nth_nat (Suc 0)  p in
     4 ## (2 ## (1 ## (1 ## k ## (index_nat ops o1)## 0) ## 0) ## 0)
      ## (2 ## (1 ## (1  ## k ## (index_nat ops o2) ## 0) ## 0) ## 0) ## 0"
definition encode_interfering_operator_pair_exclusion_tail :: "nat
    \<Rightarrow> nat
    \<Rightarrow> nat
    \<Rightarrow> nat
    \<Rightarrow> nat" where 
"encode_interfering_operator_pair_exclusion_tail p k o1 o2 =
encode_interfering_operator_pair_exclusion_nat p k o1 o2 "

lemma subtail_encode_interfering_operator_pair_exclusion:
"encode_interfering_operator_pair_exclusion_tail p k o1 o2 =
encode_interfering_operator_pair_exclusion_nat p k o1 o2 "
  using encode_interfering_operator_pair_exclusion_tail_def by presburger

lemma subnat_encode_interfering_operator_pair_exclusion:
"encode_interfering_operator_pair_exclusion_nat (strips_list_problem_encode p) k
 (strips_operator_encode o1) (strips_operator_encode o2) = 
sat_formula_encode (encode_interfering_operator_pair_exclusion_list p k o1 o2)"
  using inj_strips_op
  apply(auto simp only: encode_interfering_operator_pair_exclusion_nat_def
    strips_list_problem_encode.simps sub_nth nth.simps strips_operator_list_encode_def
      sub_index Let_def sub_cons cons0 encode_interfering_operator_pair_exclusion_list_def
 simp flip: sat_variable_encode.simps sat_formula_encode.simps
)
  done


declare elemof.simps [simp del]
fun list_inter :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"list_inter xs ys = (if xs = 0 then 0 
else if elemof (hd_nat xs) ys \<noteq> 0 then 1 else list_inter (tl_nat xs) ys)"

definition list_inter_tail ::  "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"list_inter_tail xs ys = list_inter xs ys"

lemma subtail_list_inter:
"list_inter_tail xs ys = list_inter xs ys"
  using list_inter_tail_def by presburger


lemma list_encode_pos:"(list_encode xs > 0) = (xs \<noteq> []) "
  using list_encode_empty by force

lemma sub_list_inter:
"inj f \<Longrightarrow> list_inter (list_encode (map f xs)) (list_encode (map f ys)) \<noteq> 0 
= list_ex (\<lambda>v. list_ex ((=) v) xs ) ys"
  apply (induct xs)
   apply (simp)
   apply (induct ys)
    apply simp
   apply simp
  apply (subst list_inter.simps)
  apply (simp add: sub_hd sub_tl tail.simps  head.simps list.simps list_encode_empty list_encode_pos
      del:list_encode.simps list_inter.simps)
  using sub_elem_of_inj[of f] apply (auto simp  del:list_encode.simps list_inter.simps)
  apply (metis (no_types, lifting) Bex_set) 
    apply (metis (no_types, lifting) Bex_set)
  using Bex_set apply fastforce
 using sub_elem_of_inj[of f]
  by (smt (z3) Bex_set)
    



definition are_operators_interfering_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"are_operators_interfering_nat o1 o2 \<equiv>
if list_inter (nth_nat (Suc (Suc 0)) o1) (nth_nat 0 o2) \<noteq> 0  \<or> 
    list_inter (nth_nat 0 o1) (nth_nat (Suc (Suc 0)) o2) \<noteq> 0 then 1 else 0 "

definition are_operators_interfering_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"are_operators_interfering_tail o1 o2 \<equiv>
if list_inter_tail (nth_nat (Suc (Suc 0)) o1) (nth_nat 0 o2) \<noteq> 0  \<or> 
    list_inter_tail (nth_nat 0 o1) (nth_nat (Suc (Suc 0)) o2) \<noteq> 0 then 1 else 0 "
lemma subtail_are_operators_interfering:
"are_operators_interfering_tail o1 o2 = are_operators_interfering_nat o1 o2"
  using are_operators_interfering_nat_def are_operators_interfering_tail_def 
list_inter_tail_def by presburger

lemma sub_are_operators_interfering:
"(are_operators_interfering_nat (strips_operator_encode o1) (strips_operator_encode o2) > 0) =
 (are_operators_interfering o1 o2)"
  using inj_sasp
  apply (auto simp only: are_operators_interfering_nat_def strips_operator_encode.simps
          sub_nth nth.simps sas_plus_assignment_list_encode_def
            sub_list_inter are_operators_interfering_def)
    apply auto
  apply presburger
  done
  

definition encode_interfering_operator_exclusion_list
  :: "'variable strips_list_problem \<Rightarrow> nat \<Rightarrow> sat_plan_variable formula"
  where "encode_interfering_operator_exclusion_list \<Pi> t \<equiv> let
      ops = operators_of \<Pi>
      ; interfering = filter (\<lambda>(op\<^sub>1, op\<^sub>2). index ops op\<^sub>1 \<noteq> index ops op\<^sub>2
        \<and> are_operators_interfering op\<^sub>1 op\<^sub>2) (List.product ops ops)
    in BigAnd (concat (map (\<lambda>(op\<^sub>1, op\<^sub>2). map (\<lambda>k. encode_interfering_operator_pair_exclusion_list \<Pi> k op\<^sub>1 op\<^sub>2)
      [0..<t]) interfering ))"

lemma sublist_encode_interfering_operator_exclusion:
"encode_interfering_operator_exclusion_list \<Pi> t
= encode_interfering_operator_exclusion (strips_list_problem_to_problem \<Pi>) t "
  apply (auto simp add:encode_interfering_operator_exclusion_list_def
encode_interfering_operator_exclusion_def
    sub_foldr sublist_encode_interfering_operator_pair_exclusion
)
  done
fun filter_interfering:: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"filter_interfering ops xs = (if xs = 0 then 0 else if index_nat ops (fst_nat (hd_nat xs)) \<noteq> index_nat ops (snd_nat (hd_nat xs))
        \<and> are_operators_interfering_nat (fst_nat (hd_nat xs)) (snd_nat (hd_nat xs)) \<noteq> 0 then (hd_nat xs) ## filter_interfering ops (tl_nat xs) else  filter_interfering ops (tl_nat xs))"

fun filter_interfering_acc:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"filter_interfering_acc acc ops xs = (if xs = 0 then acc else if index_nat ops (fst_nat (hd_nat xs)) \<noteq> index_nat ops (snd_nat (hd_nat xs))
        \<and> are_operators_interfering_tail (fst_nat (hd_nat xs)) (snd_nat (hd_nat xs)) \<noteq> 0 then filter_interfering_acc ((hd_nat xs) ## acc) ops (tl_nat xs) else  filter_interfering_acc acc ops (tl_nat xs))"

lemma filter_interfering_induct:
"filter_interfering_acc acc ops xs  = filter_acc  (\<lambda>n. index_nat ops (fst_nat n) \<noteq> index_nat ops (snd_nat n)
        \<and> are_operators_interfering_nat (fst_nat n) (snd_nat n) \<noteq> 0 ) acc xs "
  apply(induct acc ops xs rule:filter_interfering_acc.induct)
  apply (auto simp add:subtail_are_operators_interfering)
  done


lemma subfilter_interfering:
"filter_interfering ops xs = filter_nat (\<lambda>n. index_nat ops (fst_nat n) \<noteq> index_nat ops (snd_nat n)
        \<and> are_operators_interfering_nat (fst_nat n) (snd_nat n) \<noteq> 0 ) xs"
  apply (induct ops xs rule:filter_interfering.induct)
  apply (auto simp del:index_nat.simps)
  done

definition filter_interfering_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"filter_interfering_tail ops xs = reverse_nat (filter_interfering_acc 0 ops xs )  "

lemma subtail_filter_interfering:
"filter_interfering_tail ops xs = filter_interfering ops xs "
  using filter_interfering_induct filter_interfering_tail_def subfilter_interfering subtail_filter
  by presburger

fun map_encode_interfering :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_encode_interfering p n xs = (if xs = 0 then 0 else (encode_interfering_operator_pair_exclusion_nat p (hd_nat xs) (fst_nat n) (snd_nat n)) 
## map_encode_interfering p n (tl_nat xs))"
lemma submap_encode_interfering: 
"map_encode_interfering p n xs = map_nat (\<lambda>k. encode_interfering_operator_pair_exclusion_nat p k (fst_nat n) (snd_nat n)) xs "
  apply (induct p n xs rule: map_encode_interfering.induct)
  apply auto
  done
fun map_encode_interfering_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_encode_interfering_acc acc  p n xs = (if xs = 0 then acc else
map_encode_interfering_acc ((encode_interfering_operator_pair_exclusion_nat p (hd_nat xs) (fst_nat n) (snd_nat n)) 
## acc) p n (tl_nat xs))"

lemma map_encode_interfering_induct:
"map_encode_interfering_acc acc  p n xs = map_acc
(\<lambda>k. encode_interfering_operator_pair_exclusion_tail p k (fst_nat n) (snd_nat n)) acc xs"
  apply(induct acc p n xs rule:map_encode_interfering_acc.induct)
  apply (auto simp add:subtail_encode_interfering_operator_pair_exclusion)
  done


fun map_map_encode_interfering :: "nat \<Rightarrow>nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_map_encode_interfering \<Pi> t xs = (if xs = 0 then 0 else 
(map_encode_interfering  \<Pi> (hd_nat xs) (list_less_nat t)) ## map_map_encode_interfering \<Pi> t (tl_nat xs) 
) "

fun map_map_encode_interfering_acc :: "nat \<Rightarrow> nat \<Rightarrow>nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_map_encode_interfering_acc acc \<Pi> t xs = (if xs = 0 then acc else  map_map_encode_interfering_acc(
(map_encode_interfering  \<Pi> (hd_nat xs) (list_less_nat t)) ## acc) \<Pi> t (tl_nat xs) 
) "

lemma map_map_encode_interfering_induct:
"map_map_encode_interfering_acc acc \<Pi> t xs = map_acc (\<lambda>n. map_encode_interfering  \<Pi> n
      (list_less_nat t) ) acc xs "
  apply(induct acc \<Pi> t xs rule: map_map_encode_interfering_acc.induct)
  apply auto
  done

lemma submap_map_encode_interfering:
"map_map_encode_interfering \<Pi> t xs = map_nat (\<lambda>n. map_encode_interfering  \<Pi> n
      (list_less_nat t) ) xs "
  apply (induct  \<Pi> t xs rule: map_map_encode_interfering.induct)
  apply auto
  done

definition map_map_encode_interfering_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_map_encode_interfering_tail \<Pi> t xs = reverse_nat (map_map_encode_interfering_acc 0 \<Pi> t xs)"

lemma subtail_map_map_encode_interfering:
"map_map_encode_interfering_tail \<Pi> t xs = map_map_encode_interfering \<Pi> t xs "
  using map_map_encode_interfering_induct map_map_encode_interfering_tail_def
 submap_map_encode_interfering subtail_map by presburger

definition encode_interfering_operator_exclusion_nat
  :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "encode_interfering_operator_exclusion_nat \<Pi> t \<equiv> let
      ops = nth_nat (Suc 0) \<Pi>
      ; interfering = filter_interfering ops (product_nat ops ops)
    in BigAnd_nat (concat_nat (map_map_encode_interfering \<Pi> t interfering ))"

definition encode_interfering_operator_exclusion_tail
  :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "encode_interfering_operator_exclusion_tail \<Pi> t \<equiv> let
      ops = nth_nat (Suc 0) \<Pi>
      ; interfering = filter_interfering_tail ops (product_tail ops ops)
    in BigAnd_tail (concat_tail (map_map_encode_interfering_tail \<Pi> t interfering ))"

lemma subtail_encode_interfering_operator_exclusion:
"encode_interfering_operator_exclusion_tail p t = encode_interfering_operator_exclusion_nat p t "
  using encode_interfering_operator_exclusion_nat_def encode_interfering_operator_exclusion_tail_def
 subtail_BigAnd subtail_concat subtail_filter_interfering subtail_map_map_encode_interfering 
subtail_product by presburger

lemma subnat_encode_interfering_operator_exclusion :
"encode_interfering_operator_exclusion_nat (strips_list_problem_encode p) t =
sat_formula_encode (encode_interfering_operator_exclusion_list p t)"
  using inj_strips_op
  apply (auto simp only: encode_interfering_operator_exclusion_nat_def
subfilter_interfering submap_encode_interfering submap_map_encode_interfering
strips_list_problem_encode.simps sub_nth nth.simps Let_def strips_operator_list_encode_def
sub_product sub_filter filter_map
         )
  apply (auto simp add: Fun.comp_def prod.case_eq_if sub_fst sub_snd simp del: list_encode.simps 
          BigAnd_nat.simps concat_nat.simps index_nat.simps strips_operator_encode.simps
        map_nat.simps simp flip: strips_operator_list_encode_def  strips_list_problem_encode.simps)
  apply (auto simp only:  strips_operator_list_encode_def sub_index sub_are_operators_interfering
      sub_map map_map Fun.comp_def  prod.case_eq_if  sub_fst sub_snd fst_conv snd_conv sub_list_less
            subnat_encode_interfering_operator_pair_exclusion
            )
  apply (auto simp only: sub_concat  simp flip: Fun.comp_def[of list_encode "\<lambda>x. 
    (map (\<lambda>k. sat_formula_encode
                (encode_interfering_operator_pair_exclusion_list p k (fst x) (snd x)))
                       [0..<t])" ] map_map map_concat)
  apply (auto simp only: simp flip: Fun.comp_def[of sat_formula_encode 
            "\<lambda>k. encode_interfering_operator_pair_exclusion_list p k (fst _) (snd _)"] map_map
)
  apply (auto simp only: case_prod_beta' sub_BigAnd encode_interfering_operator_exclusion_list_def split_comp_eq 
      Let_def simp flip: Fun.comp_def[of "map sat_formula_encode"
"\<lambda>x. (map (\<lambda>k. encode_interfering_operator_pair_exclusion_list p k (fst x) (snd x))
                       [0..<t])"] map_map map_concat sat_formula_list_encode_def split_comp_eq)
  done

definition encode_problem_with_operator_interference_exclusion_list
  :: "'variable strips_list_problem \<Rightarrow> nat \<Rightarrow> sat_plan_variable formula"
  where "encode_problem_with_operator_interference_exclusion_list \<Pi> t
    \<equiv> encode_initial_state_list \<Pi>
      \<^bold>\<and> (encode_operators_list \<Pi> t
      \<^bold>\<and> (encode_all_frame_axioms_list \<Pi> t
      \<^bold>\<and> (encode_interfering_operator_exclusion_list \<Pi> t
      \<^bold>\<and> (encode_goal_state_list \<Pi> t))))"

definition encode_problem_with_operator_interference_exclusion_nat
  :: "nat\<Rightarrow> nat \<Rightarrow> nat"
  where "encode_problem_with_operator_interference_exclusion_nat \<Pi> t
    \<equiv> 3 ## (encode_initial_state_nat \<Pi>)
      ## (3 ## (encode_operators_nat \<Pi> t)
      ## (3 ## (encode_all_frame_axioms_nat \<Pi> t)
      ## (3 ## (encode_interfering_operator_exclusion_nat \<Pi> t)
      ## (encode_goal_state_nat \<Pi> t) ## 0) ## 0 )## 0) ## 0"

definition encode_problem_with_operator_interference_exclusion_tail
  :: "nat\<Rightarrow> nat \<Rightarrow> nat"
  where "encode_problem_with_operator_interference_exclusion_tail \<Pi> t
    \<equiv> 3 ## (encode_initial_state_tail \<Pi>)
      ## (3 ## (encode_operators_tail \<Pi> t)
      ## (3 ## (encode_all_frame_axioms_tail \<Pi> t)
      ## (3 ## (encode_interfering_operator_exclusion_tail \<Pi> t)
      ## (encode_goal_state_tail \<Pi> t) ## 0) ## 0 )## 0) ## 0"

lemma subtail_encode_problem_with_operator_interference_exclusion:
"encode_problem_with_operator_interference_exclusion_tail \<Pi> t =
 encode_problem_with_operator_interference_exclusion_nat \<Pi> t"
  using encode_problem_with_operator_interference_exclusion_nat_def
 encode_problem_with_operator_interference_exclusion_tail_def subtail_encode_all_frame_axioms
 subtail_encode_goal_state subtail_encode_initial_state subtail_encode_interfering_operator_exclusion 
subtail_encode_operators by presburger

lemma subnat_encode_problem_with_operator_interference_exclusion:
"encode_problem_with_operator_interference_exclusion_nat (strips_list_problem_encode \<Pi>) t =
sat_formula_encode (encode_problem_with_operator_interference_exclusion_list \<Pi> t)"
  apply (auto simp only:encode_problem_with_operator_interference_exclusion_nat_def
    sub_cons cons0 subnat_encode_initial_state subnat_encode_operators subnat_encode_all_frame_axioms
subnat_encode_interfering_operator_exclusion subnat_encode_goal_state simp flip: sat_formula_encode.simps
    encode_problem_with_operator_interference_exclusion_list_def
)
  done

lemma sublist_encode_problem_with_operator_interference_exclusion:
"encode_problem_with_operator_interference_exclusion_list \<Pi> t
= encode_problem_with_operator_interference_exclusion (strips_list_problem_to_problem \<Pi>) t"
  apply (auto simp only: encode_problem_with_operator_interference_exclusion_list_def 
encode_problem_with_operator_interference_exclusion_def
    sublist_encode_initial_state sublist_encode_operators sublist_encode_all_frame_axioms
    sublist_encode_interfering_operator_exclusion
    sublist_encode_goal_state
)
  done

 definition imp_to_sat_list :: "Com.com \<Rightarrow> (nat*nat) \<Rightarrow> (nat*nat) \<Rightarrow> nat \<Rightarrow> sat_plan_formula" where
    "imp_to_sat_list c pt p_cer x =
      (let I = [(''input'', x)]; 
          G = [(''input'',0)];
          guess_range = x + 1 + 2 * 2 ^ (poly_of p_cer (bit_length x));
          max_bits = max_input_bits_list c I guess_range
      in
        encode_problem_with_operator_interference_exclusion_list 
        (sas_plus_problem_to_strips_problem_list (prob_with_noop_list (IMP_Minus_to_SAS_Plus_list c I guess_range G (t'_pair pt p_cer x))))
           (100 * (max_bits + (t'_pair pt p_cer x) + 1) * ((t'_pair pt p_cer x) - 1) +
             (max_bits + (t'_pair pt p_cer x) + 2) * (num_variables c + 2) + 52))"

lemma sublist_imp_to_sat:
"imp_to_sat_list c pt p_cer x 
= imp_to_sat c (poly_of pt) (poly_of p_cer) x"
  apply (auto simp only: imp_to_sat_list_def sublist_encode_problem_with_operator_interference_exclusion
              sublist_sas_plus_problem_to_strips_problem sublist_prob_with_noop  sublist_max_input_bits
                  subpair_t' imp_to_sat_def Let_def)
  using sublist_IMP_Minus_to_SAS_Plus[of " [(''input'', x)]"] sublist_max_input_bits[of " [(''input'', x)]"]
  apply (auto)
  done

lemma poly_poly_of:"poly (poly_of p)"
  apply(cases p)
  subgoal for a b
  proof (induct b arbitrary:p)
    case 0
    then have "poly_of p = (\<lambda>_.a)" using poly_of.simps(1) by presburger
    then show ?case by auto
  next
    case (Suc b)
    then obtain p' where p'_def: "p' = poly_of (a,b)" by blast
    then have "poly p'" using Suc by simp
    moreover have "poly_of p = (\<lambda>x. (p' x *x))" using Suc p'_def by force
    ultimately show ?case apply auto
      using poly_linear poly_mult by presburger
  qed
  done

lemma main_lemma_hol_list:
  fixes c pt p_cer in_lang
  assumes verifier_tbounded:
  (*Mohammad: I don't think we need the time to bounded by the cert length since the cert length
              is bounded by input length.*)
    "\<And>s. \<exists>t s'. (c, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and>
                   t \<le> poly_of pt (bit_length (s ''input''))"
  assumes verifier_terminates: 
          (*"\<And>x z. \<forall>s. s ''input'' = x \<and> s ''certificate'' = z \<longrightarrow>
                         (\<exists>t s'. (c, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = in_lang x)"*)
          (*Mohammad: The TM needs no access to the certificate since it is non-deterministic, i.e. it can
            assume it is guessed.*)
          (*Mohammad: The computation output should depend on the state, otherwise the theorem
                      statement does not hold*)
          (*Mohammad: We need to specify what it means for c to be a verifier for the certificates*)
          "\<And>x s. \<lbrakk>in_lang x = 0 ; s ''input'' = x\<rbrakk> \<Longrightarrow>
                    (\<exists>z t s'. bit_length z \<le> poly_of p_cer (bit_length x) \<and>
                              (c, s(''certificate'' := z)) \<Rightarrow>\<^bsup> t \<^esup> s' \<and>
                              s' ''input'' = in_lang x)"
          "\<And>x s s' t. \<lbrakk>in_lang x \<noteq> 0; s ''input'' = x; (c, s) \<Rightarrow>\<^bsup> t \<^esup> s'\<rbrakk> \<Longrightarrow>
                         s' ''input'' = in_lang x"
  assumes verifier_has_registers:
    "''input'' \<in> set (Max_Constant.all_variables c)"
  shows "\<exists>t_red s_red.
         poly t_red 
       \<and> poly s_red
       \<and> (\<forall>x. \<exists>f.  bit_length (encode_sat f) \<le> s_red ( bit_length x ) \<and> imp_to_sat_list c pt p_cer x = f
                   \<and> (Sema.sat {f}  \<longleftrightarrow> in_lang x = 0))"
  using main_lemma_hol poly_poly_of assms  by (auto simp add: sublist_imp_to_sat) 

 definition imp_to_sat_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
    "imp_to_sat_nat c pt p_cer x =
      (let I = (prod_encode (vname_encode ''input'', x)) ## 0; 
          G = (prod_encode (vname_encode ''input'', 0)) ## 0;
          guess_range = x + 1 + 2 * 2 ^ (poly_of_nat p_cer (bit_length x));
          max_bits = max_input_bits_nat c I guess_range
      in
        encode_problem_with_operator_interference_exclusion_nat 
        (sas_plus_problem_to_strips_problem_nat (prob_with_noop_nat (IMP_Minus_to_SAS_Plus_nat c I guess_range G (t'_nat pt p_cer x))))
           (100 * (max_bits + (t'_nat pt p_cer x) + 1) * ((t'_nat pt p_cer x) - 1) +
             (max_bits + (t'_nat pt p_cer x) + 2) * (num_variables_nat c + 2) + 52))"

definition imp_to_sat_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
    "imp_to_sat_tail c pt p_cer x =
      (let I = (prod_encode (vname_encode ''input'', x)) ## 0; 
          G = (prod_encode (vname_encode ''input'', 0)) ## 0;
          guess_range = x + 1 + 2 * 2 ^ (poly_of_tail p_cer (bit_length x));
          max_bits = max_input_bits_tail c I guess_range
      in
        encode_problem_with_operator_interference_exclusion_tail 
        (sas_plus_problem_to_strips_problem_tail (prob_with_noop_tail (IMP_Minus_to_SAS_Plus_tail c I guess_range G (t'_tail pt p_cer x))))
           (100 * (max_bits + (t'_tail pt p_cer x) + 1) * ((t'_tail pt p_cer x) - 1) +
             (max_bits + (t'_tail pt p_cer x) + 2) * (num_variables_tail c + 2) + 52))"

lemma subtail_imp_to_sat :
"imp_to_sat_tail c pt p_cer x = imp_to_sat_nat c pt p_cer x"
  apply(auto simp only: imp_to_sat_tail_def imp_to_sat_nat_def
subtail_poly_of subtail_max_input_bits subtail_encode_problem_with_operator_interference_exclusion
subtail_sas_plus_problem_to_strips_problem subtail_prob_with_noop subtail_IMP_Minus_to_SAS_Plus
subtail_t' subtail_num_variables
)
  done

lemma unfold_map_signleton:"[f x] = map f [x]"
  apply auto
  done

lemma subnat_imp_to_sat:
"imp_to_sat_nat (com_encode c) (prod_encode pt) (prod_encode p_cer) x =
sat_formula_encode (imp_to_sat_list c pt p_cer x)  "
  apply (auto simp only: imp_to_sat_nat_def Let_def
    cons0 sub_cons  unfold_map_signleton[of impm_assignment_encode] 
sub_poly_of subnat_max_input_bits subnat_t' sub_num_variables subnat_IMP_Minus_to_SAS_Plus
subnat_prob_with_noop subnat_encode_problem_with_operator_interference_exclusion
simp flip: impm_assignment_encode.simps  impm_assignment_list_encode_def
)
proof -
  let ?P = "IMP_Minus_to_SAS_Plus_list c [(''input'', x)]
              (x + 1 + 2 * 2 ^ poly_of p_cer (Bit_Length.bit_length x)) [(''input'', 0)]
              (t'_pair pt p_cer x)"
  let ?P'= "IMP_Minus_to_SAS_Plus c (map_of [(''input'', x)])
              (x + 1 + 2 * 2 ^ poly_of p_cer (Bit_Length.bit_length x)) (map_of [(''input'', 0)])
              (t'_pair pt p_cer x)"
  have "list_problem_to_problem ?P = ?P'" using sublist_IMP_Minus_to_SAS_Plus by blast
  hence "is_valid_problem_sas_plus (list_problem_to_problem ?P)" using valid_problem by presburger
  hence "is_valid_problem_sas_plus (prob_with_noop (list_problem_to_problem ?P))" using noops_valid
    by fast
  hence "is_valid_problem_sas_plus (list_problem_to_problem (prob_with_noop_list ?P))"
    using sublist_prob_with_noop by metis
  thus "encode_problem_with_operator_interference_exclusion_nat
     (sas_plus_problem_to_strips_problem_nat
       (list_problem_plus_encode
         (prob_with_noop_list
           (IMP_Minus_to_SAS_Plus_list c [(''input'', x)]
             (x + 1 + 2 * 2 ^ poly_of p_cer (Bit_Length.bit_length x)) [(''input'', 0)]
             (t'_pair pt p_cer x)))))
     (100 *
      (max_input_bits_list c [(''input'', x)]
        (x + 1 + 2 * 2 ^ poly_of p_cer (Bit_Length.bit_length x)) +
       t'_pair pt p_cer x +
       1) *
      (t'_pair pt p_cer x - 1) +
      (max_input_bits_list c [(''input'', x)]
        (x + 1 + 2 * 2 ^ poly_of p_cer (Bit_Length.bit_length x)) +
       t'_pair pt p_cer x +
       2) *
      (num_variables c + 2) +
      52) =
    sat_formula_encode (imp_to_sat_list c pt p_cer x)"
    apply (auto simp only: subnat_sas_plus_problem_to_strips_problem Let_def
          subnat_encode_problem_with_operator_interference_exclusion imp_to_sat_list_def )
    done
       
qed 

lemma inj_formula : "inj sat_formula_encode" 
  apply (auto simp add: inj_def)
  using sat_formula_id by metis

lemma inj_formula_simp : "(sat_formula_encode x = sat_formula_encode y) = (x=y)"
  using inj_formula by (auto simp add:inj_def)
lemma main_lemma_hol_nat:
  fixes c and pt::"nat*nat" and p_cer::"nat*nat" and in_lang
  assumes verifier_tbounded:
    "\<And>s. \<exists>t s'. (c, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and>
                   t \<le> poly_of pt (bit_length (s ''input''))"
  assumes verifier_terminates: 
          "\<And>x s. \<lbrakk>in_lang x = 0 ; s ''input'' = x\<rbrakk> \<Longrightarrow>
                    (\<exists>z t s'. bit_length z \<le> poly_of p_cer (bit_length x) \<and>
                              (c, s(''certificate'' := z)) \<Rightarrow>\<^bsup> t \<^esup> s' \<and>
                              s' ''input'' = in_lang x)"
          "\<And>x s s' t. \<lbrakk>in_lang x \<noteq> 0; s ''input'' = x; (c, s) \<Rightarrow>\<^bsup> t \<^esup> s'\<rbrakk> \<Longrightarrow>
                         s' ''input'' = in_lang x"
  assumes verifier_has_registers:
    "''input'' \<in> set (Max_Constant.all_variables c)"
  shows "\<exists>t_red s_red.
         poly t_red 
       \<and> poly s_red
       \<and> (\<forall>x. \<exists>f.  bit_length (encode_sat f) \<le> s_red ( bit_length x ) \<and> imp_to_sat_nat (com_encode c) (prod_encode pt) (prod_encode p_cer) x = sat_formula_encode f
                   \<and> (Sema.sat {f}  \<longleftrightarrow> in_lang x = 0))"
  using assms main_lemma_hol_list by (auto simp add:subnat_imp_to_sat inj_formula_simp)

lemma main_lemma_hol_tail:
  fixes c and pt::"nat*nat" and p_cer::"nat*nat" and in_lang
  assumes verifier_tbounded:
    "\<And>s. \<exists>t s'. (c, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and>
                   t \<le> poly_of pt (bit_length (s ''input''))"
  assumes verifier_terminates: 
          "\<And>x s. \<lbrakk>in_lang x = 0 ; s ''input'' = x\<rbrakk> \<Longrightarrow>
                    (\<exists>z t s'. bit_length z \<le> poly_of p_cer (bit_length x) \<and>
                              (c, s(''certificate'' := z)) \<Rightarrow>\<^bsup> t \<^esup> s' \<and>
                              s' ''input'' = in_lang x)"
          "\<And>x s s' t. \<lbrakk>in_lang x \<noteq> 0; s ''input'' = x; (c, s) \<Rightarrow>\<^bsup> t \<^esup> s'\<rbrakk> \<Longrightarrow>
                         s' ''input'' = in_lang x"
  assumes verifier_has_registers:
    "''input'' \<in> set (Max_Constant.all_variables c)"
  shows "\<exists>t_red s_red.
         poly t_red 
       \<and> poly s_red
       \<and> (\<forall>x. \<exists>f.  bit_length (encode_sat f) \<le> s_red ( bit_length x ) \<and> imp_to_sat_tail(com_encode c) (prod_encode pt) (prod_encode p_cer) x = sat_formula_encode f
                   \<and> (Sema.sat {f}  \<longleftrightarrow> in_lang x = 0))"
  using assms main_lemma_hol_nat by (auto simp add:subtail_imp_to_sat inj_formula_simp)
                                 
end