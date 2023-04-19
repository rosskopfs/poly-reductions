theory SAS_Plus_Strips_Nat 
  imports "Verified_SAT_Based_AI_Planning.SAS_Plus_STRIPS" Primitives
begin

definition possible_assignments_for_list
  :: "('variable, 'domain) sas_plus_list_problem \<Rightarrow> 'variable \<Rightarrow> ('variable \<times> 'domain) list" 
  where "possible_assignments_for_list \<Psi> v \<equiv> [(v, a). a \<leftarrow> the (map_list_find (range_ofl \<Psi>) v)]"

lemma sublist_possible_assignments_for:
"possible_assignments_for_list P v =
 possible_assignments_for (list_problem_to_problem P) v"
  apply (auto simp add: sub_map_list_find possible_assignments_for_list_def possible_assignments_for_def )
  done

fun map_prodWith :: " nat \<Rightarrow> nat \<Rightarrow>  nat" where 
"map_prodWith v n = (if n = 0 then 0 else (prod_encode(v,hd_nat n)) ## map_prodWith v (tl_nat n)) "

fun map_prodWith_acc :: " nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>  nat" where 
"map_prodWith_acc v acc n = (if n = 0 then acc else map_prodWith_acc v ((prod_encode(v,hd_nat n)) ## acc) (tl_nat n)) "

lemma map_prodWith_induct:
"map_prodWith_acc v acc n = map_acc (\<lambda>a. prod_encode (v,a)) acc n"
  apply(induct v acc n rule:map_prodWith_acc.induct)
  apply auto
  done

lemma submap_prodWith :
"map_prodWith v n = map_nat (\<lambda>a. prod_encode (v,a)) n"
  apply (induct v n rule:map_prodWith.induct)
  apply auto
  done

definition map_prodWith_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_prodWith_tail v n = reverse_nat (map_prodWith_acc v 0 n)"

lemma subtail_map_prodWith:
"map_prodWith_tail v n = map_prodWith v n"
  using map_prodWith_induct map_prodWith_tail_def submap_prodWith subtail_map by presburger

definition possible_assignments_for_nat
  :: "nat \<Rightarrow> nat \<Rightarrow> nat" 
  where "possible_assignments_for_nat P v \<equiv> map_prodWith v (the_nat (map_list_find_nat (nth_nat (Suc (Suc (Suc (Suc 0)))) P) v))"

definition possible_assignments_for_tail
  :: "nat \<Rightarrow> nat \<Rightarrow> nat" 
  where "possible_assignments_for_tail P v \<equiv> map_prodWith_tail v (the_nat (map_list_find_nat (nth_nat (Suc (Suc (Suc (Suc 0)))) P) v))"

lemma subtail_possible_assignments_for:
"possible_assignments_for_tail P v = possible_assignments_for_nat P v"
  using possible_assignments_for_nat_def possible_assignments_for_tail_def subtail_map_prodWith by presburger

lemma vdlist_plus_simp:"vdlist_plus_encode = prod_encode o (\<lambda>(v,d). (var_encode v, list_encode (map dom_encode d)))"
  apply auto
  done

lemma subnat_possible_assignments_for_pre:
  assumes "v \<in> set (variables_ofl P)"
  assumes " v \<in> set (variables_ofl P ) \<Longrightarrow> map_list_find  (range_ofl P)  v \<noteq> None"
  shows
"possible_assignments_for_nat (list_problem_plus_encode P) (var_encode v)
= sas_plus_assignment_list_encode (possible_assignments_for_list P v)"
  using inj_var assms
  apply auto
  apply (auto simp only: possible_assignments_for_nat_def 
submap_prodWith
              list_problem_plus_encode_def sub_nth nth.simps
sub_map_list_find_nat  inj_map_list_find[of var_encode]
            option_encode.simps the_nat.simps diff_Suc_1
 map_list_find_map  sub_map
possible_assignments_for_list_def
sas_plus_assignment_list_encode_def
vdlist_plus_simp simp flip:map_map 
)
  apply (auto simp add:comp_def)
  done

lemma inv_possible_assignments_for:
  assumes "is_valid_problem_sas_plus (list_problem_to_problem P)"
  assumes "v \<in> set (variables_ofl P)"
  shows "map_list_find  (range_ofl P)  v \<noteq> None"
proof -
  have "v \<in> set (sas_plus_problem.variables_of (list_problem_to_problem P))"
    using assms by auto
  hence "range_of (list_problem_to_problem P) v \<noteq> None" using assms apply (auto simp add:
    is_valid_problem_sas_plus_def ) 
    by (smt Ball_set_list_all)
  thus ?thesis by (auto simp add: sub_map_list_find)
qed

lemma subnat_possible_assignments_for:
  assumes "is_valid_problem_sas_plus (list_problem_to_problem P)"
  assumes "v \<in> set (variables_ofl P)"
  shows "possible_assignments_for_nat (list_problem_plus_encode P) (var_encode v)
= sas_plus_assignment_list_encode (possible_assignments_for_list P v)"
  using  subnat_possible_assignments_for_pre inv_possible_assignments_for assms by fastforce

definition all_possible_assignments_for_list
  :: "('variable, 'domain) sas_plus_list_problem \<Rightarrow> ('variable \<times> 'domain) list"
  where "all_possible_assignments_for_list \<Psi> 
    \<equiv> concat [possible_assignments_for_list \<Psi> v. v \<leftarrow> variables_ofl \<Psi>]" 

lemma sublist_all_possible_assignments_for:
" all_possible_assignments_for_list P =
all_possible_assignments_for (list_problem_to_problem P)"
  apply (auto simp add: all_possible_assignments_for_list_def all_possible_assignments_for_def
  sublist_possible_assignments_for)
  done

fun map_possible_assignments_for :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_possible_assignments_for P n = (if n = 0 then 0 else (possible_assignments_for_nat P  (hd_nat n)) ## map_possible_assignments_for P (tl_nat n))"

fun map_possible_assignments_for_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_possible_assignments_for_acc  P acc n = (if n = 0 then acc else map_possible_assignments_for_acc P ((possible_assignments_for_tail P  (hd_nat n)) ## acc ) (tl_nat n))"

lemma map_possible_assignments_for_induct :
"map_possible_assignments_for_acc  P acc n  = map_acc (possible_assignments_for_nat P) acc n"
  apply(induct P acc n rule:map_possible_assignments_for_acc.induct)
  apply (auto simp add: subtail_possible_assignments_for) 
  done

definition  map_possible_assignments_for_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_possible_assignments_for_tail P n = reverse_nat (map_possible_assignments_for_acc  P 0 n  ) "

lemma submap_possible_assignments_for:
"map_possible_assignments_for P n = map_nat (possible_assignments_for_nat P) n"
  apply(induct P n rule: map_possible_assignments_for.induct)
  apply auto
  done
lemma subtail_map_possible_assignments_for:
"map_possible_assignments_for_tail  P  n  = map_possible_assignments_for  P  n  "
  using map_possible_assignments_for_induct map_possible_assignments_for_tail_def
 submap_possible_assignments_for subtail_map by presburger

definition all_possible_assignments_for_nat::
   "nat \<Rightarrow> nat"
  where "all_possible_assignments_for_nat \<Psi> 
    \<equiv> concat_nat (map_possible_assignments_for \<Psi> (nth_nat 0 \<Psi>))" 

definition all_possible_assignments_for_tail::
   "nat \<Rightarrow> nat"
  where "all_possible_assignments_for_tail \<Psi> 
    \<equiv> concat_tail (map_possible_assignments_for_tail \<Psi> (nth_nat 0 \<Psi>))" 

lemma subtail_all_possible_assignments_for:
"all_possible_assignments_for_tail P = all_possible_assignments_for_nat P"
  using all_possible_assignments_for_nat_def all_possible_assignments_for_tail_def subtail_concat
 subtail_map_possible_assignments_for by presburger

lemma subnat_all_possible_assignments_for_map:
  assumes "is_valid_problem_sas_plus (list_problem_to_problem P)"
  shows " map (\<lambda>x. possible_assignments_for_nat (list_problem_plus_encode P) (var_encode x))
         (variables_ofl P) =
 map sas_plus_assignment_list_encode (map (\<lambda>x. possible_assignments_for_list P x)  (variables_ofl P))"
  apply (induct "variables_ofl P")
   apply simp
  using assms apply (auto simp del: list_problem_to_problem.simps)
  apply (auto simp add:subnat_possible_assignments_for simp del: list_problem_to_problem.simps)
  done

lemma subnat_all_possible_assignments_for:
  assumes "is_valid_problem_sas_plus (list_problem_to_problem P)"
  shows "all_possible_assignments_for_nat (list_problem_plus_encode P)
= sas_plus_assignment_list_encode (all_possible_assignments_for_list P)"
  using assms
  apply (auto simp only:all_possible_assignments_for_nat_def 
 submap_possible_assignments_for
list_problem_plus_encode_def
            sub_nth nth.simps sas_plus_assignment_list_encode_def[of "all_possible_assignments_for_list P"] )
  apply (auto simp only: sub_map map_map comp_def all_possible_assignments_for_list_def 
    subnat_all_possible_assignments_for_map
 simp flip:list_problem_plus_encode_def)
  apply (auto simp only: sas_plus_assignment_list_encode_def sub_concat map_concat simp flip: map_map comp_def[of _ "\<lambda>x. map sas_plus_assignment_encode (possible_assignments_for_list P x)"] )
  apply (auto simp only:map_map comp_def)
  done

definition state_to_strips_state_list
  :: "('variable, 'domain) sas_plus_list_problem 
    \<Rightarrow> ('variable, 'domain) assignment list 
    \<Rightarrow> (('variable, 'domain) assignment ,bool) assignment list" 
  where "state_to_strips_state_list \<Psi> s 
    \<equiv> let defined = filter (\<lambda>v. map_list_find s v \<noteq> None) (variables_ofl \<Psi>) in
      map (\<lambda>(v, a). ((v, a), the (map_list_find s v) = a)) 
        (concat [possible_assignments_for_list \<Psi> v. v \<leftarrow> defined])"

lemma sublist_state_to_strips_state:
"map_of (state_to_strips_state_list P s) =
state_to_strips_state (list_problem_to_problem P) (map_of s)"
  apply (auto simp add:state_to_strips_state_list_def sub_map_list_find
state_to_strips_state_def sublist_possible_assignments_for)
  done

declare map_list_find_nat.simps [simp del]
fun  map_find_eq:: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_find_eq s n = 
(if n = 0 then 0 else (prod_encode(hd_nat n, if the_nat (map_list_find_nat s (fst_nat (hd_nat n))) = snd_nat (hd_nat n) then 1 else 0)) ## map_find_eq s (tl_nat n))"

fun  map_find_eq_acc:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_find_eq_acc s acc n = 
  (if n = 0 then acc
   else map_find_eq_acc s ((prod_encode
    ( hd_nat n
    , if the_nat (map_list_find_nat s (fst_nat (hd_nat n))) = snd_nat (hd_nat n)
      then 1 else 0)
    ) ## acc ) (tl_nat n)
  )"

lemma map_find_eq_induct:
"map_find_eq_acc s acc n = map_acc  (\<lambda>va. prod_encode(va, if the_nat (map_list_find_nat s (fst_nat va)) = snd_nat va then 1 else 0)) acc n"
  apply(induct s acc n rule:map_find_eq_acc.induct)
  apply auto
  done

definition map_find_eq_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_find_eq_tail s n = reverse_nat (map_find_eq_acc s 0 n)"

lemma submap_find_eq: 
"map_find_eq s n =  map_nat (\<lambda>va. prod_encode(va, if the_nat (map_list_find_nat s (fst_nat va)) = snd_nat va then 1 else 0)) n "
  apply (induct s n rule: map_find_eq.induct)
  apply (auto simp del:map_list_find_nat.simps)
  done

lemma subtail_map_find_eq :
"map_find_eq_tail s n = map_find_eq s n"
  using map_find_eq_induct map_find_eq_tail_def submap_find_eq subtail_map by presburger



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




definition state_to_strips_state_nat
  :: "nat \<Rightarrow>nat \<Rightarrow>nat" 
  where "state_to_strips_state_nat \<Psi> s 
    \<equiv> let defined = filter_defined s (nth_nat 0 \<Psi>) in
      map_find_eq s (concat_nat (map_possible_assignments_for \<Psi> defined))"

definition state_to_strips_state_tail
  :: "nat \<Rightarrow>nat \<Rightarrow>nat" 
  where "state_to_strips_state_tail \<Psi> s 
    \<equiv> let defined = filter_defined_tail s (nth_nat 0 \<Psi>) in
      map_find_eq_tail s (concat_tail (map_possible_assignments_for_tail \<Psi> defined))"

lemma subtail_state_to_strips_state:
"state_to_strips_state_tail \<Psi> s = state_to_strips_state_nat \<Psi> s"
  using state_to_strips_state_nat_def state_to_strips_state_tail_def subtail_concat
 subtail_filter_defined subtail_map_find_eq subtail_map_possible_assignments_for by presburger

lemma subnat_state_to_strips_state_map:
  assumes "is_valid_problem_sas_plus (list_problem_to_problem P)"
shows
"map (\<lambda>x. possible_assignments_for_nat (list_problem_plus_encode P) (var_encode x))
           (filter (\<lambda>x. map_list_find s x \<noteq> None) (variables_ofl P))
= map  sas_plus_assignment_list_encode  ( map (possible_assignments_for_list P)
 (filter (\<lambda>x. map_list_find s x \<noteq> None) (variables_ofl P)) )"
  using assms apply (auto simp add: subnat_possible_assignments_for)
  done

lemma  possible_assignments_fst: "(x, b) \<in> set (possible_assignments_for_list P y) \<Longrightarrow> x = y"
  apply (auto simp add:possible_assignments_for_list_def)
  done

lemma subnat_state_to_strips_state:
  assumes "is_valid_problem_sas_plus (list_problem_to_problem P)"
  shows "state_to_strips_state_nat (list_problem_plus_encode P) (sas_plus_assignment_list_encode s)
= strips_assignment_list_encode (state_to_strips_state_list P s)"
  apply (auto simp only:state_to_strips_state_nat_def subfilter_defined
submap_possible_assignments_for      
submap_find_eq list_problem_plus_encode_def sub_nth nth.simps)
  apply (auto simp only: simp flip: list_problem_plus_encode_def)
  apply (auto simp only:       sub_filter  sas_plus_assignment_list_encode_def sas_plus_simp sub_map_list_find_nat option_encode_0
                    filter_map
            simp flip: map_map )
  using inj_var  apply (auto simp only:comp_def  inj_map_list_find  map_list_find_map_none 
subnat_possible_assignments_for Let_def sub_map map_map
)
  using assms apply(auto simp only:sub_map
state_to_strips_state_list_def
 sub_concat subnat_state_to_strips_state_map  sas_plus_list_simp simp flip:map_map map_concat)
  apply (auto simp only:map_map comp_def fst_sas_simp snd_sas_simp  inj_map_list_find
 strips_assignment_list_encode_def list_encode_eq Let_def
 )
  apply (induct "variables_ofl P")
   apply (auto simp del:list_problem_to_problem.simps)
  subgoal for a x y aa b ya
    apply (cases "map_list_find (map (\<lambda>(v, d). (v, dom_encode d)) s) aa")
    using possible_assignments_fst[of aa b P y] 
     apply (auto simp add: map_list_find_map_none map_list_find_map dom_inj_simp
          simp del:list_problem_to_problem.simps)
    done
 subgoal for a x y aa b ya
    apply (cases "map_list_find (map (\<lambda>(v, d). (v, dom_encode d)) s) aa")
    using possible_assignments_fst[of aa b P y] 
     apply (auto simp add: map_list_find_map_none map_list_find_map dom_inj_simp
          simp del:list_problem_to_problem.simps)
    done
  done

definition sasp_op_to_strips_list
  :: "('variable, 'domain) sas_plus_list_problem
    \<Rightarrow> ('variable, 'domain) sas_plus_operator
    \<Rightarrow> ('variable, 'domain) assignment strips_operator" 
  ("\<phi>\<^sub>O _ _" 99)
  where "sasp_op_to_strips_list \<Psi> op \<equiv> let
      pre = precondition_of op
      ; add = effect_of op
      ; delete = concat (map (\<lambda>(v,a). map (\<lambda>a'. (v, a')) (filter ((\<noteq>) a) (the (map_list_find (range_ofl \<Psi> )v)))) (effect_of op))
    in STRIPS_Representation.operator_for pre add delete"

lemma sublist_sasp_op_to_strips:
"sasp_op_to_strips_list P op = sasp_op_to_strips (list_problem_to_problem P) op"
  apply (auto simp add:sasp_op_to_strips_list_def  sasp_op_to_strips_def sub_map_list_find)
  done

fun operator_for_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"operator_for_nat pre add delete = pre ## add ## delete ##0 "

definition operator_for_tail  :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"operator_for_tail pre add delete = operator_for_nat pre add delete "

lemma subtail_operator_for:
"operator_for_tail pre add delete = operator_for_nat pre add delete "
  using operator_for_tail_def by fastforce

lemma sub_operator_for : "operator_for_nat (sas_plus_assignment_list_encode pre) (sas_plus_assignment_list_encode add) (sas_plus_assignment_list_encode delete)
= strips_operator_encode (operator_for pre add delete)"
  apply (auto simp add: sub_cons cons0 simp del: list_encode.simps)
  done


fun filter_diff_snd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"filter_diff_snd n xs = (if xs = 0 then 0 else if (hd_nat xs) \<noteq> snd_nat n then (hd_nat xs) ## filter_diff_snd n (tl_nat xs) else filter_diff_snd n (tl_nat xs))"

fun filter_diff_snd_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"filter_diff_snd_acc n acc xs = (if xs = 0 then acc else if (hd_nat xs) \<noteq> snd_nat n then filter_diff_snd_acc n  ((hd_nat xs) ## acc) (tl_nat xs) else filter_diff_snd_acc n acc (tl_nat xs))"

lemma filter_diff_snd_induct : 
"filter_diff_snd_acc n acc xs = filter_acc ((\<noteq>) (snd_nat n)) acc xs"
  apply(induct n acc xs rule:filter_diff_snd_acc.induct)
  apply auto
  done

definition filter_diff_snd_tail :: "nat \<Rightarrow> nat \<Rightarrow>nat" where 
"filter_diff_snd_tail n xs = reverse_nat (filter_diff_snd_acc n 0 xs)"

lemma subfilter_diff_snd :
"filter_diff_snd n xs = filter_nat ((\<noteq>) (snd_nat n)) xs"
  apply (induct n xs rule:filter_diff_snd.induct)
  apply (auto)
  done

lemma subtail_filter_diff_snd :
"filter_diff_snd_tail n xs = filter_diff_snd n xs "
  using filter_diff_snd_induct filter_diff_snd_tail_def subfilter_diff_snd
 subtail_filter by presburger

fun map_prod_fst :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_prod_fst n xs = (if xs = 0 then 0 else (prod_encode(fst_nat n,hd_nat xs)) ## map_prod_fst n (tl_nat xs))"

fun map_prod_fst_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_prod_fst_acc n acc xs = (if xs = 0 then acc else map_prod_fst_acc n ((prod_encode(fst_nat n,hd_nat xs)) ## acc) (tl_nat xs))"

lemma submap_prod_fst:
"map_prod_fst n xs =  map_nat (\<lambda>a'. prod_encode(fst_nat n, a')) xs"
  apply (induct n xs rule: map_prod_fst.induct)
  apply (auto)
  done

lemma map_prod_fst_induct:
"map_prod_fst_acc n acc xs = map_acc (\<lambda>a'. prod_encode(fst_nat n, a')) acc xs"
  apply(induct n acc xs rule: map_prod_fst_acc.induct)
  apply auto
  done

definition map_prod_fst_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_prod_fst_tail n xs = reverse_nat (map_prod_fst_acc n 0 xs)"

lemma subtail_map_prod_fst:
"map_prod_fst_tail n xs = map_prod_fst n xs"
  using map_prod_fst_induct map_prod_fst_tail_def submap_prod_fst subtail_map by presburger

fun map_sasp_op_to_strips:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
" map_sasp_op_to_strips P xs = (if xs=0 then 0 else (
 map_prod_fst (hd_nat xs) (filter_diff_snd (hd_nat xs) (the_nat (map_list_find_nat (nth_nat (Suc (Suc (Suc (Suc 0)))) P) (fst_nat (hd_nat xs))
)))) ##  map_sasp_op_to_strips P (tl_nat xs)) "

fun map_sasp_op_to_strips_acc:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
" map_sasp_op_to_strips_acc P acc xs = (if xs=0 then acc else  map_sasp_op_to_strips_acc P ( (
 map_prod_fst (hd_nat xs) (filter_diff_snd (hd_nat xs) (the_nat (map_list_find_nat (nth_nat (Suc (Suc (Suc (Suc 0)))) P) (fst_nat (hd_nat xs))
)))) ## acc) (tl_nat xs)) "

lemma map_sasp_op_to_strips_induct :
"map_sasp_op_to_strips_acc P acc xs = map_acc  (\<lambda>n. map_prod_fst n (filter_diff_snd n (the_nat (map_list_find_nat (nth_nat (Suc (Suc (Suc (Suc 0)))) P ) (fst_nat n))))) acc xs"
  apply(induct P acc xs rule:map_sasp_op_to_strips_acc.induct)
  apply auto
  done

lemma submap_sasp_op_to_strips:
"map_sasp_op_to_strips P xs = map_nat (\<lambda>n. map_prod_fst n (filter_diff_snd n (the_nat (map_list_find_nat (nth_nat (Suc (Suc (Suc (Suc 0)))) P ) (fst_nat n))))) xs "
  apply (induct P xs rule: map_sasp_op_to_strips.induct)
  apply auto
  done

definition  map_sasp_op_to_strips_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_sasp_op_to_strips_tail P xs = reverse_nat (map_sasp_op_to_strips_acc  P 0 xs)"

lemma subtail_map_sasp_op_to_strips:
"map_sasp_op_to_strips_tail P xs = map_sasp_op_to_strips P xs"
  using map_sasp_op_to_strips_induct map_sasp_op_to_strips_tail_def submap_sasp_op_to_strips subtail_map by presburger

definition sasp_op_to_strips_nat
  :: "nat \<Rightarrow>nat \<Rightarrow> nat " 
  where "sasp_op_to_strips_nat \<Psi> op \<equiv> let
      pre = nth_nat 0 op
      ; add = nth_nat (Suc 0)  op
      ; delete = concat_nat (map_sasp_op_to_strips \<Psi>  (nth_nat (Suc 0) op))
    in operator_for_nat pre add delete"

definition sasp_op_to_strips_tail
  :: "nat \<Rightarrow>nat \<Rightarrow> nat " 
  where "sasp_op_to_strips_tail \<Psi> op \<equiv> let
      pre = nth_nat 0 op
      ; add = nth_nat (Suc 0)  op
      ; delete = concat_tail (map_sasp_op_to_strips_tail \<Psi>  (nth_nat (Suc 0) op))
    in operator_for_tail pre add delete"

lemma subtail_sasp_op_to_strips:
"sasp_op_to_strips_tail P op = sasp_op_to_strips_nat P op"
  using operator_for_tail_def sasp_op_to_strips_nat_def sasp_op_to_strips_tail_def subtail_concat
 subtail_map_sasp_op_to_strips by presburger



lemma subnat_sasp_op_to_strips_map:
  assumes "\<forall>(v,d)\<in> set (effect_of op). map_list_find (range_ofl P) v \<noteq> None"
  shows
"map (\<lambda>x. map_nat (\<lambda>a'. prod_encode (var_encode (fst x), a'))
                            (filter_nat ((\<noteq>) (dom_encode (snd x)))
                              (the_nat
                                (option_encode
                                  (map_list_find
                                    (map (\<lambda>(v, d).
                                             (var_encode v, list_encode (map dom_encode d)))
                                      (range_ofl P))
                                    (var_encode (fst x)))))))
                  (effect_of op) =
map (\<lambda>(v,d). map_nat (\<lambda>a'. prod_encode (var_encode v, a'))
                            (filter_nat ((\<noteq>) (dom_encode d))
                             (list_encode (map dom_encode (the (map_list_find (range_ofl P)  v))))))
                  (effect_of op)

"
  apply (induct "effect_of op")
  using inj_var
   apply  (auto simp del:map_nat.simps filter_nat.simps the_nat.simps )
  apply (auto simp only: inj_map_list_find[of var_encode])
  subgoal for a b x ax bx
    apply (cases "map_list_find (range_ofl P) ax")
    using assms apply 
(auto simp add:  map_list_find_map_none   simp del:map_nat.simps filter_nat.simps the_nat.simps
)
    subgoal for y
    apply (auto simp add:  map_list_find_map)
      done
    done
  done

lemma subnat_sasp_op_to_strips_map2: 
 "(\<lambda>(v, d).
                         list_encode
                          (map (\<lambda>a'. prod_encode (var_encode v, a'))
                            (filter ((\<noteq>) (dom_encode d))
                              (map dom_encode (the (map_list_find (range_ofl P) v))))))
= list_encode o (\<lambda>(v,d). map (\<lambda>a'. prod_encode (var_encode v, a'))
                            (filter ((\<noteq>) (dom_encode d))
                              (map dom_encode (the (map_list_find (range_ofl P) v)))))"
  apply (auto)
  done
lemma subnat_sasp_op_to_strips_map3:
"(\<lambda>(v, d).
                         map sas_plus_assignment_encode
                          (map (Pair v) (filter ((\<noteq>) d) (the (map_list_find (range_ofl P) v)))))
= map sas_plus_assignment_encode o (\<lambda>(v,d). map (Pair v) (filter ((\<noteq>) d) (the (map_list_find (range_ofl P) v))) )"
  apply auto
  done
lemma subnat_sasp_op_to_strips_inv:
  assumes  "is_valid_problem_sas_plus (list_problem_to_problem P)"  "op \<in> set (operators_ofl P)"
  shows  "\<forall>(v,d)\<in> set (effect_of op). map_list_find (range_ofl P) v \<noteq> None"
  using assms
  apply (auto simp add: is_valid_problem_sas_plus_def is_valid_operator_sas_plus_def)
  by (smt case_prodD is_valid_operator_sas_plus_then(3) list_all_iff sas_plus_problem.select_convs(1) sub_map_list_find)

lemma subnat_sasp_op_to_strips_pre:
  assumes "\<forall>(v,d)\<in> set (effect_of op). map_list_find (range_ofl P) v \<noteq> None"
  shows   "sasp_op_to_strips_nat (list_problem_plus_encode P) (operator_plus_encode op) 
= 
strips_operator_encode (sasp_op_to_strips_list P op)"
  apply (auto simp only:sasp_op_to_strips_nat_def operator_plus_encode_def sub_nth nth.simps
subfilter_diff_snd  submap_sasp_op_to_strips  submap_prod_fst         
list_problem_plus_encode_def sub_map_list_find_nat vdlist_plus_simp
sas_plus_assignment_list_encode_def sub_map 

 simp flip: map_map )
  using inj_var apply (auto simp only: map_map comp_def fst_sas_simp snd_sas_simp

)
  using assms apply (auto simp only:subnat_sasp_op_to_strips_map sub_filter sub_map 
subnat_sasp_op_to_strips_map2  sub_concat simp flip: map_map
)
  apply (auto simp only:filter_map comp_def dom_inj_simp map_map simp flip:
sas_plus_assignment_encode.simps)
  apply (auto simp only: simp flip: comp_def map_map)
  apply (auto simp only: comp_def)
  apply (auto simp only: subnat_sasp_op_to_strips_map3
sasp_op_to_strips_list_def
  Let_def sub_operator_for simp flip: map_map map_concat
sas_plus_assignment_list_encode_def
)
  done

lemma subnat_sasp_op_to_strips:
  assumes  "is_valid_problem_sas_plus (list_problem_to_problem P)"  "op \<in> set (operators_ofl P)"
  shows   "sasp_op_to_strips_nat (list_problem_plus_encode P) (operator_plus_encode op)
= 
strips_operator_encode (sasp_op_to_strips_list P op)"
  using assms  subnat_sasp_op_to_strips_pre  subnat_sasp_op_to_strips_inv by blast

definition problem_for_list
  :: "'variable list 
  \<Rightarrow> 'variable strips_operator list 
  \<Rightarrow> ('variable,bool) assignment list  
  \<Rightarrow> ('variable,bool) assignment list
  \<Rightarrow> ('variable) strips_list_problem"
  where "problem_for_list vs ops I gs \<equiv> \<lparr> 
    variables_of = vs
    , operators_of = ops
    , initial_of = I
    , goal_of = gs \<rparr>" 

lemma sublist_problem_for :
"strips_list_problem_to_problem (problem_for_list vs ops I gs) = 
problem_for vs ops (map_of I) (map_of gs)"
  apply (auto simp add:problem_for_list_def)
  done

definition sas_plus_problem_to_strips_problem_list
  :: "('variable, 'domain) sas_plus_list_problem \<Rightarrow> ('variable, 'domain) assignment strips_list_problem" 
  ("\<phi> _ " 99)
  where "sas_plus_problem_to_strips_problem_list \<Psi> \<equiv> let 
      vs =  concat (map (possible_assignments_for_list \<Psi>)(variables_ofl \<Psi>))
      ; ops = map (sasp_op_to_strips_list \<Psi>) (operators_ofl \<Psi>)
      ; I = state_to_strips_state_list \<Psi> (initial_ofl \<Psi>)
      ; G = state_to_strips_state_list \<Psi> (goal_ofl \<Psi>)
    in problem_for_list vs ops I G"

lemma sublist_sas_plus_problem_to_strips_problem:
"strips_list_problem_to_problem (sas_plus_problem_to_strips_problem_list P) =
sas_plus_problem_to_strips_problem (list_problem_to_problem P)"
  apply (auto simp only: Let_def
sublist_possible_assignments_for
sas_plus_problem_to_strips_problem_def
list_problem_to_problem.simps
sas_plus_list_problem.simps
sas_plus_problem.simps

  sas_plus_problem_to_strips_problem_list_def   
sublist_problem_for sublist_sasp_op_to_strips sublist_state_to_strips_state )
  apply (auto simp add:sublist_sasp_op_to_strips sublist_possible_assignments_for simp flip: list_problem_to_problem.simps)
  apply (meson sublist_possible_assignments_for)
  done
definition problem_for_nat
  :: "nat 
  \<Rightarrow> nat 
  \<Rightarrow> nat  
  \<Rightarrow> nat
  \<Rightarrow> nat"
  where "problem_for_nat vs ops I gs \<equiv> vs ## ops ## I ## gs ## 0 "

definition problem_for_tail:: "nat 
  \<Rightarrow> nat 
  \<Rightarrow> nat  
  \<Rightarrow> nat
  \<Rightarrow> nat" where 
"problem_for_tail vs ops I gs  = problem_for_nat vs ops I gs "

lemma subtail_problem_for:
"problem_for_tail vs ops I gs  = problem_for_nat vs ops I gs "
  using problem_for_tail_def by presburger

lemma subnat_problem_for: 
"problem_for_nat (sas_plus_assignment_list_encode vs) (strips_operator_list_encode ops)
(strips_assignment_list_encode I) (strips_assignment_list_encode gs)
= 
 strips_list_problem_encode(problem_for_list vs ops I gs)
 "
  apply (auto simp only: problem_for_nat_def sub_cons cons0 problem_for_list_def
strips_list_problem_encode.simps strips_list_problem.simps) done

fun maps_sasp_op_to_strips :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"maps_sasp_op_to_strips P xs = (if xs =0 then 0 else (sasp_op_to_strips_nat P (hd_nat xs)) 
## maps_sasp_op_to_strips P (tl_nat xs))"

fun maps_sasp_op_to_strips_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"maps_sasp_op_to_strips_acc P acc xs = (if xs =0 then acc else maps_sasp_op_to_strips_acc P ( (sasp_op_to_strips_tail P (hd_nat xs)) 
## acc) (tl_nat xs))"

lemma maps_sasp_op_to_strips_induct:
"maps_sasp_op_to_strips_acc P acc xs = map_acc (sasp_op_to_strips_nat P) acc xs"
  apply(induct P acc xs rule:maps_sasp_op_to_strips_acc.induct)
  apply (auto simp add:subtail_sasp_op_to_strips)
  done

definition maps_sasp_op_to_strips_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"maps_sasp_op_to_strips_tail P xs = reverse_nat (maps_sasp_op_to_strips_acc P 0 xs)"

lemma sub_maps_sasp_op_to_strips:
"maps_sasp_op_to_strips P xs = map_nat (sasp_op_to_strips_nat P) xs"
  apply (induct P xs rule:maps_sasp_op_to_strips.induct)
  apply (auto)
  done

lemma subtail_maps_sasp_op_to_strips:
"maps_sasp_op_to_strips_tail P xs = maps_sasp_op_to_strips P xs"
  using maps_sasp_op_to_strips_induct maps_sasp_op_to_strips_tail_def 
sub_maps_sasp_op_to_strips subtail_map by presburger  


definition sas_plus_problem_to_strips_problem_nat
  :: "nat\<Rightarrow>nat" 
  where "sas_plus_problem_to_strips_problem_nat \<Psi> \<equiv> let 
      vs =  concat_nat (map_possible_assignments_for \<Psi>(nth_nat 0 \<Psi>))
      ; ops = maps_sasp_op_to_strips \<Psi> (nth_nat (Suc 0) \<Psi>)
      ; I = state_to_strips_state_nat \<Psi> (nth_nat (Suc (Suc 0)) \<Psi>)
      ; G = state_to_strips_state_nat \<Psi> (nth_nat (Suc (Suc (Suc 0))) \<Psi>)
    in problem_for_nat vs ops I G"

definition sas_plus_problem_to_strips_problem_tail
  :: "nat\<Rightarrow>nat" 
  ("\<phi> _ " 99)
  where "sas_plus_problem_to_strips_problem_tail \<Psi> \<equiv> let 
      vs =  concat_tail (map_possible_assignments_for_tail \<Psi>(nth_nat 0 \<Psi>))
      ; ops = maps_sasp_op_to_strips_tail \<Psi> (nth_nat (Suc 0) \<Psi>)
      ; I = state_to_strips_state_tail \<Psi> (nth_nat (Suc (Suc 0)) \<Psi>)
      ; G = state_to_strips_state_tail \<Psi> (nth_nat (Suc (Suc (Suc 0))) \<Psi>)
    in problem_for_tail vs ops I G"

lemma subtail_sas_plus_problem_to_strips_problem:
"sas_plus_problem_to_strips_problem_tail P =  sas_plus_problem_to_strips_problem_nat P "
  using problem_for_tail_def sas_plus_problem_to_strips_problem_nat_def 
sas_plus_problem_to_strips_problem_tail_def subtail_concat subtail_map_possible_assignments_for
 subtail_maps_sasp_op_to_strips subtail_state_to_strips_state by presburger

lemma  subnat_sas_plus_problem_to_strips_problem_map:
  assumes  "is_valid_problem_sas_plus (list_problem_to_problem P)"
  shows  "map (\<lambda>x. possible_assignments_for_nat (list_problem_plus_encode P)
                             (var_encode x))
                   (variables_ofl P)
  = map sas_plus_assignment_list_encode (map (possible_assignments_for_list P) (variables_ofl P))"
  using subnat_all_possible_assignments_for_map assms by blast

lemma  subnat_sas_plus_problem_to_strips_problem_map2:
  assumes  "is_valid_problem_sas_plus (list_problem_to_problem P)"
  shows  "map (\<lambda>x. sasp_op_to_strips_nat (list_problem_plus_encode P)
                        (operator_plus_encode x))
              (operators_ofl P)
  = map strips_operator_encode (map (sasp_op_to_strips_list P) (operators_ofl P))"
  using assms subnat_sasp_op_to_strips
  by auto

lemma subnat_sas_plus_problem_to_strips_problem:
  assumes  "is_valid_problem_sas_plus (list_problem_to_problem P)"
  shows "sas_plus_problem_to_strips_problem_nat (list_problem_plus_encode P)
 =  strips_list_problem_encode (sas_plus_problem_to_strips_problem_list P)"
  apply (auto simp only: sas_plus_problem_to_strips_problem_nat_def
list_problem_plus_encode_def sub_nth nth.simps submap_possible_assignments_for 
 sub_maps_sasp_op_to_strips
)
  using assms  apply (auto simp only: sub_map
              subnat_possible_assignments_for map_map comp_def 
              subnat_sasp_op_to_strips
subnat_state_to_strips_state 
 simp flip: list_problem_plus_encode_def)
  apply (auto simp only:subnat_sas_plus_problem_to_strips_problem_map sas_plus_list_simp 
sub_concat 
simp flip: map_map map_concat )
  apply (auto simp only: 
 simp flip: sas_plus_assignment_list_encode_def)
  apply (auto simp only:  subnat_sas_plus_problem_to_strips_problem_map2 simp flip: strips_operator_list_encode_def)
  apply (auto simp only: Let_def  subnat_problem_for sas_plus_problem_to_strips_problem_list_def )
  done



      
end