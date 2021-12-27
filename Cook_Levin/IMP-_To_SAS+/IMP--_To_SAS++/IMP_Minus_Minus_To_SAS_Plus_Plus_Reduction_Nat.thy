theory IMP_Minus_Minus_To_SAS_Plus_Plus_Reduction_Nat
  imports 
    Primitives IMP_Minus_Minus_To_SAS_Plus_Plus_State_Translations_Nat  IMP_Minus_Minus_Subprograms_Nat
 IMP_Minus_Minus_To_SAS_Plus_Plus_Reduction  
begin                               
definition domain_nat :: "nat" where
"domain_nat = list_encode [prod_encode(0,0), prod_encode(0,1)]"

definition domain_tail :: "nat " where "domain_tail = domain_nat"

lemma subtail_domain  : "domain_tail = domain_nat" using domain_tail_def by auto

lemma sub_domain: "domain_nat = list_encode (map domain_element_encode domain)"
  apply (auto simp add:domain_nat_def)
  done

definition pc_to_com_nat :: "nat\<Rightarrow> nat" where
"pc_to_com_nat l =(if fst_nat(snd_nat(hd_nat l)) = 1 then snd_nat (snd_nat (hd_nat l)) 
                  else  0##0)"

definition pc_to_com_tail ::" nat \<Rightarrow> nat" where 
"pc_to_com_tail l = pc_to_com_nat l"

lemma subtail_pc_to_com:
"pc_to_com_tail l = pc_to_com_nat l" using pc_to_com_tail_def by auto

lemma sub_pc_to_com :
  "pc_to_com_nat (sas_assignment_list_encode l) = comm_encode (pc_to_com l)"
  apply (cases l)
  apply (auto simp only: pc_to_com_nat_def sas_assignment_list_encode_def sub_hd 
              pc_to_com_def list.map head.simps sas_assignment_encode.simps
                    sub_snd snd_def nth.simps 
                  split:list.splits)
  apply(simp add:fst_nat_def snd_nat_def prod_decode_def prod_decode_aux.simps cons_def)
      
  subgoal for a b l
    apply (cases b)
     apply (auto simp only: domain_element_encode.simps sub_snd snd_def sub_fst cons0)
     apply auto
    done
  done

declare nth_nat.simps[simp del]

fun map_com_to_operators:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_com_to_operators c c2 n = (if n = 0 then 0 else 
 (let c1' = pc_to_com_nat (nth_nat (Suc 0) (hd_nat n)) in  
        (list_update_nat (nth_nat 0 (hd_nat n)) 0 (prod_encode (0,prod_encode(1,c))))##
        (list_update_nat (nth_nat (Suc 0) (hd_nat n)) 0 (prod_encode(0, prod_encode(1, 2 ##c1'##c2##0))))##0 )
## map_com_to_operators c c2 (tl_nat n)
)"

fun map_com_to_operators_acc:: " nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_com_to_operators_acc c c2 acc n = (if n = 0 then acc else map_com_to_operators_acc c c2 
 ((let c1' = pc_to_com_tail (nth_nat (Suc 0) (hd_nat n)) in  
        (list_update_tail (nth_nat 0 (hd_nat n)) 0 (prod_encode (0,prod_encode(1,c))))##
        (list_update_tail (nth_nat (Suc 0) (hd_nat n)) 0 (prod_encode(0, prod_encode(1, 2 ##c1'##c2##0))))##0 )
## acc) (tl_nat n)
)"

lemma map_com_to_operators_induct:
"map_com_to_operators_acc c c2 acc n = map_acc(\<lambda> op. 
    (let c1' = pc_to_com_nat (nth_nat (Suc 0) op) in  
        (list_update_nat (nth_nat 0 op) 0 (prod_encode (0,prod_encode(1,c))))##
        (list_update_nat (nth_nat (Suc 0) op) 0 (prod_encode(0, prod_encode(1, 2 ##c1'##c2##0))))##0 ))
acc n "
  apply(induct c c2 acc n rule:map_com_to_operators_acc.induct)
  apply(auto simp add: subtail_pc_to_com subtail_list_update)
  done

definition map_com_to_operators_tail :: "nat => nat => nat => nat" where 
"map_com_to_operators_tail c c2 n =  reverse_nat (map_com_to_operators_acc c c2 0 n)"

lemma submap_com_to_operators:
"map_com_to_operators c c2 n =
 map_nat (\<lambda> op. 
    (let c1' = pc_to_com_nat (nth_nat (Suc 0) op) in  
        (list_update_nat (nth_nat 0 op) 0 (prod_encode (0,prod_encode(1,c))))##
        (list_update_nat (nth_nat (Suc 0) op) 0 (prod_encode(0, prod_encode(1, 2 ##c1'##c2##0))))##0 )) n
 "
  apply (induct c c2 n rule:map_com_to_operators.induct)
  apply auto
  done

lemma subtail_map_com_to_operators:
"map_com_to_operators_tail c c2 n = map_com_to_operators c c2 n"
  using  submap_com_to_operators  map_com_to_operators_tail_def
 map_com_to_operators_induct subtail_map by presburger

fun map_com_to_operators2 :: "nat \<Rightarrow> nat" where 
" map_com_to_operators2 n = (if n = 0 then 0 else (prod_encode(Suc (hd_nat n), prod_encode(0,0)))##  map_com_to_operators2 (tl_nat n))"


lemma submap_com_to_operators2: 
" map_com_to_operators2 n =  map_nat (\<lambda>v. prod_encode(Suc v, prod_encode(0,0))) n"
  apply (induct n rule:map_com_to_operators2.induct)
  apply auto
  done

fun map_com_to_operators2_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
" map_com_to_operators2_acc acc n = (if n = 0 then acc else map_com_to_operators2_acc
((prod_encode(Suc (hd_nat n), prod_encode(0,0)))## acc )(tl_nat n))"

lemma map_com_to_operators2_induct: 
"map_com_to_operators2_acc acc n = map_acc (\<lambda>v. prod_encode(Suc v, prod_encode(0,0))) acc n"
  apply(induct acc n rule:map_com_to_operators2_acc.induct)
apply auto
  done

definition map_com_to_operators2_tail :: "nat => nat" where 
"map_com_to_operators2_tail n =  reverse_nat (map_com_to_operators2_acc 0 n)"

lemma subtail_map_com_to_operators2:
"map_com_to_operators2_tail  n = map_com_to_operators2 n"
  using  submap_com_to_operators2  map_com_to_operators2_tail_def
 map_com_to_operators2_induct subtail_map by presburger

fun  map_com_to_operators3 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_com_to_operators3 i c1 n  = (if n =0 then 0 else ((((prod_encode(0, i))## (prod_encode(Suc (hd_nat n), prod_encode(0,1)))##0)## 
         ((prod_encode(0, prod_encode(1, c1)))##0)## 0)) ##map_com_to_operators3 i c1 (tl_nat n))"

fun  map_com_to_operators3_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_com_to_operators3_acc  i c1 acc n  = (if n =0 then acc else map_com_to_operators3_acc  i c1  (((((prod_encode(0, i))## (prod_encode(Suc (hd_nat n), prod_encode(0,1)))##0)## 
         ((prod_encode(0, prod_encode(1, c1)))##0)## 0)) ##acc) (tl_nat n))"

lemma submap_com_to_operators3:
"map_com_to_operators3 i c1 n = map_nat (\<lambda> v. 
      ( ((prod_encode(0, i))## (prod_encode(Suc v, prod_encode(0,1)))##0)## 
         ((prod_encode(0, prod_encode(1, c1)))##0)## 0)) n"
  apply (induct i c1 n rule:map_com_to_operators3.induct)
  apply auto
  done
lemma map_com_to_operators3_induct:
"map_com_to_operators3_acc  i c1 acc n = map_acc  (\<lambda> v. 
      ( ((prod_encode(0, i))## (prod_encode(Suc v, prod_encode(0,1)))##0)## 
         ((prod_encode(0, prod_encode(1, c1)))##0)## 0)) acc n"
  apply(induct  i c1 acc n  rule:map_com_to_operators3_acc.induct)
  apply auto
  done

definition map_com_to_operators3_tail :: " nat \<Rightarrow> nat \<Rightarrow> nat => nat" where 
"map_com_to_operators3_tail i c1 n =  reverse_nat (map_com_to_operators3_acc i c1 0 n)"

lemma subtail_map_com_to_operators3:
"map_com_to_operators3_tail i c1 n = map_com_to_operators3 i c1 n"
  using  submap_com_to_operators3  map_com_to_operators3_tail_def
 map_com_to_operators3_induct subtail_map by presburger

fun  map_com_to_operators4 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>nat" where 
"map_com_to_operators4 i j n = (if n=0 then 0 else ((((prod_encode(0, i)) ## (prod_encode (Suc (hd_nat n), prod_encode(0,1) )) ##0)) ## 
         (((prod_encode(0, j))##0) ## 0 )) ## map_com_to_operators4 i j (tl_nat n))"

lemma submap_com_to_operators4:
"map_com_to_operators4 i j n =  map_nat (\<lambda> v. 
       (((prod_encode(0, i)) ## (prod_encode (Suc v, prod_encode(0,1) )) ##0)) ## 
         (((prod_encode(0, j))##0) ## 0 )) n "
  apply (induct i j n rule:map_com_to_operators4.induct)
  apply auto
  done
fun  map_com_to_operators4_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>nat" where 
"map_com_to_operators4_acc i j acc n = (if n=0 then acc else map_com_to_operators4_acc i j  (((((prod_encode(0, i)) ## (prod_encode (Suc (hd_nat n), prod_encode(0,1) )) ##0)) ## 
         (((prod_encode(0, j))##0) ## 0 )) ## acc) (tl_nat n))"

lemma map_com_to_operators4_induct:
"map_com_to_operators4_acc i j acc n = map_acc(\<lambda> v. 
      ( (((prod_encode(0, i)) ## (prod_encode (Suc v, prod_encode(0,1) )) ##0)) ## 
         (((prod_encode(0, j))##0) ## 0 ))) acc n"
  apply(induct i j acc n rule:map_com_to_operators4_acc.induct)
  apply auto
  done


definition map_com_to_operators4_tail :: " nat \<Rightarrow> nat \<Rightarrow> nat => nat" where 
"map_com_to_operators4_tail i j n =  reverse_nat (map_com_to_operators4_acc i j 0 n)"

lemma subtail_map_com_to_operators4:
"map_com_to_operators4_tail i j n = map_com_to_operators4 i j n"
  using  submap_com_to_operators4  map_com_to_operators4_tail_def
 map_com_to_operators4_induct subtail_map by presburger


datatype com_op = Bot "operator list" |
                  SKIP |
                  Assign vname bit |
                  Seq_0 com com |
                  Seq_f com com "operator list"|
                  If "vname list" com com |
                  While "vname list" com

fun com_op_encode :: "com_op \<Rightarrow> nat" where 
"com_op_encode SKIP = list_encode [0]"|
"com_op_encode (Assign v b) = list_encode [1,vname_encode v, bit_encode b]"|
"com_op_encode (Seq_0 c1 c2) = list_encode [2,comm_encode c1, comm_encode c2]"|
"com_op_encode (If v c1 c2) = list_encode [3, vname_list_encode v, comm_encode c1 ,comm_encode c2] "|
"com_op_encode (While v c) = list_encode [4,vname_list_encode v, comm_encode c] "|
"com_op_encode (Seq_f c1 c2 op) = list_encode [5, comm_encode c1, comm_encode c2, list_encode (map operator_encode op)]"|
"com_op_encode (Bot x) = list_encode [6, list_encode (map operator_encode x)]"

fun com_op_decode :: "nat \<Rightarrow> com_op" where 
"com_op_decode n = (case list_decode n of 
    [0] \<Rightarrow> SKIP |
    [Suc 0,v,b] \<Rightarrow> Assign (vname_decode v) (bit_decode b)|
    [Suc (Suc 0), c1, c2] \<Rightarrow> Seq_0 (comm_decode c1) (comm_decode c2)|
    [Suc (Suc (Suc 0)),v ,c1 ,c2] \<Rightarrow> If (vname_list_decode v) (comm_decode c1) (comm_decode c2)|
    [Suc (Suc (Suc (Suc 0))), v, c] \<Rightarrow> While (vname_list_decode v) (comm_decode c)|
    [Suc (Suc (Suc (Suc (Suc 0)))),c1,c2,op] \<Rightarrow> Seq_f (comm_decode c1) (comm_decode c2) (map operator_decode (list_decode op))|
    [Suc (Suc (Suc (Suc (Suc (Suc 0))))),op] \<Rightarrow> Bot (map operator_decode (list_decode op))
)"

lemma com_op_id: 
"com_op_decode (com_op_encode x) = x"
  apply(induct x)
        apply(auto simp add: operator_id comp_def vname_id comm_id 
          vname_list_id simp del: comm_decode.simps )
  done

fun push_to_stack_op :: "com \<Rightarrow> com_op list \<Rightarrow> com_op list" where 
"push_to_stack_op com.SKIP s = SKIP#s "|
"push_to_stack_op (com.Assign v n) s = Assign v n #s"|
"push_to_stack_op (com.Seq c1 c2)  s = Seq_0 c1 c2 # s "|
"push_to_stack_op (com.If v c1 c2) s = If v c1 c2 #s"|
"push_to_stack_op (com.While v c) s = While v c #s"

definition push_to_stack_op_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"push_to_stack_op_nat c s = (c ## s)"

lemma sub_push_to_stack_op :
"push_to_stack_op_nat (comm_encode c) (list_encode (map com_op_encode  s))
 = list_encode (map com_op_encode (push_to_stack_op c s)) "
  apply(cases c)
      apply(auto simp add:  push_to_stack_op_nat_def 
sub_cons  simp del:list_encode.simps)
  done

fun add_res_to_stack_op :: "operator list \<Rightarrow> com_op list \<Rightarrow> com_op list" where 
"add_res_to_stack_op op [] = [Bot op]"|
"add_res_to_stack_op op (Seq_0 c1 c2 # s) = Seq_f c1 c2 op # s"|
"add_res_to_stack_op op s = s"

definition add_res_to_stack_op_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"add_res_to_stack_op_nat op s = (if s = 0 then (6 ## op ## 0)##0
else if hd_nat (hd_nat s) = 2 then (5 ## (nth_nat (Suc 0) (hd_nat s)) ## (nth_nat (Suc (Suc 0)) (hd_nat s)) ## op ## 0)## (tl_nat s)
else s)"

lemma list_encode_0:"(list_encode s = 0) = (s= [])"
  using list_encode_eq by fastforce

lemma sub_add_res_to_stack:
"add_res_to_stack_op_nat (list_encode (map operator_encode op)) (list_encode (map com_op_encode s))
 = list_encode (map com_op_encode (add_res_to_stack_op op s))"
   apply(cases s)
  apply (auto simp add: sub_hd add_res_to_stack_op_nat_def list_encode_0  sub_cons cons0  simp del: list_encode.simps  )
  subgoal for a xs
    apply(cases a)
      apply (auto simp add: sub_nth sub_tl sub_hd list_encode_0  sub_cons cons0  simp del: list_encode.simps  )
    done
  subgoal for a xs
    apply(cases a)
      apply (auto simp add: sub_nth sub_tl sub_hd list_encode_0  sub_cons cons0  simp del: list_encode.simps  )
    done
  done

fun size_e :: "com \<Rightarrow> nat" where 
"size_e com.SKIP = 1 "|
"size_e (com.Assign v a)  = 1"|
"size_e (com.Seq c1 c2) = Suc (size_e c1)"|
"size_e (com.If v c1 c2) = 1"|
"size_e (com.While v c) = 1"

fun stack_size_rev :: "com_op list \<Rightarrow> nat" where 
"stack_size_rev (Seq_0 c1 c2 # s ) = (if s = [] then Suc (2 * size_e c1) else 
  Suc (stack_size_rev s))"|
"stack_size_rev (Bot x # s) = (if s = [] then 0 else Suc (stack_size_rev s))"|
"stack_size_rev (_ #s) = (if s = [] then 1 else Suc (stack_size_rev s))"|
"stack_size_rev [] = 1"

fun stack_size :: "com_op list \<Rightarrow> nat" where 
"stack_size s = stack_size_rev (rev s)"

lemma 
stack_size_mono :" x \<noteq> [] \<Longrightarrow>y \<noteq>  [] \<Longrightarrow> stack_size_rev y < stack_size_rev x
 \<Longrightarrow> stack_size_rev (s @ y) < stack_size_rev (s @ x) "
  apply(induct s )
   apply auto
  subgoal for a xs
    apply (cases a)
           apply (auto)
    done
  done

lemma stack_size_0:"(stack_size_rev x = 0) = (\<exists>n. x = [Bot n]) "
  apply(cases x)
   apply auto
  subgoal for a xs
    apply (cases a)
           apply (auto split :if_splits)
    done
 subgoal for a xs
    apply (cases a)
           apply (auto split :if_splits)
   done
  done

lemma add_res_less:
"\<forall>x. s \<noteq> [Bot x] \<and> a \<noteq> Bot x \<Longrightarrow> stack_size (add_res_to_stack_op r s) < stack_size (a#s) "
  apply(cases s)
   apply auto
   apply (cases a)
  apply (auto simp add: stack_size_mono)
  subgoal for a xs
    apply (cases a)
    using stack_size_mono stack_size_0 nat_less_le    apply (auto )
    done
  done

function com_to_operators_stack :: "com_op list \<Rightarrow> operator list" where 
"com_to_operators_stack (Bot x # s) = x "|
"com_to_operators_stack (SKIP# s) = com_to_operators_stack (add_res_to_stack_op [] s)"|
"com_to_operators_stack (Assign v b # s) = com_to_operators_stack (add_res_to_stack_op
     [\<lparr> precondition_of = [(PC, PCV (com.Assign v b))], 
      effect_of = [(PC, PCV com.SKIP), (VN v, EV b)]\<rparr>] s )" |
"com_to_operators_stack (Seq_0 c1 c2 #s) = 
(if c1 = com.SKIP then com_to_operators_stack ( add_res_to_stack_op  [\<lparr> precondition_of = [(PC, PCV (c1 ;; c2))],
                                                   effect_of = [(PC, PCV c2)]\<rparr>] s)
else com_to_operators_stack (push_to_stack_op c1 (Seq_0 c1 c2 #s))
)"|
"com_to_operators_stack (Seq_f c1 c2 ops # s) = 
com_to_operators_stack (add_res_to_stack_op ( map (\<lambda> op. 
    (let c1' = pc_to_com (effect_of op) in 
      \<lparr> precondition_of = 
        list_update (precondition_of op) 0 (PC, PCV (com.Seq c1 c2)),
        effect_of = 
        list_update (effect_of op) 0 (PC, PCV (com.Seq c1' c2))\<rparr>)) ops) s)"|
"com_to_operators_stack (If vs c1 c2 #s) = 
com_to_operators_stack (add_res_to_stack_op   (let i = PCV (IF vs\<noteq>0 THEN c1 ELSE c2)
   in  \<lparr> precondition_of = (PC, i) # map (\<lambda>v. (VN v, EV Zero)) (remdups vs), 
        effect_of = [(PC, PCV c2)]\<rparr> 
      # map (\<lambda> v. 
      \<lparr> precondition_of = [(PC, i), (VN v, EV One)], 
         effect_of = [(PC, PCV c1)]\<rparr>) vs)   s )" |
"com_to_operators_stack (While vs c # s) = 
com_to_operators_stack (add_res_to_stack_op  (let i = PCV (com.While vs c) ;
  j = PCV (com.Seq c (com.While vs c)); k = PCV (com.SKIP) in 
    \<lparr> precondition_of = (PC, i) # map (\<lambda>v. (VN v, EV Zero)) (remdups vs), 
        effect_of = [(PC, k)]\<rparr> 
      # map (\<lambda> v. 
      \<lparr> precondition_of = [(PC, i), (VN v, EV One)], 
         effect_of = [(PC, j)]\<rparr>) vs) s)"|
"com_to_operators_stack [] = []"
  by pat_completeness auto
termination
proof (relation "measure stack_size",goal_cases)
case 1
then show ?case by auto
next
  case (2 s)
  then show ?case using add_res_less apply auto
    by (metis add_res_to_stack_op.simps butlast.simps(2) butlast_snoc com_op.distinct 
neq0_conv not_Cons_self2 rev_singleton_conv stack_size_0)

    
next
  case (3 v b s)
   then show ?case using add_res_less apply auto
     by (smt One_nat_def Zero_not_Suc add_res_to_stack_op.simps(3) 
last_ConsL last_snoc less_nat_zero_code linorder_neqE_nat rev_singleton_conv 
stack_size_0 stack_size_rev.simps(4))
      
next
  case (4 c1 c2 s)
  then show ?case using add_res_less apply auto
     by (smt One_nat_def Zero_not_Suc add_res_to_stack_op.simps
last_ConsL last_snoc less_nat_zero_code linorder_neqE_nat rev_singleton_conv 
stack_size_0 stack_size_rev.simps)

next
  case (5 c1 c2 s)
  then show ?case using stack_size_mono  by (cases c1) auto

next
  case (6 c1 c2 ops s)
  then show ?case using add_res_less apply auto
     by (smt One_nat_def Zero_not_Suc add_res_to_stack_op.simps
last_ConsL last_snoc less_nat_zero_code linorder_neqE_nat rev_singleton_conv 
stack_size_0 stack_size_rev.simps)
next
case (7 vs c1 c2 s)
then show ?case using add_res_less apply auto
     by (smt One_nat_def Zero_not_Suc add_res_to_stack_op.simps
last_ConsL last_snoc less_nat_zero_code linorder_neqE_nat rev_singleton_conv 
stack_size_0 stack_size_rev.simps)
next
  case (8 vs c s)
  then show ?case using add_res_less apply auto
     by (smt One_nat_def Zero_not_Suc add_res_to_stack_op.simps
last_ConsL last_snoc less_nat_zero_code linorder_neqE_nat rev_singleton_conv 
stack_size_0 stack_size_rev.simps)
qed


lemma com_to_operators_stack_correct:
"com_to_operators_stack (push_to_stack_op c s) = com_to_operators_stack (add_res_to_stack_op (
com_to_operators c) s)"
  apply(induct c  arbitrary:s rule: com_to_operators.induct)
      apply auto
  done

definition com_to_operators_t :: "com  \<Rightarrow> operator list" where 
"com_to_operators_t c = com_to_operators_stack (push_to_stack_op c [])"

lemma subtailnat_com_to_operators:
"com_to_operators_t c = com_to_operators c"
  using com_to_operators_stack_correct[of c "[]"]
  apply(auto simp add: com_to_operators_t_def)
  done


function (domintros) com_to_operators_stack_nat :: "nat \<Rightarrow> nat" where 
"com_to_operators_stack_nat s = ( if s = 0 then 0 else let c = hd_nat s ; t = tl_nat s in  
(if hd_nat c = 0 then com_to_operators_stack_nat (add_res_to_stack_op_nat 0 t) else 
if hd_nat c = 1 then com_to_operators_stack_nat (add_res_to_stack_op_nat ((
                        ((prod_encode(0,prod_encode(1,c)))##0)
                        ##
                          (
                              (prod_encode(0,prod_encode(1,0##0)))
                                ##
                              (prod_encode(Suc (nth_nat (Suc 0) c),prod_encode(0,nth_nat (Suc (Suc 0)) c)))
                               ##0
                          )
                        ##0)##0) t)
else if hd_nat c = 2 then (let c1 = nth_nat (Suc 0) c; c2= nth_nat (Suc (Suc 0)) c in 
  (if c1 = 0##0 then  com_to_operators_stack_nat (add_res_to_stack_op_nat ( (((prod_encode(0,prod_encode(1,c)))##0)##((prod_encode(0,prod_encode(1,c2)))##0)##0)##0) t)
else  com_to_operators_stack_nat (push_to_stack_op_nat c1 s)))
else if hd_nat c = 3 then 
(let i = prod_encode (1, c); vs = nth_nat (Suc 0) c ; c1 = nth_nat (Suc (Suc 0)) c ; c2 = nth_nat (Suc (Suc (Suc 0))) c
   in com_to_operators_stack_nat (add_res_to_stack_op_nat (( ((prod_encode(0, i)) ## map_com_to_operators2_tail (remdups_tail vs))## 
        ((prod_encode(0, prod_encode(1, c2)))##0)## 0)
      ## map_com_to_operators3_tail i c1 vs ) t ) )
else  if hd_nat c = 4 then (let i = prod_encode(1,c) ;  vs = nth_nat (Suc 0) c ; c' = nth_nat (Suc (Suc 0)) c ; 
  j = prod_encode(1, (2##c'## c##0)); k = prod_encode(1, 0##0) in 
  com_to_operators_stack_nat (add_res_to_stack_op_nat (( ((prod_encode(0, i)) ##  map_com_to_operators2_tail (remdups_tail vs))## 
        (((prod_encode(0, k))##0))##0) 
      ## map_com_to_operators4_tail i j vs) t))
else if hd_nat c = 5 then 
(let ops = nth_nat (Suc (Suc (Suc 0))) c; c2 = nth_nat (Suc (Suc 0)) c ; c1 = nth_nat (Suc 0) c  in  com_to_operators_stack_nat (add_res_to_stack_op_nat  (map_com_to_operators_tail (2 ## c1 ##c2 ## 0) c2 ops) t))
else nth_nat (Suc 0) c
))
"  by pat_completeness auto
 




lemma push_stack_not_Nil :
"push_to_stack_op c s \<noteq> []"
  apply (cases c)
  apply auto
  done

lemma add_res_not_Nil : 
"add_res_to_stack_op c s \<noteq> []"
  apply (cases s)
   apply auto
  subgoal for a xs
    apply( cases a)
          apply auto
    done
  done
lemma Nil_is_map_op:
"[] = map operator_encode []"
  by  auto
lemma sas_singleton:"list_encode [sas_assignment_encode x] = sas_assignment_list_encode [x]"
  apply (auto simp add: sas_assignment_list_encode_def)
  done

lemma op_singleton:"[operator_encode x] = map operator_encode [x]"
  apply (auto)
  done

lemma sas_couple:"list_encode [sas_assignment_encode x,sas_assignment_encode y] = sas_assignment_list_encode [x,y]"
  apply (auto simp add: sas_assignment_list_encode_def)
  done
lemma operator_encode_simps: 
"list_encode [sas_assignment_list_encode x, sas_assignment_list_encode y] = operator_encode \<lparr>
  precondition_of = x, effect_of = y
\<rparr>"
  apply (auto simp add:operator_encode_def)
  done
lemma comm_inj_simps: "(comm_encode x= comm_encode y) = (x=y)"
  by (simp add: comm_inj inj_eq)


lemma sub_map_dec: "map_nat P xs = list_encode (map P (list_decode xs))"
  using sub_map list_decode_inverse by metis


lemma comm_encode_eq : "(comm_encode c1 = comm_encode c2) = (c1 = c2)"
  apply (cases c2)
  apply (induct c1 arbitrary:c2)
          apply (auto simp add:prod_encode_eq)
  apply (metis One_nat_def comm_encode.simps(2) comm_id list_encode.simps(1) list_encode.simps(2))
  apply (metis comm_encode.simps(3) comm_id list_encode.simps(1) list_encode.simps(2))
   apply (metis comm_encode.simps(4) comm_id list_encode.simps(1) list_encode.simps(2))
  by (metis comm_encode.simps(5) comm_id cons0 cons_def list_encode.simps(2))


  
lemma list_encode_empty:"(list_encode l = 0) =(l = [])"
  apply (auto)
  using list_encode_eq by force

lemma suc_eq: "(Suc i = Suc j) = (i=j) "
  by simp

lemma list_update_nat_zero: "list_update_nat 0 0 n = 0"
  apply auto
  done

lemma  simp_op_id:"\<lparr>sas_plus_operator.precondition_of =
                       sas_plus_operator.precondition_of a,
                       effect_of = effect_of a\<rparr> = a"
  by auto
lemma ev_zero_encode:"prod_encode (0,0) = domain_element_encode (EV Zero)"
  apply auto
  done
lemma com_to_operators_term:
"com_to_operators_stack_nat_dom (list_encode (map  com_op_encode s))"
proof (induct s rule: com_to_operators_stack.induct)
case (1 x s)
  then show ?case using com_to_operators_stack_nat.domintros[of 
        "list_encode
       (list_encode [6, list_encode (map operator_encode x)] # map com_op_encode s)"]
        apply(simp only: list.simps head.simps tail.simps com_op_encode.simps cons0 sub_cons sub_nth
                        nth.simps com_to_operators_stack.simps
                        add_res_not_Nil push_stack_not_Nil sub_hd sub_tl Let_def 
                   del: list_encode.simps )    
done
next
  case (2 s)
  then show ?case using com_to_operators_stack_nat.domintros[of 
        "list_encode
       (list_encode [0] # map com_op_encode s)"]
        apply(simp only: list.simps head.simps tail.simps com_op_encode.simps cons0 sub_cons sub_nth
                        nth.simps com_to_operators_stack.simps
                        add_res_not_Nil push_stack_not_Nil sub_hd sub_tl Let_def 
                   del: list_encode.simps )  
       apply (simp only: sub_add_res_to_stack list_encode_eq  Nil_is_map_op   flip: list_encode.simps  )
    apply simp
done
next
  case (3 v b s)
  then show ?case  using com_to_operators_stack_nat.domintros[of 
        "list_encode
       (list_encode [1, vname_encode v, bit_encode b] # map com_op_encode s)"]
        apply(simp only: One_nat_def non_empty_positive list.simps head.simps tail.simps com_op_encode.simps cons0 sub_cons sub_nth
                        nth.simps com_to_operators_stack.simps
                        add_res_not_Nil push_stack_not_Nil sub_hd sub_tl Let_def 
                   del: list_encode.simps ) 
         
  apply(simp only:   flip: comm_encode.simps One_nat_def del:list_encode.simps)
      apply (simp only:sub_hd  head.simps sub_cons cons0 sub_map sub_nth
                                      nth.simps  flip: domain_element_encode.simps  variable_encode.simps sas_assignment_encode.simps comm_encode.simps )
      apply (simp only: nth.simps  sub_hd sub_add_res_to_stack op_singleton operator_encode_simps  sas_singleton sas_couple  head.simps sub_cons cons0 sub_map sub_nth variable_encode.simps(1)
                                      nth.simps  flip:  domain_element_encode.simps  sas_assignment_encode.simps comm_encode.simps )
    done
next
  case (4 c1 c2 s)
  then show ?case  using com_to_operators_stack_nat.domintros[of 
        "list_encode
       (list_encode [2, comm_encode c1, comm_encode c2] # map com_op_encode s)"]
    apply (cases "c1=com.SKIP")
        apply(auto simp only: non_empty_positive list.simps head.simps tail.simps com_op_encode.simps cons0 sub_cons sub_nth
                        nth.simps com_to_operators_stack.simps
                        add_res_not_Nil push_stack_not_Nil sub_hd sub_tl Let_def  
                   simp del: list_encode.simps ) 
  apply( simp only:    flip: comm_encode.simps One_nat_def  del:list_encode.simps)
      apply (auto  simp only:sub_hd  head.simps sub_cons cons0 sub_map sub_nth
                                      nth.simps  simp flip:  domain_element_encode.simps  variable_encode.simps sas_assignment_encode.simps comm_encode.simps )[1]
      apply ( auto simp only: sub_hd sub_add_res_to_stack sub_push_to_stack_op op_singleton operator_encode_simps  sas_singleton sas_couple  head.simps sub_cons cons0 sub_map sub_nth variable_encode.simps(1)
                                      nth.simps   simp  flip:  domain_element_encode.simps  sas_assignment_encode.simps )
    apply (auto simp only:sub_push_to_stack_op sub_add_res_to_stack list_encode_0 comm_inj_simps simp flip: One_nat_def com_op_encode.simps(3) comm_encode.simps(1) list.map(2) split: if_splits)
    apply auto
    done
next
  case (5 c1 c2 ops s)
  then show ?case   using com_to_operators_stack_nat.domintros[of 
        "list_encode
       (list_encode  [5, comm_encode c1, comm_encode c2, list_encode (map operator_encode ops)] # map com_op_encode s)"]
        apply(simp only: list.simps head.simps tail.simps com_op_encode.simps cons0 sub_cons sub_nth
                        nth.simps com_to_operators_stack.simps
                        add_res_not_Nil push_stack_not_Nil sub_hd sub_tl Let_def 
                   del: list_encode.simps ) 
    apply(simp only:subtail_map_com_to_operators
        submap_com_to_operators   sub_nth nth.simps  flip: comm_encode.simps del:list_encode.simps)
      apply (simp only:sub_hd sub_list_update  head.simps sub_cons cons0 sub_map sub_nth
                                      nth.simps  flip: domain_element_encode.simps  variable_encode.simps sas_assignment_encode.simps comm_encode.simps del: list_encode.simps )
      apply (simp only:sub_hd sub_add_res_to_stack op_singleton operator_encode_simps  sas_singleton sas_couple  head.simps sub_cons cons0 sub_map sub_nth variable_encode.simps(1)
                                      nth.simps  flip:  domain_element_encode.simps  sas_assignment_encode.simps comm_encode.simps )
      apply (auto simp only: sub_hd list_encode_eq suc_eq list_encode_empty comm_encode_eq head.simps sub_cons cons0 sub_map sub_map_dec sub_nth com_to_operators.simps
                         sub_list_update sas_plus_operator.simps sas_assignment_list_encode_def list.map prod_encode_eq  nth.simps sub_pc_to_com Let_def comp_def operator_encode_def
  domain_element_encode.simps  variable_encode.simps  sas_assignment_encode.simps
    map_map list_encode_inverse subtail_remdups sub_remdups  comm_encode.simps submap_com_to_operators
  simp flip: comm_encode.simps
                          del: list_encode.simps hd_nat_def cons_def pc_to_com_nat_def map_nat.simps nth_nat.simps list_update_nat.simps split:if_splits)
  apply (auto simp only:sub_pc_to_com simp flip:  sas_assignment_list_encode_def  comm_encode.simps )
    apply (auto simp only:  operator_encode_simps sas_assignment_list_encode_def list.simps map_update 
            sas_assignment_encode.simps variable_encode.simps domain_element_encode.simps  simp flip:  sas_assignment_encode.simps sas_assignment_list_encode_def map_update  variable_encode.simps domain_element_encode.simps comm_encode.simps)
     apply (auto simp only:  simp flip:comp_def[of operator_encode 
"\<lambda>x.  \<lparr>sas_plus_operator.precondition_of = (sas_plus_operator.precondition_of x)
                           [variable_encode PC := (PC, PCV (_;; _))],
                           effect_of = (effect_of x)
                             [variable_encode PC := (PC, PCV (pc_to_com (effect_of x);; _))]\<rparr>"

 ] )
    apply(auto simp only:sub_add_res_to_stack simp_op_id simp flip: map_map)
    apply auto
    done

next
  case (6 vs c1 c2 s)
  then show ?case  using com_to_operators_stack_nat.domintros[of 
        "list_encode
       (list_encode   [3, list_encode (map vname_encode vs), comm_encode c1, comm_encode c2] # map com_op_encode s)"]
        apply(simp only: non_empty_positive subtail_remdups sub_remdups vname_list_encode_def list.simps head.simps tail.simps com_op_encode.simps cons0 sub_cons sub_nth
                        nth.simps com_to_operators_stack.simps
                        add_res_not_Nil push_stack_not_Nil sub_hd sub_tl Let_def 
                   del: list_encode.simps ) 
    apply(simp only:subtail_map_com_to_operators2
        submap_com_to_operators2  subtail_map_com_to_operators3
        submap_com_to_operators3   sub_nth nth.simps  flip: comm_encode.simps  vname_list_encode_def del:list_encode.simps)
      apply (simp only:sub_hd sub_list_update  head.simps sub_cons cons0 sub_map sub_nth
                                      nth.simps  flip: domain_element_encode.simps  variable_encode.simps sas_assignment_encode.simps comm_encode.simps del: list_encode.simps )
      apply (simp only:sub_hd sub_add_res_to_stack op_singleton operator_encode_simps  sas_singleton sas_couple  head.simps sub_cons cons0 sub_map sub_nth variable_encode.simps(1)
                                      nth.simps   variable_encode.simps  flip:  bit_encode.simps domain_element_encode.simps  sas_assignment_encode.simps comm_encode.simps )
    apply( simp only: bit_encode.simps  flip:One_nat_def domain_element_encode.simps)
    apply (simp only:  flip: bit_encode.simps)
  using vname_inj
   apply(simp only: remdups_map  map_map comp_def flip: variable_encode.simps sas_assignment_encode.simps)
  apply(simp only: ev_zero_encode  bit_encode.simps(1) cons0 sub_cons sub_map flip:  sas_assignment_encode.simps domain_element_encode.simps )
  apply (simp only:  flip: sas_assignment_encode.simps   variable_encode.simps  comp_def[of sas_assignment_encode "\<lambda>x. (VN x, EV Zero)"] map_map list.map(2))
   apply( simp only: sub_map vname_list_encode_def map_map comp_def sas_singleton sas_couple operator_encode_simps sub_cons flip: variable_encode.simps sas_assignment_encode.simps  sas_assignment_list_encode_def ) 
  apply( simp only: sub_add_res_to_stack flip: map_map list.map comp_def [of operator_encode "\<lambda>x. \<lparr>sas_plus_operator.precondition_of =
                                                [(PC, PCV (IF _\<noteq>0 THEN _ ELSE _)), (VN x, EV One)],
                                                effect_of = [(PC, PCV _)]\<rparr>" ])
  apply simp
 done
next
  case (7 vs c s)
  then show ?case  using com_to_operators_stack_nat.domintros[of 
        "list_encode
       (list_encode   [4, list_encode (map vname_encode vs), comm_encode c] # map com_op_encode s)"]
       apply(simp only: subtail_remdups sub_remdups vname_list_encode_def list.simps head.simps tail.simps com_op_encode.simps cons0 sub_cons sub_nth
                        nth.simps com_to_operators_stack.simps
                        add_res_not_Nil push_stack_not_Nil sub_hd sub_tl Let_def 
                   del: list_encode.simps ) 
    apply(simp only:subtail_map_com_to_operators4
        submap_com_to_operators4  subtail_map_com_to_operators2
        submap_com_to_operators2   sub_nth nth.simps  flip: comm_encode.simps  vname_list_encode_def del:list_encode.simps)
      apply (simp only:sub_hd sub_list_update  head.simps sub_cons cons0 sub_map sub_nth
                                      nth.simps  flip: domain_element_encode.simps  variable_encode.simps sas_assignment_encode.simps comm_encode.simps del: list_encode.simps )
      apply (simp only:sub_hd sub_add_res_to_stack op_singleton operator_encode_simps  sas_singleton sas_couple  head.simps sub_cons cons0 sub_map sub_nth variable_encode.simps(1)
                                      nth.simps   variable_encode.simps  flip:  bit_encode.simps domain_element_encode.simps  sas_assignment_encode.simps comm_encode.simps )
      apply( simp only: bit_encode.simps  flip:One_nat_def domain_element_encode.simps)
    apply (simp only:  flip: bit_encode.simps)
  using vname_inj
   apply(simp only: remdups_map  map_map comp_def flip: variable_encode.simps sas_assignment_encode.simps)
  apply(simp only: ev_zero_encode  bit_encode.simps(1) cons0 sub_cons sub_map flip:  sas_assignment_encode.simps domain_element_encode.simps )
  apply (simp only:  flip: sas_assignment_encode.simps   variable_encode.simps  comp_def[of sas_assignment_encode "\<lambda>x. (VN x, EV Zero)"] map_map list.map(2))
   apply( simp only: sub_map vname_list_encode_def map_map comp_def sas_singleton sas_couple operator_encode_simps sub_cons flip: variable_encode.simps sas_assignment_encode.simps  sas_assignment_list_encode_def )
  apply( simp only: sub_add_res_to_stack flip: map_map list.map(2) comp_def [of operator_encode "\<lambda>x.\<lparr>sas_plus_operator.precondition_of =
                                                     [(PC, PCV (WHILE _\<noteq>0 DO _ )), (VN x, EV One)],
                                                     effect_of = [(PC, PCV (_;; WHILE _\<noteq>0 DO _))]\<rparr>" ])
  apply simp
  done
next
  case 8
  then show ?case by (auto intro: com_to_operators_stack_nat.domintros)
qed

lemma sub_com_to_operators_stack:
" com_to_operators_stack_nat (list_encode (map  com_op_encode s))
= list_encode (map operator_encode(com_to_operators_stack s))"
proof (induct s rule: com_to_operators_stack.induct)
case (1 x s)
  then show ?case apply(subst com_to_operators_stack_nat.psimps)
    using  com_to_operators_term apply blast
        apply(simp only: list.simps head.simps tail.simps com_op_encode.simps cons0 sub_cons sub_nth
                        nth.simps com_to_operators_stack.simps
                        add_res_not_Nil push_stack_not_Nil sub_hd sub_tl Let_def 
                   del: list_encode.simps )    
    apply simp
done
next
  case (2 s)
  then show ?case  apply(subst com_to_operators_stack_nat.psimps)
    using  com_to_operators_term apply blast
        apply(simp only: list.simps head.simps tail.simps com_op_encode.simps cons0 sub_cons sub_nth
                        nth.simps com_to_operators_stack.simps
                        add_res_not_Nil push_stack_not_Nil sub_hd sub_tl Let_def 
                   del: list_encode.simps )  
       apply (simp only: sub_add_res_to_stack list_encode_eq  Nil_is_map_op   flip: list_encode.simps  )
    apply simp
done
next
  case (3 v b s)
  then show ?case  apply(subst com_to_operators_stack_nat.psimps)
    using  com_to_operators_term apply blast
        apply(simp only: list.simps head.simps tail.simps com_op_encode.simps cons0 sub_cons sub_nth
                        nth.simps com_to_operators_stack.simps
                        add_res_not_Nil push_stack_not_Nil sub_hd sub_tl Let_def 
                   del: list_encode.simps ) 
  apply(simp only:  flip: comm_encode.simps del:list_encode.simps)
      apply (simp only:sub_hd  head.simps sub_cons cons0 sub_map sub_nth
                                      nth.simps  flip: domain_element_encode.simps  variable_encode.simps sas_assignment_encode.simps comm_encode.simps )
      apply (simp only:sub_hd sub_add_res_to_stack op_singleton operator_encode_simps  sas_singleton sas_couple  head.simps sub_cons cons0 sub_map sub_nth variable_encode.simps(1)
                                      nth.simps  flip:  domain_element_encode.simps  sas_assignment_encode.simps comm_encode.simps )
    apply simp
    done
next
  case (4 c1 c2 s)
  then show ?case apply(subst com_to_operators_stack_nat.psimps)
    using  com_to_operators_term apply blast
    apply (cases "c1=com.SKIP")
        apply(auto simp only: list.simps head.simps tail.simps com_op_encode.simps cons0 sub_cons sub_nth
                        nth.simps com_to_operators_stack.simps
                        add_res_not_Nil push_stack_not_Nil sub_hd sub_tl Let_def 
                   del: list_encode.simps ) 
  apply(simp only:   flip: comm_encode.simps del:list_encode.simps)
      apply ( simp only:sub_hd  head.simps sub_cons cons0 sub_map sub_nth
                                      nth.simps   flip: domain_element_encode.simps  variable_encode.simps sas_assignment_encode.simps comm_encode.simps )
      apply ( simp only:sub_hd sub_add_res_to_stack op_singleton operator_encode_simps  sas_singleton sas_couple  head.simps sub_cons cons0 sub_map sub_nth variable_encode.simps(1)
                                      nth.simps   flip:  domain_element_encode.simps  sas_assignment_encode.simps comm_encode.simps )
     apply simp
    apply (auto simp only:sub_push_to_stack_op list_encode_0 comm_inj_simps simp flip: com_op_encode.simps(3) comm_encode.simps(1) list.map(2) split: if_splits)
    done
next
  case (5 c1 c2 ops s)
  then show ?case apply(subst com_to_operators_stack_nat.psimps)
    using  com_to_operators_term apply blast
        apply(simp only: list.simps head.simps tail.simps com_op_encode.simps cons0 sub_cons sub_nth
                        nth.simps com_to_operators_stack.simps
                        add_res_not_Nil push_stack_not_Nil sub_hd sub_tl Let_def 
                   del: list_encode.simps ) 
    apply(simp only:subtail_map_com_to_operators
        submap_com_to_operators   sub_nth nth.simps  flip: comm_encode.simps del:list_encode.simps)
      apply (simp only:sub_hd sub_list_update  head.simps sub_cons cons0 sub_map sub_nth
                                      nth.simps  flip: domain_element_encode.simps  variable_encode.simps sas_assignment_encode.simps comm_encode.simps del: list_encode.simps )
      apply (simp only:sub_hd sub_add_res_to_stack op_singleton operator_encode_simps  sas_singleton sas_couple  head.simps sub_cons cons0 sub_map sub_nth variable_encode.simps(1)
                                      nth.simps  flip:  domain_element_encode.simps  sas_assignment_encode.simps comm_encode.simps )
      apply (auto simp only: sub_hd list_encode_eq suc_eq list_encode_empty comm_encode_eq head.simps sub_cons cons0 sub_map sub_map_dec sub_nth com_to_operators.simps
                         sub_list_update sas_plus_operator.simps sas_assignment_list_encode_def list.map prod_encode_eq  nth.simps sub_pc_to_com Let_def comp_def operator_encode_def
  domain_element_encode.simps  variable_encode.simps  sas_assignment_encode.simps
    map_map list_encode_inverse subtail_remdups sub_remdups  comm_encode.simps submap_com_to_operators
  simp flip: comm_encode.simps
                          del: list_encode.simps hd_nat_def cons_def pc_to_com_nat_def map_nat.simps nth_nat.simps list_update_nat.simps split:if_splits)
  apply (auto simp only:sub_pc_to_com simp flip:  sas_assignment_list_encode_def  comm_encode.simps )
    apply (auto simp only:  operator_encode_simps sas_assignment_list_encode_def list.simps map_update 
            sas_assignment_encode.simps variable_encode.simps domain_element_encode.simps  simp flip:  sas_assignment_encode.simps sas_assignment_list_encode_def map_update  variable_encode.simps domain_element_encode.simps comm_encode.simps)
     apply (auto simp only:  simp flip:comp_def[of operator_encode 
"\<lambda>x.  \<lparr>sas_plus_operator.precondition_of = (sas_plus_operator.precondition_of x)
                           [variable_encode PC := (PC, PCV (_;; _))],
                           effect_of = (effect_of x)
                             [variable_encode PC := (PC, PCV (pc_to_com (effect_of x);; _))]\<rparr>"

 ] )
     apply(auto simp only:sub_add_res_to_stack simp_op_id simp flip: map_map)
    done

next
  case (6 vs c1 c2 s)
  then show ?case apply(subst com_to_operators_stack_nat.psimps)
    using  com_to_operators_term apply blast
        apply(simp only: subtail_remdups sub_remdups vname_list_encode_def list.simps head.simps tail.simps com_op_encode.simps cons0 sub_cons sub_nth
                        nth.simps com_to_operators_stack.simps
                        add_res_not_Nil push_stack_not_Nil sub_hd sub_tl Let_def 
                   del: list_encode.simps ) 
    apply(simp only:subtail_map_com_to_operators2
        submap_com_to_operators2  subtail_map_com_to_operators3
        submap_com_to_operators3   sub_nth nth.simps  flip: comm_encode.simps  vname_list_encode_def del:list_encode.simps)
      apply (simp only:sub_hd sub_list_update  head.simps sub_cons cons0 sub_map sub_nth
                                      nth.simps  flip: domain_element_encode.simps  variable_encode.simps sas_assignment_encode.simps comm_encode.simps del: list_encode.simps )
      apply (simp only:sub_hd sub_add_res_to_stack op_singleton operator_encode_simps  sas_singleton sas_couple  head.simps sub_cons cons0 sub_map sub_nth variable_encode.simps(1)
                                      nth.simps   variable_encode.simps  flip:  bit_encode.simps domain_element_encode.simps  sas_assignment_encode.simps comm_encode.simps )
   apply(subst (6) bit_encode.simps) 
   apply( simp only: flip: domain_element_encode.simps)
  using vname_inj
   apply(simp only: remdups_map  map_map comp_def flip: variable_encode.simps sas_assignment_encode.simps)
   apply(simp only: bit_encode.simps(1) cons0 sub_cons sub_map flip: domain_element_encode.simps comp_def[of sas_assignment_encode "\<lambda>x. (VN x, EV Zero)"] map_map list.map(2))
   apply( simp only: sub_map vname_list_encode_def map_map comp_def sas_singleton sas_couple operator_encode_simps sub_cons flip: variable_encode.simps sas_assignment_encode.simps  sas_assignment_list_encode_def ) 
  apply( simp only: sub_add_res_to_stack flip: map_map list.map(2) comp_def [of operator_encode "\<lambda>x. \<lparr>sas_plus_operator.precondition_of =
                                                [(PC, PCV (IF _\<noteq>0 THEN _ ELSE _)), (VN x, EV One)],
                                                effect_of = [(PC, PCV _)]\<rparr>" ])
   apply simp
done
next
  case (7 vs c s)
  then show ?case apply(subst com_to_operators_stack_nat.psimps)
    using  com_to_operators_term apply blast
        apply(simp only: subtail_remdups sub_remdups vname_list_encode_def list.simps head.simps tail.simps com_op_encode.simps cons0 sub_cons sub_nth
                        nth.simps com_to_operators_stack.simps
                        add_res_not_Nil push_stack_not_Nil sub_hd sub_tl Let_def 
                   del: list_encode.simps ) 
    apply(simp only:subtail_map_com_to_operators4
        submap_com_to_operators4  subtail_map_com_to_operators2
        submap_com_to_operators2   sub_nth nth.simps  flip: comm_encode.simps  vname_list_encode_def del:list_encode.simps)
      apply (simp only:sub_hd sub_list_update  head.simps sub_cons cons0 sub_map sub_nth
                                      nth.simps  flip: domain_element_encode.simps  variable_encode.simps sas_assignment_encode.simps comm_encode.simps del: list_encode.simps )
      apply (simp only:sub_hd sub_add_res_to_stack op_singleton operator_encode_simps  sas_singleton sas_couple  head.simps sub_cons cons0 sub_map sub_nth variable_encode.simps(1)
                                      nth.simps   variable_encode.simps  flip:  bit_encode.simps domain_element_encode.simps  sas_assignment_encode.simps comm_encode.simps )
   apply(subst (10) bit_encode.simps) 
   apply( simp only: flip: domain_element_encode.simps)
  using vname_inj
   apply(simp only: remdups_map map_map comp_def flip: variable_encode.simps sas_assignment_encode.simps)
   apply(simp only: bit_encode.simps(1) cons0 sub_cons sub_map flip: domain_element_encode.simps comp_def[of sas_assignment_encode "\<lambda>x. (VN x, EV Zero)"] map_map list.map(2))
   apply( simp only: sub_map vname_list_encode_def map_map comp_def sas_singleton sas_couple operator_encode_simps sub_cons flip: variable_encode.simps sas_assignment_encode.simps  sas_assignment_list_encode_def ) 
  apply( simp only: sub_add_res_to_stack flip: map_map list.map(2) comp_def [of operator_encode "\<lambda>x.\<lparr>sas_plus_operator.precondition_of =
                                                     [(PC, PCV (WHILE _\<noteq>0 DO _ )), (VN x, EV One)],
                                                     effect_of = [(PC, PCV (_;; WHILE _\<noteq>0 DO _))]\<rparr>" ])
  apply simp
  done
next
  case 8
  then show ?case apply(subst com_to_operators_stack_nat.psimps)
    using  com_to_operators_term apply blast
    apply auto
    done
qed

                
        
        
     

definition com_to_operators_nat:: "nat \<Rightarrow> nat" where 
"com_to_operators_nat c = com_to_operators_stack_nat (push_to_stack_op_nat c 0)"

lemma subnat_com_to_operators: 
"com_to_operators_nat (comm_encode c) = list_encode (map operator_encode (com_to_operators_t c)) "
  by (metis com_to_operators_nat_def com_to_operators_t_def list.simps(8) list_encode.simps(1)
 push_stack_not_Nil sub_com_to_operators_stack sub_push_to_stack_op)

lemma sub_com_to_operators:
"com_to_operators_nat (comm_encode c) = list_encode (map operator_encode (com_to_operators c))"
  by (simp add: subnat_com_to_operators subtailnat_com_to_operators)

definition com_to_operators_tail:: "nat \<Rightarrow> nat" where
"com_to_operators_tail c = com_to_operators_nat c"

lemma subtail_com_to_operators:
"com_to_operators_tail c = com_to_operators_nat c"
  by (simp add: com_to_operators_tail_def)
fun map_coms_to_operators :: "nat \<Rightarrow> nat" where 
"map_coms_to_operators n = (if n = 0 then 0 else (com_to_operators_nat (hd_nat n)) ## map_coms_to_operators (tl_nat n))"

fun map_coms_to_operators_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_coms_to_operators_acc acc  n = (if n = 0 then acc else map_coms_to_operators_acc ((com_to_operators_tail (hd_nat n)) ## acc) (tl_nat n))"

lemma map_coms_to_operators_induct:
"map_coms_to_operators_acc acc  n = map_acc  com_to_operators_nat acc n"
  apply(induct acc n rule: map_coms_to_operators_acc.induct)
  apply (auto simp add: subtail_com_to_operators)
  done


lemma submap_coms_to_operators : 
"map_coms_to_operators n  = map_nat com_to_operators_nat n "
  apply (induct n rule:map_coms_to_operators.induct)
  apply auto
  done

definition  map_coms_to_operators_tail:: "nat \<Rightarrow> nat" where 
"map_coms_to_operators_tail n = reverse_nat (map_coms_to_operators_acc 0 n)"

lemma subtail_map_coms_to_operators:
"map_coms_to_operators_tail n = map_coms_to_operators n"
  
  using map_coms_to_operators_induct map_coms_to_operators_tail_def submap_coms_to_operators 
subtail_map by auto

definition coms_to_operators_nat :: "nat \<Rightarrow> nat" where
"coms_to_operators_nat cs = concat_nat (map_coms_to_operators cs)"

definition coms_to_operators_tail :: "nat \<Rightarrow> nat" where
"coms_to_operators_tail cs = concat_tail (map_coms_to_operators_tail cs)"
lemma subtail_coms_to_operators:
"coms_to_operators_tail cs = coms_to_operators_nat cs"
  by (simp add: coms_to_operators_nat_def
 coms_to_operators_tail_def subtail_concat subtail_map_coms_to_operators)

lemma sub_coms_to_operators:
    "coms_to_operators_nat (list_encode( map comm_encode cs)) = 
          list_encode (map operator_encode (coms_to_operators cs)) "
  apply (auto simp only: coms_to_operators_nat_def sub_map map_map comp_def
        sub_com_to_operators submap_coms_to_operators )
  apply (auto simp only: coms_to_operators_def sub_concat map_concat simp flip: 
comp_def[of "list_encode" "%x.(map operator_encode (com_to_operators x))"]
            map_map)
  apply (auto simp add: comp_def)
  done



definition imp_minus_minus_to_sas_plus_list::
"com \<Rightarrow> (vname,bit) assignment list  \<Rightarrow> (vname,bit) assignment list \<Rightarrow> 
      (variable,domain_element) sas_plus_list_problem" where 
"imp_minus_minus_to_sas_plus_list c I G = (let cs = enumerate_subprograms c ; 
  initial_vs = restrict_list I (enumerate_variables c) ;
  goal_vs = restrict_list G (enumerate_variables c) ;
  pc_d = map (\<lambda> i. PCV i) cs in
    \<lparr> variables_ofl = PC # (map VN (enumerate_variables c)),
      operators_ofl = coms_to_operators cs, 
      initial_ofl = imp_minus_state_to_sas_plus_list (c, initial_vs),
      goal_ofl = imp_minus_state_to_sas_plus_list (com.SKIP, goal_vs),
      range_ofl = (PC, pc_d)#(map (\<lambda> v. (VN v, domain)) (enumerate_variables c))\<rparr>)"

lemma sublist_imp_minus_minus_to_sas_plus:
"list_problem_to_problem (imp_minus_minus_to_sas_plus_list c I G) = 
    imp_minus_minus_to_sas_plus c (map_of I) (map_of G)"
  apply (auto simp add:
          imp_minus_minus_to_sas_plus_list_def list_problem_to_problem.simps
          sub_restrict_list Let_def sas_plus_problem.simps sas_plus_list_problem.simps
            sublist_imp_minus_state_to_sas_plus 
            imp_minus_minus_to_sas_plus_def  )
  done

fun map_PCV :: "nat \<Rightarrow> nat" where 
"map_PCV n = (if n = 0 then 0 else  (prod_encode(1, hd_nat n))## map_PCV (tl_nat n))"

lemma submap_PCV : 
"map_PCV n =  map_nat (\<lambda> i. prod_encode(1, i)) n "
  apply (induct n rule: map_PCV.induct)
  apply (auto)
  done

fun map_PCV_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_PCV_acc acc n = (if n = 0 then acc else map_PCV_acc ((prod_encode(1, hd_nat n))## acc) (tl_nat n))"

lemma map_PCV_induct: 
"map_PCV_acc acc n = map_acc (\<lambda> i. prod_encode(1, i)) acc n"
  apply(induct acc n rule:map_PCV_acc.induct)
  apply auto done

definition map_PCV_tail :: "nat \<Rightarrow> nat" where 
"map_PCV_tail n = reverse_nat (map_PCV_acc 0 n)"

lemma subtail_map_PCV:
"map_PCV_tail n =  map_PCV n"
  using map_PCV_tail_def map_PCV_induct submap_PCV subtail_map by presburger

fun map_Suc :: "nat \<Rightarrow> nat" where 
"map_Suc n = (if n = 0 then 0 else (Suc(hd_nat n)) ## (map_Suc (tl_nat n)))"

fun map_Suc_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_Suc_acc acc n = (if n = 0 then acc else map_Suc_acc ((Suc(hd_nat n)) ## acc) (tl_nat n))"

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

definition map_Suc_tail :: "nat \<Rightarrow> nat" where 
"map_Suc_tail n = reverse_nat (map_Suc_acc 0 n)"

lemma subtail_map_Suc:
"map_Suc_tail n = map_Suc n"
  
  using map_Suc_induct map_Suc_tail_def submap_Suc subtail_map by auto

fun map_domain :: "nat\<Rightarrow> nat" where 
"map_domain n = (if n = 0 then 0 else (prod_encode(Suc (hd_nat n), domain_nat)) ## map_domain (tl_nat n))"

fun map_domain_acc :: " nat \<Rightarrow> nat\<Rightarrow> nat" where 
"map_domain_acc acc n = (if n = 0 then acc else  map_domain_acc ((prod_encode(Suc (hd_nat n), domain_nat)) ## acc) (tl_nat n))"

lemma submap_domain :
"map_domain n = map_nat (\<lambda> v. (prod_encode(Suc v, domain_nat))) n"
  apply (induct n rule:map_domain.induct)
  apply auto
  done
lemma map_domain_induct: 
"map_domain_acc acc n = map_acc   (\<lambda> v. (prod_encode(Suc v, domain_nat))) acc n"
  apply(induct acc n rule:map_domain_acc.induct)
  apply auto
  done

definition map_domain_tail :: "nat  \<Rightarrow> nat" where 
"map_domain_tail n = reverse_nat (map_domain_acc 0 n )"

lemma subtail_map_domain:
"map_domain_tail n = map_domain n"
  using map_domain_induct map_domain_tail_def submap_domain subtail_map by presburger

definition imp_minus_minus_to_sas_plus_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"imp_minus_minus_to_sas_plus_nat c I G = (let cs = enumerate_subprograms_nat c ; 
  initial_vs = restrict_nat I (enumerate_variables_nat c) ;
  goal_vs = restrict_nat G (enumerate_variables_nat c) ;
  pc_d = map_PCV cs in
   (0 ## (map_Suc (enumerate_variables_nat c)))## 
      (coms_to_operators_nat cs) ## 
      (imp_minus_state_to_sas_plus_nat (prod_encode (c, initial_vs)))##
      (imp_minus_state_to_sas_plus_nat (prod_encode (0##0, goal_vs)))##
      ((prod_encode(0, pc_d))##(map_domain (enumerate_variables_nat c)))##0 )"

definition imp_minus_minus_to_sas_plus_tail:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"imp_minus_minus_to_sas_plus_tail c I G = (let cs = enumerate_subprograms_tail c ; 
  initial_vs = restrict_tail I (enumerate_variables_tail c) ;
  goal_vs = restrict_tail G (enumerate_variables_tail c) ;
  pc_d = map_PCV_tail cs in
   (0 ## (map_Suc_tail (enumerate_variables_tail c)))## 
      (coms_to_operators_tail cs) ## 
      (imp_minus_state_to_sas_plus_tail (prod_encode (c, initial_vs)))##
      (imp_minus_state_to_sas_plus_tail (prod_encode (0##0, goal_vs)))##
      ((prod_encode(0, pc_d))##(map_domain_tail (enumerate_variables_tail c)))##0 )"

lemma subtail_imp_minus_minus_to_sas_plus:
"imp_minus_minus_to_sas_plus_tail c I G = imp_minus_minus_to_sas_plus_nat c I G"
  apply (auto simp only:  imp_minus_minus_to_sas_plus_tail_def imp_minus_minus_to_sas_plus_nat_def
      subtail_enumerate_subprograms subtail_map_PCV subtail_map_Suc subtail_enumerate_variables
      subtail_coms_to_operators subtail_map_domain subtail_imp_minus_state_to_sas_plus 
subtail_restrict
) done

lemma subnat_imp_minus_minus_to_sas_plus:
"imp_minus_minus_to_sas_plus_nat (comm_encode c) 
            (imp_assignment_list_encode I) (imp_assignment_list_encode G) =
 list_problem_encode (imp_minus_minus_to_sas_plus_list c I G)"
  apply (auto simp only: imp_minus_minus_to_sas_plus_nat_def
      sub_enumerate_subprograms sub_restrict_nat sub_enumerate_variables sub_map
      sub_cons cons0 Let_def submap_PCV submap_Suc submap_domain
)
  apply (auto simp only: vname_list_encode_def sub_map sub_cons
      sub_coms_to_operators sub_domain
   subnat_imp_minus_state_to_sas_plus map_map comp_def
        simp flip: comm_encode.simps(1) cilist_encode.simps variable_encode.simps(2))
  apply (auto simp only: subnat_imp_minus_state_to_sas_plus list_problem_encode_def  sas_plus_list_problem.simps 
              imp_minus_minus_to_sas_plus_list_def Let_def list.simps simp flip: comp_def map_map )
  apply (auto simp only: domain_element_encode.simps sas_assignment_list_encode_def map_map[of "vdlist_encode"] map_map[of "domain_element_encode"] comp_def vdlist_encode.simps variable_encode.simps)
  done

lemma sub_imp_minus_minus_to_sas:
"list_problem_to_problem (list_problem_decode (imp_minus_minus_to_sas_plus_nat (comm_encode c) 
            (imp_assignment_list_encode I) (imp_assignment_list_encode G)))
= imp_minus_minus_to_sas_plus c (map_of I) (map_of G)"
  apply (auto simp only: subnat_imp_minus_minus_to_sas_plus sublist_imp_minus_minus_to_sas_plus list_problem_id)
  done

   
  


      
        
        


    
end