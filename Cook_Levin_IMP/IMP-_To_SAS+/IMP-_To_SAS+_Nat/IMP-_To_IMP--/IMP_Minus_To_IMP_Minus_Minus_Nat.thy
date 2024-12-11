theory IMP_Minus_To_IMP_Minus_Minus_Nat 
  imports  "IMP-_To_SAS+_HOL.IMP_Minus_To_IMP_Minus_Minus"  IMP_Minus_Max_Constant_Nat Binary_Operations_Nat 
begin


fun map_var_bit_to_var:: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_var_bit_to_var v n = (if n =0 then 0 else (var_bit_to_var_nat (prod_encode (v,hd_nat n)))## map_var_bit_to_var v (tl_nat n)  )"

fun map_var_bit_to_var_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_var_bit_to_var_acc acc v n = (if n =0 then acc 
else map_var_bit_to_var_acc ((var_bit_to_var_nat (prod_encode (v,hd_nat n)))## acc) v (tl_nat n)  )"

lemma submap_var_bit_to_var :
"map_var_bit_to_var v n =  map_nat (\<lambda>i. var_bit_to_var_nat (prod_encode (v,i))) n "
  apply (induct v n rule:map_var_bit_to_var.induct)
  apply auto
  done


lemma map_var_bit_to_var_append:
"map_var_bit_to_var v (append_nat xs ys) = 
append_nat(map_var_bit_to_var v xs) (map_var_bit_to_var v ys)"
proof -
  obtain xs' ys' where "ys = list_encode ys'"  "xs = list_encode xs'" 
  by (metis list_decode_inverse)
  thus ?thesis 
    apply(auto simp add: sub_append submap_var_bit_to_var
sub_map
 simp del:map_nat.simps
map_var_bit_to_var.simps)
    done
qed

lemma map_var_bit_to_var_induct:
"reverse_nat (map_var_bit_to_var v (append_nat xs ys))
= map_var_bit_to_var_acc (reverse_nat (map_var_bit_to_var v xs)) v ys"
  apply(induct ys arbitrary:xs rule:length_nat.induct)
   apply(auto simp del:  map_var_bit_to_var_acc.simps  map_var_bit_to_var.simps
          simp add: append_nat_0)
   apply simp
    apply(auto simp del:  map_var_bit_to_var_acc.simps  map_var_bit_to_var.simps
          simp add: append_nat_0 append_nat_Suc)
  apply (subst (2) map_var_bit_to_var_acc.simps)
  apply(auto simp add: map_var_bit_to_var_append subtail_var_bit_to_var
        reverse_append_nat simp del:  map_var_bit_to_var_acc.simps  map_var_bit_to_var.simps
          simp add: append_nat_0 append_nat_Suc)
  apply(subst map_var_bit_to_var.simps)
  apply(auto simp add: cons_Nil
 simp del:  map_var_bit_to_var_acc.simps  map_var_bit_to_var.simps)

  apply(auto simp only: cons0 sub_hd head.simps sub_tl tail.simps)
  apply(subst map_var_bit_to_var.simps)
    apply(auto simp add: reverse_singleton_nat append_singleton_nat
 simp del:  map_var_bit_to_var_acc.simps  map_var_bit_to_var.simps)
  done

definition map_var_bit_to_var_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_var_bit_to_var_tail v n = reverse_nat (map_var_bit_to_var_acc 0 v n)"

lemma subtail_map_var_bit_to_var:
"map_var_bit_to_var_tail v n = map_var_bit_to_var v n"
  apply(auto simp only: map_var_bit_to_var_tail_def)
  using map_var_bit_to_var_induct [of v 0 n] rev_rev_nat map_var_bit_to_var.simps
  by (metis append_nat.simps(1) reverse_nat_0)

definition var_bit_list_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"var_bit_list_nat n v = map_var_bit_to_var v (list_less_nat n)"

definition var_bit_list_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"var_bit_list_tail n v = map_var_bit_to_var_tail v (list_less_tail n)"

lemma subtail_var_bit_list: 
"var_bit_list_tail n v = var_bit_list_nat n v"
  apply(auto simp only: var_bit_list_tail_def var_bit_list_nat_def 
          subtail_list_less subtail_map_var_bit_to_var)
  done

lemma sub_var_bit_list: "var_bit_list_nat n (vname_encode v) = vname_list_encode (var_bit_list n v)"
  apply (simp only: submap_var_bit_to_var  var_bit_list_nat_def var_bit_list_def sub_var_bit_to_var sub_map sub_list_less
        vname_list_encode_def
 flip: vname_nat_encode.simps )
  apply auto
  by (metis comp_apply)


declare nth_nat.simps[simp del]
datatype IMPm_IMPmm = Bot IMP_Minus_Minus_com |
                      SKIP nat| 
                      Assign vname aexp nat |
                      Seq_0 IMP_Minus_com IMP_Minus_com nat |
                      Seq_m IMP_Minus_com IMP_Minus_com nat IMP_Minus_Minus_com  |
                      Seq_f IMP_Minus_com IMP_Minus_com nat IMP_Minus_Minus_com IMP_Minus_Minus_com  |
                      If_0  vname IMP_Minus_com IMP_Minus_com nat|
                      If_m  vname IMP_Minus_com IMP_Minus_com nat IMP_Minus_Minus_com  |
                      If_f vname IMP_Minus_com IMP_Minus_com nat  IMP_Minus_Minus_com IMP_Minus_Minus_com |
                      While_0 vname IMP_Minus_com nat|
                      While_f vname IMP_Minus_com nat IMP_Minus_Minus_com


fun IMPm_IMPmm_encode :: "IMPm_IMPmm \<Rightarrow> nat" where 
"IMPm_IMPmm_encode (Bot x) = list_encode [0,comm_encode x]"|
"IMPm_IMPmm_encode (SKIP n) = list_encode [1, n]"|
"IMPm_IMPmm_encode (Assign v a n) = list_encode [2, vname_encode v, aexp_encode a , n]"|
"IMPm_IMPmm_encode (Seq_0 c1 c2 n) = list_encode [3, com_encode c1, com_encode c2, n]"|
"IMPm_IMPmm_encode (Seq_m c1 c2 n c3) = list_encode [4, com_encode c1 ,com_encode c2, n , comm_encode c3]"|
"IMPm_IMPmm_encode (Seq_f c1 c2 n c3 c4) = list_encode [5, com_encode c1 ,com_encode c2, n , comm_encode c3,comm_encode c4]"|
"IMPm_IMPmm_encode (If_0 v c1 c2 n) = list_encode [6, vname_encode v, com_encode c1, com_encode c2, n]"|
"IMPm_IMPmm_encode (If_m v c1 c2 n c3) = list_encode [7, vname_encode v, com_encode c1, com_encode c2, n, comm_encode c3]"|
"IMPm_IMPmm_encode (If_f v c1 c2 n c3 c4) = list_encode [8, vname_encode v, com_encode c1, com_encode c2, n, comm_encode c3 , comm_encode c4]"|
"IMPm_IMPmm_encode (While_0 v c n) = list_encode [9, vname_encode v, com_encode c , n]"|
"IMPm_IMPmm_encode (While_f v c n c') = list_encode [10, vname_encode v, com_encode c, n, comm_encode c']"

fun IMPm_IMPmm_decode :: "nat \<Rightarrow> IMPm_IMPmm" where 
"IMPm_IMPmm_decode  n = (case list_decode n of
    [0,x] \<Rightarrow> Bot (comm_decode x)|
    [Suc 0,n] \<Rightarrow> SKIP n|
    [Suc (Suc 0) , v , a, n] \<Rightarrow> Assign (vname_decode v) (aexp_decode a) n|
    [Suc (Suc (Suc 0)), c1, c2,n] \<Rightarrow> Seq_0 (com_decode c1) (com_decode c2) n|
    [Suc (Suc (Suc (Suc 0))), c1, c2 ,n, c3] \<Rightarrow> Seq_m (com_decode c1) (com_decode c2) n (comm_decode c3)|
    [Suc (Suc (Suc (Suc (Suc 0)))), c1, c2, n, c3,c4] \<Rightarrow> Seq_f (com_decode c1) (com_decode c2) n (comm_decode c3) (comm_decode c4)|
    [Suc (Suc (Suc (Suc (Suc (Suc 0))))), v ,c1, c2,n] \<Rightarrow> If_0 (vname_decode v) (com_decode c1)  (com_decode c2) n|
    [Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))), v ,c1 ,c2,n,c3] \<Rightarrow> If_m (vname_decode v) (com_decode c1) (com_decode c2) n (comm_decode c3)|
    [Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))),v ,c1 ,c2,n,c3,c4] \<Rightarrow> If_f (vname_decode v) (com_decode c1) (com_decode c2) n (comm_decode c3) (comm_decode c4)|
    [Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))),v,c,n] \<Rightarrow> While_0 (vname_decode v) (com_decode c)  n|
    [Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))), v, c, n, c'] \<Rightarrow> While_f (vname_decode v) (com_decode c) n (comm_decode c')
) "

lemma IMPm_IMPmm_id : 
"IMPm_IMPmm_decode (IMPm_IMPmm_encode x) = x"
  apply(cases x)
   apply(auto simp add: IMPm_IMPmm_encode.simps IMPm_IMPmm_decode.simps list_encode_inverse comm_id vname_id aexp_id com_id
                    simp del: comm_encode.simps com_encode.simps comm_decode.simps com_decode.simps aexp_encode.simps aexp_decode.simps)
  done

definition IMPm_IMPmm_list_encode :: "IMPm_IMPmm list \<Rightarrow> nat" where 
"IMPm_IMPmm_list_encode xs = list_encode (map IMPm_IMPmm_encode xs)"

definition IMPm_IMPmm_list_decode :: "nat \<Rightarrow> IMPm_IMPmm list " where 
"IMPm_IMPmm_list_decode xs = map IMPm_IMPmm_decode (list_decode xs)"

lemma IMPm_IMPmm_list_id: 
"IMPm_IMPmm_list_decode (IMPm_IMPmm_list_encode x) = x"
  apply(auto simp only:  IMPm_IMPmm_list_decode_def  IMPm_IMPmm_list_encode_def list_encode_inverse 
            map_map comp_def IMPm_IMPmm_id)
  apply auto
  done

fun size_e :: "Com.com \<Rightarrow> nat" where 
"size_e Com.com.SKIP = 1 "|
"size_e (Com.com.Assign v a)  = 1"|
"size_e (Com.com.Seq c1 c2) = Suc (size_e c1 + size_e c2)"|
"size_e (Com.com.If v c1 c2) = Suc (size_e c1 + size_e c2)"|
"size_e (Com.com.While v c) = Suc (size_e c)"

fun size_stack_rev :: "IMPm_IMPmm list \<Rightarrow> nat" where
"size_stack_rev (Seq_0 c1 c2 _# s) =  (if s = [] then Suc (2* (size_e c1 + size_e c2)) else  Suc (2 * size_e c2) + size_stack_rev s )  "|
"size_stack_rev (Seq_m c1 c2 _ _#s) = (if s = [] then  Suc (2 * size_e c2) else  Suc (size_stack_rev s)) "|
"size_stack_rev (If_0 _ c1 c2 _# s) =  (if s = [] then Suc (2* (size_e c1 + size_e c2)) else  Suc (2 * size_e c2) + size_stack_rev s )  "|
"size_stack_rev (If_m _ c1 c2  _ _#s) = (if s = [] then  Suc (2 * size_e c2) else  Suc (size_stack_rev s)) "|
"size_stack_rev (While_0 _ c _ #s)  = (if s = [] then Suc (2* size_e c) else Suc (size_stack_rev s) )"|
"size_stack_rev (Bot x # s) = (if s =[] then 0 else Suc (size_stack_rev s))"|
"size_stack_rev (_#s) = (if s = [] then 1 else Suc (size_stack_rev s))"|
"size_stack_rev [] = 1"

fun size_stack :: "IMPm_IMPmm list \<Rightarrow> nat" where 
"size_stack s = size_stack_rev (rev s)"

lemma 
size_stack_mono :" x \<noteq> [] \<Longrightarrow>y \<noteq>  [] \<Longrightarrow> size_stack_rev y < size_stack_rev x
 \<Longrightarrow> size_stack_rev (s @ y) < size_stack_rev (s @ x) "
  apply(induct s )
   apply auto
  subgoal for a xs
    apply (cases a)
           apply (auto)
    done
  done

lemma size_stack_var_0:"(size_stack_rev x = 0) = (\<exists>n. x = [Bot n]) "
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



fun push_on_stack :: "IMP_Minus_com \<Rightarrow> nat \<Rightarrow> IMPm_IMPmm list \<Rightarrow> IMPm_IMPmm list" where 
"push_on_stack Com.SKIP n stack = SKIP n # stack "|
"push_on_stack (Com.Assign v aexp) n stack =  ( Assign v aexp n) # stack "|
"push_on_stack (Com.Seq c1 c2) n stack =  ( Seq_0 c1 c2 n) # stack "|
"push_on_stack (Com.If v c1 c2) n stack =  (If_0 v c1 c2 n) # stack "|
"push_on_stack (Com.While v c) n stack =  (While_0 v c n) # stack "

definition push_on_stack_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"push_on_stack_nat c n s = (if hd_nat c = 0 then (1##n##0)##s else 
if hd_nat c = 1 then (2## (nth_nat (Suc 0) c) ## (nth_nat (Suc (Suc 0)) c) ## n ## 0)## s else 
if hd_nat c = 2 then (3## (nth_nat (Suc 0) c) ## (nth_nat (Suc (Suc 0)) c) ## n ## 0)## s else 
if hd_nat c = 3 then (6## (nth_nat (Suc 0) c) ## (nth_nat (Suc (Suc 0)) c) ## (nth_nat (Suc (Suc (Suc 0))) c) ## n ## 0) ## s else
(9## (nth_nat (Suc 0) c) ## (nth_nat (Suc (Suc 0)) c) ## n ## 0)## s
)"

lemma sub_push_on_stack:
"push_on_stack_nat (com_encode c) n (IMPm_IMPmm_list_encode s) = 
IMPm_IMPmm_list_encode (push_on_stack c n s)"
  apply(cases c)
      apply (auto simp only: push_on_stack_nat_def push_on_stack.simps sub_hd head.simps com_encode.simps
             IMPm_IMPmm_list_encode_def sub_cons cons0 sub_nth nth.simps)
  apply auto
  done



       
           
fun add_result_to_stack :: "IMP_Minus_Minus_com \<Rightarrow> IMPm_IMPmm list \<Rightarrow> IMPm_IMPmm list" where 
"add_result_to_stack c [] = [Bot c]"|
"add_result_to_stack c (Seq_0 c1 c2 n # stack) = Seq_m c1 c2 n c # stack" |
"add_result_to_stack c (Seq_m c1 c2 n c3 #stack) = (Seq_f c1 c2 n c3 c) # stack"|
"add_result_to_stack c (If_0 v c1 c2  n # stack)  = If_m v c1 c2 n c # stack"|
"add_result_to_stack c (If_m v c1 c2 n c3 #stack) = If_f v c1 c2 n c3 c # stack"|
"add_result_to_stack c (While_0 v c' n # stack ) = While_f v c' n c #stack"|
"add_result_to_stack c s = s"

definition add_result_to_stack_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"add_result_to_stack_nat c s = (if s = 0 then (0##c##0)##0
else (let h = hd_nat s; con = hd_nat h; t = tl_nat s  in 
  if con = 3 then ((4## (nth_nat (Suc 0) h) ## (nth_nat (Suc (Suc 0)) h) ## (nth_nat (Suc (Suc (Suc 0))) h) ## c ## 0) ## t) 
  else if con = 4 then ((5## (nth_nat (Suc 0) h) ## (nth_nat (Suc (Suc 0)) h) ## (nth_nat (Suc (Suc (Suc 0))) h)  ## (nth_nat (Suc (Suc (Suc ( Suc 0)))) h) ## c ## 0) ## t)
  else if con = 6 then ((7## (nth_nat (Suc 0) h) ## (nth_nat (Suc (Suc 0)) h) ## (nth_nat (Suc (Suc (Suc 0))) h)  ## (nth_nat (Suc (Suc (Suc ( Suc 0)))) h) ## c ## 0) ## t)    
  else if con = 7 then ((8## (nth_nat (Suc 0) h) ## (nth_nat (Suc (Suc 0)) h) ## (nth_nat (Suc (Suc (Suc 0))) h)  ## (nth_nat (Suc (Suc (Suc ( Suc 0)))) h)  ## (nth_nat (Suc (Suc (Suc ( Suc (Suc 0))))) h) ## c ## 0) ## t)
  else if con = 9 then ((10 ## (nth_nat (Suc 0) h) ## (nth_nat (Suc (Suc 0)) h) ## (nth_nat (Suc (Suc (Suc 0))) h) ## c ## 0) ## t) 
  else s
))"

lemma sub_add_result_to_stack:
"add_result_to_stack_nat (comm_encode c) (IMPm_IMPmm_list_encode s)
= IMPm_IMPmm_list_encode (add_result_to_stack c s) "
  apply(cases s)
      apply (auto simp only: map_is_Nil_conv
      list_encode_non_empty  
      list.simps add_result_to_stack_nat_def add_result_to_stack.simps sub_hd head.simps comm_encode.simps
             IMPm_IMPmm_list_encode_def sub_cons cons0 sub_nth nth.simps)
    
   apply (auto simp del: list_encode.simps)
  subgoal for a xs
    apply(cases a)
   apply (auto simp add: Let_def sub_tl sub_cons sub_nth sub_hd list.simps simp del: list_encode.simps)
    done
  done

lemma add_res_less:
"\<forall>x. s \<noteq> [Bot x] \<and> a \<noteq> Bot x \<Longrightarrow> size_stack (add_result_to_stack r s) < size_stack (a#s) "
  apply(cases s)
   apply auto
   apply (cases a)
  apply (auto simp add: size_stack_var_mono)
  subgoal for a xs
    apply (cases a)
    using size_stack_mono size_stack_var_0 nat_less_le    apply (auto )
    done
  done


function IMP_Minus_to_IMP_Minus_Minus_stack :: "IMPm_IMPmm list \<Rightarrow> IMP_Minus_Minus_com" where 
"IMP_Minus_to_IMP_Minus_Minus_stack (Seq_0 c1 c2 n #stack) = 
  IMP_Minus_to_IMP_Minus_Minus_stack (push_on_stack c1 n (Seq_0 c1 c2 n #stack))"|
"IMP_Minus_to_IMP_Minus_Minus_stack (Seq_m c1 c2 n c3 #stack) = 
  IMP_Minus_to_IMP_Minus_Minus_stack (push_on_stack c2 n (Seq_m c1 c2 n c3 #stack ))"|
"IMP_Minus_to_IMP_Minus_Minus_stack (If_0 v c1 c2 n # stack) = 
  IMP_Minus_to_IMP_Minus_Minus_stack (push_on_stack c1 n (If_0 v c1 c2 n #stack ))"|
"IMP_Minus_to_IMP_Minus_Minus_stack (If_m v c1 c2 n c3 # stack) = 
  IMP_Minus_to_IMP_Minus_Minus_stack (push_on_stack c2 n (If_m v c1 c2 n c3 #stack ))"|
"IMP_Minus_to_IMP_Minus_Minus_stack (While_0 v c n # stack) = 
  IMP_Minus_to_IMP_Minus_Minus_stack (push_on_stack c n (While_0 v c n #stack ))" |
"IMP_Minus_to_IMP_Minus_Minus_stack (SKIP _ # stack) = 
  IMP_Minus_to_IMP_Minus_Minus_stack (add_result_to_stack (IMP_Minus_Minus_Com.SKIP) stack)" |
"IMP_Minus_to_IMP_Minus_Minus_stack (Assign v aexp n # stack) = 
  IMP_Minus_to_IMP_Minus_Minus_stack (add_result_to_stack (assignment_to_binary n v aexp) stack)"|
"IMP_Minus_to_IMP_Minus_Minus_stack (Seq_f _ _ _ c1 c2 # stack) = 
  IMP_Minus_to_IMP_Minus_Minus_stack (add_result_to_stack (IMP_Minus_Minus_Com.Seq c1 c2) stack)"|
"IMP_Minus_to_IMP_Minus_Minus_stack (If_f v _ _ n c1 c2 # stack) = 
  IMP_Minus_to_IMP_Minus_Minus_stack (add_result_to_stack ( IMP_Minus_Minus_Com.If (var_bit_list n v) c1  c2) stack)"|
"IMP_Minus_to_IMP_Minus_Minus_stack (While_f v _ n c # stack) = 
  IMP_Minus_to_IMP_Minus_Minus_stack (add_result_to_stack (IMP_Minus_Minus_Com.While (var_bit_list n v) c) stack)"|
"IMP_Minus_to_IMP_Minus_Minus_stack (Bot res # stack) =  res"|
"IMP_Minus_to_IMP_Minus_Minus_stack [] =  com.SKIP"
  by pat_completeness  auto
termination 
proof  (relation "measure size_stack",goal_cases)
case 1
then show ?case by auto
next
  case (2 c1 c2 n stack)
  then show ?case   using size_stack_mono by (cases c1)  auto
next
  case (3 c1 c2 n c3 stack)
  then show ?case  using size_stack_mono by (cases c2)  auto
next
  case (4 v c1 c2 n stack)
  then show ?case  using size_stack_mono by (cases c1)  auto
next
  case (5 v c1 c2 n c3 stack)
  then show ?case  using size_stack_mono by (cases c2)  auto
next
  case (6 v c n stack)
  then show ?case  using size_stack_mono by (cases c)  auto
next
  case (7 uu stack)
  then show ?case using add_res_less apply auto
    by (metis IMP_Minus_To_IMP_Minus_Minus_nat.size_stack_var_0 
IMPm_IMPmm.distinct One_nat_def Suc_less_SucD Suc_mono add_result_to_stack.simps
gr0I length_Cons length_append_singleton list.size(3) rev_singleton_conv zero_less_one)
    
next
  case (8 v aexp n stack)
  then show ?case  using add_res_less apply auto
    by (metis IMP_Minus_To_IMP_Minus_Minus_nat.size_stack_var_0 
IMPm_IMPmm.distinct One_nat_def Suc_less_SucD Suc_mono add_result_to_stack.simps
gr0I length_Cons length_append_singleton list.size(3) rev_singleton_conv zero_less_one)

next
case (9 uv uw ux c1 c2 stack)
  then show ?case  using add_res_less apply auto
    by (metis IMP_Minus_To_IMP_Minus_Minus_nat.size_stack_var_0 
IMPm_IMPmm.distinct One_nat_def Suc_less_SucD Suc_mono add_result_to_stack.simps
gr0I length_Cons length_append_singleton list.size(3) rev_singleton_conv zero_less_one)

next
  case (10 v uy uz n c1 c2 stack)
  then show ?case  using add_res_less apply auto
    by (metis IMP_Minus_To_IMP_Minus_Minus_nat.size_stack_var_0 
IMPm_IMPmm.distinct One_nat_def Suc_less_SucD Suc_mono add_result_to_stack.simps
gr0I length_Cons length_append_singleton list.size(3) rev_singleton_conv zero_less_one)

next
  case (11 v va n c stack)
  then show ?case  using add_res_less apply auto
    by (metis IMP_Minus_To_IMP_Minus_Minus_nat.size_stack_var_0 
IMPm_IMPmm.distinct One_nat_def Suc_less_SucD Suc_mono add_result_to_stack.simps
gr0I length_Cons length_append_singleton list.size(3) rev_singleton_conv zero_less_one)

qed


function (domintros) IMP_Minus_to_IMP_Minus_Minus_stack_nat :: "nat \<Rightarrow> nat" where 
"IMP_Minus_to_IMP_Minus_Minus_stack_nat s  = ( if s = 0 then 0##0 else let h = hd_nat s ; c = hd_nat h ; t = tl_nat s in
  if c = 3  then  IMP_Minus_to_IMP_Minus_Minus_stack_nat (push_on_stack_nat (nth_nat (Suc 0) h) (nth_nat (Suc (Suc (Suc 0))) h) s)
else if c = 4 then IMP_Minus_to_IMP_Minus_Minus_stack_nat (push_on_stack_nat (nth_nat (Suc (Suc 0)) h) (nth_nat (Suc (Suc (Suc 0))) h) s) 
else if c = 6 then IMP_Minus_to_IMP_Minus_Minus_stack_nat (push_on_stack_nat (nth_nat (Suc (Suc 0)) h) (nth_nat (Suc (Suc (Suc (Suc 0)))) h) s)
else if c = 7 then IMP_Minus_to_IMP_Minus_Minus_stack_nat (push_on_stack_nat (nth_nat (Suc (Suc (Suc 0))) h) (nth_nat (Suc (Suc (Suc (Suc 0)))) h) s)
else if c = 9 then IMP_Minus_to_IMP_Minus_Minus_stack_nat (push_on_stack_nat (nth_nat (Suc (Suc 0)) h) (nth_nat (Suc (Suc (Suc 0))) h) s) 
else if c = 1 then IMP_Minus_to_IMP_Minus_Minus_stack_nat (add_result_to_stack_nat (0##0) t)
else if c = 2 then IMP_Minus_to_IMP_Minus_Minus_stack_nat (add_result_to_stack_nat (assignment_to_binary_nat (nth_nat (Suc (Suc (Suc 0))) h) (nth_nat (Suc 0) h) (nth_nat (Suc (Suc 0)) h)) t)
else if c = 5 then IMP_Minus_to_IMP_Minus_Minus_stack_nat (add_result_to_stack_nat (2 ## (nth_nat (Suc (Suc (Suc (Suc 0)))) h) ## (nth_nat (Suc (Suc (Suc (Suc(Suc 0))))) h) ## 0  ) t) 
else if c = 8 then IMP_Minus_to_IMP_Minus_Minus_stack_nat (add_result_to_stack_nat (3 ## (var_bit_list_nat (nth_nat (Suc (Suc (Suc (Suc 0)))) h)
  (nth_nat (Suc 0) h))
 ## (nth_nat (Suc (Suc (Suc (Suc (Suc 0))))) h) ## (nth_nat (Suc (Suc (Suc (Suc (Suc (Suc 0)))))) h) ## 0  ) t)
else if c = 10 then IMP_Minus_to_IMP_Minus_Minus_stack_nat (add_result_to_stack_nat (4 ## (var_bit_list_nat (nth_nat (Suc (Suc (Suc 0))) h)
  (nth_nat (Suc 0) h))
 ## (nth_nat (Suc (Suc (Suc (Suc 0)))) h)  ## 0  ) t )

else nth_nat (Suc 0) h

)"
  by pat_completeness auto

lemma push_non_empty : "push_on_stack c n s \<noteq> []"
  apply(cases c)
      apply auto
  done
lemma add_result_non_empty: "add_result_to_stack c s \<noteq> []"
  apply(cases s)
   apply auto
  subgoal for a xs
    apply(cases a)
              apply auto
    done 
  done

lemma IMP_Minus_To_IMP_Minus_Minus_term:
"IMP_Minus_to_IMP_Minus_Minus_stack_nat_dom (IMPm_IMPmm_list_encode c)"
proof (induct c rule:IMP_Minus_to_IMP_Minus_Minus_stack.induct)
case (1 c1 c2 n stack)
  then show ?case  using IMP_Minus_to_IMP_Minus_Minus_stack_nat.domintros[of
"list_encode
       (list_encode [3, com_encode c1, com_encode c2, n] # map IMPm_IMPmm_encode stack)"]
    apply(simp only: Let_def sub_hd head.simps sub_nth nth.simps sub_push_on_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps)
    apply( simp only: sub_push_on_stack flip:IMPm_IMPmm_encode.simps list.simps IMPm_IMPmm_list_encode_def)
    done
next
  case (2 c1 c2 n c3 stack)
  then show ?case using IMP_Minus_to_IMP_Minus_Minus_stack_nat.domintros[of
"list_encode
       (list_encode [4, com_encode c1, com_encode c2, n, comm_encode c3] # map IMPm_IMPmm_encode stack)"]
    apply(simp only: Let_def sub_hd head.simps sub_nth nth.simps sub_push_on_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps)
    apply( simp only: sub_push_on_stack flip:IMPm_IMPmm_encode.simps list.simps IMPm_IMPmm_list_encode_def)
    done
next
  case (3 v c1 c2 n stack)
  then show ?case  using IMP_Minus_to_IMP_Minus_Minus_stack_nat.domintros[of
"list_encode
       (list_encode [6, vname_encode v, com_encode c1, com_encode c2, n] # map IMPm_IMPmm_encode stack)"]
    
    apply(simp only: Let_def sub_hd head.simps sub_nth nth.simps sub_push_on_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps)
    apply( simp only: sub_push_on_stack flip:IMPm_IMPmm_encode.simps list.simps IMPm_IMPmm_list_encode_def)
    done
next
  case (4 v c1 c2 n c3 stack)
  then show ?case  using IMP_Minus_to_IMP_Minus_Minus_stack_nat.domintros[of
"list_encode
       (list_encode [7, vname_encode v, com_encode c1, com_encode c2, n, comm_encode c3] # map IMPm_IMPmm_encode stack)"]   
    apply(simp only: Let_def sub_hd head.simps sub_nth nth.simps sub_push_on_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps)
            apply( simp only: sub_push_on_stack flip:IMPm_IMPmm_encode.simps list.simps IMPm_IMPmm_list_encode_def)

    done
  next
    case (5 v c n stack)
    then show ?case  using IMP_Minus_to_IMP_Minus_Minus_stack_nat.domintros[of
"list_encode
       (list_encode [9, vname_encode v, com_encode c, n] # map IMPm_IMPmm_encode stack)"]   
 apply(simp only: Let_def sub_hd head.simps sub_nth nth.simps sub_push_on_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps)
            apply( simp only: sub_add_result_to_stack sub_push_on_stack flip:IMPm_IMPmm_encode.simps list.simps IMPm_IMPmm_list_encode_def)
      done
next
  case (6 uu stack)
  then show ?case  using IMP_Minus_to_IMP_Minus_Minus_stack_nat.domintros[of
"list_encode
       (list_encode [1, uu] # map IMPm_IMPmm_encode stack)"]
    apply(simp only: Let_def cons0 sub_cons sub_hd sub_tl tail.simps head.simps sub_nth nth.simps sub_push_on_stack sub_add_result_to_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps  flip: comm_encode.simps )
    apply( simp only:sub_add_result_to_stack  flip: IMPm_IMPmm_list_encode_def )
    done
next
  case (7 v aexp n stack)
  then show ?case   using IMP_Minus_to_IMP_Minus_Minus_stack_nat.domintros[of
"list_encode
       (list_encode [2, vname_encode v, aexp_encode aexp, n] # map IMPm_IMPmm_encode stack)"]
    
    apply(simp only: Let_def cons0 sub_cons sub_hd sub_tl tail.simps head.simps sub_nth nth.simps sub_push_on_stack sub_add_result_to_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps  flip: comm_encode.simps )
       apply( simp only:sub_add_result_to_stack sub_assignment_to_binary  flip: IMPm_IMPmm_list_encode_def )
done
  next
  case (8 uv uw ux c1 c2 stack)
  then show ?case using IMP_Minus_to_IMP_Minus_Minus_stack_nat.domintros[of
"list_encode
       (list_encode [5, com_encode uv, com_encode uw, ux, comm_encode c1, comm_encode c2] #
         map IMPm_IMPmm_encode stack)"]
        
    apply(simp only: sub_var_bit_list sub_add_result_to_stack  Let_def cons0 sub_cons sub_hd sub_tl tail.simps head.simps sub_nth nth.simps sub_push_on_stack sub_add_result_to_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps  )
    apply(simp only: sub_add_result_to_stack flip: IMPm_IMPmm_list_encode_def comm_encode.simps)
    done
next
  case (9 v uy uz n c1 c2 stack)
  then show ?case   using IMP_Minus_to_IMP_Minus_Minus_stack_nat.domintros[of
"list_encode
       (list_encode [8, vname_encode v, com_encode uy, com_encode uz, n, comm_encode c1,
          comm_encode c2] #
         map IMPm_IMPmm_encode stack)"]
    
    apply(simp only: sub_var_bit_list sub_add_result_to_stack  Let_def cons0 sub_cons sub_hd sub_tl tail.simps head.simps sub_nth nth.simps sub_push_on_stack sub_add_result_to_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps  )
  apply(simp only: sub_add_result_to_stack flip: IMPm_IMPmm_list_encode_def comm_encode.simps)
    done
next
  case (10 v va n c stack)
  then show ?case   using IMP_Minus_to_IMP_Minus_Minus_stack_nat.domintros[of
"list_encode
       (list_encode [10, vname_encode v, com_encode va, n, comm_encode c] #
         map IMPm_IMPmm_encode stack)"]
    
    apply(simp only: sub_var_bit_list sub_add_result_to_stack  Let_def cons0 sub_cons sub_hd sub_tl tail.simps head.simps sub_nth nth.simps sub_push_on_stack sub_add_result_to_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps  )
  apply(simp only: sub_add_result_to_stack flip: IMPm_IMPmm_list_encode_def comm_encode.simps)
    done
next
  case (11 res stack)
  then show ?case   using IMP_Minus_to_IMP_Minus_Minus_stack_nat.domintros[of
"list_encode
       (list_encode [0, comm_encode res] #
         map IMPm_IMPmm_encode stack)"]
    apply(simp only: sub_var_bit_list sub_add_result_to_stack  Let_def cons0 sub_cons sub_hd sub_tl tail.simps head.simps sub_nth nth.simps sub_push_on_stack sub_add_result_to_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps  )
done         
next
  case 12
  then show ?case by (auto intro: IMP_Minus_to_IMP_Minus_Minus_stack_nat.domintros
simp add:IMPm_IMPmm_list_encode_def)
qed

lemmas IMP_Minus_to_IMP_Minus_Minus_stack_nat_simp =
IMP_Minus_to_IMP_Minus_Minus_stack_nat.psimps[OF IMP_Minus_To_IMP_Minus_Minus_term]

lemma IMPm_IMPmm_list_encode_0: "(IMPm_IMPmm_list_encode xs = 0) = (xs = [])"
  by (auto simp add: IMPm_IMPmm_list_encode_def list_encode_0)
lemma subtailnat_IMP_Minus_to_IMP_Minus_Minus_stack:
" IMP_Minus_to_IMP_Minus_Minus_stack_nat (IMPm_IMPmm_list_encode s)
= comm_encode (IMP_Minus_to_IMP_Minus_Minus_stack s) "
proof (induct s rule: IMP_Minus_to_IMP_Minus_Minus_stack.induct )
case (1 c1 c2 n stack)
  then show ?case apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.psimps)
  using  IMP_Minus_To_IMP_Minus_Minus_term apply blast
            apply(simp only: Let_def sub_hd head.simps sub_nth nth.simps sub_push_on_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps)
            apply( simp only: sub_push_on_stack  flip:IMPm_IMPmm_encode.simps list.simps IMPm_IMPmm_list_encode_def)
            apply (auto simp add: push_non_empty  IMPm_IMPmm_list_encode_0) done
next
  case (2 c1 c2 n c3 stack)
  then show ?case  apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.psimps)
using  IMP_Minus_To_IMP_Minus_Minus_term apply blast
            apply(simp only: Let_def sub_hd head.simps sub_nth nth.simps sub_push_on_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps)
          apply( simp only: sub_push_on_stack IMPm_IMPmm_list_encode_0 flip:IMPm_IMPmm_encode.simps list.simps IMPm_IMPmm_list_encode_def)
           apply (auto) done
next
  case (3 v c1 c2 n stack)
  then show ?case  apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.psimps)
using  IMP_Minus_To_IMP_Minus_Minus_term apply blast
            apply(simp only: Let_def sub_hd head.simps sub_nth nth.simps sub_push_on_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps)
            apply( simp only: sub_push_on_stack flip:IMPm_IMPmm_encode.simps list.simps IMPm_IMPmm_list_encode_def)
          apply (auto simp add: IMPm_IMPmm_list_encode_0  ) done
next
  case (4 v c1 c2 n c3 stack)
  then show ?case apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.psimps)
using  IMP_Minus_To_IMP_Minus_Minus_term apply blast
            apply(simp only: Let_def sub_hd head.simps sub_nth nth.simps sub_push_on_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps)
            apply( simp only: sub_push_on_stack flip:IMPm_IMPmm_encode.simps list.simps IMPm_IMPmm_list_encode_def)
          apply (auto simp add: IMPm_IMPmm_list_encode_0  ) done
next
  case (5 v c n stack)
  then show ?case apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.psimps)
using  IMP_Minus_To_IMP_Minus_Minus_term apply blast
            apply(simp only: Let_def sub_hd head.simps sub_nth nth.simps sub_push_on_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps)
            apply( simp only: sub_add_result_to_stack sub_push_on_stack flip:IMPm_IMPmm_encode.simps list.simps IMPm_IMPmm_list_encode_def)
          apply (auto simp add: IMPm_IMPmm_list_encode_0  ) done
next
  case (6 uu stack)
  then show ?case apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.psimps)
using  IMP_Minus_To_IMP_Minus_Minus_term apply blast
            apply(simp only: Let_def cons0 sub_cons sub_hd sub_tl tail.simps head.simps sub_nth nth.simps sub_push_on_stack sub_add_result_to_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps  flip: comm_encode.simps )
       apply( simp only:sub_add_result_to_stack  flip: IMPm_IMPmm_list_encode_def )
          apply (auto simp add: IMPm_IMPmm_list_encode_0  ) done
next
  case (7 v aexp n stack)
  then show ?case  apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.psimps)
using  IMP_Minus_To_IMP_Minus_Minus_term apply blast
            apply(simp only: Let_def cons0 sub_cons sub_hd sub_tl tail.simps head.simps sub_nth nth.simps sub_push_on_stack sub_add_result_to_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps  flip: comm_encode.simps )
       apply( simp only:sub_add_result_to_stack sub_assignment_to_binary  flip: IMPm_IMPmm_list_encode_def )
          apply (auto simp add: IMPm_IMPmm_list_encode_0  ) done
next
  case (8 uv uw ux c1 c2 stack)
  then show ?case apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.psimps)
using  IMP_Minus_To_IMP_Minus_Minus_term apply blast
            apply(simp only: Let_def cons0 sub_cons sub_hd sub_tl tail.simps head.simps sub_nth nth.simps sub_push_on_stack sub_add_result_to_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps  flip: comm_encode.simps )
       apply( simp only:sub_add_result_to_stack sub_assignment_to_binary  flip: IMPm_IMPmm_list_encode_def )
 apply (auto simp add: IMPm_IMPmm_list_encode_0  ) done
next
  case (9 v uy uz n c1 c2 stack)
  then show ?case apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.psimps)
using  IMP_Minus_To_IMP_Minus_Minus_term apply blast
            apply(simp only: sub_var_bit_list sub_add_result_to_stack  Let_def cons0 sub_cons sub_hd sub_tl tail.simps head.simps sub_nth nth.simps sub_push_on_stack sub_add_result_to_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps  )
  apply(simp only: sub_add_result_to_stack flip: IMPm_IMPmm_list_encode_def comm_encode.simps)
  apply (auto simp add: IMPm_IMPmm_list_encode_0  )
done
next
  case (10 v va n c stack)
  then show ?case apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.psimps)
using  IMP_Minus_To_IMP_Minus_Minus_term apply blast
            apply(simp only: sub_var_bit_list sub_add_result_to_stack  Let_def cons0 sub_cons sub_hd sub_tl tail.simps head.simps sub_nth nth.simps sub_push_on_stack sub_add_result_to_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps  )
  apply(simp only: sub_add_result_to_stack flip: IMPm_IMPmm_list_encode_def comm_encode.simps)
          apply (auto simp add: IMPm_IMPmm_list_encode_0  ) done
next
  case (11 res stack)
  then show ?case apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.psimps)
using  IMP_Minus_To_IMP_Minus_Minus_term apply blast
            apply(simp only: sub_var_bit_list sub_add_result_to_stack  Let_def cons0 sub_cons sub_hd sub_tl tail.simps head.simps sub_nth nth.simps sub_push_on_stack sub_add_result_to_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps  )
  apply(simp only: sub_add_result_to_stack flip: IMPm_IMPmm_list_encode_def comm_encode.simps)
  apply (auto simp add: IMPm_IMPmm_list_encode_0  ) done
next
  case 12
  then show ?case  apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.psimps)
  using  IMP_Minus_To_IMP_Minus_Minus_term apply blast
    apply (auto simp add: IMPm_IMPmm_list_encode_0 cons_def  )
  done
qed

             
           
        
        
       
      
    
    
         
   
  
  


lemma IMP_Minus_to_IMP_Minus_Minus_stack_correct:
"IMP_Minus_to_IMP_Minus_Minus_stack (push_on_stack c n stack) 
= IMP_Minus_to_IMP_Minus_Minus_stack (add_result_to_stack (IMP_Minus_To_IMP_Minus_Minus c n) stack)"
  by (induct c arbitrary:stack) auto

definition IMP_Minus_to_IMP_Minus_Minus_t:: "IMP_Minus_com \<Rightarrow> nat \<Rightarrow> IMP_Minus_Minus_com" where
  "IMP_Minus_to_IMP_Minus_Minus_t c n = 
IMP_Minus_to_IMP_Minus_Minus_stack (push_on_stack c n [])"

definition IMP_Minus_To_IMP_Minus_Minus_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "IMP_Minus_To_IMP_Minus_Minus_nat c n = 
IMP_Minus_to_IMP_Minus_Minus_stack_nat (push_on_stack_nat c n 0)"

lemma IMPm_IMPmm_nil: "0 = IMPm_IMPmm_list_encode []"
  using IMPm_IMPmm_list_encode_def by force

lemma subtailnat_IMP_Minus_to_IMP_Minus_Minus:
"IMP_Minus_To_IMP_Minus_Minus_nat (com_encode c) n
= comm_encode (IMP_Minus_to_IMP_Minus_Minus_t c n)"
  using push_non_empty subtailnat_IMP_Minus_to_IMP_Minus_Minus_stack
  apply(auto simp only: IMPm_IMPmm_nil IMP_Minus_To_IMP_Minus_Minus_nat_def IMP_Minus_to_IMP_Minus_Minus_t_def 
       sub_push_on_stack )
  done

lemma subtail_IMP_Minus_to_IMP_Minus_Minus:
"IMP_Minus_to_IMP_Minus_Minus_t c n = 
IMP_Minus_To_IMP_Minus_Minus c n "
  using  IMP_Minus_to_IMP_Minus_Minus_stack_correct [of c n "[]"]
  apply (auto simp add:IMP_Minus_to_IMP_Minus_Minus_t_def)
  done
lemma sub_IMP_Minus_To_IMP_Minus_Minus:
"IMP_Minus_To_IMP_Minus_Minus_nat (com_encode c) n = comm_encode (IMP_Minus_To_IMP_Minus_Minus c n)"
  using subtail_IMP_Minus_to_IMP_Minus_Minus subtailnat_IMP_Minus_to_IMP_Minus_Minus by presburger

definition IMP_Minus_To_IMP_Minus_Minus_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"IMP_Minus_To_IMP_Minus_Minus_tail c n = IMP_Minus_To_IMP_Minus_Minus_nat c n "

lemma subtail_IMP_Minus_To_IMP_Minus_Minus:
"IMP_Minus_To_IMP_Minus_Minus_tail c n = IMP_Minus_To_IMP_Minus_Minus_nat c n "
  by (simp add: IMP_Minus_To_IMP_Minus_Minus_tail_def)

definition "IMP_Minus_to_IMP_Minus_Minus_stack_end_recur s = (
    if s = 0 then 0##0
    else nth_nat 1 (hd_nat s)
)"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux0 c h t = (
if c = 10 then (add_result_to_stack_nat (4 ## (var_bit_list_nat (nth_nat 3 h)
  (nth_nat 1 h))
 ## (nth_nat 4 h) ## 0) t)
else 0
)"


definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux1 c h t = (
if c = 8 then (add_result_to_stack_nat (3 ## (var_bit_list_nat (nth_nat 4 h)
  (nth_nat (Suc 0) h))
 ## (nth_nat 5 h) ## (nth_nat 6 h) ## 0  ) t)
else 
 IMP_Minus_to_IMP_Minus_Minus_stack_aux0 c h t
 )"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux2 c h t = (
if c = 5 then (add_result_to_stack_nat (2 ## (nth_nat 4 h) ## (nth_nat 5 h) 
## 0  ) t)
else IMP_Minus_to_IMP_Minus_Minus_stack_aux1 c h t)"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux3 c h t = (
if c = 2 then (add_result_to_stack_nat (assignment_to_binary_nat 
   (nth_nat 3 h) (nth_nat 1 h) (nth_nat 2 h)) t)
else IMP_Minus_to_IMP_Minus_Minus_stack_aux2 c h t)"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux4 c h t = (
if c = 1 then (add_result_to_stack_nat (0##0) t)
else IMP_Minus_to_IMP_Minus_Minus_stack_aux3 c h t)"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux5 s c h t = (
if c = 9 then (push_on_stack_nat (nth_nat 2 h) (nth_nat 3 h) s)
else IMP_Minus_to_IMP_Minus_Minus_stack_aux4 c h t)"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux6 s c h t = (
if c = 7 then (push_on_stack_nat (nth_nat 3 h) (nth_nat 4 h) s)
else IMP_Minus_to_IMP_Minus_Minus_stack_aux5 s c h t)"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux7 s c h t = (
if c = 6 then (push_on_stack_nat (nth_nat 2 h) (nth_nat 4 h) s)
else IMP_Minus_to_IMP_Minus_Minus_stack_aux6 s c h t)"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux8 s c h t = (
if c = 4 then (push_on_stack_nat (nth_nat 2 h) (nth_nat 3 h) s)
else IMP_Minus_to_IMP_Minus_Minus_stack_aux7 s c h t)"

definition "IMP_Minus_to_IMP_Minus_Minus_stack_aux9 s c h t = (
if c = 3 then (push_on_stack_nat (nth_nat 1 h) (nth_nat 3 h) s)
else IMP_Minus_to_IMP_Minus_Minus_stack_aux8 s c h t)"

lemma IMP_Minus_to_IMP_Minus_Minus_stack_aux_correct:
assumes "s = IMPm_IMPmm_list_encode c"
shows  "IMP_Minus_to_IMP_Minus_Minus_stack_nat s = (
    if s = 0 \<or> 10 < (hd_nat (hd_nat s)) \<or> (hd_nat (hd_nat s)) = 0 
    then (IMP_Minus_to_IMP_Minus_Minus_stack_end_recur s)
    else let h = hd_nat s ; c = hd_nat h ; t = tl_nat s in
    IMP_Minus_to_IMP_Minus_Minus_stack_nat (IMP_Minus_to_IMP_Minus_Minus_stack_aux9 s c h t)
  )"
  apply (simp only: IMP_Minus_to_IMP_Minus_Minus_stack_end_recur_def
  IMP_Minus_to_IMP_Minus_Minus_stack_aux9_def 
  IMP_Minus_to_IMP_Minus_Minus_stack_aux8_def
  IMP_Minus_to_IMP_Minus_Minus_stack_aux7_def
  IMP_Minus_to_IMP_Minus_Minus_stack_aux6_def
  IMP_Minus_to_IMP_Minus_Minus_stack_aux5_def
  IMP_Minus_to_IMP_Minus_Minus_stack_aux4_def
  IMP_Minus_to_IMP_Minus_Minus_stack_aux3_def
  IMP_Minus_to_IMP_Minus_Minus_stack_aux2_def
  IMP_Minus_to_IMP_Minus_Minus_stack_aux1_def
  IMP_Minus_to_IMP_Minus_Minus_stack_aux0_def Let_def)+
  apply (subst IMP_Minus_to_IMP_Minus_Minus_stack_nat_simp[of c] assms)+
  apply (simp only: Let_def)
  apply (auto simp add: numeral_eq_Suc)
  by presburger

end