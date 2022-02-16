theory IMP_Minus_Minus_Subprograms_Nat
  imports Primitives IMP_Minus_Minus_Subprograms 
begin 




fun map_all_subprograms:: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_all_subprograms c n = (if n =0 then 0 else ( 2## (hd_nat n) ## c ## 0) ## map_all_subprograms c (tl_nat n) )"


lemma submap_all_subprograms:
"map_all_subprograms c n = map_nat (\<lambda>x. 2## x ## c ## 0) n"
  apply (induct c n rule: map_all_subprograms.induct)
  apply auto
  done

fun map_all_subprograms_acc:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_all_subprograms_acc  c acc n = (if n =0 then acc else 
map_all_subprograms_acc c (( 2## (hd_nat n) ## c ## 0) ## acc) (tl_nat n) )"

lemma  map_all_subprograms_induct:
" map_all_subprograms_acc c acc n = map_acc  (\<lambda>x. 2## x ## c ## 0) acc n"
  apply(induct c acc n rule:map_all_subprograms_acc.induct)
  apply auto
  done

definition map_all_subprograms_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_all_subprograms_tail c n = reverse_nat (map_all_subprograms_acc c 0 n)"

lemma subtail_map_all_subprograms:
"map_all_subprograms_tail c n = map_all_subprograms c n"
  using submap_all_subprograms map_all_subprograms_tail_def  map_all_subprograms_induct[of c 0 n]
  subtail_map by presburger

datatype all_sub = Bot  "com list" |
                   SKIP|
                   Assign vname bit |
                   Seq_0 com com|
                   Seq_m com com "com list"|
                   Seq_f com com "com list" "com list"|
                   If_0 "vname list" com com |
                   If_m  "vname list" com com "com list"|
                   If_f  "vname list" com com "com list" "com list"|
                   While_0  "vname list" com |
                   While_f  "vname list" com "com list"


fun all_sub_encode :: "all_sub \<Rightarrow> nat" where 
"all_sub_encode SKIP = list_encode [0] "|
"all_sub_encode (Assign v b) = list_encode [1, vname_encode v, bit_encode b]"|
"all_sub_encode (Seq_0 c1 c2) = list_encode[2 , comm_encode c1 , comm_encode c2]"|
"all_sub_encode (If_0 v c1 c2) = list_encode [3, vname_list_encode v, comm_encode c1, comm_encode c2]"|
"all_sub_encode (While_0 v c) = list_encode [4,vname_list_encode v, comm_encode c]"|
"all_sub_encode (Seq_m  c1 c2 c3) = list_encode[5, comm_encode c1 ,comm_encode c2, list_encode (map comm_encode c3) ]"|
"all_sub_encode (Seq_f c1 c2 c3 c4) = list_encode [6, comm_encode c1 ,comm_encode c2 , list_encode (map comm_encode c3) , list_encode (map comm_encode c4)]"|
"all_sub_encode (If_m v c1 c2 c3) = list_encode[7, vname_list_encode v, comm_encode c1 ,comm_encode c2, list_encode (map comm_encode c3)]"|
"all_sub_encode (If_f v c1 c2 c3 c4) = list_encode [8, vname_list_encode v, comm_encode c1, comm_encode c2, list_encode (map comm_encode c3), list_encode (map comm_encode c4)]"|
"all_sub_encode (While_f v c c') = list_encode [9, vname_list_encode v, comm_encode c, list_encode (map comm_encode c')]"|
"all_sub_encode (Bot x) = list_encode [10, list_encode (map comm_encode x)]"

fun push_stack :: "com \<Rightarrow> all_sub list \<Rightarrow> all_sub list" where 
"push_stack com.SKIP s = SKIP#s "|
"push_stack (com.Assign v b) s = Assign v b # s"|
"push_stack (com.Seq c1 c2) s = Seq_0 c1 c2 # s"|
"push_stack (com.If v c1 c2) s = If_0 v c1 c2 # s"|
"push_stack (com.While v c) s = While_0 v c #s"

fun push_stack_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"push_stack_nat c s = (c ##s )"

lemma sub_push_stack:
"push_stack_nat (comm_encode c) (list_encode (map all_sub_encode s)) 
= list_encode (map all_sub_encode (push_stack c s))"
  apply( cases c)
  apply (auto simp add: sub_cons simp del: list_encode.simps)
  done

lemma push_stack_not_Nil:
"push_stack c s \<noteq> []"
  apply(cases c)
      apply auto
  done



fun add_res :: "com list \<Rightarrow> all_sub list \<Rightarrow> all_sub list" where 
"add_res c [] = [Bot c] "|
"add_res c (Seq_0 c1 c2 # s) = Seq_m c1 c2 c #s "|
"add_res c (Seq_m c1 c2 c3 # s) = Seq_f c1 c2 c3 c # s"|
"add_res c (If_0 v c1 c2 # s) = If_m v c1 c2 c # s "|
"add_res c (If_m v c1 c2 c3 #s) = If_f v c1 c2 c3 c # s"|
"add_res c (While_0 v c'#s) = While_f v c' c # s"|
"add_res c s = s"

lemma add_res_not_Nil:
"add_res c s \<noteq> []"
  apply(cases s)
   apply auto
  subgoal for a xs
    apply (cases a)
    apply auto
    done
  done

fun add_res_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"add_res_nat c s = (if s =0 then (10##c##0)##0 else 
(let h = hd_nat s; con = hd_nat h ; fs = nth_nat (Suc 0) h ; sn = nth_nat (Suc (Suc 0)) h;
       th = nth_nat (Suc (Suc (Suc 0))) h; ft = nth_nat (Suc (Suc (Suc (Suc 0)))) h; t = tl_nat s in
    if con = 2 then (5## fs ## sn ## c ## 0) ## t
else if con = 5 then(6 ## fs ## sn ## th ## c ## 0) ## t
else if con = 3 then (7 ## fs ## sn ## th ## c ## 0) ## t
else if con = 7 then (8 ## fs ## sn ## th ## ft ## c ## 0)## t
else if con = 4 then (9 ## fs ## sn ## c ## 0) ## t else s 
  ))"

lemma sub_add_res:
"add_res_nat (list_encode (map comm_encode c)) (list_encode  (map all_sub_encode s))
= list_encode (map all_sub_encode (add_res c s))"
  apply (cases s)
   apply (simp add: cons0 sub_cons  flip: list_encode.simps)
  subgoal for a xs 
    apply(cases a)
       apply (auto simp add:cons0 sub_cons list_encode_eq sub_hd sub_tl  simp flip: list_encode.simps)
                   apply(auto simp add: Let_def sub_hd sub_tl simp flip: list_encode.simps(2)) 
    done
  done

function (sequential, domintros) all_subprograms_stack :: "all_sub list \<Rightarrow> com list" where 
"all_subprograms_stack (Bot x#s) = x"|
"all_subprograms_stack (SKIP # s) = all_subprograms_stack (add_res  [com.SKIP] s )"|
"all_subprograms_stack (Assign v b # s) = all_subprograms_stack (add_res [(com.Assign v b), com.SKIP] s )"|
"all_subprograms_stack (Seq_0 c1 c2 # s) = all_subprograms_stack (push_stack c1 (Seq_0 c1 c2 # s) )"|
"all_subprograms_stack (Seq_m c1 c2 c3 # s) = all_subprograms_stack (push_stack c2 (Seq_m c1 c2 c3 # s))"|
"all_subprograms_stack (Seq_f c1 c2 c3 c4 #s) = all_subprograms_stack (add_res ((map (\<lambda> c. c ;; c2) c3 ) @ c3 
  @ c4) s) "|
"all_subprograms_stack (If_0 v c1 c2 # s) = all_subprograms_stack (push_stack c1 (If_0 v c1 c2 # s))"|
"all_subprograms_stack (If_m v c1 c2 c3 # s) = all_subprograms_stack (push_stack c2 (If_m v c1 c2 c3 # s)) "|
"all_subprograms_stack (If_f v c1 c2 c3 c4 # s) = all_subprograms_stack (add_res (
[(com.If v c1 c2)] @ c3 @ c4 ) s )"|
"all_subprograms_stack (While_0 v c # s) = all_subprograms_stack (push_stack c (While_0 v c # s) )"|
"all_subprograms_stack (While_f v c c' # s) = all_subprograms_stack (add_res ([(While v c), com.SKIP] @ c' @ 
  (map (\<lambda> x. x ;; (While v c))  c')) s)"
  by pat_completeness auto

function all_subprograms_stack_nat :: "nat  \<Rightarrow> nat" where 
"all_subprograms_stack_nat s = (let h = hd_nat s; con = hd_nat h ; fs = nth_nat (Suc 0) h ; sn = nth_nat (Suc (Suc 0)) h;
       th = nth_nat (Suc (Suc (Suc 0))) h; ft = nth_nat (Suc (Suc (Suc (Suc 0)))) h; v = nth_nat (Suc (Suc (Suc (Suc (Suc 0))))) h;  t = tl_nat s in
if con = 10 then  fs else 
if con = 0 then  all_subprograms_stack_nat (add_res_nat  ((0##0)##0) t ) else
if con = 1 then  all_subprograms_stack_nat (add_res_nat   (h##(0##0)##0)  t ) else 
if con = 2 then all_subprograms_stack_nat (push_stack_nat fs s) else 
if con = 5 then all_subprograms_stack_nat (push_stack_nat sn s) else 
if con = 6 then all_subprograms_stack_nat (add_res_nat (append_nat ( append_nat (map_all_subprograms_tail sn th ) th 
  ) ft) t) else
if con = 3 then all_subprograms_stack_nat (push_stack_nat sn s) else
if con = 7 then all_subprograms_stack_nat (push_stack_nat th s) else
if con = 8 then all_subprograms_stack_nat (add_res_nat (append_nat ((3##fs##sn##th##0)## ft )v) t) else
if con = 4 then all_subprograms_stack_nat (push_stack_nat sn s) else
all_subprograms_stack_nat (add_res_nat ((4##fs##sn##0) ## (0##0) ## append_nat th (map_all_subprograms_tail (4##fs##sn##0) th)) t)
) "
  sorry
termination sorry 

lemma map_singleton:
"[f x] = map f [x]" by auto
lemma sub_all_programs_stack:
"s \<noteq> [] \<Longrightarrow> all_subprograms_stack_nat (list_encode (map all_sub_encode s))
 = list_encode (map comm_encode (all_subprograms_stack s))"
  apply (cases s)
   apply simp
  subgoal  for a xs
    apply(induct s  arbitrary : a xs rule:all_subprograms_stack.induct)
    using push_stack_not_Nil add_res_not_Nil   apply (auto simp only:)
              apply (subst all_subprograms_stack_nat.simps)
   apply (simp add: Let_def sub_nth sub_hd sub_cons
              del: all_subprograms_stack_nat.simps 
                list_encode.simps nth_nat.simps add_res_nat.simps push_stack.simps )
   apply (subst all_subprograms_stack_nat.simps)
   apply (simp add: Let_def sub_nth sub_hd sub_cons sub_tl  cons0
              del: all_subprograms_stack_nat.simps 
                list_encode.simps nth_nat.simps add_res_nat.simps push_stack.simps ) 
             apply(simp only:  add_res.simps sub_add_res map_singleton[of comm_encode]  flip: comm_encode.simps list.map )
    apply (metis neq_Nil_conv)
 apply (subst all_subprograms_stack_nat.simps)
   apply (simp add: Let_def sub_nth sub_hd sub_cons sub_tl  cons0
              del: all_subprograms_stack_nat.simps 
                list_encode.simps nth_nat.simps add_res_nat.simps push_stack.simps ) 
             apply(simp only:  add_res.simps sub_add_res map_singleton[of comm_encode]  flip: One_nat_def comm_encode.simps list.map )
    apply (metis neq_Nil_conv)
     apply (subst all_subprograms_stack_nat.simps)
   apply (simp add: Let_def sub_nth sub_hd sub_cons sub_tl  cons0
              del: all_subprograms_stack_nat.simps 
                list_encode.simps nth_nat.simps add_res_nat.simps push_stack_nat.simps ) 
             apply(simp only:  sub_push_stack   flip: One_nat_def all_sub_encode.simps list.map )
           apply (metis list.exhaust)
  apply (subst all_subprograms_stack_nat.simps)
   apply (simp add: Let_def sub_nth sub_hd sub_cons sub_tl  cons0
              del: all_subprograms_stack_nat.simps 
                list_encode.simps nth_nat.simps add_res_nat.simps push_stack_nat.simps ) 
          apply(simp only:  sub_push_stack   flip: One_nat_def all_sub_encode.simps list.map )
               apply (metis list.exhaust)
 apply (subst all_subprograms_stack_nat.simps)
   apply (simp add: Let_def sub_nth sub_hd sub_cons sub_tl  cons0
              del: all_subprograms_stack_nat.simps 
                list_encode.simps nth_nat.simps add_res_nat.simps push_stack_nat.simps ) 
         apply(simp only: subtail_map_all_subprograms submap_all_subprograms
        sub_map sub_append map_map comp_def sub_cons cons0
  add_res.simps sub_add_res  flip: One_nat_def comm_encode.simps list.map )
    apply (simp only: sub_add_res flip: map_append comp_def[of comm_encode "\<lambda>x. (com.Seq x  _ )"] map_map)
         apply (metis append.assoc neq_Nil_conv)
  apply (subst all_subprograms_stack_nat.simps)
   apply (simp add: Let_def sub_nth sub_hd sub_cons sub_tl  cons0
              del: all_subprograms_stack_nat.simps 
                list_encode.simps nth_nat.simps add_res_nat.simps push_stack_nat.simps ) 
          apply(simp only:  sub_push_stack   flip: One_nat_def all_sub_encode.simps list.map )
        apply (metis list.exhaust)
  apply (subst all_subprograms_stack_nat.simps)
   apply (simp add: Let_def sub_nth sub_hd sub_cons sub_tl  cons0
              del: all_subprograms_stack_nat.simps 
                list_encode.simps nth_nat.simps add_res_nat.simps push_stack_nat.simps ) 
          apply(simp only:  sub_push_stack   flip: One_nat_def all_sub_encode.simps list.map )
       apply (metis list.exhaust)
 apply (subst all_subprograms_stack_nat.simps)
   apply (simp add: Let_def sub_nth sub_hd sub_cons sub_tl  cons0
              del: all_subprograms_stack_nat.simps 
                list_encode.simps nth_nat.simps add_res_nat.simps push_stack_nat.simps ) 
         apply(simp only: subtail_map_all_subprograms submap_all_subprograms
        sub_map sub_append map_map comp_def sub_cons cons0
  add_res.simps sub_add_res  flip: One_nat_def comm_encode.simps list.map map_append)
      apply (metis append_Cons neq_Nil_conv)
  apply (subst all_subprograms_stack_nat.simps)
   apply (simp add: Let_def sub_nth sub_hd sub_cons sub_tl  cons0
              del: all_subprograms_stack_nat.simps 
                list_encode.simps nth_nat.simps add_res_nat.simps push_stack_nat.simps ) 
          apply(simp only:  sub_push_stack   flip: One_nat_def all_sub_encode.simps list.map )
     apply (metis list.exhaust)
 apply (subst all_subprograms_stack_nat.simps)
   apply (simp add: Let_def sub_nth sub_hd sub_cons sub_tl  cons0
              del: all_subprograms_stack_nat.simps 
                list_encode.simps nth_nat.simps add_res_nat.simps push_stack_nat.simps ) 
         apply(simp only: subtail_map_all_subprograms submap_all_subprograms
        sub_map sub_append map_map comp_def sub_cons cons0
  add_res.simps sub_add_res  flip: One_nat_def comm_encode.simps list.map map_append)
    apply (simp only: sub_add_res flip: comp_def [of comm_encode "\<lambda>x. (com.Seq x  (com.While _ _))" ]
          map_map map_append list.map )
    apply (metis list.exhaust)
    done
  done

lemma all_subprograms_stack_correct:
"all_subprograms_stack (push_stack c s) = all_subprograms_stack (add_res (all_subprograms c) s)"
  apply (induct c arbitrary: s )
      apply auto
  done

definition all_subprograms_t :: "com \<Rightarrow> com list" where
"all_subprograms_t c = all_subprograms_stack (push_stack c [] )"

definition all_subprograms_nat :: "nat \<Rightarrow> nat" where 
"all_subprograms_nat c = all_subprograms_stack_nat (push_stack_nat c 0)"

lemma subtailnat_all_subprograms:
"all_subprograms_nat (comm_encode c) = list_encode (map comm_encode (all_subprograms_t c))"
  by (metis all_subprograms_nat_def all_subprograms_t_def list.simps(8) list_encode.simps(1)
 push_stack_not_Nil sub_all_programs_stack sub_push_stack)

lemma sub_all_subprograms_t:
"all_subprograms_t c = all_subprograms c"
  by (simp add: all_subprograms_stack_correct all_subprograms_t_def)

lemma sub_all_subprograms:
 "all_subprograms_nat (comm_encode c) = list_encode(map comm_encode (all_subprograms c))"
  by (simp add: sub_all_subprograms_t subtailnat_all_subprograms)

definition all_subprograms_tail :: "nat \<Rightarrow> nat" where 
"all_subprograms_tail c = all_subprograms_nat c"

lemma subtail_all_subprograms:
"all_subprograms_tail c = all_subprograms_nat c"
  by (simp add: all_subprograms_tail_def)

definition enumerate_subprograms_nat :: "nat \<Rightarrow>nat" where
"enumerate_subprograms_nat c = remdups_nat (all_subprograms_nat c)"

definition enumerate_subprograms_tail :: "nat \<Rightarrow>nat" where
"enumerate_subprograms_tail c = remdups_tail (all_subprograms_tail c)"

lemma subtail_enumerate_subprograms:
"enumerate_subprograms_tail c = enumerate_subprograms_nat c"
  using all_subprograms_tail_def enumerate_subprograms_nat_def 
enumerate_subprograms_tail_def subtail_remdups by auto

lemma sub_enumerate_subprograms:
"enumerate_subprograms_nat (comm_encode c) = list_encode (map comm_encode (enumerate_subprograms c))"
  using comm_inj
  apply (auto simp only: enumerate_subprograms_nat_def enumerate_subprograms_def remdups_map sub_all_subprograms sub_remdups list_encode_eq)
  done

fun all_variables_nat :: "nat \<Rightarrow>nat" where
"all_variables_nat n = (if n=0 \<or> hd_nat n =0 \<or> hd_nat n =2  then 0 else
if hd_nat n = 1 then (nth_nat (Suc 0) n) ## 0 else
nth_nat (Suc 0) n )"

definition all_variables_tail where "all_variables_tail = all_variables_nat"

lemma subtail_all_variables : "all_variables_tail = all_variables_nat" using  all_variables_tail_def by meson

lemma sub_all_variables: "all_variables_nat (comm_encode c) = vname_list_encode (all_variables c)"
  apply (cases c)
      apply (auto simp only:all_variables_nat.simps sub_hd comm_encode.simps head.simps 
              vname_list_encode_def cons0 sub_cons sub_nth nth.simps)
      apply auto
  done

fun map_all_variables:: "nat \<Rightarrow> nat" where 
"map_all_variables n = (if n =0 then 0 else (all_variables_nat (hd_nat n)) ## map_all_variables (tl_nat n) )"

fun map_all_variables_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_all_variables_acc acc n = (if n =0 then acc else map_all_variables_acc ((all_variables_tail (hd_nat n)) ## acc) (tl_nat n) )"

lemma submap_all_variables:
"map_all_variables n = map_nat all_variables_nat n"
  apply (induct n rule:map_all_variables.induct)
  apply auto
  done
lemma  map_all_variables_induct:
" map_all_variables_acc acc n = map_acc all_variables_nat acc n"
  apply(induct acc n rule: map_all_variables_acc.induct)
  apply (auto simp add: subtail_all_variables )
  done

definition map_all_variables_tail :: "nat \<Rightarrow> nat" where 
" map_all_variables_tail n = reverse_nat (map_all_variables_acc 0 n)"

lemma subtail_map_all_variables:
" map_all_variables_tail n  =  map_all_variables n "
  using map_all_variables_tail_def  map_all_variables_induct[of 0 n]
  submap_all_variables subtail_map by presburger


definition enumerate_variables_nat :: "nat \<Rightarrow> nat" where
"enumerate_variables_nat c =
     remdups_nat (concat_nat (map_all_variables (enumerate_subprograms_nat c)))"

definition enumerate_variables_tail :: "nat \<Rightarrow> nat" where
"enumerate_variables_tail c =
     remdups_tail (concat_tail (map_all_variables_tail (enumerate_subprograms_tail c)))"


lemma subtail_enumerate_variables:
"enumerate_variables_tail c = enumerate_variables_nat c "
  by (simp add: enumerate_variables_nat_def enumerate_variables_tail_def subtail_concat 
subtail_enumerate_subprograms subtail_map_all_variables subtail_remdups)

lemma sub_enumerate_variables:
  "enumerate_variables_nat (comm_encode c) = vname_list_encode ( enumerate_variables c)"
  apply 
   (simp only:  submap_all_variables enumerate_variables_nat_def enumerate_variables_def sub_enumerate_subprograms 
                sub_map  map_map)
  apply (simp only: comp_def)
  apply (simp only: sub_all_variables)
  apply (simp only: flip:comp_def) 
  apply (simp only: flip:map_map)
  apply (simp only: vname_list_encode_as_comp)
  apply (simp only: flip:map_map)
  using vname_inj
  apply (simp only: sub_concat sub_remdups comp_apply map_concat flip:remdups_map )
  done


end 