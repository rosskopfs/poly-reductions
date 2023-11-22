theory IMP_Minus_To_SAS_Plus_Nat imports
  Primitives IMP_Minus_To_SAS_Plus IMP_Minus_Max_Constant_Nat
  IMP_Minus_To_IMP_Minus_Minus_nat SAS_Plus_Plus_To_SAS_Plus_Nat
  IMP_Minus_Minus_To_SAS_Plus_Plus_Reduction_Nat

begin


definition max_input_bits_list :: "IMP_Minus_com \<Rightarrow> (vname,nat) assignment list \<Rightarrow> nat \<Rightarrow> nat" where 
" max_input_bits_list c I r = 
 bit_length (max (max (max_list (ran_list I)) r) (max_constant c)) "

definition max_input_bits_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat\<Rightarrow> nat" where 
"max_input_bits_nat c I r =
bit_length (max (max (max_list_nat (ran_nat I)) r) (max_constant_nat c))"

definition max_input_bits_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat\<Rightarrow> nat" where 
"max_input_bits_tail c I r =
bit_length (max (max (max_list_tail (ran_tail I)) r) (max_constant_tail c))"

lemma subtail_max_input_bits:
"max_input_bits_tail c I r = max_input_bits_nat c I r "
  using max_constant_tail_def max_input_bits_nat_def max_input_bits_tail_def
 subtail_max_list subtail_ran by presburger

lemma impm_assignment_simp:"impm_assignment_encode = prod_encode o (\<lambda>(a,b). (vname_encode a,b))"
  apply auto
  done
lemma sublist_max_input_bits:
  assumes "I \<noteq> []"
  shows " max_input_bits_list c I r =  max_input_bits c (map_of I) r"
  using assms ran_list_pre apply (auto simp only: max_input_bits_list_def  max_input_bits_def  simp flip:sub_ran_list  )
  using sub_max_list  by fastforce

lemma subnat_max_input_bits: " max_input_bits_nat (com_encode c) 
(impm_assignment_list_encode  I) r = max_input_bits_list c I r"
  using vname_inj
  apply (auto simp only:max_input_bits_nat_def sub_ran_nat impm_assignment_list_encode_def 
 impm_assignment_simp sub_max_list_nat sub_max_constant ran_inj max_input_bits_list_def simp flip: map_map
)
  done

definition IMP_Minus_initial_to_IMP_Minus_Minus:: "(vname \<rightharpoonup> nat) 
  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (vname \<rightharpoonup> bit)" where
"IMP_Minus_initial_to_IMP_Minus_Minus I n guess_range = (\<lambda>v. 
  (case var_to_operand_bit v of 
    Some (CHR ''a'', k) \<Rightarrow> if k < n then Some Zero else None |
    Some (CHR ''b'', k) \<Rightarrow> if k < n then Some Zero else None | 
    _ \<Rightarrow> (if v = ''carry'' then Some Zero 
  else (IMP_Minus_State_To_IMP_Minus_Minus_partial I n guess_range) v)))" 

definition IMP_Minus_initial_to_IMP_Minus_Minus_list:: "(vname, nat) assignment list 
  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> vname \<Rightarrow> bit option" where
"IMP_Minus_initial_to_IMP_Minus_Minus_list I n guess_range v =
  (case var_to_operand_bit v of 
    Some (CHR ''a'', k) \<Rightarrow> if k < n then Some Zero else None |
    Some (CHR ''b'', k) \<Rightarrow> if k < n then Some Zero else None | 
    _ \<Rightarrow> (if v = ''carry'' then Some Zero 
  else (IMP_Minus_State_To_IMP_Minus_Minus_partial_list I n guess_range) v))" 

lemma sublist_IMP_Minus_initial_to_IMP_Minus_Minus:
"IMP_Minus_initial_to_IMP_Minus_Minus (map_of I) n guess_range v =
IMP_Minus_initial_to_IMP_Minus_Minus_list I n guess_range v"
  apply (auto simp only:IMP_Minus_initial_to_IMP_Minus_Minus_def
sublist_IMP_Minus_State_To_IMP_Minus_Minus_partial
IMP_Minus_initial_to_IMP_Minus_Minus_list_def
)
  done

definition IMP_Minus_initial_to_IMP_Minus_Minus_nat::" nat 
  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"IMP_Minus_initial_to_IMP_Minus_Minus_nat I n guess_range v =
  (let p = var_to_operand_bit_nat v; v' = fst_nat (p-1) ; k = snd_nat (p-1) in if
    p \<noteq> 0 \<and> v' = encode_char (CHR ''a'') then 
    if k < n then Suc 0 else 0 else if  p \<noteq> 0 \<and> v' = encode_char (CHR ''b'')
   then if k < n then Suc 0 else 0  
 else (if v = vname_encode ''carry'' then Suc 0 
  else (IMP_Minus_State_To_IMP_Minus_Minus_partial_nat I n guess_range) v))" 

definition IMP_Minus_initial_to_IMP_Minus_Minus_tail::" nat 
  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"IMP_Minus_initial_to_IMP_Minus_Minus_tail I n guess_range v =
  (let p = var_to_operand_bit_tail v; v' = fst_nat (p-1) ; k = snd_nat (p-1) in if
    p \<noteq> 0 \<and> v' = encode_char (CHR ''a'') then 
    if k < n then Suc 0 else 0 else if  p \<noteq> 0 \<and> v' = encode_char (CHR ''b'')
   then if k < n then Suc 0 else 0  
 else (if v = vname_encode ''carry'' then Suc 0 
  else (IMP_Minus_State_To_IMP_Minus_Minus_partial_tail I n guess_range) v))"

lemma subtail_IMP_Minus_initial_to_IMP_Minus_Minus:
"IMP_Minus_initial_to_IMP_Minus_Minus_tail I n guess_range v = 
IMP_Minus_initial_to_IMP_Minus_Minus_nat I n guess_range v"
  using IMP_Minus_initial_to_IMP_Minus_Minus_nat_def IMP_Minus_initial_to_IMP_Minus_Minus_tail_def 
subtail_IMP_Minus_State_To_IMP_Minus_Minus_partial subtail_var_to_operand_bit by presburger

lemma subnat_IMP_Minus_initial_to_IMP_Minus_Minus:
"IMP_Minus_initial_to_IMP_Minus_Minus_nat (impm_assignment_list_encode I) n guess_range 
(vname_encode v) = 

bit_option_encode (IMP_Minus_initial_to_IMP_Minus_Minus_list I n guess_range v)"
  apply (cases "var_to_operand_bit
        v")
  apply (auto simp add: IMP_Minus_initial_to_IMP_Minus_Minus_nat_def vname_inj_simp Let_def
     sub_var_to_operand_bit  char_nat_option_encode_0 char_inj_simp sub_snd sub_fst
IMP_Minus_initial_to_IMP_Minus_Minus_list_def subnat_IMP_Minus_State_To_IMP_Minus_Minus_partial)
   apply (smt char.case char.exhaust)
  apply (smt char.case char.exhaust)
  done



definition IMP_Minus_to_SAS_Plus_list:: "IMP_Minus_com \<Rightarrow> (vname, nat) assignment list \<Rightarrow> nat \<Rightarrow> (vname, nat) assignment list 
  \<Rightarrow>  nat \<Rightarrow> (var,dom) sas_plus_list_problem" where
"IMP_Minus_to_SAS_Plus_list c I r G t = (let 
  guess_range = max_input_bits_list c I r;
  n = t + guess_range + 1;
  c' = IMP_Minus_To_IMP_Minus_Minus c n;
  I' = 
map (\<lambda>(x,y). (x, the y)) (filter (\<lambda>(x,y) . y \<noteq> None) (map (\<lambda>x. (x,IMP_Minus_State_To_IMP_Minus_Minus_partial_list I n guess_range x)) (enumerate_variables c')))
;

  G' = map (\<lambda>(x,y). (x, the y)) (filter (\<lambda>(x,y) . y \<noteq> None) (map (\<lambda>x. (x,IMP_Minus_State_To_IMP_Minus_Minus_partial_list G n n x)) (enumerate_variables c')))
 in
  SAS_Plus_Plus_To_SAS_Plus_list (imp_minus_minus_to_sas_plus_list c' I' G'))"

lemma sublist_IMP_Minus_to_SAS_Plus:
  assumes "I \<noteq> []"
  shows
" list_problem_to_problem ( IMP_Minus_to_SAS_Plus_list c I r G t)
= IMP_Minus_to_SAS_Plus c (map_of I) r (map_of G) t "
  apply (auto simp only:  IMP_Minus_to_SAS_Plus_list_def
        IMP_Minus_to_SAS_Plus_def Let_def  sublist_imp_minus_minus_to_sas_plus
sublist_SAS_Plus_Plus_To_SAS_Plus
sub_restrict
              
 )
  using assms 
  apply (auto simp add: sublist_max_input_bits sublist_IMP_Minus_State_To_IMP_Minus_Minus_partial 
simp flip:sublist_IMP_Minus_initial_to_IMP_Minus_Minus)
  done

fun map_IMP_Minus_initial_to_IMP_Minus_Minus:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"map_IMP_Minus_initial_to_IMP_Minus_Minus I n guess_range x  =(if x = 0 then 0 else (prod_encode(hd_nat x, IMP_Minus_initial_to_IMP_Minus_Minus_nat I n guess_range (hd_nat x)))## map_IMP_Minus_initial_to_IMP_Minus_Minus I n guess_range (tl_nat x))"

lemma submap_IMP_Minus_initial_to_IMP_Minus_Minus:
"map_IMP_Minus_initial_to_IMP_Minus_Minus I n guess_range x = map_nat (\<lambda>x. prod_encode(x, IMP_Minus_initial_to_IMP_Minus_Minus_nat I n guess_range x))x"
  apply (induct I n guess_range  x rule:map_IMP_Minus_initial_to_IMP_Minus_Minus.induct)
  apply auto
  done

fun map_IMP_Minus_State_To_IMP_Minus_Minus_partial :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_IMP_Minus_State_To_IMP_Minus_Minus_partial I n guess_range x = (if x =0 then 0 else 
( prod_encode(hd_nat x,IMP_Minus_State_To_IMP_Minus_Minus_partial_nat I n guess_range (hd_nat x)))## map_IMP_Minus_State_To_IMP_Minus_Minus_partial I n guess_range (tl_nat x) )"

lemma submap_IMP_Minus_State_To_IMP_Minus_Minus_partial :
"map_IMP_Minus_State_To_IMP_Minus_Minus_partial I n guess_range x = map_nat (\<lambda>x. prod_encode(x,IMP_Minus_State_To_IMP_Minus_Minus_partial_nat I n guess_range x)) x "
  apply(induct I  n guess_range x rule: map_IMP_Minus_State_To_IMP_Minus_Minus_partial.induct)
  apply auto
  done
fun map_IMP_Minus_State_To_IMP_Minus_Minus_partial_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_IMP_Minus_State_To_IMP_Minus_Minus_partial_acc acc I n guess_range x = (if x =0 then acc else  map_IMP_Minus_State_To_IMP_Minus_Minus_partial_acc (
( prod_encode(hd_nat x,IMP_Minus_State_To_IMP_Minus_Minus_partial_nat I n guess_range (hd_nat x)))## acc) I n guess_range (tl_nat x) )"

lemma map_IMP_Minus_State_To_IMP_Minus_Minus_partial_induct:
"map_IMP_Minus_State_To_IMP_Minus_Minus_partial_acc acc  I n guess_range x = 
 map_acc (\<lambda>x. prod_encode(x,IMP_Minus_State_To_IMP_Minus_Minus_partial_nat I n guess_range x)) acc x  "
  apply(induct acc I n guess_range x rule: map_IMP_Minus_State_To_IMP_Minus_Minus_partial_acc.induct)
  apply auto
  done

definition map_IMP_Minus_State_To_IMP_Minus_Minus_partial_tail ::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_IMP_Minus_State_To_IMP_Minus_Minus_partial_tail   I n guess_range x =
reverse_nat (map_IMP_Minus_State_To_IMP_Minus_Minus_partial_acc 0  I n guess_range x)  "

lemma subtail_map_IMP_Minus_State_To_IMP_Minus_Minus_partial:
"map_IMP_Minus_State_To_IMP_Minus_Minus_partial_tail   I n guess_range x =
map_IMP_Minus_State_To_IMP_Minus_Minus_partial   I n guess_range x "
  using IMP_Minus_To_SAS_Plus_Nat.map_IMP_Minus_State_To_IMP_Minus_Minus_partial_induct 
IMP_Minus_To_SAS_Plus_Nat.map_IMP_Minus_State_To_IMP_Minus_Minus_partial_tail_def
 IMP_Minus_To_SAS_Plus_Nat.submap_IMP_Minus_State_To_IMP_Minus_Minus_partial 
subtail_map by presburger

fun filter_none :: "nat \<Rightarrow> nat" where
"filter_none n = (if n =0 then 0 else if snd_nat (hd_nat n) \<noteq> 0 then (hd_nat n) ## (filter_none (tl_nat n)) else filter_none (tl_nat n))"

fun filter_none_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"filter_none_acc acc n = (if n =0 then acc else if snd_nat (hd_nat n) \<noteq> 0 then filter_none_acc ((hd_nat n) ## acc) (tl_nat n) else filter_none_acc acc (tl_nat n))"

lemma subfilter_none :
"filter_none n = filter_nat (\<lambda>n . snd_nat n \<noteq> 0) n"
  apply (induct n rule: filter_none.induct)
  apply auto
  done
lemma filter_none_induct : 
"filter_none_acc acc n = filter_acc (\<lambda>n . snd_nat n \<noteq> 0) acc n"
  apply(induct acc n rule:filter_none_acc.induct)
  apply auto
  done

definition filter_none_tail :: "nat \<Rightarrow> nat" where 
"filter_none_tail n = reverse_nat (filter_none_acc 0 n)"

lemma subtail_filter_none:
"filter_none_tail n = filter_none n"
  using filter_none_induct filter_none_tail_def subfilter_none subtail_filter by presburger

fun map_prod_the :: "nat \<Rightarrow> nat" where 
"map_prod_the n = (if n = 0 then 0 else (prod_encode(fst_nat (hd_nat n), the_nat (snd_nat (hd_nat n)))) ## map_prod_the(tl_nat n) )"

lemma submap_prod_the:
"map_prod_the n = map_nat (\<lambda>n. prod_encode(fst_nat n, the_nat (snd_nat n))) n"
  apply (induct n rule:map_prod_the.induct)
  apply auto
  done

fun map_prod_the_acc :: "nat\<Rightarrow> nat \<Rightarrow> nat" where 
"map_prod_the_acc acc n = (if n = 0 then acc else map_prod_the_acc ( (prod_encode(fst_nat (hd_nat n), the_nat (snd_nat (hd_nat n)))) ## acc) (tl_nat n) )"

lemma map_prod_the_induct:
"map_prod_the_acc acc n = map_acc (\<lambda>n. prod_encode(fst_nat n, the_nat (snd_nat n))) acc n "
  apply(induct acc n rule:map_prod_the_acc.induct)
  apply auto
  done

definition map_prod_the_tail :: "nat \<Rightarrow> nat" where 
"map_prod_the_tail n = reverse_nat (map_prod_the_acc 0 n)"

lemma subtail_map_prod_the:
"map_prod_the_tail n = map_prod_the n"
  using map_prod_the_induct map_prod_the_tail_def submap_prod_the subtail_map by presburger

definition IMP_Minus_to_SAS_Plus_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat
  \<Rightarrow>  nat \<Rightarrow> nat" where
"IMP_Minus_to_SAS_Plus_nat c I r G t = (let 
  guess_range = max_input_bits_nat c I r;
  n = t + guess_range + 1;
  c' = IMP_Minus_To_IMP_Minus_Minus_nat c n;
  I' = 
map_prod_the (filter_none (map_IMP_Minus_State_To_IMP_Minus_Minus_partial I n guess_range (enumerate_variables_nat c')))
;

  G' = map_prod_the (filter_none (map_IMP_Minus_State_To_IMP_Minus_Minus_partial G n n (enumerate_variables_nat c')))
 in
  SAS_Plus_Plus_To_SAS_Plus_nat (imp_minus_minus_to_sas_plus_nat c' I' G'))"


definition IMP_Minus_to_SAS_Plus_tail:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat
  \<Rightarrow>  nat \<Rightarrow> nat" where
"IMP_Minus_to_SAS_Plus_tail c I r G t = (let 
  guess_range = max_input_bits_tail c I r;
  n = t + guess_range + 1;
  c' = IMP_Minus_To_IMP_Minus_Minus_tail c n;
  I' = 
map_prod_the_tail (filter_none_tail (map_IMP_Minus_State_To_IMP_Minus_Minus_partial_tail I n guess_range (enumerate_variables_tail c')))
;

  G' = map_prod_the_tail (filter_none_tail (map_IMP_Minus_State_To_IMP_Minus_Minus_partial_tail G n n (enumerate_variables_tail c')))
 in
  SAS_Plus_Plus_To_SAS_Plus_tail (imp_minus_minus_to_sas_plus_tail c' I' G'))"

lemma subtail_IMP_Minus_to_SAS_Plus:
"IMP_Minus_to_SAS_Plus_tail c I r G t = IMP_Minus_to_SAS_Plus_nat c I r G t "
  using IMP_Minus_To_IMP_Minus_Minus_tail_def
 IMP_Minus_To_SAS_Plus_Nat.subtail_map_IMP_Minus_State_To_IMP_Minus_Minus_partial 
IMP_Minus_to_SAS_Plus_nat_def IMP_Minus_to_SAS_Plus_tail_def subtail_SAS_Plus_Plus_To_SAS_Plus 
subtail_enumerate_variables subtail_filter_none subtail_imp_minus_minus_to_sas_plus
 subtail_map_prod_the subtail_max_input_bits by presburger

lemma thef_bit_option_lambda:"
map (\<lambda>x. prod_encode
                     (vname_encode x,
                      thefn
                       (bit_option_to_option
                         (ff x))))
           (filter
             (\<lambda>x. ff x \<noteq>
                   None)
xs) 
= 
map (\<lambda>x. prod_encode
                     (vname_encode x,
                      bit_encode ( the
                         (ff x))))
           (filter
             (\<lambda>x. ff x \<noteq>
                   None)
xs) 

"
  apply (induct xs)
   apply auto
  done

lemma subnat_IMP_Minus_to_SAS_Plus:
"IMP_Minus_to_SAS_Plus_nat (com_encode c) (impm_assignment_list_encode I) r (impm_assignment_list_encode G) t
=  list_problem_plus_encode (IMP_Minus_to_SAS_Plus_list c I r G t) "
  apply (auto simp only:IMP_Minus_to_SAS_Plus_nat_def submap_IMP_Minus_State_To_IMP_Minus_Minus_partial
          submap_IMP_Minus_initial_to_IMP_Minus_Minus  submap_prod_the  subfilter_none   
         subnat_max_input_bits sub_IMP_Minus_To_IMP_Minus_Minus Let_def
                sub_enumerate_variables vname_list_encode_def sub_map map_map
filter_map sub_fst fst_def sub_snd snd_def
comp_def sub_filter  subnat_SAS_Plus_Plus_To_SAS_Plus
IMP_Minus_to_SAS_Plus_list_def
subnat_IMP_Minus_State_To_IMP_Minus_Minus_partial
bit_option_encode_0 sub_the
subnat_imp_minus_minus_to_sas_plus
subnat_IMP_Minus_initial_to_IMP_Minus_Minus
 subnat_IMP_Minus_initial_to_IMP_Minus_Minus
)
  apply (auto simp only: bit_option_encode_simps comp_def sub_the2 

 thef_bit_option_lambda

imp_assignment_list_encode_def

 simp flip: imp_assignment_encode.simps)
  apply (auto simp only:
subnat_SAS_Plus_Plus_To_SAS_Plus
 subnat_imp_minus_minus_to_sas_plus simp flip:comp_def[of imp_assignment_encode "\<lambda>x.(x, the (IMP_Minus_State_To_IMP_Minus_Minus_partial_list I                             
(t + max_input_bits_list c I r + 1)
(max_input_bits_list c I r)  
                                x))" ]
comp_def[of imp_assignment_encode "\<lambda>x. (x, the (IMP_Minus_State_To_IMP_Minus_Minus_partial_list G
                               (t + max_input_bits_list c I r + 1)
                               (t + max_input_bits_list c I r + 1) x))" ]

 map_map
imp_assignment_list_encode_def
)
proof -
  let ?P = "imp_minus_minus_to_sas_plus_list (IMP_Minus_To_IMP_Minus_Minus c (t + max_input_bits_list c I r + 1))
         (map (\<lambda>x. (x, the (IMP_Minus_State_To_IMP_Minus_Minus_partial_list I
                              (t + max_input_bits_list c I r + 1) (max_input_bits_list c I r) x)))
           (filter
             (\<lambda>x. IMP_Minus_State_To_IMP_Minus_Minus_partial_list I (t + max_input_bits_list c I r + 1)
                    (max_input_bits_list c I r) x \<noteq>
                   None)
             (enumerate_variables (IMP_Minus_To_IMP_Minus_Minus c (t + max_input_bits_list c I r + 1)))))
         (map (\<lambda>x. (x, the (IMP_Minus_State_To_IMP_Minus_Minus_partial_list G
                              (t + max_input_bits_list c I r + 1) (t + max_input_bits_list c I r + 1) x)))
           (filter
             (\<lambda>x. IMP_Minus_State_To_IMP_Minus_Minus_partial_list G (t + max_input_bits_list c I r + 1)
                    (t + max_input_bits_list c I r + 1) x \<noteq>
                   None)
             (enumerate_variables (IMP_Minus_To_IMP_Minus_Minus c (t + max_input_bits_list c I r + 1)))))"
  have "is_valid_problem_sas_plus_plus (list_problem_to_problem ?P)"
    by (auto simp only:sublist_imp_minus_minus_to_sas_plus  imp_minus_minus_to_sas_plus_valid)
  thus " SAS_Plus_Plus_To_SAS_Plus_nat
     (list_problem_encode
       (imp_minus_minus_to_sas_plus_list (IMP_Minus_To_IMP_Minus_Minus c (t + max_input_bits_list c I r + 1))
         (map (\<lambda>x. (x, the (IMP_Minus_State_To_IMP_Minus_Minus_partial_list I
                              (t + max_input_bits_list c I r + 1) (max_input_bits_list c I r) x)))
           (filter
             (\<lambda>x. IMP_Minus_State_To_IMP_Minus_Minus_partial_list I (t + max_input_bits_list c I r + 1)
                    (max_input_bits_list c I r) x \<noteq>
                   None)
             (enumerate_variables (IMP_Minus_To_IMP_Minus_Minus c (t + max_input_bits_list c I r + 1)))))
         (map (\<lambda>x. (x, the (IMP_Minus_State_To_IMP_Minus_Minus_partial_list G
                              (t + max_input_bits_list c I r + 1) (t + max_input_bits_list c I r + 1) x)))
           (filter
             (\<lambda>x. IMP_Minus_State_To_IMP_Minus_Minus_partial_list G (t + max_input_bits_list c I r + 1)
                    (t + max_input_bits_list c I r + 1) x \<noteq>
                   None)
             (enumerate_variables (IMP_Minus_To_IMP_Minus_Minus c (t + max_input_bits_list c I r + 1))))))) =
    list_problem_plus_encode
     (SAS_Plus_Plus_To_SAS_Plus_list
       (imp_minus_minus_to_sas_plus_list (IMP_Minus_To_IMP_Minus_Minus c (t + max_input_bits_list c I r + 1))
         (map (\<lambda>x. (x, the (IMP_Minus_State_To_IMP_Minus_Minus_partial_list I
                              (t + max_input_bits_list c I r + 1) (max_input_bits_list c I r) x)))
           (filter
             (\<lambda>x. IMP_Minus_State_To_IMP_Minus_Minus_partial_list I (t + max_input_bits_list c I r + 1)
                    (max_input_bits_list c I r) x \<noteq>
                   None)
             (enumerate_variables (IMP_Minus_To_IMP_Minus_Minus c (t + max_input_bits_list c I r + 1)))))
         (map (\<lambda>x. (x, the (IMP_Minus_State_To_IMP_Minus_Minus_partial_list G
                              (t + max_input_bits_list c I r + 1) (t + max_input_bits_list c I r + 1) x)))
           (filter
             (\<lambda>x. IMP_Minus_State_To_IMP_Minus_Minus_partial_list G (t + max_input_bits_list c I r + 1)
                    (t + max_input_bits_list c I r + 1) x \<noteq>
                   None)
             (enumerate_variables (IMP_Minus_To_IMP_Minus_Minus c (t + max_input_bits_list c I r + 1)))))))"
    by (auto simp only: subnat_SAS_Plus_Plus_To_SAS_Plus)
qed

end


