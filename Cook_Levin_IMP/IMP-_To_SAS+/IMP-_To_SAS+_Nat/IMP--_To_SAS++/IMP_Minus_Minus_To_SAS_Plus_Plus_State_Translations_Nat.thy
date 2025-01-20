theory IMP_Minus_Minus_To_SAS_Plus_Plus_State_Translations_Nat
  imports "IMP-_To_SAS+_HOL.IMP_Minus_Minus_To_SAS_Plus_Plus_State_Translations" 
          Primitives
begin


definition imp_minus_state_to_sas_plus_list:: 
      "(com * (vname*bit) list) \<Rightarrow> (variable*domain_element) list" where
"imp_minus_state_to_sas_plus_list ci =(PC,PCV (fst ci))# 
        map  (\<lambda>(x,y). (x, EV y)) (map (\<lambda>(x,y). (VN x, y)) (snd ci))"

lemma inj_vn: "inj VN"
  by (meson injI variable.inject)
   
lemma sublist_imp_minus_state_to_sas_plus_apply:
  "map_of (imp_minus_state_to_sas_plus_list ci) k = 
          imp_minus_state_to_sas_plus (cilist_to_map ci) k"
  apply (cases ci)
  apply (cases k)
  apply (auto simp add: imp_minus_state_to_sas_plus_list_def imp_minus_state_to_sas_plus_def
        map_comp_def map_of_map simp del:map_map)
  subgoal for a b x
    apply (cases "map_of b x")
     apply auto
    subgoal
    proof -
      assume "k = VN x" "map_of b x = None"
      hence "\<forall>y. (x,y) \<notin> set b"
        using weak_map_of_SomeI by force
      hence "\<forall>y. (VN x, y) \<notin> set (map (\<lambda>(x, y). (VN x, y)) b)"
        by auto
      thus ?thesis
        by (metis (no_types, lifting) imageE map_of_eq_None_iff prod.collapse) 
    qed
    using map_of_mapk_SomeI inj_vn by fast
  done

lemma sublist_imp_minus_state_to_sas_plus:
  "map_of (imp_minus_state_to_sas_plus_list ci) = 
          imp_minus_state_to_sas_plus (cilist_to_map ci)"
  using sublist_imp_minus_state_to_sas_plus_apply by blast
    
fun map_impms_sp:: " nat \<Rightarrow> nat" where 
"map_impms_sp n = (if n =0 then 0 else (prod_encode (Suc(fst_nat (hd_nat n)) , prod_encode(0,snd_nat (hd_nat n))))## map_impms_sp (tl_nat n))"

fun map_impms_sp_acc:: " nat \<Rightarrow> nat \<Rightarrow> nat" where
"map_impms_sp_acc acc n = (if n = 0 then acc else map_impms_sp_acc ((prod_encode (Suc(fst_nat (hd_nat n)) , prod_encode(0,snd_nat (hd_nat n))))  ## acc) (tl_nat n) )"

lemma map_impms_sp_induct:
"map_impms_sp_acc acc n = map_acc (\<lambda>x. prod_encode (Suc(fst_nat x) , prod_encode(0,snd_nat x)) ) acc n"
  apply(induct acc n rule: map_impms_sp_acc.induct)
  apply auto
  done

definition map_impms_sp_tail :: "nat \<Rightarrow> nat" where
"map_impms_sp_tail n = reverse_nat (map_impms_sp_acc 0 n)"

lemma submap_immpms_sp:
"map_impms_sp n = map_nat (\<lambda>x. prod_encode (Suc(fst_nat x) , prod_encode(0,snd_nat x)) ) n "
  apply (induct n rule:map_impms_sp.induct)
  apply auto
  done

lemma subtail_map_impms_sp:
"map_impms_sp_tail n = map_impms_sp n"
  using subtail_map map_impms_sp_tail_def map_impms_sp_induct submap_immpms_sp
  by presburger

definition imp_minus_state_to_sas_plus_nat :: "nat \<Rightarrow> nat" where
"imp_minus_state_to_sas_plus_nat ci = (prod_encode (0,prod_encode(1,fst_nat ci)))##
(map_impms_sp (snd_nat ci))"

definition imp_minus_state_to_sas_plus_tail :: "nat \<Rightarrow> nat" where
"imp_minus_state_to_sas_plus_tail ci = (prod_encode (0,prod_encode(1,fst_nat ci)))##
(map_impms_sp_tail (snd_nat ci))"

lemma subtail_imp_minus_state_to_sas_plus:
"imp_minus_state_to_sas_plus_tail ci = imp_minus_state_to_sas_plus_nat ci"
  apply(auto simp only: imp_minus_state_to_sas_plus_nat_def imp_minus_state_to_sas_plus_tail_def
      subtail_map_impms_sp)
  done

lemma subnat_imp_minus_state_to_sas_plus:
"imp_minus_state_to_sas_plus_nat   (cilist_encode ci)
  = list_encode (map sas_assignment_encode (imp_minus_state_to_sas_plus_list ci))  "
  apply (cases ci)
  apply (auto simp only: cilist_encode.simps imp_assignment_list_encode_def
submap_immpms_sp
      imp_minus_state_to_sas_plus_nat_def sub_cons cons0 sub_map sub_snd
                snd_def sub_fst fst_def map_map comp_def imp_assignment_encode.simps 
                   imp_minus_state_to_sas_plus_list_def list.map
                          list_encode_eq
                        split:prod.splits 
                  simp flip: variable_encode.simps domain_element_encode.simps
                            sas_assignment_encode.simps)
  apply(auto simp add: prod_encode_eq sub_fst sub_snd)
  done

lemma sub_imp_minus_state_to_sas_plus:
"sas_state_decode (imp_minus_state_to_sas_plus_nat (cilist_encode ci)) =
      imp_minus_state_to_sas_plus (cilist_to_map ci)"
  
  apply (auto simp only: subnat_imp_minus_state_to_sas_plus
      sas_state_decode_def list_encode_inverse map_map comp_def sas_assignment_id map_idI
 sublist_imp_minus_state_to_sas_plus)
  done



  
    
end