theory HOL_To_IMP_Minus_TSAT_To_IS
  imports
    HOL_To_IMP_Minus_Arithmetics
    Karp21.TSAT_To_IS_List
begin

(*TODO: compiled and verify reduction here + move tairec funds from
Tail_Rec_Funs into corresponding locale *)

(*
subsubsection \<open>tail recursive definition of \<open>sat_is_list\<close>\<close>

text \<open>tail recursive definition of \<open>sat_is_un_1_list\<close>\<close>
definition
  "sat_is_un_1_list_tr F \<equiv>
    let
      p1 = enumerate_tr 0 F;
      p2 = map_tr (\<lambda>(xsa, xsb). map_tr (\<lambda>x. (x, xsa)) xsb) p1;
      p3 = map_tr (\<lambda>xs. product_tr xs xs) p2;
      p4 = map_tr (\<lambda>xs. filter_tr (\<lambda>((a, _), (b, _)). a \<noteq> b) xs) p3;
      p5 = concat_tr p4;
      p6 = map_tr (\<lambda>(a, b).  [a, b]) p5
    in p6"

lemma sat_is_un_1_list_tr_eq: "sat_is_un_1_list_tr = sat_is_un_1_list"
  unfolding sat_is_un_1_list_tr_def sat_is_un_1_list_def tr_simps
  by (rule refl)

text \<open>tail recursive definition of \<open>sat_is_un_2_list\<close>\<close>
definition
  "sat_is_un_2_list_tr F \<equiv>
    let
      p1 = enumerate_tr 0 F;
      p2 = map_tr (\<lambda>(xsa, xsb). map_tr (\<lambda>x. (x, xsa)) xsb) p1;
      p3 = product_tr p2 p2;
      p4 = map_tr (\<lambda>(a, b). product_tr a b) p3;
      p5 = concat_tr p4;
      p6 = filter_tr (\<lambda>((a, _), (b, _)). conflict_lit a b) p5;
      p7 = map_tr (\<lambda>(a, b). [a, b]) p6
    in p7"

lemma sat_is_un_2_list_tr_eq: "sat_is_un_2_list_tr = sat_is_un_2_list"
  unfolding sat_is_un_2_list_tr_def sat_is_un_2_list_def tr_simps
  by (rule refl)

definition
  "sat_is_list_tr F \<equiv> if list_all_tr (\<lambda>xs. length_tr (remdups_tr xs) = 3) F
    then (sat_is_un_1_list_tr F @tr sat_is_un_2_list_tr F, length_tr F)
    else ([], 1)"

lemma sat_is_list_tr_eq: "sat_is_list_tr = sat_is_list"
  unfolding sat_is_list_tr_def sat_is_list_def sat_is_un_1_list_tr_eq sat_is_un_2_list_tr_eq tr_simps
  by (rule refl)

*)

(* subsubsection \<open>Tail recursive definition of \<open>is_vc_list\<close>\<close>

definition
  "is_vc_list_tr \<equiv> \<lambda>(E, k). if k > length_tr (remdups_tr (concat_tr E)) then (E, k) else (E, length_tr (remdups_tr (concat_tr E)) - k)"

lemma is_vc_list_tr_eq: "is_vc_list_tr = is_vc_list"
  unfolding is_vc_list_def is_vc_list_tr_def tr_simps by (rule refl) *)


end