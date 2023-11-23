theory Primitives
  imports
    Main
    "HOL-Library.Nat_Bijection"
    IMP_Minus.Com
    IMP_Minus_Minus_Com
    "HOL.String"
    "Verified_SAT_Based_AI_Planning.SAT_Plan_Base"
    "Verified_SAT_Based_AI_Planning.STRIPS_Representation"
    SAS_Plus_Plus
    "HOL-Library.Mapping"
    SAS_Plus_Plus_To_SAS_Plus
    IMP_Minus_Minus_To_SAS_Plus_Plus_State_Translations
    "Poly_Reductions_Lib.Encode_Nat"
begin


type_synonym sas_state = "(variable, domain_element) State_Variable_Representation.state"
type_synonym imp_state =  "vname \<rightharpoonup> bit"

lemma extract_lambda: "(\<lambda>i. f(g i v)) = f o (\<lambda>i .g i v)"
  by auto

lemma extract_lambda2: "(\<lambda>i .g i v) o f = (\<lambda>i. g (f i) v)"
  by auto

type_synonym IMP_Minus_com = Com.com
type_synonym IMP_Minus_Minus_com = com



fun fst_helper where
  "fst_helper (a, b) = a"

fun snd_helper where
  "snd_helper (a, b) = b"

lemma fst_helper_eq: "fst_helper = fst" by fastforce
lemma snd_helper_eq: "snd_helper = snd" by fastforce

function_nat_rewrite_auto fst_helper

function_nat_rewrite_auto snd_helper

definition "fst_nat \<equiv> fst_helper_nat"
definition "snd_nat \<equiv> snd_helper_nat"

lemma fst_nat_equiv:
  fixes enc_'a :: "('a::order_bot) \<Rightarrow> nat"
    and enc_'b :: "('b::order_bot) \<Rightarrow> nat"
  assumes "dec_'a \<circ> enc_'a = id"
    and "dec_'b \<circ> enc_'b = id"
  shows
    "fst_nat (enc_prod enc_'a enc_'b p) = enc_'a (fst p)"
  using fst_helper_nat_equiv assms
  by (subst fst_nat_def, subst fst_helper_eq[symmetric]) blast

lemma snd_nat_equiv:
  fixes enc_'a :: "('a::order_bot) \<Rightarrow> nat"
    and enc_'b :: "('b::order_bot) \<Rightarrow> nat"
  assumes "dec_'a \<circ> enc_'a = id"
    and "dec_'b \<circ> enc_'b = id"
  shows
    "snd_nat (enc_prod enc_'a enc_'b p) = enc_'b (snd p)"
  using snd_helper_nat_equiv assms
  by (subst snd_nat_def, subst snd_helper_eq[symmetric]) blast

lemma eq: "prod_encode (n,m) = (m+n) * (m+n+1) div 2 + n"
  by (simp add: add.commute prod_encode_def triangle_def)

fun head :: "('a::order_bot) list \<Rightarrow> 'a" where
  "head [] = bot"
| "head (x # xs) = x"


function_nat_rewrite_auto head

fun tail :: "'a list \<Rightarrow> 'a list" where
  "tail (x # xs) = xs"
| "tail [] = []"

function_nat_rewrite_auto tail


lemma enc_list_nil: "xs = [] \<longleftrightarrow> enc_list enc_'a xs = 0"
  by(simp add: enc_list.simps prod_encode_def Nil_nat_def Cons_nat_def split: list.split)

(*
lemma [simp]: " tl_nat (Suc v) < Suc v"
  apply (auto simp add:tl_nat_def snd_nat_def)
  by (metis le_imp_less_Suc le_prod_encode_2 prod.exhaust_sel prod_decode_inverse)


lemma [simp]:  "0 < xs \<Longrightarrow> list_encode (tail (list_decode xs)) < xs"
  by (metis (no_types, lifting) Suc_diff_1 Suc_le_eq Suc_le_mono case_prod_beta tail.simps(2)
 le_prod_encode_2
list_decode.simps(2) list_decode_inverse prod.exhaust_sel prod_decode_inverse)

lemma [simp]: "list_encode (tail (case prod_decode v of (x, y) \<Rightarrow> x # list_decode y)) < Suc v"
  by (metis case_prod_beta tail.simps(2) le_imp_less_Suc le_prod_encode_2
 list_decode_inverse prod.exhaust_sel prod_decode_inverse)

*)

fun length_acc :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "length_acc acc [] = acc"
| "length_acc acc (x#xs) = length_acc (1 + acc) xs"

lemma suc_length_acc: "Suc (length_acc acc xs) = length_acc (Suc acc) xs"
  by(induction acc xs rule: length_acc.induct; simp)

ML \<open>
  exists (fn x => String.isPrefix x "Groups.plus_class.plus")
       ["HOL.", \<comment> \<open>\<open>If\<close>, \<open>Let\<close>, and more\<close>
        "Nat.", "Num.", "Groups.", \<comment> \<open>Relating to (natural) numbers\<close>
        "enc"
       ]
\<close>

function_nat_rewrite_auto length_acc
thm length_acc_nat.simps

fun length :: "'a list \<Rightarrow> nat" where
  "length xs = length_acc 0 xs"

declare length.simps[simp del]

lemma length_eq_length: "length xs = List.length xs"
  by(induction xs; simp add: length.simps flip: suc_length_acc)

function_nat_rewrite_auto length


lemma length_acc_add_acc: "length_acc acc xs = acc + (length_acc 0 xs)"
proof(induction xs arbitrary: acc)
  case Nil show ?case by simp
next
  case (Cons _ _ acc) show ?case
    unfolding length_acc.simps
    by (subst Cons[of "1 + acc"], simp add: suc_length_acc)
qed

lemma length_append_add: "length (append xs ys) = length xs + length ys"
  unfolding append_equiv
  by(induction xs; simp add: length.simps length_acc_add_acc[of "Suc 0"])

lemma non_empty_positive: "enc_list enc_'a (x # xs) > 0"
  by(simp add: enc_list.simps prod_encode_def Nil_nat_def Cons_nat_def)


(* fun takeWhile_nat :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat" where
  "takeWhile_nat P xs = (let h = hd_nat xs; t = tl_nat xs in (if xs = 0 then 0 else (if P h
            then cons h (takeWhile_nat P t) else 0)))"

lemma sub_takeWhile:"takeWhile_nat P (list_encode xs) = list_encode (takeWhile P xs) "
  apply (induct xs)
   apply simp
  by (smt cons_def head.simps(2) list.distinct(1) list_decode.simps(1) list_decode_inverse
      list_encode.simps(2) list_encode_eq sub_hd sub_tl tail.simps(2) takeWhile.simps(2)
      takeWhile_nat.simps)




fun dropWhile_nat :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat" where
  "dropWhile_nat P xs = (let h = hd_nat xs; t = tl_nat xs in (if xs = 0 then 0 else (if P h
            then dropWhile_nat P t else xs)))  "

lemma sub_dropWhile: "dropWhile_nat P (list_encode xs) = list_encode (dropWhile P xs)"
  apply (induct xs)
   apply simp
  by (metis dropWhile.simps(2) dropWhile_nat.elims head.simps(2)
      list_decode_inverse nat_less_le non_empty_positive sub_hd sub_tl tail.simps(2)) *)


datatype_nat_encode option

datatype_nat_decode option
declare dec_option.simps[of _ "prod_encode _", simp]


datatype_nat_wellbehaved option
  apply(intro ext)
  subgoal for x
    using assms[THEN pointfree_idE]
    by(induction x rule: option.induct; simp add: enc_option.simps None_nat_def Some_nat_def)
  done

definition enc_vname :: "vname \<Rightarrow> nat" where
  "enc_vname = enc_list enc_char"

definition dec_vname :: "nat \<Rightarrow> vname" where
  "dec_vname = dec_list dec_char"

lemma encoding_vname_wellbehaved: "dec_vname \<circ> enc_vname = id"
  unfolding enc_vname_def dec_vname_def
  using encoding_list_wellbehaved[OF encoding_char_wellbehaved] .

lemmas inj_enc_vname = inj_inverseI[OF encoding_vname_wellbehaved]

definition enc_vname_list :: "string list \<Rightarrow> nat" where
  "enc_vname_list = enc_list enc_vname"

definition dec_vname_list :: "nat \<Rightarrow> string list" where
  "dec_vname_list = dec_list dec_vname"

lemma vname_list_id: "dec_vname_list (enc_vname_list x) = x"
  unfolding enc_vname_list_def dec_vname_list_def
  using encoding_list_wellbehaved[
      OF encoding_vname_wellbehaved,
      THEN pointfree_idE] .

lemma "reverse_acc_nat bot bot = bot"
  by(simp add: reverse_acc_nat.simps prod_decode_def prod_decode_aux.simps)

fun elemof :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "elemof _ [] = False"
| "elemof y (x#xs) = (if (y = x) then True else elemof y xs)"

lemma elemof_set_in: "elemof x xs = (x \<in> set xs)"
  by(induction x xs rule: elemof.induct; simp)

function_nat_rewrite_auto elemof

lemma sub_elemof: "elemof x xs = (x \<in> set xs)"
  by(induction xs; simp)

lemma sub_elemof_nat:
  assumes "dec_'a \<circ> enc_'a = id"
  shows "elemof_nat (enc_'a e) (enc_list enc_'a l) \<noteq> 0 = (e \<in> set l)"
    and "elemof_nat (enc_'a e) (enc_list enc_'a l) = 0 = (e \<notin> set l)"
  using elemof_nat_equiv[OF assms]
  by(simp add: enc_bool.simps sub_elemof prod_encode_def True_nat_def False_nat_def
      split: bool.split)+


fun remdups_acc :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remdups_acc acc [] = acc" |
  "remdups_acc acc (x # xs) =
  (if elemof x xs then remdups_acc acc xs
   else remdups_acc (append acc [x]) xs)"

function_nat_rewrite_auto remdups_acc

lemma append_assoc: "append (append xs ys) zs = append xs (append ys zs)"
  unfolding append_equiv by simp

lemma remdups_acc_append: "remdups_acc acc xs = append acc (remdups_acc [] xs)"
  apply(induction xs arbitrary: acc)
   apply(simp add: append_equiv reverse_equiv[simplified])
  by (metis append_equiv append_assoc remdups_acc.simps(2) self_append_conv2)

lemma "remdups xs = remdups_acc [] xs"
  apply(induction xs; simp add: elemof_set_in)
  by (metis (full_types) append_equiv append_Cons remdups_acc_append)

fun remdups :: "'a list \<Rightarrow> 'a list" where
  "remdups xs = remdups_acc [] xs"

function_nat_rewrite_auto remdups

lemma non_empty_not_zero: "enc_list enc_'a (a # xs) \<noteq> 0"
  using non_empty_positive by simp

lemma prod_sum_less:"0 < x \<Longrightarrow> (x, y) = prod_decode p \<Longrightarrow> x + y < p"
  by (smt Nat.add_0_right Suc_leI add.left_commute add_Suc_right le_imp_less_Suc le_prod_encode_2
      add_mono_thms_linordered_semiring(1) canonically_ordered_monoid_add_class.lessE not_le
      prod.simps(2) prod_decode_inverse prod_encode_def)

lemma prod_sum_less2:"(x, y) = prod_decode p \<Longrightarrow> x + y \<le> p"
  by (metis le_prod_encode_2 less_add_same_cancel2 less_imp_le
      linorder_neqE_nat not_add_less2 prod_decode_inverse prod_sum_less)

lemma prod_snd_less:"0 < x \<Longrightarrow> (x, y) = prod_decode p \<Longrightarrow> y < p"
  using prod_sum_less by (metis add.commute add_lessD1)

lemma prod_snd_less2:"(x, y) = prod_decode p \<Longrightarrow> y \<le> p"
  using prod_sum_less by (metis le_prod_encode_2 prod_decode_inverse)

lemma prod_fst_less2:"(x, y) = prod_decode p \<Longrightarrow> x \<le> p"
  using prod_sum_less by (metis le_prod_encode_1 prod_decode_inverse)

datatype_nat_encode atomExp

lemma enc_atomExp_bot: "enc_atomExp bot = bot"
  by(simp add: enc_atomExp.simps prod_encode_0 bot_atomExp_def bot_nat_def N_nat_def enc_nat.simps)

datatype_nat_decode atomExp
lemmas dec_atomExp_prod_encode_simp[simp] = dec_atomExp.simps[of  "prod_encode _"]

datatype_nat_wellbehaved atomExp
  using encoding_list_wellbehaved[OF encoding_char_wellbehaved, THEN pointfree_idE]
  by (intro ext, simp add: enc_atomExp.simps N_nat_def V_nat_def enc_nat.simps dec_nat.simps
      split: atomExp.split)


datatype_nat_encode aexp

lemma enc_aexp_bot: "enc_aexp bot = bot"
  by(simp add: enc_atomExp.simps enc_aexp.simps prod_encode_0 bot_atomExp_def bot_aexp_def
      bot_nat_def enc_nat.simps A_nat_def N_nat_def)

datatype_nat_decode aexp
lemmas dec_aexp_prod_encode_simp[simp] = dec_aexp.simps[of  "prod_encode _"]

datatype_nat_wellbehaved aexp
  using encoding_atomExp_wellbehaved[THEN pointfree_idE]
  by (intro ext, simp add: enc_aexp.simps Plus_nat_def Sub_nat_def Parity_nat_def RightShift_nat_def
      enc_nat.simps A_nat_def split: aexp.split)


datatype_nat_encode bit

lemma enc_bit_bot: "enc_bit bot = bot"
  by(simp add: enc_bit.simps prod_encode_0 bot_bit_def bot_nat_def Zero_nat_def)

datatype_nat_decode bit
lemmas dec_bit_prod_encode_simp[simp] = dec_bit.simps[of  "prod_encode _"]

datatype_nat_wellbehaved bit
  using encoding_atomExp_wellbehaved[THEN pointfree_idE]
  by (intro ext, simp add: enc_bit.simps Zero_nat_def One_nat_def split: bit.split)

datatype_nat_encode com

lemma enc_com_bot: "enc_com bot = bot"
  by(simp add: enc_com.simps prod_encode_0 bot_com_def bot_nat_def SKIP_nat_def)

datatype_nat_decode com
lemmas dec_com_prod_encode_simp[simp] = dec_com.simps[of  "prod_encode _"]

datatype_nat_wellbehaved com
  apply (intro ext)
  subgoal for x
    using vname_list_id encoding_bit_wellbehaved[THEN pointfree_idE]
      encoding_vname_wellbehaved[THEN pointfree_idE]
    by (induction x rule: com.induct; simp add: dec_vname_def enc_vname_def dec_vname_list_def
        enc_vname_list_def enc_com.simps SKIP_nat_def Assign_nat_def Seq_nat_def If_nat_def
        While_nat_def)
  done

fun nth :: "nat \<Rightarrow> ('a::order_bot) list \<Rightarrow> 'a" where
  "nth _ [] = bot"
| "nth 0 (x # _) = x"
| "nth (Suc n) (_ # xs) = nth n xs"


function_nat_rewrite_auto nth

lemma pos_hd_less[termination_simp]: "x > 0 \<Longrightarrow> head_nat x < x"
  by(simp add: head_nat.simps bot_nat_def fst_prod_decode_less snd_prod_decode_lt_intro)

lemma pos_tl_less[termination_simp]: "x > 0 \<Longrightarrow> tail_nat x < x"
  by(simp add: tail_nat.simps prod_encode_0 snd_prod_decode_less snd_prod_decode_lt_intro
      Nil_nat_def)


(* fun map_nat :: "(nat\<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "map_nat f n = (if n = 0 then 0 else cons (f (hd_nat n)) (map_nat f (tl_nat n)))"

lemma sub_map:"map_nat f (list_encode xs) = list_encode (map f xs)"
  apply (induct xs)
  apply simp
  apply (subst map_nat.simps)
  apply (simp only: sub_hd head.simps sub_cons sub_tl tail.simps)
  apply auto
  done *)

instantiation num :: order_bot
begin

definition bot_num :: "num" where
  "bot_num = Num.num.One"

instance
proof(standard, goal_cases)
  case (1 a)
  then show ?case
    unfolding bot_num_def less_eq_num_def
    by (cases a; simp add: Suc_leI nat_of_num_pos)
qed
end


lemma remdups_map: "inj f \<Longrightarrow> remdups (map f xs) = map f (remdups xs)"
  by (induction xs; simp add: inj_def elemof_set_in)
    (metis append_equiv append_Cons image_iff list.simps(9) remdups_acc_append)


datatype_nat_encode domain_element
datatype_nat_decode domain_element
declare dec_domain_element.simps[of "prod_encode _", simp]

datatype_nat_wellbehaved domain_element
  apply(intro ext)
  subgoal for x
    using encoding_bit_wellbehaved[THEN pointfree_idE] encoding_com_wellbehaved[THEN pointfree_idE]
    by(induction x rule: domain_element.induct; simp add: enc_domain_element.simps EV_nat_def
        PCV_nat_def)
  done

datatype_nat_encode variable
datatype_nat_decode variable
declare dec_variable.simps[of "prod_encode _", simp]

datatype_nat_wellbehaved variable
  apply(intro ext)
  subgoal for x
    using encoding_list_wellbehaved[OF encoding_char_wellbehaved, THEN pointfree_idE]
    by(induction x rule: variable.induct; simp add: enc_variable.simps VN_nat_def PC_nat_def)
  done

definition enc_sas_assignment:: "variable * domain_element \<Rightarrow> nat" where
  "enc_sas_assignment = enc_prod enc_variable enc_domain_element"

definition dec_sas_assignment:: "nat \<Rightarrow> (variable * domain_element)" where
  "dec_sas_assignment = dec_prod dec_variable dec_domain_element"

lemma encoding_sas_assignment_wellbehaved: "dec_sas_assignment \<circ> enc_sas_assignment = id"
  unfolding dec_sas_assignment_def enc_sas_assignment_def
  using
    encoding_prod_wellbehaved[OF encoding_variable_wellbehaved encoding_domain_element_wellbehaved]
  .

definition map_to_list :: "('a,'b) map \<Rightarrow> ('a * 'b) list" where
  "map_to_list s \<equiv> (SOME l. map_of l = s)"

lemma has_map:
  fixes s
  assumes "finite (dom s)"
  shows "\<exists>l. map_of l = s "
proof -
  obtain n where n_def:"n = card (dom s)" by blast
  then show  "\<exists>l. map_of l = s " using assms
  proof (induct n arbitrary:s)
    case 0 then show ?case by simp
  next
    case (Suc n)
    hence "dom s  \<noteq> {}" using card_gt_0_iff by force
    then obtain x where x_def: "x \<in> dom s" by blast
    then obtain y where y_def: "s x = Some y" by fast
    obtain s' where s'_def: "s' = s(x:=None)" by blast
    hence dom':"dom s' = dom s - {x} " by simp
    hence "card (dom s') = n" using x_def Suc by simp
    moreover have "finite (dom s')" using dom' Suc(3) by simp
    ultimately obtain l where "map_of l = s'" using Suc(1) by blast
    then have "map_of ((x,y)#l) = s" using s'_def y_def by auto
    then show ?case by blast
  qed
qed

lemma map_to_list_id: "finite (dom s) \<Longrightarrow> map_of (map_to_list s) = s "
  using has_map
  by (metis (mono_tags) map_to_list_def someI_ex)

definition enc_sas_state ::"sas_state \<Rightarrow> nat" where
  "enc_sas_state xs = enc_list enc_sas_assignment (map_to_list xs)"

definition dec_sas_state :: "nat \<Rightarrow> sas_state" where
  "dec_sas_state n = map_of (dec_list dec_sas_assignment n)"

lemma sas_state_id : "finite (dom x) \<Longrightarrow> dec_sas_state (enc_sas_state x) = x"
  unfolding enc_sas_state_def dec_sas_state_def
  using map_to_list_id
    encoding_list_wellbehaved[OF encoding_sas_assignment_wellbehaved, THEN pointfree_idE]
    encoding_sas_assignment_wellbehaved[THEN pointfree_idE]
  by fastforce

definition enc_imp_assignment:: "vname * bit \<Rightarrow> nat" where
  "enc_imp_assignment = enc_prod enc_vname enc_bit"

definition dec_imp_assignment:: "nat \<Rightarrow> (vname * bit)" where
  "dec_imp_assignment = dec_prod dec_vname dec_bit"

lemma encoding_imp_assignment_wellbehaved: "dec_imp_assignment \<circ> enc_imp_assignment = id"
  unfolding enc_imp_assignment_def dec_imp_assignment_def
  using encoding_prod_wellbehaved[OF encoding_vname_wellbehaved encoding_bit_wellbehaved] .

definition enc_imp_state :: "imp_state \<Rightarrow> nat" where
  "enc_imp_state xs = enc_list (enc_prod enc_vname enc_bit) (map_to_list xs)"

definition dec_imp_state :: "nat \<Rightarrow> imp_state" where
  "dec_imp_state n = map_of (dec_list (dec_prod dec_vname dec_bit) n)"

lemma imp_state_id : "finite (dom x) \<Longrightarrow> dec_imp_state (enc_imp_state x) = x"
  unfolding enc_imp_state_def dec_imp_state_def
  using map_to_list_id encoding_imp_assignment_wellbehaved[THEN pointfree_idE]
    encoding_list_wellbehaved[OF encoding_prod_wellbehaved, OF encoding_vname_wellbehaved
      encoding_bit_wellbehaved, THEN pointfree_idE]
  by fastforce

definition enc_comm_imp_state:: "(com * imp_state) \<Rightarrow> nat" where
  "enc_comm_imp_state = enc_prod enc_com enc_imp_state"

definition dec_comm_imp_state:: "nat \<Rightarrow> (com * imp_state)" where
  "dec_comm_imp_state = dec_prod dec_com dec_imp_state"
thm encoding_prod_wellbehaved

(* Works well for prod here but for other algebraic datatypes? Needs t.pred_t for type t?
   look into BNF? *)
lemma encoding_prod_id_alt:
  assumes "\<And>a b. P1 (a, b) \<Longrightarrow> P2 a"
    and "\<And>a b. P1 (a, b) \<Longrightarrow> P3 b"
    and "\<And>a. P2 a \<Longrightarrow>  dec_'a (enc_'a a) = a"
    and "\<And>b. P3 b \<Longrightarrow> dec_'b (enc_'b b) = b"
  shows "P1 (a,b) \<Longrightarrow> dec_prod dec_'a dec_'b (enc_prod enc_'a enc_'b (a, b)) = (a, b)"
  using assms apply(induction "(a, b)" rule: prod.induct)
  by(auto simp add: enc_prod.simps Pair_nat_def)


(* TODO: Should wellbehavedness lemmas always look like this? *)
lemma encoding_prod_id:
  assumes "dec_'a (enc_'a a) = a"
    and "dec_'b (enc_'b b) = b"
  shows "dec_prod dec_'a dec_'b (enc_prod enc_'a enc_'b (a, b)) = (a, b)"
  using assms by (induction "(a, b)" rule: prod.induct; simp add: enc_prod.simps Pair_nat_def)


lemma comm_imp_state_id:
  "finite (dom (snd x)) \<Longrightarrow> dec_comm_imp_state (enc_comm_imp_state x) = x"
  unfolding enc_comm_imp_state_def dec_comm_imp_state_def
  using encoding_prod_id[where ?enc_'a=enc_com and ?dec_'a=dec_com and ?enc_'b=enc_imp_state and
      ?dec_'b=dec_imp_state] encoding_com_wellbehaved[THEN pointfree_idE] imp_state_id
  by (cases x, simp)

definition enc_imp_assignment_list :: "(vname, bit) assignment list \<Rightarrow> nat" where
  "enc_imp_assignment_list = enc_list (enc_prod enc_vname enc_bit)"

definition dec_imp_assignment_list :: "nat \<Rightarrow> (vname, bit) assignment list" where
  "dec_imp_assignment_list = dec_list (dec_prod dec_vname dec_bit)"

lemma encoding_imp_assignment_list_wellbehaved:
  "dec_imp_assignment_list \<circ> enc_imp_assignment_list = id"
  unfolding dec_imp_assignment_list_def enc_imp_assignment_list_def
  using encoding_list_wellbehaved[OF encoding_prod_wellbehaved,
      OF encoding_vname_wellbehaved encoding_bit_wellbehaved] .

definition enc_cilist :: "(com * (vname * bit) list) \<Rightarrow> nat" where
  "enc_cilist = enc_prod enc_com enc_imp_assignment_list"

definition dec_cilist :: " nat \<Rightarrow> (com * (vname*bit) list)" where
  "dec_cilist = dec_prod dec_com dec_imp_assignment_list"

lemma encoding_cilist_wellbehaved: "dec_cilist \<circ> enc_cilist = id"
  unfolding dec_cilist_def enc_cilist_def
  using
    encoding_prod_wellbehaved[OF encoding_com_wellbehaved encoding_imp_assignment_list_wellbehaved]
  .

fun cilist_to_map:: "(com * (vname * bit) list) \<Rightarrow> (com * imp_state)" where
  "cilist_to_map (c, i) = (c, map_of i)"

(* TODO: make en-/decoder for record types *)
type_synonym operator = "(variable, domain_element) sas_plus_operator"
type_synonym problem = "(variable, domain_element) sas_plus_problem"

instantiation sas_plus_operator_ext :: (order_bot, order_bot, order_bot) order_bot
begin

fun less_eq_sas_plus_operator_ext ::
  "('a, 'b, 'c) sas_plus_operator_scheme \<Rightarrow> ('a, 'b, 'c) sas_plus_operator_scheme \<Rightarrow> bool" where
  "less_eq_sas_plus_operator_ext
    \<lparr>precondition_of = a1, effect_of = b1, \<dots> = c1\<rparr>
    \<lparr>precondition_of = a2, effect_of = b2, \<dots> = c2\<rparr>
       \<longleftrightarrow> (a1 \<le> a2 \<and> b1 \<le> b2 \<and> c1 \<le> c2)"

definition less_sas_plus_operator_ext ::
  "('a, 'b, 'c) sas_plus_operator_scheme \<Rightarrow> ('a, 'b, 'c) sas_plus_operator_scheme \<Rightarrow> bool" where
  "less_sas_plus_operator_ext a b = (a \<le> b \<and> \<not> b \<le> a)"

definition bot_sas_plus_operator_ext :: "('a, 'b, 'c) sas_plus_operator_scheme" where
  "bot_sas_plus_operator_ext = \<lparr>precondition_of = bot,
                                effect_of = bot, \<dots> = bot\<rparr>"

instance
proof(standard, goal_cases)
  case 1 show ?case using less_sas_plus_operator_ext_def by simp
next
  case (2 x) show ?case by (induction x; simp)
next
  case (3 x y z) thus ?case
    by(induction x z arbitrary: y rule: less_eq_sas_plus_operator_ext.induct;
        force elim: less_eq_sas_plus_operator_ext.elims)
next
  case (4 x y) thus ?case
    by(induction x y rule: less_eq_sas_plus_operator_ext.induct;
        force elim: less_eq_sas_plus_operator_ext.elims)
next
  case (5 a)
  then show ?case unfolding bot_sas_plus_operator_ext_def by(cases a; simp)
qed

end

instantiation sas_plus_problem_ext :: (order_bot, order_bot, order_bot) order_bot
begin

fun less_eq_sas_plus_problem_ext ::
  "('a, 'b, 'c) sas_plus_problem_scheme \<Rightarrow> ('a, 'b, 'c) sas_plus_problem_scheme \<Rightarrow> bool" where
  "less_eq_sas_plus_problem_ext
    \<lparr>variables_of = a1,
    operators_of = b1,
    initial_of = c1,
    goal_of = d1,
    range_of = e1,
    \<dots> = f1\<rparr>
    \<lparr>variables_of = a2,
    operators_of = b2,
    initial_of = c2,
    goal_of = d2,
    range_of = e2,
    \<dots> = f2\<rparr>
       \<longleftrightarrow> (a1 \<le> a2 \<and> b1 \<le> b2 \<and> c1 \<le> c2 \<and> d1 \<le> d2 \<and> e1 \<le> e2 \<and> f1 \<le> f2)"

definition less_sas_plus_problem_ext ::
  "('a, 'b, 'c) sas_plus_problem_scheme \<Rightarrow> ('a, 'b, 'c) sas_plus_problem_scheme \<Rightarrow> bool" where
  "less_sas_plus_problem_ext a b = (a \<le> b \<and> \<not> b \<le> a)"

definition bot_sas_plus_problem_ext :: "('a, 'b, 'c) sas_plus_problem_scheme" where
  "bot_sas_plus_problem_ext =
  \<lparr>variables_of = bot,
  operators_of = bot,
  initial_of = bot,
  goal_of = bot,
  range_of = bot,
  \<dots> = bot\<rparr>"

instance
proof(standard, goal_cases)
  case 1 show ?case using less_sas_plus_problem_ext_def by simp
next
  case (2 x) show ?case by (induction x; simp)
next
  case (3 x y z) thus ?case
    by(induction x z arbitrary: y rule: less_eq_sas_plus_problem_ext.induct;
        force elim: less_eq_sas_plus_problem_ext.elims)
next
  case (4 x y) thus ?case
    by(induction x y rule: less_eq_sas_plus_problem_ext.induct;
        force elim: less_eq_sas_plus_problem_ext.elims)
next
  case (5 a)
  then show ?case unfolding bot_sas_plus_problem_ext_def by(cases a; simp)
qed

end

definition enc_sas_assignment_list :: "(variable, domain_element) assignment list \<Rightarrow> nat" where
  "enc_sas_assignment_list = enc_list (enc_prod enc_variable enc_domain_element)"

definition dec_sas_assignment_list :: "nat \<Rightarrow> (variable, domain_element) assignment list" where
  "dec_sas_assignment_list = dec_list (dec_prod dec_variable dec_domain_element)"

lemma encoding_sas_assignment_list_wellbehaved:
  "dec_sas_assignment_list \<circ> enc_sas_assignment_list = id"
  unfolding dec_sas_assignment_list_def enc_sas_assignment_list_def
  using encoding_list_wellbehaved[OF encoding_prod_wellbehaved, OF encoding_variable_wellbehaved
      encoding_domain_element_wellbehaved] .

(* ad hoc manually written en-/decoder as there is no automatic conversion for record types yet *)
definition enc_operator :: "operator \<Rightarrow> nat" where
  "enc_operator op = enc_list enc_nat [enc_sas_assignment_list (precondition_of op),
                                          enc_sas_assignment_list (effect_of op)]"

definition dec_operator :: "nat \<Rightarrow> operator" where
  "dec_operator n = (case dec_list dec_nat n of [p, e] \<Rightarrow>
                        \<lparr>precondition_of = dec_sas_assignment_list p,
                         effect_of = dec_sas_assignment_list e\<rparr>)"

lemma encoding_operator_wellbehaved: "dec_operator \<circ> enc_operator = id"
  apply(rule ext)
  unfolding enc_operator_def dec_operator_def
  using encoding_sas_assignment_list_wellbehaved[THEN pointfree_idE]
    encoding_list_wellbehaved[OF encoding_nat_wellbehaved, THEN pointfree_idE]
  by(simp)

fun list_update_acc :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "list_update_acc acc [] _ _ = acc"
| "list_update_acc acc (x # xs) 0 v = append acc (v # xs)"
| "list_update_acc acc (x # xs) (Suc i) v = list_update_acc (append acc [x]) xs i v"

lemma list_update_acc_append: "list_update_acc acc xs i v = acc @ list_update xs i v"
  using append_equiv by(induction acc xs i v rule: list_update_acc.induct; force)

fun list_update where
  "list_update xs i v = list_update_acc [] xs i v"

lemma list_update_equiv: "list_update xs i v = List.list_update xs i v"
  by (simp add: list_update_acc_append)

function_nat_rewrite_auto list_update_acc

function_nat_rewrite_auto list_update

fun restrict_acc ::
  "('vname, 'bit) assignment list \<Rightarrow> ('vname, 'bit) assignment list \<Rightarrow> 'vname list
    \<Rightarrow> ('vname, 'bit) assignment list"
  where
    "restrict_acc acc [] s = acc" |
    "restrict_acc acc ((x, y) # xs) s =
    (if elemof x s then restrict_acc (append acc [(x, y)]) xs s else restrict_acc acc xs s)"

lemma restrict_acc_append: "restrict_acc acc xs s = append acc (restrict_acc [] xs s)"
  by(induction acc xs s arbitrary: acc s rule: restrict_acc.induct;
      simp add: append_equiv elemof_set_in del: append.simps)
    (metis append.assoc)



function_nat_rewrite_auto restrict_acc
function_nat_rewrite restrict_acc


function_nat_rewrite_correctness restrict_acc
proof(induction arg\<^sub>1 arg\<^sub>2 arg\<^sub>3 rule: restrict_acc.induct)
  case (1 acc s)
  show ?case
    apply(subst restrict_acc.simps)
    apply(subst restrict_acc_nat.simps)
    using encoding_list_wellbehaved[OF encoding_prod_wellbehaved, OF assms(3) assms(1), THEN pointfree_idE]
    apply(simp add: enc_list.simps enc_prod.simps Nil_nat_def)
    done
next
  case (2 acc x y xs s)
  have h1: "(fstP (enc_list (enc_prod enc_'a enc_'b) ((x, y) # xs)) = atomic 0) = False"
    by(simp add: enc_list.simps Cons_nat_def)
  have h2: "sndP (sndP (enc_list (enc_prod enc_'a enc_'b) ((x, y) # xs))) =
      enc_list (enc_prod enc_'a enc_'b) xs"
    by(simp add: enc_list.simps Cons_nat_def)
  have h3: "sndP (sndP (fstP (sndP (enc_list (enc_prod enc_'a enc_'b) ((x, y) # xs))))) = enc_'b y"
    by(simp add: enc_list.simps enc_prod.simps Cons_nat_def Pair_nat_def)
  have h4: "fstP (sndP (fstP (sndP (enc_list (enc_prod enc_'a enc_'b) ((x, y) # xs))))) = enc_'a x"
    by(simp add: enc_list.simps enc_prod.simps Cons_nat_def Pair_nat_def)
  show ?case
    apply(subst restrict_acc.simps)
    apply(subst restrict_acc_nat.simps)
    apply(simp only: h1 if_False)
    apply(simp only: h2 h3 h4 Let_def)
    
    apply(subst Pair_nat_equiv[OF assms(1) assms(3), of x y])
    apply(subst elemof_nat_equiv[OF assms(3), of x s])
    apply(subst Nil_nat_equiv[OF encoding_prod_wellbehaved, OF assms(3) assms(1)])
    apply(subst Cons_nat_equiv[OF encoding_prod_wellbehaved, OF assms(3) assms(1), of "(x,y)"])
    apply(subst append_nat_equiv[OF encoding_prod_wellbehaved, OF assms(3) assms(1), of acc "[(x,y)]"])

    apply(simp only: encoding_bool_wellbehaved[THEN pointfree_idE])
    using 2 by simp

qed


fun restrict :: "('vname, 'bit) assignment list \<Rightarrow> 'vname list \<Rightarrow> ('vname, 'bit) assignment list"
  where
    "restrict xs s = restrict_acc [] xs s"

function_nat_rewrite_auto restrict
function_nat_rewrite restrict
function_nat_rewrite_correctness restrict
  using restrict_acc_nat_equiv[OF assms]
  by (metis Nil_nat_equiv assms(3) bot_list_def enc_list_bot restrict.elims restrict_nat.simps)

lemma sub_restrict_helper:
  "map_of (restrict xs s) t = restrict_map (map_of xs) (set s) t"
  apply (induction xs)
  by (auto simp add: restrict_map_def elemof_set_in)
    (metis append_equiv append_Cons restrict_acc_append map_of_Cons_code(2))+

lemma sub_restrict:
  "map_of (restrict xs s) = restrict_map (map_of xs) (set s)"
  using sub_restrict_helper by fast


(* TODO: remove restrict_list and only use restrict and auto generated restrict_nat *)
fun restrict_list ::
  "('vname, 'bit) assignment list \<Rightarrow> 'vname list \<Rightarrow> ('vname, 'bit) assignment list" where
  "restrict_list [] s = []" |
  "restrict_list ((x, y) # xs) s =
    (if x \<in> set s then (x, y) # (restrict_list xs s) else restrict_list xs s)"

lemma "restrict xs s = restrict_list xs s"
  apply(induction xs s rule: restrict_list.induct)
   apply (simp)
  subgoal for x y xs s
    using restrict_acc_append[of "[(x, y)]"] by (simp add: elemof_set_in)
  done

lemma sub_restrict_list_helper:
  "map_of (restrict_list xs s) t = restrict_map (map_of xs) (set s) t"
  by (induction xs; fastforce simp add: restrict_map_def)

lemma sub_restrict_list:
  "map_of (restrict_list xs s) = restrict_map (map_of xs) (set s)"
  using sub_restrict_list_helper by fast


record  ('variable, 'domain) sas_plus_list_problem =
  variables_ofl :: "'variable list" ("(_\<^sub>\<V>\<^sub>+)" [1000] 999)
  operators_ofl :: "('variable, 'domain) sas_plus_operator list" ("(_\<^sub>\<O>\<^sub>+)" [1000] 999)
  initial_ofl :: "('variable, 'domain) assignment list" ("(_\<^sub>I\<^sub>+)" [1000] 999)
  goal_ofl :: "('variable, 'domain) assignment list" ("(_\<^sub>G\<^sub>+)" [1000] 999)
  range_ofl :: "('variable, 'domain list) assignment list"

instantiation sas_plus_list_problem_ext :: (order_bot, order_bot, order_bot) order_bot
begin

fun less_eq_sas_plus_list_problem_ext ::
  "('a, 'b, 'c) sas_plus_list_problem_scheme \<Rightarrow> ('a, 'b, 'c) sas_plus_list_problem_scheme \<Rightarrow> bool" where
  "less_eq_sas_plus_list_problem_ext
    \<lparr>variables_ofl = a1,
    operators_ofl = b1,
    initial_ofl = c1,
    goal_ofl = d1,
    range_ofl = e1,
    \<dots> = f1\<rparr>
    \<lparr>variables_ofl = a2,
    operators_ofl = b2,
    initial_ofl = c2,
    goal_ofl = d2,
    range_ofl = e2,
    \<dots> = f2\<rparr>
       \<longleftrightarrow> (a1 \<le> a2 \<and> b1 \<le> b2 \<and> c1 \<le> c2 \<and> d1 \<le> d2 \<and> e1 \<le> e2 \<and> f1 \<le> f2)"

definition less_sas_plus_list_problem_ext ::
  "('a, 'b, 'c) sas_plus_list_problem_scheme \<Rightarrow> ('a, 'b, 'c) sas_plus_list_problem_scheme \<Rightarrow> bool" where
  "less_sas_plus_list_problem_ext a b = (a \<le> b \<and> \<not> b \<le> a)"

definition bot_sas_plus_list_problem_ext :: "('a, 'b, 'c) sas_plus_list_problem_scheme" where
  "bot_sas_plus_list_problem_ext =
  \<lparr>variables_ofl = bot,
  operators_ofl = bot,
  initial_ofl = bot,
  goal_ofl = bot,
  range_ofl = bot,
  \<dots> = bot\<rparr>"

instance
proof(standard, goal_cases)
  case 1 show ?case using less_sas_plus_list_problem_ext_def by simp
next
  case (2 x) show ?case by (induction x; simp)
next
  case (3 x y z) thus ?case
    by(induction x z arbitrary: y rule: less_eq_sas_plus_list_problem_ext.induct;
        force elim: less_eq_sas_plus_list_problem_ext.elims)
next
  case (4 x y) thus ?case
    by(induction x y rule: less_eq_sas_plus_list_problem_ext.induct;
        force elim: less_eq_sas_plus_list_problem_ext.elims)
next
  case (5 a)
  then show ?case unfolding bot_sas_plus_list_problem_ext_def by(cases a; simp)
qed

end

definition enc_vdlist :: "(variable, domain_element list) assignment \<Rightarrow> nat" where
  "enc_vdlist = enc_prod enc_variable (enc_list enc_domain_element)"

definition dec_vdlist :: "nat \<Rightarrow> (variable, domain_element list) assignment" where
  "dec_vdlist = dec_prod dec_variable (dec_list dec_domain_element)"

lemma encoding_vdlist_wellbehaved: "dec_vdlist \<circ> enc_vdlist = id"
  unfolding dec_vdlist_def enc_vdlist_def
  using encoding_prod_wellbehaved[OF encoding_variable_wellbehaved
      encoding_list_wellbehaved[OF encoding_domain_element_wellbehaved]] .

fun list_problem_to_problem :: "('v, 'd) sas_plus_list_problem \<Rightarrow> ('v, 'd) sas_plus_problem" where
  "list_problem_to_problem x =
    \<lparr>variables_of = variables_ofl x,
     operators_of = operators_ofl x,
     initial_of = map_of (initial_ofl x),
     goal_of = map_of (goal_ofl x),
     range_of = map_of (range_ofl x)\<rparr>"

(* ad hoc manually written en-/decoder as there is no automatic conversion for record types yet *)
definition enc_list_problem :: "(variable, domain_element) sas_plus_list_problem \<Rightarrow> nat" where
  "enc_list_problem x = enc_list enc_nat [enc_list enc_variable (variables_ofl x),
                                          enc_list enc_operator (operators_ofl x),
                                          enc_sas_assignment_list (initial_ofl x),
                                          enc_sas_assignment_list (goal_ofl x),
                                          enc_list enc_vdlist (range_ofl x)]"

definition dec_list_problem ::"nat \<Rightarrow> (variable, domain_element) sas_plus_list_problem" where
  "dec_list_problem x = (case dec_list dec_nat x of [var,op,i,g,r] \<Rightarrow>
                               \<lparr>variables_ofl = dec_list dec_variable var,
                               operators_ofl = dec_list dec_operator op,
                               initial_ofl = dec_sas_assignment_list i,
                               goal_ofl = dec_sas_assignment_list g,
                               range_ofl = dec_list dec_vdlist r\<rparr>)"

lemma encoding_list_problem_wellbehaved: "dec_list_problem \<circ> enc_list_problem = id"
  apply(rule ext)
  unfolding enc_list_problem_def dec_list_problem_def
  using
    encoding_list_wellbehaved[OF encoding_variable_wellbehaved, THEN pointfree_idE]
    encoding_list_wellbehaved[OF encoding_operator_wellbehaved, THEN pointfree_idE]
    encoding_sas_assignment_list_wellbehaved[THEN pointfree_idE]
    encoding_list_wellbehaved[OF encoding_vdlist_wellbehaved, THEN pointfree_idE]
    encoding_list_wellbehaved[OF encoding_nat_wellbehaved, THEN pointfree_idE]
  by(simp)

(* We have to define a type alias because the type "variable" is already defined *)
type_alias sas_variable = SAS_Plus_Plus_To_SAS_Plus.variable
datatype_nat_encode sas_variable
datatype_nat_decode sas_variable
termination by (decode_termination "measure snd")
datatype_nat_wellbehaved sas_variable
  apply(intro ext)
  subgoal for x
    using assms[THEN pointfree_idE]
    by(induction x rule: SAS_Plus_Plus_To_SAS_Plus.variable.induct; simp add: enc_list.simps)
  done

type_synonym  var = "variable sas_variable"

definition enc_var :: "var \<Rightarrow> nat" where
  "enc_var = enc_sas_variable enc_variable"

definition dec_var :: "nat \<Rightarrow> var" where
  "dec_var = dec_sas_variable dec_variable"

lemma encoding_var_wellbehaved: "dec_var \<circ> enc_var = id"
  unfolding dec_var_def enc_var_def
  using encoding_sas_variable_wellbehaved[OF encoding_variable_wellbehaved] .

type_alias sas_domain_element = SAS_Plus_Plus_To_SAS_Plus.domain_element
datatype_nat_encode sas_domain_element
datatype_nat_decode sas_domain_element
termination by (decode_termination "measure snd")
datatype_nat_wellbehaved sas_domain_element
  apply(intro ext)
  subgoal for x
    using assms[THEN pointfree_idE]
    by(induction x rule: SAS_Plus_Plus_To_SAS_Plus.domain_element.induct; simp add: enc_list.simps)
  done

type_synonym  dom = "domain_element sas_domain_element"

definition enc_dom :: "dom \<Rightarrow> nat" where
  "enc_dom = enc_sas_domain_element enc_domain_element"

definition dec_dom :: "nat \<Rightarrow> dom" where
  "dec_dom = dec_sas_domain_element dec_domain_element"

lemma encoding_dom_wellbehaved: "dec_dom \<circ> enc_dom = id"
  unfolding dec_dom_def enc_dom_def
  using encoding_sas_domain_element_wellbehaved[OF encoding_domain_element_wellbehaved] .

definition enc_sas_plus_assignment :: "(var, dom) assignment \<Rightarrow> nat" where
  "enc_sas_plus_assignment = enc_prod enc_var enc_dom"

definition dec_sas_plus_assignment:: "nat \<Rightarrow> (var, dom) assignment" where
  "dec_sas_plus_assignment = dec_prod dec_var dec_dom"

lemma encoding_sas_plus_assignment_wellbehaved:
  "dec_sas_plus_assignment \<circ> enc_sas_plus_assignment = id"
  unfolding dec_sas_plus_assignment_def enc_sas_plus_assignment_def
  using encoding_prod_wellbehaved[OF encoding_var_wellbehaved encoding_dom_wellbehaved] .

definition enc_sas_plus_assignment_list ::  "(var, dom) assignment list \<Rightarrow> nat" where
  "enc_sas_plus_assignment_list = enc_list enc_sas_plus_assignment"

definition dec_sas_plus_assignment_list ::  "nat \<Rightarrow> (var, dom) assignment list" where
  "dec_sas_plus_assignment_list = dec_list dec_sas_plus_assignment"

lemma encoding_sas_plus_assignment_list_wellbehaved:
  "dec_sas_plus_assignment_list \<circ> enc_sas_plus_assignment_list = id"
  unfolding dec_sas_plus_assignment_list_def enc_sas_plus_assignment_list_def
  using encoding_list_wellbehaved[OF encoding_sas_plus_assignment_wellbehaved] .

definition enc_islist :: "(dom \<times> (variable, domain_element) assignment list) \<Rightarrow> nat" where
  "enc_islist = enc_prod enc_dom enc_sas_assignment_list"

definition dec_islist :: "nat \<Rightarrow> (dom \<times> (variable, domain_element) assignment list)" where
  "dec_islist = dec_prod dec_dom dec_sas_assignment_list"

lemma encoding_islist_wellbehaved: "dec_islist \<circ> enc_islist = id"
  unfolding dec_islist_def enc_islist_def
  using encoding_prod_wellbehaved[OF encoding_dom_wellbehaved encoding_sas_assignment_list_wellbehaved]
  .

fun islist_to_map:: "(dom \<times> (variable, domain_element) assignment list) \<Rightarrow> (dom \<times> sas_state)" where
  "islist_to_map (i,s) = (i, map_of s)"

type_synonym  sas_plus_state = "(var, dom) State_Variable_Representation.state"

definition dec_sas_plus_state :: "nat \<Rightarrow> sas_plus_state" where
  "dec_sas_plus_state x = map_of (dec_list (dec_prod dec_var dec_dom) x)"

type_synonym operator_plus = "(var, dom) sas_plus_operator"
type_synonym problem_plus = "(var, dom) sas_plus_problem"

definition enc_operator_plus :: "operator_plus \<Rightarrow> nat" where
  "enc_operator_plus op = enc_list enc_nat [enc_sas_plus_assignment_list (precondition_of op),
                                            enc_sas_plus_assignment_list (effect_of op)]"

definition dec_operator_plus :: " nat \<Rightarrow> operator_plus" where
  "dec_operator_plus n = (case dec_list dec_nat n of [p, e] \<Rightarrow>
                            \<lparr>precondition_of = dec_sas_plus_assignment_list p,
                             effect_of = dec_sas_plus_assignment_list e\<rparr>)"

lemma encoding_operator_plus_wellbehaved : "dec_operator_plus \<circ> enc_operator_plus = id"
  apply(rule ext)
  unfolding dec_operator_plus_def enc_operator_plus_def
  using encoding_sas_plus_assignment_list_wellbehaved[THEN pointfree_idE]
    encoding_list_wellbehaved[OF encoding_nat_wellbehaved, THEN pointfree_idE]
  by(simp)

fun map_list_find ::"('a, 'b) assignment list \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "map_list_find [] _ = None" |
  "map_list_find ((x, y) # xs) a = (if x = a then Some y else map_list_find xs a)"

lemma sub_map_list_find: "map_list_find xs a = (map_of xs) a"
  by (induct xs; force)


function_nat_rewrite map_list_find
function_nat_rewrite_correctness map_list_find
  by (natfn_correctness \<open>induct arg\<^sub>1 arg\<^sub>2 rule: map_list_find.induct\<close>
      assms: assms
      simps_nat: map_list_find_nat.simps
      enc_simps: enc_list.simps enc_prod.simps Let_def
      args_wellbehaved: inj_inverseI[OF assms(3), THEN injD]
      encoding_prod_wellbehaved[OF assms(3) assms(1), THEN pointfree_idE])
    force

definition enc_vdlist_plus :: "(var, dom list) assignment \<Rightarrow> nat" where
  "enc_vdlist_plus = enc_prod enc_var (enc_list enc_dom)"

definition dec_vdlist_plus ::  "nat \<Rightarrow> (var, dom list) assignment" where
  "dec_vdlist_plus = dec_prod dec_var (dec_list dec_dom)"

lemma encoding_vdlist_plus_wellbehaved: "dec_vdlist_plus \<circ> enc_vdlist_plus = id"
  unfolding dec_vdlist_plus_def enc_vdlist_plus_def
  using encoding_prod_wellbehaved[OF encoding_var_wellbehaved encoding_list_wellbehaved,
      OF encoding_dom_wellbehaved] .

definition enc_list_problem_plus :: "(var, dom) sas_plus_list_problem \<Rightarrow> nat" where
  "enc_list_problem_plus x = enc_list enc_nat [enc_list enc_var (variables_ofl x),
                                               enc_list enc_operator_plus (operators_ofl x),
                                               enc_sas_plus_assignment_list (initial_ofl x),
                                               enc_sas_plus_assignment_list (goal_ofl x),
                                               enc_list enc_vdlist_plus (range_ofl x)]"

definition dec_list_problem_plus :: "nat \<Rightarrow> (var, dom) sas_plus_list_problem" where
  "dec_list_problem_plus x = (case dec_list dec_nat x of [var,op,i,g,r]  \<Rightarrow>
                                    \<lparr>variables_ofl = dec_list dec_var var,
                                     operators_ofl = dec_list dec_operator_plus op,
                                     initial_ofl = dec_sas_plus_assignment_list i,
                                     goal_ofl = dec_sas_plus_assignment_list g,
                                     range_ofl = dec_list dec_vdlist_plus r\<rparr>)"

lemma encoding_list_problem_plus_wellbehaved: "dec_list_problem_plus \<circ> enc_list_problem_plus = id"
  apply(rule ext)
  unfolding dec_list_problem_plus_def enc_list_problem_plus_def
  using
    encoding_list_wellbehaved[OF encoding_var_wellbehaved, THEN pointfree_idE]
    encoding_list_wellbehaved[OF encoding_operator_plus_wellbehaved, THEN pointfree_idE]
    encoding_sas_plus_assignment_list_wellbehaved[THEN pointfree_idE]
    encoding_list_wellbehaved[OF encoding_vdlist_plus_wellbehaved, THEN pointfree_idE]
    encoding_list_wellbehaved[OF encoding_nat_wellbehaved, THEN pointfree_idE]
  by(simp)


definition fun_of :: "(vname, nat) assignment list \<Rightarrow> vname \<Rightarrow> nat" where
  "fun_of x v =  (case (map_of x) v of None \<Rightarrow> 0 | Some x \<Rightarrow> x)"

fun fun_list_find :: "('a, 'b::bot) assignment list \<Rightarrow> 'a \<Rightarrow> 'b" where
  "fun_list_find [] _ = bot" |
  "fun_list_find ((x, y) # xs) a = (if x = a then y else fun_list_find xs a)"

function_nat_rewrite fun_list_find
function_nat_rewrite_correctness fun_list_find
  by (natfn_correctness \<open>induct arg\<^sub>1 arg\<^sub>2 rule: fun_list_find.induct\<close>
      assms: assms
      simps_nat: fun_list_find_nat.simps
      enc_simps: enc_list.simps enc_prod.simps Let_def
      args_wellbehaved: inj_inverseI[OF assms(3), THEN injD]
      encoding_prod_wellbehaved[OF assms(3) assms(1), THEN pointfree_idE])
    force

lemma sub_fun_list_find: "fun_list_find xs a = fun_of xs a"
  by(induct xs; fastforce simp add: fun_of_def bot_nat_def)


definition enc_impm_assignment :: "(vname, nat) assignment \<Rightarrow> nat" where
  "enc_impm_assignment = enc_prod enc_vname enc_nat"

definition dec_impm_assignment :: "nat \<Rightarrow> (vname, nat) assignment" where
  "dec_impm_assignment = dec_prod dec_vname dec_nat"

lemmas encoding_impm_assignment_wellbehaved =
  encoding_prod_wellbehaved[OF encoding_vname_wellbehaved encoding_nat_wellbehaved,
    folded dec_impm_assignment_def enc_impm_assignment_def]

definition enc_impm_assignment_list :: "(vname, nat) assignment list \<Rightarrow> nat" where
  "enc_impm_assignment_list = enc_list enc_impm_assignment"

definition dec_impm_assignment_list :: "nat \<Rightarrow> (vname, nat) assignment list" where
  "dec_impm_assignment_list = dec_list dec_impm_assignment"

lemmas encoding_impm_assignment_list_wellbehaved =
  encoding_list_wellbehaved [OF encoding_impm_assignment_wellbehaved,
    folded dec_impm_assignment_list_def enc_impm_assignment_list_def]

definition enc_bit_option :: "bit option \<Rightarrow> nat" where
  "enc_bit_option = enc_option enc_bit"

definition dec_bit_option :: "nat \<Rightarrow> bit option" where
  "dec_bit_option = dec_option dec_bit"

lemmas encoding_bit_option_wellbehaved =
  encoding_option_wellbehaved [OF encoding_bit_wellbehaved,
    folded dec_bit_option_def enc_bit_option_def]


lemma inj_fun_list_find:
  "inj f \<Longrightarrow> fun_list_find (map (\<lambda> (x, y). (f x, y) ) xs) (f x) = fun_list_find xs x"
  by (induction xs; fastforce simp add: inj_def)

lemma inj_fun_list_find_plus:
  "inj f \<Longrightarrow> fun_list_find (map (\<lambda>(x,y). (f x, g y) ) xs) (f x) =
              fun_list_find (map (\<lambda>(x,y). (x , g y)) xs) x"
  by (induction xs; fastforce simp add: inj_def)


fun max_list_acc :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "max_list_acc acc [] = acc" |
  "max_list_acc acc (x # xs) = max_list_acc (max acc x) xs"

(* Manually rewrite function as automation can't handle max resp. \<le> *)
function max_list_acc_nat where
  "max_list_acc_nat acc xs = (if fstP xs = atomic 0 then acc
  else max_list_acc_nat (max acc (fstP (sndP xs))) (sndP (sndP xs)))"
  by fast+
termination by(relation "measure snd"; simp add: snd_prod_decode_less snd_prod_decode_lt_intro)
declare max_list_acc_nat.simps[simp del]

function_nat_rewrite_correctness max_list_acc
  apply (natfn_correctness \<open>induct arg\<^sub>1 arg\<^sub>2 rule: max_list_acc.induct\<close>
      simps_nat: max_list_acc_nat.simps
      enc_simps: enc_list.simps
      args_wellbehaved: encoding_list_wellbehaved[OF encoding_nat_wellbehaved])
  unfolding enc_nat.simps by blast

fun max_list :: "nat list \<Rightarrow> nat" where
  "max_list xs = max_list_acc 0 xs"

function_nat_rewrite max_list
function_nat_rewrite_correctness max_list
  using max_list_acc_nat_equiv by(simp add: max_list_nat.simps prod_encode_0)

lemma sub_max_list: "xs \<noteq> [] \<Longrightarrow> max_list xs = Max (set xs)"
proof(induction xs)
  case Nil then show ?case by simp
next
  case (Cons a xs)
  have 1:"xs \<noteq> [] \<Longrightarrow> a \<le> Max (set xs) \<Longrightarrow> max_list_acc a xs = max_list_acc 0 xs"
    by(induction xs arbitrary: a; simp)
      (metis List.finite_set Max_insert Max_singleton max_def set_empty)
  have 2:"xs \<noteq> [] \<Longrightarrow> a > Max (set xs) \<Longrightarrow> max_list_acc a xs = a"
    by(induction xs arbitrary: a; fastforce)
  have 3:"max_list (a # xs) = max_list_acc a xs" by (simp)
  have 4:"Max (set (a # xs)) = a \<or> Max (set (a # xs)) = Max (set xs)"
    by (metis List.finite_set Max_eqI Max_ge Max_in emptyE list.set_intros(2) set_ConsD)
  show ?case using disjE[OF 4] Cons.IH
    by (metis (no_types) 1 2 3 finite_set Max_in Max_insert bex_empty list.set(2)
        list.set_intros(1) max_def max_list.elims max_list_acc.simps(1) not_le_imp_less set_ConsD
        set_empty2)
qed


fun del_acc ::
  "('a, 'b) assignment list \<Rightarrow> ('a, 'b) assignment list \<Rightarrow> 'a \<Rightarrow> ('a, 'b) assignment list" where
  "del_acc acc [] _ = acc" |
  "del_acc acc ((x, y) # xs) a =
    (if x = a then del_acc acc xs a else del_acc (append acc [(x, y)]) xs a)"

function_nat_rewrite del_acc


lemma del_acc_nat_equiv2:
  assumes "(dec_'b::nat \<Rightarrow> 'b::order_bot) \<circ> enc_'b = id"
    and "dec_'b bot = bot"
    and "dec_'a \<circ> enc_'a = id"
    and "dec_'a bot = bot"
  shows "del_acc_nat (enc_list (enc_prod enc_'a enc_'b) acc) (enc_list (enc_prod enc_'a enc_'b) xs) (enc_'a a)
          = enc_list (enc_prod enc_'a enc_'b) (del_acc acc xs a)"
  apply(induction acc xs a rule: del_acc.induct; subst del_acc.simps; subst del_acc_nat.simps)
  subgoal by (simp add: enc_list.simps)
  subgoal for acc x y xs a
    using inj_inverseI[OF assms(3), THEN injD, of x a]
      append_nat_equiv2[OF encoding_prod_wellbehaved, OF assms(3) assms(1), of acc "[(x, y)]"]
    by (fastforce simp: enc_list.simps enc_prod.simps)
  done

function_nat_rewrite_correctness del_acc
  using del_acc_nat_equiv2[OF assms, THEN arg_cong, of "dec_list (dec_prod dec_'a dec_'b)"]
    encoding_list_wellbehaved[OF encoding_prod_wellbehaved, OF assms(3) assms(1), THEN pointfree_idE]
  by(simp)

fun del :: "('a, 'b) assignment list \<Rightarrow> 'a \<Rightarrow> ('a, 'b) assignment list" where
  "del xs a = del_acc [] xs a"
declare del.simps[simp del]

function_nat_rewrite del
function_nat_rewrite_correctness del
  using del_acc_nat_equiv[OF assms, of "[]" arg\<^sub>1 arg\<^sub>2]
  by (simp add: del.simps prod_encode_0 del_nat.simps enc_list.simps)


lemma del_acc_filter: "del_acc acc xs a = append acc (filter (\<lambda>x. fst x \<noteq> a) xs)"
  by(induction xs arbitrary: acc; fastforce simp add: append_equiv simp flip: append.simps)

lemma del_filter: "del xs a = filter (\<lambda>x. fst x \<noteq> a) xs"
  by(simp add: del_acc_filter del.simps)

lemma length_del_dec: "length (del xs x) < Suc (length xs)"
  unfolding length_eq_length
  by (induction xs; simp add: del_filter)

lemma del_correct: "\<forall>(x, y) \<in> set (del xs a). x \<noteq> a"
  by (induction xs; simp add: del_filter split: prod.split)

lemma del_correct_corr: " a \<noteq> x \<Longrightarrow> map_of (del xs a) x = map_of xs x"
  by (induction xs; simp add: del_filter)

function nub_acc :: "('a, 'b) assignment list \<Rightarrow> ('a, 'b) assignment list \<Rightarrow> ('a, 'b) assignment list" where
  "nub_acc acc [] = acc "|
  "nub_acc acc ((x, y) # xs) = nub_acc (append acc [(x, y)]) (del xs x)"
  by (auto, metis clearjunk.cases surj_pair)
termination
  by (relation "measure (length \<circ> snd)";
      simp add: length_eq_length;
      simp add: length_del_dec flip: length_eq_length)



lemma del_nat_equiv2:
  assumes "(dec_'b::nat \<Rightarrow> 'b::order_bot) \<circ> enc_'b = id"
    and "dec_'b bot = bot"
    and "dec_'a \<circ> enc_'a = id"
    and "dec_'a bot = bot"
  shows "del_nat (enc_list (enc_prod enc_'a enc_'b) xs) (enc_'a a)
          = enc_list (enc_prod enc_'a enc_'b) (del xs a)"
  apply(induction xs a rule: del.induct; subst del.simps; subst del_nat.simps)
  using del_acc_nat_equiv2[OF assms, of "[]"]
  by(simp add: enc_list.simps)


declare append.simps[simp del]
function_nat_rewrite nub_acc
function_nat_rewrite_correctness nub_acc
  apply(induction arg\<^sub>1 arg\<^sub>2 rule: nub_acc.induct; subst nub_acc.simps; subst nub_acc_nat.simps)
  subgoal
    using encoding_list_wellbehaved[OF encoding_prod_wellbehaved, OF assms(3) assms(1),
        THEN pointfree_idE]
    by(simp add: enc_list.simps)
  subgoal for acc x y xs
    using append_nat_equiv2[OF encoding_prod_wellbehaved, OF assms(3) assms(1), of acc "[(x, y)]"]
      del_nat_equiv2[OF assms]
    by(simp add: enc_list.simps, simp add: enc_prod.simps)
  done


function nub :: "('a, 'b) assignment list \<Rightarrow> ('a, 'b) assignment list" where
  "nub [] = [] "|
  "nub ((x, y) # xs) = (x, y) # nub (del xs x)"
  by (auto, metis clearjunk.cases surj_pair)
termination
  by (relation "measure length"; simp add: length_eq_length)
    (simp add: length_del_dec flip: length_eq_length)

lemma 1:"nub_acc (acc1 @ acc2) xs = acc1 @ (nub_acc acc2 xs)"
  by(induction acc2 xs rule: nub_acc.induct; simp add: append_equiv del: append.simps)


lemma 2:"nub_acc acc xs = acc @ (nub_acc [] xs)"
  apply(induction acc xs arbitrary: acc rule: nub_acc.induct)
   apply simp
  subgoal premises p for acc x y xs acc1
    by ( simp add: 1 append_equiv p[of "(append acc1 [(x, y)])"] del: append.simps)
  done

lemma "nub xs = nub_acc [] xs"
  apply (induction xs rule:nub.induct)
   apply simp
  subgoal premises p for x y xs
    by (simp add: p 2[of "[(x, y)]" "(del xs x)"])
  done

lemma del_shorter : "length (del xs a) \<le> length xs"
  unfolding length_eq_length
  by (induction xs; simp add: del_filter le_SucI)



function nub_nat :: "nat \<Rightarrow> nat" where
  "nub_nat xs = (if xs = 0 then 0 else (hd_nat xs) ## nub_nat (del_nat xs (fst_nat (hd_nat xs))))"
  by pat_completeness auto
termination
  apply (relation "measure length_nat")
  apply simp
  apply (auto simp del: del_nat.simps)
  subgoal for xs
  proof -
    assume asm:"0 < xs"
    obtain ys where ys_def: "ys = map prod_decode (list_decode xs)" by simp
    then have t:"xs = list_encode (map prod_encode ys)"
      by (auto simp add: comp_def)
    moreover have "ys \<noteq> []" using ys_def asm t by force
    ultimately show  ?thesis  apply (auto simp only: t sub_del sub_length  length_map  sub_hd)
      apply (auto simp add: sub_head_map sub_fst)
      apply (cases ys)
       apply auto
      subgoal for a b xs
        using del_shorter[of xs a] by simp
      done
  qed
  done

lemma sub_nub: "nub_nat (list_encode( map prod_encode xs)) = list_encode (map prod_encode (nub xs))"
  apply (induct xs rule:nub.induct)
   apply simp
   apply (subst nub_nat.simps)
   apply (auto simp only: sub_hd sub_cons  sub_del )
   apply (auto simp add: sub_fst list_encode_eq sub_cons  simp del:nub_nat.simps list_encode.simps(2) simp flip: list_encode.simps(1))
  done


lemma del_includes: "set (del xs x) \<subseteq> set xs"
  apply (induct xs)
   apply (auto split:if_splits)
  done

lemma nub_includes: "set (nub xs) \<subseteq> set xs"
  apply (induct xs rule: nub.induct)
   apply (auto)
  using del_includes apply fast
  using del_includes apply fast
  done

lemma nub_correct : "distinct (map fst (nub xs))"
  apply (induct xs rule:nub.induct)
   apply auto
  using nub_includes del_correct by fastforce

lemma map_of_nub_apply:"map_of (nub xs) x = map_of xs x"
  apply (induct xs rule:nub.induct)
   apply (auto simp add: del_correct_corr)
  done
lemma map_of_nub:"map_of (nub xs)  = map_of xs "
  using map_of_nub_apply by fast


definition ran_list :: "('a,'b) assignment list \<Rightarrow> 'b list" where
  "ran_list xs = map snd (nub xs)"

fun map_snd  :: "nat \<Rightarrow> nat " where
  "map_snd xs = (if xs = 0 then 0 else (snd_nat (hd_nat xs)) ## map_snd (tl_nat xs))"

lemma submap_snd:
  "map_snd xs = map_nat snd_nat xs"
  apply(induct xs rule:map_snd.induct)
  apply auto
  done

definition ran_nat :: "nat \<Rightarrow> nat" where
  "ran_nat xs = map_snd (nub_nat xs)"

lemma sub_ran_nat : "ran_nat (list_encode (map prod_encode  xs)) = list_encode (ran_list xs) "
  apply (auto simp only: ran_nat_def ran_list_def submap_snd
      sub_nub sub_map map_map comp_def sub_snd)
  done

lemma sub_ran_list_helper : "distinct (map fst xs) \<Longrightarrow>
set (map snd xs) = ran (map_of xs)"
  apply (induct xs)
   apply (auto)
    apply (meson fun_upd_same ranI)
   apply (auto simp add: map_of_eq_None_iff)
  done

lemma sub_ran_list : "set (ran_list xs) = ran (map_of xs)"
  apply (simp only:ran_list_def sub_ran_list_helper[of "nub xs"] nub_correct[of xs] map_of_nub )
  done

lemma ran_list_pre:"I \<noteq> [] \<Longrightarrow> ran_list I \<noteq> []"
  apply (cases I)
   apply (auto simp add:ran_list_def )
  done
lemma del_inj: "inj f \<Longrightarrow>del (map (\<lambda>(a, y). (f a, y)) I) (f a) = map (\<lambda>(a, y). (f a, y)) ( del I a) "
  apply (induct I)
   apply (auto simp add:inj_def)
  done
lemma nub_inj : "inj f \<Longrightarrow> nub (map (\<lambda>(a, y). (f a, y)) I) = map (\<lambda>(a, y). (f a, y)) (nub I)"
  apply (induct I rule:nub.induct)
   apply (auto simp add:inj_def del_inj)
  done
lemma ran_inj: "inj f \<Longrightarrow>ran_list (map (\<lambda>(a, y). (f a, y)) I) = ran_list I"
  apply (induct I)
   apply (auto simp add:ran_list_def inj_def nub_inj del_inj)
  done

lemma sub_restrict_apply: "map_of (map (\<lambda>(x,y). (x, the y)) (filter (\<lambda>(x,y) . y \<noteq> None) (map (\<lambda>x. (x,f x)) xs))) k  = (f |` set xs) k"
  apply (induct xs)
   apply auto
    apply (metis restrict_in restrict_out)
   apply (simp add: restrict_map_def)
  apply(simp add: restrict_map_def)
  done

lemma sub_restrict: "map_of (map (\<lambda>(x,y). (x, the y)) (filter (\<lambda>(x,y) . y \<noteq> None) (map (\<lambda>x. (x,f x)) xs))) = (f |` set xs) "
  using sub_restrict_apply by fast


(*
fun filter_nat ::"(nat\<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat" where
"filter_nat f xs = (if xs = 0 then 0 else if f (hd_nat xs) then (hd_nat xs) ## (filter_nat f (tl_nat xs)) else (filter_nat f (tl_nat xs))) "

lemma sub_filter: "filter_nat f (list_encode xs) = list_encode (filter f xs)"
  apply (induct xs)
  apply (simp)
  apply (subst filter_nat.simps)
  apply (auto simp only: sub_hd head.simps sub_tl tail.simps sub_cons )
  apply auto
  done

lemma sub_restrict_map_nat: "map_nat (\<lambda>n. prod_encode(fst_nat n, the_nat (snd_nat n))) (filter_nat (\<lambda>n . snd_nat n \<noteq> 0) (map_nat (\<lambda>x. prod_encode(x,option_encode (f x))) (list_encode xs)))
  = list_encode (map prod_encode (map (\<lambda>(x,y). (x, the y)) (filter (\<lambda>(x,y) . y \<noteq> None) (map (\<lambda>x. (x,f x)) xs))))"
  apply (induct xs)
   apply simp
  apply (auto simp only: sub_map list.simps sub_fst sub_filter sub_the)
  apply (auto simp add: sub_snd list_encode_eq sub_fst simp del: list_encode.simps)
  using option_encode.elims by blast

fun bit_option_to_option ::"bit option \<Rightarrow> nat option" where
"bit_option_to_option None = None"|
"bit_option_to_option (Some x) = Some (bit_encode x)"

lemma bit_option_encode_simps: "bit_option_encode = option_encode o bit_option_to_option"
  apply (auto simp add:comp_def)
  by (metis bit_option_encode.elims bit_option_encode.simps(2) bit_option_to_option.elims option.simps(3)
 option_encode.elims some_nat_def sub_some)

lemma inj_var: "inj var_encode"
  apply (auto simp add:inj_def)
  by (metis var_id)

lemma inj_map_list_find : "inj f \<Longrightarrow> map_list_find (map (\<lambda>(x,y). (f x, g y)) s) (f x) =
map_list_find (map (\<lambda>(x,y). (x, g y)) s) x"
  apply (induct s)
   apply (auto simp add:inj_def)
  done

lemma map_list_find_map:"map_list_find s x = Some y  \<Longrightarrow> map_list_find (map (\<lambda>(x,y). (x , f y)) s) x = Some (f y)"
  apply (induct s arbitrary: x y)
   apply auto
  done
lemma map_list_find_map_none: "( map_list_find (map (\<lambda>(x,y). (x , f y)) s) x = None) = (map_list_find s x = None)"
  apply (induct s arbitrary: x )
   apply auto
  done

fun bool_encode :: "bool \<Rightarrow> nat" where
"bool_encode False = 0"|
"bool_encode True = 1"

fun bool_decode :: "nat \<Rightarrow> bool" where
"bool_decode 0 = False"|
"bool_decode (Suc x ) = True"

lemma bool_id : "bool_decode (bool_encode x) = x"
  by (cases x) auto

fun strips_assignment_encode :: "((var,dom) assignment,bool) assignment \<Rightarrow> nat" where
"strips_assignment_encode (s,b) = prod_encode (sas_plus_assignment_encode s , bool_encode b)"

fun strips_assignment_decode :: "nat \<Rightarrow> ((var,dom) assignment,bool) assignment" where
"strips_assignment_decode n = (case prod_decode n of (s,b) \<Rightarrow>
(sas_plus_assignment_decode s , bool_decode b))"

lemma strips_assignment_id : "strips_assignment_decode (strips_assignment_encode x) = x"
  apply (cases x)
  apply (auto simp add:var_id dom_id bool_id)
  done

definition strips_assignment_list_encode :: "((var,dom) assignment,bool) assignment list \<Rightarrow> nat" where
"strips_assignment_list_encode  x = list_encode (map strips_assignment_encode x)"

definition strips_assignment_list_decode :: "nat \<Rightarrow> ((var,dom) assignment,bool) assignment list" where
"strips_assignment_list_decode  x = map strips_assignment_decode (list_decode x)"

lemma strips_assignment_list_id: "strips_assignment_list_decode (strips_assignment_list_encode x) = x"
  apply (auto simp add: strips_assignment_list_encode_def strips_assignment_list_decode_def
 )
  apply (auto simp only:         comp_def strips_assignment_id)
  apply auto
  done

lemma sas_plus_simp: "sas_plus_assignment_encode = prod_encode o (\<lambda>(v,d). (var_encode v, dom_encode d))"
  by auto

lemma option_encode_0 : "(option_encode x = 0) = (x = None)"
  apply (cases x)
   apply auto
  done

lemma sas_plus_list_simp: "sas_plus_assignment_list_encode = list_encode o (map sas_plus_assignment_encode)"
  apply (auto simp add:comp_def sas_plus_assignment_list_encode_def)
  done

lemma fst_sas_simp : "fst_nat (sas_plus_assignment_encode x ) = var_encode (fst x)"
  apply (cases x)
  apply (auto simp add:sub_fst)
  done

lemma snd_sas_simp : "snd_nat (sas_plus_assignment_encode x ) = dom_encode (snd x)"
  apply (cases x)
  apply (auto simp add:sub_snd)
  done


lemma dom_inj : "inj dom_encode"
  apply (auto simp add:inj_def)
  by (metis dom_id)

lemma dom_inj_simp : "(dom_encode a = dom_encode b) = (a=b)"
  using dom_inj inj_def by metis

fun strips_operator_encode :: "(var,dom) assignment strips_operator \<Rightarrow> nat" where
"strips_operator_encode op = list_encode [sas_plus_assignment_list_encode (strips_operator.precondition_of op),
                                         sas_plus_assignment_list_encode (strips_operator.add_effects_of op),
                                         sas_plus_assignment_list_encode (strips_operator.delete_effects_of op)]"


fun strips_operator_decode :: "nat \<Rightarrow> (var,dom) assignment strips_operator " where
"strips_operator_decode n = (case list_decode n of [pre,add,delete] \<Rightarrow>
      \<lparr>strips_operator.precondition_of = sas_plus_assignment_list_decode pre,
        strips_operator.add_effects_of =  sas_plus_assignment_list_decode add,
        strips_operator.delete_effects_of =  sas_plus_assignment_list_decode delete \<rparr>)
"

lemma strips_operator_id: "strips_operator_decode (strips_operator_encode x) = x"
  apply (auto simp add: sas_plus_assignment_list_id)
  done

record  ('variable) strips_list_problem =
  variables_of :: "'variable list" ("(_\<^sub>\<V>)" [1000] 999)
  operators_of :: "'variable strips_operator list" ("(_\<^sub>\<O>)" [1000] 999)
  initial_of :: "('variable,bool) assignment list" ("(_\<^sub>I)" [1000] 999)
  goal_of :: "('variable,bool) assignment list" ("(_\<^sub>G)" [1000] 999)

fun strips_list_problem_to_problem ::
 "('variable) strips_list_problem \<Rightarrow> ('variable)strips_problem" where
"strips_list_problem_to_problem P =
\<lparr>
  strips_problem.variables_of = variables_of P,
  operators_of = operators_of P,
  initial_of = map_of (initial_of P),
  goal_of = map_of (goal_of P)
 \<rparr>"

definition strips_operator_list_encode :: " (var,dom) assignment strips_operator list \<Rightarrow> nat" where
" strips_operator_list_encode xs = list_encode (map  strips_operator_encode xs)"

definition strips_operator_list_decode :: " nat \<Rightarrow> (var,dom) assignment strips_operator list" where
" strips_operator_list_decode n = map  strips_operator_decode (list_decode n)"

lemma strips_operator_list_id:
"  strips_operator_list_decode ( strips_operator_list_encode x) = x"
  apply (auto simp only:  strips_operator_list_decode_def  strips_operator_list_encode_def
comp_def list_encode_inverse map_map strips_operator_id)
  apply auto
  done

fun strips_list_problem_encode :: "((var,dom) assignment) strips_list_problem \<Rightarrow> nat" where
"strips_list_problem_encode P = list_encode
[sas_plus_assignment_list_encode(variables_of P),
strips_operator_list_encode (operators_of P),
strips_assignment_list_encode (initial_of P),
strips_assignment_list_encode (goal_of P)
]"

fun strips_list_problem_decode :: "nat \<Rightarrow> ((var,dom) assignment) strips_list_problem" where
"strips_list_problem_decode n = (case list_decode n of
[vs,ops,I,gs] \<Rightarrow> \<lparr>
  variables_of  = sas_plus_assignment_list_decode vs,
  operators_of  = strips_operator_list_decode ops,
  initial_of =  strips_assignment_list_decode I,
  goal_of = strips_assignment_list_decode gs
 \<rparr> )"

lemma  strips_list_problem_id:
"strips_list_problem_decode (strips_list_problem_encode x) = x"
  apply (auto simp add:sas_plus_assignment_list_id strips_operator_list_id strips_assignment_list_id )
  done

fun sat_variable_encode :: "sat_plan_variable \<Rightarrow> nat" where
"sat_variable_encode (State x y) = list_encode [0,x,y]"|
"sat_variable_encode (Operator x y) = list_encode [1,x,y]"

fun sat_variable_decode :: "nat \<Rightarrow> sat_plan_variable" where
"sat_variable_decode n = (case list_decode n of [0,x,y] \<Rightarrow> State x y | [Suc 0, x ,y] \<Rightarrow> Operator x y)"

lemma sat_variable_id :
"sat_variable_decode(sat_variable_encode x) = x"
  apply (cases x)
   apply (auto)
  done

fun sat_formula_encode :: "sat_plan_formula \<Rightarrow> nat" where
"sat_formula_encode Bot = list_encode [0] "|
"sat_formula_encode (Atom v) = list_encode [1, sat_variable_encode v] "|
"sat_formula_encode (Not v) = list_encode[2, sat_formula_encode v]"|
"sat_formula_encode (And a b) = list_encode[3,sat_formula_encode a,sat_formula_encode b]"|
"sat_formula_encode (Or a b) = list_encode[4,sat_formula_encode a,sat_formula_encode b]"|
"sat_formula_encode (Imp a b) = list_encode[5,sat_formula_encode a,sat_formula_encode b]"

fun sat_formula_decode :: "nat \<Rightarrow> sat_plan_formula" where
"sat_formula_decode n =  (case list_decode n of
  [0] \<Rightarrow> Bot|
  [Suc 0,v] \<Rightarrow> Atom (sat_variable_decode v)|
  [Suc (Suc 0),v] \<Rightarrow> Not (sat_formula_decode v)|
  [Suc (Suc (Suc 0)),a,b] \<Rightarrow> And (sat_formula_decode a) (sat_formula_decode b)|
  [Suc (Suc (Suc (Suc 0))),a,b] \<Rightarrow> Or (sat_formula_decode a) (sat_formula_decode b)|
  [Suc (Suc (Suc (Suc (Suc 0)))),a,b] \<Rightarrow> Imp (sat_formula_decode a) (sat_formula_decode b)
) "

lemma sat_formula_id :
"sat_formula_decode (sat_formula_encode x) = x"
  apply (induct x)
  apply (auto simp add: sat_variable_id simp del: sat_variable_decode.simps)
  done

fun bool_option_encode :: "bool option \<Rightarrow> nat" where
"bool_option_encode None = 0"|
"bool_option_encode (Some b) = Suc (bool_encode b)"

fun bool_option_decode :: "nat \<Rightarrow> bool option" where
"bool_option_decode 0 = None"|
"bool_option_decode (Suc b) = Some (bool_decode b)"

lemma bool_option_id :
"bool_option_decode (bool_option_encode b) = b"
  apply (cases b)
   apply (auto simp add:bool_id)
  done

fun index_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"index_nat xs a = (if xs = 0 then 0 else if hd_nat xs = a then 0 else 1 + index_nat (tl_nat xs) a)"

lemma sub_index:
"inj f \<Longrightarrow> index_nat (list_encode (map f xs)) (f a) = index xs a"
  apply (induct xs)
   apply simp
  apply (subst index_nat.simps)
  apply (auto simp add: sub_hd list_encode_eq sub_tl inj_def
          simp del:index_nat.simps simp flip:list_encode.simps)
  done

definition sat_formula_list_encode :: "sat_plan_formula list \<Rightarrow>nat" where
"sat_formula_list_encode xs = list_encode (map sat_formula_encode xs)"

definition sat_formula_list_decode :: "nat \<Rightarrow> sat_plan_formula list" where
"sat_formula_list_decode n = map sat_formula_decode (list_decode n)"

lemma sat_formula_list_id:
"sat_formula_list_decode (sat_formula_list_encode x) = x"
  apply (auto simp add:sat_formula_list_decode_def sat_formula_list_encode_def)
  using sat_formula_id
  by (simp add: map_idI)

fun BigAnd_nat:: "nat \<Rightarrow> nat" where
"BigAnd_nat xs = (if xs=0 then 2##(0##0)##0 else 3##(hd_nat xs)##(BigAnd_nat (tl_nat xs))##0)"

fun BigAnd_acc:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"BigAnd_acc acc xs = (if xs=0 then acc
 else BigAnd_acc (3##(hd_nat xs)## acc ##0) (tl_nat xs))"



lemma sub_BigAnd:
"BigAnd_nat (sat_formula_list_encode xs) = sat_formula_encode (BigAnd xs)"
  apply (induct xs)
  apply (simp add:sat_formula_list_encode_def sub_cons cons0  flip:list_encode.simps)
  apply (subst BigAnd_nat.simps)
  apply (auto simp add:sat_formula_list_encode_def sub_hd sub_tl sub_cons cons0 list_encode_eq simp flip:list_encode.simps
simp del:BigAnd_nat.simps)
  done

lemma BigAnd_induct :
" BigAnd_nat (append_nat (reverse_nat xs) ys) = BigAnd_acc (BigAnd_nat ys) xs"
proof -
  obtain xs' ys' where "xs =list_encode xs' " "ys = list_encode ys'"

    by (metis list_decode_inverse)
  thus ?thesis apply (auto simp only: sub_reverse sub_BigAnd sub_append)
    apply(induct xs' arbitrary:ys' xs ys )
     apply (auto simp del:BigAnd_nat.simps BigAnd_acc.simps list_encode.simps)
     apply simp
    apply(subst(2) BigAnd_acc.simps)
    apply (auto simp add: list_encode_eq sub_hd
        simp del:BigAnd_nat.simps BigAnd_acc.simps simp flip:list_encode.simps)
    apply(subst BigAnd_nat.simps)
     apply (auto simp add: list_encode_eq sub_hd sub_tl
        simp del:BigAnd_nat.simps BigAnd_acc.simps simp flip:list_encode.simps)
    done
qed
definition BigAnd_tail :: "nat \<Rightarrow> nat" where
"BigAnd_tail xs = BigAnd_acc (2##(0##0)##0) (reverse_nat xs) "

lemma subtail_BigAnd :
" BigAnd_tail xs = BigAnd_nat xs "
  by (metis BigAnd_induct BigAnd_nat.elims BigAnd_tail_def append_nat_0 rev_rev_nat)

fun BigOr_nat:: "nat \<Rightarrow> nat" where
"BigOr_nat xs = (if xs=0 then (0##0) else 4##(hd_nat xs)##(BigOr_nat (tl_nat xs))##0)"

lemma sub_BigOr:
"BigOr_nat (sat_formula_list_encode xs) = sat_formula_encode (BigOr xs)"
  apply (induct xs)
  apply (simp add:sat_formula_list_encode_def sub_cons cons0  flip:list_encode.simps)
  apply (subst BigOr_nat.simps)
  apply (auto simp add:sat_formula_list_encode_def sub_hd sub_tl sub_cons cons0 list_encode_eq simp flip:list_encode.simps
simp del:BigOr_nat.simps)
  done

fun BigOr_acc:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"BigOr_acc acc xs = (if xs=0 then acc
 else BigOr_acc (4##(hd_nat xs)## acc ##0) (tl_nat xs))"




lemma BigOr_induct :
" BigOr_nat (append_nat (reverse_nat xs) ys) = BigOr_acc (BigOr_nat ys) xs"
proof -
  obtain xs' ys' where "xs =list_encode xs' " "ys = list_encode ys'"

    by (metis list_decode_inverse)
  thus ?thesis apply (auto simp only: sub_reverse sub_BigAnd sub_append)
    apply(induct xs' arbitrary:ys' xs ys )
     apply (auto simp del:BigOr_nat.simps BigOr_acc.simps list_encode.simps)
     apply simp
    apply(subst(2) BigOr_acc.simps)
    apply (auto simp add: list_encode_eq sub_hd
        simp del:BigOr_nat.simps BigOr_acc.simps simp flip:list_encode.simps)
     apply (auto simp add: list_encode_eq sub_hd sub_tl
        simp del:BigAnd_nat.simps BigAnd_acc.simps simp flip:list_encode.simps)
    done
qed

definition BigOr_tail :: "nat \<Rightarrow> nat" where
"BigOr_tail xs = BigOr_acc (0##0) (reverse_nat xs) "

lemma subtail_BigOr :
" BigOr_tail xs = BigOr_nat xs "
  by (metis BigOr_induct BigOr_nat.elims BigOr_tail_def append_nat_0 rev_rev_nat)

lemma strips_simp:"strips_assignment_encode = prod_encode o (\<lambda>(s,b). (sas_plus_assignment_encode s, bool_encode b))"
  apply (auto)
  done

fun map_pair :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"map_pair x xs = (if xs = 0 then 0 else (prod_encode (x,hd_nat xs)) ## map_pair x (tl_nat xs))"

fun map_pair_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"map_pair_acc acc x xs = (if xs = 0 then acc else map_pair_acc ((prod_encode (x,hd_nat xs)) ## acc) x (tl_nat xs))"

lemma submap_pair:
"map_pair (f x) (list_encode (map g xs)) = list_encode ( map (\<lambda>(x,y). prod_encode (f x, g y)) (map (Pair x) xs)) "
  apply (induct xs)
   apply simp
  apply (subst map_pair.simps)
  apply (auto simp add: sub_cons cons0 sub_hd sub_tl
list_encode_eq simp del: map_pair.simps
simp flip: list_encode.simps
)
  done

lemma submap_pair_gen:
"map_pair x (list_encode xs) = list_encode  (map (prod_encode o Pair x) xs) "
  using submap_pair[of id x id xs] apply auto
  done

lemma submap_pair_mappair:
"map_pair x xs = map_nat (prod_encode o Pair x) xs"
using submap_pair_gen sub_map
  by (metis list_decode_inverse)



fun product_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"product_nat xs ys = (if xs = 0 then 0 else append_nat (map_pair (hd_nat xs) ys) (product_nat (tl_nat xs) ys))"


lemma sub_product:
"product_nat (list_encode (map f xs)) (list_encode (map g ys))
= list_encode (map (\<lambda>(x,y). prod_encode (f x, g y)) (List.product xs ys))"
  apply (induct xs)
   apply simp
  apply (subst product_nat.simps)
  apply (auto simp only: submap_pair list.simps sub_tl tail.simps sub_append map_map comp_def
sub_hd head.simps)
  apply (auto simp add: list_encode_eq)
  done

lemma sub_product_id:
"product_nat (list_encode xs) (list_encode ys)
= list_encode (map prod_encode (List.product xs ys))"
  using sub_product[of id xs id ys] by simp

lemma sub_elem_of_inj: "inj f \<Longrightarrow> (elemof (f e) (list_encode (map f l)) \<noteq> 0) = (e \<in> set l)"
  apply (induct l)
   apply simp
  apply (subst elemof.simps)
  apply (auto simp add: inj_def
      list_encode_eq sub_hd sub_tl simp del:elemof.simps simp flip: list_encode.simps)
  done

fun map_acc :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"map_acc f acc n = (if n = 0 then acc else map_acc f ((f (hd_nat n)) ## acc) (tl_nat n))"

lemma rev_cons: "a # rev xs = rev (xs @[a])"
  apply auto
  done
lemma append_singleton:
"map f xs @ [f a] = map f (xs@[a])"
  apply(auto)
  done
lemma map_induct :
"reverse_nat (map_nat f (append_nat xs ys))
= map_acc f (reverse_nat ( map_nat f xs)) ys"
proof -
  obtain xs' ys' where "xs = list_encode xs'" "ys = list_encode ys'"
    by (metis list_decode_inverse)
  thus ?thesis
    apply(auto simp only: sub_append sub_map sub_reverse)
    apply(induct ys' arbitrary:xs' xs ys)
     apply simp
    apply(subst map_acc.simps)
    apply(auto simp add: sub_tl sub_hd sub_cons
            simp del:map_acc.simps list_encode.simps)
     apply simp
    subgoal for a ys' xs'
      apply(auto simp only: rev_cons append_singleton)
      done
    done
qed


lemma subtail_map:
"reverse_nat (map_acc f  0 xs) = map_nat f xs"
  using map_induct[of f 0 xs]
  by (metis append_nat.simps(1) map_nat.simps rev_rev_nat reverse_nat_0)

fun filter_acc :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"filter_acc f acc xs = (if xs = 0 then acc else if f (hd_nat xs) then filter_acc f ((hd_nat xs) ## acc) (tl_nat xs)
else filter_acc  f  acc (tl_nat xs))"

lemma filter_append:
"f a \<Longrightarrow> filter f xs @ [a] = filter f (xs @ [a]) "
  apply auto
  done

lemma filter_induct:
"reverse_nat (filter_nat f (append_nat xs ys))
= filter_acc f (reverse_nat ( filter_nat f xs)) ys"
proof -
  obtain xs' ys' where "xs = list_encode xs'" "ys = list_encode ys'"
    by (metis list_decode_inverse)
  thus ?thesis
    apply(auto simp only: sub_append sub_filter sub_reverse)
    apply(induct ys' arbitrary:xs' xs ys)
     apply simp
    apply(subst filter_acc.simps)
    apply(auto simp add: sub_tl sub_hd sub_cons  non_empty_not_zero
            simp del:filter_acc.simps list_encode.simps)
    subgoal for a ys' xs'
      apply(auto simp only: rev_cons filter_append append_singleton)
      done
    done
qed

lemma subtail_filter:
"reverse_nat (filter_acc f  0 xs) = filter_nat f xs"
  using filter_induct[of f 0 xs]
  by (metis append_nat.simps(1) filter_nat.simps rev_rev_nat reverse_nat_0)

lemma map_pair_induct :
"map_pair_acc acc x xs = map_acc (prod_encode o Pair x) acc xs"
  apply(induct acc x xs rule:map_pair_acc.induct)
  apply auto
  done

definition map_pair_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"map_pair_tail x xs = reverse_nat (map_pair_acc 0 x xs)"

lemma subtail_map_pair:
"map_pair_tail x xs = map_pair x xs"
  using map_pair_tail_def map_pair_induct submap_pair_mappair subtail_map by presburger

fun product_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"product_acc acc xs ys = (if xs = 0 then acc else
product_acc (append_tail ( reverse_nat (map_pair_tail (hd_nat xs) ys)) acc ) (tl_nat xs) ys)"


lemma product_induct:
"product_acc acc xs ys = append_nat (reverse_nat (product_nat xs ys))  acc "
proof -
  obtain acc' xs' ys'  where "acc = list_encode acc'" "xs = list_encode xs'" "ys =list_encode ys'"
    by (metis list_decode_inverse)
  thus ?thesis using sub_product_id  apply(auto simp only: list.map_id  id_apply
        sub_reverse sub_append  )
    apply(induct xs' arbitrary: acc' acc xs)
     apply simp
    apply (subst product_acc.simps)
    apply (auto simp add: non_empty_not_zero subtail_append sub_reverse sub_hd subtail_map_pair
      submap_pair_mappair sub_map sub_append sub_tl
 simp flip: map_append
          simp del: product_acc.simps product_nat.simps list_encode.simps map_pair.simps map_nat.simps)
    apply force
    done

qed

definition product_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"product_tail xs ys = reverse_nat (product_acc 0 xs ys)"

lemma subtail_product:
"product_tail xs ys = product_nat xs ys "
  using append_nat_0 product_induct product_tail_def rev_rev_nat by presburger

fun map_snd_acc  :: "nat \<Rightarrow> nat \<Rightarrow> nat " where
"map_snd_acc acc xs = (if xs = 0 then acc else map_snd_acc ((snd_nat (hd_nat xs)) ##acc) (tl_nat xs))"

lemma map_snd_induct:
"map_snd_acc acc xs = map_acc snd_nat acc xs"
  apply(induct acc xs rule:map_snd_acc.induct)
  apply auto
  done

definition map_snd_tail :: "nat \<Rightarrow> nat" where
"map_snd_tail xs = reverse_nat (map_snd_acc 0 xs)"

lemma subtail_map_snd:
"map_snd_tail xs = map_snd xs"
  using map_snd_induct map_snd_tail_def submap_snd subtail_map by presburger

lemma del_filter_nat:
"del_nat xs a = filter_nat (\<lambda>x. fst_nat x \<noteq> a) xs"
proof -
  obtain xs' where "xs =list_encode (map prod_encode xs')"
    by (metis list_decode_inverse map_idI map_map o_def prod_decode_inverse)
  thus ?thesis apply (auto simp only: sub_filter filter_map comp_def sub_fst sub_del del_filter)
    done
qed

fun del_acc :: "nat \<Rightarrow>nat \<Rightarrow> nat \<Rightarrow> nat" where
"del_acc acc xs a = (if xs =0 then acc else if fst_nat (hd_nat xs) = a then del_acc acc (tl_nat xs) a else del_acc
  ((hd_nat xs)##acc)  (tl_nat xs) a )"

lemma del_induct :
"del_acc acc xs a = filter_acc (\<lambda>x. fst_nat x \<noteq> a) acc  xs "
  apply(induct acc xs a rule:del_acc.induct)
  apply auto
  done

definition del_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"del_tail xs a = reverse_nat (del_acc 0 xs a) "

lemma subtail_del:
"del_tail xs a = del_nat xs a"
  using del_tail_def del_induct del_filter_nat subtail_filter by presburger

function nub_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"nub_acc acc xs = (if xs = 0 then acc else nub_acc ((hd_nat xs) ## acc)
      (del_tail xs (fst_nat (hd_nat xs))))"
 by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(acc,xs). length_nat xs)")
   apply simp
  apply (auto simp del: del_nat.simps)
  subgoal for xs
  proof -
    assume asm:"0 < xs"
    obtain ys where ys_def: "ys = map prod_decode (list_decode xs)" by simp
    then have t:"xs = list_encode (map prod_encode ys)"
      by (auto simp add: comp_def)
    moreover have "ys \<noteq> []" using ys_def asm t by force
    ultimately show  ?thesis  apply (auto simp only: t sub_del sub_length  length_map  sub_hd)
      apply (auto simp add: sub_head_map sub_fst)
      apply (cases ys)
       apply (auto simp only: subtail_del sub_del sub_length )
      by (auto simp add: del_shorter less_Suc_eq_le)
  qed
  done

lemma nub_induct:
"nub_acc acc xs = append_nat (reverse_nat (nub_nat xs)) acc "
proof -
  obtain xs' acc' where "xs =list_encode (map prod_encode xs')" "acc =list_encode acc'"
    by (metis list_decode_inverse map_idI map_map o_def prod_decode_inverse)
  thus ?thesis apply(auto simp only: sub_nub  sub_reverse sub_append )
    apply(induct  xs' arbitrary: xs acc' acc rule: nub.induct)
     apply simp
    apply(subst nub_acc.simps)
    apply (auto simp only:subtail_del sub_del sub_hd head.simps list.simps sub_fst fst_conv sub_cons )
    apply(auto simp only: sub_del  simp flip: list.map )
    by (metis (no_types, lifting) append.assoc append.left_neutral
 del.simps(2) list.simps(3) list.simps(9) list_encode.simps(1) list_encode_eq
nub.simps(2) rev_append rev_cons rev_rev_ident)
qed

definition nub_tail :: "nat \<Rightarrow> nat" where
"nub_tail xs = reverse_nat (nub_acc 0 xs)"

lemma subtail_nub:
"nub_tail xs = nub_nat xs"
  using append_nat_0 nub_induct nub_tail_def rev_rev_nat by presburger

definition ran_tail :: "nat \<Rightarrow> nat" where
"ran_tail xs = map_snd_tail (nub_tail xs)"

lemma subtail_ran:
"ran_tail xs = ran_nat xs"
  using ran_nat_def ran_tail_def subtail_map_snd subtail_nub by presburger

fun length_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"length_acc acc xs = (if xs = 0 then acc else length_acc (acc+1) (tl_nat xs))"

lemma length_induct:
"length_acc acc xs = length_nat xs + acc"
proof -
  obtain xs' where "xs = list_encode xs'"
    by (metis list_decode_inverse)
  thus ?thesis apply (auto simp only: sub_length)
    apply(induct xs' arbitrary:xs acc)
     apply simp
    apply(subst length_acc.simps)
    apply( auto simp add: non_empty_positive sub_tl simp del:length_acc.simps list_encode.simps(2))
    done
qed
definition length_tail :: "nat \<Rightarrow> nat" where
"length_tail xs = length_acc 0 xs"

lemma subtail_length :
"length_tail xs = length_nat xs"
  using Primitives.length_induct length_tail_def by auto

*)
end