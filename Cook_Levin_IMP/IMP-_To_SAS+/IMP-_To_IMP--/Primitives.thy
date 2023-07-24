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

function_nat_rewrite fst_helper
function_nat_rewrite_correctness fst_helper
  apply(induction arg\<^sub>1 rule: fst_helper.induct)
  apply(all \<open>subst fst_helper_nat.simps\<close>)
  subgoal for a b
    apply(subst enc_prod.simps)
    by(simp add: assms pointfree_idE enc_prod.simps)
  done

function_nat_rewrite snd_helper
function_nat_rewrite_correctness snd_helper
  by(natfn_correctness \<open>induct arg\<^sub>1 rule: snd_helper.induct\<close>
      assms: assms
      simps_nat: snd_helper_nat.simps
      enc_simps: enc_prod.simps
      args_wellbehaved: assms(1)[THEN pointfree_idE])

definition "fst_nat \<equiv> fst_helper_nat"
definition "snd_nat \<equiv> snd_helper_nat"

lemma fst_nat_equiv:
  fixes enc_'a :: "('a::order_bot) \<Rightarrow> nat"
    and enc_'b :: "('b::order_bot) \<Rightarrow> nat"
  assumes "dec_'a \<circ> enc_'a = id"
    and "dec_'b \<circ> enc_'b = id"
    and "dec_'a bot = bot"
    and "dec_'b bot = bot"
  shows
    "dec_'a (fst_nat (enc_prod enc_'a enc_'b p)) = fst p"
  using fst_helper_nat_equiv assms
  by (subst fst_nat_def, subst fst_helper_eq[symmetric]) blast

lemma snd_nat_equiv:
  fixes enc_'a :: "('a::order_bot) \<Rightarrow> nat"
    and enc_'b :: "('b::order_bot) \<Rightarrow> nat"
  assumes "dec_'a \<circ> enc_'a = id"
    and "dec_'b \<circ> enc_'b = id"
    and "dec_'a bot = bot"
    and "dec_'b bot = bot"
  shows
    "dec_'b (snd_nat (enc_prod enc_'a enc_'b p)) = snd p"
  using snd_helper_nat_equiv assms
  by (subst snd_nat_def, subst snd_helper_eq[symmetric]) blast

lemma eq: "prod_encode (n,m) = (m+n) * (m+n+1) div 2 + n"
  by (simp add: add.commute prod_encode_def triangle_def)



fun head :: "('a::order_bot) list \<Rightarrow> 'a" where
  "head [] = bot"
| "head (x # xs) = x"

function_nat_rewrite head
function_nat_rewrite_correctness head
  by (natfn_correctness \<open>induct arg\<^sub>1 rule: head.induct\<close>
      assms: assms assms(1)[THEN pointfree_idE]
      simps_nat: head_nat.simps
      enc_simps: enc_list.simps pointfree_idE
      args_wellbehaved: encoding_list_wellbehaved[OF assms(1), THEN pointfree_idE])

fun tail :: "'a list \<Rightarrow> 'a list" where
  "tail (x # xs) = xs"
| "tail [] = []"

function_nat_rewrite tail
function_nat_rewrite_correctness tail
  by(natfn_correctness \<open>induct arg\<^sub>1 rule: tail.induct\<close>
      assms: assms
      simps_nat: tail_nat.simps
      enc_simps: enc_list.simps
      args_wellbehaved: encoding_list_wellbehaved[OF assms(1), THEN pointfree_idE])

thm encoding_list_wellbehaved[of inj_on_imageI]
thm inj_on_imageI[of ] encoding_list_wellbehaved inj_on_inverseI
thm inj_on_inverseI[of _ "dec_list dec_'a" "enc_list enc_'a"] encoding_list_wellbehaved

lemma inj_inverseI: "g \<circ> f = id \<Longrightarrow> inj f"
  by (metis inj_on_inverseI pointfree_idE)

thm inj_inverseI[OF encoding_list_wellbehaved]

lemma enc_list_nil: "xs = [] \<longleftrightarrow> enc_list enc_'a xs = 0"
  by(simp add: enc_list.simps prod_encode_def split: list.split)

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

function_nat_rewrite length_acc
thm length_acc_nat.simps
function_nat_rewrite_correctness length_acc
  by (natfn_correctness \<open>induct arg\<^sub>1 arg\<^sub>2 rule: length_acc.induct\<close>
      assms: assms(1)[THEN pointfree_idE] assms(2)
      simps_nat: length_acc_nat.simps
      enc_simps: enc_list.simps
      args_wellbehaved: encoding_list_wellbehaved[OF assms(1), THEN pointfree_idE]
      encoding_nat_wellbehaved[THEN pointfree_idE])

fun length :: "'a list \<Rightarrow> nat" where
  "length xs = length_acc 0 xs"

lemma length_eq_length: "List.length xs = length xs"
  by(induction xs; simp add: suc_length_acc)

function_nat_rewrite length
function_nat_rewrite_correctness length
  using length_acc_nat_equiv[OF assms]
  by(simp add: length_nat.simps prod_encode_0)

lemma non_empty_positive : "enc_list enc_'a (x#xs) > 0"
  by(simp add: enc_list.simps prod_encode_def)


fun takeWhile_nat :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat" where
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
      list_decode_inverse nat_less_le non_empty_positive sub_hd sub_tl tail.simps(2))


datatype_nat_encode option
declare enc_option.simps[simp del]

datatype_nat_decode option
termination by (decode_termination "measure snd")
declare dec_option.simps[simp del]
declare dec_option.simps[of _ "prod_encode _", simp]


datatype_nat_wellbehaved option
  apply(intro ext)
  subgoal for x
    using assms[THEN pointfree_idE]
    by(induction x rule: option.induct; simp add: enc_option.simps)
  done


definition vname_encode :: "string \<Rightarrow> nat" where
  "vname_encode n = enc_list enc_char n"

definition vname_decode :: "nat \<Rightarrow> string" where
  "vname_decode n = dec_list dec_char n"

lemma vname_id: "vname_decode (vname_encode xs) = xs"
  using encoding_list_wellbehaved[THEN pointfree_idE] encoding_char_wellbehaved
  by (simp add: vname_encode_def vname_decode_def)

lemma vname_inj: "inj vname_encode"
  unfolding vname_encode_def
  using inj_inverseI[OF encoding_list_wellbehaved, OF encoding_char_wellbehaved] .

definition vname_list_encode :: "string list \<Rightarrow> nat" where
  "vname_list_encode l = list_encode (map vname_encode l)"

definition vname_list_encode2 :: "string list \<Rightarrow> nat" where
  "vname_list_encode2 l = enc_list (enc_list enc_char) l"

definition vname_list_decode :: "nat \<Rightarrow> string list" where
  "vname_list_decode n = map vname_decode (list_decode n)"

definition vname_list_decode2 :: "nat \<Rightarrow> string list" where
  "vname_list_decode2 n = dec_list (dec_list dec_char) n"

lemma vname_list_id2: "vname_list_decode2 (vname_list_encode2 x) = x"
  unfolding vname_list_encode2_def vname_list_decode2_def
  using encoding_list_wellbehaved[
      OF encoding_list_wellbehaved,
      OF encoding_char_wellbehaved,
      THEN pointfree_idE] .

lemma vname_list_id: "vname_list_decode (vname_list_encode x) = x"
  by (simp add: vname_list_encode_def vname_list_decode_def map_idI vname_id)

lemma "loop_nat bot bot = bot"
  by(simp add: loop_nat.simps prod_decode_def prod_decode_aux.simps)

(* TODO: rename *)
lemma sub_reverse:
  assumes "dec_'a \<circ> enc_'a = id"
  shows "reverse_nat (enc_list enc_'a xs) = enc_list enc_'a (reverse xs)"
  using reverse_nat_equiv assms reverse_nat_equiv2 by blast

lemma reverse_nat_0:"(reverse_nat 0 = 0)"
  by(simp add: reverse_nat.simps loop_nat.simps prod_decode_def prod_decode_aux.simps
      prod_encode_0)

lemma reverse_append_nat:
  "reverse_nat (append_nat xs ys) = append_nat (reverse_nat ys) (reverse_nat xs)"
  oops

fun elemof :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "elemof _ [] = False"
| "elemof y (x#xs) = (if (y = x) then True else elemof y xs)"

lemma elemof_set_in: "elemof x xs = (x \<in> set xs)"
  by(induction x xs rule: elemof.induct; simp)

fun foo where
  "foo x = True"

function_nat_rewrite foo

function_nat_rewrite_correctness foo
  by(simp add: foo_nat.simps)

fun bar where
  "bar x = (if foo x then False else True)"

ML \<open>
@{term "if foo x then True else False"};
@{term "enc_bool"};

fun change_if ((c as Const ("HOL.If", _)) $ cond $ thn $ els) =
  c $ (@{term "enc_bool"} $ cond) $ thn $ els
  | change_if x = x

\<close>

function_nat_rewrite bar
function_nat_rewrite_correctness bar
  using  foo_nat_equiv[OF assms] by(simp add: bar_nat.simps)

function_nat_rewrite elemof

lemma elemof_nat_equiv2:
  assumes "dec_'a \<circ> enc_'a = id"
  shows "elemof_nat (enc_'a arg\<^sub>1) (enc_list enc_'a arg\<^sub>2) = enc_bool (elemof arg\<^sub>1 arg\<^sub>2)"
  apply (induction arg\<^sub>1 arg\<^sub>2 rule: elemof.induct)
   apply(all \<open>subst elemof.simps\<close>)
  subgoal for u
    by(simp add: enc_list.simps elemof_nat.simps enc_bool.simps)
  subgoal for y x xs
    apply(simp add: enc_list.simps)
    using encoding_list_wellbehaved[OF assms(1), THEN pointfree_idE]
      assms(1)[THEN pointfree_idE]
    apply(simp add: elemof_nat.simps Let_def enc_bool.simps)
    by metis
  done

function_nat_rewrite_correctness elemof
  using elemof_nat_equiv2[OF assms(1)] encoding_bool_wellbehaved[THEN pointfree_idE]
  by fastforce

lemma sub_elemof: "elemof x xs = (x \<in> set xs)"
  by(induction xs; simp)

lemma sub_elemof_nat:
  assumes "dec_'a \<circ> enc_'a = id"
  shows "elemof_nat (enc_'a e) (enc_list enc_'a l) \<noteq> 0 = (e \<in> set l)"
  using elemof_nat_equiv2[OF assms]
  by(simp add: enc_bool.simps sub_elemof prod_encode_def split: bool.split)

lemma sub_elemof_nat2:
  assumes "dec_'a \<circ> enc_'a = id"
  shows "elemof_nat (enc_'a e) (enc_list enc_'a l) = 0 = (e \<notin> set l)"
  using elemof_nat_equiv2[OF assms]
  by(simp add: enc_bool.simps sub_elemof prod_encode_def split: bool.split)

fun remdups_acc :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remdups_acc acc [] = acc" |
  "remdups_acc acc (x # xs) =
  (if elemof x xs then remdups_acc acc xs
   else remdups_acc (append acc [x]) xs)"

function_nat_rewrite remdups_acc
function_nat_rewrite_correctness remdups_acc
  apply (natfn_correctness \<open>induct arg\<^sub>1 arg\<^sub>2 rule: remdups_acc.induct\<close>
      assms: assms assms(1)[THEN pointfree_idE]
      simps_nat: remdups_acc_nat.simps
      enc_simps: enc_list.simps
      args_wellbehaved: encoding_list_wellbehaved[OF assms(1), THEN pointfree_idE]
      elemof_nat_equiv[OF assms] append_nat_equiv2[OF assms(1)] )
  unfolding atomic.simps pair.simps  One_nat_def using 11 list.simps(5)
  by smt


lemma append_assoc: "append (append xs ys) zs = append xs (append ys zs)"
  unfolding 8 by simp

lemma remdups_acc_append: "remdups_acc acc xs = append acc (remdups_acc [] xs)"
  apply(induction xs arbitrary: acc)
   apply (simp add: 7)
  by (metis "8" append_assoc remdups_acc.simps(2) self_append_conv2)

lemma "remdups xs = remdups_acc [] xs"
  apply(induction xs; simp add: elemof_set_in)
  by (metis (full_types) "8" append_Cons remdups_acc_append)

fun remdups :: "'a list \<Rightarrow> 'a list" where
  "remdups xs = remdups_acc [] xs"

function_nat_rewrite remdups
function_nat_rewrite_correctness remdups
  unfolding remdups.simps
  using remdups_acc_nat_equiv[OF assms, of "[]" arg\<^sub>1]
  by(simp add: remdups_nat.simps enc_list.simps)


lemma sub_remdups: "remdups_nat (enc_list enc_'a xs) = enc_list enc_'a (remdups xs)"
  apply (subst remdups_nat.simps)
  apply (induct xs)
   apply (auto simp only:  tail.simps head.simps sub_tail sub_head remdups.simps sub_elemof
      )
   apply (auto)[1]
  using "11" remdups_acc_nat.simps apply force
  apply(auto simp add: remdups_acc.simps remdups_acc_nat.simps)
  oops


lemma non_empty_not_zero: "enc_list enc_'a (a # xs) \<noteq> 0"
  using non_empty_positive by simp

lemma remdups_induct :
  "reverse_nat (append_nat (reverse_nat acc) (remdups_nat xs)) = remdups_acc acc xs "
proof -
  obtain xs' acc' where "xs =list_encode xs'" "acc = list_encode acc'"
    by (metis list_decode_inverse)
  thus ?thesis apply(auto simp only: sub_reverse sub_remdups sub_append rev_append rev_rev_ident)
    apply(induct xs' arbitrary: acc' xs acc)
    apply simp
    apply(subst remdups_acc.simps)
    apply(auto simp add: sub_cons sub_hd sub_tl sub_elem_of2 sub_elem_of non_empty_positive non_empty_not_zero
        simp del: list_encode.simps remdups_acc.simps append_nat.simps elemof.simps)
    oops
  qed



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
declare enc_atomExp.simps [simp del]

lemma enc_atomExp_bot: "enc_atomExp bot = bot"
  by(simp add: enc_atomExp.simps prod_encode_0 bot_atomExp_def bot_nat_def)

datatype_nat_decode atomExp
termination by (decode_termination "measure id")
declare dec_atomExp.simps[simp del]
lemmas dec_atomExp_prod_encode_simp[simp] = dec_atomExp.simps[of  "prod_encode _"]

datatype_nat_wellbehaved atomExp
  using encoding_list_wellbehaved[OF encoding_char_wellbehaved, THEN pointfree_idE]
  by (intro ext, simp add: enc_atomExp.simps split: atomExp.split)



datatype_nat_encode aexp
declare enc_aexp.simps [simp del]

lemma enc_aexp_bot: "enc_aexp bot = bot"
  by(simp add: enc_atomExp.simps enc_aexp.simps prod_encode_0 bot_atomExp_def bot_aexp_def
      bot_nat_def)

datatype_nat_decode aexp
termination by (decode_termination "measure id")
declare dec_aexp.simps[simp del]
lemmas dec_aexp_prod_encode_simp[simp] = dec_aexp.simps[of  "prod_encode _"]

datatype_nat_wellbehaved aexp
  using encoding_atomExp_wellbehaved[THEN pointfree_idE]
  by (intro ext, simp add: enc_aexp.simps split: aexp.split)


datatype_nat_encode bit
declare enc_bit.simps [simp del]

lemma enc_bit_bot: "enc_bit bot = bot"
  by(simp add: enc_bit.simps prod_encode_0 bot_bit_def bot_nat_def)

datatype_nat_decode bit
termination by (decode_termination "measure id")
declare dec_bit.simps[simp del]
lemmas dec_bit_prod_encode_simp[simp] = dec_bit.simps[of  "prod_encode _"]

datatype_nat_wellbehaved bit
  using encoding_atomExp_wellbehaved[THEN pointfree_idE]
  by (intro ext, simp add: enc_bit.simps split: bit.split)

datatype_nat_encode com
declare enc_com.simps [simp del]

lemma enc_com_bot: "enc_com bot = bot"
  by(simp add: enc_com.simps prod_encode_0 bot_com_def bot_nat_def)

datatype_nat_decode com
termination by (decode_termination "measure id")
declare dec_com.simps[simp del]
lemmas dec_com_prod_encode_simp[simp] = dec_com.simps[of  "prod_encode _"]

datatype_nat_wellbehaved com
  apply (intro ext)
  subgoal for x
    using encoding_list_wellbehaved[OF encoding_char_wellbehaved, THEN pointfree_idE] vname_list_id2
      encoding_bit_wellbehaved[THEN pointfree_idE]
    by (induction x rule: com.induct; simp add: vname_list_decode2_def vname_list_encode2_def
        enc_com.simps)
  done

fun nth :: "nat \<Rightarrow> ('a::order_bot) list \<Rightarrow> 'a" where
  "nth _ [] = bot"
| "nth 0 (x # _) = x"
| "nth (Suc n) (_ # xs) = nth n xs"

function_nat_rewrite nth
function_nat_rewrite_correctness nth
  by (natfn_correctness \<open>induct arg\<^sub>1 arg\<^sub>2 rule: nth.induct\<close>
      assms: assms(2) assms(1)[THEN pointfree_idE]
      simps_nat: nth_nat.simps
      enc_simps: enc_list.simps
      args_wellbehaved: encoding_list_wellbehaved[OF assms(1), THEN pointfree_idE])



lemma pos_hd_less[termination_simp]: "x > 0 \<Longrightarrow> head_nat x < x"
  by(simp add: head_nat.simps bot_nat_def fst_prod_decode_less snd_prod_decode_lt_intro)


lemma pos_tl_less[termination_simp]: "x > 0 \<Longrightarrow> tail_nat x < x"
  by(simp add: tail_nat.simps prod_encode_0 snd_prod_decode_less snd_prod_decode_lt_intro)

lemma nth_less[simp]: "nth_nat n x \<le> x"
  apply(induct n arbitrary:x)
   apply(auto simp add: nth_nat.simps head_nat.simps tail_nat.simps snd_nat_def
      fst_prod_decode_lte snd_prod_decode_lte)
  oops

lemma [simp]: "x > 0 \<Longrightarrow> nth_nat n x < x"
  apply (induct n arbitrary:x)
  oops

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

datatype_nat_encode num
declare enc_num.simps[simp del]

datatype_nat_decode num
termination by (decode_termination "measure id")
declare dec_num.simps[simp del]
declare dec_num.simps[of "prod_encode _", simp]


datatype_nat_wellbehaved num
  apply(intro ext)
  subgoal for x
    by(induction x rule: num.induct; simp add: enc_num.simps)
  done

lemma Suc_plus: "Suc (m + n) = Suc m + n"
  by simp


lemma remdups_map : "inj f \<Longrightarrow> remdups (map f xs) = map f (remdups xs)"
  apply (induction xs)
   apply simp
  apply (simp add: inj_def elemof_set_in)
  by (metis "8" append_Cons image_iff list.simps(9) remdups_acc_append)



lemma vname_list_encode_as_comp:"vname_list_encode = list_encode o (map vname_encode)"
  by (auto simp add:fun_eq_iff vname_list_encode_def)


datatype_nat_encode domain_element
declare enc_domain_element.simps[simp del]

datatype_nat_decode domain_element
termination by (decode_termination "measure id")
declare dec_domain_element.simps[simp del]
declare dec_domain_element.simps[of "prod_encode _", simp]

datatype_nat_wellbehaved domain_element
  apply(intro ext)
  subgoal for x
    using encoding_bit_wellbehaved[THEN pointfree_idE] encoding_com_wellbehaved[THEN pointfree_idE]
    by(induction x rule: domain_element.induct; simp add: enc_domain_element.simps)
  done

datatype_nat_encode variable
declare enc_variable.simps[simp del]

datatype_nat_decode variable
termination by (decode_termination "measure id")
declare dec_variable.simps[simp del]
declare dec_variable.simps[of "prod_encode _", simp]

datatype_nat_wellbehaved variable
  apply(intro ext)
  subgoal for x
    using encoding_list_wellbehaved[OF encoding_char_wellbehaved, THEN pointfree_idE]
    by(induction x rule: variable.induct; simp add: enc_variable.simps)
  done


definition sas_assignment_encode:: "variable * domain_element \<Rightarrow> nat" where
  "sas_assignment_encode = enc_prod enc_variable enc_domain_element"

definition sas_assignment_decode:: "nat \<Rightarrow> (variable * domain_element)" where
  "sas_assignment_decode = dec_prod dec_variable dec_domain_element"

lemmas encoding_sas_assignment_wellbehaved =
  encoding_prod_wellbehaved[OF encoding_variable_wellbehaved, OF encoding_domain_element_wellbehaved]

fun someOf :: "'a option \<Rightarrow> 'a" where
  "someOf (Some x) = x"

definition map_to_list :: "('a,'b) map \<Rightarrow> ('a*'b) list" where
  "map_to_list s \<equiv> (SOME l. map_of l = s)"

lemma has_map:
  fixes s
  assumes "finite (dom s)"
  shows "\<exists>l. map_of l = s "
proof -
  obtain n where n_def:"n = card (dom s)" by blast
  then show  "\<exists>l. map_of l = s " using assms
  proof (induct n arbitrary:s)
    case 0
    then have "dom s ={}" using card_eq_0_iff by simp
    then show ?case  by simp
  next
    case (Suc n)
    hence "dom s  \<noteq> {}" using card_gt_0_iff
      by force
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

definition sas_state_encode ::"sas_state \<Rightarrow> nat" where
  "sas_state_encode xs = list_encode (map sas_assignment_encode (map_to_list xs)) "

definition sas_state_decode :: "nat \<Rightarrow> sas_state" where
  "sas_state_decode n = map_of (map sas_assignment_decode (list_decode n)) "


lemma sas_state_id : "finite (dom x) \<Longrightarrow> sas_state_decode (sas_state_encode x) = x"
  apply (auto simp only: sas_state_encode_def sas_state_decode_def map_to_list_id comp_def
      list_encode_inverse map_map sas_assignment_id)
  apply (auto simp add: map_to_list_id)
  done




fun imp_assignment_encode:: "vname * bit \<Rightarrow> nat" where
"imp_assignment_encode (v,d) = prod_encode (vname_encode v, bit_encode d)"

fun imp_assignment_decode:: "nat \<Rightarrow> (vname * bit)" where
"imp_assignment_decode n = (case prod_decode n of (v,d) \<Rightarrow> (vname_decode v, bit_decode d))"

lemma  imp_assignment_id: "imp_assignment_decode (imp_assignment_encode x) = x"
  apply (cases x)
  apply (auto simp only:vname_id bit_id imp_assignment_decode.simps imp_assignment_encode.simps
        prod_encode_inverse)
  done

definition imp_state_encode :: "imp_state \<Rightarrow> nat" where
"imp_state_encode xs = list_encode (map imp_assignment_encode (map_to_list xs)) "

definition imp_state_decode :: "nat \<Rightarrow> imp_state" where
"imp_state_decode n = map_of (map imp_assignment_decode (list_decode n))"

lemma imp_state_id : " finite (dom x) \<Longrightarrow> imp_state_decode (imp_state_encode x) = x"
 apply (auto simp only: imp_state_encode_def imp_state_decode_def map_to_list_id comp_def
      list_encode_inverse map_map imp_assignment_id)
    apply (auto simp add: map_to_list_id)
  done

fun comm_imp_state_encode:: "(com * imp_state) \<Rightarrow> nat" where
"comm_imp_state_encode (c,i) = prod_encode (comm_encode c, imp_state_encode i)"

fun comm_imp_state_decode :: "nat \<Rightarrow> (com*imp_state)" where
"comm_imp_state_decode n = (case prod_decode n of (c,i) \<Rightarrow> (comm_decode c, imp_state_decode i))"

lemma comm_imp_state_id:
  "finite (dom (snd x)) \<Longrightarrow> comm_imp_state_decode (comm_imp_state_encode x) = x"
  apply (cases x)
  apply (auto simp only: comm_imp_state_encode.simps comm_imp_state_decode.simps comm_id imp_state_id prod_encode_inverse snd_def)
  done

definition imp_assignment_list_encode :: "(vname,bit)assignment list \<Rightarrow> nat" where
"imp_assignment_list_encode xs = list_encode (map imp_assignment_encode xs)"

definition imp_assignment_list_decode :: "nat \<Rightarrow> (vname,bit)assignment list" where
"imp_assignment_list_decode xs = map imp_assignment_decode (list_decode xs)"

lemma imp_assignment_list_id: "imp_assignment_list_decode (imp_assignment_list_encode x) = x"
  apply (auto simp only:imp_assignment_list_decode_def imp_assignment_list_encode_def list_encode_inverse
      imp_assignment_id map_map comp_def map_idI)
  done


fun cilist_encode :: "(com * (vname*bit) list) \<Rightarrow> nat" where
"cilist_encode (c,i) = prod_encode (comm_encode c, imp_assignment_list_encode i)"

fun cilist_decode :: " nat \<Rightarrow> (com * (vname*bit) list)" where
"cilist_decode n = (case prod_decode n of (c,i) \<Rightarrow>
         (comm_decode c, imp_assignment_list_decode i))"

lemma cilist_id: "cilist_decode(cilist_encode x) = x"
  apply (cases x)
  apply (auto simp only: cilist_decode.simps cilist_encode.simps prod_encode_inverse comm_id imp_assignment_list_id)
  done

fun cilist_to_map:: "(com*(vname*bit) list) \<Rightarrow> (com*imp_state) " where
"cilist_to_map (c,i) = (c,map_of i)"



type_synonym operator = "(variable, domain_element) sas_plus_operator"
type_synonym problem = "(variable, domain_element) sas_plus_problem"

definition sas_assignment_list_encode :: "(variable,domain_element)assignment list \<Rightarrow> nat" where
"sas_assignment_list_encode xs =list_encode (map sas_assignment_encode xs)"

definition sas_assignment_list_decode :: "nat \<Rightarrow> (variable,domain_element)assignment list" where
"sas_assignment_list_decode xs = map sas_assignment_decode (list_decode xs)"

lemma sas_assignment_list_id: "sas_assignment_list_decode (sas_assignment_list_encode x) = x"
  apply (auto simp only:sas_assignment_list_decode_def sas_assignment_list_encode_def list_encode_inverse
      sas_assignment_id map_map comp_def map_idI)
  done


definition operator_encode :: "operator \<Rightarrow> nat" where
"operator_encode op = list_encode [sas_assignment_list_encode (precondition_of op),
                                    sas_assignment_list_encode (effect_of op)] "

definition operator_decode :: " nat \<Rightarrow> operator" where
"operator_decode n =  ( case list_decode n of  [p,e] \<Rightarrow>
                       \<lparr>precondition_of = sas_assignment_list_decode p,
                        effect_of = sas_assignment_list_decode e \<rparr> )  "

lemma operator_id : " operator_decode (operator_encode x) = x"
  apply (auto simp add:operator_decode_def operator_encode_def sas_assignment_list_id)
  done

fun list_update_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"list_update_nat l n v = (if l =0 then 0 else if n=0 then (v##tl_nat l) else (hd_nat l) ##
               list_update_nat (tl_nat l) (n-1) v)"

definition list_update_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"list_update_tail l n v = list_update_nat l n v"

lemma subtail_list_update:
"list_update_tail l n v = list_update_nat l n v" using list_update_tail_def by auto

lemma sub_list_update :
      "list_update_nat (list_encode l) n v = list_encode (list_update l n v) "
  apply (induct l arbitrary:n)
  apply (subst list_update_nat.simps)
  apply (auto simp only: sub_hd sub_head sub_tl sub_cons list_encode_eq split:if_splits list.splits
            simp flip: list_encode.simps)
  apply ( simp  (no_asm) only: sub_head sub_tail list_encode.simps list_update_def)
  apply simp
   apply simp
  apply (subst list_update_nat.simps)
   apply (auto simp only: sub_hd sub_head sub_tl sub_cons list_encode_eq split:if_splits list.splits
            simp flip: list_encode.simps)
   apply simp
  apply (simp only: head.simps sub_cons )
  by (metis One_nat_def Suc_pred list_encode.simps(1) list_update_code(3) neq0_conv sub_cons tail.simps(2))

fun restrict_list :: "('vname,'bit) assignment list \<Rightarrow> 'vname list \<Rightarrow> ('vname,'bit) assignment list" where
"restrict_list [] s = []" |
"restrict_list ((x,y)#xs) s = (if x \<in> set s then (x,y) # (restrict_list xs s) else restrict_list xs s)"

lemma sub_restrict_list_helper:
  "map_of (restrict_list xs s) t = restrict_map (map_of xs) (set s) t"
  apply (induct xs)
   apply (auto simp add:snd_def  restrict_map_def)
  done

lemma sub_restrict_list:
"map_of (restrict_list xs s) = restrict_map (map_of xs) (set s)"
  using sub_restrict_list_helper by fast

record  ('variable, 'domain) sas_plus_list_problem =
  variables_ofl :: "'variable list" ("(_\<^sub>\<V>\<^sub>+)" [1000] 999)
  operators_ofl :: "('variable, 'domain) sas_plus_operator list" ("(_\<^sub>\<O>\<^sub>+)" [1000] 999)
  initial_ofl :: "('variable, 'domain) assignment list" ("(_\<^sub>I\<^sub>+)" [1000] 999)
  goal_ofl :: "('variable, 'domain) assignment list" ("(_\<^sub>G\<^sub>+)" [1000] 999)
  range_ofl :: "('variable, 'domain list) assignment list"

fun vdlist_encode :: "(variable, domain_element list) assignment \<Rightarrow> nat" where
"vdlist_encode (x,y) = prod_encode (variable_encode x,list_encode (map domain_element_encode y))"

fun vdlist_decode ::  "nat \<Rightarrow> (variable, domain_element list) assignment" where
"vdlist_decode n = (case prod_decode n of (x,y) \<Rightarrow> (variable_decode x, map domain_element_decode (list_decode y)))"

lemma vdlist_id: "vdlist_decode (vdlist_encode x) = x"
  apply (cases x)
  apply (simp add: comp_def variable_id domain_element_id del:domain_element_decode.simps)
  done

fun list_problem_to_problem ::
  "('v,'d) sas_plus_list_problem \<Rightarrow>('v,'d)sas_plus_problem"
  where   " list_problem_to_problem x =
        \<lparr> variables_of = variables_ofl x,
          operators_of = operators_ofl x,
          initial_of = map_of (initial_ofl x),
          goal_of = map_of (goal_ofl x),
          range_of = map_of (range_ofl x)
       \<rparr>"

definition list_problem_encode ::
    "(variable,domain_element) sas_plus_list_problem \<Rightarrow>nat" where
"list_problem_encode x = list_encode [list_encode (map variable_encode (variables_ofl x)),
                                      list_encode (map operator_encode (operators_ofl x)),
                                      sas_assignment_list_encode (initial_ofl x),
                                       sas_assignment_list_encode (goal_ofl x),
                                       list_encode (map vdlist_encode (range_ofl x)) ] "

definition list_problem_decode ::"nat \<Rightarrow> (variable,domain_element) sas_plus_list_problem" where
"list_problem_decode x = (case list_decode x of
[var,op,i,g,r]  \<Rightarrow> \<lparr>           variables_ofl = map variable_decode (list_decode var),
                               operators_ofl = map operator_decode (list_decode op),
                               initial_ofl = sas_assignment_list_decode i,
                               goal_ofl = sas_assignment_list_decode g,
                               range_ofl = map vdlist_decode (list_decode r) \<rparr> )"

lemma list_problem_id :
      "list_problem_decode (list_problem_encode x) = x"
  apply (auto simp only:list_problem_encode_def list_problem_decode_def list_encode_inverse)
  apply (auto simp add: comp_def variable_id operator_id sas_assignment_list_id vdlist_id simp del: vdlist_decode.simps)
  done

declare elemof.simps [simp del]

fun restrict_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"restrict_nat l s = (if l = 0 then 0 else (let t = restrict_nat (tl_nat l) s in (if elemof (fst_nat (hd_nat l)) s \<noteq> 0 then
    (hd_nat l)## t else t))) "

fun restrict_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"restrict_acc acc l s = (if l = 0 then acc else(if elemof (fst_nat (hd_nat l)) s \<noteq> 0 then
   restrict_acc  ((hd_nat l)## acc) (tl_nat l) s else restrict_acc acc (tl_nat l) s)) "

lemma sub_restrict_nat:
  "restrict_nat (imp_assignment_list_encode l) (vname_list_encode s) = imp_assignment_list_encode (restrict_list l s)"
  apply (simp only: vname_list_encode_def)
  apply (induct l)
   apply (simp add: imp_assignment_list_encode_def)
  subgoal for x l
    apply (cases x)
  apply (subst restrict_nat.simps)
    apply (auto simp only:  sub_cons restrict_list.simps list_encode_eq sub_tl  imp_assignment_list_encode_def sub_tail_map Let_def sub_fst sub_hd sub_head_map list.simps  head.simps imp_assignment_encode.simps fst_def tail.simps non_empty_positive  split:if_splits
  simp flip: list_encode.simps
)
     apply (auto simp only: list_encode.simps sub_elem_of2)
     apply simp
    apply (metis imageE set_map vname_id)
    done
  done

lemma sub_restrict_nat_gen:
  "restrict_nat (list_encode (map prod_encode  l)) (list_encode s) = list_encode (map prod_encode  (restrict_list l s))"
  apply(induct l)
   apply (simp)
  subgoal for x xs
  apply (cases x)
  apply (subst restrict_nat.simps)
    apply (auto simp only:  sub_cons restrict_list.simps list_encode_eq sub_tl  imp_assignment_list_encode_def sub_tail_map Let_def sub_fst sub_hd sub_head_map list.simps  head.simps imp_assignment_encode.simps fst_def tail.simps non_empty_positive  split:if_splits
  simp flip: list_encode.simps
)
     apply (auto simp only: list_encode.simps sub_elem_of2)
    done
  done

lemma restrict_induct:
"restrict_acc acc l s = append_nat (reverse_nat (restrict_nat l s)) acc"
proof -
  obtain acc' l' s' where "acc = list_encode (map prod_encode acc') "
"l = list_encode (map prod_encode l')" "s = list_encode s'"
    by (metis ex_map_conv list_decode_inverse prod_decode_inverse)
  thus ?thesis apply (auto simp only: sub_restrict_nat_gen sub_reverse sub_append rev_map simp flip:
        map_append)
    apply(induct l' arbitrary: acc' acc l)
    apply (subst restrict_acc.simps)
     apply simp
    apply (subst restrict_acc.simps)
    apply (auto simp only: sub_hd head.simps fst_conv  sub_fst list.simps sub_cons sub_tl tail.simps sub_elem_of2)
    apply (auto simp only:restrict_list.simps simp flip: list.map(2))
    apply auto
    done
qed

definition restrict_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat " where
"restrict_tail l s = reverse_nat (restrict_acc 0 l s)"

lemma subtail_restrict:
"restrict_tail l s =  restrict_nat l s"
  using append_nat_0 restrict_induct restrict_tail_def rev_rev_nat by auto

declare elemof.simps [simp]



type_synonym  var = "variable SAS_Plus_Plus_To_SAS_Plus.variable"
type_synonym  dom = "domain_element SAS_Plus_Plus_To_SAS_Plus.domain_element"
type_synonym  sas_plus_state = "(var,dom)  State_Variable_Representation.state"
fun var_encode :: "var \<Rightarrow> nat" where
"var_encode Stage = 0 " |
"var_encode (Var v) = Suc (variable_encode v)"

fun var_decode :: "nat \<Rightarrow> var" where
"var_decode 0 = Stage"|
"var_decode (Suc v) = (Var (variable_decode v))"

lemma var_id: "var_decode (var_encode x) = x"
  apply (cases x)
   apply (auto simp add:variable_id)
  done

fun dom_encode :: "dom \<Rightarrow> nat" where
"dom_encode NonInit = 0"|
"dom_encode Init = Suc 0"|
"dom_encode (DE d) = Suc (Suc (domain_element_encode d))"

fun dom_decode :: "nat \<Rightarrow> dom" where
"dom_decode 0 = NonInit"|
"dom_decode (Suc 0) = Init"|
"dom_decode (Suc (Suc d)) = DE (domain_element_decode d)"

lemma dom_id : "dom_decode (dom_encode x) = x"
 apply (cases x)
   apply (auto simp add:domain_element_id simp del: domain_element_decode.simps)
  done

fun sas_plus_assignment_encode:: "(var,dom) assignment \<Rightarrow> nat" where
  "sas_plus_assignment_encode (v,d) = prod_encode(var_encode v, dom_encode d)"

fun sas_plus_assignment_decode:: " nat \<Rightarrow> (var,dom) assignment" where
  "sas_plus_assignment_decode n = (case prod_decode n of (v,d) \<Rightarrow>
                                (var_decode v, dom_decode d))"

lemma sas_plus_assignment_id:
      "sas_plus_assignment_decode (sas_plus_assignment_encode x) = x"
  apply (cases x)
  apply (auto simp add:var_id dom_id)
  done

definition sas_plus_assignment_list_encode ::  "(var,dom) assignment list \<Rightarrow> nat "
  where "sas_plus_assignment_list_encode x = list_encode (map sas_plus_assignment_encode x)"

definition sas_plus_assignment_list_decode ::  "nat \<Rightarrow> (var,dom) assignment list"
  where "sas_plus_assignment_list_decode x = map sas_plus_assignment_decode (list_decode x)"

lemma sas_plus_assignment_list_id:
    "sas_plus_assignment_list_decode ( sas_plus_assignment_list_encode x) = x"
  apply (auto simp add: sas_plus_assignment_list_encode_def  sas_plus_assignment_list_decode_def comp_def
        sas_plus_assignment_id  simp del: sas_plus_assignment_decode.simps)
  done

fun islist_encode :: "(dom \<times> (variable,domain_element) assignment list) \<Rightarrow> nat" where
"islist_encode (i,s) = prod_encode (dom_encode i, sas_assignment_list_encode s)"

fun islist_decode :: "nat \<Rightarrow> (dom \<times> (variable,domain_element) assignment list)" where
"islist_decode n = (case prod_decode n of (i,s) \<Rightarrow>
         (dom_decode i, sas_assignment_list_decode s))"

lemma islist_id: "islist_decode(islist_encode x) = x"
  apply (cases x)
  apply (auto simp only: islist_decode.simps islist_encode.simps prod_encode_inverse dom_id sas_assignment_list_id)
  done

fun islist_to_map:: "(dom \<times> (variable,domain_element) assignment list) \<Rightarrow> (dom \<times> sas_state) " where
"islist_to_map (i,s) = (i,map_of s)"

definition sas_plus_state_decode :: "nat \<Rightarrow> sas_plus_state" where
"sas_plus_state_decode x = map_of (sas_plus_assignment_list_decode x)"

type_synonym operator_plus = "(var, dom) sas_plus_operator"
type_synonym problem_plus = "(var, dom) sas_plus_problem"

definition operator_plus_encode :: "operator_plus \<Rightarrow> nat" where
"operator_plus_encode op = list_encode [sas_plus_assignment_list_encode (precondition_of op),
                                    sas_plus_assignment_list_encode (effect_of op)] "

definition operator_plus_decode :: " nat \<Rightarrow> operator_plus" where
"operator_plus_decode n =  ( case list_decode n of  [p,e] \<Rightarrow>
                       \<lparr>precondition_of = sas_plus_assignment_list_decode p,
                        effect_of = sas_plus_assignment_list_decode e \<rparr> )  "

lemma operator_plus_id : " operator_plus_decode (operator_plus_encode x) = x"
  apply (auto simp add:operator_plus_decode_def operator_plus_encode_def sas_plus_assignment_list_id)
  done

fun the_nat :: "nat \<Rightarrow> nat" where
 "the_nat x = x-1"

fun list_option_encode :: " nat list option \<Rightarrow> nat" where
"list_option_encode None = 0"|
"list_option_encode (Some x) = Suc (list_encode x)"

fun list_option_decode :: "nat \<Rightarrow>  nat list option" where
"list_option_decode 0 = None"|
"list_option_decode (Suc x) = Some (list_decode x)"

lemma list_option_id:"list_option_decode (list_option_encode x) = x"
  apply (cases x)
   apply (auto)
  done

lemma sub_the: " the_nat (list_option_encode x) = list_encode (thef x)"
  apply (cases x)
   apply (auto)
  done

fun thefn :: "nat option \<Rightarrow> nat" where
"thefn None = 0"|
"thefn (Some x) = x"

lemma sub_the2: "the_nat (option_encode  x) = thefn x"
  apply (cases x)
  apply auto
  done


fun map_list_find ::"('a,'b) assignment list \<Rightarrow>'a \<Rightarrow> 'b option" where
"map_list_find [] _ = None "|
"map_list_find ((x,y)#xs) a = (if x =a then Some y else map_list_find xs a )"

lemma sub_map_list_find: "map_list_find xs a = (map_of xs) a"
  apply (induct xs)
   apply auto
  done

fun map_list_find_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"map_list_find_nat xs a = (if xs = 0 then 0 else if fst_nat (hd_nat xs) = a then some_nat (snd_nat (hd_nat xs))
  else map_list_find_nat (tl_nat xs) a) "

lemma sub_map_list_find_nat:
      "map_list_find_nat (list_encode (map prod_encode xs)) a =
        option_encode (map_list_find xs a)"
  apply (induct xs)
   apply simp
  apply (subst  map_list_find_nat.simps)
  apply (auto simp only: list.simps sub_hd head.simps sub_fst fst_def sub_snd snd_def sub_some sub_tl tail.simps
        map_list_find.simps )
  apply auto
  done

fun vdlist_plus_encode :: "(var, dom list) assignment \<Rightarrow> nat" where
"vdlist_plus_encode (x,y) = prod_encode (var_encode x,list_encode (map dom_encode y))"

fun vdlist_plus_decode ::  "nat \<Rightarrow> (var, dom list) assignment" where
"vdlist_plus_decode n = (case prod_decode n of (x,y) \<Rightarrow> (var_decode x, map dom_decode (list_decode y)))"

lemma vdlist_plus_id: "vdlist_plus_decode (vdlist_plus_encode x) = x"
  apply (cases x)
  apply (simp add: comp_def var_id dom_id del:domain_element_decode.simps)
  done

definition list_problem_plus_encode ::
    "(var,dom) sas_plus_list_problem \<Rightarrow>nat" where
"list_problem_plus_encode x = list_encode [list_encode (map var_encode (variables_ofl x)),
                                      list_encode (map operator_plus_encode (operators_ofl x)),
                                      sas_plus_assignment_list_encode (initial_ofl x),
                                       sas_plus_assignment_list_encode (goal_ofl x),
                                       list_encode (map vdlist_plus_encode (range_ofl x)) ] "

definition list_problem_plus_decode ::"nat \<Rightarrow> (var,dom) sas_plus_list_problem" where
"list_problem_plus_decode x = (case list_decode x of
[var,op,i,g,r]  \<Rightarrow> \<lparr>           variables_ofl = map var_decode (list_decode var),
                               operators_ofl = map operator_plus_decode (list_decode op),
                               initial_ofl = sas_plus_assignment_list_decode i,
                               goal_ofl = sas_plus_assignment_list_decode g,
                               range_ofl = map vdlist_plus_decode (list_decode r) \<rparr> )"

lemma list_problem_plus_id :
      "list_problem_plus_decode (list_problem_plus_encode x) = x"
  apply (auto simp only:list_problem_plus_encode_def list_problem_plus_decode_def list_encode_inverse)
  apply (auto simp add: comp_def var_id operator_plus_id sas_plus_assignment_list_id vdlist_plus_id simp del: vdlist_plus_decode.simps)
  done

(*

lemma sub_thefn: "the_nat (option_encode x) =thefn x"
  apply (cases x)
   apply (auto)
  done

definition fun_of :: "(vname,nat) assignment list \<Rightarrow> vname \<Rightarrow> nat" where
"fun_of x v =  (case (map_of x) v of None \<Rightarrow> 0 | Some x \<Rightarrow> x)"

fun fun_list_find :: "('a,nat) assignment list \<Rightarrow> 'a \<Rightarrow> nat" where
"fun_list_find [] _ = 0"|
"fun_list_find ((x,y)#xs) a = (if x= a then y else fun_list_find xs a)"

lemma sub_fun_list_find:"fun_list_find xs a = fun_of xs a"
  apply(induct xs)
   apply (auto simp add:fun_of_def)
  done

fun fun_list_find_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"fun_list_find_nat xs a  = (if xs = 0 then 0 else if fst_nat (hd_nat xs) = a then snd_nat (hd_nat xs) else fun_list_find_nat (tl_nat xs) a) "

fun fun_list_find_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"fun_list_find_tail xs a  = (if xs = 0 then 0 else if fst_nat (hd_nat xs) = a then snd_nat (hd_nat xs) else fun_list_find_tail (tl_nat xs) a) "

lemma subtail_fun_list_find: "fun_list_find_tail xs a = fun_list_find_nat xs a"
  apply(induct xs a rule: fun_list_find_tail.induct)
  apply auto
  done

lemma sub_fun_list_find_nat :
 "fun_list_find_nat (list_encode (map prod_encode xs)) a = fun_list_find xs a"
  apply (induct xs)
   apply simp
  apply (subst fun_list_find_nat.simps)
  apply (auto simp only: list.simps list_encode_eq
        sub_hd head.simps sub_fst fst_def sub_snd snd_def sub_tl tail.simps

simp flip: list_encode.simps

 )
  apply auto
  done

fun impm_assignment_encode :: "(vname,nat) assignment \<Rightarrow> nat" where
"impm_assignment_encode (v,n) = prod_encode (vname_encode v, n)"

fun impm_assignment_decode :: " nat \<Rightarrow> (vname,nat) assignment" where
"impm_assignment_decode  x =  (case prod_decode x of (v,n) \<Rightarrow> (vname_decode v, n))"

lemma impm_assignment_id:"impm_assignment_decode (impm_assignment_encode x) = x"
  by (cases x) (auto simp add:vname_id)

definition impm_assignment_list_encode ::  "(vname,nat) assignment list \<Rightarrow> nat" where
"impm_assignment_list_encode x = list_encode (map impm_assignment_encode x)"

definition impm_assignment_list_decode ::  "nat \<Rightarrow> (vname,nat) assignment list" where
"impm_assignment_list_decode x = map impm_assignment_decode ( list_decode x)"

lemma impm_assignment_list_id:
  "impm_assignment_list_decode (impm_assignment_list_encode x) = x"
  apply (auto simp add: impm_assignment_list_decode_def  impm_assignment_list_encode_def)
  apply (auto simp only: comp_def impm_assignment_id)
  apply auto
  done

fun bit_option_encode :: "bit option \<Rightarrow> nat" where
"bit_option_encode None = 0"|
"bit_option_encode (Some x) = Suc (bit_encode x)"

fun bit_option_decode :: "nat \<Rightarrow> bit option" where
"bit_option_decode 0 = None"|
"bit_option_decode (Suc n ) = Some (bit_decode n)"

lemma bit_option_id : "bit_option_decode (bit_option_encode x) = x"
  apply (cases x)
   apply auto
  done

lemma inj_fun_list_find : "inj f \<Longrightarrow> fun_list_find (map (\<lambda>(x,y). (f x, y) ) xs) (f x) =
fun_list_find xs x
"
  apply ( induct xs)
   apply (auto simp add:inj_def)
  done

lemma inj_fun_list_find_plus : "inj f \<Longrightarrow> fun_list_find (map (\<lambda>(x,y). (f x, g y) ) xs) (f x) =
fun_list_find (map (\<lambda>(x,y). (x , g y)) xs) x
"
  apply ( induct xs)
   apply (auto simp add:inj_def)
  done

fun max_list :: "nat list \<Rightarrow> nat" where
"max_list [] = 0"|
"max_list (x#xs) = max x (max_list xs)"

fun max_list_nat :: "nat \<Rightarrow> nat" where
"max_list_nat xs = (if xs = 0 then 0 else max (hd_nat xs) (max_list_nat (tl_nat xs)))"

fun max_list_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"max_list_acc acc xs = (if xs = 0 then acc else max_list_acc (max (hd_nat xs) acc) (tl_nat xs))"

lemma sub_max_list_nat: "max_list_nat (list_encode xs) = max_list xs"
  apply (induct xs)
  apply simp
  apply (subst max_list_nat.simps)
  apply (auto simp only: sub_tl tail.simps sub_hd head.simps)
  apply auto
  done

lemma max_list_acc_correct:
"max_list_acc acc xs = max (max_list_nat xs) acc"
proof -
  obtain xs' where "xs = list_encode xs'"
    by (metis list_decode_inverse)
  thus ?thesis apply(auto simp only:sub_max_list_nat )
    apply(induct xs' arbitrary: xs acc)
     apply simp
    apply(subst max_list_acc.simps)
    apply (auto simp only: sub_tl tail.simps sub_hd head.simps)
    apply auto
    done
qed

definition max_list_tail :: "nat \<Rightarrow>  nat" where
"max_list_tail xs = max_list_acc 0 xs "

lemma subtail_max_list:
"max_list_tail xs =  max_list_nat xs"
  using max_list_acc_correct max_list_tail_def by presburger



lemma sub_max_list: "xs \<noteq> [] \<Longrightarrow> max_list xs = Max (set xs)"
  apply (cases xs)
    apply (auto simp add: Max.set_eq_fold )
  apply (induct xs)
   apply (auto)
  using Max_insert
  by (metis List.finite_set Max_singleton empty_iff list.set(1) list.set_intros(1)
 list.simps(15) max_0R max_list.elims)



fun del :: "('a,'b) assignment list \<Rightarrow> 'a \<Rightarrow>  ('a,'b) assignment list" where
"del [] _ = []"|
"del ((x,y)#xs) a = (if x = a then del xs a else (x,y)# del xs a)"

lemma del_filter:
"del xs a = filter(\<lambda>x. fst x \<noteq> a) xs"
  apply(induct xs)
   apply auto
  done


fun del_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"del_nat xs a = (if xs =0 then 0 else if fst_nat (hd_nat xs) = a then del_nat (tl_nat xs) a else cons
(hd_nat xs)  (del_nat (tl_nat xs) a) )"
lemma sub_del: "del_nat (list_encode (map prod_encode xs)) a = list_encode (map prod_encode (del xs a))"
  apply (induct xs)
   apply simp
  apply (subst del_nat.simps)
  apply (simp only: sub_fst sub_hd sub_tl sub_cons list.simps head.simps tail.simps)
  subgoal for ax xs
    apply (cases ax)
    apply auto
    done
  done

lemma [termination_simp]:"length (del xs x) < Suc (length xs)"
  apply (induct xs)
   apply auto
  done

lemma del_correct: "\<forall>(x,y) \<in> set (del xs a). x \<noteq> a"
  apply (induct xs)
  apply auto
  by (smt case_prod_conv set_ConsD)

lemma del_correct_corr: " a \<noteq> x \<Longrightarrow> map_of (del xs a) x = map_of xs x"
  apply (induct xs)
   apply (auto split:if_splits)
  done
fun nub :: "('a,'b) assignment list \<Rightarrow> ('a,'b) assignment list" where
"nub [] = [] "|
"nub ((x,y)#xs) = (x,y) # nub (del xs x) "

lemma del_shorter : "length (del xs a) \<le> length xs"
  apply (induct xs)
   apply auto
  done

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