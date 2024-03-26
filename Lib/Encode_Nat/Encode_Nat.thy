(*  Title:      Encode_Nat.thy
    Author:     Johannes Neubrand, TU Muenchen
    Author:     Andreas Vollert, TU Muenchen
    Copyright   2022, 2023, 2024
*)

theory Encode_Nat
  imports
    Main
    "HOL-Library.Nat_Bijection"
    "HOL-Library.Simps_Case_Conv"
    "HOL-Library.Tree"
    HOL_To_IMP_Minus.Compile_Nat
    HOL_To_IMP_Minus.HOL_To_IMP_Minus_Fun_Pattern_Setup
    Transport.Transport_Typedef_Base
  keywords
    "datatype_lift_nat" :: thy_decl and
    "function_lift_nat" :: thy_decl and
    "test" :: thy_decl
begin

class lift_nat =
  fixes Abs_nat :: "'a \<Rightarrow> nat"
  fixes Rep_nat :: "nat \<Rightarrow> 'a"
  assumes Rep_nat_Abs_nat_id[simp]: "\<And>x. Rep_nat (Abs_nat x) = x"
begin

lemma inj_Abs_nat: "inj Abs_nat"
  by(rule inj_on_inverseI[of _ Rep_nat], simp)

(*@Vollert: are you sure you don't want this to be "'a \<Rightarrow> nat \<Rightarrow> bool"? Usually, the type that should
be transferred from stands on the left (Kevin)*)
definition cr_nat :: "nat \<Rightarrow> 'a \<Rightarrow> bool" where
  "cr_nat \<equiv> (\<lambda>n l. n = Abs_nat l)"

lemma typedef_nat: "type_definition Abs_nat Rep_nat (Abs_nat ` UNIV)"
  by (unfold_locales) auto

lemmas typedef_nat_transfer[OF typedef_nat cr_nat_def, transfer_rule] =
  typedef_bi_unique typedef_right_unique typedef_left_unique typedef_right_total

sublocale lift_nat_type_def :
  type_definition Abs_nat Rep_nat "(Abs_nat ` UNIV)" by (fact typedef_nat)

lemma cr_nat_Abs_nat[transfer_rule]:
  "cr_nat (Abs_nat x) x"
  unfolding cr_nat_def by simp

lemma Galois_eq_range_Abs_nat_Rep_nat_eq_inv_cr_nat:
  "galois_rel.Galois (=) (=\<^bsub>range Abs_nat\<^esub>) Rep_nat = cr_nat\<inverse>"
  unfolding cr_nat_def by (intro ext)
  (fastforce elim: galois_rel.left_GaloisE intro: galois_rel.left_GaloisI)


end


type_synonym pair_repr = nat


datatype ('a, 'b) keyed_list_tree =
  KLeaf |
  KNode "(('a, 'b) keyed_list_tree)" 'a "('b list)" "(('a, 'b) keyed_list_tree)"


definition pair :: "pair_repr \<Rightarrow> pair_repr \<Rightarrow> pair_repr"
  where "pair l r = prod_encode (l, r)"

definition fstP :: "pair_repr \<Rightarrow> pair_repr" where
  "fstP v = fst (prod_decode v)"

definition sndP :: "pair_repr \<Rightarrow> pair_repr" where
  "sndP v = snd (prod_decode v)"

lemmas [termination_simp] = fstP_def sndP_def

lemma prod_encode_0: "prod_encode (0, 0) = 0"
  by (simp add: prod_encode_def)

lemma prod_decode_less[termination_simp]:
  assumes "v < v'"
  shows fst_prod_decode_less: "fst (prod_decode v) < v'"
    and snd_prod_decode_less: "snd (prod_decode v) < v'"
  using assms le_prod_encode_1[of "fstP v" "sndP v"] le_prod_encode_2[of "sndP v" "fstP v"]
  by (simp add: fstP_def sndP_def)+

lemma prod_encode_less:
  assumes "0 < a"
  shows fst_prod_encode_less: "a < prod_encode (a, b)"
    and snd_prod_encode_less: "b < prod_encode (a, b)"
  using assms by (induction a; simp add: prod_encode_def)+

corollary prod_decode_less_intro[termination_simp]:
  assumes "0 < fstP v"
  shows "snd (prod_decode v) < v"
    and "fst (prod_decode v) < v"
  using assms prod_decode_inverse[of v]
  by (cases "prod_decode v"; fastforce simp add: fstP_def prod_encode_less)+


declare [[ML_print_depth = 50]]
ML_file \<open>./Encode_Nat.ML\<close>

declare [[show_types = true]]

datatype_lift_nat nat
print_theorems

datatype_lift_nat list
print_theorems

datatype_lift_nat bool
print_theorems

datatype_lift_nat char
print_theorems

datatype_lift_nat prod
print_theorems

datatype_lift_nat tree
print_theorems

datatype_lift_nat keyed_list_tree
print_theorems

datatype_lift_nat num
print_theorems

datatype_lift_nat option
print_theorems



(* functions for tesiting later *)

fun reverset :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "reverset [] r = r"
| "reverset (l # ls) r = reverset ls (l # r)"



function_lift_nat reverset
print_theorems


lemma reverset_rev: "reverset l r = rev l @ r"
  by (induction l r rule: reverset.induct; simp)

lemma reverset_correct: "reverset l [] = rev l"
  by (simp add: reverset_rev)


fun prefixes :: "'a list \<Rightarrow> ('a list) list" where
  "prefixes (v # vs) = (v # vs) # (prefixes vs)"
| "prefixes [] = [[]]"

fun prefixest :: "'a list \<Rightarrow> ('a list) list \<Rightarrow> ('a list) list" where
  "prefixest (v # vs) ps = prefixest vs ((v # vs) # ps)"
| "prefixest [] ps = [] # ps"

lemma prefixest_prefixes: "prefixest a l = rev (prefixes a) @ l"
  by (induction a l rule: prefixest.induct; simp)

corollary prefixest_correct: "prefixest a [] = rev (prefixes a)"
  by (simp add: prefixest_prefixes)


lemma reverset_length: "length xs = length (reverset xs [])"
  by(induction xs; simp add: reverset_rev)


function foo :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "foo [] acc = acc"
| "foo (x # xs) acc = foo (reverset xs []) (x # (reverset acc []))"
  using reverset.cases by blast+
termination by(relation "measure (length o fst)"; simp add: reverset_correct)

fun prefixes2 :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
  "prefixes2 [] ps = reverset ([] # ps) []"
| "prefixes2 (a # b) ps = prefixes2 b ((a # b) # ps)"


fun subtrees :: "'a tree \<Rightarrow> 'a tree list" where
  "subtrees \<langle>\<rangle> = []"
| "subtrees \<langle>l, v, r\<rangle> = subtrees l @ subtrees r @ [l] @ [r]"

function subtreest :: "'a tree \<Rightarrow> 'a tree list \<Rightarrow> 'a tree list \<Rightarrow> 'a tree list" where
  "subtreest \<langle>\<rangle> [] ts = ts"
| "subtreest \<langle>\<rangle> (s # stk) ts = subtreest s stk ts"
| "subtreest \<langle>l, v, r\<rangle> stk ts = subtreest l (r # stk) (l # r # ts)"
  using neq_Leaf_iff surj_pair
  by simp_all (metis neq_Leaf_iff splice.cases surj_pair)
termination
  by (relation "(\<lambda>(t, stk, _). size t + size1 t + sum_list (map (\<lambda>t. size t + size1 t) stk))
                <*mlex*> {}"; simp add: wf_mlex mlex_less)



fun reverse_acc where
  "reverse_acc acc [] = acc"
| "reverse_acc acc (x#xs) = reverse_acc (x#acc) xs"


fun reverse where
  "reverse xs = reverse_acc [] xs"

lemma reverse_acc_append_acc: "reverse_acc acc xs = (reverse_acc [] xs) @ acc"
proof(induction xs arbitrary: acc)
  case Nil show ?case by simp
next
  case (Cons x xs)
  show ?case using Cons[of "(x # acc)"] Cons[of "[x]"] by simp
qed

lemma reverse_equiv: "reverse xs = rev xs"
  by(induction xs; simp)
    (subst reverse_acc_append_acc, simp)


fun append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "append xs ys = reverse_acc ys (reverse xs)"


lemma append_nil: "append xs [] = xs"
proof(induction xs)
  case Nil show ?case by simp
next
  case (Cons a xs)
  have "reverse_acc [] (reverse_acc acc xs) = (reverse_acc [] acc) @ xs" for acc
    using reverse_acc_append_acc by(induction xs arbitrary: acc; force)
  then show ?case by simp
qed


lemma append_equiv:"append xs ys = xs @ ys"
proof(cases xs)
  case Nil then show ?thesis by simp
next
  case (Cons x xs)
  then show ?thesis
    by (simp add: reverse_acc_append_acc[of ys "(reverse (x # xs))"] del: reverse.simps
        List.append.append_Cons, simp add: append_nil flip: append.simps del: reverse.simps
        List.append.append_Cons)
qed



fun plus where
  "plus 0 n = n"
| "plus (Suc m) n = plus m (Suc n)"

lemma plus_equiv: "plus a b = a + b"
  by(induction a arbitrary: b; simp)





fun fn_test1 :: "nat \<Rightarrow> nat" where
  "fn_test1 x = (if x = 3 then 5 else 7)"


fun fn_test2 :: "('a::order_bot) \<Rightarrow> nat" where
  "fn_test2 a = 2"



fun baz :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
  "baz acc [[]] = acc"
| "baz acc [] = acc"
| "baz acc (xs#xss) = baz (append acc xs) xss"


fun bazz where
  "bazz acc [[]] = acc"
| "bazz acc [] = acc"
| "bazz acc ((v # va) # xss) = bazz (append acc (v # va)) xss"
| "bazz acc (xs # v # va) = bazz (append acc xs) (v # va)"

fun baz2 :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
  "baz2 acc [] = acc"
| "baz2 acc (xs#xss) = baz2 (append acc xs) xss"


fun test3 where
  "test3 x = (case x of True \<Rightarrow> False | False \<Rightarrow> True)"


end