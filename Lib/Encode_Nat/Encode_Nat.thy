(*  Title:      Encode_Nat.thy
    Author:     Johannes Neubrand, TU Muenchen
    Author:     Andreas Vollert, TU Muenchen
    Copyright   2022, 2023
*)

theory Encode_Nat
  imports
    Main
    "HOL-Library.Char_ord"
    "HOL-Library.Nat_Bijection"
    "HOL-Library.Tree"
    "HOL-Library.List_Lexorder"
    "HOL-Library.Product_Lexorder"
    "HOL-Library.Multiset"
    "HOL-Library.Option_ord"
    Test
  keywords
    "test" :: thy_decl and
    "test2" :: thy_decl and
    "datatype_lift_nat" :: thy_decl and
    "datatype_nat_decode" :: thy_decl and
    "datatype_nat_wellbehaved" :: thy_goal and
    "function_nat_rewrite" :: thy_decl and
    "function_nat_rewrite_auto" :: thy_decl and
    "function_nat_rewrite_correctness" :: thy_goal
begin


class lift_nat =
  fixes Abs_nat :: "'a \<Rightarrow> nat"
  fixes Rep_nat :: "nat \<Rightarrow> 'a"
  assumes Rep_nat_Abs_nat_id[simp]: "\<And>x. Rep_nat (Abs_nat x) = x"
begin
lemma inj_Abs_nat: "inj Abs_nat"
  by(rule inj_on_inverseI[of _ Rep_nat], simp)

definition cr_nat :: "nat \<Rightarrow> 'a \<Rightarrow> bool" where
  "cr_nat \<equiv> (\<lambda>n l. n = Abs_nat l)"

lemma typedef_nat: "type_definition Abs_nat Rep_nat (Abs_nat ` UNIV)"
  by (unfold_locales) auto

lemmas typedef_nat_transfer[OF typedef_nat cr_nat_def, transfer_rule] =
  typedef_bi_unique typedef_right_unique typedef_left_unique typedef_right_total

lemma cr_nat_Abs_nat[transfer_rule]:
  "cr_nat (Abs_nat x) x"
  unfolding cr_nat_def by simp

end




declare [[ML_print_depth = 50]]

datatype ('a, 'b) keyed_list_tree =
  KLeaf |
  KNode "(('a, 'b) keyed_list_tree)" 'a "('b list)" "(('a, 'b) keyed_list_tree)"

type_synonym pair_repr = nat


fun atomic :: "nat \<Rightarrow> pair_repr" where
  "atomic a = a"

fun pair :: "pair_repr \<Rightarrow> pair_repr \<Rightarrow> pair_repr"
  where "pair l r = prod_encode (l, r)"

fun fstP :: "pair_repr \<Rightarrow> pair_repr" where
  "fstP v = fst (prod_decode v)"

fun sndP :: "pair_repr \<Rightarrow> pair_repr" where
  "sndP v = snd (prod_decode v)"

lemma prod_encode_0: "prod_encode (0,0) = 0" by (simp add: prod_encode_def)

lemma inj_inverseI: "g \<circ> f = id \<Longrightarrow> inj f"
  by(rule inj_on_inverseI, rule pointfree_idE, simp)


lemma prod_decode_less[termination_simp]:
  assumes "v < v'"
  shows fst_prod_decode_less: "fst (prod_decode v) < v'"
    and snd_prod_decode_less: "snd (prod_decode v) < v'"
  using assms
    le_prod_encode_1[of "fstP v" "sndP v"]
    le_prod_encode_2[of "sndP v" "fstP v"]
  by simp+

lemma prod_decode_lte:
  assumes "v \<le> v'"
  shows fst_prod_decode_lte: "fst (prod_decode v) \<le> v'"
    and snd_prod_decode_lte: "snd (prod_decode v) \<le> v'"
  using prod_decode_less[of v "Suc v'"] assms by simp+

lemma snd_prod_encode_lt: "a > 0 \<Longrightarrow> b < prod_encode (a, b)"
  by (induction b; simp add: prod_encode_def)

corollary snd_prod_decode_lt_intro[termination_simp]:
  assumes "fstP v \<noteq> 0"
  shows "snd (prod_decode v) < v"
  by (metis assms fstP.simps gr0I prod.collapse snd_prod_encode_lt prod_decode_inverse)




inductive_set subpairings :: "pair_repr \<Rightarrow> pair_repr set" for x where
  "x \<in> subpairings x"
| "t \<in> subpairings x \<Longrightarrow> fstP t \<in> subpairings x"
| "t \<in> subpairings x \<Longrightarrow> sndP t \<in> subpairings x"

lemma
  shows subpairings_fstP_imp: "a \<in> subpairings (fstP x) \<Longrightarrow> a \<in> subpairings x" (is "(PROP ?P)")
    and subpairings_sndP_imp: "a \<in> subpairings (sndP x) \<Longrightarrow> a \<in> subpairings x" (is "(PROP ?Q)")
  by(induction rule: subpairings.induct; blast intro: subpairings.intros)+



ML_file \<open>./Encode_Nat.ML\<close>



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
test2 num

test list


fun reverset :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "reverset [] r = r"
| "reverset (l # ls) r = reverset ls (l # r)"

lemma reverset_rev: "reverset l r = rev l @ r"
  by (induction l r rule: reverset.induct; simp)

lemma reverset_correct: "reverset l [] = rev l"
  by (simp add: reverset_rev)

(* TODO: put into other commands *)

(*
test2 list
thm Cons_nat_equiv
test2 bool

test2 char

test2 prod

test2 tree

test2 keyed_list_tree
 *)


(* Do nat manually as lifting of nat is different *)
lemma case_nat_eq_if:
  "(case Rep_nat arg\<^sub>1 of 0 \<Rightarrow> f\<^sub>1 | Suc x \<Rightarrow> f\<^sub>2 x) = (if arg\<^sub>1 = 0 then f\<^sub>1 else f\<^sub>2 ((Rep_nat arg\<^sub>1) - 1))"
  by(simp add: Rep_nat_nat.simps split: nat.split)

definition case_nat_nat where
  "case_nat_nat \<equiv>
    \<lambda>(f\<^sub>1::nat) (f\<^sub>2::nat \<Rightarrow> nat) (arg\<^sub>1::nat). if fstP arg\<^sub>1 = 0 then f\<^sub>1 else f\<^sub>2 (arg\<^sub>1 - 1)"

test2 list print_theorems
test2 bool print_theorems
test2 char print_theorems
test2 prod print_theorems
test2 tree print_theorems
test2 keyed_list_tree print_theorems


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

lemma subtrees_subtreest:
  "mset (subtrees t @ concat (map subtrees ts) @ stk) = mset (subtreest t ts stk)"
  by (induction t ts stk rule: subtreest.induct; simp)

lemma subtreest_correct: "mset (subtrees t) = mset (subtreest t [] [])"
  using subtrees_subtreest[of t "[]" "[]"] by simp



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




(* TODOs/Things not wroking/Things to investigate *)


fun baz :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
  "baz acc [[]] = acc"
| "baz acc [] = acc"
| "baz acc (xs#xss) = baz (append acc xs) xss"

(* function_nat_rewrite_auto baz *)

fun bazz where
  "bazz acc [[]] = acc"
| "bazz acc [] = acc"
| "bazz acc ((v # va) # xss) = bazz (append acc (v # va)) xss"
| "bazz acc (xs # v # va) = bazz (append acc xs) (v # va)"

fun baz2 :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
  "baz2 acc [] = acc"
| "baz2 acc (xs#xss) = baz2 (append acc xs) xss"




(* function_nat_rewrite_auto bazz *)


(* can't handle case expressions *)
fun test3 where
  "test3 x = (case x of True \<Rightarrow> False | False \<Rightarrow> True)"

(* function_nat_rewrite_auto test3 *)

(*

TODO: case_list xs f (\<lambda> a as. g a as) = if ... then f else g (fst (snd (arg1)) ..

*)

end