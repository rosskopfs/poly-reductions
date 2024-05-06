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
    Transport.HOL_Alignment_Functions
    Transport.Transport_Prototype
    Transport.Transport_Typedef_Base
  keywords
    "datatype_lift_nat" :: thy_decl and
    "function_lift_nat" :: thy_decl and
    "test" :: thy_decl
begin


section\<open>Encoding of datatypes\<close>


(* TODO: Shouldn't the signature (or names) of \<^term>\<open>Abs_nat\<close> and \<^term>\<open>Rep_nat\<close> be swapped?
  In \<^locale>\<open>type_definition\<close>, the names are the other way around. *)
class lift_nat =
  fixes Abs_nat :: "'a \<Rightarrow> nat"
  fixes Rep_nat :: "nat \<Rightarrow> 'a"
  assumes Rep_nat_Abs_nat_id[simp]: "\<And>x. Rep_nat (Abs_nat x) = x"
begin

lemma inj_Abs_nat: "inj Abs_nat"
  by(rule inj_on_inverseI[of _ Rep_nat], simp)

definition cr_nat :: "nat \<Rightarrow> 'a \<Rightarrow> bool" where
  "cr_nat \<equiv> (\<lambda>n l. n = Abs_nat l)"

sublocale lift_nat_type_def: type_definition Abs_nat Rep_nat "(Abs_nat ` UNIV)"
  by (unfold_locales) auto

lemmas
  typedef_nat_transfer[OF lift_nat_type_def.type_definition_axioms cr_nat_def, transfer_rule] =
  typedef_bi_unique typedef_right_unique typedef_left_unique typedef_right_total

lemma cr_nat_Abs_nat[transfer_rule]:
  "cr_nat (Abs_nat x) x"
  unfolding cr_nat_def by simp

lemma Galois_eq_range_Abs_nat_Rep_nat_eq_inv_cr_nat:
  "galois_rel.Galois (=) (=\<^bsub>range Abs_nat\<^esub>) Rep_nat = cr_nat\<inverse>"
  unfolding cr_nat_def by (intro ext)
    (fastforce elim: galois_rel.left_GaloisE intro: galois_rel.left_GaloisI)

end

type_synonym pair_repr = nat

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



section\<open>Translation of functions\<close>


(*PER for lift_nat class*)
lemmas lift_nat_partial_equivalence_rel_equivalence =
  iffD1[OF
    transport.partial_equivalence_rel_equivalence_right_left_iff_partial_equivalence_rel_equivalence_left_right
    lift_nat_type_def.partial_equivalence_rel_equivalenceI]

(*register PER*)
declare lift_nat_partial_equivalence_rel_equivalence[per_intro]

(*nicer relatedness theorem output*)
declare Galois_eq_range_Abs_nat_Rep_nat_eq_inv_cr_nat[trp_relator_rewrite]


lemma rel_inv_Fun_Rel_rel_eq[simp]: "(R \<Rrightarrow> S )\<inverse> = (R\<inverse> \<Rrightarrow> S\<inverse>)"
  by fast

lemma rel_inv_Fun_Rel_swap: "Fun_Rel_rel R\<inverse> S\<inverse> f g = Fun_Rel_rel R S g f"
  by blast

declare [[ML_print_depth = 50]]
declare [[show_types = false]]
ML_file \<open>./Encode_Nat.ML\<close>



(* Encoding of standard datatypes *)



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

datatype_lift_nat num
print_theorems

datatype_lift_nat option
print_theorems


(* HOL.If has to be translated manually atm *)

unbundle lifting_syntax

lemma if_related_self[trp_in_dom]:
  "(lift_nat_type_def.R \<Rrightarrow> lift_nat_type_def.R \<Rrightarrow> lift_nat_type_def.R \<Rrightarrow> lift_nat_type_def.R)
    HOL.If HOL.If"
  by simp

trp_term If_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where x = "HOL.If :: bool \<Rightarrow> ('a :: lift_nat) \<Rightarrow> _"
  by trp_prover

lemma If_nat_lifting[transfer_rule]:
  "(cr_nat ===> cr_nat ===> cr_nat ===> cr_nat)
    (If_nat TYPE('a::lift_nat)) (HOL.If :: bool \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a)"
  using If_nat_related' by fast

lemma If_case_def: "HOL.If c t f = (case c of True \<Rightarrow> t | False \<Rightarrow> f)"
  by simp

schematic_goal If_nat_synth:
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> bool \<Rightarrow> bool) c (Rep_nat c)"
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a \<Rightarrow> bool) t (Rep_nat t)"
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a \<Rightarrow> bool) f (Rep_nat f)"
  shows "cr_nat ?t ((HOL.If :: bool \<Rightarrow> 'a::lift_nat \<Rightarrow> 'a \<Rightarrow> 'a) (Rep_nat c) (Rep_nat t) (Rep_nat f))"
  by (subst If_case_def, transfer_prover)

lemma If_nat_synth_def:
  fixes c :: "bool" and t :: "'a::lift_nat" and f :: "'a"
  assumes "cn = Abs_nat c"
  assumes "tn = Abs_nat t"
  assumes "fn = Abs_nat f"
  shows "If_nat TYPE('a) cn tn fn = case_bool_nat tn fn cn"
  unfolding assms
  by (rule HOL.trans[OF _ If_nat_synth[unfolded cr_nat_def, symmetric]])
    (fastforce simp: If_nat_app_eq)+


(* Example of more complex datatype *)

datatype ('a, 'b) keyed_list_tree =
  KLeaf |
  KNode "(('a, 'b) keyed_list_tree)" 'a "('b list)" "(('a, 'b) keyed_list_tree)"

datatype_lift_nat keyed_list_tree
print_theorems



(* Examples of translating functions *)



fun rev_tr :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_tr acc [] = acc"
| "rev_tr acc (x # xs) = rev_tr (x # acc) xs"


function_lift_nat rev_tr
print_theorems


test rev_tr
print_theorems

lemma rev_tr_nat_synth_def:
  fixes acc :: "'a::lift_nat list" and xs :: "'a list"
  assumes "accn = Abs_nat acc"
  assumes "xsn = Abs_nat xs"
  shows "rev_tr_nat TYPE('a) accn xsn
    = case_list_nat accn (\<lambda>x3a. rev_tr_nat TYPE('a) (Cons_nat x3a accn)) xsn"
  apply(rule HOL.trans[OF _ rev_tr_nat_synth[unfolded cr_nat_def, symmetric]])
    apply(use assms in \<open>simp_all add: rev_tr_nat_app_eq\<close>)
  done


thm rev_tr_nat_synth_def[unfolded case_list_nat_def]


fun swap :: "'a \<times> 'b \<Rightarrow> 'b \<times> 'a" where
  "swap (a, b) = (b, a)"

function_lift_nat swap
print_theorems

test swap
print_theorems

lemma swap_nat_synth_def:
  fixes p :: "'a::lift_nat \<times> 'b::lift_nat"
  assumes "pn = Abs_nat p"
  shows "swap_nat TYPE('a) TYPE('b) pn
    = case_prod_nat (\<lambda>(x2a::nat) x1a::nat. Pair_nat x1a x2a) (pn::nat)"
  apply(rule HOL.trans[OF _ swap_nat_synth[unfolded cr_nat_def, symmetric]])
  using assms apply(simp add: swap_nat_app_eq; subst Rep_nat_Abs_nat_id)+
  done

thm swap_nat_synth_def[unfolded case_prod_nat_def]


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