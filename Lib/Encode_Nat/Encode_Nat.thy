\<^marker>\<open>creator "Johannes Neubrand"\<close>
\<^marker>\<open>creator "Andreas Vollert"\<close>
section\<open>Compilation from HOL to Natified HOL\<close>
theory Encode_Nat
  imports
    Main
    "HOL-Library.Nat_Bijection"
    "HOL-Library.Simps_Case_Conv"
    "HOL-Library.Tree"
    ML_Unification.Unification_Attributes
    Transport.HOL_Alignment_Functions
    Transport.Transport_Prototype
    Transport.Transport_Typedef_Base
  keywords
    "datatype_compile_nat" :: thy_decl and
    "function_compile_nat" :: thy_decl and
    "test" :: thy_decl
begin


subsection\<open>Datatypes\<close>

unbundle no_HOL_relation_syntax
unbundle lifting_syntax

class compile_nat =
  fixes natify :: "'a \<Rightarrow> nat"
  fixes denatify :: "nat \<Rightarrow> 'a"
  assumes denatify_natify_eq_self[simp]: "\<And>x. denatify (natify x) = x"
begin

sublocale compile_nat_type_def: type_definition natify denatify "range natify"
  by unfold_locales auto

lemma inj_natify: "inj natify"
  by (rule inj_on_inverseI[where ?g=denatify]) simp

definition Rel_nat :: "nat \<Rightarrow> 'a \<Rightarrow> bool" where
  "Rel_nat n x \<equiv> n = natify x"

lemma Rel_nat_iff_eq_natify: "Rel_nat n x \<longleftrightarrow> n = natify x"
  by (simp add: Rel_nat_def)

lemmas
  typedef_nat_transfer[OF compile_nat_type_def.type_definition_axioms,
    OF eq_reflection, OF ext, OF ext, OF Rel_nat_iff_eq_natify,
    transfer_rule] =
  typedef_bi_unique typedef_right_unique typedef_left_unique typedef_right_total

lemma Rel_nat_natify_self [transfer_rule]: "Rel_nat (natify x) x"
  by (simp add: Rel_nat_iff_eq_natify)

lemma Galois_eq_eq_range_natify_denatify_eq_inv_Rel_nat:
  "galois_rel.Galois (=) (=\<^bsub>range natify\<^esub>) denatify = Rel_nat\<inverse>"
  by (intro ext) (fastforce elim: galois_rel.left_GaloisE intro: galois_rel.left_GaloisI
    iff: Rel_nat_iff_eq_natify)

lemmas compile_nat_partial_equivalence_rel_equivalence =
  iffD1[OF
    transport.partial_equivalence_rel_equivalence_right_left_iff_partial_equivalence_rel_equivalence_left_right
    compile_nat_type_def.partial_equivalence_rel_equivalenceI]

end

(*register PER*)
declare compile_nat_partial_equivalence_rel_equivalence[per_intro]

(*nicer relatedness theorem output*)
declare Galois_eq_eq_range_natify_denatify_eq_inv_Rel_nat[trp_relator_rewrite, trp_uhint]
lemma eq_eq_Fun_Rel_rel_eq_eq_uhint [trp_uhint]: "P \<equiv> (=) \<Longrightarrow> P \<equiv> (=) \<Rrightarrow> (=)" by simp


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


subsection\<open>Functions\<close>

lemma rel_inv_Fun_Rel_rel_eq: "(R \<Rrightarrow> S)\<inverse> = (R\<inverse> \<Rrightarrow> S\<inverse>)"
  by (urule rel_inv_Dep_Fun_Rel_rel_eq)

declare [[ML_print_depth = 50]]
declare [[show_types = false]]
ML_file \<open>./Encode_Nat.ML\<close>

subsection \<open>Setup of Basic Datatypes and Functions\<close>

datatype_compile_nat nat
print_theorems

datatype_compile_nat list
print_theorems

datatype_compile_nat bool
print_theorems

datatype_compile_nat char
print_theorems

datatype_compile_nat prod
print_theorems

datatype_compile_nat tree
print_theorems

datatype_compile_nat num
print_theorems

datatype_compile_nat option
print_theorems


(* HOL.If has to be translated manually *)

lemma if_related_self[trp_in_dom]:
  "(compile_nat_type_def.R \<Rrightarrow> compile_nat_type_def.R \<Rrightarrow> compile_nat_type_def.R \<Rrightarrow> compile_nat_type_def.R)
    HOL.If HOL.If"
  by simp

trp_term If_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where x = "HOL.If :: bool \<Rightarrow> 'a::compile_nat \<Rightarrow> _"
  by trp_prover

lemma If_nat_lifting[transfer_rule]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat ===> Rel_nat)
    (If_nat TYPE('a::compile_nat)) (HOL.If :: bool \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a)"
  using If_nat_related' by fast

lemma If_case_def: "HOL.If c t f = (case c of True \<Rightarrow> t | False \<Rightarrow> f)"
  by simp

schematic_goal If_nat_synth:
  assumes [transfer_rule]: "(Rel_nat :: nat \<Rightarrow> bool \<Rightarrow> bool) c (denatify c)"
  assumes [transfer_rule]: "(Rel_nat :: nat \<Rightarrow> 'a \<Rightarrow> bool) t (denatify t)"
  assumes [transfer_rule]: "(Rel_nat :: nat \<Rightarrow> 'a \<Rightarrow> bool) f (denatify f)"
  shows "Rel_nat ?t ((HOL.If :: bool \<Rightarrow> 'a::compile_nat \<Rightarrow> 'a \<Rightarrow> 'a) (denatify c) (denatify t) (denatify f))"
  by (subst If_case_def, transfer_prover)

lemma If_nat_synth_def:
  fixes c :: "bool" and t :: "'a::compile_nat" and f :: "'a"
  assumes "cn = natify c"
  assumes "tn = natify t"
  assumes "fn = natify f"
  shows "If_nat TYPE('a) cn tn fn = case_bool_nat tn fn cn"
  unfolding assms
  by (rule HOL.trans[OF _ If_nat_synth[unfolded Rel_nat_def, symmetric]])
    (fastforce simp: If_nat_app_eq)+


(* Example of more complex datatype *)

datatype ('a, 'b) keyed_list_tree =
  KLeaf |
  KNode "(('a, 'b) keyed_list_tree)" 'a "('b list)" "(('a, 'b) keyed_list_tree)"

datatype_compile_nat keyed_list_tree
print_theorems



(* Examples of translating functions *)

function_compile_nat zip

fun rev_tr :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_tr acc [] = acc"
| "rev_tr acc (x # xs) = rev_tr (x # acc) xs"

function_compile_nat rev_tr
print_theorems

thm
  rev_tr_nat_synth
  rev_tr_nat_synth[unfolded Rel_nat_def, symmetric]
  rev_tr_nat_synth[unfolded Rel_nat_def, THEN sym]
  HOL.trans[OF _ rev_tr_nat_synth[unfolded Rel_nat_def, symmetric]]
  HOL.trans[OF _ rev_tr_nat_synth[unfolded Rel_nat_def, symmetric]]

test rev_tr
print_theorems
  (*
lemma rev_tr_nat_synth_def:
  fixes acc :: "'a::compile_nat list" and xs :: "'a list"
  assumes "accn = natify acc"
  assumes "xsn = natify xs"
  shows "rev_tr_nat TYPE('a) accn xsn
    = case_list_nat accn (\<lambda>x3a. rev_tr_nat TYPE('a) (Cons_nat x3a accn)) xsn"
  apply(rule HOL.trans[OF _ rev_tr_nat_synth[unfolded Rel_nat_def, symmetric]])
  using rev_tr_nat_app_eq assms by fastforce+ *)

thm rev_tr_nat_synth_def[unfolded case_list_nat_def]


fun swap :: "'a \<times> 'b \<Rightarrow> 'b \<times> 'a" where
  "swap (a, b) = (b, a)"

function_compile_nat swap
print_theorems

test swap
print_theorems

thm HOL.trans[OF _ swap_nat_synth[unfolded Rel_nat_def, symmetric]]

(* lemma swap_nat_synth_def:
  fixes x :: "'a::compile_nat \<times> 'b::compile_nat"
  assumes "n = natify x"
  shows "swap_nat TYPE('a) TYPE('b) n
    = case_prod_nat (\<lambda>(x2a::nat) x1a::nat. Pair_nat x1a x2a) (n::nat)"
  apply (rule HOL.trans[OF _ swap_nat_synth[unfolded Rel_nat_def, symmetric]])
  using swap_nat_app_eq assms by fastforce+ *)

thm swap_nat_synth_def[unfolded case_prod_nat_def]





(*

Remaining (optional?) TODOs:
  - Automatically and recursively lift not yet lifted functions during lifting
  - Make it work with single equation functions/definitions
  - make it overridable: this doesn't work in the same file atm

    function_compile_nat append

    fun append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
      "append xs [] = xs" |
      "append xs ys = rev_tr ys (rev_tr [] xs)"

    function_compile_nat append (* Error here because of duplicate definitions *)

*)




(* functions for tesiting later *)

fun reverset :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "reverset [] r = r"
| "reverset (l # ls) r = reverset ls (l # r)"


function_compile_nat reverset
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

function_compile_nat prefixes
function_compile_nat prefixest


lemma reverset_length: "length xs = length (reverset xs [])"
  by(induction xs; simp add: reverset_rev)


function foo :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "foo [] acc = acc"
| "foo (x # xs) acc = foo (reverset xs []) (x # (reverset acc []))"
  using reverset.cases by blast+
termination by(relation "measure (length o fst)"; simp add: reverset_correct)

function_compile_nat foo



fun prefixes2 :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
  "prefixes2 [] ps = reverset ([] # ps) []"
| "prefixes2 (a # b) ps = prefixes2 b ((a # b) # ps)"


function_compile_nat prefixes2

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

function_compile_nat subtreest

fun reverse_acc where
  "reverse_acc acc [] = acc"
| "reverse_acc acc (x#xs) = reverse_acc (x#acc) xs"

function_compile_nat reverse_acc

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

function_compile_nat append
thm append_nat_synth
test append
function_compile_nat rev


fun fn_test1 :: "nat \<Rightarrow> nat" where
  "fn_test1 x = (if x = 3 then 5 else 7)"


fun fn_test2 :: "('a::order_bot) \<Rightarrow> nat" where
  "fn_test2 a = 2"



fun baz :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
  "baz acc [[]] = acc"
| "baz acc [] = acc"
| "baz acc (xs#xss) = baz (append acc xs) xss"

function_compile_nat baz

fun bazz where
  "bazz acc [[]] = acc"
| "bazz acc [] = acc"
| "bazz acc ((v # va) # xss) = bazz (append acc (v # va)) xss"
| "bazz acc (xs # v # va) = bazz (append acc xs) (v # va)"

function_compile_nat bazz

fun baz2 :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
  "baz2 acc [] = acc"
| "baz2 acc (xs#xss) = baz2 (append acc xs) xss"


function_compile_nat baz2

fun test3 where
  "test3 x = (case x of True \<Rightarrow> False | False \<Rightarrow> True)"


end