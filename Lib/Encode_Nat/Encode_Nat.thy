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
    "HOL-Eisbach.Eisbach"
    "HOL-Eisbach.Eisbach_Tools"
    Test
  keywords
    "test" :: thy_decl and
    "test2" :: thy_decl and
    "datatype_nat_encode" :: thy_decl and
    "datatype_nat_decode" :: thy_decl and
    "datatype_nat_wellbehaved" :: thy_goal and
    "function_nat_rewrite" :: thy_decl and
    "function_nat_rewrite_auto" :: thy_decl and
    "function_nat_rewrite_correctness" :: thy_goal
begin

declare [[ML_print_depth = 50]]

datatype ('a, 'b) keyed_list_tree =
  KLeaf |
  KNode "(('a, 'b) keyed_list_tree)" 'a "('b list)" "(('a, 'b) keyed_list_tree)"

type_synonym pair_repr = nat

instantiation char :: order_bot
begin

definition bot_char :: "char" where
  "bot_char = CHR 0x00"

instance
proof(standard, goal_cases)
  case (1 a)
  then show ?case
    unfolding bot_char_def less_eq_char_def by (cases a, fastforce)
qed
end

instantiation tree :: (order) order_bot
begin

fun less_eq_tree :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> bool" where
  "less_eq_tree \<langle>\<rangle> _ \<longleftrightarrow> True"
| "less_eq_tree _ \<langle>\<rangle> \<longleftrightarrow> False"
| "less_eq_tree \<langle>l1, a1, r1\<rangle> \<langle>l2, a2, r2\<rangle> \<longleftrightarrow>
    (l1 \<le> l2 \<and> r1 \<le> r2 \<and> a1 \<le> a2)"

definition less_tree :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> bool" where
  "less_tree t1 t2 = (t1 \<le> t2 \<and> \<not> t2 \<le> t1)"

definition bot_tree :: "'a tree" where
  "bot_tree = \<langle>\<rangle>"

instance
proof(standard, goal_cases)
  case 1 show ?case using less_tree_def by simp
next
  case (2 t) show ?case by(induction t; simp)
next
  case (3 t1 t2 t3) thus ?case
    by(induction t1 t3 arbitrary: t2 rule: less_eq_tree.induct; force elim: less_eq_tree.elims)
next
  case (4 t1 t2) thus ?case
    by(induction t1 t2 rule: less_eq_tree.induct; force elim: less_eq_tree.elims)
next
  case (5 a)
  then show ?case
    unfolding bot_tree_def less_eq_tree.simps by simp
qed
end

instantiation keyed_list_tree :: (order, order) order_bot
begin

fun less_eq_keyed_list_tree :: "('a, 'b) keyed_list_tree \<Rightarrow> ('a, 'b) keyed_list_tree \<Rightarrow> bool" where
  "less_eq_keyed_list_tree KLeaf _ \<longleftrightarrow> True"
| "less_eq_keyed_list_tree _ KLeaf \<longleftrightarrow> False"
| "less_eq_keyed_list_tree (KNode l1 a1 bs1 r1) (KNode l2 a2 bs2 r2) \<longleftrightarrow>
    (l1 \<le> l2 \<and> r1 \<le> r2 \<and> a1 \<le> a2 \<and> bs1 \<le> bs2)"

definition less_keyed_list_tree :: "('a, 'b) keyed_list_tree \<Rightarrow> ('a, 'b) keyed_list_tree \<Rightarrow> bool"
  where
    "less_keyed_list_tree t1 t2 = (t1 \<le> t2 \<and> \<not> t2 \<le> t1)"

definition bot_keyed_list_tree :: "('a, 'b) keyed_list_tree" where
  "bot_keyed_list_tree = KLeaf"

instance
proof(standard, goal_cases)
  case 1 show ?case using less_keyed_list_tree_def by simp
next
  case (2 t) show ?case by(induction t; simp)
next
  case (3 t1 t2 t3) thus ?case
    by(induction t1 t3 arbitrary: t2 rule: less_eq_keyed_list_tree.induct;
        force elim: less_eq_keyed_list_tree.elims)
next
  case (4 t1 t2) thus ?case
    by(induction t1 t2 rule: less_eq_keyed_list_tree.induct;
        force elim: less_eq_keyed_list_tree.elims)
next
  case (5 a)
  then show ?case
    unfolding bot_keyed_list_tree_def less_eq_keyed_list_tree.simps by simp
qed
end


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

ML_file \<open>./Encode_Nat.ML\<close>


lemma prod_decode_less:
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

corollary snd_prod_decode_lt_intro:
  assumes "fstP v \<noteq> 0"
  shows "snd (prod_decode v) < v"
  by (metis assms fstP.simps gr0I prod.collapse snd_prod_encode_lt prod_decode_inverse)

datatype_nat_encode nat


lemma enc_nat_bot: "enc_nat bot = bot"
  by (simp add: enc_nat.simps bot_nat_def prod_encode_0)

datatype_nat_encode list
print_theorems
thm enc_list.simps

lemma "Nil_nat = enc_list enc_'a []"
  by (simp add: enc_list.simps Nil_nat_def)

lemma enc_list_bot: "enc_list enc_'a bot = bot"
  by(simp add: enc_list.simps prod_encode_0 bot_list_def bot_nat_def Nil_nat_def)

datatype_nat_encode bool

lemma enc_bool_bot: "enc_bool bot = bot"
  by(simp add: enc_bool.simps prod_encode_0 bot_nat_def False_nat_def)

datatype_nat_encode char

lemma enc_char_bot: "enc_char bot = bot"
  by(simp add: enc_char.simps enc_bool.simps prod_encode_0 bot_nat_def bot_char_def Char_nat_def
      False_nat_def)

datatype_nat_encode "('a, 'b) prod"

lemma enc_prod_bot:
  assumes "enc_'a bot = bot"
    and "enc_'b bot = bot"
  shows "enc_prod enc_'a enc_'b bot = bot"
  by (simp add: enc_prod.simps prod_encode_0 bot_nat_def bot_prod_def assms Pair_nat_def)

datatype_nat_encode "'a tree"

lemma enc_tree_bot: "enc_tree enc_'a bot = bot"
  by (simp add: enc_tree.simps prod_encode_0 bot_nat_def bot_tree_def Leaf_nat_def)

datatype_nat_encode "('a, 'b) keyed_list_tree"

lemma enc_keyed_list_tree_bot: "enc_keyed_list_tree enc_'a enc_'b bot = bot"
  by (simp add: enc_keyed_list_tree.simps prod_encode_0 bot_nat_def bot_keyed_list_tree_def
      KLeaf_nat_def)


(* TODO: Do we need similar lemmas for other data types? *)
lemma enc_List_list_cong[fundef_cong]:
  assumes "xs = ys"
    and "\<And>x. x \<in> set ys \<Longrightarrow> enc\<^sub>a x = enc\<^sub>b x"
  shows "enc_list enc\<^sub>a xs = enc_list enc\<^sub>b ys"
  using assms by (induction xs arbitrary: ys; auto simp add: enc_list.simps)


method decode_termination for t =
  relation t, auto;
  (auto intro!: prod_decode_less snd_prod_decode_lt_intro)?

declare prod_decode_less[termination_simp]
declare snd_prod_decode_lt_intro[termination_simp]



datatype_nat_decode nat



datatype_nat_decode list
print_theorems

(* TODO: Automate that *)
lemmas dec_list_prod_encode_simp[simp] = dec_list.simps[of _ "prod_encode _"]

thm dec_list.simps

datatype_nat_decode bool
lemmas dec_bool_prod_encode_simp[simp] = dec_bool.simps[of "prod_encode _"]

datatype_nat_decode char
lemmas dec_char_prod_encode_simp[simp] = dec_char.simps[of "prod_encode _"]

datatype_nat_decode prod
lemmas dec_prod_prod_encode_simp[simp] = dec_prod.simps[of _ _ "prod_encode _"]

lemma dec_prod_bot:
  assumes "dec_'a bot = bot" and "dec_'b bot = bot"
  shows "dec_prod dec_'a dec_'b bot = bot"
  using assms
  by(simp add: dec_prod.simps prod_decode_def bot_prod_def prod_decode_aux.simps bot_nat_def)

datatype_nat_decode tree
lemmas dec_tree_prod_encode_simp[simp] = dec_tree.simps[of _ "prod_encode _"]

datatype_nat_decode keyed_list_tree
lemmas dec_keyed_list_tree_prod_encode_simp[simp]
  = dec_keyed_list_tree.simps[of _ _ "prod_encode _"]


inductive_set subpairings :: "pair_repr \<Rightarrow> pair_repr set" for x where
  "x \<in> subpairings x"
| "t \<in> subpairings x \<Longrightarrow> fstP t \<in> subpairings x"
| "t \<in> subpairings x \<Longrightarrow> sndP t \<in> subpairings x"

lemma
  shows subpairings_fstP_imp: "a \<in> subpairings (fstP x) \<Longrightarrow> a \<in> subpairings x"
    and subpairings_sndP_imp: "a \<in> subpairings (sndP x) \<Longrightarrow> a \<in> subpairings x"
   apply(simp , all \<open>induction rule: subpairings.induct\<close>)
  using subpairings.intros by simp+

lemma dec_List_list_cong[fundef_cong]:
  assumes "x = y"
    and "\<And>t. t \<in> subpairings y \<Longrightarrow> dec\<^sub>a t = dec\<^sub>b t"
  shows "dec_list dec\<^sub>a x = dec_list dec\<^sub>b y"
  unfolding assms(1) using assms(2)
  by (induction dec\<^sub>a y rule: dec_list.induct;
      metis subpairings_sndP_imp dec_list.simps subpairings.intros(1) subpairings.intros(2))

datatype_nat_wellbehaved nat
  by(induction; simp add: enc_nat.simps dec_nat.simps)

datatype_nat_wellbehaved bool
  by(intro ext, simp add: dec_bool.simps enc_bool.simps True_nat_def False_nat_def split:bool.split)

datatype_nat_wellbehaved list
  apply(intro ext)
  subgoal for x
    using assms[THEN pointfree_idE]
    by(induction x rule: list.induct; simp add: enc_list.simps Nil_nat_def Cons_nat_def)
  done

datatype_nat_wellbehaved char
  using encoding_bool_wellbehaved[THEN pointfree_idE]
  by(intro ext, simp add: dec_char.simps enc_char.simps Char_nat_def split: char.split)

datatype_nat_wellbehaved prod
  apply(intro ext)
  subgoal for x
    using assms[THEN pointfree_idE]
    by(induction x rule: prod.induct; simp add: enc_prod.simps Pair_nat_def)
  done

datatype_nat_wellbehaved tree
  apply(intro ext)
  subgoal for x
    using assms[THEN pointfree_idE]
    by(induction x rule: tree.induct; simp add: enc_tree.simps Leaf_nat_def Node_nat_def)
  done

datatype_nat_wellbehaved keyed_list_tree
  apply(intro ext)
  subgoal for x
    apply(induction x rule: keyed_list_tree.induct)
    using encoding_list_wellbehaved[OF assms(2), THEN pointfree_idE] assms(1)[THEN pointfree_idE]
    by (simp add: enc_keyed_list_tree.simps KLeaf_nat_def KNode_nat_def)+
  done


fun reverset :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "reverset [] r = r"
| "reverset (l # ls) r = reverset ls (l # r)"

lemma reverset_rev: "reverset l r = rev l @ r"
  by (induction l r rule: reverset.induct; simp)

lemma reverset_correct: "reverset l [] = rev l"
  by (simp add: reverset_rev)

(* TODO: put into other commands *)
test2 list
thm Cons_nat_equiv
test2 bool

test2 char

test2 prod

test2 tree

test2 keyed_list_tree

lemma dec_list_bot: "dec_list dec_'a bot = bot"
  by(simp add: dec_list.simps prod_decode_def prod_decode_aux.simps bot_list_def)

lemma dec_tree_bot: "dec_tree dec_'a bot = bot"
  by(simp add: dec_tree.simps prod_decode_def prod_decode_aux.simps bot_tree_def)

term "case_list acc (\<lambda>x xs. x # acc) xs"

definition case_list_nat :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "case_list_nat f g xs =
  (if fstP xs = atomic 0 then f else g (fstP (sndP xs)) (sndP (sndP xs)))"

term "case_list"

lemma "(case dec_list dec_'a xs of [] => f | a # as => g a as)
  = (if fstP xs = atomic 0 then f else g (dec_'a (fstP (sndP xs))) (dec_list dec_'a (sndP (sndP xs))))"
  by (simp add: dec_list.simps)

term "foo [] = f1"
term "foo (x # xs) = f1 x xs"

ML \<open>
  hd [1, 2, 3]
\<close>

term "case_keyed_list_tree"

test keyed_list_tree

test list
test bool
test char
test prod
test tree

lemma
  fixes f::"'a \<Rightarrow> 'b"
  assumes "dec_'a \<circ> enc_'a = id"
    and "dec_'b \<circ> enc_'b = id"
    and "f_nat = (\<lambda>x. enc_'b (f (dec_'a x)))"
  shows "f_nat (enc_'a x) = enc_'b (f x)"
  using assms
  by (simp add: pointfree_idE)

lemma foo:
  fixes enc_'a :: "'a::order_bot \<Rightarrow> nat"
    and dec_'a :: "nat \<Rightarrow> 'a"
    and enc_'b :: "'b::order_bot \<Rightarrow> nat"
    and dec_'b :: "nat \<Rightarrow> 'b"
  assumes "\<And>x xs. g_nat (enc_'b x) (enc_list enc_'b xs) = enc_'a (g x xs)"
  shows "enc_'a (case_list f (\<lambda>x xs. g x xs) xs) =
          case_list_nat (enc_'a f) (\<lambda>x xs. g_nat x xs) (enc_list enc_'b xs)"
  unfolding case_list_nat_def using assms
  by(induction xs; simp add: enc_list.simps Nil_nat_def Cons_nat_def)+

lemma "case_list f (\<lambda>x xs. g x xs) xs =
      (if xs = [] then f else g (hd xs) (tl xs))"
  oops
function_nat_rewrite_auto reverset
print_theorems

thm List.list.case_eq_if

thm reverset_nat_equiv encoding_list_wellbehaved[THEN pointfree_idE]

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

function_nat_rewrite_auto prefixest


lemma reverset_length: "length xs = length (reverset xs [])"
  by(induction xs; simp add: reverset_rev)


function foo :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "foo [] acc = acc"
| "foo (x # xs) acc = foo (reverset xs []) (x # (reverset acc []))"
  using reverset.cases by blast+
termination by(relation "measure (length o fst)"; simp add: reverset_correct)

function_nat_rewrite_auto foo
print_theorems


fun prefixes2 :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
  "prefixes2 [] ps = reverset ([] # ps) []"
| "prefixes2 (a # b) ps = prefixes2 b ((a # b) # ps)"

function_nat_rewrite_auto prefixes2


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

function_nat_rewrite_auto subtreest
print_theorems


fun reverse_acc where
  "reverse_acc acc [] = acc"
| "reverse_acc acc (x#xs) = reverse_acc (x#acc) xs"



function_nat_rewrite_auto reverse_acc
thm reverse_acc_nat.simps

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

function_nat_rewrite_auto reverse


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


function_nat_rewrite_auto append

fun plus where
  "plus 0 n = n"
| "plus (Suc m) n = plus m (Suc n)"

lemma plus_equiv: "plus a b = a + b"
  by(induction a arbitrary: b; simp)

function_nat_rewrite_auto plus


datatype_nat_encode num


datatype_nat_decode num
lemmas dec_num_prod_encode_simp[simp] = dec_num.simps[of "prod_encode _"]

datatype_nat_wellbehaved num
  apply(intro ext)
  subgoal for x
    by(induction x rule: num.induct; simp add: enc_num.simps One_nat_def Bit1_nat_def Bit0_nat_def)
  done

fun fn_test1 :: "nat \<Rightarrow> nat" where
  "fn_test1 x = (if x = 3 then 5 else 7)"

function_nat_rewrite_auto fn_test1


fun fn_test2 :: "('a::order_bot) \<Rightarrow> nat" where
  "fn_test2 a = 2"

function_nat_rewrite_auto fn_test2




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


function_nat_rewrite_auto baz2

(* function_nat_rewrite_auto bazz *)


(* can't handle case expressions *)
fun test3 where
  "test3 x = (case x of True \<Rightarrow> False | False \<Rightarrow> True)"

(* function_nat_rewrite_auto test3 *)

(*

TODO: case_list xs f (\<lambda> a as. g a as) = if ... then f else g (fst (snd (arg1)) ..

*)

end