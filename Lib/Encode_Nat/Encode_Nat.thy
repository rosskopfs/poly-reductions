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
    "test" :: thy_goal and
    "test2" :: thy_decl and
    "datatype_nat_encode" :: thy_decl and
    "datatype_nat_decode" :: thy_goal and
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
  by (simp add: bot_nat_def prod_encode_0)



datatype_nat_encode list
declare enc_list.simps [simp del]

thm enc_list.simps Cons_nat_def


lemma "Nil_nat = enc_list enc_'a []"
  by (simp add: enc_list.simps Nil_nat_def)

lemma enc_list_bot: "enc_list enc_'a bot = bot"
  by(simp add: enc_list.simps prod_encode_0 bot_list_def bot_nat_def Nil_nat_def)

datatype_nat_encode bool
declare enc_bool.simps [simp del]

lemma enc_bool_bot: "enc_bool bot = bot"
  by(simp add: enc_bool.simps prod_encode_0 bot_nat_def False_nat_def)

datatype_nat_encode char
declare enc_char.simps [simp del]

lemma enc_char_bot: "enc_char bot = bot"
  by(simp add: enc_char.simps enc_bool.simps prod_encode_0 bot_nat_def bot_char_def Char_nat_def
      False_nat_def)

datatype_nat_encode "('a, 'b) prod"
declare enc_prod.simps [simp del]

lemma enc_prod_bot:
  assumes "enc_'a bot = bot"
    and "enc_'b bot = bot"
  shows "enc_prod enc_'a enc_'b bot = bot"
  by (simp add: enc_prod.simps prod_encode_0 bot_nat_def bot_prod_def assms Pair_nat_def)

datatype_nat_encode "'a tree"
declare enc_tree.simps [simp del]

lemma enc_tree_bot: "enc_tree enc_'a bot = bot"
  by (simp add: enc_tree.simps prod_encode_0 bot_nat_def bot_tree_def Leaf_nat_def)

datatype_nat_encode "('a, 'b) keyed_list_tree"
declare enc_keyed_list_tree.simps [simp del]

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


datatype_nat_decode nat
termination by (decode_termination "measure id")

datatype_nat_decode list
termination by (decode_termination "measure snd")
declare dec_list.simps[simp del]
  (* Why? *)
lemmas dec_list_prod_encode_simp[simp] = dec_list.simps[of _ "prod_encode _"]

thm dec_list.simps

datatype_nat_decode bool
termination by (decode_termination "measure id")
declare dec_bool.simps[simp del]
  (* Why? *)
lemmas dec_bool_prod_encode_simp[simp] = dec_bool.simps[of "prod_encode _"]

datatype_nat_decode char
termination by (decode_termination "measure id")
declare dec_char.simps[simp del]
  (* Why? *)
lemmas dec_char_prod_encode_simp[simp] = dec_char.simps[of "prod_encode _"]

datatype_nat_decode prod
termination by (decode_termination "measure (snd o snd)")
declare dec_prod.simps[simp del]
  (* Why? *)
lemmas dec_prod_prod_encode_simp[simp] = dec_prod.simps[of _ _ "prod_encode _"]

lemma dec_prod_bot:
  assumes "dec_'a bot = bot" and "dec_'b bot = bot"
  shows "dec_prod dec_'a dec_'b bot = bot"
  using assms
  by(simp add: dec_prod.simps prod_decode_def bot_prod_def prod_decode_aux.simps bot_nat_def)

datatype_nat_decode tree
termination by (decode_termination "measure snd")
declare dec_tree.simps[simp del]
  (* Why? *)
lemmas dec_tree_prod_encode_simp[simp] = dec_tree.simps[of _ "prod_encode _"]

datatype_nat_decode keyed_list_tree
termination by (decode_termination "measure (snd o snd)")
declare dec_keyed_list_tree.simps[simp del]
  (* Why? *)
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

(* TODO: Do we need similar lemmas for other data types? *)
lemma dec_List_list_cong[fundef_cong]:
  assumes "x = y"
    and "\<And>t. t \<in> subpairings y \<Longrightarrow> dec\<^sub>a t = dec\<^sub>b t"
  shows "dec_list dec\<^sub>a x = dec_list dec\<^sub>b y"
  unfolding assms(1) using assms(2)
  by (induction dec\<^sub>a y rule: dec_list.induct;
      metis subpairings_sndP_imp dec_list.simps subpairings.intros(1) subpairings.intros(2))

(* No longer working. TODO? *)
method wellbehavedness_case
  uses assms enc_simps uses_wellbehaved =
  subst enc_simps,
  insert assms,
  insert uses_wellbehaved,
  auto

(* No longer working. TODO? *)
method wellbehavedness
  uses induct_rule assms enc_simps uses_wellbehaved =
  (intro ext, insert TrueI, match premises in True \<Rightarrow> \<open>induction rule: induct_rule\<close>);
  (solves \<open>wellbehavedness_case
            assms: assms enc_simps: enc_simps uses_wellbehaved: uses_wellbehaved\<close>)?


datatype_nat_wellbehaved nat
  by(induction; simp)

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

method natfn_correctness
  methods induct_rule
  uses assms simps_nat dels enc_simps args_wellbehaved =
  \<comment> \<open>Add wellbehavedness assumptions to get induction hypotheses\<close>
  print_fact assms, print_fact args_wellbehaved, insert assms,
  \<comment> \<open>Computation induction over the original function\<close>
  induct_rule;
  \<comment> \<open>Unfold exactly one level of the natfn we're looking at—corresponding to the inductive step\<close>
  subst simps_nat;
  insert args_wellbehaved; simp del: dels add: enc_simps; meson?



fun reverset :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "reverset [] r = r"
| "reverset (l # ls) r = reverset ls (l # r)"

lemma reverset_rev: "reverset l r = rev l @ r"
  by (induction l r rule: reverset.induct; simp)

lemma reverset_correct: "reverset l [] = rev l"
  by (simp add: reverset_rev)

ML \<open>
  Proof_Context.read_const {proper = false, strict = false} @{context} "Cons"
\<close>

test2 list

test2 bool

test2 char

test2 prod

test2 tree

test2 keyed_list_tree

lemma dec_list_bot: "dec_list dec_'a bot = bot"
  by(simp add: dec_list.simps prod_decode_def prod_decode_aux.simps bot_list_def)

function_nat_rewrite_auto reverset
thm reverset_nat_equiv



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

ML \<open>
fun can_resolve bottom_rl rls =
  (case Seq.chop 2 (Drule.multi_resolve NONE rls bottom_rl) of
    ([_], _) => true
  | _ => false);

@{typ "'a \<Rightarrow> 'a"} |> dest_Type
\<close>

thm encoding_list_wellbehaved dec_list_bot

function_nat_rewrite_auto prefixest

function_nat_rewrite prefixest
function_nat_rewrite_correctness prefixest
proof(induction arg\<^sub>1 arg\<^sub>2 rule: prefixest.induct)
  case (1 v vs ps)
  have h1: "(fstP (enc_list enc_'a (v # vs)) = atomic 1) = True"
    by (simp add: enc_list.simps Cons_nat_def)
  have h2: "sndP (sndP (enc_list enc_'a (v # vs))) = enc_list enc_'a vs"
    by (simp add: enc_list.simps Cons_nat_def)
  have h3: "fstP (sndP (enc_list enc_'a (v # vs))) = enc_'a v"
    by (simp add: enc_list.simps Cons_nat_def)
  show ?case
    apply(subst prefixest.simps; subst prefixest_nat.simps)
    apply(subst h1)
    apply(subst if_True)
    apply(simp only: h2 h3 Let_def)
    apply(subst Cons_nat_equiv[where arg\<^sub>1=v and arg\<^sub>2=vs, OF assms])
    using Cons_nat_equiv[where arg\<^sub>1="v # vs" and arg\<^sub>2=ps]
           dec_list_bot
    apply(subst Cons_nat_equiv[where arg\<^sub>1="v # vs" and arg\<^sub>2=ps, OF encoding_list_wellbehaved,
          OF assms(1), OF dec_list_bot])
    using 1 apply(assumption)
    done
next
  case (2 ps)
  have h1: "(fstP (enc_list enc_'a []) = atomic 1) = False"
    by (simp add: enc_list.simps Nil_nat_def)
  show ?case
    apply(subst prefixest.simps; subst prefixest_nat.simps)
    apply(subst h1)
    apply(subst if_False)
    apply(simp only: Let_def)
    apply(subst Nil_nat_equiv[OF assms])
    apply(subst Cons_nat_equiv[where arg\<^sub>1="[]" and arg\<^sub>2=ps, OF encoding_list_wellbehaved, OF assms(1), OF dec_list_bot])
    using pointfree_idE[OF encoding_list_wellbehaved, OF encoding_list_wellbehaved, OF assms(1)]
    apply simp
    done
qed

  apply(induction arg\<^sub>1 arg\<^sub>2 rule: prefixest.induct; subst prefixest.simps; subst prefixest_nat.simps)
  subgoal for v vs ps
    using
      pointfree_idE[OF encoding_list_wellbehaved, OF assms(1)]
      Nil_nat_equiv[OF encoding_list_wellbehaved, OF assms(1), OF dec_list_bot]
      Cons_nat_equiv[where arg\<^sub>1=v and arg\<^sub>2=vs, OF assms]
      Cons_nat_equiv[where arg\<^sub>1="v # vs" and arg\<^sub>2=ps, OF encoding_list_wellbehaved, OF assms(1), OF dec_list_bot]
      Cons_nat_equiv[where arg\<^sub>1="[]" and arg\<^sub>2=ps, OF encoding_list_wellbehaved, OF assms(1), OF dec_list_bot]

    apply(auto simp add: enc_list.simps Nil_nat_def Cons_nat_def)
    sorry
  subgoal
    sorry
  done

thm prefixest_nat_equiv

lemma reverset_length: "length xs = length (reverset xs [])"
  by(induction xs; simp add: reverset_rev)

function foo :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "foo [] acc = acc"
| "foo (x # xs) acc = foo (reverset xs []) (x # (reverset acc []))"
     apply auto
  using prefixes.cases by blast
termination sorry

thm enc_list.simps

lemma Nil_nat: "enc_list enc_'a [] = pair (atomic 0) (atomic 0)"
  by(simp add: enc_list.simps)

lemma Cons_nat: "enc_list enc_'a (x # xs) =
  pair (atomic 1) (pair (enc_'a x) (enc_list enc_'a xs))"
  by(simp add: enc_list.simps)

function_nat_rewrite_auto foo
function_nat_rewrite foo
function_nat_rewrite_correctness foo
proof(induction arg\<^sub>1 arg\<^sub>2 rule: foo.induct)
  case (1 acc)
  then show ?case
    apply(subst foo.simps; subst foo_nat.simps)
    by(simp add: Cons_nat Nil_nat)
next
  case (2 x xs acc)
  then show ?case
    apply(subst foo.simps; subst foo_nat.simps)
    using reverset_nat_equiv[OF assms, of xs "[]"]
    reverset_nat_equiv[OF assms, of acc "[]"]
    reverset_nat_equiv
    by (simp add: Cons_nat Nil_nat)
qed

fun prefixes2 where
  "prefixes2 [] ps = reverset ([] # ps) []"
| "prefixes2 (a # b) ps = prefixes2 b ((a # b) # ps)"

thm reverset_nat_equiv reverset.simps




ML \<open>
 Envir.subst_type
\<close>




function_nat_rewrite_auto prefixes2
function_nat_rewrite prefixes2

lemma hh: "(pair (atomic 0) (atomic 0)) = enc_list enc_'a []" by (simp add: enc_list.simps)

function_nat_rewrite_correctness prefixes2
proof(induction arg\<^sub>1 arg\<^sub>2 rule: prefixes2.induct)
  case (1 ps)
  have h1: "(fstP (enc_list enc_'a []) = atomic 0) = True" by (simp add: enc_list.simps)
  have h2: "pair (atomic 1) (pair (pair (atomic 0) (atomic 0)) (enc_list (enc_list enc_'a) ps)) =
            enc_list (enc_list enc_'a) ([] # ps)" by (simp add: enc_list.simps)
  have h3: "(pair (atomic 0) (atomic 0)) = enc_list (enc_list enc_'a) []" by (simp add: enc_list.simps)
  show ?case
    apply(subst prefixes2_nat.simps; subst prefixes2.simps)
    using reverset_nat_equiv[
        where arg\<^sub>1="[] # ps" and arg\<^sub>2="[]"] encoding_list_wellbehaved assms dec_list_bot
    apply(force simp add: Cons_nat Nil_nat)
    using reverset_nat_equiv[
        where arg\<^sub>1="[] # ps" and arg\<^sub>2="[]",
        OF encoding_list_wellbehaved,
        OF assms(1),
        OF dec_list_bot]
    by(simp add: Cons_nat Nil_nat)
next
  case (2 a b ps)
  then show ?case
    apply(subst prefixes2_nat.simps; subst prefixes2.simps)
    using assms
    by(simp add: Cons_nat Nil_nat)
qed

  using assms
  apply(induction arg\<^sub>1 arg\<^sub>2 rule: prefixes2.induct; subst prefixes2_nat.simps)
  subgoal for ps
    using reverset_nat_equiv[
        where arg\<^sub>1="[] # ps" and arg\<^sub>2="[]",
        OF encoding_list_wellbehaved,
        OF assms(1),
        OF dec_list_bot]
     reverset_nat_equiv[
        where arg\<^sub>1="[] # ps" and arg\<^sub>2="[]"] encoding_list_wellbehaved
    by(simp add: enc_list.simps)
  by(simp add: enc_list.simps Let_def)

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
                <*mlex*> {}")
      (simp_all add: wf_mlex mlex_less)

lemma subtrees_subtreest:
  "mset (subtrees t @ concat (map subtrees ts) @ stk) = mset (subtreest t ts stk)"
  by (induction t ts stk rule: subtreest.induct; simp)

lemma subtreest_correct: "mset (subtrees t) = mset (subtreest t [] [])"
  using subtrees_subtreest[of t "[]" "[]"] by simp

function_nat_rewrite subtreest

function_nat_rewrite_correctness subtreest
  by (natfn_correctness \<open>induct arg\<^sub>1 arg\<^sub>2 arg\<^sub>3 rule: subtreest.induct\<close>
      assms: assms
      simps_nat: subtreest_nat.simps
      enc_simps: enc_list.simps enc_tree.simps
      args_wellbehaved: encoding_tree_wellbehaved[OF assms(1), THEN pointfree_idE]
      encoding_list_wellbehaved[OF encoding_tree_wellbehaved, OF assms(1), THEN pointfree_idE])


fun plus where
  "plus 0 n = n"
| "plus (Suc m) n = plus m (Suc n)"

lemma plus_equiv: "plus a b = a + b"
  by(induction a arbitrary: b; simp)

(* function_nat_rewrite plus
function_nat_rewrite_correctness plus
  using encoding_nat_wellbehaved[THEN pointfree_idE]
  by(induction arg\<^sub>1 arg\<^sub>2 rule: plus.induct;
      subst plus_nat.simps, simp add: enc_nat.simps plus_nat.simps, presburger?) *)

fun bar :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bar a b = a + b"


ML \<open>

@{term "n - 1"}

\<close>





(* TODOs/Things not wroking/Things to investigate *)


fun fn_test1 :: "nat \<Rightarrow> nat" where
  "fn_test1 x = (if x = 3 then 5 else 7)"

fun fn_test2 :: "('a::order_bot) \<Rightarrow> nat" where
  "fn_test2 a = 2"

(* function_nat_rewrite fn_test1 *)
(* function_nat_rewrite fn_test2 *)


fun reverse_acc where
  "reverse_acc acc [] = acc"
| "reverse_acc acc (x#xs) = reverse_acc (x#acc) xs"


function_nat_rewrite reverse_acc
function_nat_rewrite_correctness reverse_acc
  by (natfn_correctness \<open>induct arg\<^sub>1 arg\<^sub>2 rule: reverse_acc.induct\<close>
      assms: assms
      simps_nat: reverse_acc_nat.simps
      enc_simps: enc_list.simps
      args_wellbehaved: encoding_list_wellbehaved[OF assms(1), THEN pointfree_idE])

lemma reverse_acc_nat_equiv2:
  assumes "dec_'a \<circ> enc_'a = id"
  shows "reverse_acc_nat (enc_list enc_'a acc) (enc_list enc_'a xs)
           = enc_list enc_'a (reverse_acc acc xs)"
  by (induction acc xs rule: reverse_acc.induct;
      subst reverse_acc.simps;
      simp add: reverse_acc_nat.simps enc_list.simps)

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

function_nat_rewrite reverse
function_nat_rewrite_correctness reverse
  using reverse_acc_nat_equiv[OF assms, of "[]"]
  by (subst reverse.simps, simp add: reverse_nat.simps enc_list.simps)


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


lemma reverse_nat_equiv2:
  assumes "dec_'a \<circ> enc_'a = id"
  shows "reverse_nat (enc_list enc_'a xs) = enc_list enc_'a (reverse xs)"
  apply(induction xs rule: reverse.induct; subst reverse.simps)
  using reverse_acc_nat_equiv2[OF assms, of "[]"]
  by(simp add: reverse_nat.simps enc_list.simps)

function_nat_rewrite append
function_nat_rewrite_correctness append
  apply(induction arg\<^sub>1 arg\<^sub>2 rule: append.induct)
  apply(all \<open>subst append.simps\<close>)
  apply(subst append_nat.simps)
  using reverse_nat_equiv2[OF assms(1)] reverse_acc_nat_equiv[OF assms]
  by(simp)

lemma append_nat_equiv2:
  assumes "dec_'a \<circ> enc_'a = id"
  shows "append_nat (enc_list enc_'a xs) (enc_list enc_'a ys) = enc_list enc_'a (append xs ys)"
  apply(induction xs ys rule: append.induct)
  apply(subst append.simps)
  using reverse_acc_nat_equiv2[OF assms] reverse_nat_equiv2[OF assms]
  using append_nat.simps by simp

lemma append_nat_equiv3:
  assumes "dec_'a \<circ> enc_'a = id"
    and "f_nat (enc_list enc_'a ys) = enc_list enc_'a (f ys)"
  shows "append_nat (enc_list enc_'a xs) (f_nat (enc_list enc_'a ys))
          = enc_list enc_'a (append xs (f ys))"
  apply(induction xs "f ys" rule: append.induct)
  apply(subst append.simps)
  using reverse_acc_nat_equiv2[OF assms(1)] reverse_nat_equiv2[OF assms(1)] assms(2)
  by (simp add: append_nat.simps)

lemma append_nat_equiv4:
  assumes "dec_'a \<circ> enc_'a = id"
    and "f_nat (enc_list enc_'a xs) = enc_list enc_'a (f xs)"
  shows "append_nat (f_nat (enc_list enc_'a xs)) (enc_list enc_'a ys)
          = enc_list enc_'a (append (f xs) ys)"
  apply(induction "f xs" ys rule: append.induct)
  apply(subst append.simps)
  using reverse_acc_nat_equiv2[OF assms(1)] reverse_nat_equiv2[OF assms(1)] assms(2)
  by (simp add: append_nat.simps)

lemma append_nat_equiv5:
  assumes "dec_'a \<circ> enc_'a = id"
    and "f_nat (enc_list enc_'a xs) = enc_list enc_'a (f xs)"
    and "g_nat (enc_list enc_'a ys) = enc_list enc_'a (g ys)"
  shows "append_nat (f_nat (enc_list enc_'a xs)) (g_nat (enc_list enc_'a ys))
          = enc_list enc_'a (append (f xs) (g ys))"
  apply(induction "f xs" "g ys" rule: append.induct)
  apply(subst append.simps)
  using reverse_acc_nat_equiv2[OF assms(1)] reverse_nat_equiv2[OF assms(1)] assms
  by (simp add: append_nat.simps)


fun baz :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
  "baz acc [[]] = acc"
| "baz acc [] = acc"
| "baz acc (xs#xss) = baz (append acc xs) xss"

fun baz2 :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
  "baz2 acc [] = acc"
| "baz2 acc (xs#xss) = baz2 (append acc xs) xss"


function_nat_rewrite baz
thm baz_nat.simps

lemma prod_decode_0_snd: "snd (prod_decode 0) = 0" by eval
lemma prod_decode_0_fst: "fst (prod_decode 0) = 0" by eval


lemma 11:"prod_encode (0, 0) = enc_list enc_'a []"
  by(simp add: enc_list.simps)


function_nat_rewrite baz2

lemma baz2_nat_equiv2:
  assumes "dec_'a \<circ> enc_'a = id"
  shows "baz2_nat (enc_list enc_'a acc) (enc_list (enc_list enc_'a) xss) = enc_list enc_'a (baz2 acc xss)"
  apply(induction acc xss rule: baz2.induct)
   apply(all \<open>subst baz2.simps\<close>)
   apply (metis "11" atomic.simps baz2_nat.simps fstP.simps fst_conv prod_encode_inverse)
  apply(subst baz2_nat.simps)
  using append_nat_equiv2[OF assms]
  by (metis (mono_tags, lifting) atomic.simps enc_list.simps fstP.simps fst_conv list.simps(5) pair.simps prod_encode_inverse sndP.simps snd_conv zero_neq_one)


function_nat_rewrite_correctness baz2
  apply(induction arg\<^sub>1 arg\<^sub>2 rule: baz2.induct)
   apply(all \<open>subst baz2.simps\<close>)
  using encoding_list_wellbehaved[OF assms(1), THEN pointfree_idE]
   apply(simp add: baz2_nat.simps enc_list.simps)
  using encoding_list_wellbehaved[OF assms(1), THEN pointfree_idE]
    baz2_nat_equiv2[OF assms(1)]
  by force

lemma a: "(fstP (sndP (enc_list (enc_list enc_'a) [[]]))) = 0"
  by(si mp add: enc_list.simps prod_encode_def prod_decode_def prod_decode_aux.simps)

lemma b: "reverse_acc_nat 0 0 = 0"
  by(simp add: reverse_acc_nat.simps prod_decode_def prod_decode_aux.simps)

lemma c: "reverse_nat 0 = 0"
  by(simp add: b reverse_nat.simps prod_encode_0)

lemma d: "append_nat 0 0 = 0"
  by(simp add: c b append_nat.simps)

lemma e: "(sndP (sndP (sndP (sndP (Suc (Suc 0)))))) = 0"
  by eval

value "(pair 1 (pair (sndP (sndP (fstP (sndP (Suc (Suc 0)))))) 0))"

lemma "baz_nat (append_nat 0 0) (Suc (Suc 0)) = 0"
  oops

lemma baz_nat_equiv2:
  assumes "dec_'a \<circ> enc_'a = id"
    and "\<And>acc. f_nat (enc_list enc_'a acc) = enc_list enc_'a (f acc)"
    and "\<And>xss. g_nat (enc_list (enc_list enc_'a) xss) = enc_list (enc_list enc_'a) (g xss)"
  shows "baz_nat (f_nat (enc_list enc_'a acc)) (g_nat (enc_list (enc_list enc_'a) xss))
          = enc_list enc_'a (baz (f acc) (g xss))"
  apply(induction "f acc" "g xss" arbitrary: acc xss rule: baz.induct)
  subgoal premises IH for acc xss
    apply(subst assms(3))
    apply(subst assms(2))
    apply(simp add: IH[symmetric])
    apply(subst baz_nat.simps)
    apply(auto simp add: enc_list.simps)
       apply (simp add: prod_decode_aux.simps prod_decode_def)
      apply (simp add: prod_decode_aux.simps prod_decode_def)
     apply (simp add: prod_decode_aux.simps prod_decode_def)
    apply (simp add: prod_decode_aux.simps prod_decode_def)
    apply (subst pair.simps)+
    apply(subst prod_encode_def)+
    apply(subst atomic.simps)+
    apply(auto split: list.split)
    sorry
  oops


lemma baz_nat_equiv2:
  assumes "(dec_'a :: pair_repr \<Rightarrow> ('a:: order_bot)) \<circ> enc_'a = id"
    and "dec_'a bot = bot"
  shows "baz_nat (enc_list enc_'a acc) (enc_list (enc_list enc_'a) xss) = enc_list enc_'a (baz acc xss)"
  apply(induction acc xss rule: baz.induct)
     apply(all \<open>subst baz.simps\<close>)
  subgoal for acc
    using append_nat_equiv2[OF assms(1)] append_nat_equiv[OF assms]
      append_nat_equiv3[OF assms(1)] append_nat_equiv4[OF assms(1)]
    apply(simp add: Let_def)
    sorry
  subgoal by (metis "11" atomic.simps baz_nat.simps fstP.simps fst_conv prod_encode_inverse)
  subgoal sorry
  subgoal
    apply(subst baz_nat.simps)
    using append_nat_equiv2[OF assms(1)]
    sorry
  oops

function_nat_rewrite_correctness baz
  apply(induction arg\<^sub>1 arg\<^sub>2 rule: baz.induct; subst baz.simps)
  subgoal for acc

    using encoding_list_wellbehaved[OF assms(1), THEN pointfree_idE]
      append_nat_equiv[OF assms]
    apply(simp add: enc_list.simps)
    sorry
  subgoal for acc
    using encoding_list_wellbehaved[OF assms(1), THEN pointfree_idE]
    by (metis "11" baz_nat.simps dec_list.elims list.discI)
  subgoal premises IH for acc v va xss

    apply(subst IH[symmetric])
    apply(subst append_nat_equiv2[OF assms(1), of acc "(v # va)", symmetric])

    using encoding_list_wellbehaved[OF assms(1), THEN pointfree_idE]
      append_nat_equiv[OF assms]
      append_nat_equiv2[OF assms(1), of acc "(v # va)", symmetric]

    sorry
  subgoal premises IH for acc xs v va
    apply(simp add: baz_nat.simps)

    apply(auto simp add: enc_list.simps)
        apply (simp add: prod_decode_aux.simps prod_decode_def)
       apply (simp add: prod_decode_aux.simps prod_decode_def)
      apply (simp add: prod_decode_aux.simps prod_decode_def)
     apply (simp add: prod_decode_aux.simps prod_decode_def)
    using encoding_list_wellbehaved[OF assms(1), THEN pointfree_idE]
      append_nat_equiv[OF assms]
      append_nat_equiv2[OF assms(1)]
      IH
    sorry
  done


(* can't handle case expressions *)
fun test3 where
  "test3 x = (case x of True \<Rightarrow> False | False \<Rightarrow> True)"

(* function_nat_rewrite foo *)


end