(*  Title:      Encode_Nat.thy
    Author:     , TU Muenchen
    Author:     Andreas Vollert, TU Muenchen
    Copyright   2022, 2023
*)

theory Encode_Nat
  imports
    Main
    "HOL-Library.Nat_Bijection"
    "HOL-Library.Tree"
    "HOL-Library.Multiset"
    "HOL-Eisbach.Eisbach"
    "HOL-Eisbach.Eisbach_Tools"
    Test
  keywords
    "test" :: thy_decl and
    "test2" :: thy_decl and
    "datatype_nat_encode" :: thy_decl and
    "datatype_nat_decode" :: thy_goal and
    "datatype_nat_wellbehaved" :: thy_goal and
    "function_nat_rewrite" :: thy_decl and
    "function_nat_rewrite_correctness" :: thy_goal
begin


type_synonym pair_repr = nat

fun atomic :: "nat \<Rightarrow> pair_repr" where
  "atomic a = a"

fun pair :: "pair_repr \<Rightarrow> pair_repr \<Rightarrow> pair_repr"
  where "pair l r = prod_encode (l, r)"

fun fstP :: "pair_repr \<Rightarrow> pair_repr" where
  "fstP v = fst (prod_decode v)"

fun sndP :: "pair_repr \<Rightarrow> pair_repr" where
  "sndP v = snd (prod_decode v)"


ML_file \<open>./Encode_Nat.ML\<close>


fun size_pair_repr :: "pair_repr \<Rightarrow> nat" where
  "size_pair_repr v = v"

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
proof -
  obtain x y where xyv: "prod_decode v = (x, y)" by fastforce
  with assms have "y < prod_encode (x, y)" using snd_prod_encode_lt by simp
  then show ?thesis using prod_decode_inverse[of v] unfolding xyv by simp
qed

declare [[ML_print_depth = 50]]


datatype_nat_encode nat
declare enc_nat.simps [simp del]

datatype_nat_encode list
declare enc_list.simps [simp del]

datatype_nat_encode bool
declare enc_bool.simps [simp del]

datatype_nat_encode char
declare enc_char.simps [simp del]

datatype_nat_encode prod
declare enc_prod.simps [simp del]

datatype_nat_encode tree
declare enc_tree.simps [simp del]


datatype ('a, 'b) keyed_list_tree =
  KLeaf |
  KNode "(('a, 'b) keyed_list_tree)" 'a "('b list)" "(('a, 'b) keyed_list_tree)"


datatype_nat_encode keyed_list_tree
declare enc_keyed_list_tree.simps [simp del]
thm enc_keyed_list_tree.simps

datatype 'a forest =
  FLeaf |
  FNode "(('a forest) list)"

lemma enc_List_list_cong[fundef_cong]:
  assumes "xs = ys"
    and "\<And>x. x \<in> set ys \<Longrightarrow> enc\<^sub>a x = enc\<^sub>b x"
  shows "enc_list enc\<^sub>a xs = enc_list enc\<^sub>b ys"
  using assms by (induction xs arbitrary: ys; auto simp add: enc_list.simps)

datatype_nat_encode forest
declare enc_forest.simps [simp del]
thm enc_forest.simps

method decode_termination for t =
  relation t, auto;
  (auto intro!: prod_decode_less snd_prod_decode_lt_intro)?




datatype_nat_decode nat
termination by (decode_termination "measure id")
thm dec_nat.simps

datatype_nat_decode list
termination by (decode_termination "measure snd")
declare dec_list.simps[simp del]
lemmas [simp] = dec_list.simps[of _ "prod_encode _"]
thm dec_list.simps

datatype_nat_decode prod
termination by (decode_termination "measure (snd o snd)")
declare dec_prod.simps[simp del]
lemmas [simp] = dec_prod.simps[of _ _ "prod_encode _"]
thm dec_prod.simps

datatype_nat_decode tree
termination by (decode_termination "measure snd")
declare dec_tree.simps[simp del]
lemmas [simp] = dec_tree.simps[of _ "prod_encode _"]
thm dec_tree.simps

datatype_nat_decode keyed_list_tree
termination by (decode_termination "measure (snd o snd)")
declare dec_keyed_list_tree.simps[simp del]
lemmas [simp] = dec_keyed_list_tree.simps[of _ _ "prod_encode _"]
thm dec_keyed_list_tree.simps


inductive_set
  subpairings :: "pair_repr \<Rightarrow> pair_repr set"
  for x
  where
    "x \<in> subpairings x"
  | "t \<in> subpairings x \<Longrightarrow> fstP t \<in> subpairings x"
  | "t \<in> subpairings x \<Longrightarrow> sndP t \<in> subpairings x"

lemma
  shows subpairings_fstP_imp: "a \<in> subpairings (fstP x) \<Longrightarrow> a \<in> subpairings x"
    and subpairings_sndP_imp: "a \<in> subpairings (sndP x) \<Longrightarrow> a \<in> subpairings x"
   apply(simp, all \<open>induction rule: subpairings.induct\<close>)
  using subpairings.intros by simp+

lemma subpairings_le: "a \<in> subpairings x \<Longrightarrow> a \<le> x"
  apply(induction rule: subpairings.induct)
  using prod_decode_lte[of _ x] by simp+

lemma dec_List_list_cong[fundef_cong]:
  assumes "x = y"
    and "\<And>t. t \<in> subpairings y \<Longrightarrow> dec\<^sub>a t = dec\<^sub>b t"
  shows "dec_list dec\<^sub>a x = dec_list dec\<^sub>b y"
  unfolding assms(1)
  using assms(2)
  apply (induction dec\<^sub>a y rule: dec_list.induct)
  subgoal for _ v
    apply (unfold dec_list.simps[of _ v])
    using subpairings.intros
      \<comment> \<open>specialized for the recursive constructor field:\<close>
      subpairings_sndP_imp[OF subpairings_sndP_imp[of _ "sndP v"]]
    by presburger
  done

datatype_nat_decode forest
termination proof (decode_termination "measure snd")
  fix v t assume
    "fst (prod_decode v) = Suc 0"
    "t \<in> subpairings (snd (prod_decode v))"
  then show "t < v"
    using subpairings_le snd_prod_decode_lt_intro by (fastforce simp: order_le_less_trans)
qed

declare dec_forest.simps[simp del]
lemmas [simp] = dec_forest.simps[of _ "prod_encode _"]
thm dec_forest.simps


method wellbehavedness_case
  uses assms enc_simps uses_wellbehaved =
  \<comment> \<open>Unfold the encoder applied to the universally argument once.\<close>
  subst enc_simps,
  \<comment> \<open>Type variables are assumed to be well-behaved.\<close>
  insert assms,
  \<comment> \<open>Wellbehavedness of other data types used by constructors must be provided.\<close>
  insert uses_wellbehaved,
  auto

method wellbehavedness
  uses induct_rule assms enc_simps uses_wellbehaved =
  (intro ext,
    \<comment> \<open>\<open>\<dots>\<close>but \<open>induction\<close> still refuses to run structural induction correctly when\<close>
    \<comment> \<open>the goal is universally quantified and there are no assumptions.\<close>
    \<comment> \<open>Outside of Eisbach, \<^bold>\<open>subgoal apply\<close> \<open>(induction rule: induct_rule)\<close>\<close>
    \<comment> \<open>does the trick. This is the shortest replacement I found.\<close>
    insert TrueI, match premises in True \<Rightarrow> \<open>induction rule: induct_rule\<close>);
  (solves \<open>wellbehavedness_case
           assms: assms enc_simps: enc_simps uses_wellbehaved: uses_wellbehaved\<close>
    \<comment> \<open>If that approach didn't work, return the original induction case\<close>
    )?

ML \<open>
val T = @{typ "'a list"};
is_Type T;
is_TFree T;
is_TVar T;
val [T'] = dest_Type T |> snd;
is_Type T;
is_TFree T;
is_TVar T;
\<close>


datatype_nat_decode bool
termination by (decode_termination "measure id")
declare dec_bool.simps[simp del]

datatype_nat_wellbehaved bool
  by(intro ext, simp add: dec_bool.simps enc_bool.simps split:bool.split)
thm encoding_bool_wellbehaved

datatype_nat_wellbehaved nat
  using dec_nat.simps enc_nat.simps by fastforce
thm encoding_nat_wellbehaved

datatype_nat_wellbehaved list
  apply(intro ext)
  subgoal for x
    using assms[THEN pointfree_idE]
    by(induction x rule: list.induct; simp add: enc_list.simps)
  done

datatype_nat_wellbehaved prod
  apply(intro ext)
  subgoal for x
    using assms[THEN pointfree_idE]
    by(induction x rule: prod.induct; simp add: enc_prod.simps)
  done

thm encoding_prod_wellbehaved

datatype_nat_wellbehaved tree
  apply(intro ext)
  subgoal for x
    using assms[THEN pointfree_idE]
    by(induction x rule: tree.induct; simp add: enc_tree.simps)
  done

thm encoding_tree_wellbehaved

datatype_nat_wellbehaved keyed_list_tree
  apply(intro ext)
  subgoal for x
    apply(induction x rule: keyed_list_tree.induct)
    using encoding_list_wellbehaved[OF assms(2)] assms(1)
    by (simp add: enc_keyed_list_tree.simps pointfree_idE)+
  done

thm encoding_keyed_list_tree_wellbehaved

datatype_nat_wellbehaved forest
  apply(intro ext)
  subgoal for x
    apply(induction x rule: forest.induct)
    using encoding_list_wellbehaved[OF assms(1)]
     apply (simp add: enc_forest.simps pointfree_idE)
    subgoal for x
      apply (induction x rule: list.induct)
      by(simp add: enc_list.simps enc_forest.simps)+
    done
  done

thm encoding_forest_wellbehaved

method natfn_correctness
  methods induct_rule
  uses assms simps_nat dels enc_simps args_wellbehaved =
  \<comment> \<open>Add wellbehavedness assumptions to get induction hypotheses\<close>
  print_fact assms, print_fact args_wellbehaved, insert assms,
  \<comment> \<open>Computation induction over the original function\<close>
  induct_rule;
  \<comment> \<open>Unfold exactly one level of the natfn we're looking at—corresponding to the inductive step\<close>
  subst simps_nat;
  insert args_wellbehaved; simp del: dels add: enc_simps; meson

fun reverset :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "reverset [] r = r"
| "reverset (l # ls) r = reverset ls (l # r)"

lemma reverset_rev: "reverset l r = rev l @ r"
  by (induction l r rule: reverset.induct; simp)

lemma reverset_correct: "reverset l [] = rev l"
  by (simp add: reverset_rev)

function_nat_rewrite reverset
thm reverset_nat.simps

function_nat_rewrite_correctness reverset
  apply(induction arg\<^sub>1 arg\<^sub>2 rule: reverset.induct)
   apply(all \<open>subst reverset_nat.simps\<close>)
  subgoal
    apply(subst enc_List_list.simps)
    using List_list_wellbehaved[OF assms(1)]
    by(simp add: assms pointfree_idE )
  subgoal
    by(simp add: enc_List_list.simps)
  done

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

function_nat_rewrite prefixest
thm prefixest_nat.simps
thm prefixest.induct

function_nat_rewrite_correctness prefixest
  using assms
  apply(induction arg\<^sub>1 arg\<^sub>2 rule: prefixest.induct; subst prefixest_nat.simps)
  using List_list_wellbehaved[OF List_list_wellbehaved, OF assms(1), THEN pointfree_idE]
  by(simp add: enc_List_list.simps Let_def)+

(* or
  by (natfn_correctness \<open>induct arg\<^sub>1 arg\<^sub>2 rule: prefixest.induct\<close>
      assms: assms
      simps_nat: prefixest_nat.simps
      enc_simps: enc_List_list.simps
      args_wellbehaved:
      List_list_wellbehaved[OF List_list_wellbehaved, OF assms(1), THEN pointfree_idE])
*)

thm prefixest_nat_equiv


fun prefixes2 where
  "prefixes2 [] ps = reverset ([] # ps) []"
| "prefixes2 (a # b) ps = prefixes2 b ((a # b) # ps)"

function_nat_rewrite prefixes2
thm prefixes2_nat.simps back_subst[of _ "x # xs"]


function_nat_rewrite_correctness prefixes2
  using assms
  apply(induction arg\<^sub>1 arg\<^sub>2 rule: prefixes2.induct; subst prefixes2_nat.simps)
  subgoal for ps
    using
      reverset_nat_equiv[OF List_list_wellbehaved, OF assms, of "[] # ps" "[]"]
    by(simp add: enc_List_list.simps)
  by(simp add: enc_List_list.simps Let_def)
    (*
  apply (natfn_correctness \<open>induct arg\<^sub>1 arg\<^sub>2 rule: prefixes2.induct\<close>
      assms: assms
      simps_nat: prefixes2_nat.simps
      enc_simps: enc_List_list.simps
      dels: reverset.simps
      args_wellbehaved: List_list_wellbehaved[OF List_list_wellbehaved, OF assms(1), THEN pointfree_idE]
      List_list_wellbehaved[OF assms(1), THEN pointfree_idE])
  subgoal for ps
    \<comment> \<open>We need to explicitly instantiate the equivalence rule for the called function.\<close>
    \<comment> \<open>Figuring out exactly what fact to supply is very mechanic:\<close>
    \<comment> \<open>The \<open>wellbehaved\<close> fact(s) can be fetched from the function, while the arguments\<close>
    \<comment> \<open>appear in the same order they do in the simp rule that generates the subgoal.\<close>
    using reverset_nat_equiv[OF List_list_wellbehaved[OF assms(1)], of "[] # ps" "[]"]
    by (simp add: enc_List_list.simps)
  done
*)
thm prefixes2_nat_equiv

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
thm subtreest_nat.simps

function_nat_rewrite_correctness subtreest
  by (natfn_correctness \<open>induct arg\<^sub>1 arg\<^sub>2 arg\<^sub>3 rule: subtreest.induct\<close>
      assms: assms
      simps_nat: subtreest_nat.simps
      enc_simps: enc_List_list.simps enc_Tree_tree.simps
      args_wellbehaved: Tree_tree_wellbehaved[OF assms(1), THEN pointfree_idE]
      List_list_wellbehaved[OF Tree_tree_wellbehaved, OF assms(1), THEN pointfree_idE])

thm subtreest_nat_equiv


end