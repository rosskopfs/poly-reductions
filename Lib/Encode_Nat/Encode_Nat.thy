theory Encode_Nat
  imports
    Main
    "HOL-Library.Nat_Bijection"
    "HOL-Library.Tree"
    "HOL-Library.Multiset"
    "HOL-Eisbach.Eisbach"
    "HOL-Eisbach.Eisbach_Tools"
  keywords
    "datatype_nat_encode" :: thy_decl and
    "datatype_nat_decode" :: thy_goal and
    "datatype_nat_wellbehaved" :: thy_goal and
    "function_nat_rewrite" :: thy_decl and
    "function_nat_rewrite_manual" :: thy_decl and
    "function_nat_rewrite_correctness" :: thy_goal
begin


type_synonym pair_repr = nat

fun atomic :: "nat \<Rightarrow> pair_repr" where "atomic a = a"
fun pair :: "pair_repr \<Rightarrow> pair_repr \<Rightarrow> pair_repr" where "pair l r = prod_encode (l, r)"

fun fstP :: "pair_repr \<Rightarrow> pair_repr" where "fstP v = fst (prod_decode v)"
fun sndP :: "pair_repr \<Rightarrow> pair_repr" where "sndP v = snd (prod_decode v)"

definition "wellbehaved enc dec \<equiv> (\<forall> a. dec (enc a) = a)"

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
  by auto

lemma prod_decode_lte:
  assumes "v \<le> v'"
  shows fst_prod_decode_lte: "fst (prod_decode v) \<le> v'"
    and snd_prod_decode_lte: "snd (prod_decode v) \<le> v'"
  using prod_decode_less[of v "Suc v'"] assms by auto

lemma snd_prod_encode_lt: "a > 0 \<Longrightarrow> b < prod_encode (a, b)"
  by (induction b; simp add: prod_encode_def)

corollary snd_prod_decode_lt_intro:
  assumes "fstP v \<noteq> 0"
  shows   "snd (prod_decode v) < v"
proof -
  obtain x y where xyv: "prod_decode v = (x, y)" by fastforce
  with assms have "y < prod_encode (x, y)" using snd_prod_encode_lt by simp
  then show ?thesis using prod_decode_inverse[of v] unfolding xyv by simp
qed

datatype_nat_encode nat
declare enc_Nat_nat.simps [simp del]
thm enc_Nat_nat.simps

datatype_nat_encode list
declare enc_List_list.simps [simp del]
thm enc_List_list.simps

datatype_nat_encode prod
declare enc_Product_Type_prod.simps [simp del]
thm enc_Product_Type_prod.simps

datatype_nat_encode tree
declare enc_Tree_tree.simps [simp del]
thm enc_Tree_tree.simps

datatype ('a, 'b) keyed_list_tree =
  KLeaf |
  KNode "(('a, 'b) keyed_list_tree)" 'a "('b list)" "(('a, 'b) keyed_list_tree)"

datatype_nat_encode keyed_list_tree
declare enc_Encode_Nat_keyed_list_tree.simps [simp del]
thm enc_Encode_Nat_keyed_list_tree.simps


datatype 'a forest =
  FLeaf |
  FNode "(('a forest) list)"


lemma enc_List_list_cong[fundef_cong]:
  assumes "xs = ys"
          "\<And>x. x \<in> set ys \<Longrightarrow> enc\<^sub>a x = enc\<^sub>b x"
  shows "enc_List_list enc\<^sub>a xs = enc_List_list enc\<^sub>b ys"
  using assms
  by (induction xs arbitrary: ys; auto simp add: enc_List_list.simps)

datatype_nat_encode forest
declare enc_Encode_Nat_forest.simps [simp del]
thm enc_Encode_Nat_forest.simps

method decode_termination for t =
  relation t, auto;
  \<comment> \<open>If some cases don't work, don't fail completely! Return them unchanged.\<close>
  (auto intro!: prod_decode_less snd_prod_decode_lt_intro)?


datatype_nat_decode nat
termination by (decode_termination "measure id")
thm dec_Nat_nat.simps


datatype_nat_decode list
termination by (decode_termination "measure snd")
declare dec_List_list.simps[simp del]
lemmas [simp] = dec_List_list.simps[of _ "prod_encode _"]
thm dec_List_list.simps


datatype_nat_decode prod
termination by (decode_termination "measure (snd o snd)")
declare dec_Product_Type_prod.simps[simp del]
lemmas [simp] = dec_Product_Type_prod.simps[of _ _ "prod_encode _"]
thm dec_Product_Type_prod.simps

datatype_nat_decode tree
termination by (decode_termination "measure snd")
declare dec_Tree_tree.simps[simp del]
lemmas [simp] = dec_Tree_tree.simps[of _ "prod_encode _"]
thm dec_Tree_tree.simps

datatype_nat_decode keyed_list_tree
termination by (decode_termination "measure (snd o snd)")(*<*)
declare dec_Encode_Nat_keyed_list_tree.simps[simp del]
lemmas [simp] = dec_Encode_Nat_keyed_list_tree.simps[of _ _ "prod_encode _"]
thm dec_Encode_Nat_keyed_list_tree.simps


inductive_set subpairings :: "pair_repr \<Rightarrow> pair_repr set" for x where
  "x \<in> subpairings x"
| "t \<in> subpairings x \<Longrightarrow> fstP t \<in> subpairings x"
| "t \<in> subpairings x \<Longrightarrow> sndP t \<in> subpairings x"

lemma subpairings_fstP_imp: "a \<in> subpairings (fstP x) \<Longrightarrow> a \<in> subpairings x"
  and subpairings_sndP_imp: "a \<in> subpairings (sndP x) \<Longrightarrow> a \<in> subpairings x"
   apply(simp, all \<open>induction rule: subpairings.induct\<close>)
  using subpairings.intros by simp+


lemma subpairings_le: "a \<in> subpairings x \<Longrightarrow> a \<le> x"
  apply(induction rule: subpairings.induct)
  using prod_decode_lte[of _ x] by simp+
  
lemma dec_List_list_cong[fundef_cong]:
  assumes "x = y"
          "\<And>t. t \<in> subpairings y \<Longrightarrow> dec\<^sub>a t = dec\<^sub>b t"
  shows "dec_List_list dec\<^sub>a x = dec_List_list dec\<^sub>b y"
  unfolding assms(1)
  using assms(2)
  apply (induction dec\<^sub>a y rule: dec_List_list.induct)
  subgoal for _ v
    apply (unfold dec_List_list.simps[of _ v])
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
    using subpairings_le fstP.elims snd_prod_decode_lt_intro
    by (metis One_nat_def less_Suc_eq_0_disj less_numeral_extra(4) order_le_less_trans)
    (* by (metis order.strict_trans1 zero_neq_numeral) *)
qed
declare dec_Encode_Nat_forest.simps[simp del]
lemmas [simp] = dec_Encode_Nat_forest.simps[of _ "prod_encode _"]
thm dec_Encode_Nat_forest.simps

declare wellbehaved_def[simp]

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
  (unfold wellbehaved_def,
    \<comment> \<open>Turn that pesky \<open>\<forall>\<close> into a \<open>\<And>\<dots>\<close>\<close>
    intro allI,
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
inferT @{term "wellbehaved"}
\<close>

datatype_nat_wellbehaved nat
  unfolding wellbehaved_def using dec_Nat_nat.simps enc_Nat_nat.simps 
  by auto
thm Nat_nat_wellbehaved


datatype_nat_wellbehaved list
  by (wellbehavedness
      induct_rule: list.induct
      enc_simps: enc_List_list.simps
      assms: assms)
thm List_list_wellbehaved

datatype_nat_wellbehaved prod
  by (wellbehavedness
      induct_rule: prod.induct
      enc_simps: enc_Product_Type_prod.simps
      assms: assms)
thm Product_Type_prod_wellbehaved

datatype_nat_wellbehaved tree
  by (wellbehavedness
      induct_rule: tree.induct
      enc_simps: enc_Tree_tree.simps
      assms: assms)
thm Tree_tree_wellbehaved

datatype_nat_wellbehaved keyed_list_tree
  by (wellbehavedness
      induct_rule: keyed_list_tree.induct
      enc_simps: enc_Encode_Nat_keyed_list_tree.simps
      assms: assms
      \<comment> \<open>Include wellbehavedness facts about referenced types\<close>
      uses_wellbehaved: List_list_wellbehaved[OF assms(2)])
thm Encode_Nat_keyed_list_tree_wellbehaved

datatype_nat_wellbehaved forest
  apply (wellbehavedness
      induct_rule: forest.induct
      enc_simps: enc_Encode_Nat_forest.simps
      assms: assms
      uses_wellbehaved: List_list_wellbehaved[OF assms(1)])
  subgoal for _ x
    apply (subst enc_Encode_Nat_forest.simps dec_Encode_Nat_forest.simps)
    \<comment> \<open>(\<open>\<star>\<close>)\<close>
    apply (induction rule: list.induct)
    subgoal by (simp add: enc_List_list.simps enc_Encode_Nat_forest.simps)
    subgoal by (subst enc_List_list.simps) simp
    done
  done
thm Encode_Nat_forest_wellbehaved

method natfn_correctness 
  methods induct_rule
  uses assms simps_nat dels enc_simps args_wellbehaved =
  \<comment> \<open>Add wellbehavedness assumptions to get induction hypotheses\<close>
  print_fact assms, print_fact args_wellbehaved, insert assms,
  \<comment> \<open>Computation induction over the original function\<close>
  induct_rule;
  \<comment> \<open>Unfold exactly one level of the natfn we're looking at—corresponding to the inductive step\<close>
  subst simps_nat;
  ( \<comment> \<open>This solves tail-recursive branches and some basic leaves:\<close>
    print_fact dels,
    insert args_wellbehaved,
    simp del: dels add: enc_simps,
    meson?)?

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
  by (natfn_correctness \<open>induct arg\<^sub>1 arg\<^sub>2 rule: reverset.induct\<close>
      assms: assms
      simps_nat: reverset_nat.simps
      enc_simps: enc_List_list.simps
      args_wellbehaved: List_list_wellbehaved[OF assms(1)])
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

function_nat_rewrite_correctness prefixest
  by (natfn_correctness \<open>induct arg\<^sub>1 arg\<^sub>2 rule: prefixest.induct\<close>
      assms: assms
      simps_nat: prefixest_nat.simps
      enc_simps: enc_List_list.simps
      args_wellbehaved: List_list_wellbehaved[OF List_list_wellbehaved[OF assms(1)]])
thm prefixest_nat_equiv

fun prefixes2 where
  "prefixes2 [] ps = reverset ([] # ps) []" |
  "prefixes2 (a # b) ps = prefixes2 b ((a # b) # ps)"

function_nat_rewrite prefixes2
thm prefixes2_nat.simps

function_nat_rewrite_correctness prefixes2
  apply (natfn_correctness \<open>induct arg\<^sub>1 arg\<^sub>2 rule: prefixes2.induct\<close>
      assms: assms
      simps_nat: prefixes2_nat.simps
      enc_simps: enc_List_list.simps
      dels: reverset.simps
      args_wellbehaved: List_list_wellbehaved[OF List_list_wellbehaved[OF assms(1)]]
      List_list_wellbehaved[OF assms(1)])
  subgoal for ps
    \<comment> \<open>We need to explicitly instantiate the equivalence rule for the called function.\<close>
    \<comment> \<open>Figuring out exactly what fact to supply is very mechanic:\<close>
    \<comment> \<open>The \<open>wellbehaved\<close> fact(s) can be fetched from the function, while the arguments\<close>
    \<comment> \<open>appear in the same order they do in the simp rule that generates the subgoal.\<close>
    using reverset_nat_equiv[OF List_list_wellbehaved[OF assms(1)], of "[] # ps" "[]"]
    by (simp add: enc_List_list.simps)
  done
thm prefixes2_nat_equiv

fun subtrees :: "'a tree \<Rightarrow> 'a tree list" where
  "subtrees \<langle>\<rangle> = []"
| "subtrees \<langle>l, v, r\<rangle> = subtrees l @ subtrees r @ [l] @ [r]"


function subtreest :: "'a tree \<Rightarrow> 'a tree list \<Rightarrow> 'a tree list \<Rightarrow> 'a tree list" where
  "subtreest \<langle>\<rangle> [] ts = ts"
| "subtreest \<langle>\<rangle> (s # stk) ts = subtreest s stk ts"
| "subtreest \<langle>l, v, r\<rangle> stk ts = subtreest l (r # stk) (l # r # ts)"
  by simp_all (metis neq_Leaf_iff splice.cases surj_pair)
termination
  by (relation "(\<lambda>(t, stk, _). size t + size1 t
                             + sum_list (map (\<lambda>t. size t + size1 t) stk))
                <*mlex*> {}")
     (simp_all add: wf_mlex mlex_less)

lemma subtrees_subtreest: "mset (subtrees t @ concat (map subtrees ts) @ stk) = mset (subtreest t ts stk)"
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
      args_wellbehaved: Tree_tree_wellbehaved[OF assms(1)]
      List_list_wellbehaved[OF Tree_tree_wellbehaved[OF assms(1)]])(*<*)
thm subtreest_nat_equiv

end