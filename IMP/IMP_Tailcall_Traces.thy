theory IMP_Tailcall_Traces
  imports IMP_Tailcall
begin

unbundle tcom_syntax
unbundle no com'_syntax

type_synonym call_trace = "(com \<times> state) list"
type_synonym trace = "nat \<times> call_trace"

(* interp_trace k T z holds when z is the running time of the trace T, plus k *)
definition interp_trace :: "nat \<Rightarrow> call_trace \<Rightarrow> nat \<Rightarrow> bool" where
  "interp_trace k T z \<equiv> (\<exists>zgs.
     length zgs = length T
     \<and> (\<forall>i < length T. \<exists>s'. T ! i \<Rightarrow>\<^bsup>zgs ! i\<^esup> s')
     \<and> z = sum_list zgs + k)"

lemma interp_trace_append:
  assumes "interp_trace k1 T1 z1" "interp_trace k2 T2 z2"
  shows "interp_trace (k1 + k2) (T1 @ T2) (z1 + z2)"
proof-
  from assms obtain zgs1 where 1:
      "length zgs1 = length T1"
      "\<forall>i < length T1. \<exists>s'. T1 ! i \<Rightarrow>\<^bsup>zgs1 ! i\<^esup> s'"
      "z1 = sum_list zgs1 + k1"
    unfolding interp_trace_def by blast
  from assms obtain zgs2 where 2:
      "length zgs2 = length T2"
      "\<forall>i < length T2. \<exists>s'. T2 ! i \<Rightarrow>\<^bsup>zgs2 ! i\<^esup> s'"
      "z2 = sum_list zgs2 + k2"
    unfolding interp_trace_def by blast

  have "length (zgs1 @ zgs2) = length (T1 @ T2)" using 1 2 by simp
  moreover have "\<exists>s'. (T1 @ T2) ! i \<Rightarrow>\<^bsup>(zgs1 @ zgs2) ! i\<^esup> s'" if "i < length (T1 @ T2)" for i
  proof (cases "i < length T1")
    case True
    then show ?thesis by (simp add: nth_append_left 1)
  next
    case False
    with 1 that have "length T1 \<le> i" "length zgs1 \<le> i" "i - length T1 < length T2" by simp_all
    with 1 2 False show ?thesis by (simp add: nth_append_right)
  qed
  moreover have "z1 + z2 = sum_list (zgs1 @ zgs2) + (k1 + k2)" using 1 2 by simp
  ultimately show "interp_trace (k1 + k2) (T1 @ T2) (z1 + z2)"
    unfolding interp_trace_def by blast
qed

lemma interp_trace_nil[simp]: "interp_trace k [] k" unfolding interp_trace_def by simp
(* lemma interp_trace_nil'[simp]: "k = z \<Longrightarrow> interp_trace k [] z" unfolding interp_trace_def by simp *)
lemma interp_trace_nilE[elim]: "interp_trace k [] z \<Longrightarrow> k = z" unfolding interp_trace_def by simp
(* lemma interp_trace_nil_iff: "interp_trace k [] z \<longleftrightarrow> k = z" unfolding interp_trace_def by fastforce *)

(*
lemma interp_trace1:
  assumes "\<exists>s'. g \<Rightarrow>\<^bsup>z\<^esup> s'"
  shows "interp_trace k [g] (k + z)"
proof (subst interp_trace_def, standard, standard)
  show "length [z] = length [g]" by simp
  show "(\<forall>i<length [g]. Ex (big_step_t ([g] ! i) ([z] ! i))) \<and> k + z = sum_list [z] + k" using assms by simp
qed *)

lemma interp_trace_singleton[simp]:
  assumes "(C, s) \<Rightarrow>\<^bsup>z\<^esup> t"
  shows "interp_trace k [(C, s)] (z + k)"
proof-
  from assms have
      "length [z] = length [(C, s)]"
      "\<forall>i < length [(C, s)]. \<exists>s'. [(C, s)] ! i \<Rightarrow>\<^bsup>[z] ! i\<^esup> s'"
      "z + k = sum_list [z] + k"
    by auto
  then show "interp_trace k [(C, s)] (z + k)" unfolding interp_trace_def by blast
qed

lemmas interp_trace_singleton'[simp] = interp_trace_singleton[where k = 0, simplified add_0_right]
  

lemma interp_trace_sum[simp]:
  "interp_trace (k + x) T (z + x) \<longleftrightarrow> interp_trace k T z"
  unfolding interp_trace_def by simp

lemma interp_trace_determ:
  assumes "interp_trace k T z1" "interp_trace k T z2"
  shows "z1 = z2"
proof-
  from assms obtain zgs1 where 1:
      "length zgs1 = length T"
      "\<forall>i < length T. \<exists>s'. (fst (T ! i), snd (T ! i)) \<Rightarrow>\<^bsup>zgs1 ! i\<^esup> s'"
      "z1 = sum_list zgs1 + k"
    unfolding interp_trace_def by fastforce
  from assms obtain zgs2 where 2:
      "length zgs2 = length T"
      "\<forall>i < length T. \<exists>s'. (fst (T ! i), snd (T ! i)) \<Rightarrow>\<^bsup>zgs2 ! i\<^esup> s'"
      "z2 = sum_list zgs2 + k"
    unfolding interp_trace_def by fastforce
  have "\<forall>i < length T. zgs1 ! i = zgs2 ! i" using 1 2 big_step_t_determ2 by blast
  then have "zgs1 = zgs2" using 1 2 by (simp add: list_eq_iff_nth_eq)
  then show "z1 = z2" using 1 2 by blast
qed


type_synonym leaf_state = "state \<times> bool"

inductive
  (* (term, state), (constants, calls), (new state, is tail call) *)
  ttrace_to_leaf :: "tcom \<times> state \<Rightarrow> trace \<Rightarrow> leaf_state \<Rightarrow> bool"  ("_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
tSkip: "(tSKIP,s) \<Rightarrow>\<^bsup>(Suc 0, [])\<^esup> (s, False)" |
tAssign: "(x ::= a,s) \<Rightarrow>\<^bsup>(Suc (Suc 0), [])\<^esup> (s(x := aval a s), False)" |
tSeq:
  "\<lbrakk>(c1,s1) \<Rightarrow>\<^bsup>(k1, T1)\<^esup> (s2, False); (c2,s2) \<Rightarrow>\<^bsup>(k2, T2)\<^esup> (s3, l); k = k1 + k2; T = T1 @ T2\<rbrakk>
   \<Longrightarrow> (c1;; c2,s1) \<Rightarrow>\<^bsup>(k, T)\<^esup> (s3, l)" |
tIfTrue:
  "\<lbrakk>s b \<noteq> 0; (c1,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l); k' = k + 1\<rbrakk>
   \<Longrightarrow> (IF b\<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>(k', T)\<^esup> (t, l)" |
tIfFalse:
  "\<lbrakk>s b = 0; (c2,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l); k' = k + 1\<rbrakk>
   \<Longrightarrow> (IF b\<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>(k', T)\<^esup> (t, l)" |
tCall: "\<lbrakk>(C,s) \<Rightarrow>\<^bsup>z \<^esup> t\<rbrakk> \<Longrightarrow> (tCall C r,s) \<Rightarrow>\<^bsup>(0, [(C,s)])\<^esup> (s(r := t r), False)" |
tTail: "(tTAIL,s) \<Rightarrow>\<^bsup>(5, [])\<^esup> (s, True)"

declare ttrace_to_leaf.intros[intro]
lemmas ttrace_to_leaf_induct = ttrace_to_leaf.induct[split_format(complete)]

(* modified introduction rules that always apply when the term is of the correct shape *)
lemma ttrace_to_leaf_tSkip'[intro]:
  assumes "t = s" and "z = 1" and "T = []" and "\<not> l"
  shows "(tSKIP,s) \<Rightarrow>\<^bsup>(z,T)\<^esup> (t,l)" using assms[unfolded One_nat_def] tSkip by simp
lemma ttrace_to_leaf_tAssign'[intro]:
  assumes "t = s(x := aval a s)" and "z = 2" and "T = []" and "\<not> l"
  shows "(x ::= a,s) \<Rightarrow>\<^bsup>(z,T)\<^esup> (t,l)" using assms[unfolded numeral_2_eq_2] tAssign by simp
lemma ttrace_to_leaf_tCall'[intro]:
  assumes "t' = s(r := t r)" and "z' = 0" and "T = [(C,s)]" and "\<not> l"
  shows "(C,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> (CALL C RETURN r,s) \<Rightarrow>\<^bsup>(z',T) \<^esup> (t',l)" using assms tCall by simp
lemma ttrace_to_leaf_tTail'[intro]:
  assumes "t = s" "z' = 5" and "T = []" and "l"
  shows "(tTAIL,s) \<Rightarrow>\<^bsup>(z',T)\<^esup> (t,l)" using assms tTail by simp

inductive_cases tSkip_trace_leafE[elim!]: "(tSKIP,s) \<Rightarrow>\<^bsup>T \<^esup> l"
inductive_cases tAssign_trace_leafE[elim!]: "(x ::= a,s) \<Rightarrow>\<^bsup>T \<^esup> l"
inductive_cases tSeq_trace_leafE[elim!]: "(c1;;c2,s1) \<Rightarrow>\<^bsup>T \<^esup> l"
inductive_cases tIf_trace_leafE[elim!]: "(IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>T \<^esup> l"
inductive_cases tCall_trace_leafE[elim!]: "(CALL C RETURN v,s) \<Rightarrow>\<^bsup>T \<^esup> l"

inductive_cases tTail_trace_leafE[elim]: "(tTAIL,s) \<Rightarrow>\<^bsup>T \<^esup> l" (* not safe ? *)


lemma nontail_trace_no_tail:
  assumes "\<not> tails c" "(c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l)" shows "\<not> l"
  using assms apply (induction c arbitrary: k T s) by auto blast+

lemma trace_leaf_nontail_bigstep:
  assumes "(c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l)" "\<not> l"
  shows "\<exists>z. interp_trace k T z \<and> f \<turnstile> (c,s) \<Rightarrow>\<^bsup>z\<^esup> t"
using assms proof (induction rule: ttrace_to_leaf_induct)
  case tSkip
  with interp_trace_nil show ?case by blast
next
  case tAssign
  with interp_trace_nil show ?case by blast
next
  case tSeq
  with interp_trace_append show ?case by blast
next
  case tIfTrue
  with interp_trace_sum show ?case by blast
next
  case tIfFalse
  with interp_trace_sum show ?case by blast
next
  case tCall
  with interp_trace_singleton' show ?case by blast
next
  case tTail
  then show ?case by blast
qed

corollary trace_leaf_nontail_bigstep':
  assumes "\<not> tails c" "(c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l)"
  shows "\<exists>z. interp_trace k T z \<and> f \<turnstile> (c,s) \<Rightarrow>\<^bsup>z\<^esup> t"
  using trace_leaf_nontail_bigstep nontail_trace_no_tail assms by metis


lemma bigstep_nontail_trace_leaf:
  assumes "f \<turnstile> (c,s) \<Rightarrow>\<^bsup>z :: nat\<^esup> t" "\<not> tails c"
  shows "\<exists>k T. interp_trace k T z \<and> (c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, False)"
using assms proof (induction rule: tbig_step_t_induct)
  case tSkip
  with interp_trace_nil show ?case by blast
next
  case tAssign
  with interp_trace_nil show ?case by blast
next
  case tSeq
  with interp_trace_append show ?case by fastforce
next
  case tIfTrue
  with interp_trace_sum show ?case by fastforce
next
  case tIfFalse
  with interp_trace_sum show ?case by fastforce
next
  case tCall
  with interp_trace_singleton' show ?case by blast
next
  case tTail
  then show ?case by simp
qed

(* each command can cost up to 5, so the static cost is at most 5 times the number of commands *)
lemma trace_nontail_static_bound:
  assumes "(c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l)"
  shows "k \<le> c_struct c"
  using assms by (induction rule: ttrace_to_leaf_induct) auto

(* there cannot be more calls than commands *)
lemma trace_nontail_call_bound:
  assumes "(c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l)"
  shows "length T \<le> IMP_Tailcall.num_commands c"
  using assms by (induction rule: ttrace_to_leaf_induct) auto


inductive
  (* (term, state), (constants, calls), new state *)
  ttrace_to_end :: "tcom \<Rightarrow> tcom \<times> state \<Rightarrow> trace \<Rightarrow> state \<Rightarrow> bool"  ("_ \<turnstile>_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
tSkip: "c \<turnstile> (tSKIP,s) \<Rightarrow>\<^bsup>(Suc 0, [])\<^esup> s" |
tAssign: "c \<turnstile> (x ::= a,s) \<Rightarrow>\<^bsup>(Suc (Suc 0), [])\<^esup> s(x := aval a s)" |
tSeq:
  (* TODO: would it be a good idea to use ttrace_to_leaf for c1 here ? *)
  "\<lbrakk>c \<turnstile> (c1,s1) \<Rightarrow>\<^bsup>(k1, T1)\<^esup> s2; c \<turnstile> (c2,s2) \<Rightarrow>\<^bsup>(k2, T2)\<^esup> s3; k = k1 + k2; T = T1 @ T2\<rbrakk>
   \<Longrightarrow> c \<turnstile> (c1;; c2,s1) \<Rightarrow>\<^bsup>(k, T)\<^esup> s3" |
tIfTrue:
  "\<lbrakk>s b \<noteq> 0; c \<turnstile> (c1,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> t; k' = k + 1\<rbrakk>
   \<Longrightarrow> c \<turnstile> (IF b\<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>(k', T)\<^esup> t" |
tIfFalse:
  "\<lbrakk>s b = 0; c \<turnstile> (c2,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> t; k' = k + 1\<rbrakk>
   \<Longrightarrow> c \<turnstile> (IF b\<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>(k', T)\<^esup> t" |
tCall: "\<lbrakk>(C,s) \<Rightarrow>\<^bsup>z \<^esup> t\<rbrakk> \<Longrightarrow> c \<turnstile> (tCall C r,s) \<Rightarrow>\<^bsup>(0, [(C,s)])\<^esup> s(r := t r)" |
tTail: "\<lbrakk>c \<turnstile> (c,s) \<Rightarrow>\<^bsup>(k, T) \<^esup> t; k' = k + 5\<rbrakk> \<Longrightarrow> c \<turnstile> (tTAIL,s) \<Rightarrow>\<^bsup>(k', T)\<^esup> t"

declare ttrace_to_end.intros[intro]
lemmas ttrace_to_end_induct = ttrace_to_end.induct[split_format(complete)]

inductive_cases tSkip_trace_endE[elim!]: "c \<turnstile> (tSKIP,s) \<Rightarrow>\<^bsup>T :: trace\<^esup> t"
inductive_cases tAssign_trace_endE[elim!]: "c \<turnstile> (x ::= a,s) \<Rightarrow>\<^bsup>T :: trace\<^esup> t"
inductive_cases tSeq_trace_endE[elim!]: "c \<turnstile> (c1;;c2,s) \<Rightarrow>\<^bsup>T :: trace\<^esup> t"
inductive_cases tIf_trace_endE[elim!]: "c \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>T :: trace\<^esup> t"
inductive_cases tCall_trace_endE[elim!]: "c \<turnstile> (CALL C RETURN v,s) \<Rightarrow>\<^bsup>T :: trace\<^esup> t"

inductive_cases tTail_trace_endE[elim]: "c \<turnstile> (tTAIL,s) \<Rightarrow>\<^bsup>T :: trace\<^esup> t" (* not safe ? *)


(* relating full traces and bigstep *)

lemma trace_end_bigstep:
  assumes "f \<turnstile> (c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> t"
  shows "\<exists>z. interp_trace k T z \<and> f \<turnstile> (c,s) \<Rightarrow>\<^bsup>z\<^esup> t"
using assms proof (induction rule: ttrace_to_end_induct)
  case tSkip
  with interp_trace_nil show ?case by blast
next
  case tAssign
  with interp_trace_nil show ?case by blast
next
  case tSeq
  with interp_trace_append show ?case by blast
next
  case tIfTrue
  with interp_trace_sum show ?case by blast
next
  case tIfFalse
  with interp_trace_sum show ?case by blast
next
  case tCall
  with interp_trace_singleton' show ?case by blast
next
  case (tTail c s k T t k')
  then obtain z :: nat where "interp_trace k T z" and *: "c \<turnstile> (c, s) \<Rightarrow>\<^bsup>z\<^esup> t" by blast
  with tTail have "interp_trace k' T (5 + z)" by (simp add: algebra_simps)
  with * show ?case by blast
qed

(* corollary trace_end_bigstepE:
  assumes "f \<turnstile> (c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> t"
  obtains z :: nat where "interp_trace k T z" "f \<turnstile> (c,s) \<Rightarrow>\<^bsup>z\<^esup> t"
  using trace_end_bigstep assms by blast *)

corollary trace_end_bigstep_z:
  assumes "f \<turnstile> (c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> t" "interp_trace k T z"
  shows "f \<turnstile> (c,s) \<Rightarrow>\<^bsup>z :: nat\<^esup> t"
proof-
  obtain z' :: nat where "interp_trace k T z'" and *: "f \<turnstile> (c,s) \<Rightarrow>\<^bsup>z'\<^esup> t"
    using assms trace_end_bigstep by blast
  with assms interp_trace_determ have "z = z'" by blast
  with * show "f \<turnstile> (c,s) \<Rightarrow>\<^bsup>z :: nat\<^esup> t" by blast
qed

lemma bigstep_trace_end:
  assumes "f \<turnstile> (c,s) \<Rightarrow>\<^bsup>z :: nat\<^esup> t"
  shows "\<exists>k T. interp_trace k T z \<and> f \<turnstile> (c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> t"
using assms proof (induction rule: tbig_step_t_induct)
  case tSkip
  with interp_trace_nil show ?case by blast
next
  case tAssign
  with interp_trace_nil show ?case by blast
next
  case tSeq
  with interp_trace_append show ?case by blast
next
  case tIfTrue
  with interp_trace_sum show ?case by blast
next
  case tIfFalse
  with interp_trace_sum show ?case by blast
next
  case tCall
  with interp_trace_singleton' show ?case by blast
next
  case (tTail c s z t)
  then obtain k T where "interp_trace k T z" and *: "c \<turnstile>(c, s) \<Rightarrow>\<^bsup>(k, T)\<^esup> t" by blast
  then have "interp_trace (5 + k) T (5 + z)" by (simp add: algebra_simps)
  with * show ?case by fastforce
qed

(* corollary bigstep_trace_endE:
  assumes "f \<turnstile> (c,s) \<Rightarrow>\<^bsup>z :: nat\<^esup> t"
  obtains k T where "interp_trace k T z" "f \<turnstile> (c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> t"
  using bigstep_trace_end assms by blast *)


(* relating partial and full traces *)

lemma trace_leaf_no_tail_trace_end:
  assumes "(c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l)" "\<not> l"
  shows "f \<turnstile> (c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> t"
using assms by (induction rule: ttrace_to_leaf_induct) blast+

lemma trace_leaf_tail_trace_end:
  assumes "(c1,s1) \<Rightarrow>\<^bsup>(k1, T1)\<^esup> (s2, l)" "l"
  assumes "c2 \<turnstile> (c2,s2) \<Rightarrow>\<^bsup>(k2, T2)\<^esup> s3"
  shows "c2 \<turnstile> (c1,s1) \<Rightarrow>\<^bsup>(k1 + k2, T1 @ T2)\<^esup> s3"
using assms proof (induction rule: ttrace_to_leaf_induct)
  case tSeq
  with trace_leaf_no_tail_trace_end show ?case by fastforce
next
  case tIfTrue
  then show ?case by fastforce
next
  case tIfFalse
  then show ?case by fastforce
next
  case tTail
  then show ?case by fastforce
qed simp_all


lemma trace_end_nontail_trace_leaf:
  assumes "f \<turnstile> (c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> t" "\<not> tails c"
  shows "(c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, False)"
using assms proof (induction rule: ttrace_to_end_induct)
  case tSkip
  show ?case by blast
next
  case tAssign
  then show ?case by blast
next
  case tSeq
  then show ?case by auto
next
  case tIfTrue
  then show ?case by auto
next
  case tIfFalse
  then show ?case by auto
next
  case tCall
  then show ?case by blast
next
  case tTail then show ?case by auto
qed

lemma trace_end_trace_leaf:
  assumes "f \<turnstile> (c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> s'"
  assumes "invar c"
  shows "\<exists>k1 T1 s2 l.
    (c,s) \<Rightarrow>\<^bsup>(k1, T1)\<^esup> (s2, l)
    \<and> (if l then (\<exists>k2 T2. f \<turnstile> (f,s2) \<Rightarrow>\<^bsup>(k2, T2)\<^esup> s' \<and> k = k1 + k2 \<and> k1 \<ge> 5 \<and> T = T1 @ T2)
            else k1 = k \<and> T1 = T \<and> s2 = s')"
using assms proof (induction rule: ttrace_to_end_induct)
  case tSkip
  show ?case by fastforce
next
  case tAssign
  show ?case by fastforce
next
  case (tSeq c c1 s1 k1 T1 s2 c2 k2 T2 s' k T)
  from tSeq trace_end_nontail_trace_leaf have 1: "(c1, s1) \<Rightarrow>\<^bsup>(k1, T1)\<^esup> (s2, False)" by simp
  with tSeq.prems tSeq.IH(2) obtain k2a k2b T2a T2b s3a l
      where 2: "(c2, s2) \<Rightarrow>\<^bsup>(k2a, T2a)\<^esup> (s3a, l)"
        and *:
          "if l then c \<turnstile>(c, s3a) \<Rightarrow>\<^bsup>(k2b, T2b)\<^esup> s' \<and> k2 = k2a + k2b \<and> k2a \<ge> 5 \<and> T2 = T2a @ T2b
           else k2a = k2 \<and> T2a = T2 \<and> s3a = s'"
    by fastforce

  show ?case
  proof (rule exI conjI)+
    from 1 2 show "(c1;; c2, s1) \<Rightarrow>\<^bsup>(k1 + k2a, T1 @ T2a)\<^esup>  (s3a, l)" by blast
  next
    have "l \<Longrightarrow> c \<turnstile>(c, s3a) \<Rightarrow>\<^bsup>(k2b, T2b)\<^esup> s' \<and> k = k1 + k2a + k2b \<and> k1 + k2a \<ge> 5 \<and> T = (T1 @ T2a) @ T2b"
      using * tSeq.hyps by fastforce
    then show
      "if l then \<exists>k2 T2. c \<turnstile>(c, s3a) \<Rightarrow>\<^bsup>(k2, T2)\<^esup>  s' \<and> k = k1 + k2a + k2 \<and> k1 + k2a \<ge> 5 \<and> T = (T1 @ T2a) @ T2
       else k1 + k2a = k \<and> T1 @ T2a = T \<and> s3a = s'"
      using * tSeq.hyps by simp
  qed
next
  case (tIfTrue s b c c1 k T s' k' c2)
  then obtain k1 T1 s2 l k2 T2
    where 1: "(c1, s) \<Rightarrow>\<^bsup>(k1, T1)\<^esup> (s2, l)"
      and *: "if l then c \<turnstile>(c, s2) \<Rightarrow>\<^bsup>(k2, T2)\<^esup> s' \<and> k = k1 + k2 \<and> k1 \<ge> 5 \<and> T = T1 @ T2
               else k1 = k \<and> T1 = T \<and> s2 = s'"
    by fastforce

  show ?case
  proof (rule exI conjI)+
    from 1 tIfTrue show "(IF b\<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup>(k1 + 1, T1)\<^esup>  (s2, l)" by blast
  next
    have "l \<Longrightarrow> c \<turnstile>(c, s2) \<Rightarrow>\<^bsup>(k2, T2)\<^esup>  s' \<and> k' = k1 + 1 + k2 \<and> k1 + 1 \<ge> 5 \<and> T = T1 @ T2"
      using * tIfTrue by simp
    then show
      "if l then \<exists>k2 T2. c \<turnstile>(c, s2) \<Rightarrow>\<^bsup>(k2, T2)\<^esup>  s' \<and> k' = k1 + 1 + k2 \<and> k1 + 1 \<ge> 5 \<and> T = T1 @ T2
       else k1 + 1 = k' \<and> T1 = T \<and> s2 = s'"
      using * tIfTrue by force
  qed
next
  case (tIfFalse s b c c2 k T s' k' c1)
  then obtain k1 T1 s2 l k2 T2
    where 1: "(c2, s) \<Rightarrow>\<^bsup>(k1, T1)\<^esup> (s2, l)"
      and *: "if l then c \<turnstile>(c, s2) \<Rightarrow>\<^bsup>(k2, T2)\<^esup> s' \<and> k = k1 + k2 \<and> k1 \<ge> 5 \<and> T = T1 @ T2
               else k1 = k \<and> T1 = T \<and> s2 = s'"
    by fastforce

  show ?case
  proof (rule exI conjI)+
    from 1 tIfFalse show "(IF b\<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup>(k1 + 1, T1)\<^esup>  (s2, l)" by blast
  next
    have "l \<Longrightarrow> c \<turnstile>(c, s2) \<Rightarrow>\<^bsup>(k2, T2)\<^esup>  s' \<and> k' = k1 + 1 + k2 \<and> k1 + 1 \<ge> 5 \<and> T = T1 @ T2"
      using * tIfFalse by simp
    then show
      "if l then \<exists>k2 T2. c \<turnstile>(c, s2) \<Rightarrow>\<^bsup>(k2, T2)\<^esup>  s' \<and> k' = k1 + 1 + k2 \<and> k1 + 1 \<ge> 5 \<and> T = T1 @ T2
       else k1 + 1 = k' \<and> T1 = T \<and> s2 = s'"
      using * tIfFalse by force
  qed
next
  case (tCall C s z t c r)
  then have "(CALL C RETURN r, s) \<Rightarrow>\<^bsup>(0, [(C, s)])\<^esup>  (s(r := t r), False)" by blast
  then show ?case by metis
next
  case (tTail c s k T s' k')

  show ?case proof (rule exI conjI)+
    show "(tTAIL, s) \<Rightarrow>\<^bsup>(5, [])\<^esup> (s, True)" by blast
  next
    from tTail.hyps show
      "if True then \<exists>k2 T2. c \<turnstile>(c, s) \<Rightarrow>\<^bsup>(k2, T2)\<^esup>  s' \<and> k' = 5 + k2 \<and> (5 :: nat) \<le> 5 \<and> T = [] @ T2
       else 5 = k' \<and> [] = T \<and> s = s'" by simp
  qed
qed

end
