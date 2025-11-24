theory HOL_TCN_To_IMP_Temp
  imports HOL_Nat_To_IMP.IMP_Terminates_With "IMP.HOL_TCN_To_IMP" (* HOL_Nat_To_IMP.Compile_HOL_Nat_To_IMP *)
(* TODO: rearrange import of stuff from Compile *)

  HOL_To_IMP_Primitives
  (* only for stuff that should be in IMP_Terminates_With, TODO: fix here once that's done *)
begin


type_synonym state = IMP_Base.state (* TODO *)

abbreviation (input) lookups where "lookups names (s :: state) \<equiv> map s names"
abbreviation "lookup_args crgt g \<equiv> lookups (args_from_crgt crgt g)"

(* note: lookups xs s = map s xs *)
lemma map_eq_on_subset_eq: fixes A assumes "set xs \<subseteq> A" "f = g on A" shows "map f xs = map g xs"
  using assms unfolding eq_on_def by (induction xs) auto

section \<open>Compiler invariant (type checking)\<close>

abbreviation disjoint :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"  (infix \<open>\<inter>\<^sub>\<emptyset>\<close> 60)
  where "A \<inter>\<^sub>\<emptyset> B \<equiv> A \<inter> B = {}" for A B

lemma disjoint_subset2:
  fixes A B
  assumes "B \<subseteq> B'"
  assumes "A \<inter>\<^sub>\<emptyset> B'"
  shows "A \<inter>\<^sub>\<emptyset> B"
  using assms by blast

(* todo: move *)
lemma fresh_not_in_stale_subset[intro]: assumes "stale' \<subseteq> set stale" shows "fresh stale name \<notin> stale'"
  using fresh_not_in_stale assms by blast

(*
- Register lists that are written to must be distinct, otherwise writing a later register will
  overwrite a register earlier in the list. Thus, f_args and g_args for each called g must be
  distinct: f_args is written before a tail call, g_args on a call to g.

- If a value is stored to a register (list) R, then later the register (list) W is written to, and
  then later that value should be read back from R, R and W must be disjoint.
  Otherwise, the write to W could overwrite the value in R. We consider "f_args" and "bs" to be
  stored at the beginning of execution, and "keep" and "r" to be read after execution. We have:

  - f_args: stored at the beginning of execution, written while preparing for a tail call, read at argument variable read
  - bs: stored at the beginning of execution, read at bound variable read
  - g_args for each call of a function g: written and then immediately read by the called function.
  - g_ret for each call of a function g: written after the call and the immediately read for copying.
  - r: written immediately before the end of execution, read after execution
  - keep: stored before execution, read after execution.

  Conflict matrix:

         W: f_args bs g_args g_ret r
    R:     +------------------------
    f_args |        -      X     X -
    bs     |     X         X     X -
    g_args |     -  -      -     - -
    g_ret  |     -  -      -     - -
    r      |     -  -      -     - -
    keep   |     X  -      X     X X

  We special-case the keep/r conflict: instead of requiring keep and r to be disjoint, the
  correctness theorems show that "keep" except "r" is preserved.

- At each (tail and plain) call site, the correct number of arguments must be provided to the called function.

Note that this is not the *weakest* possible invariant, but that would
significantly complicate the invariant with no obvious benefit.
*)


inductive check_arg_count :: "(nat \<times> com_registry) \<Rightarrow> thol \<Rightarrow> bool" ("_ \<turnstile> _") where
  hLetBound: "_ \<turnstile> hLetBound _" | hArg: "_ \<turnstile> hArg _" | hNumber: "_ \<turnstile> hNumber _" |
  hLet: "\<lbrakk>(n, crgt) \<turnstile> t1; (n, crgt) \<turnstile> t2\<rbrakk> \<Longrightarrow> (n, crgt) \<turnstile> LET t1 IN t2" |
  hIf: "\<lbrakk>(n, crgt) \<turnstile> t1; (n, crgt) \<turnstile> t2; (n, crgt) \<turnstile> t3\<rbrakk> \<Longrightarrow> (n, crgt) \<turnstile> IF t1\<noteq>0 THEN t2 ELSE t3" |
  hCall: "\<lbrakk>length ts = length (args_from_crgt crgt g); \<forall>t \<in> set ts. (n, crgt) \<turnstile> t\<rbrakk> \<Longrightarrow> (n, crgt) \<turnstile> hCall g ts" |
  hTail: "\<lbrakk>length ts = n; \<forall>t \<in> set ts. (n, crgt) \<turnstile> t\<rbrakk> \<Longrightarrow> (n, crgt) \<turnstile> hTAIL ts"

declare check_arg_count.intros[intro]
lemmas check_arg_count_induct = check_arg_count.induct[split_format(complete)]
code_pred [show_modes] check_arg_count .

inductive_cases hLet_check_arg_count_case [elim!]: "(n, crgt) \<turnstile> LET t1 IN t2"
inductive_cases hIf_check_arg_count_case [elim!]: "(n, crgt) \<turnstile> IF t1\<noteq>0 THEN t2 ELSE t3"
inductive_cases hCall_check_arg_count_case [elim!, rule_format]: "(n, crgt) \<turnstile> hCall g ts"
inductive_cases hTail_check_arg_count_case [elim!, rule_format]: "(n, crgt) \<turnstile> hTAIL ts"


definition "check_call crgt L f \<equiv>
  set (args_from_crgt crgt f) \<inter>\<^sub>\<emptyset> L \<and> ret_from_crgt crgt f \<notin> L \<and> distinct (args_from_crgt crgt f)"

lemma check_callI[intro]:
  assumes "set (args_from_crgt crgt f) \<inter>\<^sub>\<emptyset> L" "ret_from_crgt crgt f \<notin> L" "distinct (args_from_crgt crgt f)"
  shows "check_call crgt L f"
  using assms unfolding check_call_def by blast

lemma check_callE[dest]:
  assumes "check_call crgt L f"
  assumes "\<lbrakk>set (args_from_crgt crgt f) \<inter>\<^sub>\<emptyset> L; ret_from_crgt crgt f \<notin> L; distinct (args_from_crgt crgt f)\<rbrakk> \<Longrightarrow> P"
  shows P
  using assms unfolding check_call_def by blast

lemma check_callD[dest]:
  assumes "check_call crgt L f"
  shows "set (args_from_crgt crgt f) \<inter>\<^sub>\<emptyset> L" "ret_from_crgt crgt f \<notin> L" "distinct (args_from_crgt crgt f)"
  using assms unfolding check_call_def by blast+

lemma check_call_union:
  assumes "check_call crgt L1 f" "check_call crgt L2 f"
  shows "check_call crgt (L1 \<union> L2) f"
  using assms by auto

abbreviation "check_args f_args bs keep \<equiv>
  distinct f_args \<and> set bs \<inter>\<^sub>\<emptyset> set f_args \<and> set keep \<inter>\<^sub>\<emptyset> set f_args"

abbreviation "check_term crgt f_args bs keep t \<equiv>
  (length f_args, crgt) \<turnstile> t \<and>
  (\<forall>g \<in> calls_names_set t. check_call crgt (set f_args \<union> set bs \<union> set keep) g)"

definition "check_compile crgt f_args bs keep t \<equiv>
  check_args f_args bs keep \<and> check_term crgt f_args bs keep t"

lemma check_compileI[intro]:
  assumes
    "distinct f_args" "set bs \<inter>\<^sub>\<emptyset> set f_args" "set keep \<inter>\<^sub>\<emptyset> set f_args"
    "(length f_args, crgt) \<turnstile> t"
    "\<And>g. g \<in> calls_names_set t \<Longrightarrow> check_call crgt (set f_args \<union> set bs \<union> set keep) g"
  shows "check_compile crgt f_args bs keep t"
  unfolding check_compile_def using assms by blast

lemma check_compileE[elim]:
  assumes "check_compile crgt f_args bs keep t"
  assumes
    "\<lbrakk>distinct f_args; set bs \<inter>\<^sub>\<emptyset> set f_args; set keep \<inter>\<^sub>\<emptyset> set f_args;
      (length f_args, crgt) \<turnstile> t;
      (\<And>g. g \<in> calls_names_set t \<Longrightarrow> check_call crgt (set f_args \<union> set bs \<union> set keep) g)\<rbrakk> \<Longrightarrow> P"
  shows P
  using assms unfolding check_compile_def by blast

lemma check_compileD[dest]:
  assumes "check_compile crgt f_args bs keep t"
  shows
    "distinct f_args" "set bs \<inter>\<^sub>\<emptyset> set f_args" "set keep \<inter>\<^sub>\<emptyset> set f_args"
    "(length f_args, crgt) \<turnstile> t"
    "\<And>g. g \<in> calls_names_set t \<Longrightarrow> check_call crgt (set f_args \<union> set bs \<union> set keep) g"
  using assms unfolding check_compile_def by blast+

(* TODO: lots of *_E[elim] rules lying around, that (I think?) should actually be *_D[dest] \<rightarrow> fix *)


lemma check_compile_fresh:
  assumes check: "check_compile crgt f_args bs keep t"
  assumes bs: "set bs' \<inter>\<^sub>\<emptyset> set (stale_registers f_args crgt bs keep t)"
  assumes keep: "set keep' \<inter>\<^sub>\<emptyset> set (stale_registers f_args crgt bs keep t)"
  shows "check_compile crgt f_args (bs' @ bs) (keep' @ keep) t"
proof -
  have *: "set bs' \<inter>\<^sub>\<emptyset> set f_args" "set keep'  \<inter>\<^sub>\<emptyset> set f_args"
    using bs keep unfolding stale_registers_def by auto

  show "check_compile crgt f_args (bs' @ bs) (keep' @ keep) t"
  proof (rule check_compileI)
    show "distinct f_args" "(length f_args, crgt) \<turnstile> t" using check by auto
    show "set (bs' @ bs) \<inter>\<^sub>\<emptyset> set f_args" "set (keep' @ keep) \<inter>\<^sub>\<emptyset> set f_args" using * check by auto
  next
    fix g assume g: "g \<in> calls_names_set t"

    have 1: "set bs' \<inter>\<^sub>\<emptyset> set (args_from_crgt crgt g) \<union> {ret_from_crgt crgt g}"
      apply (rule disjoint_subset2[OF _ bs])
      unfolding stale_registers_def call_registers_def using g by force
    have 2: "set keep' \<inter>\<^sub>\<emptyset> set (args_from_crgt crgt g) \<union> {ret_from_crgt crgt g}"
      apply (rule disjoint_subset2[OF _ keep])
      unfolding stale_registers_def call_registers_def using g by force

    have "check_call crgt ((set bs' \<union> set keep') \<union> (set f_args \<union> set bs \<union> set keep)) g"
    proof (rule check_call_union[OF check_callI])
      show "set (args_from_crgt crgt g) \<inter>\<^sub>\<emptyset> set bs' \<union> set keep'" using 1 2 by blast
      show "ret_from_crgt crgt g \<notin> set bs' \<union> set keep'" using 1 2 by blast
    next
      show "distinct (args_from_crgt crgt g)" "check_call crgt (set f_args \<union> set bs \<union> set keep) g"
        using g check by blast+
    qed
    then show "check_call crgt (set f_args \<union> set (bs' @ bs) \<union> set (keep' @ keep)) g" by auto
  qed
qed

lemma check_compile_let:
  fixes crgt f_args bs keep t1 t2
  assumes check_compile: "check_compile crgt f_args bs keep (LET t1 IN t2)"
  defines "r \<equiv> fresh' (stale_registers f_args crgt bs keep LET t1 IN t2) ''Let.x''"
  shows "check_compile crgt f_args (r # bs) (r # keep) t2"
proof -
  from check_compile have check_t2: "check_compile crgt f_args bs keep t2"
    using check_compileE check_compileI by auto

  have r: "r \<notin> set (stale_registers f_args crgt bs keep t2)"
  proof (rule contra_subsetD)
    show "r \<notin> set (stale_registers f_args crgt bs keep LET t1 IN t2)"
      unfolding r_def using fresh_not_in_stale by blast
    show "set (stale_registers f_args crgt bs keep t2) \<subseteq> set (stale_registers f_args crgt bs keep LET t1 IN t2)"
      using stale_registers_def call_registers_def by auto
  qed

  from check_compile_fresh[where bs' = "[r]" and keep' = "[r]"] check_t2 r show ?thesis by simp
qed

lemma check_compile_call:
  fixes f_args crgt bs keep gr ts
  assumes check_compile: "check_compile crgt f_args bs keep (hCall gr ts)"
  defines "xs \<equiv> make_n_fresh (stale_registers f_args crgt bs keep (hCall gr ts)) ''Call.x.'' (length ts)"
  assumes t: "t \<in> set ts"
  shows "check_compile crgt f_args bs (xs @ keep) t"
proof -
  have t_calls: "g \<in> calls_names_set t \<Longrightarrow> g \<in> calls_names_set (hCall gr ts)" for g using t by auto
  have check_t: "check_compile crgt f_args bs keep t"
    apply (rule check_compileI)
    using check_compileD[OF check_compile] check_compile t t_calls by auto

  have xs: "set xs \<inter>\<^sub>\<emptyset> set (stale_registers f_args crgt bs keep t)"
  proof (rule disjoint_subset2)
    show "set xs \<inter>\<^sub>\<emptyset> set (stale_registers f_args crgt bs keep (hCall gr ts))"
      unfolding xs_def using make_n_fresh_not_in_stale by blast
    show "set (stale_registers f_args crgt bs keep t) \<subseteq> set (stale_registers f_args crgt bs keep (hCall gr ts))"
      unfolding stale_registers_def call_registers_def using t by auto
  qed

  from check_compile_fresh[where bs' = "[]" and keep' = xs] check_t xs show ?thesis by simp
qed

lemma check_compile_tail:
  fixes f_args crgt bs keep gr ts
  assumes check_compile: "check_compile crgt f_args bs keep (hTAIL ts)"
  defines "xs \<equiv> make_n_fresh (stale_registers f_args crgt bs keep (hTAIL ts)) ''TAIL.x.'' (length ts)"
  assumes t: "t \<in> set ts"
  shows "check_compile crgt f_args bs (xs @ keep) t"
proof -
  have t_calls: "g \<in> calls_names_set t \<Longrightarrow> g \<in> calls_names_set (hTAIL ts)" for g using t by auto
  have check_t: "check_compile crgt f_args bs keep t"
    apply (rule check_compileI)
    using check_compileD[OF check_compile] check_compile t t_calls by auto

  have xs: "set xs \<inter>\<^sub>\<emptyset> set (stale_registers f_args crgt bs keep t)"
  proof (rule disjoint_subset2)
    show "set xs \<inter>\<^sub>\<emptyset> set (stale_registers f_args crgt bs keep (hTAIL ts))"
      unfolding xs_def using make_n_fresh_not_in_stale by blast
    show "set (stale_registers f_args crgt bs keep t) \<subseteq> set (stale_registers f_args crgt bs keep (hTAIL ts))"
      unfolding stale_registers_def call_registers_def using t by auto
  qed

  from check_compile_fresh[where bs' = "[]" and keep' = xs] check_t xs show ?thesis by simp
qed


section \<open>Notions of trace relatedness\<close>

(* the "state" of the HOL-TCN execution (args, bounds) is related
   to the state of the IMP-TC execution *)
definition "relate_exec_state f_args bs vs_arg vs_b s \<longleftrightarrow>
  lookups f_args s = vs_arg \<and> lookups bs s = vs_b"

definition "relate_rgt_correctness frgt crgt fs \<longleftrightarrow> (\<forall>f \<in> fs.
  \<forall>s. terminates_with_res_IMP (com_from_crgt crgt f) s (ret_from_crgt crgt f) (f_from_frgt frgt f (lookup_args crgt f s)))"


definition rel_trace_call :: "com_registry \<Rightarrow> fun_ref \<Rightarrow> nat list \<Rightarrow> com \<Rightarrow> state \<Rightarrow> bool" where
  "rel_trace_call crgt gr gargs gcom gs \<longleftrightarrow> com_from_crgt crgt gr = gcom \<and> lookup_args crgt gr gs = gargs"

definition rel_trace_calls :: "com_registry \<Rightarrow> HOL_TCN_Timing.call_trace \<Rightarrow> IMP_Tailcall_Traces.call_trace \<Rightarrow> bool" where
  "rel_trace_calls crgt hT cT \<longleftrightarrow>
    length hT = length cT \<and>
    list_all (\<lambda>((gr,gargs),(gcom,gs)). rel_trace_call crgt gr gargs gcom gs) (zip hT cT)"

fun rel_leaf_state :: "com_registry \<Rightarrow> vname list \<Rightarrow> vname \<Rightarrow> leaf_state \<Rightarrow> state \<Rightarrow> bool \<Rightarrow> bool" where
  "rel_leaf_state crgt _      r (Value v) s l \<longleftrightarrow> \<not> l \<and> s       r        = v " |
  "rel_leaf_state crgt f_args _ (Tail vs) s l \<longleftrightarrow>   l \<and> lookups f_args s = vs"

definition rel_trace_to_leaf ::
    "com_registry \<Rightarrow> vname list \<Rightarrow> vname \<Rightarrow>
      HOL_TCN_Timing.call_trace \<Rightarrow> leaf_state \<Rightarrow>
        IMP_Tailcall_Traces.call_trace \<Rightarrow> state \<Rightarrow> bool \<Rightarrow> bool" where
  "rel_trace_to_leaf crgt f_args r hT hl cT s cl \<longleftrightarrow>
    rel_trace_calls crgt hT cT \<and> rel_leaf_state crgt f_args r hl s cl"

definition rel_trace_to_end where
  "rel_trace_to_end crgt r hT v cT s \<longleftrightarrow>
    rel_trace_calls crgt hT cT \<and> s r = v"

lemma rel_trace_to_leaf_cl:
  shows "rel_trace_to_leaf crgt f_args r hT (Value v) cT s cl \<Longrightarrow> \<not> cl"
    and "rel_trace_to_leaf crgt f_args r hT (Tail vs) cT s cl \<Longrightarrow> cl"
  unfolding rel_trace_to_leaf_def by simp_all

(* concatenating traces *)

lemma rel_trace_calls_append:
  assumes "rel_trace_calls crgt hT1 cT1"
  assumes "rel_trace_calls crgt hT2 cT2"
  shows "rel_trace_calls crgt (hT1 @ hT2) (cT1 @ cT2)" using assms unfolding rel_trace_calls_def by simp

lemma rel_trace_to_leaf_append:
  assumes "rel_trace_calls crgt hT1 cT1"
  assumes "rel_trace_to_leaf crgt f_args r hT2 hl cT2 s cl"
  shows "rel_trace_to_leaf crgt f_args r (hT1 @ hT2) hl (cT1 @ cT2) s cl"
  using assms rel_trace_calls_append unfolding rel_trace_to_leaf_def by auto

lemma rel_trace_to_end_append:
  assumes "rel_trace_calls crgt hT1 cT1"
  assumes "rel_trace_to_end crgt r hT2 v cT2 s"
  shows "rel_trace_to_end crgt r (hT1 @ hT2) v (cT1 @ cT2) s"
  using assms rel_trace_calls_append unfolding rel_trace_to_end_def by auto

(* relating partial and full traces *)

lemma rel_trace_to_leaf_value_rel_trace_to_end:
  "rel_trace_to_leaf crgt f_args r hT (Value v) cT s False \<longleftrightarrow> rel_trace_to_end crgt r hT v cT s"
  unfolding rel_trace_to_leaf_def rel_trace_to_end_def by simp


section \<open>Relating partial traces\<close>

lemma snoc_list_induct2 [case_names len Nil snoc]:
  assumes len: "length xs = length ys"
  assumes nil: "P [] []"
  assumes snoc: "\<And>xs x ys y. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (xs @ [x]) (ys @ [y])"
  shows "P xs ys"
proof -
  let ?P = "\<lambda>xs ys. P (rev xs) (rev ys)"
  have "length (rev xs) = length (rev ys)" using len by simp
  then have "?P (rev xs) (rev ys)"
  proof (induction rule: list_induct2)
  qed (simp_all add: nil snoc)
  then show "P xs ys" by simp
qed


(* argument lists are defined in terms of regular lists, but proofs are far easier on nat \<rightarrow> 'a functions,
    so we work with those instead; conceptually the pair (x, n) represents the variables x_0,...,x_n-1 *)

(* x_0,..x_n-1 are disjoint from y_0..y_m-1 *)
abbreviation "disjoint_v x n y m \<equiv> (\<And>i j. \<lbrakk>i < n; j < m\<rbrakk> \<Longrightarrow> x i \<noteq> y j)"

(* x_0,..x_n-1 are distinct *)
abbreviation "distinct_v x n \<equiv> (\<And>i j. \<lbrakk>i < n; j < n; i \<noteq> j\<rbrakk> \<Longrightarrow> x i \<noteq> x j)"

(* {x_0,..x_n-1} \<subseteq> A *)
abbreviation "subset_v x n A \<equiv> (\<And>i. i < n \<Longrightarrow> x i \<in> A)" for A

(* {x_0,..x_n-1} \<inter>\<^sub>\<emptyset> A *)
abbreviation "disjoint_from_v x n A \<equiv> (\<And>i. i < n \<Longrightarrow> x i \<notin> A)" for A

(* inputs *)

lemma distinct_v:
  assumes "distinct xs"
  shows "PROP distinct_v (nth xs) (length xs)"
  using assms nth_eq_iff_index_eq by blast

lemma disjoint_v:
  assumes "set xs \<inter>\<^sub>\<emptyset> set ys"
  shows "PROP disjoint_v (nth xs) (length xs) (nth ys) (length ys)"
  using assms by (simp add: disjoint_iff_not_equal)

lemma subset_v:
  fixes A
  assumes "set xs \<subseteq> A"
  shows "PROP subset_v (nth xs) (length xs) A"
  using assms by auto

lemma disjoint_from_v:
  fixes A
  assumes "set xs \<inter>\<^sub>\<emptyset> A"
  shows "PROP disjoint_from_v (nth xs) (length xs) A"
  apply (rule ccontr) using assms by force

(* outputs *)

lemma lookups_v:
  assumes "length xs = length ys"
  assumes "\<And>i. i < length xs \<Longrightarrow> f (xs ! i) = g (ys ! i)"
  shows "map f xs = map g ys"
proof -
  have "map f (map (nth xs) [0..<length xs]) = map g (map (nth ys) [0..<length ys])" using assms by simp
  then show ?thesis by (simp only: map_nth)
qed

lemma lookups_v_list:
  assumes "length xs = length ys"
  assumes "\<And>i. i < length xs \<Longrightarrow> f (xs ! i) = ys ! i"
  shows "map f xs = ys"
  using assms lookups_v[where g = Fun.id, simplified] by blast

lemma eq_on_v_except:
  fixes A
  assumes "\<And>x. x \<in> A \<Longrightarrow> (\<And>i. i < length xs \<Longrightarrow> x \<noteq> xs ! i) \<Longrightarrow> f x = g x"
  shows "f = g on A - set xs"
proof (rule eq_onI)
  fix x assume "x \<in> A - set xs"
  then have "x \<in> A" "x \<notin> set xs" by simp_all
  moreover then have "i < length xs \<Longrightarrow> x \<noteq> xs ! i" for i by fastforce
  ultimately show "f x = g x" using assms by blast
qed

lemma eq_on_v_complement:
  assumes "\<And>x. (\<And>i. i < length xs \<Longrightarrow> x \<noteq> xs ! i) \<Longrightarrow> f x = g x"
  shows "f = g on - set xs"
proof (rule eq_onI)
  fix x assume "x \<in> - set xs"
  then have "i < length xs \<Longrightarrow> x \<noteq> xs ! i" for i by auto
  with assms show "f x = g x" by blast
qed

(* executing a list of terms (as in the call and tail-call cases) *)
lemma compiled_arguments_trace:
  assumes args:
    "PROP distinct_v x n" "PROP subset_v x n (set keep)"
    "PROP disjoint_from_v x n (set f_args)" "PROP disjoint_from_v x n (set bs)"
  assumes trace: "\<And>i. i < n \<Longrightarrow> frgt \<turnstile> (t i, vs_b, vs_arg) \<Rightarrow>\<^bsup>hT i\<^esup> Value (v i)"
  assumes rel_state: "relate_exec_state f_args bs vs_arg vs_b s"
  assumes step:
    "\<And>i s. \<lbrakk> i < n; relate_exec_state f_args bs vs_arg vs_b s \<rbrakk> \<Longrightarrow>
      \<exists>k cT s'.
        (to_imp_tc f_args crgt bs (x i) keep (t i), s) \<Rightarrow>\<^bsup>(k, cT)\<^esup>  (s', False) \<and>
        rel_trace_to_leaf crgt f_args (x i) (hT i) (Value (v i)) cT s' False \<and>
        (\<forall>y \<in> set f_args \<union> set bs \<union> set keep. y \<noteq> x i \<longrightarrow> s' y = s y)"
  shows
    "\<exists>k cT s'.
      (mk_seqs (generate (\<lambda>i. to_imp_tc f_args crgt bs (x i) keep (t i)) n), s) \<Rightarrow>\<^bsup>(k, cT)\<^esup> (s', False) \<and>
      rel_trace_calls crgt (concat (map hT [0..<n])) cT \<and>
      (\<forall>i < n. s' (x i) = v i) \<and>
      (\<forall>y \<in> set f_args \<union> set bs \<union> set keep. (\<forall>i < n. y \<noteq> x i) \<longrightarrow> s' y = s y)"
using args trace step proof (induction n rule: induct_nat_012)
  case 0
  then show ?case
    unfolding generate_def rel_trace_calls_def by auto
next
  case 1
  with rel_state show ?case
    unfolding generate_def rel_trace_to_leaf_def by simp
next
  case (ge2 n)
  let ?n = "Suc n" and ?n' = "Suc (Suc n)"
  let ?cs = "\<lambda>n. generate (\<lambda>i. to_imp_tc f_args crgt bs (x i) keep (t i)) n"

  (* first n terms *)

  from ge2.prems ge2.IH(2) obtain k1 cT1 s2 where trace1[rule_format]:
      "(mk_seqs (?cs ?n), s) \<Rightarrow>\<^bsup>(k1, cT1)\<^esup>  (s2, False)"
      "rel_trace_calls crgt (concat_map hT [0..<?n]) cT1"
      "\<forall>i < ?n. s2 (x i) = v i"
      "\<forall>y\<in>set f_args \<union> set bs \<union> set keep. (\<forall>i<?n. y \<noteq> x i) \<longrightarrow> s2 y = s y"
    by simp blast

  from rel_state trace1(4) ge2.prems(3,4) have rel_state': "relate_exec_state f_args bs vs_arg vs_b s2"
    unfolding relate_exec_state_def by fastforce

  (* term n + 1 *)

  let ?c' = "to_imp_tc f_args crgt bs (x ?n) keep (t ?n)"

  from ge2.prems(6)[where i = ?n, OF _ rel_state'] obtain k2 cT2 s3 where trace2[rule_format]:
      "(?c', s2) \<Rightarrow>\<^bsup>(k2, cT2)\<^esup> (s3, False)"
      "rel_trace_to_leaf crgt f_args (x ?n) (hT ?n) (Value (v ?n)) cT2 s3 False"
      "\<forall>y\<in>set f_args \<union> set bs \<union> set keep. y \<noteq> x ?n \<longrightarrow> s3 y = s2 y"
    by blast

  show ?case
  proof (repeat \<open>rule exI conjI allI impI\<close>)
    show "(mk_seqs (?cs ?n'), s) \<Rightarrow>\<^bsup>(k1 + k2, cT1 @ cT2)\<^esup>  (s3, False)"
    proof (rule same_linearize_trace_leaf[THEN iffD1])
      from trace1 trace2 show "(mk_seqs (?cs ?n);; ?c', s) \<Rightarrow>\<^bsup>(k1 + k2, cT1 @ cT2)\<^esup>  (s3, False)" by blast
      show "linearize (mk_seqs (?cs ?n);; ?c') = linearize (mk_seqs (?cs ?n'))" unfolding generate_def by simp
    qed
  next
    from rel_trace_to_leaf_append[OF trace1(2) trace2(2)]
    show "rel_trace_calls crgt (concat_map hT [0..<Suc (Suc n)]) (cT1 @ cT2)"
      unfolding rel_trace_to_leaf_def by simp
  next
    fix i assume *: "i < ?n'"
    then consider "i < ?n" | "i = ?n" by linarith
    then show "s3 (x i) = v i"
      using ge2.prems(1,2) trace2(2,3) trace1(3) unfolding rel_trace_to_leaf_def by cases simp_all
  next
    show "\<forall>y\<in>set f_args \<union> set bs \<union> set keep. (\<forall>i<Suc (Suc n). y \<noteq> x i) \<longrightarrow> s3 y = s y"
      using trace2(3) trace1(4) by simp
  qed
qed

lemma compiled_arguments_trace':
  assumes lengths: "length vs = length ts" "length xs = length ts" "length hTs = length ts"
  assumes args: "distinct xs" "set xs \<subseteq> set keep" "set xs \<inter>\<^sub>\<emptyset> set f_args" "set xs \<inter>\<^sub>\<emptyset> set bs"
  assumes trace: "\<And>i. i < length ts \<Longrightarrow> frgt \<turnstile> (ts ! i, vs_b, vs_arg) \<Rightarrow>\<^bsup>hTs ! i\<^esup>  Value (vs ! i)"
  assumes rel_state: "relate_exec_state f_args bs vs_arg vs_b s"
  assumes step: "\<And>i s.
    \<lbrakk> i < length ts; relate_exec_state f_args bs vs_arg vs_b s \<rbrakk> \<Longrightarrow>
    \<exists>k cT s'. (to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i), s) \<Rightarrow>\<^bsup>(k, cT)\<^esup>  (s', False) \<and>
              rel_trace_to_leaf crgt f_args (xs ! i) (hTs ! i) (Value (vs ! i)) cT s' False \<and>
              s' = s on set f_args \<union> set bs \<union> set keep - {xs ! i}"
  obtains k cT s' where
    "(mk_seqs (generate (\<lambda>i. to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i)) (length ts)), s) \<Rightarrow>\<^bsup>(k, cT)\<^esup> (s', False)"
    "rel_trace_calls crgt (concat hTs) cT"
    "lookups xs s' = vs"
    "s' = s on set f_args \<union> set bs \<union> set keep - set xs"
proof goal_cases
  case obt: 1

  have step':
    "\<exists>k cT s'.
      (to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i), s) \<Rightarrow>\<^bsup>(k, cT)\<^esup>  (s', False) \<and>
      rel_trace_to_leaf crgt f_args (xs ! i) (hTs ! i) (Value (vs ! i)) cT s' False \<and>
      (\<forall>y \<in> set f_args \<union> set bs \<union> set keep. (y \<noteq> (xs ! i)) \<longrightarrow> s' y = s y)"
    if "i < length ts" "relate_exec_state f_args bs vs_arg vs_b s" for i s
    using step that by blast

  note args' =
    distinct_v[OF args(1)] subset_v[OF args(2)]
    disjoint_from_v[OF args(3)] disjoint_from_v[OF args(4)]

  from compiled_arguments_trace[
      where x = "nth xs" and v = "nth vs" and hT = "nth hTs" and n = "length ts",
      OF args' trace rel_state step']
  obtain k cT s' where trace[rule_format]:
      "(mk_seqs (generate (\<lambda>i. to_imp_tc f_args crgt bs (xs ! i) keep (ts ! i)) (length ts)), s) \<Rightarrow>\<^bsup>(k, cT)\<^esup>  (s', False)"
      "rel_trace_calls crgt (concat_map (nth hTs) [0..<length hTs]) cT"
      "\<forall>i<length xs. s' (xs ! i) = vs ! i"
      "\<forall>y\<in>set f_args \<union> set bs \<union> set keep. (\<forall>i<length xs. y \<noteq> xs ! i) \<longrightarrow> s' y = s y"
    unfolding lengths by blast

  from
    trace(1) trace(2)[simplified map_nth] lookups_v_list[OF _ trace(3), simplified lengths]
    eq_on_v_except[where A = "set f_args \<union> set bs \<union> set keep" and f = s' and g = s and xs = xs, OF trace(4)]
  show ?case using obt by blast
qed


(* copying a list of registers *)
lemma copy_list_trace:
  fixes x y :: "nat \<Rightarrow> vname"
  assumes "PROP distinct_v y n"
  assumes "PROP disjoint_v x n y n"
  shows
    "\<exists>s'. (mk_seqs (generate (\<lambda>i. (y i) ::= A (V (x i))) n), s) \<Rightarrow>\<^bsup>((2 * n)\<^sub>+, [])\<^esup> (s', False) \<and>
          (\<forall>i < n. s' (y i) = s (x i)) \<and> (\<forall>y'. (\<forall>i < n. y' \<noteq> y i) \<longrightarrow> s' y' = s y')"
using assms proof (induction n rule: induct_nat_012)
  case 0
  show ?case proof (rule exI, repeat \<open>rule conjI\<close>)
    show "(mk_seqs (generate (\<lambda>i. (y i) ::= A (V (x i))) 0), s) \<Rightarrow>\<^bsup>((2 * 0)\<^sub>+, [])\<^esup>  (s, False)"
      unfolding generate_def by auto
  qed simp_all
next
  case 1
  show ?case proof (rule exI, repeat \<open>rule conjI\<close>)
    show "(mk_seqs (generate (\<lambda>i. (y i) ::= A (V (x i))) (Suc 0)), s) \<Rightarrow>\<^bsup>((2 * Suc 0)\<^sub>+, [])\<^esup>  ((s(y 0 := s (x 0))), False)"
      unfolding generate_def by auto
  qed (simp_all add: 1)
next
  case (ge2 n)

  let ?cs = "\<lambda>n. generate (\<lambda>i. (y i) ::= A (V (x i)) :: tcom) n"

  let ?n = "Suc n"
  from ge2.IH(2) ge2.prems obtain s2 where trace1[rule_format]:
      "(mk_seqs (?cs ?n), s) \<Rightarrow>\<^bsup>((2 * ?n)\<^sub>+, [])\<^esup> (s2, False)"
      "\<And>i. i < ?n \<Longrightarrow> s2 (y i) = s (x i)"
      "\<And>y'. (\<forall>i < ?n. y' \<noteq> y i) \<longrightarrow> s2 y' = s y'" by auto

  let ?c' = "(y ?n) ::= A (V (x ?n)) :: tcom"
  let ?s3 = "s2(y ?n := s2 (x ?n))"
  have trace2: "(?c', s2) \<Rightarrow>\<^bsup>(Suc (Suc 0), [])\<^esup> (?s3, False)" by auto

  let ?n' = "Suc ?n"

  show ?case
  proof (repeat \<open>rule exI conjI allI impI\<close>)
    show "(mk_seqs (?cs ?n'), s) \<Rightarrow>\<^bsup>((2 * ?n')\<^sub>+, [])\<^esup> (?s3, False)"
    proof (rule same_linearize_trace_leaf[THEN iffD1])
      show "(mk_seqs (?cs ?n);; ?c', s) \<Rightarrow>\<^bsup>((2 * ?n')\<^sub>+, [])\<^esup> (?s3, False)"
        using ttrace_to_leaf.tSeq[OF trace1(1) trace2] by simp
      show "linearize (mk_seqs (?cs ?n);; ?c') = linearize (mk_seqs (?cs ?n'))"
        unfolding generate_def by simp
    qed
  next
    fix i assume "i < ?n'"
    then consider "i < ?n" | "i = ?n" by linarith
    then show "?s3 (y i) = s (x i)"
      using ge2.prems(1,2) trace1(2,3) by cases simp_all
  next
    show "\<And>y'. \<forall>i<?n'. y' \<noteq> y i \<Longrightarrow> ?s3 y' = s y'"
      using trace1(3) by simp
  qed
qed

lemma copy_list_trace':
  assumes lengths: "length xs = n" "length ys = n"
  assumes distinct: "distinct ys"
  assumes disjoint: "set xs \<inter>\<^sub>\<emptyset> set ys"
  obtains s' where
    "(mk_seqs (generate (\<lambda>i. (ys ! i) ::= A (V (xs ! i))) n),s) \<Rightarrow>\<^bsup>((2 * n)\<^sub>+, [])\<^esup> (s', False)"
    "lookups ys s' = lookups xs s" "s' = s on (- set ys)"
proof goal_cases
  case obt: 1
  note distinct' = distinct_v[OF distinct, unfolded lengths]
  note disjoint' = disjoint_v[OF disjoint, unfolded lengths]
  from copy_list_trace[where x = "nth xs" and y = "nth ys" and n = n, OF distinct' disjoint']
  obtain s' where cp:
    "(mk_seqs (generate (\<lambda>i. (ys ! i) ::= A (V (xs ! i))) n), s) \<Rightarrow>\<^bsup>((2 * n)\<^sub>+, [])\<^esup> (s', False)"
    "\<And>i. i < n \<Longrightarrow> s' (ys ! i) = s (xs ! i)" "\<And>y'. (\<And>i. i < n \<Longrightarrow> y' \<noteq> ys ! i) \<Longrightarrow> s' y' = s y'"
    by blast
  note lookups = lookups_v[of ys xs s' s, unfolded lengths, OF refl cp(2)]
  note eq_on = eq_on_v_complement[of ys s' s, unfolded lengths, OF cp(3)]
  from obt[OF cp(1) lookups eq_on] show ?case by blast
qed


(* needed multiple times and slow \<rightarrow> pull out *)
lemma eq_on_drop_fresh:
  assumes "s' = s on set f_args \<union> set bs \<union> set keep - {fresh' (stale_registers f_args crgt bs keep t) name}"
  shows "s' = s on set f_args \<union> set bs \<union> set keep"
  by (smt (verit) DiffI Un_iff eq_on_def fresh_not_in_stale assms set_append singletonD stale_registers_def)

abbreviation "if_is_value l x \<equiv> (case l of Value _ \<Rightarrow> x | _ \<Rightarrow> {})"

theorem compiler_rel_trace_to_leaf:
  assumes "frgt \<turnstile> (t,vs_b,vs_arg) \<Rightarrow>\<^bsup> hT :: HOL_TCN_Timing.call_trace \<^esup> hl"
  assumes "check_compile crgt f_args bs keep t"
  assumes "relate_rgt_correctness frgt crgt (calls_names_set t)"
  assumes "relate_exec_state f_args bs vs_arg vs_b s"
  shows "\<exists>k cT s' cl.
    (to_imp_tc f_args crgt bs r keep t,s)\<Rightarrow>\<^bsup>(k, cT)\<^esup> (s', cl)
    \<and> rel_trace_to_leaf crgt f_args r hT hl cT s' cl
    \<and> s' = s on if_is_value hl (set f_args) \<union> set bs \<union> set keep - {r}"
using assms proof (induction arbitrary: bs keep s r crgt rule: htrace_to_leaf_induct)
  case (hLet frgt t1 vs_b vs_arg T1 v1 t2 T2 l2 T)

  let ?r1 = "fresh' (stale_registers f_args crgt bs keep LET t1 IN t2) ''Let.x''"
  let ?c1 = "to_imp_tc f_args crgt bs ?r1 keep t1"
  let ?c2 = "to_imp_tc f_args crgt (?r1 # bs) r (?r1 # keep) t2"

  (* solve assumptions, and obtain IH for t1 *)

  from hLet.prems(1) have check_compile1: "check_compile crgt f_args bs keep t1"
    using check_compileE check_compileI by auto
  from check_compile_let[OF hLet.prems(1)] have check_compile2:
    "check_compile crgt f_args (?r1 # bs) (?r1 # keep) t2" by blast

  from hLet.prems(2) have rel_rgt:
      "relate_rgt_correctness frgt crgt (calls_names_set t1)"
      "relate_rgt_correctness frgt crgt (calls_names_set t2)"
    unfolding relate_rgt_correctness_def by simp_all

  from hLet.prems(3) have rel_state1: "relate_exec_state f_args bs vs_arg vs_b s" by blast

  from hLet.IH(1)[OF check_compile1 rel_rgt(1) rel_state1, where r = ?r1] rel_trace_to_leaf_cl(1)
  obtain k1 cT1 s2 where ih1:
        "(to_imp_tc f_args crgt bs ?r1 keep t1, s) \<Rightarrow>\<^bsup>(k1, cT1)\<^esup> (s2, False)"
        "rel_trace_to_leaf crgt f_args ?r1 T1 (Value v1) cT1 s2 False"
        "s2 ?r1 = v1" "s2 = s on set f_args \<union> set bs \<union> set keep - {?r1}"
    using rel_trace_to_leaf_def by auto

  (* solve assumptions and obtain IH for t2 *)

  have s2_like_s: "s2 = s on set f_args \<union> set bs \<union> set keep"
    using eq_on_drop_fresh ih1(4) by blast
  then have rel_state2: "relate_exec_state f_args (?r1 # bs) vs_arg (v1 # vs_b) s2"
    using hLet.prems(3) unfolding relate_exec_state_def using ih1(3) by fastforce

  from hLet.IH(2)[OF check_compile2 rel_rgt(2) rel_state2, of r]
  obtain k2 cT2 s3 cl2 where ih2:
      "(?c2,s2)\<Rightarrow>\<^bsup>(k2,cT2)\<^esup> (s3,cl2)"
      "rel_trace_to_leaf crgt f_args r T2 l2 cT2 s3 cl2"
      "s3 = s2 on if_is_value l2 (set f_args) \<union> set (?r1 # bs) \<union> set (?r1 # keep) - {r}" by blast

  (* putting it together *)

  show ?case unfolding to_imp_tc.simps Let_def
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    show "(?c1;; ?c2,s) \<Rightarrow>\<^bsup>(k1 + k2, cT1 @ cT2)\<^esup> (s3, cl2)"
      using ttrace_to_leaf.tSeq ih1(1) ih2(1) by blast
  next
    show "rel_trace_to_leaf crgt f_args r T l2 (cT1 @ cT2) s3 cl2"
      using hLet.hyps(3) rel_trace_to_leaf_append ih1(2) ih2(2)
      unfolding rel_trace_to_leaf_def by blast
  next
    have "s3 = s2 on if_is_value l2 (set f_args) \<union> set bs \<union> set keep - {r}"
      using Un_Diff ih2(3) by auto
    with s2_like_s show "s3 = s on if_is_value l2 (set f_args) \<union> set bs \<union> set keep - {r}"
      by (cases l2) (simp_all add: eq_on_def)
  qed
next
  case (hLetBound n vs_b _ _)
  show ?case
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    have "aval (A (V (bs ! n))) s = vs_b ! n" using hLetBound unfolding relate_exec_state_def by auto
    then show "(to_imp_tc f_args crgt bs r keep (hLetBound n), s) \<Rightarrow>\<^bsup>(Suc (Suc 0), [])\<^esup> (s(r := vs_b ! n), False)"
      unfolding to_imp_tc.simps using ttrace_to_leaf.tAssign by metis
  next
    show "rel_trace_to_leaf crgt f_args r [] (Value (vs_b ! n)) [] (s(r := vs_b ! n)) False"
      unfolding rel_trace_to_leaf_def rel_trace_calls_def rel_trace_call_def by simp
  qed (simp add: eq_on_def)
next
  case (hArg n vs_arg _ _)
  show ?case
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    have "aval (A (V (f_args ! n))) s = vs_arg ! n" using hArg unfolding relate_exec_state_def by auto
    then show "(to_imp_tc f_args crgt bs r keep (hArg n), s) \<Rightarrow>\<^bsup>(Suc (Suc 0), [])\<^esup> (s(r := vs_arg ! n), False)"
      unfolding to_imp_tc.simps using ttrace_to_leaf.tAssign by metis
  next
    show "rel_trace_to_leaf crgt f_args r [] (Value (vs_arg ! n)) [] (s(r := vs_arg ! n)) False"
      unfolding rel_trace_to_leaf_def rel_trace_calls_def rel_trace_call_def by simp
  qed (simp add: eq_on_def)
next
  case (hNumber frgt n _ _)
  show ?case
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    have "aval (A (N n)) s = n" by auto
    then show "(to_imp_tc f_args crgt bs r keep (hNumber n), s) \<Rightarrow>\<^bsup>(Suc (Suc 0), [])\<^esup> (s(r := n), False)"
      unfolding to_imp_tc.simps using ttrace_to_leaf.tAssign by metis
  next
    show "rel_trace_to_leaf crgt f_args r [] (Value n) [] (s(r := n)) False"
      unfolding rel_trace_to_leaf_def rel_trace_calls_def rel_trace_call_def by simp
  qed (simp add: eq_on_def)
next
  case (hIfTrue frgt t1 vs_b vs_arg T1 v1 t2 T2 l2 T t3)

  let ?r1 = "fresh' (stale_registers f_args crgt bs keep (IF t1\<noteq>0 THEN t2 ELSE t3)) ''If.x''"
  let ?c1 = "to_imp_tc f_args crgt bs ?r1 keep t1"
  let ?c2 = "to_imp_tc f_args crgt bs r keep t2"
  let ?c3 = "to_imp_tc f_args crgt bs r keep t3"

  from hIfTrue.prems(1) have check_compile:
      "check_compile crgt f_args bs keep t1"
      "check_compile crgt f_args bs keep t2"
    unfolding check_compile_def by auto

  from hIfTrue.prems have rel_rgt:
      "relate_rgt_correctness frgt crgt (calls_names_set t1)"
      "relate_rgt_correctness frgt crgt (calls_names_set t2)"
    unfolding relate_rgt_correctness_def by simp_all

  from hIfTrue.prems have rel_state1: "relate_exec_state f_args bs vs_arg vs_b s" by blast

  (* t1 *)

  from hIfTrue.IH(1)[OF check_compile(1) rel_rgt(1) rel_state1, where r = ?r1] rel_trace_to_leaf_cl(1)
  obtain k1 cT1 s2 where ih1:
      "(to_imp_tc f_args crgt bs ?r1 keep t1, s) \<Rightarrow>\<^bsup>(k1, cT1)\<^esup>  (s2, False)"
      "rel_trace_to_leaf crgt f_args ?r1 T1 (Value v1) cT1 s2 False"
      "s2 ?r1 = v1" "s2 = s on set f_args \<union> set bs \<union> set keep - {?r1}"
    using rel_trace_to_leaf_def by auto

  (* t2 *)

  have s2_like_s: "s2 = s on set f_args \<union> set bs \<union> set keep" using eq_on_drop_fresh ih1(4) by blast
  then have rel_state2: "relate_exec_state f_args bs vs_arg vs_b s2"
    using hIfTrue.prems unfolding relate_exec_state_def by fastforce

  from hIfTrue.IH(2)[OF check_compile(2) rel_rgt(2) rel_state2]
  obtain k2 cT2 s3 cl2 where ih2:
      "(?c2,s2)\<Rightarrow>\<^bsup>(k2,cT2)\<^esup> (s3,cl2)"
      "rel_trace_to_leaf crgt f_args r T2 l2 cT2 s3 cl2"
      "s3 = s2 on if_is_value l2 (set f_args) \<union> set bs \<union> set keep - {r}"
    by blast

  (* putting it together *)

  show ?case unfolding to_imp_tc.simps Let_def
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    show "(?c1;; IF ?r1\<noteq>0 THEN ?c2 ELSE ?c3,s) \<Rightarrow>\<^bsup>(Suc (k1 + k2), cT1 @ cT2)\<^esup> (s3, cl2)"
    proof
      show "(?c1,s) \<Rightarrow>\<^bsup>(k1, cT1)\<^esup> (s2, False)" using ih1(1) by simp
      show "(IF ?r1\<noteq>0 THEN ?c2 ELSE ?c3,s2)\<Rightarrow>\<^bsup>(Suc k2, cT2)\<^esup> (s3, cl2)"
      proof (rule ttrace_to_leaf.tIfTrue)
        show "s2 ?r1 \<noteq> 0" using hIfTrue.hyps ih1(3) by simp
        show "(?c2, s2) \<Rightarrow>\<^bsup>(k2, cT2)\<^esup>  (s3, cl2)" using ih2(1) by blast
      qed simp
    qed simp_all
  next
    from hIfTrue.hyps(4) rel_trace_to_leaf_append ih1(2) ih2(2)
    show "rel_trace_to_leaf crgt f_args r T l2 (cT1 @ cT2) s3 cl2"
      unfolding rel_trace_to_leaf_def by blast
  next
    from ih2(3) s2_like_s
    show "s3 = s on if_is_value l2 (set f_args) \<union> set bs \<union> set keep - {r}"
      by (cases l2) (simp_all add: eq_on_def)
  qed
next
  case (hIfFalse frgt t1 vs_b vs_arg T1 v1 t3 T3 l3 T t2)

  let ?r1 = "fresh' (stale_registers f_args crgt bs keep (IF t1\<noteq>0 THEN t2 ELSE t3)) ''If.x''"
  let ?c1 = "to_imp_tc f_args crgt bs ?r1 keep t1"
  let ?c2 = "to_imp_tc f_args crgt bs r keep t2"
  let ?c3 = "to_imp_tc f_args crgt bs r keep t3"

  from hIfFalse.prems(1) have check_compile:
      "check_compile crgt f_args bs keep t1"
      "check_compile crgt f_args bs keep t3"
    unfolding check_compile_def by auto

  from hIfFalse.prems have rel_rgt:
      "relate_rgt_correctness frgt crgt (calls_names_set t1)"
      "relate_rgt_correctness frgt crgt (calls_names_set t3)"
    unfolding relate_rgt_correctness_def by simp_all

  from hIfFalse.prems have rel_state1: "relate_exec_state f_args bs vs_arg vs_b s" by blast

  (* t1 *)

  from hIfFalse.IH(1)[OF check_compile(1) rel_rgt(1) rel_state1, where r = ?r1] rel_trace_to_leaf_cl(1)
  obtain k1 cT1 s2 where ih1:
      "(to_imp_tc f_args crgt bs ?r1 keep t1, s) \<Rightarrow>\<^bsup>(k1, cT1)\<^esup>  (s2, False)"
      "rel_trace_to_leaf crgt f_args ?r1 T1 (Value v1) cT1 s2 False"
      "s2 ?r1 = v1" "s2 = s on set f_args \<union> set bs \<union> set keep - {?r1}"
    using rel_trace_to_leaf_def by auto

  (* t2 *)

  have s2_like_s: "s2 = s on set f_args \<union> set bs \<union> set keep" using eq_on_drop_fresh ih1(4) by blast
  then have rel_state2: "relate_exec_state f_args bs vs_arg vs_b s2"
    using hIfFalse.prems unfolding relate_exec_state_def by fastforce

  from hIfFalse.IH(2)[OF check_compile(2) rel_rgt(2) rel_state2]
  obtain k3 cT3 s3 cl3 where ih2:
      "(?c3,s2)\<Rightarrow>\<^bsup>(k3,cT3)\<^esup> (s3,cl3)"
      "rel_trace_to_leaf crgt f_args r T3 l3 cT3 s3 cl3"
      "s3 = s2 on if_is_value l3 (set f_args) \<union> set bs \<union> set keep - {r}"
    by blast

  (* putting it together *)

  show ?case unfolding to_imp_tc.simps Let_def
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    show "(?c1;; IF ?r1\<noteq>0 THEN ?c2 ELSE ?c3,s) \<Rightarrow>\<^bsup>(Suc (k1 + k3), cT1 @ cT3)\<^esup> (s3, cl3)"
    proof
      show "(?c1,s) \<Rightarrow>\<^bsup>(k1, cT1)\<^esup> (s2, False)" using ih1(1) by simp
      show "(IF ?r1\<noteq>0 THEN ?c2 ELSE ?c3,s2)\<Rightarrow>\<^bsup>(Suc k3, cT3)\<^esup> (s3, cl3)"
      proof (rule ttrace_to_leaf.tIfFalse)
        show "s2 ?r1 = 0" using hIfFalse.hyps ih1(3) by simp
        show "(?c3, s2) \<Rightarrow>\<^bsup>(k3, cT3)\<^esup>  (s3, cl3)" using ih2(1) by blast
      qed simp
    qed simp_all
  next
    show "rel_trace_to_leaf crgt f_args r T l3 (cT1 @ cT3) s3 cl3"
      using hIfFalse.hyps(4) rel_trace_to_leaf_append ih1(2) ih2(2)
      unfolding rel_trace_to_leaf_def by blast
  next
    from ih2(3) s2_like_s
    show "s3 = s on if_is_value l3 (set f_args) \<union> set bs \<union> set keep - {r}"
      by (cases l3) (simp_all add: eq_on_def)
  qed
next
  case (hCall vs ts hTs frgt vs_b vs_arg T gr v)
  let ?g = "f_from_frgt frgt gr"
  let ?T_g = "T_f_from_frgt frgt gr"

  let ?xs = "make_n_fresh (stale_registers f_args crgt bs keep (hCall gr ts)) ''Call.x.'' (length ts)"
  let ?c_arg = "\<lambda>i. to_imp_tc f_args crgt bs (?xs ! i) (?xs @ keep) (ts ! i)"
  let ?c1 = "mk_seqs (generate ?c_arg (length ts))"

  (* part 1: computing the arguments *)

  from check_compile_call[OF hCall.prems(1)] have check_compile:
      "check_compile crgt f_args bs (?xs @ keep) (ts ! i)" if "i < length ts" for i
    using that by simp

  have "calls_names_set (ts ! i) \<subseteq> calls_names_set (hCall gr ts)" if "i < length ts" for i
    using that by fastforce
  with hCall.prems have rel_rgt:
      "relate_rgt_correctness frgt crgt (calls_names_set (ts ! i))" if "i < length ts" for i
    using that unfolding relate_rgt_correctness_def by blast

  from hCall.IH have htrace: "frgt \<turnstile> (ts ! i, vs_b, vs_arg) \<Rightarrow>\<^bsup>hTs ! i\<^esup>  Value (vs ! i)"
    if "i < length ts" for i using that by blast

  from check_compile rel_rgt hCall.IH[simplified] have ih:
    "\<exists>k cT s'.
      (?c_arg i, s) \<Rightarrow>\<^bsup>(k, cT)\<^esup>  (s', False) \<and>
      rel_trace_to_leaf crgt f_args (?xs ! i) (hTs ! i) (Value (vs ! i)) cT s' False \<and>
      s' = s on set f_args \<union> set bs \<union> set (?xs @ keep) - {?xs ! i}"
    if "relate_exec_state f_args bs vs_arg vs_b s" "i < length ts" for i s
    using that rel_trace_to_leaf_cl by (metis (full_types))

  have lengths: "length vs = length ts" "length ?xs = length ts" "length hTs = length ts"
    using hCall.hyps unfolding make_n_fresh_def generate_def by simp_all
  have *: "distinct ?xs" using distinct_make_n_fresh by blast
  have **: "set ?xs \<subseteq> set (?xs @ keep)" by simp
  have ***: "set ?xs \<inter>\<^sub>\<emptyset> set f_args" "set ?xs \<inter>\<^sub>\<emptyset> set bs"
    unfolding stale_registers_def using make_n_fresh_not_in_stale by fastforce+

  from compiled_arguments_trace'[OF lengths * ** *** htrace hCall.prems(3) ih]
  obtain k1 cTs s2 where trace1:
      "(?c1,s) \<Rightarrow>\<^bsup>(k1, cTs)\<^esup> (s2, False)" "rel_trace_calls crgt (concat hTs) cTs"
      "lookups ?xs s2 = vs" "s2 = s on set f_args \<union> set bs \<union> set (?xs @ keep) - set ?xs"
    by blast

  (* part 2: copying from temporaries to argument registers *)

  let ?c2 = "mk_seqs (generate (\<lambda>i. (args_from_crgt crgt gr ! i) ::= A (V (?xs ! i))) (length ts))"
  let ?k2 = "(2 * length ts)\<^sub>+"

  have "set (args_from_crgt crgt gr) \<subseteq> set (stale_registers f_args crgt bs keep (hCall gr ts))"
    unfolding stale_registers_def call_registers_def by auto
  then have "set ?xs \<inter>\<^sub>\<emptyset> set (args_from_crgt crgt gr)" using make_n_fresh_not_in_stale by blast
  moreover have "distinct (args_from_crgt crgt gr)" using hCall.prems(1) by auto
  moreover have "length ?xs = length ts" by simp
  moreover have "length (args_from_crgt crgt gr) = length ts" using hCall.prems(1) by auto

  ultimately obtain s3 where trace2:
      "(?c2, s2) \<Rightarrow>\<^bsup>(?k2, [])\<^esup> (s3, False)"
      "lookup_args crgt gr s3 = lookups ?xs s2"
      "s3 = s2 on - set (args_from_crgt crgt gr)"
    using copy_list_trace' by blast

  (* part 3: calling g *)

  let ?gcom = "com_from_crgt crgt gr" and ?gret = "ret_from_crgt crgt gr" and ?gv = "f_from_frgt frgt gr (lookup_args crgt gr s3)"
  let ?c3 = "CALL ?gcom RETURN ?gret :: tcom"
  let ?k3 = "0 :: nat"
  let ?s4 = "s3(?gret := ?gv)"

  have "terminates_with_res_IMP ?gcom s3 ?gret ?gv" using hCall.prems unfolding relate_rgt_correctness_def by simp
  then obtain z3 s4' where "(?gcom, s3) \<Rightarrow>\<^bsup>z3\<^esup> s4'" "s4' ?gret = ?gv"
    unfolding terminates_with_res_IMP_def terminates_with_res_pred_time_IMP_def terminates_with_pred_time_IMP_def by blast
  then have trace3: "(?c3, s3) \<Rightarrow>\<^bsup>(?k3, [(?gcom, s3)])\<^esup> (?s4, False)" using ttrace_to_leaf.tCall by metis

  have g_args: "lookup_args crgt gr s3 = vs" using trace2 trace1(3) by simp
  then have g_call: "?gv = v" using trace1 hCall split_from_frgt by auto

  (* part 4: copying to r *)

  let ?c4 = "r ::= A (V (ret_from_crgt crgt gr)) :: tcom"

  let ?k4 = "Suc (Suc 0)"
  let ?s5 = "?s4(r := aval (A (V ?gret)) ?s4)"
  have trace4: "(?c4, ?s4) \<Rightarrow>\<^bsup>(?k4, [])\<^esup> (?s5, False)" using ttrace_to_leaf.tAssign by blast
  have s5: "?s5 = ?s4(r := v)" using g_call trace3 by simp

  (* putting it together *)

  show ?case unfolding to_imp_tc.simps Let_def split_beta
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    show "(?c1;; ?c2;; ?c3;; ?c4, s) \<Rightarrow>\<^bsup>(k1 + ?k2 + ?k3 + ?k4, cTs @ [(?gcom, s3)])\<^esup> (?s5,False)"
      apply (repeat \<open>rule ttrace_to_leaf.tSeq\<close>)
      using trace1 trace2 trace3 trace4 by blast+ auto
  next
    have "rel_trace_call crgt gr vs ?gcom s3"
      unfolding rel_trace_call_def using g_args by blast
    then have *: "rel_trace_calls crgt [(gr, vs)] [(?gcom, s3)]"
      unfolding rel_trace_calls_def by simp

    have **: "rel_leaf_state crgt f_args r (Value v) ?s5 False"
      using g_call by simp

    from * ** trace1(2)
    show "rel_trace_to_leaf crgt f_args r T (Value v) (cTs @ [(?gcom, s3)]) ?s5 False"
      unfolding rel_trace_to_leaf_def \<open>T = concat hTs @ [(gr, vs)]\<close>
      using rel_trace_calls_append by blast
  next
    have "set f_args \<union> set bs \<union> set (?xs @ keep) - set ?xs = set f_args \<union> set bs \<union> set keep"
      using make_n_fresh_not_in_stale unfolding stale_registers_def by fastforce
    then have *: "s2 = s on set f_args \<union> set bs \<union> set keep - {r}"
      using trace1 by blast

    have "set f_args \<union> set bs \<union> set keep \<inter>\<^sub>\<emptyset> set (args_from_crgt crgt gr)"
      using hCall.prems(1) unfolding check_compile_def using call_registers_def by auto
    then have **: "s3 = s2 on set f_args \<union> set bs \<union> set keep - {r}"
      using trace2 by auto

    have "ret_from_crgt crgt gr \<notin> set f_args \<union> set bs \<union> set keep"
      using hCall.prems(1) unfolding check_compile_def using call_registers_def by auto
    then have ***: "?s5 = s3 on set f_args \<union> set bs \<union> set keep - {r}" by auto

    show "?s5 = s on if_is_value (Value v) (set f_args) \<union> set bs \<union> set keep - {r}"
      using * ** *** by fastforce
  qed
next
  case (hTail vs ts hTs frgt vs_b vs_arg T)

  let ?xs = "make_n_fresh (stale_registers f_args crgt bs keep (hTAIL ts)) ''TAIL.x.'' (length ts)"
  let ?c_arg = "\<lambda>i. to_imp_tc f_args crgt bs (?xs ! i) (?xs @ keep) (ts ! i)"
  let ?c1 = "mk_seqs (generate ?c_arg (length ts))"

  (* part 1: computing the arguments *)

  from check_compile_tail[OF hTail.prems(1)] have check_compile:
      "check_compile crgt f_args bs (?xs @ keep) (ts ! i)" if "i < length ts" for i
    using that by simp

  have "calls_names_set (ts ! i) \<subseteq> calls_names_set (hTAIL ts)" if "i < length ts" for i
    using that by fastforce
  with hTail.prems have rel_rgt:
      "relate_rgt_correctness frgt crgt (calls_names_set (ts ! i))" if "i < length ts" for i
    using that unfolding relate_rgt_correctness_def by blast

  from hTail.IH have htrace: "frgt \<turnstile> (ts ! i, vs_b, vs_arg) \<Rightarrow>\<^bsup>hTs ! i\<^esup>  Value (vs ! i)"
    if "i < length ts" for i using that by blast

  from check_compile rel_rgt hTail.IH[simplified] have ih:
    "\<exists>k cT s'.
      (?c_arg i, s) \<Rightarrow>\<^bsup>(k, cT)\<^esup>  (s', False) \<and>
      rel_trace_to_leaf crgt f_args (?xs ! i) (hTs ! i) (Value (vs ! i)) cT s' False \<and>
      s' = s on set f_args \<union> set bs \<union> set (?xs @ keep) - {?xs ! i}"
    if "relate_exec_state f_args bs vs_arg vs_b s" "i < length ts" for i s
    using that rel_trace_to_leaf_cl by (metis (full_types))

  have lengths: "length vs = length ts" "length ?xs = length ts" "length hTs = length ts"
    using hTail.hyps unfolding make_n_fresh_def generate_def by simp_all
  have *: "distinct ?xs" using distinct_make_n_fresh by blast
  have **: "set ?xs \<subseteq> set (?xs @ keep)" by simp
  have ***: "set ?xs \<inter>\<^sub>\<emptyset> set f_args" "set ?xs \<inter>\<^sub>\<emptyset> set bs"
    unfolding stale_registers_def using make_n_fresh_not_in_stale by fastforce+

  from compiled_arguments_trace'[OF lengths * ** *** htrace hTail.prems(3) ih]
  obtain k1 cTs s2 where trace1:
      "(?c1,s) \<Rightarrow>\<^bsup>(k1, cTs)\<^esup> (s2, False)" "rel_trace_calls crgt (concat hTs) cTs"
      "lookups ?xs s2 = vs" "s2 = s on set f_args \<union> set bs \<union> set (?xs @ keep) - set ?xs"
    by blast

  (* part 2: copying from temporaries to argument registers *)

  let ?c2 = "mk_seqs (generate (\<lambda>i. (f_args ! i) ::= A (V (?xs ! i))) (length ts))"
  let ?k2 = "(2 * length ts)\<^sub>+"

  have "set f_args \<subseteq> set (stale_registers f_args crgt bs keep (hTAIL ts))"
    unfolding stale_registers_def call_registers_def by auto
  then have "set ?xs \<inter>\<^sub>\<emptyset> set f_args" using make_n_fresh_not_in_stale by blast
  moreover have "distinct f_args" using hTail.prems(1) by auto
  moreover have "length ?xs = length ts" by simp
  moreover have "length f_args = length ts" using hTail.prems(1) by auto

  ultimately obtain s3 where trace2:
      "(?c2, s2) \<Rightarrow>\<^bsup>(?k2, [])\<^esup> (s3,False)"
      "lookups f_args s3 = lookups ?xs s2"
      "s3 = s2 on - set f_args"
    using copy_list_trace' by blast

  (* putting it together *)

  show ?case unfolding to_imp_tc.simps Let_def split_beta
  proof (repeat \<open>rule exI\<close>; repeat \<open>rule conjI\<close>)
    show "(?c1;; ?c2;; tTAIL, s) \<Rightarrow>\<^bsup>(k1 + ?k2 + 5, cTs)\<^esup> (s3, True)"
      apply (repeat \<open>rule ttrace_to_leaf.tSeq ttrace_to_leaf.tTail\<close>)
      using trace1(1) trace2(1) by auto
  next
    have f_args: "lookups f_args s3 = vs" using trace2 trace1(3) by simp
    then have **: "rel_leaf_state crgt f_args r (Tail vs) s3 True" by simp

    from * ** trace1(2)
    show "rel_trace_to_leaf crgt f_args r T (Tail vs) cTs s3 True"
      unfolding rel_trace_to_leaf_def \<open>T = concat hTs\<close>
      using rel_trace_calls_append by blast
  next
    have "set bs \<union> set (?xs @ keep) - set ?xs = set bs \<union> set keep"
      using make_n_fresh_not_in_stale unfolding stale_registers_def by fastforce
    then have *: "s2 = s on set bs \<union> set keep - {r}"
      using trace1 by blast

    have "set bs \<union> set keep \<inter>\<^sub>\<emptyset> set f_args"
      using hTail.prems(1) unfolding check_compile_def using call_registers_def by auto
    then have **: "s3 = s2 on set bs \<union> set keep - {r}"
      using hTail.prems(3) trace2 by auto

    show "s3 = s on if_is_value (Tail vs) (set f_args) \<union> set bs \<union> set keep - {r}"
      using * ** by simp blast
  qed
qed

(* same as above, but remove the "technical" conclusion about state preservation *)
corollary compiler_rel_trace_to_leaf':
  assumes "frgt \<turnstile> (t,vs_b,vs_arg) \<Rightarrow>\<^bsup> hT :: HOL_TCN_Timing.call_trace \<^esup> hl"
  assumes "check_compile crgt f_args bs keep t"
  assumes "relate_rgt_correctness frgt crgt (calls_names_set t)"
  assumes "relate_exec_state f_args bs vs_arg vs_b s"
  obtains k cT s' cl where
    "(to_imp_tc f_args crgt bs r keep t,s)\<Rightarrow>\<^bsup>(k, cT)\<^esup> (s', cl)"
    "rel_trace_to_leaf crgt f_args r hT hl cT s' cl"
  using assms compiler_rel_trace_to_leaf by metis


section \<open>Relating full traces\<close>

lemma ind_tail:
  fixes P :: "thol \<Rightarrow> fun_registry \<Rightarrow> thol \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> HOL_TCN_Timing.call_trace \<Rightarrow> nat \<Rightarrow> bool"
  assumes invar: "invar t" "invar f"
  assumes trace: "(f,frgt) \<turnstile> (t, vs_b, vs_arg) \<Rightarrow>\<^bsup> (k, T) :: HOL_TCN_Timing.trace \<^esup> v"
  assumes val:
    "\<And>f frgt t vs_b vs_arg T v.
      frgt \<turnstile> (t, vs_b, vs_arg) \<Rightarrow>\<^bsup> T :: HOL_TCN_Timing.call_trace \<^esup> Value v \<Longrightarrow>
      P f frgt t vs_b vs_arg 0 T v"
  assumes tail:
    "\<And>f frgt t vs_b vs_arg k T1 T2 vs v.
      frgt \<turnstile> (t, vs_b, vs_arg) \<Rightarrow>\<^bsup> T1 :: HOL_TCN_Timing.call_trace \<^esup> Tail vs \<Longrightarrow>
      (f, frgt) \<turnstile> (f, [], vs) \<Rightarrow>\<^bsup> (k, T2) :: HOL_TCN_Timing.trace \<^esup> v \<Longrightarrow>
      P f frgt f [] vs k T2 v \<Longrightarrow>
      P f frgt t vs_b vs_arg (k + 1) (T1 @ T2) v"
  shows "P f frgt t vs_b vs_arg k T v"
using assms(3,1) proof (induction k arbitrary: t vs_b vs_arg T v)
  case 0
  then have "frgt \<turnstile> (t, vs_b, vs_arg) \<Rightarrow>\<^bsup>T\<^esup> Value v"
    using HOL_TCN_Timing.trace_end_nontail_trace_leaf by force
  then show ?case
    using val by blast
next
  case (Suc k)

  from trace_end_trace_leaf[OF Suc.prems(1,2)] obtain T1 l where
      "frgt \<turnstile> (t, vs_b, vs_arg) \<Rightarrow>\<^bsup>T1\<^esup> l"
      "case l of Value v1 \<Rightarrow> Suc k = 0 \<and> T1 = T \<and> v1 = v
               | Tail ts \<Rightarrow> \<exists>T2. (f, frgt) \<turnstile> (f, [], ts) \<Rightarrow>\<^bsup>(Suc k - 1, T2)\<^esup>  v \<and> T = T1 @ T2"
    by blast
  then obtain ts T2 where
      "frgt \<turnstile> (t, vs_b, vs_arg) \<Rightarrow>\<^bsup>T1\<^esup> Tail ts"
      "(f, frgt) \<turnstile> (f, [], ts) \<Rightarrow>\<^bsup>(k, T2)\<^esup> v" "T = T1 @ T2"
    by (cases l) auto

  with Suc tail invar(2) show ?case by simp
qed

(* don't need this, but mention it in the thesis *)
lemma ind_tail_imp_tc:
  fixes P :: "tcom \<Rightarrow> tcom \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> IMP_Tailcall_Traces.call_trace \<Rightarrow> state \<Rightarrow> bool"
  assumes invar: "IMP_Tailcall.invar c" "IMP_Tailcall.invar f"
  assumes trace: "f \<turnstile> (c, s) \<Rightarrow>\<^bsup> (k, T) :: IMP_Tailcall_Traces.trace \<^esup> s'"
  assumes val:
    "\<And>f c s k T s'.
      (c, s) \<Rightarrow>\<^bsup> (k, T) :: IMP_Tailcall_Traces.trace \<^esup> (s', False) \<Longrightarrow>
      P f c s k T s'"
  assumes tail:
    "\<And>f c s k1 k2 T1 T2 s' s''.
      (c, s) \<Rightarrow>\<^bsup> (k1, T1) :: IMP_Tailcall_Traces.trace \<^esup> (s', True) \<Longrightarrow>
      f \<turnstile> (f, s') \<Rightarrow>\<^bsup> (k2, T2) :: IMP_Tailcall_Traces.trace \<^esup> s'' \<Longrightarrow>
      k1 \<ge> 5 \<Longrightarrow>
      P f f s' k2 T2 s'' \<Longrightarrow>
      P f c s (k1 + k2) (T1 @ T2) s''"
  shows "P f c s k T s'"
using assms(3,1) proof (induction k arbitrary: c s T s' rule: less_induct)
  case (less k)
  from less.prems IMP_Tailcall_Traces.trace_end_trace_leaf obtain k1 T1 s2 l k2 T2
    where 1: "(c, s) \<Rightarrow>\<^bsup> (k1, T1) \<^esup> (s2, l)"
      and *: "if l then f \<turnstile>(f, s2) \<Rightarrow>\<^bsup>(k2, T2)\<^esup> s' \<and> k = k1 + k2 \<and> k1 \<ge> 5 \<and> T = T1 @ T2
              else k1 = k \<and> T1 = T \<and> s2 = s'" by metis
  then consider
    (base) "(c, s) \<Rightarrow>\<^bsup> (k, T) \<^esup> (s', False)" |
    (step) "(c, s) \<Rightarrow>\<^bsup> (k1, T1) \<^esup> (s2, True)" "f \<turnstile>(f, s2) \<Rightarrow>\<^bsup>(k2, T2)\<^esup> s'" "k1 \<ge> 5" "T = T1 @ T2" "k = k1 + k2"
    by (metis (full_types))
  then show ?case proof cases
    case base
    then show ?thesis using val by blast
  next
    case step
    from \<open>k = k1 + k2\<close> \<open>k1 \<ge> 5\<close> have "k2 < k" by linarith
    note ih = less.IH[OF \<open>k2 < k\<close> step(2) invar(2)]
    show "P f c s k T s'"
      by (subst \<open>T = T1 @ T2\<close>, subst \<open>k = k1 + k2\<close>, rule tail[OF step(1,2,3) ih])
  qed
qed

(* due to `c_struct` (5 * ..) and lemma `to_imp_num_commands` (7 * ..) *)
definition "rel_trace_time t hk k \<equiv> k \<le> 35 * HOL_TCN_Timing.num_commands t * (hk + 1)"
(* this says: in each of `hk + 1` "chunks" of source program, the structural execution time of the
    compiled program is bounded by some constant (35 * |t|) *)

lemma compiler_rel_trace_time_to_leaf:
  assumes "(to_imp_tc f_args crgt bs r keep t,s)\<Rightarrow>\<^bsup>(k, cT)\<^esup> (s', l)"
  shows "rel_trace_time t 0 k"
proof-
  have "k \<le> c_struct (to_imp_tc f_args crgt bs r keep t)"
    using assms trace_nontail_static_bound by blast
  also have "... \<le> 35 * HOL_TCN_Timing.num_commands t"
    using to_imp_num_commands by simp
  term ?thesis
  finally show ?thesis unfolding rel_trace_time_def by simp
qed

lemma rel_trace_time_join:
  assumes "rel_trace_time t hk1 k1" "rel_trace_time t hk2 k2"
  shows "rel_trace_time t (hk1 + hk2 + 1) (k1 + k2)"
  using assms unfolding rel_trace_time_def by (simp add: algebra_simps)

lemma rel_trace_time_num_commands_mono:
  assumes "HOL_TCN_Timing.num_commands t \<le> HOL_TCN_Timing.num_commands f"
  assumes "rel_trace_time t hk k"
  shows "rel_trace_time f hk k"
  using assms unfolding rel_trace_time_def
  by (meson dual_order.refl mult_le_mono order_trans)


(* todo move *)
lemma sum_map_mono2:
  fixes f :: "_ \<Rightarrow> 'a :: {ordered_ab_semigroup_add, monoid_add}" and g :: "_ \<Rightarrow> 'a"
  assumes "length xs = length ys"
  assumes "\<forall>i < length xs. f (xs ! i) \<le> g (ys ! i)"
  shows "sum_map f xs \<le> sum_map g ys"
using assms(2) proof (induction xs ys rule: snoc_list_induct2)
  case (snoc xs x ys y)
  from snoc have *: "f x \<le> g y" by (metis length_append_singleton lessI nth_append_length)
  from snoc have **: "\<forall>i<length xs. f (xs ! i) \<le> g (ys ! i)" by (simp add: less_Suc_eq nth_append_left)
  from * ** snoc.IH show ?case using add_mono by fastforce
qed (simp_all add: assms(1))

(* todo: move *)
lemma htrace_to_leaf_length_bound:
  assumes "frgt \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup> T :: HOL_TCN_Timing.call_trace \<^esup> l"
  shows "length T \<le> HOL_TCN_Timing.num_commands t"
using assms proof (induction rule: htrace_to_leaf_induct)
  case (hCall vs ts Ts frgt bs xs T gr v)
  have "\<forall>i < length ts. HOL_TCN_Timing.num_commands (ts ! i) \<le> sum_map HOL_TCN_Timing.num_commands ts" by (simp add: member_le_sum_list)
  then have "\<forall>i < length Ts. length (Ts ! i) \<le> HOL_TCN_Timing.num_commands (ts ! i)" using hCall.IH hCall.hyps by auto
  with hCall.hyps have "sum_map length Ts \<le> sum_map HOL_TCN_Timing.num_commands ts" using sum_map_mono2 by blast
  then have "length (concat Ts) \<le> sum_map HOL_TCN_Timing.num_commands ts" by (simp add: length_concat)
  with hCall.hyps show ?case by simp
next
  case (hTail vs ts Ts frgt bs xs T)
  have "\<forall>i < length ts. HOL_TCN_Timing.num_commands (ts ! i) \<le> sum_map HOL_TCN_Timing.num_commands ts" by (simp add: member_le_sum_list)
  then have "\<forall>i < length Ts. length (Ts ! i) \<le> HOL_TCN_Timing.num_commands (ts ! i)" using hTail.IH hTail.hyps by auto
  with hTail.hyps have "sum_map length Ts \<le> sum_map HOL_TCN_Timing.num_commands ts"
    using sum_map_mono2 by blast
  then have *: "length (concat Ts) \<le> sum_map HOL_TCN_Timing.num_commands ts" by (simp add: length_concat)
  with hTail.hyps show ?case by simp
qed simp_all


(* mostly duplicate of htrace_to_leaf_length_bound, which we use in the full trace proof to prove the same thing *)
lemma htrace_to_end_length_bound_:
  assumes "(f,frgt) \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup> (k, T) :: HOL_TCN_Timing.trace \<^esup> v"
  shows "length T \<le> HOL_TCN_Timing.num_commands f * k + HOL_TCN_Timing.num_commands t"
using assms proof (induction rule: htrace_to_end_induct)
  case (hCall vs ts Ts f frgt bs xs T gr v)
  have "\<forall>i < length ts. HOL_TCN_Timing.num_commands (ts ! i) \<le> sum_map HOL_TCN_Timing.num_commands ts" by (simp add: member_le_sum_list)
  then have "\<forall>i < length Ts. length (Ts ! i) \<le> HOL_TCN_Timing.num_commands (ts ! i)" using hCall.IH hCall.hyps by auto
  with hCall.hyps have "sum_map length Ts \<le> sum_map HOL_TCN_Timing.num_commands ts" using sum_map_mono2 by blast
  then have "length (concat Ts) \<le> sum_map HOL_TCN_Timing.num_commands ts" by (simp add: length_concat)
  with hCall.hyps show ?case by simp
next
  case (hTail vs ts Ts f frgt bs xs n' T' v' T k)
  have "\<forall>i < length ts. HOL_TCN_Timing.num_commands (ts ! i) \<le> sum_map HOL_TCN_Timing.num_commands ts" by (simp add: member_le_sum_list)
  then have "\<forall>i < length Ts. length (Ts ! i) \<le> HOL_TCN_Timing.num_commands (ts ! i)" using hTail.IH hTail.hyps by auto
  with hTail.hyps have "sum_map length Ts \<le> sum_map HOL_TCN_Timing.num_commands ts"
    using sum_map_mono2 by blast
  then have *: "length (concat Ts) \<le> sum_map HOL_TCN_Timing.num_commands ts" by (simp add: length_concat)
  have **: "length T' \<le> HOL_TCN_Timing.num_commands f * k + (length ts + 1)" using hTail.hyps hTail.IH(2) by simp
  from * ** \<open>T = _\<close> show ?case by simp
qed auto

(* this lemma says that there are at most |f| calls per "chunk" *)
corollary htrace_to_end_length_bound'_:
  assumes "(f,frgt) \<turnstile> (f,bs,xs) \<Rightarrow>\<^bsup> (k, T) :: HOL_TCN_Timing.trace \<^esup> v"
  shows "length T \<le> HOL_TCN_Timing.num_commands f * (k + 1)"
  using htrace_to_end_length_bound_ assms by fastforce




(* hT only "calls" functions which occur in f *)
definition "trace_calls_in f hT \<equiv> set (map fst hT) \<subseteq> calls_names_set f"

lemma Union_mono2:
  assumes "length xs = length ys"
  assumes "\<forall>i < length xs. f (xs ! i) \<subseteq> g (ys ! i)"
  shows "(\<Union>x \<in> set xs. f x) \<subseteq> (\<Union>y \<in> set ys. g y)"
using assms(2) proof (induction xs ys rule: snoc_list_induct2)
  case (snoc xs x ys y)
  from snoc have *: "f x \<subseteq> g y" by (metis length_append_singleton lessI nth_append_length)
  from snoc have **: "\<forall>i<length xs. f (xs ! i) \<subseteq> g (ys ! i)" by (simp add: less_Suc_eq nth_append_left)
  from * ** snoc.IH show ?case using add_mono by fastforce
qed (simp_all add: assms(1))


lemma htrace_to_end_calls_in:
  assumes "(f,frgt) \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup> (k, T) :: HOL_TCN_Timing.trace \<^esup> v"
  shows "set (map fst T) \<subseteq> calls_names_set f \<union> calls_names_set t"
using assms proof (induction rule: htrace_to_end_induct)
  case (hCall vs ts Ts f frgt bs xs T gr v)

  have 1: "gr \<in> calls_names_set f \<union> calls_names_set (hCall gr ts)" by simp

  have *: "\<forall>i < length Ts. set (map fst (Ts ! i)) \<subseteq> calls_names_set f \<union> calls_names_set (ts ! i)"
    using hCall by auto

  have "set (map fst (concat Ts)) = (\<Union>Ti\<in>set Ts. set (map fst Ti))" by auto
  also have "... \<subseteq> (\<Union>t\<in>set ts. calls_names_set f \<union> calls_names_set t)"
    using Union_mono2 \<open>length Ts = length ts\<close> * by meson
  also have "... \<subseteq> calls_names_set f \<union> (\<Union>t\<in>set ts. calls_names_set t)" by blast
  also have "... = calls_names_set f \<union> set (concat_map calls_names ts)" by simp
  also have "... \<subseteq> calls_names_set f \<union> calls_names_set (hCall gr ts)" by auto
  finally show "set (map fst T) \<subseteq> calls_names_set f \<union> calls_names_set (hCall gr ts)"
    using 1 \<open>T = _\<close> by simp
next
  case (hTail vs ts Ts f frgt bs xs n' T' v' T k)

  have tail: "set (map fst T') \<subseteq> calls_names_set f \<union> calls_names_set (hTAIL ts)" using hTail.IH by blast

  have *: "\<forall>i < length Ts. set (map fst (Ts ! i)) \<subseteq> calls_names_set f \<union> calls_names_set (ts ! i)"
    using hTail by auto

  have "set (map fst (concat Ts)) = (\<Union>Ti\<in>set Ts. set (map fst Ti))" by auto
  also have "... \<subseteq> (\<Union>t\<in>set ts. calls_names_set f \<union> calls_names_set t)"
    using Union_mono2 \<open>length Ts = length ts\<close> * by meson
  also have "... \<subseteq> calls_names_set f \<union> (\<Union>t\<in>set ts. calls_names_set t)" by blast
  also have "... = calls_names_set f \<union> calls_names_set (hTAIL ts)" by auto
  finally show "set (map fst T) \<subseteq> calls_names_set f \<union> calls_names_set (hTAIL ts)"
    using tail \<open>T = _\<close> by simp
qed auto

corollary htrace_to_end_calls_in':
  assumes "(f,frgt) \<turnstile> (f,bs,xs) \<Rightarrow>\<^bsup> (k, T) :: HOL_TCN_Timing.trace \<^esup> v"
  shows "set (map fst T) \<subseteq> calls_names_set f"
  using htrace_to_end_calls_in assms by blast


theorem compiler_rel_trace_end:
  assumes "invar t" "invar f"
  assumes "HOL_TCN_Timing.num_commands t \<le> HOL_TCN_Timing.num_commands f"
  assumes "calls_names_set t \<subseteq> calls_names_set f"
  assumes "(f,frgt) \<turnstile> (t,vs_b,vs_arg) \<Rightarrow>\<^bsup> (hk, hT) :: HOL_TCN_Timing.trace \<^esup> hv"
  assumes "check_compile crgt f_args bs keep t"
  assumes "check_compile crgt f_args [] [] f"
  (* assumes "relate_rgt_correctness frgt crgt (calls_names_set t)" *)
  assumes "relate_rgt_correctness frgt crgt (calls_names_set f)"
  assumes "relate_exec_state f_args bs vs_arg vs_b s"
  shows "\<exists>k cT s'.
    (to_imp_tc f_args crgt [] r [] f \<turnstile> (to_imp_tc f_args crgt bs r keep t,s)\<Rightarrow>\<^bsup>(k, cT)\<^esup> s')
    \<and> rel_trace_to_end crgt r hT hv cT s'
    \<and> rel_trace_time f hk k
    \<and> length hT \<le> HOL_TCN_Timing.num_commands f * (hk + 1)"
using assms(1-4,6-) proof (induction arbitrary: s bs keep rule: ind_tail[OF assms(1,2,5)])
  (* base case: t executes to a value without a tail call *)
  case (1 f frgt t vs_b vs_arg hT v)

  (* using the partial trace relatedness theorem, obtain a related trace *)
  from "1.prems"(4,7) have *: "relate_rgt_correctness frgt crgt (calls_names_set t)"
    unfolding relate_rgt_correctness_def by (simp add: in_mono)
  from compiler_rel_trace_to_leaf'[OF "1.hyps"(1) "1.prems"(5) * "1.prems"(8)] obtain k cT s'
    where imp: "(to_imp_tc f_args crgt bs r keep t, s) \<Rightarrow>\<^bsup>(k, cT)\<^esup>  (s', False)"
      and rel: "rel_trace_to_leaf crgt f_args r hT (Value v) cT s' False"
    using rel_trace_to_leaf_cl by (metis (full_types))

  (* turn the information about partial traces (ending in a value) to full traces *)
  from rel have "rel_trace_to_end crgt r hT v cT s'"
    using rel_trace_to_leaf_value_rel_trace_to_end by simp
  moreover from imp have "f \<turnstile> (to_imp_tc f_args crgt bs r keep t, s) \<Rightarrow>\<^bsup>(k, cT)\<^esup>  s'" for f
    using IMP_Tailcall_Traces.trace_leaf_no_tail_trace_end by blast

  (* the running time until the tail call is bounded *)
  moreover from imp have "rel_trace_time f 0 k"
    using compiler_rel_trace_time_to_leaf "1.prems" rel_trace_time_num_commands_mono by blast

  (* the length of the trace is bounded *)
  moreover have "length hT \<le> HOL_TCN_Timing.num_commands f"
    using htrace_to_leaf_length_bound "1.hyps" "1.prems"(3) le_trans by blast

  ultimately show ?case by auto
next
  (* inductive step: t executes to a tail call *)
  case (2 f frgt t vs_b vs_arg hk hT1 hT2 vs v)

  (* again using the partial trace relatedness theorem, obtain a related trace up to the tail call *)
  from "2.prems"(4,7) have *: "relate_rgt_correctness frgt crgt (calls_names_set t)"
    unfolding relate_rgt_correctness_def by (simp add: in_mono)
  from compiler_rel_trace_to_leaf'[OF "2.hyps"(1) "2.prems"(5) * "2.prems"(8)] obtain ck1 cT1 s2
    where imp1: "(to_imp_tc f_args crgt bs r keep t, s) \<Rightarrow>\<^bsup>(ck1, cT1)\<^esup>  (s2, True)"
      and rel1: "rel_trace_to_leaf crgt f_args r hT1 (Tail vs) cT1 s2 True"
    using rel_trace_to_leaf_cl by (metis (full_types))
  then have rel_time1: "rel_trace_time f 0 ck1"
    using compiler_rel_trace_time_to_leaf "2.prems" rel_trace_time_num_commands_mono by blast

  from 2 htrace_to_leaf_length_bound have trace_len1:
    "length hT1 \<le> HOL_TCN_Timing.num_commands f" by fastforce

  (* show that the intermediate state s2 encodes the initial context for the remaining trace *)
  from rel1 have "lookups f_args s2 = vs" unfolding rel_trace_to_leaf_def by simp
  then have rel_state2: "relate_exec_state f_args [] vs [] s2"
    unfolding relate_exec_state_def by simp

  (* from there, apply the IH to get the remaining trace *)
  with "2.IH"[where bs = "[]" and keep = "[]"] "2.prems" obtain ck2 cT2 s3
    where imp2: "to_imp_tc f_args crgt [] r [] f \<turnstile>(to_imp_tc f_args crgt [] r [] f, s2) \<Rightarrow>\<^bsup>(ck2, cT2)\<^esup>  s3"
      and rel2: "rel_trace_to_end crgt r hT2 v cT2 s3"
      and rel_time2: "rel_trace_time f hk ck2"
      and trace_len2: "length hT2 \<le> HOL_TCN_Timing.num_commands f * (hk + 1)"
    by blast

  (* combine the first and second parts of the execution *)
  moreover from imp1 imp2 have
    "to_imp_tc f_args crgt [] r [] f \<turnstile>(to_imp_tc f_args crgt bs r keep t, s) \<Rightarrow>\<^bsup>(ck1 + ck2, cT1 @ cT2)\<^esup>  s3"
    using IMP_Tailcall_Traces.trace_leaf_tail_trace_end by auto
  moreover from rel1 rel2 have "rel_trace_to_end crgt r (hT1 @ hT2) v (cT1 @ cT2) s3"
    using rel_trace_to_end_append unfolding rel_trace_to_leaf_def by metis
  moreover from rel_time1 rel_time2 have "rel_trace_time f (hk + 1) (ck1 + ck2)"
    using rel_trace_time_join by fastforce
  moreover from trace_len1 trace_len2 have "length (hT1 @ hT2) \<le> HOL_TCN_Timing.num_commands f * (hk + 1 + 1)"
    by simp

  ultimately show ?case by blast
qed



definition order_of_c :: "nat \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> bool" where
  "order_of_c c f g = (\<forall>x. f x \<le> c * (g x)\<^sub>+)"

definition order_of :: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> bool" (\<open>(\<open>notation=\<open>infix \<le>\<close>\<close>_/ \<le>\<^sub>c _)\<close>  [51, 51] 50) where
  "order_of f g = (\<exists>c. order_of_c c f g)"
(* - for a function g that is nowhere-zero, this says that f must be no larger than g times some factor c
   - for a function that is everywhere-zero, this says f must be less than some c everywhere
   - in general, there must be some constant c, such that f must be no larger than g times that factor c,
      except where g is zero, where f is no larger than c *)

lemma order_of_cI[intro]: assumes "\<And>x. f x \<le> c * (g x)\<^sub>+" shows "order_of_c c f g"
  using assms unfolding order_of_c_def by blast

lemma order_of_cE[elim]: assumes "order_of_c c f g" shows "f x \<le> c * (g x)\<^sub>+"
  using assms unfolding order_of_c_def by blast

lemma order_ofI[intro]: assumes "order_of_c c f g" shows "f \<le>\<^sub>c g"
  using assms unfolding order_of_def by blast

lemma order_ofE[elim]: assumes "f \<le>\<^sub>c g" obtains c where "order_of_c c f g"
  using assms unfolding order_of_def by blast

lemma order_of_refl: "f \<le>\<^sub>c f"
unfolding order_of_def order_of_c_def proof
  show "\<forall>x. f x \<le> 1 * (f x)\<^sub>+" using max1_non_dec by simp
qed

lemma order_of_c_trans:
  assumes "order_of_c c1 f g" "order_of_c c2 g h"
  shows "order_of_c (c1 * c2\<^sub>+) f h"
unfolding order_of_c_def proof
  fix x
  from assms have *: "f x \<le> c1 * (g x)\<^sub>+" and **: "g x \<le> c2 * (h x)\<^sub>+" unfolding order_of_c_def by auto
  show "f x \<le> (c1 * c2\<^sub>+) * (h x)\<^sub>+"
  proof (cases "g x = 0")
    assume "g x = 0"
    with * have "f x \<le> c1" by simp
    also have "... \<le> (c1 * c2\<^sub>+) * (h x)\<^sub>+" using linorder_not_less by fastforce
    finally show ?thesis .
  next
    assume "g x \<noteq> 0"
    with * have "f x \<le> c1 * g x" by simp
    also with ** have "... \<le> c1 * c2 * (h x)\<^sub>+" by simp
    also have "... \<le> (c1 * c2\<^sub>+) * (h x)\<^sub>+" using linorder_not_less by fastforce
    finally show ?thesis .
  qed
qed

lemma order_of_trans: assumes "f \<le>\<^sub>c g" "g \<le>\<^sub>c h" shows "f \<le>\<^sub>c h"
  using assms unfolding order_of_def using order_of_c_trans by blast

lemma order_of_not_antisym: obtains f g where "f \<le>\<^sub>c g" "g \<le>\<^sub>c f" "f \<noteq> g"
proof
  show "(\<lambda>_. 0) \<le>\<^sub>c (\<lambda>_. 1)" by blast
  show "(\<lambda>_. 1) \<le>\<^sub>c (\<lambda>_. 0)" by fastforce
  show "(\<lambda>_. 0 :: nat) \<noteq> (\<lambda>_. 1)" by (meson zero_neq_one)
qed

lemma order_of_le:
  assumes "\<And>x. f x \<le> g x"
  shows "f \<le>\<^sub>c g"
proof (rule order_ofI, rule order_of_cI[where c = 1], rule max1I)
  fix x assume "g x = 0" with assms[of x] show "f x \<le> 1 * 1" by linarith
next
  fix x assume "g x \<noteq> 0" with assms[of x] show "f x \<le> 1 * g x" by linarith
qed

(* shows us that our order definition is nothing but the classic a*f+b definition... *)
lemma order_of_ab: "f \<le>\<^sub>c g \<longleftrightarrow> (\<exists>a b. \<forall>x. f x \<le> a * g x + b)"
proof
  assume "f \<le>\<^sub>c g"
  then obtain c where "f x \<le> c * (g x)\<^sub>+" for x by force
  then have "f x \<le> c * g x + c" for x by (fastforce elim: max1E)
  then show "\<exists>a b. \<forall>x. f x \<le> a * g x + b" by blast
next
  assume "\<exists>a b. \<forall>x. f x \<le> a * g x + b"
  then obtain a b where "f x \<le> a * g x + b" for x by blast
  also have "... x \<le> (a + b) * (g x)\<^sub>+" for x using max1_abc by blast
  finally show "f \<le>\<^sub>c g" by blast
qed

lemma order_of_const: "(\<lambda>_. k) \<le>\<^sub>c f"
  by (rule order_ofI, rule order_of_cI[where c = k], rule max1I; simp)

(* in fact, any complexity class satisfying this property should work *)
lemma order_of_plus: assumes "f \<le>\<^sub>c h" "g \<le>\<^sub>c h" shows "(\<lambda>x. f x + g x) \<le>\<^sub>c h"
proof-
  from assms obtain c1 c2 where *: "order_of_c c1 f h" "order_of_c c2 g h" by blast
  show "(\<lambda>x. f x + g x) \<le>\<^sub>c h"
  proof (rule order_ofI, rule order_of_cI, rule max1I)
    fix x assume "h x = 0"
    with * have "f x \<le> c1" "g x \<le> c2" using order_of_cE[where g = h and x = x] by auto
    then show "f x + g x \<le> (c1 + c2) * 1" by simp
  next
    fix x assume "h x \<noteq> 0"
    with * have "f x \<le> c1 * h x" "g x \<le> c2 * h x" using order_of_cE[where g = h and x = x] by auto
    then show "f x + g x \<le> (c1 + c2) * h x" by (simp add: algebra_simps)
  qed
qed

lemma order_of_const_mult: assumes "f \<le>\<^sub>c g" shows "(\<lambda>x. k * f x) \<le>\<^sub>c g"
  using assms order_of_plus by (induction k) auto


(* Following the formulation from A Fistful of Dollars,
    we abstract the definition of "asymptotically bounded" away.

  Advantages:
  - No more "c" floating around in the definition of terminates_with_res_time_order_IMP
  - Also don't need to add a "c" parameter to terminates_with_res_time_IMP, which I think would get in the way:
      - Since that predicate is used for the recursion on the term, the "c" would be an extra parameter fixed at 1
      - There's also nothing that could force "c" to be a constant there, so it would just be an extra parameter that gets multiplied in inside the predicate
  - Keeps the definition of "of_order" in one place, which we might need when considering functions that have run time of 0
      - E.g. of_order g f = if (g is zero function) then (f is constant function) else (existing def ...)
      - Any change here would of course nevertheless need to be accounted for whenever an auxiliary function is called.
 *)

definition "terminates_with_res_time_order_IMP p r f T_f \<equiv>
  \<exists>T. T \<le>\<^sub>c T_f \<and> (\<forall>s. HOL_Nat_To_IMP.terminates_with_res_time_IMP p s r (f s) (T s))"

lemma terminates_with_res_time_order_IMP_I[intro]:
  assumes "T \<le>\<^sub>c T_f"
  assumes "\<And>s. HOL_Nat_To_IMP.terminates_with_res_time_IMP p s r (f s) (T s)"
  shows "terminates_with_res_time_order_IMP p r f T_f"
  using assms unfolding terminates_with_res_time_order_IMP_def by blast

lemma terminates_with_res_time_order_IMP_E[elim]:
  assumes "terminates_with_res_time_order_IMP p r f T_f"
  obtains T where "T \<le>\<^sub>c T_f" "\<And>s. HOL_Nat_To_IMP.terminates_with_res_time_IMP p s r (f s) (T s)"
  using assms unfolding terminates_with_res_time_order_IMP_def by blast

lemma terminates_with_res_time_order_IMP_mono:
  assumes "T_f \<le>\<^sub>c T_f'"
  assumes "terminates_with_res_time_order_IMP p r f T_f"
  shows "terminates_with_res_time_order_IMP p r f T_f'"
proof-
  from assms(2) obtain T
    where "T \<le>\<^sub>c T_f"
      and *: "\<And>s. HOL_Nat_To_IMP.terminates_with_res_time_IMP p s r (f s) (T s)" by fast
  with assms(1) order_of_trans have "T \<le>\<^sub>c T_f'" by blast
  with * show ?thesis by blast
qed

definition "terminates_with_res_time_order_IMP_Tailcall tp p r f T_f \<equiv>
  \<exists>T. T \<le>\<^sub>c T_f \<and> (\<forall>s. HOL_Nat_To_IMP.terminates_with_res_time_IMP_Tailcall tp p s r (f s) (T s))"

lemma terminates_with_res_time_order_IMP_TailcallI[intro]:
  assumes "T \<le>\<^sub>c T_f"
  assumes "\<And>s. HOL_Nat_To_IMP.terminates_with_res_time_IMP_Tailcall tp p s r (f s) (T s)"
  shows "terminates_with_res_time_order_IMP_Tailcall tp p r f T_f"
  using assms unfolding terminates_with_res_time_order_IMP_Tailcall_def by blast

lemma terminates_with_res_time_order_IMP_TailcallE[elim]:
  assumes "terminates_with_res_time_order_IMP_Tailcall tp p r f T_f"
  obtains T where "T \<le>\<^sub>c T_f" "\<And>s. HOL_Nat_To_IMP.terminates_with_res_time_IMP_Tailcall tp p s r (f s) (T s)"
  using assms unfolding terminates_with_res_time_order_IMP_Tailcall_def by blast

lemma terminates_with_res_time_order_IMP_Tailcall_to_IMP:
  assumes "IMP_Tailcall.invar p"
  assumes "r \<in> set (vars p)"
  assumes "terminates_with_res_time_order_IMP_Tailcall p p r f T_f"
  shows "terminates_with_res_time_order_IMP (tailcall_to_IMP p) r f T_f"
proof-
  from assms(3) obtain T where tc:
      "T \<le>\<^sub>c T_f"
      "\<And>s. HOL_Nat_To_IMP.terminates_with_res_time_IMP_Tailcall p p s r (f s) (T s)"
    by fastforce

  let ?T = "\<lambda>s. (1 + size\<^sub>c (compile p) + 8 + 8 * size\<^sub>c (compile p)) * T s"
  show ?thesis
  proof
    fix s
    from tc obtain z1 s'1 where imp_tc:
        "p \<turnstile> (p, s) \<Rightarrow>\<^bsup> z1 :: nat \<^esup> s'1" "s'1 r = f s" "z1 \<le> T s"
      using HOL_Nat_To_IMP.terminates_with_res_time_IMP_TailcallE by blast
    with assms(1) compile_sound obtain s'2 where imp':
        "(compile p, s) \<Rightarrow>'\<^bsup> 7 + z1 \<^esup> s'2" "s'1 = s'2 on set (vars p)" by blast
    with assms(2) inline_sound obtain z3 s'3 where imp:
        "(inline (compile p), s) \<Rightarrow>\<^bsup> z3 \<^esup> s'3"
        "s'3 = s'2 on set (vars (compile p))"
        "7 + z1 \<le> z3" "z3 \<le> (7 + z1 + 1) * (1 + size\<^sub>c (compile p))"
      using inline_sound by blast

    show "HOL_Nat_To_IMP.terminates_with_res_time_IMP (tailcall_to_IMP p) s r (f s) (?T s)"
    proof (rule HOL_Nat_To_IMP.terminates_with_res_time_IMPI)
      show "(tailcall_to_IMP p, s) \<Rightarrow>\<^bsup> z3 \<^esup> s'3" using imp tailcall_to_IMP_eq by simp
    next
      have "f s = s'1 r" using imp_tc by simp
      also have "... = s'2 r" using imp' assms(2) by blast
      also have "... = s'3 r" using imp assms(2) set_vars_compile by force
      finally show "s'3 r = f s" by simp
    next
      have *: "T s > 0" using imp_tc IMP_Tailcall.bigstep_progress by fastforce

      have "7 + z1 + 1 \<le> T s + 8" using imp_tc by linarith
      then have "z3 \<le> (T s + 8) * (1 + size\<^sub>c (compile p))" using imp by (meson le_trans mult_le_mono1)
      also have "... = T s + T s * size\<^sub>c (compile p) + 8 + 8 * size\<^sub>c (compile p)" by (simp add: algebra_simps)
      also with * have "... \<le> 1 * T s + size\<^sub>c (compile p) * T s + 8 * T s + 8 * size\<^sub>c (compile p) * T s"
        by (simp add: algebra_simps add_mono)
      also have "... = (1 + size\<^sub>c (compile p) + 8 + 8 * size\<^sub>c (compile p)) * T s" by algebra
      finally show "z3 \<le> ?T s" .
    qed
  next
    show "?T \<le>\<^sub>c T_f" using tc order_of_const_mult by blast
  qed
qed


definition "some_constant_IMP p T_f \<equiv>
  (SOME c. \<exists>T. order_of_c c T T_f \<and> (\<forall>s. \<exists>s'. HOL_Nat_To_IMP.terminates_with_time_IMP p s s' (T s)))"

(* TODO: we're switching between terminates_with_res and plain terminates_with,
  maybe be consistent? \<rightarrow> defs in _Primitives are more complete *)

lemma some_constant_IMP_as_bound:
  assumes "terminates_with_res_time_order_IMP p r f T_f"
  shows "HOL_Nat_To_IMP.terminates_with_res_time_IMP p s r (f s) (some_constant_IMP p T_f * (T_f s)\<^sub>+)"
proof-
  show "HOL_Nat_To_IMP.terminates_with_res_time_IMP p s r (f s) (some_constant_IMP p T_f * (T_f s)\<^sub>+)"
    unfolding some_constant_IMP_def proof (rule someI2_ex)
    show "\<exists>c T. order_of_c c T T_f \<and> (\<forall>s. \<exists>s'. HOL_Nat_To_IMP.terminates_with_time_IMP p s s' (T s))"
      using assms HOL_Nat_To_IMP.terminates_with_time_res_equiv terminates_with_res_time_order_IMP_E order_ofE by metis
  next
    fix c
    assume "\<exists>T. order_of_c c T T_f \<and> (\<forall>s. \<exists>s'. HOL_Nat_To_IMP.terminates_with_time_IMP p s s' (T s))"
    then obtain T s' where some_c:
      "HOL_Nat_To_IMP.terminates_with_time_IMP p s s' (T s)"
      "order_of_c c T T_f" by blast

    from assms obtain T' where
      "HOL_Nat_To_IMP.terminates_with_res_time_IMP p s r (f s) (T' s)" by blast
    moreover from some_c(1) have *: "HOL_Nat_To_IMP.terminates_with_res_time_IMP p s r (s' r) (T s)"
      using HOL_Nat_To_IMP.terminates_with_time_res_equiv by blast
    ultimately have **: "f s = s' r"
      by (metis HOL_Nat_To_IMP.terminates_with_res_time_IMPE bigstep_det)

    from some_c(2) have ***: "T s \<le> c * (T_f s)\<^sub>+" by auto

    from * ** *** show "HOL_Nat_To_IMP.terminates_with_res_time_IMP p s r (f s) (c * (T_f s)\<^sub>+)"
      using HOL_Nat_To_IMP.terminates_with_res_time_IMP_mono by presburger
  qed
qed



definition "terminates_time_order_IMP p T_f =
  (\<exists>r f. terminates_with_res_time_order_IMP p r f T_f)"

lemma terminates_time_order_IMP_I[intro]:
  assumes "terminates_with_res_time_order_IMP p r f T_f"
  shows "terminates_time_order_IMP p T_f"
  unfolding terminates_time_order_IMP_def using assms by blast

lemma terminates_time_order_IMP_E[elim]:
  assumes "terminates_time_order_IMP p T_f"
  obtains r f where "terminates_with_res_time_order_IMP p r f T_f"
  using assms unfolding terminates_time_order_IMP_def by blast

definition "relate_rgt_time frgt crgt fs \<longleftrightarrow> (\<forall>f \<in> fs.
  terminates_time_order_IMP (com_from_crgt crgt f) (T_f_from_frgt frgt f o lookup_args crgt f))"
(* note that terminates_time_order_IMP imposes only an upper bound on the running time, even though it could really by exact *)

definition "some_constant_f frgt crgt f =
  some_constant_IMP (com_from_crgt crgt f) (T_f_from_frgt frgt f o lookup_args crgt f)"

definition "some_constant_fs frgt crgt fs =
  max_list0 (map (some_constant_f frgt crgt) fs)"

definition "some_constant_t frgt crgt t =
  some_constant_fs frgt crgt (calls_names t)"

lemma some_constant_trace_to_term:
  assumes "set fs \<subseteq> calls_names_set t"
  shows "some_constant_fs frgt crgt fs \<le> some_constant_t frgt crgt t"
proof-
  have "set (map (some_constant_f frgt crgt) fs) = some_constant_f frgt crgt ` set fs" by simp
  also from assms have "... \<subseteq> some_constant_f frgt crgt ` calls_names_set t" by blast
  also have "... = set (map (some_constant_f frgt crgt) (calls_names t))" by auto
  finally show ?thesis
  unfolding some_constant_fs_def some_constant_t_def using max_list0_subset by blast
qed


lemma rel_trace_time:
  assumes "rel_trace_calls crgt hT cT"
  assumes "relate_rgt_time frgt crgt (set (map fst hT))"
  shows "\<exists>z. IMP_Tailcall_Traces.interp_trace 0 cT z \<and>
             z \<le> some_constant_fs frgt crgt (map fst hT) * (length hT + HOL_TCN_Timing.interp_trace frgt 0 hT)"
(* note: `length hT` is bounded by the number of recursive calls, so this is still "linear" *)
proof-
  from assms(1) have "length hT = length cT" unfolding rel_trace_calls_def by blast
  then show ?thesis
  using assms proof (induction rule: list_induct2)
    case Nil
    then show ?case by simp
  next
    case (Cons hg hT cg cT)
    let ?gr = "fst hg" and ?gargs = "snd hg"
    let ?gcom = "fst cg" and ?gs = "snd cg"

    (* first handle the head of the list:
        - show ?gcom(?gs) runs in time z1
        - show z1 \<le> c_?gr * T_?gr(?gargs) *)

    from Cons.prems(1) have "rel_trace_call crgt ?gr ?gargs ?gcom ?gs"
      unfolding rel_trace_calls_def by auto
    then have rel1: "?gcom = com_from_crgt crgt ?gr" "?gargs = lookup_args crgt ?gr ?gs"
      unfolding rel_trace_call_def by simp_all

    let ?T_f = "T_f_from_frgt frgt ?gr o lookup_args crgt ?gr"
    let ?c1 = "some_constant_IMP ?gcom ?T_f"

    have "?gr \<in> set (map fst (hg # hT))" by simp
    with Cons.prems(2) rel1 have
        "terminates_time_order_IMP ?gcom ?T_f"
      unfolding relate_rgt_time_def by simp
    then obtain r f where
        "terminates_with_res_time_order_IMP ?gcom r f ?T_f"
      unfolding terminates_time_order_IMP_def by blast
    with some_constant_IMP_as_bound have
        "HOL_Nat_To_IMP.terminates_with_res_time_IMP ?gcom ?gs r (f ?gs) (?c1 * (?T_f ?gs)\<^sub>+)" by blast
    then obtain z1 s' where g:
        "(?gcom, ?gs) \<Rightarrow>\<^bsup> z1 \<^esup> s'" "z1 \<le> ?c1 * (?T_f ?gs)\<^sub>+"
      using HOL_Nat_To_IMP.terminates_with_res_time_IMPE by blast

    (* then obtain the IH for the tail of the trace *)

    let ?c2 = "some_constant_fs frgt crgt (map fst hT)"
    from Cons obtain z2 where gs:
        "IMP_Tailcall_Traces.interp_trace 0 cT z2"
        "z2 \<le> ?c2 * (length hT + HOL_TCN_Timing.interp_trace frgt 0 hT)"
      unfolding rel_trace_calls_def relate_rgt_time_def by auto

    (* now put it together *)

    let ?c = "some_constant_fs frgt crgt (map fst (hg # hT))"
    have c: "?c = max ?c1 ?c2"
      unfolding some_constant_fs_def some_constant_f_def using max_list0_cons rel1 by simp

    show ?case
    proof (rule exI, rule conjI)
      have "IMP_Tailcall_Traces.interp_trace 0 [(?gcom, ?gs)] z1"
        using IMP_Tailcall_Traces.interp_trace_singleton' g by blast
      with gs show "IMP_Tailcall_Traces.interp_trace 0 (cg # cT) (z1 + z2)"
        using IMP_Tailcall_Traces.interp_trace_append by force
    next
      from g rel1 c have "z1 \<le> ?c * (T_f_from_frgt frgt ?gr ?gargs)\<^sub>+" using le_trans nat_mult_max_left by force
      also have "... = ?c * (HOL_TCN_Timing.interp_trace frgt 0 [hg])\<^sub>+"
        unfolding HOL_TCN_Timing.interp_trace_singleton[symmetric, where n = 0, simplified add_0_left] by simp
      also have "... \<le> ?c * (1 + HOL_TCN_Timing.interp_trace frgt 0 [hg])" by (simp add: max1_def)
      finally have *: "z1 \<le> ?c * (1 + HOL_TCN_Timing.interp_trace frgt 0 [hg])" .

      from gs c have **: "z2 \<le> ?c * (length hT + HOL_TCN_Timing.interp_trace frgt 0 hT)" using le_trans[of z2] nat_mult_max_left by force

      from * ** have "z1 + z2 \<le> ?c * ((1 + length hT) + (HOL_TCN_Timing.interp_trace frgt 0 [hg] + HOL_TCN_Timing.interp_trace frgt 0 hT))"
        by (simp add: algebra_simps)
      also have "... = ?c * (length (hg # hT) + HOL_TCN_Timing.interp_trace frgt 0 (hg # hT))"
        unfolding HOL_TCN_Timing.interp_trace_append[symmetric] by simp
      finally show "z1 + z2 \<le> some_constant_fs frgt crgt (map fst (hg # hT)) * (length (hg # hT) + HOL_TCN_Timing.interp_trace frgt 0 (hg # hT))" .
    qed
  qed
qed


(* todo move *)
lemma num_commands_nonzero: "HOL_TCN_Timing.num_commands f \<ge> 1" by (cases f) auto

definition "relate_rgt_f frgt crgt f \<longleftrightarrow>
  terminates_with_res_time_order_IMP (com_from_crgt crgt f) (ret_from_crgt crgt f)
    (f_from_frgt frgt f o lookup_args crgt f) (T_f_from_frgt frgt f o lookup_args crgt f)"

definition "relate_rgt frgt crgt fs \<longleftrightarrow> (\<forall>f \<in> fs. relate_rgt_f frgt crgt f)"

(* todo: move *)
lemma terminates_with_res_time_order_combine:
  "terminates_with_res_time_order_IMP c r f T_f \<longleftrightarrow>
    (\<forall>s. terminates_with_res_IMP c s r (f s)) \<and> terminates_time_order_IMP c T_f"
proof
  assume *: "terminates_with_res_time_order_IMP c r f T_f"
  have "terminates_with_res_IMP c s r (f s)" for s
  proof-
    from * obtain z where "HOL_Nat_To_IMP.terminates_with_res_time_IMP c s r (f s) z" by blast
    then show "terminates_with_res_IMP c s r (f s)"
      using HOL_Nat_To_IMP.terminates_with_res_time_IMPE terminates_with_IMPI terminates_with_res_IMPI by metis
  qed
  moreover have "terminates_time_order_IMP c T_f" using * by blast
  ultimately show "(\<forall>s. terminates_with_res_IMP c s r (f s)) \<and> terminates_time_order_IMP c T_f" by blast
next
  assume "(\<forall>s. terminates_with_res_IMP c s r (f s)) \<and> terminates_time_order_IMP c T_f"
  then have
    "\<And>s. terminates_with_res_IMP c s r (f s)"
    "terminates_time_order_IMP c T_f" by blast+
  then show "terminates_with_res_time_order_IMP c r f T_f"
    using
      terminates_time_order_IMP_E terminates_with_res_time_order_IMP_E HOL_Nat_To_IMP.terminates_with_res_time_IMPE
      terminates_with_res_IMPE terminates_with_IMPE
      terminates_with_res_time_order_IMP_I HOL_Nat_To_IMP.terminates_with_res_time_IMPI
      bigstep_det
    by (smt (verit, best))
qed

lemma relate_rgt_combine_correctness_time:
    "relate_rgt frgt crgt fs \<longleftrightarrow> relate_rgt_correctness frgt crgt fs \<and> relate_rgt_time frgt crgt fs"
  unfolding relate_rgt_correctness_def relate_rgt_f_def relate_rgt_def relate_rgt_time_def
  using terminates_with_res_time_order_combine by auto


definition "the_hol_to_imp_c' frgt crgt f = (35 + some_constant_t frgt crgt f)"
(* definition "the_hol_to_imp_c frgt crgt f = 2 * (35 + some_constant_t frgt crgt f) * HOL_TCN_Timing.num_commands f" *)

lemma compiler_rel_time_end:
  assumes invar: "invar t" "invar f"
  assumes size_bound: "HOL_TCN_Timing.num_commands t \<le> HOL_TCN_Timing.num_commands f"
  assumes calls_bound: "calls_names_set t \<subseteq> calls_names_set f"
  assumes bigstep: "(f,frgt) \<turnstile> (t,vs_b,vs_arg) \<Rightarrow>\<^bsup> hz :: nat \<^esup> hv"
  assumes rgt: "relate_rgt frgt crgt (calls_names_set f)"
  assumes prereq:
    "check_compile crgt f_args bs keep t"
    "check_compile crgt f_args [] [] f"
  assumes state: "relate_exec_state f_args bs vs_arg vs_b s"
  shows
    "HOL_Nat_To_IMP.terminates_with_res_time_IMP_Tailcall
      (to_imp_tc f_args crgt [] r [] f) (to_imp_tc f_args crgt bs r keep t) s r hv
      (the_hol_to_imp_c' frgt crgt f * HOL_TCN_Timing.num_commands f * (hz + 1))"
proof-
  from rgt relate_rgt_combine_correctness_time
    have rgt_correctness: "relate_rgt_correctness frgt crgt (calls_names_set f)"
      and rgt_time: "relate_rgt_time frgt crgt (calls_names_set f)" by simp_all

  from bigstep invar HOL_TCN_Timing.bigstep_trace_end obtain hk hT
    where 5: "HOL_TCN_Timing.interp_trace frgt hk hT = hz"
    and htrace: "(f, frgt) \<turnstile> (t, vs_b, vs_arg) \<Rightarrow>\<^bsup>(hk, hT)\<^esup>  hv" by blast

  from calls_bound rgt_correctness have
      "relate_rgt_correctness frgt crgt (calls_names_set t)"
    unfolding relate_rgt_correctness_def by blast
  with compiler_rel_trace_end[OF invar size_bound calls_bound htrace prereq rgt_correctness state] obtain k cT s'
    where ctrace: "to_imp_tc f_args crgt [] r [] f \<turnstile>(to_imp_tc f_args crgt bs r keep t, s) \<Rightarrow>\<^bsup>(k, cT)\<^esup> s'"
    and rel_tr: "rel_trace_to_end crgt r hT hv cT s'"
    and rel_tr_time: "rel_trace_time f hk k"
    and 4: "length hT \<le> HOL_TCN_Timing.num_commands f * (hk + 1)"
    by blast

  from ctrace IMP_Tailcall_Traces.trace_end_bigstep obtain z
    where "IMP_Tailcall_Traces.interp_trace k cT z"
    and cexec: "to_imp_tc f_args crgt [] r [] f \<turnstile> (to_imp_tc f_args crgt bs r keep t, s) \<Rightarrow>\<^bsup>z :: nat\<^esup> s'" by blast
  then obtain cTz
    where 1: "z = k + cTz"
      and cTz: "IMP_Tailcall_Traces.interp_trace 0 cT cTz"
    by (metis IMP_Tailcall_Traces.interp_trace_def add.commute add_0)

  show ?thesis
  proof (rule HOL_Nat_To_IMP.terminates_with_res_time_IMP_TailcallI[OF cexec])
    from rel_tr show "s' r = hv" unfolding rel_trace_to_end_def by blast
  next
    from rel_tr_time have 2: "k \<le> 35 * HOL_TCN_Timing.num_commands f * (hk + 1)"
      unfolding rel_trace_time_def by blast

    from calls_bound htrace htrace_to_end_calls_in have calls_in: "set (map fst hT) \<subseteq> calls_names_set f" by blast

    from calls_in some_constant_trace_to_term have some_const:
      "some_constant_fs frgt crgt (map fst hT) \<le> some_constant_t frgt crgt f" by blast

    from rel_tr have "rel_trace_calls crgt hT cT" unfolding rel_trace_to_end_def by blast
    moreover with calls_in rgt_time have "relate_rgt_time frgt crgt (set (map fst hT))"
      unfolding relate_rgt_time_def by blast
    ultimately have x:
      "cTz \<le> some_constant_fs frgt crgt (map fst hT) * (length hT + HOL_TCN_Timing.interp_trace frgt 0 hT)"
      using rel_trace_time interp_trace_determ cTz by blast
    then have 3: "cTz \<le> some_constant_t frgt crgt f * (length hT + HOL_TCN_Timing.interp_trace frgt 0 hT)"
      using some_const mult_le_mono1 le_trans by blast

    from 1 have "z = k + cTz" .
    also have
      "... \<le> 35 * HOL_TCN_Timing.num_commands f * (hk + 1)
             + some_constant_t frgt crgt f
               * (HOL_TCN_Timing.num_commands f * (hk + 1) + HOL_TCN_Timing.interp_trace frgt 0 hT)"
      using add_le_mono[OF 2 le_trans[OF 3 _]] 4 by simp
    also have
      "... = the_hol_to_imp_c' frgt crgt f * HOL_TCN_Timing.num_commands f * (hk + 1)
             + some_constant_t frgt crgt f * HOL_TCN_Timing.interp_trace frgt 0 hT"
      unfolding the_hol_to_imp_c'_def by algebra
    also have
      "... \<le> the_hol_to_imp_c' frgt crgt f * HOL_TCN_Timing.num_commands f * (hk + 1)
             + the_hol_to_imp_c' frgt crgt f * HOL_TCN_Timing.num_commands f * HOL_TCN_Timing.interp_trace frgt 0 hT"
      unfolding the_hol_to_imp_c'_def
      using mult_le_mono[OF _ HOL_TCN_To_IMP_Temp.num_commands_nonzero] by simp
    also have
      "... = the_hol_to_imp_c' frgt crgt f * HOL_TCN_Timing.num_commands f * (hz + 1)"
      using 5[symmetric] interp_trace_n[where n = hk] by (simp add: algebra_simps)
    finally show "z \<le> the_hol_to_imp_c' frgt crgt f * HOL_TCN_Timing.num_commands f * (hz + 1)" .
  qed
qed


(* unneeded, TODO: move *)
lemma ignores_free:
  assumes "(f,frgt) \<turnstile> (t,vs_b,vs_arg) \<Rightarrow>\<^bsup> z :: nat \<^esup> v"
  shows "(f,frgt) \<turnstile> (t,vs_b @ supp,vs_arg) \<Rightarrow>\<^bsup> z :: nat \<^esup> v"
using assms proof (induction rule: hbig_step_t_induct)
  case (hLetBound n bs f t xs)
  show ?case
  proof (rule hbig_step_t_hLetBound')
    show "bs ! n = (bs @ supp) ! n" "n < length (bs @ supp)"
      using \<open>n < length bs\<close> by (simp_all add: nth_append_left)
  qed simp
qed auto
corollary ignores_free':
  assumes "(f,frgt) \<turnstile> (t,[],vs_arg) \<Rightarrow>\<^bsup> z :: nat \<^esup> v"
  shows "(f,frgt) \<turnstile> (t,supp,vs_arg) \<Rightarrow>\<^bsup> z :: nat \<^esup> v"
  using ignores_free[OF assms] by simp


theorem compiler_correct:
  assumes invar: "invar t"
  assumes bigstep: "\<And>vs_arg. length vs_arg = length f_args \<Longrightarrow> (t,frgt) \<turnstile> (t,[],vs_arg) \<Rightarrow>\<^bsup> T_f vs_arg :: nat \<^esup> f vs_arg"
  assumes rgt: "relate_rgt frgt crgt (calls_names_set t)"
  assumes prereq: "check_compile crgt f_args [] [] t"
  shows
    "terminates_with_res_time_order_IMP_Tailcall
      (to_imp_tc f_args crgt [] r [] t) (to_imp_tc f_args crgt [] r [] t) r
      (f o lookups f_args) (T_f o lookups f_args)"
proof-
  let ?T = "\<lambda>s. the_hol_to_imp_c' frgt crgt t * HOL_TCN_Timing.num_commands t * (T_f (lookups f_args s) + 1)"

  show ?thesis
  proof (rule terminates_with_res_time_order_IMP_TailcallI)
    show "?T \<le>\<^sub>c T_f o lookups f_args"
      unfolding comp_def
      unfolding order_of_ab distrib_left by blast
      (* by (rule order_of_const_mult[OF order_of_plus[OF order_of_refl order_of_const]]) *) (* also works *)
  next
    fix s
    let ?vs_arg = "lookups f_args s"
    have bound:
      "HOL_TCN_Timing.num_commands t \<le> HOL_TCN_Timing.num_commands t"
      "calls_names_set t \<subseteq> calls_names_set t" by simp_all
    from bigstep have bigstep': "(t,frgt) \<turnstile> (t,[],?vs_arg) \<Rightarrow>\<^bsup> T_f ?vs_arg :: nat \<^esup> f ?vs_arg" by simp
    have state: "relate_exec_state f_args [] (lookups f_args s) [] s" unfolding relate_exec_state_def by blast

    from compiler_rel_time_end invar bound bigstep' rgt prereq state
    show "HOL_Nat_To_IMP.terminates_with_res_time_IMP_Tailcall
           (to_imp_tc f_args crgt [] r [] t) (to_imp_tc f_args crgt [] r [] t) s r
           ((f o lookups f_args) s) (?T s)" by simp
  qed
qed

(* todo: move *)
lemma bigstep_can_terminate:
  assumes "(f,frgt) \<turnstile> (t,bs,vs_arg) \<Rightarrow>\<^bsup> z :: nat \<^esup> v"
  shows "can_terminate f \<or> can_terminate t"
  using assms by (induction rule: hbig_step_t_induct) auto

corollary compiler_correct':
  assumes invar: "invar t"
  assumes bigstep: "\<And>vs_arg. length vs_arg = length f_args \<Longrightarrow> (t,frgt) \<turnstile> (t,[],vs_arg) \<Rightarrow>\<^bsup> T_f vs_arg :: nat \<^esup> f vs_arg"
  assumes rgt: "relate_rgt frgt crgt (calls_names_set t)"
  assumes prereq: "check_compile crgt f_args [] [] t"
  shows
    "terminates_with_res_time_order_IMP
      (tailcall_to_IMP (to_imp_tc f_args crgt [] r [] t)) r
      (f o lookups f_args) (T_f o lookups f_args)"
proof (cases "can_terminate t")
  case can_term: True
  from
    to_imp_invar[OF invar] to_imp_r_in_vars[OF can_term]
    compiler_correct[OF invar bigstep rgt prereq]
    terminates_with_res_time_order_IMP_Tailcall_to_IMP
  show ?thesis by blast
next
  let ?vs_arg = "replicate (length f_args) 0"
  case False
  then have False using bigstep_can_terminate bigstep[of ?vs_arg] by fastforce
  then show ?thesis by blast
qed


section \<open>Examples\<close>

subsection \<open>Primitives\<close>

(* primitives: +, - *)

lemma terminates_with_res_const:
  assumes "\<And>s. (c, s) \<Rightarrow>\<^bsup> z :: nat \<^esup> s' s"
  assumes "\<And>s. (s' s) r = (f o lookups args) s"
  assumes "\<And>s. T_f s = 0"
  shows "terminates_with_res_time_order_IMP c r (f o lookups args) T_f"
proof (rule terminates_with_res_time_order_IMP_I)
  show "(\<lambda>_. z) \<le>\<^sub>c T_f" using assms by fastforce
next
  fix s show "HOL_Nat_To_IMP.terminates_with_res_time_IMP c s r ((f o lookups args) s) z"
    apply (rule HOL_Nat_To_IMP.terminates_with_res_time_IMPI)
    using assms by blast+
qed

abbreviation "mk_frgt1 f T_f \<equiv> ((f, T_f) :: fun_registry_entry)"
abbreviation "mk_crgt1 args tcom r \<equiv> ((args, tcom, r) :: com_registry_entry)"


definition [simp]: "plus_name \<equiv> ''+''"
definition [simp]: "(plus_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. xs ! 0 + xs ! 1)"
definition [simp]: "(plus_T_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. 0)"
definition [simp]: "plus_args \<equiv> [''+.args.x'', ''+.args.y'']"
definition "plus_com \<equiv> Assign ''+.ret'' (V ''+.args.x'' \<oplus>  V ''+.args.y'')"
definition [simp]: "plus_r \<equiv> ''+.ret''"

lemma plus_correctness:
  "terminates_with_res_time_order_IMP plus_com plus_r (plus_f o lookups plus_args) (plus_T_f o lookups plus_args)"
  unfolding plus_com_def
  by (rule terminates_with_res_const) fastforce+

definition [simp]: "plus_frgt_upd upd = upd(plus_name := mk_frgt1 plus_f plus_T_f)"
definition [simp]: "plus_crgt_upd upd = upd(plus_name := mk_crgt1 plus_args plus_com plus_r)"

(* callers will use this; make it general since each caller will have their own f/crgt *)
lemma plus_correctness_rgt:
  assumes "frgt plus_name = plus_frgt_upd null plus_name"
  assumes "crgt plus_name = plus_crgt_upd null plus_name"
  shows "relate_rgt_f frgt crgt plus_name"
  unfolding relate_rgt_f_def
  using assms plus_correctness by simp


definition [simp]: "minus_name \<equiv> ''-''"
definition [simp]: "(minus_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. xs ! 0 - xs ! 1)"
definition [simp]: "(minus_T_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. 0)"
definition [simp]: "minus_args \<equiv> [''-.args.x'', ''-.args.y'']"
definition "minus_com \<equiv> Assign ''-.ret'' (V ''-.args.x'' \<ominus>  V ''-.args.y'')"
definition [simp]: "minus_r \<equiv> ''-.ret''"

lemma minus_correctness:
  "terminates_with_res_time_order_IMP minus_com minus_r (minus_f o lookups minus_args) (minus_T_f o lookups minus_args)"
  unfolding minus_com_def
  by (rule terminates_with_res_const) fastforce+

definition [simp]: "minus_frgt_upd upd = upd(minus_name := mk_frgt1 minus_f minus_T_f)"
definition [simp]: "minus_crgt_upd upd = upd(minus_name := mk_crgt1 minus_args minus_com minus_r)"

lemma minus_correctness_rgt:
  assumes "frgt minus_name = minus_frgt_upd null minus_name"
  assumes "crgt minus_name = minus_crgt_upd null minus_name"
  shows "relate_rgt_f frgt crgt minus_name"
  unfolding relate_rgt_f_def
  using assms minus_correctness by simp


subsection \<open>Compiled functions\<close>

(* using the compiler *)

abbreviation (input) revapp (infixl "|>" 55) where "revapp x f \<equiv> f x"

lemma eq_on_lookup:
  fixes frgt :: fun_registry and f_frgt :: fun_registry
  assumes "frgt = f_frgt on f_aux"
  assumes "g \<in> f_aux"
  shows "frgt g = f_frgt g"
  using assms by blast

lemma bigstep_start:
  assumes "t \<equiv> t_def"
  assumes "(t, frgt) \<turnstile> (t_def, bs, xs)\<Rightarrow>\<^bsup> T_f xs :: nat \<^esup> f xs"
  shows "(t, frgt) \<turnstile> (t, bs, xs)\<Rightarrow>\<^bsup> T_f xs :: nat \<^esup> f xs"
  using assms by simp

lemma bigstep_apply_ih:
  assumes "T_f xs = T_f xs' + k"
  assumes "f xs = f xs'"
  assumes "(t, frgt) \<turnstile> (t, [], xs')\<Rightarrow>\<^bsup> T_f xs' :: nat \<^esup> f xs'"
  shows "(t, frgt) \<turnstile> (t, [], xs')\<Rightarrow>\<^bsup> T_f xs - k \<^esup> f xs"
  using assms by simp

lemma forall_i_length_Cons:
  assumes "P 0 x"
  assumes "\<forall>i < length xs. P (Suc i) (xs ! i)"
  shows "\<forall>i < length (x # xs). P i ((x # xs) ! i)"
  using assms by (simp add: All_less_Suc2)

lemma forall_i_insert:
  fixes A
  assumes "P x" and "\<forall>x \<in> A. P x"
  shows "\<forall>x \<in> insert x A. P x"
  using assms by simp

lemma relate_rgt_unfold:
  assumes "f_aux = fs"
  assumes "\<forall>f \<in> fs. relate_rgt_f frgt crgt f"
  shows "relate_rgt frgt crgt f_aux"
  using assms unfolding relate_rgt_def by blast

lemma terminates_with_res_time_order_IMP_mono':
  assumes "f = f'"
  assumes "T_f \<le>\<^sub>c T_f'"
  assumes "terminates_with_res_time_order_IMP p r f T_f"
  shows "terminates_with_res_time_order_IMP p r f' T_f'"
  using assms terminates_with_res_time_order_IMP_mono by blast

lemma args_nil:
  shows "\<forall>i<length ([] :: thol list). (t, frgt) \<turnstile> ([] ! i, bs, xs) \<Rightarrow>\<^bsup> [] ! i :: nat\<^esup> [] ! i"
  by simp

lemma args_cons:
  assumes "(t, frgt) \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup> z1 :: nat\<^esup> v1"
  assumes "\<forall>i<length ts. (t, frgt) \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup> zs ! i :: nat\<^esup> vs ! i"
  shows "\<forall>i<length (t1 # ts). (t, frgt) \<turnstile> ((t1 # ts) ! i, bs, xs) \<Rightarrow>\<^bsup> (z1 # zs) ! i :: nat\<^esup> (v1 # vs) ! i"
proof (rule, rule)
  fix i assume *: "i < length (t1 # ts)"
  consider (0) "i = 0" | (cons) "i > 0" by linarith
  then show "(t, frgt) \<turnstile> ((t1 # ts) ! i, bs, xs) \<Rightarrow>\<^bsup>(z1 # zs) ! i\<^esup>  (v1 # vs) ! i"
  proof cases
    case 0 with assms(1) show ?thesis by simp
  next
    case cons
    with * assms(2) have "(t, frgt) \<turnstile> (ts ! (i - 1), bs, xs) \<Rightarrow>\<^bsup>zs ! (i - 1)\<^esup>  vs ! (i - 1)" by simp
    with cons show ?thesis by simp
  qed
qed

method exec_inference =
    (* u *)rule
      hbig_step_t.hLet hbig_step_t_hIf'
      hbig_step_t_hLetBound' hbig_step_t_hArg' hbig_step_t_hNumber'
      hbig_step_t.hCall hbig_step_t.hTail

method exec_arglist = (* u *)rule args_cons args_nil

method exec1 = rule refl | repeat \<open>exec_arglist\<close> | exec_inference
method exec_bigstep = repeat \<open>exec1\<close>


(*todo: move*)
lemma swap_registry:
  assumes "frgt = frgt' on calls_names_set t"
  assumes "frgt = frgt' on calls_names_set f"
  assumes "(f, frgt) \<turnstile> (t, bs, xs)\<Rightarrow>\<^bsup> z :: nat \<^esup> v"
  shows "(f, frgt') \<turnstile> (t, bs, xs)\<Rightarrow>\<^bsup> z :: nat \<^esup> v"
  using assms(3,1,2) proof (induction arbitrary: frgt' rule: hbig_step_t_induct)
  case hLet
  then show ?case apply simp using eq_on_subset apply blast done
next
  case hIfTrue
  then show ?case apply simp using eq_on_subset apply blast done
next
  case hIfFalse
  then show ?case apply simp using eq_on_subset apply blast done
next
  case [rule_format]: (hCall zs ts vs f frgt bs xs v' gr z')
  have *: "frgt' gr = frgt gr" using hCall.prems(1) by fastforce
  show ?case proof (rule hbig_step_t.hCall[OF _ _ allI[OF impI]])
    show "(f, frgt') \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>zs ! i\<^esup>  vs ! i" if "i < length ts" for i
      using hCall.IH[rule_format, of i, THEN conjunct2, OF that, rule_format, OF eq_on_subset hCall.prems(2), OF hCall.prems(1), OF calls_names_subset_call(2)]
      using that by simp
  qed (simp_all add: * hCall.hyps)
next
  case (hTail zs ts vs f frgt bs xs z' v' z'')
  show ?case proof (rule hbig_step_t.hTail[OF _ _ allI[OF impI]])
    show "(f, frgt') \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>zs ! i\<^esup>  vs ! i" if "i < length ts" for i
      using hTail.IH(1)[rule_format, of i, THEN conjunct2, OF that, rule_format, OF eq_on_subset hTail.prems(2), OF hTail.prems(1), OF calls_names_subset_tail]
      using that by simp
  next
    show "(f, frgt') \<turnstile> (f, [], vs) \<Rightarrow>\<^bsup>z'\<^esup>  v'"
      using hTail.IH(2)[OF hTail.prems(2,2)] .
  qed (simp_all add: hTail.hyps)
qed blast+


definition "EMBED (d :: nat) (h :: nat) (t :: thol) (z :: nat) \<equiv> (True \<equiv> True)"
lemma EMBED: "PROP EMBED d h t z" unfolding EMBED_def by simp
method EMBED = rule EMBED

definition "EMBED_ARG (v :: nat) (i :: nat) = v"
definition "EMBED_BOUND (v :: nat) (d :: nat) = v"
definition "(EMBED_TAIL :: 'a) = undefined"

(* don't simplify values which are copied into the time function directly from the source function, keeps defs alot nicer *)
definition "EMBED_PROTECT x = x"
lemma EMBED_PROTECT_cong[cong]: "EMBED_PROTECT x = EMBED_PROTECT x" by simp

lemma EMBED_start:
  assumes "PROP EMBED d v t z"
  assumes "PROP SIMPS_TO t t'"
  assumes "PROP SIMPS_TO z z'"
  shows "PROP EMBED d v t' z'"
  by EMBED

lemma EMBED_let:
  assumes "PROP EMBED d v1 t1 z1" "PROP EMBED (Suc d) (v2 (EMBED_BOUND v1 d)) t2 (z2 v1)"
  shows "PROP EMBED d (let x = v1 in v2 x) (LET t1 IN t2) (z1 + (let x = EMBED_PROTECT v1 in z2 x))"
  by EMBED

lemma EMBED_if:
  assumes "PROP EMBED d v1 t1 z1" "PROP EMBED d v2 t2 z2" "PROP EMBED d v3 t3 z3"
  shows "PROP EMBED d (if v1 \<noteq> 0 then v2 else v3) (IF t1 \<noteq>0 THEN t2 ELSE t3) (z1 + (if EMBED_PROTECT (v1 \<noteq> 0) then z2 else z3))"
  by EMBED

lemma EMBED_arg: shows "PROP EMBED d (EMBED_ARG v i) (hArg i) 0" by EMBED
lemma EMBED_bound: shows "PROP EMBED d (EMBED_BOUND v d') (hLetBound (d - d' - 1)) 0" by EMBED
lemma EMBED_num: shows "PROP EMBED d n (hNumber n) 0" by EMBED

lemma EMBED_call1:
  assumes "PROP EMBED d v1 t1 z1"
  shows "PROP EMBED d (g v1) (hCall gr [t1]) (sum_list [z1] + T_g [EMBED_PROTECT v1])"
  by EMBED
lemma EMBED_call2:
  assumes "PROP EMBED d v1 t1 z1" "PROP EMBED d v2 t2 z2"
  shows "PROP EMBED d (g v1 v2) (hCall gr [t1, t2]) (sum_list [z1, z2] + T_g [EMBED_PROTECT v1, EMBED_PROTECT v2])"
  by EMBED
lemma EMBED_call3:
  assumes "PROP EMBED d v1 t1 z1" "PROP EMBED d v2 t2 z2" "PROP EMBED d v3 t3 z3"
  shows "PROP EMBED d (g v1 v2 v3) (hCall gr [t1, t2, t3]) (sum_list [z1, z2, z3] + T_g [EMBED_PROTECT v1, EMBED_PROTECT v2, EMBED_PROTECT v3])"
  by EMBED
lemma EMBED_tail1:
  assumes "PROP EMBED d v1 t1 z1"
  shows "PROP EMBED d (f v1) (hTAIL [t1]) (sum_list [z1] + EMBED_PROTECT (EMBED_TAIL v1) + 1)"
  by EMBED
lemma EMBED_tail2:
  assumes "PROP EMBED d v1 t1 z1" "PROP EMBED d v2 t2 z2"
  shows "PROP EMBED d (f v1 v2) (hTAIL [t1, t2]) (sum_list [z1, z2] + EMBED_PROTECT (EMBED_TAIL v1 v2) + 1)"
  by EMBED
lemma EMBED_tail3:
  assumes "PROP EMBED d v1 t1 z1" "PROP EMBED d v2 t2 z2" "PROP EMBED d v3 t3 z3"
  shows "PROP EMBED d (f v1 v2 v3) (hTAIL [t1, t2, t3]) (sum_list [z1, z2, z3] + EMBED_PROTECT (EMBED_TAIL v1 v2 v3) + 1)"
  by EMBED

lemmas EMBED_core = EMBED_if EMBED_let EMBED_arg EMBED_bound EMBED_num

(* just looks nicer *)
method numeralize =
  (unfold numeral_3_eq_3[symmetric])?,
  (unfold numeral_2_eq_2[symmetric])?,
  (unfold One_nat_def[symmetric])?

method embed uses f_def embed_extra =
  rule EMBED_start,
  subst f_def,
  (rule embed_extra EMBED_core)+, (* why does \<open>repeat\<close> do something different here? *)
  (simp, numeralize, rule SIMPS_TOI; fail),
  (simp cong: if_cong, numeralize, (unfold EMBED_ARG_def EMBED_BOUND_def EMBED_PROTECT_def)?, rule SIMPS_TOI; fail)


(*
definition "embed_BOUND v1 d = v1"

lemma embed_start:
  assumes "(f', frgt) \<turnstile> (t', bs, xs)\<Rightarrow>\<^bsup> z' bs xs :: nat \<^esup> v"
  assumes "PROP SIMPS_TO f' f"
  assumes "PROP SIMPS_TO t' t"
  (* assumes "PROP SIMPS_TO z' z" *)
  (* assumes "PROP SIMPS_TO v v'" *)

  assumes "PROP SIMPS_TO (z' bs xs) (z bs xs)"
(*   assumes "PROP SIMPS_TO (v bs xs) (v' bs xs)" *)
  shows "(f, frgt) \<turnstile> (t, bs, xs)\<Rightarrow>\<^bsup> z bs xs :: nat \<^esup> v"
  using assms unfolding SIMPS_TO_def by simp

lemma embed_let:
  assumes "(f, frgt) \<turnstile> (t1, bs, xs)\<Rightarrow>\<^bsup> z1 :: nat \<^esup> v1"
  assumes "(f, frgt) \<turnstile> (t2, v1 # bs, xs)\<Rightarrow>\<^bsup> z2 :: nat \<^esup> v2 (embed_BOUND v1 (length bs))"
  shows "(f, frgt) \<turnstile> (LET t1 IN t2, bs, xs)\<Rightarrow>\<^bsup> z1 + z2 \<^esup> (let x = v1 in v2 x)"
  using hbig_step_t.hLet assms unfolding Let_def embed_BOUND_def by blast

lemma embed_if:
  assumes "(f, frgt) \<turnstile> (t1, bs, xs)\<Rightarrow>\<^bsup> z1 :: nat \<^esup> v1"
  assumes "v1 \<noteq> 0 \<Longrightarrow> (f, frgt) \<turnstile> (t2, bs, xs)\<Rightarrow>\<^bsup> z2 :: nat \<^esup> v2"
  assumes "v1 = 0 \<Longrightarrow> (f, frgt) \<turnstile> (t3, bs, xs)\<Rightarrow>\<^bsup> z3 :: nat \<^esup> v3"
  shows "(f, frgt) \<turnstile> (IF t1 \<noteq>0 THEN t2 ELSE t3, bs, xs)\<Rightarrow>\<^bsup> z1 + (if v1 \<noteq> 0 then z2 else z3) :: nat \<^esup> (if v1 \<noteq> 0 then v2 else v3)"
  apply (rule hbig_step_t_hIf'[OF assms(1)])
  using assms(2,3) by simp_all

lemma embed_arg:
  assumes "n < length xs"
  shows "(f, frgt) \<turnstile> (hArg n, bs, xs)\<Rightarrow>\<^bsup> 0 \<^esup> (xs ! n)"
  apply (rule hbig_step_t_hArg')
  using assms by simp_all

lemma embed_bound:
  assumes "bs \<noteq> []"
  assumes "bs ! (length bs - Suc d) = v"
  shows "(f, frgt) \<turnstile> (hLetBound (length bs - Suc d), bs, xs)\<Rightarrow>\<^bsup> 0 \<^esup> (embed_BOUND v d)"
  apply (rule hbig_step_t_hLetBound')
  unfolding embed_BOUND_def using assms by simp_all

lemma embed_num:
  shows "(f, frgt) \<turnstile> (hNumber n, bs, xs)\<Rightarrow>\<^bsup> 0 \<^esup> n"
  by (rule hbig_step_t.hNumber)

lemma embed_call1:
  assumes "(f, frgt) \<turnstile> (t1, bs, xs)\<Rightarrow>\<^bsup> z1 :: nat \<^esup> v1"
  assumes "f_from_frgt frgt gr [v1] = g v1"
  shows "(f, frgt) \<turnstile> (hCall gr [t1], bs, xs)\<Rightarrow>\<^bsup> sum_list [z1] + T_f_from_frgt frgt gr [v1] :: nat \<^esup> g v1"
proof (rule hbig_step_t.hCall)
  show "\<forall>i<length [t1]. (f, frgt) \<turnstile> ([t1] ! i, bs, xs) \<Rightarrow>\<^bsup>[z1] ! i\<^esup>  [v1] ! i"
    by (rule args_cons args_nil assms)+
qed (simp_all add: assms)

lemma embed_call2:
  assumes "(f, frgt) \<turnstile> (t1, bs, xs)\<Rightarrow>\<^bsup> z1 :: nat \<^esup> v1"
  assumes "(f, frgt) \<turnstile> (t2, bs, xs)\<Rightarrow>\<^bsup> z2 :: nat \<^esup> v2"
  assumes "f_from_frgt frgt gr [v1, v2] = g v1 v2"
  shows "(f, frgt) \<turnstile> (hCall gr [t1, t2], bs, xs)\<Rightarrow>\<^bsup> sum_list [z1, z2] + T_f_from_frgt frgt gr [v1, v2] :: nat \<^esup> g v1 v2"
proof (rule hbig_step_t.hCall)
  show "\<forall>i<length [t1, t2]. (f, frgt) \<turnstile> ([t1, t2] ! i, bs, xs) \<Rightarrow>\<^bsup>[z1, z2] ! i\<^esup>  [v1, v2] ! i"
    by (rule args_cons args_nil assms)+
qed (simp_all add: assms)

lemma embed_call3:
  assumes "(f, frgt) \<turnstile> (t1, bs, xs)\<Rightarrow>\<^bsup> z1 :: nat \<^esup> v1"
  assumes "(f, frgt) \<turnstile> (t2, bs, xs)\<Rightarrow>\<^bsup> z2 :: nat \<^esup> v2"
  assumes "(f, frgt) \<turnstile> (t3, bs, xs)\<Rightarrow>\<^bsup> z3 :: nat \<^esup> v3"
  assumes "f_from_frgt frgt gr [v1, v2, v3] = g v1 v2 v3"
  shows "(f, frgt) \<turnstile> (hCall gr [t1, t2, t3], bs, xs)\<Rightarrow>\<^bsup> sum_list [z1, z2, z3] + T_f_from_frgt frgt gr [v1, v2, v3] :: nat \<^esup> g v1 v2 v3"
proof (rule hbig_step_t.hCall)
  show "\<forall>i<length [t1, t2, t3]. (f, frgt) \<turnstile> ([t1, t2, t3] ! i, bs, xs) \<Rightarrow>\<^bsup>[z1, z2, z3] ! i\<^esup>  [v1, v2, v3] ! i"
    by (rule args_cons args_nil assms)+
qed (simp_all add: assms)

lemmas embed_base = embed_let embed_if embed_arg embed_bound embed_num *)


lemma Ball_cons: assumes "P x" "\<forall>y \<in> set xs. P y" shows "\<forall>y \<in> set (x # xs). P y"
  using assms by simp
method check_arg_count = (repeat \<open>rule Ball_cons check_arg_count.intros\<close>; simp)

declare [[goals_limit=1000]]

(* lemmas if_bool_simps[simp] = if_P[where x = "1 :: nat" and y = 0] if_not_P[where x = "1 :: nat" and y = 0] *)


method to_imp_tc_unfold uses def =
  rule SIMPS_TOD,
  simp add:
    def generate_def Let_def split_beta
    make_n_fresh_def make_nth_fresh_def stale_registers_def call_registers_def Fresh.fresh_def
    char_of_def bit_simps,
  rule SIMPS_TOI


subsubsection \<open>Handling Booleans\<close>

(* future work needs to integrate with the existing datatype
    translation functionality, but we just hack boolean equality in *)
definition unbool :: "bool \<Rightarrow> nat" where "unbool b = (if b then 1 else 0)"
time_fun unbool

(* need to find the right balance of simplification rules so that termination proofs go through *)
lemma unbool_simps[simp]: "unbool True = 1" "unbool False = 0" unfolding unbool_def by simp_all
lemma unbool_neg_iff[iff]: "unbool b = 0 \<longleftrightarrow> \<not> b" by (cases b; simp)

definition unbool_if_else :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "unbool_if_else x1 x2 x3 = (if x1 \<noteq> 0 then x2 else x3)"
lemma unbool_if_else: "(if b then x1 else x2) = (unbool_if_else (unbool b) x1 x2)"
  unfolding unbool_if_else_def by simp

subsubsection \<open>Equality\<close>

(* the following comments refer to preliminary work to embed HOL functions to HOL-TCNat
    and prove their relatedness lemmas automatically *)

(* part i: holtcn \<rightarrow> funtc *)

(* a function and its timing function are provided by the user *)
definition eq :: "nat \<Rightarrow> nat \<Rightarrow> nat" where [simp]: "eq x y = unbool (x = y)"
time_fun eq

(* "register" eq as a boolean function *)
lemma unbool_eq: "unbool (x = y) = eq x y" unfolding eq_def by simp

(* a function we can actually compile must also be provided, i.e., a tail-recursive
    function on nats which refers only to already compiled functions *)
definition eq' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  [simp]: "eq' x y = (let a = x - y in let b = y - x in if a + b \<noteq> 0 then 0 else 1)"

(* embed the function! *)
schematic_goal "PROP EMBED 0 (eq' (EMBED_ARG x 0) (EMBED_ARG y 1)) ?t ?z"
  supply EMBED_extra =
    EMBED_call2[where g = "(-)" and T_g = minus_T_f and gr = minus_name]
    EMBED_call2[where g = "(+)" and T_g = plus_T_f and gr = plus_name]
  by (embed f_def: eq'_def embed_extra: EMBED_extra)

(* the embedded term and the timing function are extracted from the theorem
    (currently that means copy-pasting, but the principle should be clear!) *)
definition [simp]: "eq_hol_tcn \<equiv>
  LET hCall ''-'' [hArg 0, hArg 1] IN
  LET hCall ''-'' [hArg 1, hArg 0] IN
  IF hCall ''+'' [hLetBound 1, hLetBound 0] \<noteq>0
  THEN hNumber 0 ELSE hNumber 1"

definition [simp]: "T_eq' \<equiv> ((\<lambda>x y. 0) :: nat \<Rightarrow> nat \<Rightarrow> nat)"

(* the user needs to prove that the HOL timing function bounds ours
  (which in the usual case should just be an induction/auto);
  in principle) this could be weakened to a linear overhead *)
lemma eq': "eq' x y = eq x y" by simp
lemma T_eq': "T_eq' x y \<le> T_eq x y" by simp

(* part ii: funtc \<rightarrow> imptc *)

definition [simp]: "eq_arg_count \<equiv> 2"

(* an frgt is built for all auxiliary functions in eq' *)
definition [simp]: "eq_frgt \<equiv> null |> plus_frgt_upd |> minus_frgt_upd"

(* the functions and timing functions are lifted to lists *)
definition [simp]: "(eq_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. eq (xs ! 0) (xs ! 1))"
definition [simp]: "(eq_T_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. T_eq (xs ! 0) (xs ! 1))"
definition [simp]: "(eq'_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. eq' (xs ! 0) (xs ! 1))"
definition [simp]: "(eq'_T_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. T_eq' (xs ! 0) (xs ! 1))"

(* then functional and time correctness is proven *)
lemma eq_hol_tcn_correctness:
  assumes *: "length xs = eq_arg_count"
  shows "(eq_hol_tcn, eq_frgt) \<turnstile> (eq_hol_tcn, [], xs)\<Rightarrow>\<^bsup> eq'_T_f xs :: nat \<^esup> eq'_f xs"
  apply (rule bigstep_start[OF eq_hol_tcn_def])
  apply exec_bigstep
  by (auto simp add: *)

(* finally, the FUNtc term is compiled to IMPtc and IMP *)
(* arguments/auxiliary functions/return register *)
definition [simp]: "eq_args \<equiv> [''=.args.x'', ''=.args.y'']"
definition [simp]: "eq_r \<equiv> ''=.ret''"
definition [simp]: "eq_crgt \<equiv> null |> plus_crgt_upd |> minus_crgt_upd"
(* compile to IMPtc then to IMP *)
definition "eq_tcom \<equiv> to_imp_tc eq_args eq_crgt [] eq_r [] eq_hol_tcn"
definition "eq_com \<equiv> tailcall_to_IMP eq_tcom"

(* just for show ;) *)
schematic_goal "eq_tcom \<equiv> ?t"
  oops (* by (to_imp_tc_unfold def: eq_tcom_def) (* works, but slow :( *) *)

(* now the compiler correctness lemma shall be used! *)
lemma eq_correctness':
  "terminates_with_res_time_order_IMP eq_com eq_r (eq'_f o lookups eq_args) (eq'_T_f o lookups eq_args)"
  unfolding eq_com_def eq_tcom_def
proof (rule compiler_correct')
  (* this is the correctness lemma for HOL-TCN *)
  fix vs_arg :: "nat list"
  assume "length vs_arg = length eq_args"
  then show "(eq_hol_tcn, eq_frgt) \<turnstile> (eq_hol_tcn, [], vs_arg) \<Rightarrow>\<^bsup>eq'_T_f vs_arg\<^esup>  eq'_f vs_arg"
    using eq_hol_tcn_correctness by simp
next
  (* here we use correctness lemmas for each called function *)
  show "relate_rgt eq_frgt eq_crgt (calls_names_set eq_hol_tcn)"
    apply (rule relate_rgt_unfold) apply simp
    using plus_correctness_rgt minus_correctness_rgt by fastforce
next
  (* these last three goals are mostly rewriting/simplifying function definitions *)
  show "check_compile eq_crgt eq_args [] [] eq_hol_tcn"
  proof (rule check_compileI)
    show "(length eq_args, eq_crgt) \<turnstile> eq_hol_tcn"
      unfolding eq_hol_tcn_def by check_arg_count
  qed auto
  show "HOL_TCN_Timing.invar eq_hol_tcn" by simp
qed

(* now we replace the generated value and timing functions with the user's again *)
corollary eq_correctness:
  "terminates_with_res_time_order_IMP eq_com eq_r (eq_f o lookups eq_args) (eq_T_f o lookups eq_args)"
proof (rule terminates_with_res_time_order_IMP_mono'[OF _ _ eq_correctness'])
  show "eq'_f o lookups eq_args = eq_f o lookups eq_args"
    using eq' by simp
next
  show "eq'_T_f o lookups eq_args \<le>\<^sub>c eq_T_f o lookups eq_args"
    apply (rule order_of_le)
    using T_eq' by simp
qed

(* set of called functions *)
(* definition [simp]: "eq_aux \<equiv> calls_names_set eq_hol_tcn"
(* note: *) lemma "eq_aux = {''+'', ''-''}" by auto *)

(* used by any callers of eq *)
definition [simp]: "eq_name \<equiv> ''=''"
definition [simp]: "eq_frgt_upd upd = upd(eq_name := mk_frgt1 eq_f eq_T_f)"
definition [simp]: "eq_crgt_upd upd = upd(eq_name := mk_crgt1 eq_args eq_com eq_r)"

lemma eq_correctness_rgt:
  assumes "frgt eq_name = eq_frgt_upd null eq_name"
  assumes "crgt eq_name = eq_crgt_upd null eq_name"
  shows "relate_rgt_f frgt crgt eq_name"
proof -
  from assms(1) have *: "frgt eq_name = mk_frgt1 eq_f eq_T_f"
    by (metis eq_frgt_upd_def fun_upd_same)
  from assms(2) have **: "crgt eq_name = mk_crgt1 eq_args eq_com eq_r"
    by (metis eq_crgt_upd_def fun_upd_same)
  show ?thesis
    unfolding relate_rgt_f_def using eq_correctness * ** by (metis split_pairs)
  (* perhaps need a way to make this more automatic *)
qed


subsubsection \<open>Multiplication (with accumulator)\<close>
(* Multiplication, see above for general comments. Here we provide some more ideas for handling
  functions and timing functions that aren't defined the same in HOL as in HOL-TCN,
  and address recursion *)

(* this is the function that the user wants to model *)
definition mul_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where [simp]: "mul_acc x y z = x * y + z"

(* this is the timing function that the user wants the modelled function to have *)
definition T_mul_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where [simp]: "T_mul_acc x y z = x"

(* the user also needs to provide a tail-recursive function equal to the modelled function *)
fun mul_acc' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mul_acc' 0 _ z = z" |
  "mul_acc' (Suc x) y z = mul_acc' x y (y + z)"
declare mul_acc'.simps[simp del] (* be explicit and use simp add: mul_acc'_eq instead? *)

(* turn the function defined on cases into an if/else and eliminate booleans from conditions *)
case_of_simps mul_acc'_eq[
  unfolded case_nat_eq_if unbool_if_else,
  unfolded unbool_eq, (* extend as needed *)
  unfolded unbool_if_else_def
] : mul_acc'.simps

(* embed the function! *)
schematic_goal "PROP EMBED 0 (mul_acc' (EMBED_ARG x 0) (EMBED_ARG y 1) (EMBED_ARG z 2)) ?t ?z"
  supply EMBED_extra =
    EMBED_call2[where g = "(-)" and T_g = minus_T_f and gr = minus_name]
    EMBED_call2[where g = "(+)" and T_g = plus_T_f and gr = plus_name]
    EMBED_call2[where g = "eq" and T_g = eq_T_f and gr = eq_name]
    EMBED_tail3[where f = "mul_acc'"]
  by (embed f_def: mul_acc'_eq embed_extra: EMBED_extra)

(* the embedded term and the timing function are extracted from the theorem
    (currently that means copy-pasting, but the principle should be clear!) *)
definition [simp]: "mul_acc_hol_tcn \<equiv>
  IF hCall ''='' [hArg 0, hNumber 0]\<noteq>0 THEN hArg 2
  ELSE LET hCall ''-'' [hArg 0, hNumber 1]
       IN hTAIL [hLetBound 0, hArg 1, hCall ''+'' [hArg 1, hArg 2]]"

fun T_mul_acc' where
  "T_mul_acc' x y z = (if eq x 0 \<noteq> 0 then 0 else Suc (T_mul_acc' (x - 1) y (y + z)))"
declare T_mul_acc'.simps[simp del] (* infinite unfolding *)

(* the user needs to prove that the HOL timing function bounds ours
  (which in the usual case should just be an induction/auto);
  in principle) this could be weakened to a linear overhead *)
lemma mul_acc': "mul_acc' x y z = mul_acc x y z" by (induction x arbitrary: z; simp add: mul_acc'_eq)
lemma T_mul_acc': "T_mul_acc' x y z \<le> T_mul_acc x y z" by (induction x arbitrary: z; simp add: T_mul_acc'.simps)

definition [simp]: "mul_acc_arg_count \<equiv> (3 :: nat)"
(* an frgt is built for all auxiliary functions *)
definition [simp]: "mul_acc_frgt \<equiv> null |> plus_frgt_upd |> minus_frgt_upd |> eq_frgt_upd"

(* the function and timing function are lifted to lists *)
definition [simp]: "(mul_acc_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. mul_acc (xs ! 0) (xs ! 1) (xs ! 2))"
definition [simp]: "(mul_acc_T_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. T_mul_acc (xs ! 0) (xs ! 1) (xs ! 2))"
definition [simp]: "(mul_acc'_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. mul_acc' (xs ! 0) (xs ! 1) (xs ! 2))"
definition [simp]: "(mul_acc'_T_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. T_mul_acc' (xs ! 0) (xs ! 1) (xs ! 2))"

lemma mul_acc_hol_tcn_correctness:
  assumes *: "length xs = mul_acc_arg_count"
  shows "(mul_acc_hol_tcn, mul_acc_frgt) \<turnstile> (mul_acc_hol_tcn, [], xs)\<Rightarrow>\<^bsup> mul_acc'_T_f xs :: nat \<^esup> mul_acc'_f xs"
using * proof (induction "xs ! 0" "xs ! 1" "xs ! 2" arbitrary: xs rule: mul_acc'.induct)
  case 1
  note len = \<open>length xs = _\<close> and ind_case = \<open>0 = xs ! 0\<close>[symmetric]
  show ?case
    apply (rule bigstep_start[OF mul_acc_hol_tcn_def])
    apply exec_bigstep
    by (simp_all add: len ind_case T_mul_acc'.simps mul_acc'_eq)
next
  case (2 x)
  note len = \<open>length xs = _\<close> and ind_case = \<open>Suc x = xs ! 0\<close>[symmetric]
  note ih = "2.hyps"(1)
  have **: "f_from_frgt mul_acc_frgt ''='' = eq_f" by simp
  show ?case
    apply (rule bigstep_start[OF mul_acc_hol_tcn_def])
    apply exec_bigstep
    prefer 17
    apply (rule bigstep_apply_ih[OF _ _ ih])
    apply (simp add: T_mul_acc'.simps; fail)
    apply (simp add: ind_case mul_acc'_eq; fail)
    by (simp_all add: len ind_case T_mul_acc'.simps mul_acc'_eq)
qed


(* finally, the FUNtc term is compiled to IMPtc and IMP *)
(* arguments/auxiliary functions/return register *)

definition [simp]: "mul_acc_args \<equiv> [''mul_acc.args.x'', ''mul_acc.args.y'', ''mul_acc.args.z'']"
definition [simp]: "mul_acc_r \<equiv> ''mul_acc.ret''"

definition [simp]: "mul_acc_crgt \<equiv> null |> plus_crgt_upd |> minus_crgt_upd |> eq_crgt_upd"

(* compile to IMPtc then to IMP *)
definition "mul_acc_tcom \<equiv> to_imp_tc mul_acc_args mul_acc_crgt [] mul_acc_r [] mul_acc_hol_tcn"
definition "mul_acc_com \<equiv> tailcall_to_IMP mul_acc_tcom"

(* just for show ;) *)
schematic_goal "mul_acc_tcom \<equiv> ?t"
  oops (* by (to_imp_tc_unfold def: mul_acc_tcom_def) *)

(* now the compiler correctness lemma shall be used! *)
lemma mul_acc_correctness':
  "terminates_with_res_time_order_IMP mul_acc_com mul_acc_r (mul_acc'_f o lookups mul_acc_args) (mul_acc'_T_f o lookups mul_acc_args)"
  unfolding mul_acc_com_def mul_acc_tcom_def
proof (rule compiler_correct')
  (* this is the correctness lemma for HOL-TCN *)
  fix vs_arg :: "nat list"
  assume "length vs_arg = length mul_acc_args"
  then show "(mul_acc_hol_tcn, mul_acc_frgt) \<turnstile> (mul_acc_hol_tcn, [], vs_arg) \<Rightarrow>\<^bsup>mul_acc'_T_f vs_arg\<^esup>  mul_acc'_f vs_arg"
    using mul_acc_hol_tcn_correctness by simp
next
  (* here we use correctness lemmas for each called function *)
  show "relate_rgt mul_acc_frgt mul_acc_crgt (calls_names_set mul_acc_hol_tcn)"
    apply (rule relate_rgt_unfold) apply simp
    using plus_correctness_rgt minus_correctness_rgt eq_correctness_rgt by fastforce
next
  (* these last three goals are mostly rewriting/simplifying function definitions *)
  show "check_compile mul_acc_crgt mul_acc_args [] [] mul_acc_hol_tcn"
  proof (rule check_compileI)
    show "(length mul_acc_args, mul_acc_crgt) \<turnstile> mul_acc_hol_tcn"
      unfolding mul_acc_hol_tcn_def by check_arg_count
  qed auto
  show "HOL_TCN_Timing.invar mul_acc_hol_tcn" by simp
qed

(* now we replace the generated value and timing functions with the user's again *)
corollary mul_acc_correctness:
  "terminates_with_res_time_order_IMP mul_acc_com mul_acc_r (mul_acc_f o lookups mul_acc_args) (mul_acc_T_f o lookups mul_acc_args)"
proof (rule terminates_with_res_time_order_IMP_mono'[OF _ _ mul_acc_correctness'])
  show "mul_acc'_f o lookups mul_acc_args = mul_acc_f o lookups mul_acc_args"
    using mul_acc' by simp
next
  show "mul_acc'_T_f o lookups mul_acc_args \<le>\<^sub>c mul_acc_T_f o lookups mul_acc_args"
    apply (rule order_of_le)
    using T_mul_acc' by simp
qed

(* set of called functions *)
definition [simp]: "mul_acc_aux \<equiv> calls_names_set mul_acc_hol_tcn"
(* note: *) lemma "mul_acc_aux = {''+'', ''-'', ''=''}" by auto

(* used by any callers of mul_acc *)
definition [simp]: "mul_acc_name \<equiv> ''mul_acc''"
definition [simp]: "mul_acc_frgt_upd upd = upd(mul_acc_name := mk_frgt1 mul_acc_f mul_acc_T_f)"
definition [simp]: "mul_acc_crgt_upd upd = upd(mul_acc_name := mk_crgt1 mul_acc_args mul_acc_com mul_acc_r)"

lemma mul_acc_correctness_rgt:
  assumes "frgt mul_acc_name = mul_acc_frgt_upd null mul_acc_name"
  assumes "crgt mul_acc_name = mul_acc_crgt_upd null mul_acc_name"
  shows "relate_rgt_f frgt crgt mul_acc_name"
proof -
  from assms(1) have *: "frgt mul_acc_name = mk_frgt1 mul_acc_f mul_acc_T_f"
    by (metis mul_acc_frgt_upd_def fun_upd_same)
  from assms(2) have **: "crgt mul_acc_name = mk_crgt1 mul_acc_args mul_acc_com mul_acc_r"
    by (metis mul_acc_crgt_upd_def fun_upd_same)
  show ?thesis
    unfolding relate_rgt_f_def using mul_acc_correctness * ** by (metis split_pairs)
  (* perhaps need a way to make this more automatic *)
qed


subsubsection \<open>Multiplication\<close>
(* now without an accumulator, this isn't as well organized as above *)

definition [simp]: "mul x y = mul_acc x y 0"
time_fun mul

definition [simp]: "(mul_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. mul (xs ! 0) (xs ! 1))"
definition [simp]: "(mul_T_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. T_mul (xs ! 0) (xs ! 1))"

(* embed the function! *)
schematic_goal "PROP EMBED 0 (mul (EMBED_ARG x 0) (EMBED_ARG y 1)) ?t ?z"
  supply EMBED_extra =
    EMBED_call3[where g = "mul_acc" and T_g = mul_acc_T_f and gr = mul_acc_name]
  by (embed f_def: mul_def embed_extra: EMBED_extra)

(* copy-paste from the reuslt *)
definition [simp]: "mul_hol_tcn \<equiv> hCall ''mul_acc'' [hArg 0, hArg 1, hNumber 0]"
definition [simp]: "T_mul' x y = x"

definition [simp]: "mul_aux \<equiv> calls_names_set mul_hol_tcn"
(* note: *) lemma "mul_aux = {''mul_acc''}" by auto

definition [simp]: "mul_frgt \<equiv> null |> mul_acc_frgt_upd"
definition [simp]: "mul_crgt \<equiv> null |> mul_acc_crgt_upd"

definition [simp]: "mul_name \<equiv> ''*''"
definition [simp]: "mul_args \<equiv> [''*.args.x'', ''*.args.y'']"
definition [simp]: "mul_r \<equiv> ''*.ret''"

definition "mul_tcom \<equiv> to_imp_tc mul_args mul_crgt [] mul_r [] mul_hol_tcn"
definition "mul_com \<equiv> tailcall_to_IMP mul_tcom"

definition [simp]: "mul_frgt_upd upd = upd(mul_name := mk_frgt1 mul_f mul_T_f)"
definition [simp]: "mul_crgt_upd upd = upd(mul_name := mk_crgt1 mul_args mul_com mul_r)"


lemma mul_hol_tcn_correctness:
  assumes rgt: "frgt = mul_frgt on mul_aux"
  assumes *: "length xs = length mul_args"
  shows "(mul_hol_tcn, frgt) \<turnstile> (mul_hol_tcn, [], xs)\<Rightarrow>\<^bsup> mul_T_f xs \<^esup> mul_f xs"
proof-
  have frgt: "frgt ''mul_acc'' = mk_frgt1 mul_acc_f mul_acc_T_f"
    using eq_on_lookup[of frgt mul_frgt, OF rgt] by auto

  show ?thesis
    apply (rule bigstep_start[OF mul_hol_tcn_def])
    apply exec_bigstep
    by (auto simp add: * frgt)
qed

lemma mul_correctness:
  "terminates_with_res_time_order_IMP mul_com mul_r (mul_f o lookups mul_args) (mul_T_f o lookups mul_args)"
  unfolding mul_com_def mul_tcom_def
proof (rule compiler_correct')
  fix vs_arg :: "nat list"
  assume "length vs_arg = length mul_args"
  then show "(mul_hol_tcn, mul_frgt) \<turnstile> (mul_hol_tcn, [], vs_arg) \<Rightarrow>\<^bsup>mul_T_f vs_arg\<^esup>  mul_f vs_arg"
    using mul_hol_tcn_correctness by blast
next
  show "relate_rgt mul_frgt mul_crgt (calls_names_set mul_hol_tcn)"
    apply (rule relate_rgt_unfold) apply simp
    apply (repeat \<open>rule forall_i_insert\<close>)
    using mul_acc_correctness_rgt by simp_all
  show "check_compile mul_crgt mul_args [] [] mul_hol_tcn"
  proof (rule check_compileI)
    show "(length mul_args, mul_crgt) \<turnstile> mul_hol_tcn"
      unfolding mul_hol_tcn_def by check_arg_count
  qed auto
  show "HOL_TCN_Timing.invar mul_hol_tcn" by simp
qed

lemma mul_correctness_rgt:
  assumes "frgt mul_name = mul_frgt_upd null mul_name"
  assumes "crgt mul_name = mul_crgt_upd null mul_name"
  shows "relate_rgt_f frgt crgt mul_name"
proof-
  from assms have
    "frgt mul_name = mk_frgt1 mul_f mul_T_f"
    "crgt mul_name = mk_crgt1 mul_args mul_com mul_r" by simp_all
  then show ?thesis unfolding relate_rgt_f_def using mul_correctness by (metis split_pairs2)
qed

schematic_goal "mul_tcom \<equiv> ?t"
  by (to_imp_tc_unfold def: mul_tcom_def)


subsubsection \<open>Square\<close>

abbreviation (input) "square x \<equiv> x\<^sup>2"
definition [simp]: "T_square (x :: nat) = x"

definition [simp]: "square' x \<equiv> mul x x"

(* embed the function! *)
schematic_goal "PROP EMBED 0 (square' (EMBED_ARG x 0)) ?t ?z"
  supply EMBED_extra =
    EMBED_call2[where g = "mul" and T_g = mul_T_f and gr = mul_name]
  by (embed f_def: square'_def embed_extra: EMBED_extra)

definition [simp]: "square_hol_tcn \<equiv> hCall ''*'' [hArg 0, hArg 0]"
definition [simp]: "T_square' x = x"

lemma square': "square' x = square x" by simp algebra
lemma T_square': "T_square' x \<le> T_square x" by simp

definition [simp]: "(square_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. square (xs ! 0))"
definition [simp]: "(square_T_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. T_square (xs ! 0))"
definition [simp]: "(square'_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. square' (xs ! 0))"
definition [simp]: "(square'_T_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. T_square' (xs ! 0))"

definition [simp]: "square_aux \<equiv> calls_names_set square_hol_tcn"
(* note: *) lemma "square_aux = {''*''}" by simp

definition [simp]: "square_frgt \<equiv> null |> mul_frgt_upd"
definition [simp]: "square_crgt \<equiv> null |> mul_crgt_upd"

definition [simp]: "square_name \<equiv> ''^2''"
definition [simp]: "square_args \<equiv> [''^2.args.x'']"
definition [simp]: "square_r \<equiv> ''^2.ret''"

definition "square_tcom \<equiv> to_imp_tc square_args square_crgt [] square_r [] square_hol_tcn"
definition "square_com \<equiv> tailcall_to_IMP square_tcom"

definition [simp]: "square_frgt_upd upd = upd(square_name := mk_frgt1 square_f square_T_f)"
definition [simp]: "square_crgt_upd upd = upd(square_name := mk_crgt1 square_args square_com square_r)"


lemma square_hol_tcn_correctness:
  assumes rgt: "frgt = square_frgt on square_aux"
  assumes *: "length xs = length square_args"
  shows "(square_hol_tcn, frgt) \<turnstile> (square_hol_tcn, [], xs)\<Rightarrow>\<^bsup> square'_T_f xs \<^esup> square'_f xs"
proof-
  have frgt: "frgt ''*'' = mk_frgt1 mul_f mul_T_f"
    using eq_on_lookup[of frgt square_frgt, OF rgt] by auto

  show "(square_hol_tcn, frgt) \<turnstile> (square_hol_tcn, [], xs)\<Rightarrow>\<^bsup> square'_T_f xs \<^esup> square'_f xs"
    apply (rule bigstep_start[OF square_hol_tcn_def])
    apply exec_bigstep
    by (auto simp add: * frgt)
qed

lemma square_correctness':
  "terminates_with_res_time_order_IMP square_com square_r (square'_f o lookups square_args) (square'_T_f o lookups square_args)"
  unfolding square_com_def square_tcom_def
proof (rule compiler_correct')
  fix vs_arg :: "nat list"
  assume "length vs_arg = length square_args"
  then show "(square_hol_tcn, square_frgt) \<turnstile> (square_hol_tcn, [], vs_arg) \<Rightarrow>\<^bsup>square'_T_f vs_arg\<^esup>  square'_f vs_arg"
    using square_hol_tcn_correctness by blast
next
  show "relate_rgt square_frgt square_crgt (calls_names_set square_hol_tcn)"
    apply (rule relate_rgt_unfold) apply simp
    apply (repeat \<open>rule forall_i_insert\<close>)
    using mul_correctness_rgt by simp_all
  show "check_compile square_crgt square_args [] [] square_hol_tcn"
  proof (rule check_compileI)
    show "(length square_args, square_crgt) \<turnstile> square_hol_tcn"
      unfolding square_hol_tcn_def by check_arg_count
  qed auto
  show "HOL_TCN_Timing.invar square_hol_tcn" by simp
qed

corollary square_correctness:
  "terminates_with_res_time_order_IMP square_com square_r (square_f o lookups square_args) (square_T_f o lookups square_args)"
proof (rule terminates_with_res_time_order_IMP_mono'[OF _ _ square_correctness'])
  show "square'_f o lookups square_args = square_f o lookups square_args"
    using square' by simp
next
  show "square'_T_f o lookups square_args \<le>\<^sub>c square_T_f o lookups square_args"
    apply (rule order_of_le) by simp
qed

lemma square_correctness_rgt:
  assumes "frgt square_name = square_frgt_upd null square_name"
  assumes "crgt square_name = square_crgt_upd null square_name"
  shows "relate_rgt_f frgt crgt square_name"
proof-
  from assms have
    "frgt square_name = mk_frgt1 square_f square_T_f"
    "crgt square_name = mk_crgt1 square_args square_com square_r" by simp_all
  then show ?thesis unfolding relate_rgt_f_def using square_correctness by (metis split_pairs2)
qed

schematic_goal "square_tcom \<equiv> ?t"
  by (to_imp_tc_unfold def: square_tcom_def)


subsubsection \<open>Less-than-equal\<close>

definition le :: "nat \<Rightarrow> nat \<Rightarrow> nat" where [simp]: "le x y = unbool (x \<le> y)"
time_fun le

definition [simp]: "(le_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. le (xs ! 0) (xs ! 1))"
definition [simp]: "(le_T_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. T_le (xs ! 0) (xs ! 1))"

(* "register" eq as a boolean function *)
lemma unbool_le: "unbool (x \<le> y) = le x y" by simp

definition le' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  [simp]: "le' x y = (if x - y = 0 then 1 else 0)"

lemmas le'_eq = le'_def[
  unfolded unbool_if_else,
  unfolded unbool_eq,
  unfolded unbool_if_else_def
]

(* embed the function! *)
schematic_goal "PROP EMBED 0 (le' (EMBED_ARG x 0) (EMBED_ARG y 1)) ?t ?z"
  supply EMBED_extra =
    EMBED_call2[where g = "(-)" and T_g = minus_T_f and gr = minus_name]
    EMBED_call2[where g = "eq" and T_g = eq_T_f and gr = eq_name]
  by (embed f_def: le'_eq embed_extra: EMBED_extra)

(* the embedded term and the timing function are extracted from the theorem
    (currently that means copy-pasting, but the principle should be clear!) *)
definition [simp]: "le_hol_tcn \<equiv>
  IF hCall ''='' [hCall ''-'' [hArg 0, hArg 1], hNumber 0]\<noteq>0 THEN hNumber 1 ELSE hNumber 0"

definition [simp]: "T_le' \<equiv> ((\<lambda>x y. 0) :: nat \<Rightarrow> nat \<Rightarrow> nat)"

lemma le': "le' x y = le x y" by simp
lemma T_le': "T_le' x y \<le> T_le x y" by simp

definition [simp]: "(le'_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. le' (xs ! 0) (xs ! 1))"
definition [simp]: "(le'_T_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. T_le' (xs ! 0) (xs ! 1))"

definition [simp]: "le_aux \<equiv> calls_names_set le_hol_tcn"
(* note: *) lemma "le_aux = {''='', ''-''}" by simp

definition [simp]: "le_frgt \<equiv> null |> eq_frgt_upd |> minus_frgt_upd"
definition [simp]: "le_crgt \<equiv> null |> eq_crgt_upd |> minus_crgt_upd"

definition [simp]: "le_arg_count \<equiv> (2 :: nat)"
definition [simp]: "le_name \<equiv> ''<=''"
definition [simp]: "le_args \<equiv> [''<=.args.x'', ''<=.args.y'']"
definition [simp]: "le_r \<equiv> ''<=.ret''"

definition "le_tcom \<equiv> to_imp_tc le_args le_crgt [] le_r [] le_hol_tcn"
definition "le_com \<equiv> tailcall_to_IMP le_tcom"

definition [simp]: "le_frgt_upd upd = upd(le_name := mk_frgt1 le_f le_T_f)"
definition [simp]: "le_crgt_upd upd = upd(le_name := mk_crgt1 le_args le_com le_r)"

lemma le_hol_tcn_correctness:
  assumes *: "length xs = le_arg_count"
  shows "(le_hol_tcn, le_frgt) \<turnstile> (le_hol_tcn, [], xs)\<Rightarrow>\<^bsup> le'_T_f xs \<^esup> le'_f xs"
  apply (rule bigstep_start[OF le_hol_tcn_def])
  apply exec_bigstep
  by (simp_all add: *)

lemma le_correctness':
  "terminates_with_res_time_order_IMP le_com le_r (le'_f o lookups le_args) (le'_T_f o lookups le_args)"
  unfolding le_com_def le_tcom_def
proof (rule compiler_correct')
  fix vs_arg :: "nat list"
  assume "length vs_arg = length le_args"
  then show "(le_hol_tcn, le_frgt) \<turnstile> (le_hol_tcn, [], vs_arg) \<Rightarrow>\<^bsup>le'_T_f vs_arg\<^esup>  le'_f vs_arg"
    using le_hol_tcn_correctness by simp
next
  show "relate_rgt le_frgt le_crgt (calls_names_set le_hol_tcn)"
    apply (rule relate_rgt_unfold) apply simp
    apply (repeat \<open>rule forall_i_insert\<close>)
    using eq_correctness_rgt minus_correctness_rgt by simp_all
  show "check_compile le_crgt le_args [] [] le_hol_tcn"
  proof (rule check_compileI)
    show "(length le_args, le_crgt) \<turnstile> le_hol_tcn"
      unfolding le_hol_tcn_def by check_arg_count
  qed auto
  show "HOL_TCN_Timing.invar le_hol_tcn" by simp
qed

(* now we replace the generated value and timing functions with the user's again *)
corollary le_correctness:
  "terminates_with_res_time_order_IMP le_com le_r (le_f o lookups le_args) (le_T_f o lookups le_args)"
proof (rule terminates_with_res_time_order_IMP_mono'[OF _ _ le_correctness'])
  show "le'_f o lookups le_args = le_f o lookups le_args"
    using le' by simp
next
  show "le'_T_f o lookups le_args \<le>\<^sub>c le_T_f o lookups le_args"
    apply (rule order_of_le)
    using T_le' by simp
qed

lemma le_correctness_rgt:
  assumes "frgt le_name = le_frgt_upd null le_name"
  assumes "crgt le_name = le_crgt_upd null le_name"
  shows "relate_rgt_f frgt crgt le_name"
proof-
  from assms have
    "frgt le_name = mk_frgt1 le_f le_T_f"
    "crgt le_name = mk_crgt1 le_args le_com le_r" by simp_all
  then show ?thesis unfolding relate_rgt_f_def using le_correctness by (metis split_pairs2)
qed

(* schematic_goal "le_tcom \<equiv> ?t"
  by (to_imp_tc_unfold def: le_tcom_def) *)


subsubsection \<open>Square-root (with auxiliary parameter)\<close>

declare not_le_imp_less[termination_simp]
lemma sq_lt0[simp]: "x\<^sup>2 > y \<Longrightarrow> x > 0" for x y :: nat by (cases x; simp)
lemma sq_Suc[simp]: "(Suc x)\<^sup>2 > x\<^sup>2" by (simp add: power2_eq_square)

lemma sqrt_aux_term_simp[termination_simp]: fixes z :: nat assumes "\<not> z\<^sup>2 \<le> n" shows "z - Suc 0 < z"
proof -
  from assms have "z > 0" using not_le_imp_less sq_lt0 by blast
  then show "z - Suc 0 < z" by linarith
qed

fun sqrt_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sqrt_aux z n = (if z\<^sup>2 \<le> n then z else sqrt_aux (z - 1) n)"
declare sqrt_aux.simps[simp del]

definition T_sqrt_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "T_sqrt_aux z n = z^2"
(* declare T_sqrt_aux.simps[simp del] *)

value "sqrt_aux 16 16"
value "sqrt_aux 4 16"
value "sqrt_aux 3 5"

lemma sqrt_aux_simps[simp]:
    "z\<^sup>2 \<le> n \<Longrightarrow> sqrt_aux z n = z"
    "z\<^sup>2 > n \<Longrightarrow> sqrt_aux z n = sqrt_aux (z - 1) n"
  using sqrt_aux.simps by simp_all
(* lemma T_sqrt_aux_simps[simp]:
    "z\<^sup>2 \<le> n \<Longrightarrow> T_sqrt_aux z n = T_square z"
    "z\<^sup>2 > n \<Longrightarrow> T_sqrt_aux z n = T_square z + T_sqrt_aux (z - 1) n + 1"
  apply (cases "z\<^sup>2 \<le> n") using T_sqrt_aux.simps apply auto done *)

lemma sqrt_aux_cases:
  fixes z n :: nat
  assumes "z\<^sup>2 \<le> n \<Longrightarrow> P"
  assumes "z\<^sup>2 > n \<Longrightarrow> P"
  shows "P"
  by (cases "z\<^sup>2 \<le> n"; simp add: assms)

lemma sqrt_aux_induct[case_names small base step]:
  fixes n k :: nat
  assumes "\<And>z n. z\<^sup>2 \<le> n \<Longrightarrow> P z n"
  assumes "\<And>z n. z\<^sup>2 > n \<Longrightarrow> (z - 1)\<^sup>2 \<le> n \<Longrightarrow> P z n"
  assumes "\<And>z n. z\<^sup>2 > n \<Longrightarrow> (z - 1)\<^sup>2 > n \<Longrightarrow> P (z - 1) n \<Longrightarrow> P z n"
  shows "P z n"
proof (induction rule: sqrt_aux.induct[unfolded not_le])
  case ih: (1 z n)
  then show ?case
  proof (cases rule: sqrt_aux_cases[of z n])
    assume "z\<^sup>2 \<le> n"
    with assms(1) show "P z n" by blast
  next
    assume *: "z\<^sup>2 > n"
    show "P z n"
    proof (cases rule: sqrt_aux_cases[of "z - 1" n])
      assume "(z - 1)\<^sup>2 \<le> n"
      with * show "P z n" using assms(2) by blast
    next
      assume "(z - 1)\<^sup>2 > n"
      with ih * show "P z n" using assms(3) by blast
    qed
  qed
qed

lemma sqrt_aux_upper: "(sqrt_aux z n)\<^sup>2 \<le> n"
  by (induction z n rule: sqrt_aux_induct) simp_all

lemma sqrt_aux_lower: assumes "z\<^sup>2 \<ge> n" shows "n < (sqrt_aux z n + 1)\<^sup>2"
  using assms by (induction z n rule: sqrt_aux_induct; auto)

lemma sqrt_aux_sq: "sqrt_aux (x\<^sup>2) (x\<^sup>2) = x"
proof (rule antisym)
  from sqrt_aux_upper have "(sqrt_aux (x\<^sup>2) (x\<^sup>2))\<^sup>2 \<le> x\<^sup>2" by blast
  then show "sqrt_aux (x\<^sup>2) (x\<^sup>2) \<le> x" by simp
next
  from sqrt_aux_lower have "x\<^sup>2 < (sqrt_aux (x\<^sup>2) (x\<^sup>2) + 1)\<^sup>2"
    using power2_nat_le_imp_le by simp
  then have "x < (sqrt_aux (x\<^sup>2) (x\<^sup>2) + 1)"
    using power_less_imp_less_base by blast
  then show "x \<le> sqrt_aux (x\<^sup>2) (x\<^sup>2)" by linarith
qed


lemmas sqrt_aux_eq = sqrt_aux.simps[
  unfolded case_nat_eq_if unbool_if_else,
  unfolded unbool_le,
  unfolded unbool_if_else_def
]

schematic_goal "PROP EMBED 0 (sqrt_aux (EMBED_ARG z 0) (EMBED_ARG n 1)) ?t ?z"
  supply EMBED_extra =
    EMBED_call2[where g = "(-)" and T_g = minus_T_f and gr = minus_name]
    EMBED_call1[where g = "square" and T_g = square_T_f and gr = square_name]
    EMBED_call2[where g = "le" and T_g = le_T_f and gr = le_name]
    EMBED_tail2[where f = sqrt_aux]
  by (embed f_def: sqrt_aux_eq embed_extra: EMBED_extra)

definition [simp]: "sqrt_aux_hol_tcn \<equiv>
  IF hCall ''<='' [hCall ''^2'' [hArg 0], hArg 1] \<noteq>0 THEN hArg 0
  ELSE hTAIL [hCall ''-'' [hArg 0, hNumber 1], hArg 1]"
fun T_sqrt_aux' where "T_sqrt_aux' z n =
  z + (if le (square z) n \<noteq> 0 then 0 else Suc (T_sqrt_aux' (z - 1) n))"
declare T_sqrt_aux'.simps[simp del]

lemma sqrt_aux'_T_f: "T_sqrt_aux' z n \<le> T_sqrt_aux z n + z"
unfolding T_sqrt_aux_def proof (induction z n rule: sqrt_aux_induct)
  case (small z n)
  then show ?case by (simp add: T_sqrt_aux'.simps)
next
  case (base z n)
  then show ?case by (simp add: T_sqrt_aux'.simps power2_eq_square le_square)
next
  case (step z n)
  have *: "z > 0" using step by simp
  have "T_sqrt_aux' z n = T_sqrt_aux' (z - 1) n + z + 1"
    apply (subst T_sqrt_aux'.simps) apply (simp add: not_le step) done
  also have "... \<le> (z - 1)\<^sup>2 + (z - 1) + z + 1" using step by linarith
  also have "... = (z - 1) * (z - 1) + z + z" by (simp add: * power2_eq_square)
  also have "... \<le> (z - 1) * z + z + z" by simp
  also have "... = z * z - z + z + z" by (simp add: algebra_simps)
  also have "... = z * z + z" by simp
  finally show ?case unfolding power2_eq_square .
qed

definition [simp]: "(sqrt_aux_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. sqrt_aux (xs ! 0) (xs ! 1))"
definition [simp]: "(sqrt_aux_T_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. T_sqrt_aux (xs ! 0) (xs ! 1))"
definition [simp]: "(sqrt_aux'_T_f :: nat list \<Rightarrow> nat) \<equiv> (\<lambda>xs. T_sqrt_aux' (xs ! 0) (xs ! 1))"

definition [simp]: "sqrt_aux_aux \<equiv> calls_names_set sqrt_aux_hol_tcn"
(* note: *) lemma "sqrt_aux_aux = {''<='', ''^2'', ''-''}" by simp

definition [simp]: "sqrt_aux_frgt \<equiv> null |> le_frgt_upd |> square_frgt_upd |> minus_frgt_upd"
definition [simp]: "sqrt_aux_crgt \<equiv> null |> le_crgt_upd |> square_crgt_upd |> minus_crgt_upd"

definition [simp]: "sqrt_aux_name \<equiv> ''sqrt''"
definition [simp]: "sqrt_aux_args \<equiv> [''sqrt.args.z'', ''sqrt.args.n'']"
definition [simp]: "sqrt_aux_r \<equiv> ''sqrt.ret''"

definition "sqrt_aux_tcom \<equiv> to_imp_tc sqrt_aux_args sqrt_aux_crgt [] sqrt_aux_r [] sqrt_aux_hol_tcn"
definition "sqrt_aux_com \<equiv> tailcall_to_IMP sqrt_aux_tcom"

definition [simp]: "sqrt_aux_frgt_upd upd = upd(sqrt_aux_name := mk_frgt1 sqrt_aux_f sqrt_aux_T_f)"
definition [simp]: "sqrt_aux_crgt_upd upd = upd(sqrt_aux_name := mk_crgt1 sqrt_aux_args sqrt_aux_com sqrt_aux_r)"

lemma sqrt_aux_hol_tcn_correctness:
  assumes rgt: "frgt = sqrt_aux_frgt on sqrt_aux_aux"
  assumes *: "length xs = length sqrt_aux_args"
  shows "(sqrt_aux_hol_tcn, frgt) \<turnstile> (sqrt_aux_hol_tcn, [], xs)\<Rightarrow>\<^bsup> sqrt_aux'_T_f xs \<^esup> sqrt_aux_f xs"
proof-
  have frgt:
      "frgt ''<='' = mk_frgt1 le_f le_T_f"
      "frgt ''^2'' = mk_frgt1 square_f square_T_f"
      "frgt ''-'' = mk_frgt1 minus_f minus_T_f"
    using eq_on_lookup[of frgt sqrt_aux_frgt, OF rgt] by auto

  show ?thesis
    using * proof (induction "xs ! 0" "xs ! 1" arbitrary: xs rule: sqrt_aux.induct)
    case ind_case: 1
    note len = \<open>length xs = _\<close> and ih = ind_case.hyps(1)
    show ?case
      apply (rule bigstep_start[OF sqrt_aux_hol_tcn_def])
      apply exec_bigstep
      (* apply the induction hypothesis *)
      prefer 15 apply (rule bigstep_apply_ih[OF _ _ ih])
                          apply (unfold sqrt_aux'_T_f_def) apply (subst T_sqrt_aux'.simps)
                          apply (simp add: frgt)
                          apply (unfold sqrt_aux_f_def) apply (subst sqrt_aux.simps)
                          apply (simp add: frgt)
      by (auto simp add: frgt len T_sqrt_aux'.simps)
  qed
qed

lemma sqrt_aux_correctness':
  "terminates_with_res_time_order_IMP sqrt_aux_com sqrt_aux_r (sqrt_aux_f o lookups sqrt_aux_args) (sqrt_aux'_T_f o lookups sqrt_aux_args)"
  unfolding sqrt_aux_com_def sqrt_aux_tcom_def
proof (rule compiler_correct')
  fix vs_arg :: "nat list"
  assume "length vs_arg = length sqrt_aux_args"
  then show "(sqrt_aux_hol_tcn, sqrt_aux_frgt) \<turnstile> (sqrt_aux_hol_tcn, [], vs_arg) \<Rightarrow>\<^bsup>sqrt_aux'_T_f vs_arg\<^esup>  sqrt_aux_f vs_arg"
    using sqrt_aux_hol_tcn_correctness by blast
next
  show "relate_rgt sqrt_aux_frgt sqrt_aux_crgt (calls_names_set sqrt_aux_hol_tcn)"
    apply (rule relate_rgt_unfold) apply simp
    apply (repeat \<open>rule forall_i_insert\<close>)
    using le_correctness_rgt square_correctness_rgt minus_correctness_rgt by simp_all
  show "check_compile sqrt_aux_crgt sqrt_aux_args [] [] sqrt_aux_hol_tcn"
  proof (rule check_compileI)
    show "(length sqrt_aux_args, sqrt_aux_crgt) \<turnstile> sqrt_aux_hol_tcn"
      unfolding sqrt_aux_hol_tcn_def by check_arg_count
  qed auto
  show "HOL_TCN_Timing.invar sqrt_aux_hol_tcn" by simp
qed

thm order_of_plus[OF order_of_refl]

lemma sqrt_aux_correctness:
  "terminates_with_res_time_order_IMP sqrt_aux_com sqrt_aux_r
    (sqrt_aux_f o lookups sqrt_aux_args) (sqrt_aux_T_f o lookups sqrt_aux_args)"
proof (rule terminates_with_res_time_order_IMP_mono'
        [OF refl order_of_trans[OF order_of_le order_of_plus[OF order_of_refl order_of_le]] sqrt_aux_correctness'])
  show "(sqrt_aux'_T_f o lookups sqrt_aux_args) s \<le> (sqrt_aux_T_f o lookups sqrt_aux_args) s + (lookups sqrt_aux_args s ! 0)" for s
    unfolding comp_def sqrt_aux_T_f_def using sqrt_aux'_T_f by simp
  show "map s sqrt_aux_args ! 0 \<le> (sqrt_aux_T_f o lookups sqrt_aux_args) s" for s
    unfolding comp_def sqrt_aux_T_f_def T_sqrt_aux_def power2_eq_square by simp
qed

thm sqrt_aux_correctness[simplified, unfolded comp_def T_sqrt_aux_def, simplified]

lemma sqrt_aux_correctness_rgt:
  assumes "frgt sqrt_aux_name = sqrt_aux_frgt_upd null sqrt_aux_name"
  assumes "crgt sqrt_aux_name = sqrt_aux_crgt_upd null sqrt_aux_name"
  shows "relate_rgt_f frgt crgt sqrt_aux_name"
proof-
  from assms have
    "frgt sqrt_aux_name = mk_frgt1 sqrt_aux_f sqrt_aux_T_f"
    "crgt sqrt_aux_name = mk_crgt1 sqrt_aux_args sqrt_aux_com sqrt_aux_r" by simp_all
  then show ?thesis unfolding relate_rgt_f_def using sqrt_aux_correctness by (metis split_pairs2)
qed

schematic_goal "sqrt_aux_tcom \<equiv> ?t"
  by (to_imp_tc_unfold def: sqrt_aux_tcom_def)




(* 
  sqrt_aux_tcom \<equiv> ''Call.x.0.1'' ::= A (V ''sqrt.args.z'');; ''^2.args.x'' ::= A (V ''Call.x.0.1'');;
  CALL square_com RETURN ''^2.ret'';; ''Call.x.0.0'' ::= A (V ''^2.ret'');; ''Call.x.1.0'' ::= A (V ''sqrt.args.n'');;
  (''<=.args.x'' ::= A (V ''Call.x.0.0'');; ''<=.args.y'' ::= A (V ''Call.x.1.0''));; CALL le_com RETURN ''<=.ret'';;
  ''If.x.0'' ::= A (V ''<=.ret'');;
  IF ''If.x.0''\<noteq>0 THEN ''sqrt.ret'' ::= A (V ''sqrt.args.z'')
  ELSE (''Call.x.0.0'' ::= A (V ''sqrt.args.z'');; ''Call.x.1.0'' ::= A (N (Suc 0));;
        (''-.args.x'' ::= A (V ''Call.x.0.0'');; ''-.args.y'' ::= A (V ''Call.x.1.0''));;
        CALL minus_com RETURN ''-.ret'';; ''TAIL.x.0.0'' ::= A (V ''-.ret'');; ''TAIL.x.1.0'' ::= A (V ''sqrt.args.n'');;
        (''sqrt.args.z'' ::= A (V ''TAIL.x.0.0'');; ''sqrt.args.n'' ::= A (V ''TAIL.x.1.0''));; tTAIL) 
 *)


(* 
cx01 = sqrt.z;; sq.x = cx01;; CALL sq RET sq.r;;
cx00 = sq.r;; cx10 = sqrt.n;; le.x = cx00;; le.y = cx10;; CALL le RET le.r;;
ifx = le.r;; IF ifx THEN sqrt.r = sqrt.z;;
ELSE
  cx00 = sqrt.z;; cx10 = 1;; sub.x = cx00;; sub.y = cx10;; CALL sub RET sub.r;;
  tx00 = sub.r;; tx10 = sqrt.n;; sqrt.z = tx00;; sqrt.n = tx10;; TAIL


sq.x = z;; CALL sq RET sq.ret;;
le.x = sq.ret;; le.y = n;; CALL le RET le.ret;;
IF le.ret THEN ret = z;;
ELSE
  sub.x = z;; sub.y = 1;; CALL sub RET sub.ret;;
  z = sub.r;; n = n;; TAIL


 *)
(* the rest is just some scratch stuff *)

(* todo: move close to hol-tcn trace semantics *)
lemma htrace_to_end_hArg':
  assumes "k = 0"
  assumes "T = []"
  assumes "v = (xs ! n)"
  assumes "n < length xs"
  shows "(f, frgt) \<turnstile> (hArg n, bs, xs) \<Rightarrow>\<^bsup>(k, T) :: HOL_TCN_Timing.trace\<^esup> v"
  using assms by blast

lemma htrace_to_end_hNumber':
  assumes "k = 0"
  assumes "T = []"
  assumes "v = n"
  shows "(f, frgt) \<turnstile> (hNumber n, bs, xs) \<Rightarrow>\<^bsup>(k, T) :: HOL_TCN_Timing.trace\<^esup> v"
  using assms by blast

lemma htrace_to_end_hIf':
  assumes "k1 = 0"
  assumes "k = (if v1 \<noteq> 0 then k2 else k3)"
  assumes "T = T1 @ (if v1 \<noteq> 0 then T2 else T3)"
  assumes "v = (if v1 \<noteq> 0 then v2 else v3)"
  assumes "(f, frgt) \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>(k1, T1) :: HOL_TCN_Timing.trace\<^esup> v1"
  assumes "v1 \<noteq> 0 \<Longrightarrow> (f, frgt) \<turnstile>(t2, bs, xs) \<Rightarrow>\<^bsup>(k2, T2) :: HOL_TCN_Timing.trace\<^esup> v2"
  assumes "v1 = 0 \<Longrightarrow> (f, frgt) \<turnstile>(t3, bs, xs) \<Rightarrow>\<^bsup>(k3, T3) :: HOL_TCN_Timing.trace\<^esup> v3"
  shows "(f, frgt) \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3, bs, xs) \<Rightarrow>\<^bsup>(k, T) :: HOL_TCN_Timing.trace\<^esup> v"
proof (cases "v1 = 0")
  case False
  show ?thesis
  proof (rule htrace_to_end.hIfTrue)
    show "(f, frgt) \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>(0, T1) :: HOL_TCN_Timing.trace\<^esup> v1" using assms(1,5) by blast
    show "(f, frgt) \<turnstile> (t2, bs, xs) \<Rightarrow>\<^bsup>(k, T2) :: HOL_TCN_Timing.trace\<^esup> v" using False assms(2,4,6) by presburger
  qed (simp_all add: False assms(1,3))
next
  case True
  show ?thesis
  proof (rule htrace_to_end.hIfFalse)
    show "(f, frgt) \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>(0, T1) :: HOL_TCN_Timing.trace\<^esup> v1" using assms(1,5) by blast
    show "(f, frgt) \<turnstile> (t3, bs, xs) \<Rightarrow>\<^bsup>(k, T3) :: HOL_TCN_Timing.trace\<^esup> v" using True assms(2,4,7) by presburger
  qed (simp_all add: True assms(3,6))
qed

lemma htrace_to_end_hLetBound':
  assumes "k = 0"
  assumes "T = []"
  assumes "v = (bs ! n)"
  assumes "n < length bs"
  shows "(f, frgt) \<turnstile> (hLetBound n, bs, xs) \<Rightarrow>\<^bsup>(k, T) :: HOL_TCN_Timing.trace\<^esup> v"
  using assms by blast

lemma hte_bigstep_start:
  assumes "t \<equiv> t_def"
  assumes "(t, frgt) \<turnstile> (t_def, bs, xs)\<Rightarrow>\<^bsup>(k, T) :: HOL_TCN_Timing.trace\<^esup> v"
  shows "(t, frgt) \<turnstile> (t, bs, xs)\<Rightarrow>\<^bsup>(k, T) :: HOL_TCN_Timing.trace\<^esup> v"
  using assms by simp

lemma hte_args_nil:
  shows "\<forall>i<length ([] :: thol list). (t, frgt) \<turnstile> ([] ! i, bs, xs) \<Rightarrow>\<^bsup>(0, [] ! i) :: HOL_TCN_Timing.trace\<^esup> [] ! i"
  by simp

lemma hte_args_cons:
  assumes "(t, frgt) \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>(0, T1) :: HOL_TCN_Timing.trace\<^esup> v1"
  assumes "\<forall>i<length ts. (t, frgt) \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup> (0, Ts ! i) :: HOL_TCN_Timing.trace\<^esup> vs ! i"
  shows "\<forall>i<length (t1 # ts). (t, frgt) \<turnstile> ((t1 # ts) ! i, bs, xs) \<Rightarrow>\<^bsup> (0, (T1 # Ts) ! i) :: HOL_TCN_Timing.trace\<^esup> (v1 # vs) ! i"
proof (rule, rule)
  fix i assume *: "i < length (t1 # ts)"
  consider (0) "i = 0" | (cons) "i > 0" by linarith
  then show "(t, frgt) \<turnstile> ((t1 # ts) ! i, bs, xs) \<Rightarrow>\<^bsup> (0, (T1 # Ts) ! i) :: HOL_TCN_Timing.trace\<^esup> (v1 # vs) ! i"
  proof cases
    case 0 with assms(1) show ?thesis by simp
  next
    case cons
    with * assms(2) have "(t, frgt) \<turnstile> (ts ! (i - 1), bs, xs) \<Rightarrow>\<^bsup> (0, Ts ! (i - 1)) :: HOL_TCN_Timing.trace\<^esup> vs ! (i - 1)" by simp
    with cons show ?thesis by simp
  qed
qed

method exec_hte_inference =
    rule
      htrace_to_end.hLet htrace_to_end_hIf'
      htrace_to_end_hLetBound' htrace_to_end_hArg' htrace_to_end_hNumber'
      htrace_to_end.hCall htrace_to_end.hTail

method exec_hte_arglist = rule hte_args_cons hte_args_nil

method exec_hte1_start uses hol_tcn_def =
  rule hte_bigstep_start[OF hol_tcn_def]

method exec_hte1 = repeat \<open>exec_hte_arglist\<close> | exec_hte_inference
method exec_hte_bigstep = repeat \<open>exec_hte1\<close>; (rule refl)?
(* ; (rule refl)? (* todo: align other method *) *)


(* lemma sqrt_aux_frgt:
    "sqrt_aux_frgt ''<='' = mk_frgt1 le_f le_T_f"
    "sqrt_aux_frgt ''^2'' = mk_frgt1 square_f square_T_f"
    "sqrt_aux_frgt ''-'' = mk_frgt1 minus_f minus_T_f"
  by auto *)



lemma hte_bigstep_simps_to_start:
  assumes "PROP SIMPS_TO k' k"
  assumes "PROP SIMPS_TO T' T"
  assumes "PROP SIMPS_TO v' v"
  assumes "(t, frgt) \<turnstile> (t, bs, xs)\<Rightarrow>\<^bsup>(k', T') :: HOL_TCN_Timing.trace\<^esup> v'"
  shows "(t, frgt) \<turnstile> (t, bs, xs)\<Rightarrow>\<^bsup>(k, T) :: HOL_TCN_Timing.trace\<^esup> v"
  using assms by (simp add: SIMPS_TO_eq)

lemma hte_bigstep_simps_to_step:
  assumes "PROP SIMPS_TO bs bs'"
  assumes "PROP SIMPS_TO xs xs'"
  assumes "(t, frgt) \<turnstile> (t, bs', xs')\<Rightarrow>\<^bsup>(k, T) :: HOL_TCN_Timing.trace\<^esup> v"
  shows "(t, frgt) \<turnstile> (t, bs, xs)\<Rightarrow>\<^bsup>(k, T) :: HOL_TCN_Timing.trace\<^esup> v"
  using assms by (simp add: SIMPS_TO_eq)

schematic_goal "(sqrt_aux_hol_tcn, sqrt_aux_frgt) \<turnstile> (sqrt_aux_hol_tcn, [], [3, 4]) \<Rightarrow>\<^bsup>(?k, ?T) :: HOL_TCN_Timing.trace \<^esup> ?v"
  apply (rule hte_bigstep_simps_to_start) prefer 4
     apply (exec_hte1_start hol_tcn_def: sqrt_aux_hol_tcn_def, exec_hte_bigstep)
                  apply simp_all[13]
     apply (rule hte_bigstep_simps_to_step)
       apply (simp_all?)[2]
       apply (rule SIMPS_TOI, rule SIMPS_TOI)
     apply (exec_hte1_start hol_tcn_def: sqrt_aux_hol_tcn_def, exec_hte_bigstep)
                  apply simp_all[13]
(*      apply (rule hte_bigstep_simps_to_step)
       apply (simp_all?)[2]
       apply (rule SIMPS_TOI, rule SIMPS_TOI)
     apply (exec_hte1_start hol_tcn_def: sqrt_aux_hol_tcn_def, exec_hte_bigstep)
                  apply simp_all[13] *)
     apply simp (* clear out the tail call *)
    apply (simp_all?)[3]
    apply (rule SIMPS_TOI, rule SIMPS_TOI, rule SIMPS_TOI)
  done

end
