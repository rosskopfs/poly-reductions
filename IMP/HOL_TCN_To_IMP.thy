theory HOL_TCN_To_IMP
  (* TODO: move file *)
  imports IMP_Tailcall_Traces HOL_TCN_Timing Fresh My_Utils
begin

unbundle no com_syntax and thol_syntax and tcom_syntax


(* command registries *)

type_synonym com_registry_entry = "vname list \<times> com \<times> vname"
(* function name \<Rightarrow> (argument registers' names \<times> IMP command \<times> return register's name *)
type_synonym com_registry = "fun_ref \<Rightarrow> com_registry_entry"
abbreviation "args_from_crgt (crgt :: com_registry) name \<equiv> fst (crgt name)"
abbreviation "com_from_crgt (crgt :: com_registry) name \<equiv> fst (snd (crgt name))"
abbreviation "ret_from_crgt (crgt :: com_registry) name \<equiv> snd (snd (crgt name))"


(* fresh *)

(* let us switch between definitions easily *)
abbreviation "fresh' \<equiv> Fresh.fresh"

(* TODO: this should go in Fresh (but then can't swap out fresh' anymore) *)
definition "make_nth_fresh stale name = fresh' stale o ((@) name) o string_of_nat" 
definition "make_n_fresh stale name = generate (make_nth_fresh stale name)"

lemma inj_make_nth_fresh[simp]: "inj (make_nth_fresh stale name)"
  by (simp add: inj_append2 inj_compose inj_fresh inj_string_of_nat make_nth_fresh_def)

lemma distinct_make_n_fresh[simp]: "distinct (make_n_fresh stale name n)"
  unfolding make_n_fresh_def generate_def using distinct_map inj_make_nth_fresh distinct_upt inj_on_subset by blast

lemma make_n_fresh_not_in_stale: "set (make_n_fresh stale name n) \<inter> set stale = {}"
  unfolding make_n_fresh_def make_nth_fresh_def generate_def using fresh_not_in_stale by auto

lemma make_n_fresh_length[simp]: "length (make_n_fresh stale name n) = n"
  unfolding make_n_fresh_def by simp

value "make_n_fresh [''f.args.2.0'', ''f.args.2.1'', ''f.args.3.0''] ''f.args.'' 5"

(*
lemma inj_inj_on: fixes A assumes "inj f" shows "inj_on f A" using assms inj_on_subset by auto
lemma none_equal_not_in: fixes A shows "(\<forall>y\<in>A. x \<noteq> y) \<longleftrightarrow> x \<notin> A" by blast
lemma some_equal_in: fixes A shows "(\<exists>y\<in>A. x = y) \<longleftrightarrow> x \<in> A" by blast
*)


(* command sequences *)

lemma tbig_step_t_tSeq_assoc:
  (* from Compile_HOL_Nat_To_IMP *)
  fixes t :: nat
  shows "C \<turnstile> (c1 ;; (c2 ;; c3), s) \<Rightarrow>\<^bsup>t\<^esup> s' \<longleftrightarrow> C \<turnstile> (c1 ;; c2 ;; c3, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  by auto

lemma ttrace_to_leaf_tSeq_assoc:
  shows "(c1 ;; (c2 ;; c3), s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l) \<longleftrightarrow> (c1 ;; c2 ;; c3, s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l)"
  by fastforce

(*
lemma tbig_step_t_tSeq_Skip_id1[simp]: "f \<turnstile> (tSKIP;; c, s) \<Rightarrow>\<^bsup>Suc z\<^esup> t \<longleftrightarrow> f \<turnstile> (c, s) \<Rightarrow>\<^bsup>z\<^esup> t"
  by fastforce

lemma tbig_step_t_tSeq_Skip_id2[simp]: "f \<turnstile> (c;; tSKIP, s) \<Rightarrow>\<^bsup>Suc z\<^esup> t \<longleftrightarrow> f \<turnstile> (c, s) \<Rightarrow>\<^bsup>z\<^esup> t"
  by fastforce
*)

(* sequencing commands *)

fun mk_seqs where
  "mk_seqs [] = tSKIP" |
  "mk_seqs (t0 # ts) = foldl tSeq t0 ts"

find_theorems "foldl ?f ?z (_ @ _)"

value "mk_seqs []"
value "mk_seqs [c1, c2, c3]"
value "mk_seqs (c1 # c2 # c3 # cs)"

lemma mk_seqs_append:
  assumes "cs1 \<noteq> []"
  shows "mk_seqs (cs1 @ cs2) = mk_seqs (mk_seqs cs1 # cs2)"
  using assms by (cases cs1, cases cs2) simp_all

lemma mk_seqs_snoc:
  assumes "cs \<noteq> []"
  shows "mk_seqs (cs @ [c]) = mk_seqs cs;; c"
  using assms by (cases cs) simp_all

(* disassembling command sequences *)

fun seqs where
  "seqs (c1 ;; c2) = seqs c1 @ seqs c2" |
  "seqs t = [t]"

value "seqs (''x'' ::= A (N 1);; IF ''x''\<noteq>0 THEN tSKIP ELSE tSKIP;; ''x'' ::= A (N 3))"

fun is_seq where
  "is_seq (_;; _) \<longleftrightarrow> True" |
  "is_seq _ \<longleftrightarrow> False"

lemmas is_seq_seqE[elim] = is_seq.elims(2)

lemma seqs_not_nil[simp]: "seqs c \<noteq> []" by (induction c) auto

lemma seqs_idem: "c \<in> set (seqs cs) \<Longrightarrow> seqs c = [c]"
  by (induction cs rule: seqs.induct) auto

lemma seqs_idem'[simp]: "concat_map seqs (seqs cs) = seqs cs"
  by (induction cs rule: seqs.induct) auto

lemma length_seqs_Seq_gt_one: "length (seqs (c1;; c2)) > 1"
proof-
  have "length (seqs c1) > 0" "length (seqs c2) > 0" using seqs_not_nil by simp_all
  then have "length (seqs c1) + length (seqs c2) > 1" by linarith
  then show "length (seqs (c1;; c2)) > 1" by simp
qed

lemma seqs_not_seq_singleton[simp]: "\<not> is_seq c \<Longrightarrow> seqs c = [c]" by (cases c) simp_all
lemma seqs_seq_not_singleton[simp]: "seqs (c1;; c2) \<noteq> [c]"
proof-
  have "length (seqs (c1;; c2)) \<noteq> length [c]" using length_seqs_Seq_gt_one[of c1 c2] by simp
  then show "seqs (c1;; c2) \<noteq> [c]" by metis
qed

lemma not_seq_singleton_iff: "\<not> is_seq c \<longleftrightarrow> (\<exists>c'. seqs c = [c'])"
  using seqs_seq_not_singleton by (cases c) simp_all

lemma seqs_singletonE[elim]:
  assumes "seqs c = [c']" shows "c = c'"
proof (cases "is_seq c")
  assume "is_seq c"
  with assms have False using not_seq_singleton_iff by metis
  then show ?thesis by blast
next
  assume "\<not> is_seq c"
  then show ?thesis using assms seqs_not_seq_singleton by simp
qed

(* seqs/mk_seqs interaction *)

abbreviation "linearize c \<equiv> mk_seqs (seqs c)"

lemma seqs_mk_seqs[simp]: "cs \<noteq> [] \<Longrightarrow> seqs (mk_seqs cs) = concat_map seqs cs"
proof-
  have *: "seqs (foldl tSeq c cs) = seqs c @ concat_map seqs cs" for c cs
    by (induction cs arbitrary: c) auto
  then show "cs \<noteq> [] \<Longrightarrow> seqs (mk_seqs cs) = concat_map seqs cs"
    by (cases cs) auto
qed

lemma linearize_idem[simp]: "linearize (linearize c) = linearize c" by simp

lemma linearize_eq_seqs_eq_iff[simp]: "linearize c = linearize c' \<longleftrightarrow> seqs c = seqs c'"
proof
  assume "linearize c = linearize c'"
  then show "seqs c = seqs c'"
    using seqs_idem' seqs_mk_seqs seqs_not_nil by metis
qed simp

(* seqs/mk_seqs and bigstep *)

lemma mk_seqs_append_bigstep:
  assumes "cs1 \<noteq> []" "cs2 \<noteq> []"
  fixes z :: nat
  shows "f \<turnstile> (mk_seqs (cs1 @ cs2),s) \<Rightarrow>\<^bsup>z\<^esup> t \<longleftrightarrow> f \<turnstile> (mk_seqs cs1;; mk_seqs cs2,s) \<Rightarrow>\<^bsup>z\<^esup> t"
  using assms(2,1) tbig_step_t_tSeq_assoc mk_seqs_append
  by (induction cs2 arbitrary: z t rule: rev_nonempty_induct) auto

lemma linearize_bigstep:
  fixes z :: nat
  shows "f \<turnstile> (c,s) \<Rightarrow>\<^bsup>z\<^esup> t \<longleftrightarrow> f \<turnstile> (linearize c,s) \<Rightarrow>\<^bsup>z\<^esup> t"
  using mk_seqs_append_bigstep by (induction c arbitrary: s z t) auto

lemma same_linearize_bigstep:
  fixes c c' :: tcom
  fixes z :: nat
  assumes "linearize c = linearize c'"
  shows "f \<turnstile> (c,s) \<Rightarrow>\<^bsup>z\<^esup> t \<longleftrightarrow> f \<turnstile> (c',s) \<Rightarrow>\<^bsup>z\<^esup> t"
  using assms linearize_bigstep by metis

theorem same_seqs_bigstep:
  fixes c c' :: tcom
  fixes z :: nat
  assumes "seqs c = seqs c'"
  shows "f \<turnstile> (c,s) \<Rightarrow>\<^bsup>z\<^esup> t \<longleftrightarrow> f \<turnstile> (c',s) \<Rightarrow>\<^bsup>z\<^esup> t"
  using assms linearize_bigstep by metis
  (* using assms same_linearize_bigstep linearize_eq_seqs_eq_iff by blast *)

(* seqs/mk_seqs and traces *)

lemma mk_seqs_append_trace_leaf:
  assumes "cs1 \<noteq> []" "cs2 \<noteq> []"
  shows "(mk_seqs (cs1 @ cs2),s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l) \<longleftrightarrow> (mk_seqs cs1;; mk_seqs cs2,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l)"
using assms(2) proof (induction cs2 arbitrary: k T t l rule: rev_nonempty_induct)
  case (single x)
  then show ?case using mk_seqs_append assms by simp
next
  case (snoc x xs)
  then show ?case using assms apply (simp add: mk_seqs_append ttrace_to_leaf_tSeq_assoc)
    using ttrace_to_leaf_tSeq_assoc
    by (smt (z3) tSeq_trace_leafE ttrace_to_leaf.tSeq)
(* TODO clean up... *)
qed

lemma linearize_trace_leaf:
  shows "(c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l) \<longleftrightarrow> (linearize c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l)"
  using mk_seqs_append_trace_leaf by (induction c arbitrary: s k T t l) auto

lemma same_linearize_trace_leaf:
  fixes c c' :: tcom
  assumes "linearize c = linearize c'"
  shows "(c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l) \<longleftrightarrow> (c',s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l)"
  using assms linearize_trace_leaf by metis

theorem same_seqs_trace_leaf:
  fixes c c' :: tcom
  assumes "seqs c = seqs c'"
  shows "(c,s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l) \<longleftrightarrow> (c',s) \<Rightarrow>\<^bsup>(k, T)\<^esup> (t, l)"
  using assms linearize_trace_leaf by metis

(* invariants and mk_seq *)

lemma rev_induct_list012 [case_names nil single snoc]:
  assumes nil: "P []"
    and single: "\<And>x. P [x]"
    and snoc: "\<And>zs y x. \<lbrakk> P zs; P (zs @ [y]) \<rbrakk> \<Longrightarrow> P ((zs @ [y]) @ [x])"
  shows "P xs"
proof (induction "rev xs" arbitrary: xs rule: induct_list012)
  case (3 x y zs)
  then have "P (rev zs)" "P (rev zs @ [y])" by simp_all
  with snoc have "P ((rev zs @ [y]) @ [x])" by blast
  then show "P xs" using \<open>x # y # zs = rev xs\<close>[symmetric] by simp
qed (auto simp add: nil single)

lemma invar_mk_seqs[simp]:
  assumes "\<forall>c \<in> set cs. \<not> IMP_Tailcall.tails c" "IMP_Tailcall.invar c"
  shows "IMP_Tailcall.invar (mk_seqs (cs @ [c]))"
  using assms mk_seqs_append by (induction cs rule: rev_induct_list012) (simp_all del: append_assoc)
lemma non_tails_mk_seqs[simp]:
  assumes "\<forall>c \<in> set cs. \<not> IMP_Tailcall.tails c"
  shows "\<not> IMP_Tailcall.tails (mk_seqs cs)"
  using assms mk_seqs_append by (induction cs rule: rev_induct_list012) (simp_all del: append_assoc)


(* compiler! *)

definition "call_registers crgt t =
  concat_map (\<lambda>g. args_from_crgt crgt g @ [ret_from_crgt crgt g]) (calls_names t)"

definition "stale_registers f_args crgt bs keep t = f_args @ bs @ keep @ call_registers crgt t"

lemma size_nth_lt[termination_simp]: assumes "i < length xs" shows "size (xs ! i) < size_list size xs"
  using id_take_nth_drop[OF assms] size_list_append[of size "take i xs" "xs ! i # drop (Suc i) xs"] by simp

fun to_imp_tc ::
    "vname list \<Rightarrow> com_registry
    \<Rightarrow> vname list \<Rightarrow> vname \<Rightarrow> vname list \<Rightarrow> thol
    \<Rightarrow> tcom" where
  (* f_args: list of argument registers' names
     crgt: see type def
     bs: names of bound variables
     r: return register name
     keep: variable names that must not be written to (let-def, call/recurse argument temporaries) *)
  "to_imp_tc f_args crgt bs r keep (hIf t1 t2 t3) =
    (let x_var = fresh' (stale_registers f_args crgt bs keep (hIf t1 t2 t3)) ''If.x'';
         c1 = to_imp_tc f_args crgt bs x_var keep t1;
         c2 = to_imp_tc f_args crgt bs r keep t2;
         c3 = to_imp_tc f_args crgt bs r keep t3
      in tSeq c1 (tIf x_var c2 c3))" |
  "to_imp_tc f_args crgt bs r keep (hLet t1 t2) =
    (let x_var = fresh' (stale_registers f_args crgt bs keep (hLet t1 t2)) ''Let.x'';
         c1 = to_imp_tc f_args crgt bs x_var keep t1;
         c2 = to_imp_tc f_args crgt (x_var # bs) r (x_var # keep) t2
      in tSeq c1 c2)" |
  "to_imp_tc f_args crgt bs r keep (hLetBound n) = tAssign r (A (V (bs ! n)))" |
  "to_imp_tc f_args crgt bs r keep (hArg n) = tAssign r (A (V (f_args ! n)))" |
  "to_imp_tc f_args crgt bs r keep (hNumber n) = tAssign r (A (N n))" |
  "to_imp_tc f_args crgt bs r keep (hCall g ts) =
    (let (g_args, c_g, g_ret) = crgt g;
         xs = make_n_fresh (stale_registers f_args crgt bs keep (hCall g ts)) ''Call.x.'' (length ts);
         cs1 = generate (\<lambda>i. to_imp_tc f_args crgt bs (xs ! i) (xs @ keep) (ts ! i)) (length ts);
         cs2 = generate (\<lambda>i. (g_args ! i) ::= A (V (xs ! i))) (length ts)
      in mk_seqs cs1;; mk_seqs cs2;; tCall c_g g_ret;; r ::= A (V g_ret))" |
  "to_imp_tc f_args crgt bs r keep (hTAIL ts) =
    (let xs = make_n_fresh (stale_registers f_args crgt bs keep (hTAIL ts)) ''TAIL.x.'' (length ts);
         cs1 = generate (\<lambda>i. to_imp_tc f_args crgt bs (xs ! i) (xs @ keep) (ts ! i)) (length ts);
         cs2 = generate (\<lambda>i. (f_args ! i) ::= A (V (xs ! i))) (length ts)
      in mk_seqs cs1;; mk_seqs cs2;; tTAIL)"

(* compile some examples *)

definition "h_let_1 = hLet (hNumber 7) (hLetBound 0)"
value "to_imp_tc [] null [] ''r'' [] h_let_1"

definition "h_call_1 = hCall ''g'' [hNumber 7, hNumber 5]"
value "to_imp_tc [] (null(''g'' := ([''g.x1'', ''g.x2''], Assign ''g.r'' (A (V ''g.x1'')), ''g.r''))) [] ''r'' [] h_call_1"

definition "com_plus = ([''plus.x'', ''plus.y''], Assign ''plus.ret'' (Plus (V ''plus.x'') (V ''plus.y'')), ''plus.ret'')"
definition "h_sum3 = hLet (hCall ''plus'' [hArg 0, hArg 1]) (hCall ''plus'' [hLetBound 0, hArg 2])"
value "to_imp_tc [''x'', ''y'', ''z''] (null(''plus'' := com_plus)) [] ''r'' [] h_sum3"


(* basic relatedness lemmas of to_imp_tc: tails, invar, and size *)

lemma to_imp_tails: "HOL_TCN_Timing.invar t \<Longrightarrow> HOL_TCN_Timing.tails t \<Longrightarrow> IMP_Tailcall.tails (to_imp_tc f_args crgt bs r keep t)"
  by (induction t arbitrary: bs r keep) (auto simp add: Let_def split_beta generate_def)

lemma to_imp_nontail: "\<not> HOL_TCN_Timing.tails t \<Longrightarrow> \<not> IMP_Tailcall.tails (to_imp_tc f_args crgt bs r keep t)"
  by (induction t arbitrary: bs r keep) (simp_all add: Let_def split_beta generate_def)

lemma to_imp_tails_iff:
  assumes "HOL_TCN_Timing.invar t"
  shows "HOL_TCN_Timing.tails t \<longleftrightarrow> IMP_Tailcall.tails (to_imp_tc f_args crgt bs r keep t)"
  using to_imp_tails to_imp_nontail assms by blast

lemma to_imp_invar: "HOL_TCN_Timing.invar t \<Longrightarrow> IMP_Tailcall.invar (to_imp_tc f_args crgt bs r keep t)"
  by (induction t arbitrary: bs r keep) (simp_all add: Let_def split_beta generate_def to_imp_nontail)

(* todo: move *)
(* predicate that checks whether it is possible for the function to return without looping forever *)
fun can_terminate :: "thol \<Rightarrow> bool" where
  "can_terminate (LET _ IN t2) \<longleftrightarrow> can_terminate t2" |
  "can_terminate (hLetBound _) = True" |
  "can_terminate (hArg _) = True" |
  "can_terminate (hNumber _) = True" |
  "can_terminate (IF _\<noteq>0 THEN t2 ELSE t3) \<longleftrightarrow> can_terminate t2 \<or> can_terminate t3" |
  "can_terminate (hCall _ ts) = True" |
  "can_terminate (hTAIL ts) = False"

lemma to_imp_r_in_vars:
  assumes "can_terminate t"
  shows "r \<in> set (vars (to_imp_tc f_args crgt bs r keep t))"
using assms proof (induction arbitrary: bs keep rule: can_terminate.induct)
  case hIf: (5 t1 t2 t3)
  then consider "can_terminate t2" | "can_terminate t3" by auto
  then show ?case using hIf by cases (simp_all add: Let_def)
qed (simp_all add: Let_def split_beta)


lemma num_commands_mk_seqs:
  assumes "cs \<noteq> []"
  shows "IMP_Tailcall.num_commands (mk_seqs cs) + 1 = length cs + sum_map IMP_Tailcall.num_commands cs"
using assms proof (induction cs rule: rev_induct_list012)
  case (snoc zs y x)
  have "mk_seqs ((zs @ [y]) @ [x]) = mk_seqs (zs @ [y]);; x" using mk_seqs_snoc by blast
  then show ?case using snoc.IH by simp
qed simp_all

(* technical lemma, formulated more generally *)
lemma sum_map_num_commands_arg_list:
  fixes g :: "tcom \<Rightarrow> nat"
  assumes "\<forall>i < length xs. g (f i) \<le> k * h (xs ! i)"
  shows "sum_map g (generate f (length xs)) \<le> k * sum_map h xs"
proof-
  from assms have *: "\<forall>i\<in>set [0..<length xs]. (g o f) i \<le> k * h (xs ! i)" by simp

  have "sum_map g (generate f (length xs)) = sum_list (generate (g o f) (length xs))"
    by (simp add: map_generate_comp)
  also have "... \<le> sum_list (generate (\<lambda>i. k * h (xs ! i)) (length xs))"
    unfolding generate_def using sum_map_mono[OF *] by blast
  also have "... = k * sum_list (generate (\<lambda>i. h (xs ! i)) (length xs))"
    unfolding generate_def using sum_list_const_mult by fast
  also have "... = k * sum_map h xs" by simp
  finally show ?thesis .
qed

lemma sum_map_num_commands_copy_list: "sum_map IMP_Tailcall.num_commands (generate (\<lambda>i. (x i) ::= y i) n) = n"
  unfolding generate_def by (induction n) auto

lemma to_imp_num_commands:
  "IMP_Tailcall.num_commands (to_imp_tc f_args crgt bs r keep t) \<le> 7 * HOL_TCN_Timing.num_commands t"
proof (induction t arbitrary: bs r keep)
  case (hLet t1 t2)
  have "IMP_Tailcall.num_commands (to_imp_tc f_args crgt bs r keep LET t1 IN t2)
    \<le> 7 * HOL_TCN_Timing.num_commands t1 + 7 * HOL_TCN_Timing.num_commands t2 + 1"
    unfolding to_imp_tc.simps Let_def using hLet.IH by (simp add: add_le_mono)
  also have "... \<le> 7 * HOL_TCN_Timing.num_commands (LET t1 IN t2)" by simp
  finally show ?case .
next
  case (hIf t1 t2 t3)
  let ?r1 = "fresh' (stale_registers f_args crgt bs keep (IF t1\<noteq>0 THEN t2 ELSE t3)) ''If.x''"
  have "IMP_Tailcall.num_commands (to_imp_tc f_args crgt bs r keep (IF t1\<noteq>0 THEN t2 ELSE t3))
    \<le> 7 * HOL_TCN_Timing.num_commands t1 + (7 * HOL_TCN_Timing.num_commands t2 + 7 * HOL_TCN_Timing.num_commands t3) + 2"
    unfolding to_imp_tc.simps Let_def using hIf.IH by (simp add: add_le_mono)
  also have "... \<le> 7 * HOL_TCN_Timing.num_commands (IF t1\<noteq>0 THEN t2 ELSE t3)" by simp
  finally show ?case .
next
  case (hCall gr ts)
  then show ?case
  proof (cases "ts = []")
    assume "ts = []"
    then have *: "generate f (length ts) = []" for f :: "nat \<Rightarrow> 'a" by simp
    show ?thesis unfolding to_imp_tc.simps Let_def split_beta * by simp
  next
    assume *: "ts \<noteq> []"

    let ?xs = "make_n_fresh (stale_registers f_args crgt bs keep (hCall gr ts)) ''Call.x.'' (length ts)"
    let ?cs1 = "generate (\<lambda>i. to_imp_tc f_args crgt bs (?xs ! i) (?xs @ keep) (ts ! i)) (length ts)"
    let ?cs2 = "generate (\<lambda>i. (args_from_crgt crgt gr ! i) ::= A (V (?xs ! i))) (length ts)"

    from num_commands_mk_seqs[where cs = ?cs1] sum_map_num_commands_arg_list[where xs = ts] hCall.IH have 1:
        "IMP_Tailcall.num_commands (mk_seqs ?cs1) + 1 \<le> length ts + 7 * sum_map HOL_TCN_Timing.num_commands ts"
      using * by simp

    from num_commands_mk_seqs sum_map_num_commands_copy_list have 2:
        "IMP_Tailcall.num_commands (mk_seqs ?cs2) + 1 = 2 * length ts"
      unfolding generate_def using * by simp

    from 1 2 show ?thesis unfolding to_imp_tc.simps Let_def split_beta by simp
  qed

next
  case (hTAIL ts)
  then show ?case
  proof (cases "ts = []")
    assume "ts = []"
    then have *: "generate f (length ts) = []" for f :: "nat \<Rightarrow> 'a" by simp
    show ?thesis unfolding to_imp_tc.simps Let_def split_beta * by simp
  next
    assume *: "ts \<noteq> []"

    let ?xs = "make_n_fresh (stale_registers f_args crgt bs keep (hTAIL ts)) ''TAIL.x.'' (length ts)"
    let ?cs1 = "generate (\<lambda>i. to_imp_tc f_args crgt bs (?xs ! i) (?xs @ keep) (ts ! i)) (length ts)"
    let ?cs2 = "generate (\<lambda>i. (f_args ! i) ::= A (V (?xs ! i))) (length ts)"

    from num_commands_mk_seqs[where cs = ?cs1] sum_map_num_commands_arg_list[where xs = ts] hTAIL.IH have 1:
        "IMP_Tailcall.num_commands (mk_seqs ?cs1) + 1 \<le> length ts + 7 * sum_map HOL_TCN_Timing.num_commands ts"
      using * by simp

    from num_commands_mk_seqs sum_map_num_commands_copy_list have 2:
        "IMP_Tailcall.num_commands (mk_seqs ?cs2) + 1 = 2 * length ts"
      unfolding generate_def using * by simp

    from 1 2 show ?thesis unfolding to_imp_tc.simps Let_def split_beta by simp
  qed

qed simp_all

end
