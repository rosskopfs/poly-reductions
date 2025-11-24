theory HOL_TCN_Timing
  imports Com My_Utils
    ML_Unification.Unify_Resolve_Tactics
begin

unbundle no com_syntax
declare [[syntax_ambiguity_warning=false]]

(* hol-tcn definition+semantics*)

type_synonym fun_ref = string

(* HOL-TCN *)
datatype
  thol = hLet thol thol
  | hLetBound nat
  | hArg nat
  | hNumber nat
  | hIf thol thol thol
  | hCall fun_ref "thol list"
  | hTAIL "thol list"
(* Idea: nat \<Rightarrow> thol for arguments instead of nat list. Then, in an (isabelle) context fix
   per-function a number of arguments. *)

open_bundle thol_syntax begin
notation hLet ("LET _ IN _") and
         hIf ("(IF _/\<noteq>0 THEN _/ ELSE _)"  [0, 0, 61] 61)
end


fun calls_names where
  "calls_names (LET t1 IN t2) = calls_names t1 @ calls_names t2" |
  "calls_names (hLetBound _) = []" |
  "calls_names (hArg _) = []" |
  "calls_names (hNumber _) = []" |
  "calls_names (IF t1\<noteq>0 THEN t2 ELSE t3) = calls_names t1 @ calls_names t2 @ calls_names t3" |
  "calls_names (hCall f ts) = f # concat (map calls_names ts)" |
  "calls_names (hTAIL ts) = concat (map calls_names ts)"

lemma calls_names_subset_let[simp]:
  shows "set (calls_names t1) \<subseteq> set (calls_names (LET t1 IN t2))"
    and "set (calls_names t2) \<subseteq> set (calls_names (LET t1 IN t2))"
  by simp_all

lemma calls_names_subset_if[simp]:
  shows "set (calls_names t1) \<subseteq> set (calls_names (IF t1\<noteq>0 THEN t2 ELSE t3))"
    "set (calls_names t2) \<subseteq> set (calls_names (IF t1\<noteq>0 THEN t2 ELSE t3))"
    "set (calls_names t3) \<subseteq> set (calls_names (IF t1\<noteq>0 THEN t2 ELSE t3))"
  by auto

lemma calls_names_subset_call[simp]:
  shows "f \<in> set (calls_names (hCall f ts))" 
    and "\<And>t. t \<in> set ts \<Longrightarrow> set (calls_names t) \<subseteq> set (calls_names (hCall f ts))"
  by auto

lemma calls_names_subset_tail[simp]:
    "\<And>t. t \<in> set ts \<Longrightarrow> set (calls_names t) \<subseteq> set (calls_names (hTAIL ts))"
  by auto


abbreviation "calls_names_set t \<equiv> set (calls_names t)"


type_synonym fun_registry_entry = "(nat list \<Rightarrow> nat) \<times> (nat list \<Rightarrow> nat)"

(* function name \<Rightarrow> (function \<times> timing function) *)
type_synonym fun_registry = "fun_ref \<Rightarrow> fun_registry_entry"

abbreviation "f_from_frgt (frgt :: fun_registry) name \<equiv> fst (frgt name)"
abbreviation "T_f_from_frgt (frgt :: fun_registry) name \<equiv> snd (frgt name)"

lemma split_from_frgt:
  "(f, T_f) = frgt fr \<longleftrightarrow> f_from_frgt frgt fr = f \<and> T_f_from_frgt frgt fr = T_f"
  using split_pairs .


inductive
  hbig_step_t :: "thol \<times> fun_registry \<Rightarrow> thol \<times> nat list \<times> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" ("_ \<turnstile> _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
  where
hLet: "\<lbrakk>env \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>z1\<^esup> v1; env \<turnstile> (t2,v1#bs,xs) \<Rightarrow>\<^bsup>z2\<^esup> v; z = z1+z2\<rbrakk>
       \<Longrightarrow> env \<turnstile> (LET t1 IN t2,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v" |
hLetBound: "n < length bs \<Longrightarrow> env \<turnstile> (hLetBound n,bs,xs) \<Rightarrow>\<^bsup>0\<^esup> bs!n" |
hArg: "n < length xs \<Longrightarrow> env \<turnstile> (hArg n,bs,xs) \<Rightarrow>\<^bsup>0\<^esup> xs!n" |
hNumber: "env \<turnstile> (hNumber n,bs,xs) \<Rightarrow>\<^bsup>0\<^esup> n" |
hIfTrue: "\<lbrakk>env \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>z1\<^esup> v1; v1 \<noteq> 0; env \<turnstile> (t2,bs,xs) \<Rightarrow>\<^bsup>z2\<^esup> v2; z = z1+z2\<rbrakk>
          \<Longrightarrow> env \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v2" |
hIfFalse: "\<lbrakk>env \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>z1\<^esup> v1; v1 = 0; env \<turnstile> (t3,bs,xs) \<Rightarrow>\<^bsup>z2\<^esup> v2; z = z1+z2\<rbrakk>
          \<Longrightarrow> env \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v2" |
hCall: "\<lbrakk>length zs = length ts; length vs = length ts;
          \<forall>i < length ts. (f,frgt) \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>zs ! i\<^esup> vs ! i;
          v' = f_from_frgt frgt gr vs; z' = sum_list zs + T_f_from_frgt frgt gr vs\<rbrakk>
          \<Longrightarrow> (f,frgt) \<turnstile> (hCall gr ts,bs,xs) \<Rightarrow>\<^bsup>z'\<^esup> v'" |
hTail: "\<lbrakk>length zs = length ts; length vs = length ts;
          \<forall>i < length ts. (f,frgt) \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>zs ! i\<^esup> vs ! i;
          (f,frgt) \<turnstile> (f,[],vs) \<Rightarrow>\<^bsup>z'\<^esup> v';
          z'' = sum_list zs + z' + 1\<rbrakk>
          \<Longrightarrow> (f,frgt) \<turnstile> (hTAIL ts,bs,xs) \<Rightarrow>\<^bsup>z''\<^esup> v'"

(* code_pred [show_modes] hbig_step_t . (* can't handle the universal quantifier? *) *)
declare hbig_step_t.intros[intro]
lemmas hbig_step_t_induct = hbig_step_t.induct[split_format(complete)]

inductive_cases hLet_case [elim!]: "env \<turnstile> (hLet t1 t2,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hLetBound_case [elim!]: "env \<turnstile> (hLetBound n,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hArg_case [elim!]: "env \<turnstile> (hArg n,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hNumber_case [elim!]: "env \<turnstile> (hNumber n,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hIf_case [elim!]: "env \<turnstile> (hIf t1 t2 t3,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hCall_case [elim!]: "(f,frgt) \<turnstile> (hCall g ts,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
inductive_cases hTAIL_case [elim!]: "(f,frgt) \<turnstile> (hTAIL ts,bs,xs) \<Rightarrow>\<^bsup>z\<^esup> v"
(* TODO: could use better names *)


lemma hbig_step_t_hLetBound':
  assumes "z = 0"
  assumes "v = (bs ! n)"
  assumes "n < length bs"
  shows "(f, frgt) \<turnstile> (hLetBound n, bs, xs) \<Rightarrow>\<^bsup>z :: nat\<^esup> v"
  using assms by blast

(* todo: move close to hol-tcn semantics *)
lemma hbig_step_t_hArg':
  assumes "z = 0"
  assumes "v = (xs ! n)"
  assumes "n < length xs"
  shows "(f, frgt) \<turnstile> (hArg n, bs, xs) \<Rightarrow>\<^bsup>z :: nat\<^esup> v"
  using assms by blast

lemma hbig_step_t_hNumber':
  assumes "z = 0"
  assumes "v = n"
  shows "(f, frgt) \<turnstile> (hNumber n, bs, xs) \<Rightarrow>\<^bsup>z :: nat\<^esup> v"
  using assms by blast

lemma hbig_step_t_hIf':
  assumes "(f, frgt) \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>x :: nat\<^esup> v1"
  assumes "v1 \<noteq> 0 \<Longrightarrow> (f, frgt) \<turnstile>(t2, bs, xs) \<Rightarrow>\<^bsup>y1 :: nat\<^esup> v"
  assumes "v1 = 0 \<Longrightarrow> (f, frgt) \<turnstile>(t3, bs, xs) \<Rightarrow>\<^bsup>y2 :: nat\<^esup> v"
  assumes "v1 \<noteq> 0 \<Longrightarrow> z = x + y1"
  assumes "v1 = 0 \<Longrightarrow> z = x + y2"
  shows "(f, frgt) \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3, bs, xs) \<Rightarrow>\<^bsup>z :: nat\<^esup> v"
proof (cases "v1 = 0")
  case False
  show ?thesis
  proof (rule hbig_step_t.hIfTrue)
    show "(f, frgt) \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>x\<^esup> v1" using assms(1) .
    show "(f, frgt) \<turnstile> (t2, bs, xs) \<Rightarrow>\<^bsup>y1\<^esup>  v" using False assms(2) by blast
  qed (simp_all add: False assms(4))
next
  case True
  show ?thesis
  proof (rule hbig_step_t.hIfFalse)
    show "(f, frgt) \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>x\<^esup> v1" using assms(1) .
    show "(f, frgt) \<turnstile> (t3, bs, xs) \<Rightarrow>\<^bsup>y2\<^esup>  v" using True assms(3) by blast
  qed (simp_all add: True assms(5))
qed



lemma determ:
  fixes t :: thol
  assumes "ctxt \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>z1\<^esup> v1"
  assumes "ctxt \<turnstile> (t,bs,xs) \<Rightarrow>\<^bsup>z2\<^esup> v2"
  shows "z1 = z2" "v1 = v2"
  oops (* TODO *)

fun num_commands :: "thol \<Rightarrow> nat" where
  "num_commands (LET t1 IN t2) = num_commands t1 + num_commands t2 + 1" |
  "num_commands (hLetBound _) = 1" |
  "num_commands (hArg n) = 1" |
  "num_commands (hNumber n) = 1" |
  "num_commands (IF t1\<noteq>0 THEN t2 ELSE t3) = num_commands t1 + num_commands t2 + num_commands t3 + 1" |
  "num_commands (hCall g ts) = sum_map num_commands ts + length ts + 1" |
  "num_commands (hTAIL ts) = sum_map num_commands ts + length ts + 1"

lemma num_commands_size: "num_commands t \<le> 3 * size t + 1"
proof (induction t)
  case (hCall g ts) then show ?case apply (induction ts) by fastforce+
  case (hTAIL ts) then show ?case apply (induction ts) by fastforce+
qed simp_all

fun tails where
  "tails (hTAIL _) \<longleftrightarrow> True" |
  "tails (hLet t1 t2) \<longleftrightarrow> tails t1 \<or> tails t2" |
  "tails (hIf t1 t2 t3) \<longleftrightarrow> tails t1 \<or> tails t2 \<or> tails t3" |
  "tails (hCall g ts) \<longleftrightarrow> (\<exists>t \<in> set ts. tails t)" |
  "tails _ = False"

fun invar where
  "invar (hLet t1 t2) \<longleftrightarrow> \<not> tails t1 \<and> invar t2" |
  "invar (hIf t1 t2 t3) \<longleftrightarrow> \<not> tails t1 \<and> invar t2 \<and> invar t3" |
  "invar (hCall g ts) = (\<forall>t \<in> set ts. \<not> tails t)" |
  "invar (hTAIL ts) = (\<forall>t \<in> set ts. \<not> tails t)" |
  "invar _ = True"

lemma no_tails_invar[simp]: "\<not> tails t \<Longrightarrow> invar t" by (induction t) auto

lemma invar_letD[dest]:
  assumes "invar LET t1 IN t2"
  shows "invar t1" "invar t2"
  using assms by simp_all

lemma invar_callD[dest]:
  assumes "invar (hCall gr ts)"
  assumes "i < length ts"
  shows "invar (ts ! i)"
  using assms by simp_all

lemma invar_tailD[dest]:
  assumes "invar (hTAIL ts)"
  assumes "i < length ts"
  shows "invar (ts ! i)"
  using assms by simp_all

(* traces *)

type_synonym call_trace = "(fun_ref \<times> nat list) list"  (* called function, arguments *)
type_synonym trace = "nat \<times> call_trace"  (* number of recursive calls \<times> call trace *)

definition "interp_trace_item frgt g vs_arg_g = T_f_from_frgt frgt g vs_arg_g"
definition "interp_trace frgt n T = n + sum_map (\<lambda>(g, vs_arg_g). interp_trace_item frgt g vs_arg_g) T"

lemma interp_trace_append[simp]:
  "interp_trace frgt (n1 + n2) (T1 @ T2) = interp_trace frgt n1 T1 + interp_trace frgt n2 T2"
  unfolding interp_trace_def by simp
lemma interp_trace_append_nt1[simp]:
  "interp_trace frgt n (T1 @ T2) = interp_trace frgt 0 T1 + interp_trace frgt n T2"
  unfolding interp_trace_def by simp
lemma interp_trace_concat_is_sum_map:
  "interp_trace frgt n (concat xss) = n + sum_map (interp_trace frgt 0) xss"
  unfolding interp_trace_def by (induction xss) auto

lemma interp_trace_nil[simp]:
  "interp_trace frgt n [] = n"
  unfolding interp_trace_def by simp

lemma interp_trace_n:
  "interp_trace frgt n T = interp_trace frgt 0 T + n"
  unfolding interp_trace_def by simp

lemma interp_trace_singleton[simp]: "interp_trace frgt n [(g, vs_arg_g)] = n + T_f_from_frgt frgt g vs_arg_g"
  unfolding interp_trace_def interp_trace_item_def by simp

lemmas interp_trace_singleton' = interp_trace_singleton[where n = 0, simplified add_0_left]

datatype leaf_state = Value nat | Tail "nat list"

inductive
  htrace_to_leaf :: "fun_registry \<Rightarrow> thol \<times> nat list \<times> nat list \<Rightarrow> call_trace \<Rightarrow> leaf_state \<Rightarrow> bool"  ("_ \<turnstile> _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
hLet:
  "\<lbrakk>frgt \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>T1\<^esup> Value v1; frgt \<turnstile> (t2,v1#bs,xs) \<Rightarrow>\<^bsup>T2\<^esup> l2; T = T1@T2\<rbrakk>
   \<Longrightarrow> frgt \<turnstile> (LET t1 IN t2,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> l2" |
hLetBound: "n < length bs \<Longrightarrow> frgt \<turnstile> (hLetBound n,bs,xs) \<Rightarrow>\<^bsup>[]\<^esup> Value (bs ! n)" |
hArg: "n < length xs \<Longrightarrow> frgt \<turnstile> (hArg n,bs,xs) \<Rightarrow>\<^bsup>[]\<^esup> Value (xs ! n)" |
hNumber: "frgt \<turnstile> (hNumber n,bs,xs) \<Rightarrow>\<^bsup>[]\<^esup> Value n" |
hIfTrue:
  "\<lbrakk>frgt \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>T1\<^esup> Value v1; v1 \<noteq> 0; frgt \<turnstile> (t2,bs,xs) \<Rightarrow>\<^bsup>T2\<^esup> l2; T = T1@T2\<rbrakk>
   \<Longrightarrow> frgt \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> l2" |
hIfFalse:
  "\<lbrakk>frgt \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>T1\<^esup> Value v1; v1 = 0; frgt \<turnstile> (t3,bs,xs) \<Rightarrow>\<^bsup>T3\<^esup> l3; T = T1@T3\<rbrakk>
   \<Longrightarrow> frgt \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> l3" |
hCall:
  "\<lbrakk>length vs = length ts; length Ts = length ts;
    \<forall>i < length ts. frgt \<turnstile> (ts ! i,bs,xs) \<Rightarrow>\<^bsup>Ts ! i\<^esup> Value (vs ! i);
    T = concat Ts @ [(gr,vs)]; v = f_from_frgt frgt gr vs\<rbrakk>
   \<Longrightarrow> frgt \<turnstile> (hCall gr ts,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> Value v" |
hTail:
  "\<lbrakk>length vs = length ts; length Ts = length ts;
    \<forall>i < length ts. frgt \<turnstile> (ts ! i,bs,xs) \<Rightarrow>\<^bsup>Ts ! i\<^esup> Value (vs ! i);
    T = concat Ts\<rbrakk>
   \<Longrightarrow> frgt \<turnstile> (hTAIL ts,bs,xs) \<Rightarrow>\<^bsup>T\<^esup> Tail vs"

declare htrace_to_leaf.intros[intro]
lemmas htrace_to_leaf_induct = htrace_to_leaf.induct[split_format(complete)]

inductive_cases hLet_trace_leafE [elim!]: "frgt \<turnstile> (LET t1 IN t2,bs,xs) \<Rightarrow>\<^bsup>T :: call_trace\<^esup> l"
inductive_cases hLetBound_trace_leafE [elim!]: "frgt \<turnstile> (hLetBound n,bs,xs) \<Rightarrow>\<^bsup>T :: call_trace\<^esup> l"
inductive_cases hArg_trace_leafE [elim!]: "frgt \<turnstile> (hArg n,bs,xs) \<Rightarrow>\<^bsup>T :: call_trace\<^esup> l"
inductive_cases hNumber_trace_leafE [elim!]: "frgt \<turnstile> (hNumber n,bs,xs) \<Rightarrow>\<^bsup>T :: call_trace\<^esup> l"
inductive_cases hIf_trace_leafE [elim!]: "frgt \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3,bs,xs) \<Rightarrow>\<^bsup>T :: call_trace\<^esup> l"
inductive_cases hCall_trace_leafE [elim!]: "frgt \<turnstile> (hCall g ts,bs,xs) \<Rightarrow>\<^bsup>T :: call_trace\<^esup> l"
inductive_cases hTAIL_trace_leafE [elim!]: "frgt \<turnstile> (hTAIL ts,bs,xs) \<Rightarrow>\<^bsup>T :: call_trace\<^esup> l"


(* relating traces to the semantics

For any t/bs/xs, there are two cases depending on whether t runs to Value or to Tail:

Case 1:
  |----- Value v|  (trace)
  |----------- v|  (sem.)

Case 2:
  |---- Tail xs'||----------- v|  (trace, sem.)
  |-------------------------- v|  (sem.)

In the direction trace \<longrightarrow> semantics:
- For case 1, we show: if there is a trace, there is a corresponding inference in the semantics.
- For case 2, we show: if there is a trace to Tail xs' and an inference in the semantics from f/[]/xs',
  there is a corresponding inference in the semantics for the "whole execution" from t/bs/xs.

In the direction semantics \<longrightarrow> trace:
We show: if there is a semantics, either:
- there exists a corresponding trace to a value (i.e. no tail call occurs), or
- there exists a trace to Tail xs', and from f/[]/xs' a semantics to a value.

TODO: update this comment. We do basically this, but instead of doing case 2 relative to
the bigstep semantics, we do it with the "full" traces.

*)


lemma nontail_trace_leaf_no_tail:
  fixes T :: call_trace
  assumes "\<not> tails t" "frgt \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>T\<^esup> l" shows "\<exists>v. l = Value v"
  using assms by (induction t arbitrary: bs xs T) auto

lemma trace_leaf_nontail_bigstep:
  fixes T :: call_trace
  assumes "frgt \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>T\<^esup> l" "l = Value v"
  shows "(f, frgt) \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>interp_trace frgt 0 T\<^esup> v"
using assms proof (induction arbitrary: v rule: htrace_to_leaf_induct)
  case (hLet frgt t1 bs xs T1 v1 t2 T2 l2 T)
  with interp_trace_append_nt1 show ?case by blast
next
  case (hIfTrue frgt t1 bs xs T1 v1 t2 T2 l2 T t3)
  with interp_trace_append_nt1 show ?case by blast
next
  case (hIfFalse frgt t1 bs xs T1 v1 t3 T3 l3 T t2)
  with interp_trace_append_nt1 show ?case by blast
next
  case (hCall vs ts Ts frgt bs xs T gr v)

  let ?zs = "map (interp_trace frgt 0) Ts"
  have len_zs: "length ?zs = length ts" using hCall by simp

  show ?case proof (rule hbig_step_t.hCall)
    show "\<forall>i<length ts. (f, frgt) \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>?zs ! i\<^esup>  vs ! i"
      using \<open>length Ts = length ts\<close> hCall.IH nth_map by simp
  next
    show "interp_trace frgt 0 T = sum_map (interp_trace frgt 0) Ts + T_f_from_frgt frgt gr vs"
      using \<open>T = concat Ts @ [(gr, vs)]\<close> interp_trace_concat_is_sum_map by simp
  next
    show "v = f_from_frgt frgt gr vs"
      using hCall by blast
  qed (auto simp add: hCall)
next
  case (hTail vs ts Ts frgt bs xs T)
  then show ?case by simp
qed auto

lemma bigstep_nontail_trace_leaf:
  fixes z :: nat and v :: nat
  assumes "(f, frgt) \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>z\<^esup> v" "\<not> tails t"
  shows "\<exists>T. interp_trace frgt 0 T = z \<and> frgt \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>T\<^esup> Value v"
using assms proof (induction rule: hbig_step_t_induct)
  case (hLet f frgt t1 bs xs z1 v1 t2 z2 v z)
  from hLet nontail_trace_leaf_no_tail obtain T1 where 1:
    "interp_trace frgt 0 T1 = z1" "frgt \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>T1\<^esup> Value v1" by fastforce
  from hLet obtain T2 where 2:
    "interp_trace frgt 0 T2 = z2" "frgt \<turnstile> (t2, v1 # bs, xs) \<Rightarrow>\<^bsup>T2\<^esup> Value v" by auto

  from \<open>z = z1 + z2\<close> 1 2 have "interp_trace frgt 0 (T1 @ T2) = z" by simp
  moreover from 1 2 have "frgt \<turnstile> (LET t1 IN t2, bs, xs) \<Rightarrow>\<^bsup>T1 @ T2\<^esup> Value v" by blast
  ultimately show ?case by blast
next
  case hLetBound
  then show ?case by force
next
  case hArg
  then show ?case by force
next
  case hNumber
  then show ?case by force
next
  case (hIfTrue f frgt t1 bs xs z1 v1 t2 z2 v2 z t3)
  from hIfTrue nontail_trace_leaf_no_tail obtain T1 where 1:
    "interp_trace frgt 0 T1 = z1" "frgt \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>T1\<^esup> Value v1" by fastforce
  from hIfTrue obtain T2 where 2:
    "interp_trace frgt 0 T2 = z2" "frgt \<turnstile> (t2, bs, xs) \<Rightarrow>\<^bsup>T2\<^esup> Value v2" by auto
  from \<open>z = z1 + z2\<close> 1 2 have "interp_trace frgt 0 (T1 @ T2) = z" by simp
  moreover from \<open>v1 \<noteq> 0\<close> 1 2 have "frgt \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3, bs, xs) \<Rightarrow>\<^bsup>T1 @ T2\<^esup> Value v2" by blast
  ultimately show ?case by blast
next
  case (hIfFalse f frgt t1 bs xs z1 v1 t3 z2 v2 z t2)
  from hIfFalse nontail_trace_leaf_no_tail obtain T1 where 1:
    "interp_trace frgt 0 T1 = z1" "frgt \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>T1\<^esup> Value v1" by fastforce
  from hIfFalse obtain T2 where 2:
    "interp_trace frgt 0 T2 = z2" "frgt \<turnstile> (t3, bs, xs) \<Rightarrow>\<^bsup>T2\<^esup> Value v2" by auto
  from \<open>z = z1 + z2\<close> 1 2 have "interp_trace frgt 0 (T1 @ T2) = z" by simp
  moreover from \<open>v1 = 0\<close> 1 2 have "frgt \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3, bs, xs) \<Rightarrow>\<^bsup>T1 @ T2\<^esup> Value v2" by blast
  ultimately show ?case by blast
next
  case (hCall zs ts vs f frgt bs xs v' gr z')
  let ?P = "\<lambda>i T. interp_trace frgt 0 T = zs ! i \<and> frgt \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>T\<^esup> Value (vs ! i)"
  let ?Ts = "map (\<lambda>i. SOME T. ?P i T) [0..<length ts]"
  let ?T = "concat ?Ts @ [(gr, vs)]"

  have P: "i<length ts \<Longrightarrow> \<exists>T. ?P i T" for i using hCall nontail_trace_leaf_no_tail by fastforce

  from P have *: "i<length ts \<Longrightarrow> interp_trace frgt 0 (SOME T. ?P i T) = zs ! i" for i
    using someI2_ex[where P = "?P i"] by fast
  have **: "length (map (interp_trace frgt 0) ?Ts) = length zs" using hCall by simp
  from * nth_equalityI[OF **] have "map (interp_trace frgt 0) ?Ts = zs" by simp
  then have "interp_trace frgt 0 ?T = z'"
    using interp_trace_concat_is_sum_map hCall by simp

  moreover have "frgt \<turnstile> (hCall gr ts, bs, xs) \<Rightarrow>\<^bsup>?T\<^esup> Value v'"
  proof (rule htrace_to_leaf.hCall)
    from P have "i<length ts \<Longrightarrow> frgt \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>SOME T. ?P i T\<^esup> Value (vs ! i)" for i
      using someI2_ex[where P = "?P i"] by fast
    then show "\<forall>i<length ts. frgt \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>?Ts ! i\<^esup> Value (vs ! i)" by simp
  qed (simp_all add: hCall)

  ultimately show ?case by blast
next
  case (hTail zs ts vs f frgt bs xs z' v' z'')
  then show ?case by simp
qed


inductive
  htrace_to_end :: "thol \<times> fun_registry \<Rightarrow> thol \<times> nat list \<times> nat list \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool"  ("_ \<turnstile> _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
hLet:
  "\<lbrakk>env \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>(0, T1)\<^esup> v1; env \<turnstile> (t2,v1#bs,xs) \<Rightarrow>\<^bsup>(k, T2)\<^esup> v2; T = T1@T2\<rbrakk>
   \<Longrightarrow> env \<turnstile> (LET t1 IN t2,bs,xs) \<Rightarrow>\<^bsup>(k, T)\<^esup> v2" |
hLetBound: "k < length bs \<Longrightarrow> env \<turnstile> (hLetBound k,bs,xs) \<Rightarrow>\<^bsup>(0, [])\<^esup> bs ! k" |
hArg: "k < length xs \<Longrightarrow> env \<turnstile> (hArg k,bs,xs) \<Rightarrow>\<^bsup>(0, [])\<^esup> xs ! k" |
hNumber: "env \<turnstile> (hNumber k,bs,xs) \<Rightarrow>\<^bsup>(0, [])\<^esup> k" |
hIfTrue:
  "\<lbrakk>env \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>(0, T1)\<^esup> v1; v1 \<noteq> 0; env \<turnstile> (t2,bs,xs) \<Rightarrow>\<^bsup>(k, T2)\<^esup> v2; T = T1@T2\<rbrakk>
   \<Longrightarrow> env \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3,bs,xs) \<Rightarrow>\<^bsup>(k, T)\<^esup> v2" |
hIfFalse:
  "\<lbrakk>env \<turnstile> (t1,bs,xs) \<Rightarrow>\<^bsup>(0, T1)\<^esup> v1; v1 = 0; env \<turnstile> (t3,bs,xs) \<Rightarrow>\<^bsup>(k, T3)\<^esup> v3; T = T1@T3\<rbrakk>
   \<Longrightarrow> env \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3,bs,xs) \<Rightarrow>\<^bsup>(k, T)\<^esup> v3" |
hCall:
  "\<lbrakk>length vs = length ts; length Ts = length ts;
    \<forall>i < length ts. (f,frgt) \<turnstile> (ts ! i,bs,xs) \<Rightarrow>\<^bsup>(0, Ts ! i)\<^esup> vs ! i;
    T = concat Ts @ [(gr,vs)]; v = f_from_frgt frgt gr vs\<rbrakk>
   \<Longrightarrow> (f,frgt) \<turnstile> (hCall gr ts,bs,xs) \<Rightarrow>\<^bsup>(0, T)\<^esup> v" |
hTail:
  "\<lbrakk>length vs = length ts; length Ts = length ts;
    \<forall>i < length ts. (f,frgt) \<turnstile> (ts ! i,bs,xs) \<Rightarrow>\<^bsup>(0, Ts ! i)\<^esup> vs ! i;
    (f,frgt) \<turnstile> (f,[],vs) \<Rightarrow>\<^bsup>(n', T')\<^esup> v';
    T = concat Ts @ T'; k = n' + 1\<rbrakk>
   \<Longrightarrow> (f,frgt) \<turnstile> (hTAIL ts,bs,xs) \<Rightarrow>\<^bsup>(k, T)\<^esup> v'"

declare htrace_to_end.intros[intro]
lemmas htrace_to_end_induct = htrace_to_end.induct[split_format(complete)]

inductive_cases hLet_trace_endE [elim!]: "env \<turnstile> (LET t1 IN t2,bs,xs) \<Rightarrow>\<^bsup>(k, T)\<^esup> v"
inductive_cases hLetBound_trace_endE [elim!]: "env \<turnstile> (hLetBound n,bs,xs) \<Rightarrow>\<^bsup>(k, T)\<^esup> v"
inductive_cases hArg_trace_endE [elim!]: "env \<turnstile> (hArg n,bs,xs) \<Rightarrow>\<^bsup>(k, T)\<^esup> v"
inductive_cases hNumber_trace_endE [elim!]: "env \<turnstile> (hNumber n,bs,xs) \<Rightarrow>\<^bsup>(k, T)\<^esup> v"
inductive_cases hIf_trace_endE [elim!]: "env \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3,bs,xs) \<Rightarrow>\<^bsup>(k, T)\<^esup> v"
inductive_cases hCall_trace_endE [elim!]: "(f,frgt) \<turnstile> (hCall g ts,bs,xs) \<Rightarrow>\<^bsup>(k, T)\<^esup> v"
inductive_cases hTAIL_trace_endE [elim!]: "(f,frgt) \<turnstile> (hTAIL ts,bs,xs) \<Rightarrow>\<^bsup>(k, T)\<^esup> v"

(* relating full traces and bigstep *)

lemma nontail_trace_end_no_tail:
  assumes "\<not> tails t" "(f, frgt) \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>(k, T)\<^esup> v" shows "k = 0"
  using assms by (induction t arbitrary: bs xs T) auto

lemma trace_end_bigstep:
  fixes T :: call_trace and v :: nat
  assumes "(f, frgt) \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>(k, T)\<^esup> v"
  shows "(f, frgt) \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>interp_trace frgt k T\<^esup> v"
using assms proof (induction rule: htrace_to_end_induct)
  case (hLet a b t1 bs xs T1 v1 t2 k T2 v2 T)
  with interp_trace_append_nt1 show ?case by blast
next
  case hLetBound
  then show ?case by fastforce
next
  case hArg
  then show ?case by fastforce
next
  case hNumber
  then show ?case by fastforce
next
  case hIfTrue
  with interp_trace_append_nt1 show ?case by blast
next
  case hIfFalse
  with interp_trace_append_nt1 show ?case by blast
next
  case (hCall vs ts Ts f frgt bs xs T gr v)

  let ?zs = "map (interp_trace frgt 0) Ts"
  have len_zs: "length ?zs = length ts" using hCall by simp

  show ?case proof (rule hbig_step_t.hCall)
    show "\<forall>i<length ts. (f, frgt) \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>?zs ! i\<^esup>  vs ! i"
      using \<open>length Ts = length ts\<close> hCall.IH nth_map by simp
  next
    show "interp_trace frgt 0 T = sum_map (interp_trace frgt 0) Ts + T_f_from_frgt frgt gr vs"
      using \<open>T = concat Ts @ [(gr, vs)]\<close> interp_trace_concat_is_sum_map by simp
  qed (simp_all add: hCall)
next
  case (hTail vs ts Ts f frgt bs xs k' T' v' T k)

  let ?zs = "map (interp_trace frgt 0) Ts"
  have len_zs: "length ?zs = length ts" using hTail by simp
    
  show ?case proof (rule hbig_step_t.hTail)
    show "\<forall>i<length ts. (f, frgt) \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>?zs ! i\<^esup>  vs ! i"
      using \<open>length Ts = length ts\<close> hTail.IH nth_map by simp
  next
    show "interp_trace frgt k T = sum_map (interp_trace frgt 0) Ts + interp_trace frgt k' T' + 1"
      apply (subst (2) interp_trace_n)
      apply (subst interp_trace_n)
      using \<open>T = concat Ts @ T'\<close> \<open>k = k' + 1\<close> interp_trace_concat_is_sum_map apply simp
      done
  qed (simp_all add: hTail)
qed

lemma bigstep_trace_end:
  fixes z :: nat and v :: nat
  assumes "(f, frgt) \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>z\<^esup> v"
  assumes "invar t" "invar f"
  shows "\<exists>k T. interp_trace frgt k T = z \<and> (f, frgt) \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>(k, T)\<^esup> v"
using assms proof (induction rule: hbig_step_t_induct)
  case (hLet f frgt t1 bs xs z1 v1 t2 z2 v z)
  from hLet nontail_trace_end_no_tail obtain T1 where 1:
    "interp_trace frgt 0 T1 = z1" "(f, frgt) \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>(0, T1)\<^esup> v1" by fastforce
  from hLet obtain k2 T2 where 2:
    "interp_trace frgt k2 T2 = z2" "(f, frgt) \<turnstile> (t2, v1 # bs, xs) \<Rightarrow>\<^bsup>(k2, T2)\<^esup> v" by auto

  from \<open>z = z1 + z2\<close> 1 2 have "interp_trace frgt k2 (T1 @ T2) = z" by simp
  moreover from 1 2 have "(f, frgt) \<turnstile> (LET t1 IN t2, bs, xs) \<Rightarrow>\<^bsup>(k2, T1 @ T2)\<^esup>  v" by blast
  ultimately show ?case by blast
next
  case hLetBound
  then show ?case by force
next
  case hArg
  then show ?case by force
next
  case hNumber
  then show ?case by force
next
  case (hIfTrue f frgt t1 bs xs z1 v1 t2 z2 v2 z t3)
  from hIfTrue nontail_trace_end_no_tail obtain T1 where 1:
    "interp_trace frgt 0 T1 = z1" "(f, frgt) \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>(0, T1)\<^esup>  v1" by fastforce
  from hIfTrue obtain k2 T2 where 2:
    "interp_trace frgt k2 T2 = z2" "(f, frgt) \<turnstile> (t2, bs, xs) \<Rightarrow>\<^bsup>(k2, T2)\<^esup>  v2" by auto
  from \<open>z = z1 + z2\<close> 1 2 have "interp_trace frgt k2 (T1 @ T2) = z" by simp
  moreover from \<open>v1 \<noteq> 0\<close> 1 2 have "(f, frgt) \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3, bs, xs) \<Rightarrow>\<^bsup>(k2, T1 @ T2)\<^esup>  v2" by blast
  ultimately show ?case by blast
next
  case (hIfFalse f frgt t1 bs xs z1 v1 t3 z2 v2 z t2)
  from hIfFalse nontail_trace_end_no_tail obtain T1 where 1:
    "interp_trace frgt 0 T1 = z1" "(f, frgt) \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>(0, T1)\<^esup>  v1" by fastforce
  from hIfFalse obtain k2 T2 where 2:
    "interp_trace frgt k2 T2 = z2" "(f, frgt) \<turnstile> (t3, bs, xs) \<Rightarrow>\<^bsup>(k2, T2)\<^esup>  v2" by auto
  from \<open>z = z1 + z2\<close> 1 2 have "interp_trace frgt k2 (T1 @ T2) = z" by simp
  moreover from \<open>v1 = 0\<close> 1 2 have "(f, frgt) \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3, bs, xs) \<Rightarrow>\<^bsup>(k2, T1 @ T2)\<^esup>  v2" by blast
  ultimately show ?case by blast
next
  case (hCall zs ts vs f frgt bs xs v' gr z')
  let ?P = "\<lambda>i T. interp_trace frgt 0 T = zs ! i \<and> (f, frgt) \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>(0, T)\<^esup>  vs ! i"
  let ?Ts = "map (\<lambda>i. SOME T. ?P i T) [0..<length ts]"
  let ?T = "concat ?Ts @ [(gr, vs)]"

  have P: "i<length ts \<Longrightarrow> \<exists>T. ?P i T" for i using hCall nontail_trace_end_no_tail by fastforce

  from P have *: "i<length ts \<Longrightarrow> interp_trace frgt 0 (SOME T. ?P i T) = zs ! i" for i
    using someI2_ex[where P = "?P i"] by fast
  have **: "length (map (interp_trace frgt 0) ?Ts) = length zs" using hCall by simp
  from * nth_equalityI[OF **] have "map (interp_trace frgt 0) ?Ts = zs" by simp
  then have "interp_trace frgt 0 ?T = z'"
    using interp_trace_concat_is_sum_map hCall by simp

  moreover have "(f, frgt) \<turnstile> (hCall gr ts, bs, xs) \<Rightarrow>\<^bsup>(0, ?T)\<^esup> v'"
  proof (rule htrace_to_end.hCall)
    from P have "i<length ts \<Longrightarrow> (f, frgt) \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>(0, SOME T. ?P i T)\<^esup>  vs ! i" for i
      using someI2_ex[where P = "?P i"] by fast
    then show "\<forall>i<length ts. (f, frgt) \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>(0, ?Ts ! i)\<^esup>  vs ! i" by simp
  qed (simp_all add: hCall)

  ultimately show ?case by blast
next
  case (hTail zs ts vs f frgt bs xs z' v' z'')
  then obtain k T where kT: "interp_trace frgt k T = z'" "(f, frgt) \<turnstile> (f, [], vs) \<Rightarrow>\<^bsup>(k, T)\<^esup>  v'" by auto

  let ?P = "\<lambda>i T. interp_trace frgt 0 T = zs ! i \<and> (f, frgt) \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>(0, T)\<^esup>  vs ! i"
  let ?Ts = "map (\<lambda>i. SOME T. ?P i T) [0..<length ts]"
  let ?T = "concat ?Ts @ T"

  have P: "i<length ts \<Longrightarrow> \<exists>T. ?P i T" for i using hTail nontail_trace_end_no_tail by fastforce

  from P have *: "i<length ts \<Longrightarrow> interp_trace frgt 0 (SOME T. ?P i T) = zs ! i" for i
    using someI2_ex[where P = "?P i"] by fast
  have **: "length (map (interp_trace frgt 0) ?Ts) = length zs" using hTail by simp
  from * nth_equalityI[OF **] have interp_Ts: "map (interp_trace frgt 0) ?Ts = zs" by simp

  have "interp_trace frgt (k + 1) ?T = interp_trace frgt 0 (concat ?Ts) + interp_trace frgt k T + 1"
    unfolding interp_trace_def by simp (* meh *)
  also have "... = sum_list zs + z' + 1" using interp_trace_concat_is_sum_map kT interp_Ts by simp
  also have "... = z''" using hTail by simp
  finally have "interp_trace frgt (k + 1) ?T = z''" .

  moreover have "(f, frgt) \<turnstile> (hTAIL ts, bs, xs) \<Rightarrow>\<^bsup>(k + 1, ?T)\<^esup> v'"
  proof (rule htrace_to_end.hTail)
    from P have "i<length ts \<Longrightarrow> (f, frgt) \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>(0, SOME T. ?P i T)\<^esup>  vs ! i" for i
      using someI2_ex[where P = "?P i"] by fast
    then show "\<forall>i<length ts. (f, frgt) \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>(0, ?Ts ! i)\<^esup>  vs ! i" by simp
  qed (simp_all add: hTail kT)

  ultimately show ?case by (metis (lifting))
qed

corollary bigstep_trace_end_v: True by blast


(* relating partial and full traces *)

lemma trace_leaf_no_tail_trace_end:
  fixes l :: leaf_state
  assumes "frgt \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>T\<^esup> l" "l = Value v"
  shows "(f, frgt) \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>(0, T)\<^esup> v"
  using assms by (induction arbitrary: v rule: htrace_to_leaf_induct) blast+

lemma trace_leaf_tail_trace_end:
  fixes l :: leaf_state
  assumes  "frgt \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>T1\<^esup> l" "l = Tail ts"
  assumes "(f, frgt) \<turnstile> (f, [], ts) \<Rightarrow>\<^bsup>(k, T2)\<^esup> v"
  shows "(f, frgt) \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>(k + 1, T1 @ T2)\<^esup> v"
using assms proof (induction (* arbitrary: ts *) rule: htrace_to_leaf_induct)
  case hLet
  with trace_leaf_no_tail_trace_end show ?case by fastforce
next
  case hIfTrue
  with trace_leaf_no_tail_trace_end show ?case by fastforce
next
  case hIfFalse
  with trace_leaf_no_tail_trace_end show ?case by fastforce
next
  case hTail
  with trace_leaf_no_tail_trace_end show ?case by blast
qed simp_all


lemma trace_end_nontail_trace_leaf:
  assumes "(f, frgt) \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>(k, T)\<^esup> v" "k = 0" (* "\<not> tails t" *)
  shows "frgt \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>T\<^esup> Value v"
using assms by (induction rule: htrace_to_end_induct) auto

lemma trace_end_trace_leaf:
  assumes "(f, frgt) \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>(k, T)\<^esup> v"
  assumes "invar t"
  shows "\<exists>T1 l.
    frgt \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>T1\<^esup> l
    \<and> (case l of Tail ts \<Rightarrow> (\<exists>T2. (f, frgt) \<turnstile> (f, [], ts) \<Rightarrow>\<^bsup>(k - 1, T2)\<^esup> v \<and> T = T1 @ T2)
               | Value v1 \<Rightarrow> k = 0 \<and> T1 = T \<and> v1 = v)"
using assms proof (induction arbitrary: rule: htrace_to_end_induct)
  case (hLet f frgt t1 bs xs T1 v1 t2 k T2 v2 T)
  from hLet trace_end_nontail_trace_leaf have 1: "frgt \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>T1\<^esup> Value v1" by simp
  from hLet obtain T2' l'
      where 2: "frgt \<turnstile> (t2, v1 # bs, xs) \<Rightarrow>\<^bsup>T2'\<^esup>  l'"
        and *: "(case l' of Tail ts \<Rightarrow> (\<exists>T3. (f, frgt) \<turnstile> (f, [], ts) \<Rightarrow>\<^bsup>(k - 1, T3)\<^esup>  v2 \<and> T2 = T2' @ T3)
                          | Value v1 \<Rightarrow> k = 0 \<and> T2' = T2 \<and> v1 = v2)"
    by auto
  from 1 2 have "frgt \<turnstile> (LET t1 IN t2, bs, xs) \<Rightarrow>\<^bsup>T1 @ T2'\<^esup> l'" by blast
  moreover from * have
      "(case l' of Tail ts \<Rightarrow> (\<exists>T3. (f, frgt) \<turnstile> (f, [], ts) \<Rightarrow>\<^bsup>(k - 1, T3)\<^esup>  v2 \<and> T = (T1 @ T2') @ T3)
                 | Value v1 \<Rightarrow> k = 0 \<and> T1 @ T2' = T \<and> v1 = v2)"
    using hLet by (cases l') simp_all

  ultimately show ?case by blast
next
  case hLetBound
  then show ?case by fastforce
next
  case hArg
  then show ?case by fastforce
next
  case hNumber
  then show ?case by fastforce
next
  case (hIfTrue f frgt t1 bs xs T1 v1 t2 k T2 v2 T t3)
  from hIfTrue trace_end_nontail_trace_leaf have 1: "frgt \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>T1\<^esup> Value v1" by simp
  from hIfTrue obtain T2' l'
      where 2: "frgt \<turnstile> (t2, bs, xs) \<Rightarrow>\<^bsup>T2'\<^esup>  l'"
        and *: "(case l' of Tail ts \<Rightarrow> (\<exists>T3. (f, frgt) \<turnstile> (f, [], ts) \<Rightarrow>\<^bsup>(k - 1, T3)\<^esup>  v2 \<and> T2 = T2' @ T3)
                          | Value v1 \<Rightarrow> k = 0 \<and> T2' = T2 \<and> v1 = v2)"
    by auto
  from 1 2 \<open>v1 \<noteq> 0\<close> have "frgt \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3, bs, xs) \<Rightarrow>\<^bsup>T1 @ T2'\<^esup> l'" by blast
  moreover from * have
      "(case l' of Tail ts \<Rightarrow> (\<exists>T3. (f, frgt) \<turnstile> (f, [], ts) \<Rightarrow>\<^bsup>(k - 1, T3)\<^esup>  v2 \<and> T = (T1 @ T2') @ T3)
                 | Value v1 \<Rightarrow> k = 0 \<and> T1 @ T2' = T \<and> v1 = v2)"
    using hIfTrue by (cases l') simp_all

  ultimately show ?case by blast
next
  (* TODO: shouldn't need a T4... better var names *)
  case (hIfFalse f frgt t1 bs xs T1 v1 t3 k T3 v3 T t2)
  from hIfFalse trace_end_nontail_trace_leaf have 1: "frgt \<turnstile> (t1, bs, xs) \<Rightarrow>\<^bsup>T1\<^esup> Value v1" by simp
  from hIfFalse obtain T2' l'
      where 2: "frgt \<turnstile> (t3, bs, xs) \<Rightarrow>\<^bsup>T2'\<^esup>  l'"
        and *: "(case l' of Tail ts \<Rightarrow> (\<exists>T4. (f, frgt) \<turnstile> (f, [], ts) \<Rightarrow>\<^bsup>(k - 1, T4)\<^esup> v3 \<and> T3 = T2' @ T4)
                          | Value v1 \<Rightarrow> k = 0 \<and> T2' = T3 \<and> v1 = v3)"
    by auto
  from 1 2 \<open>v1 = 0\<close> have "frgt \<turnstile> (IF t1\<noteq>0 THEN t2 ELSE t3, bs, xs) \<Rightarrow>\<^bsup>T1 @ T2'\<^esup> l'" by blast
  moreover from * have
      "(case l' of Tail ts \<Rightarrow> (\<exists>T4. (f, frgt) \<turnstile> (f, [], ts) \<Rightarrow>\<^bsup>(k - 1, T4)\<^esup>  v3 \<and> T = (T1 @ T2') @ T4)
                 | Value v1 \<Rightarrow> k = 0 \<and> T1 @ T2' = T \<and> v1 = v3)"
    using hIfFalse by (cases l') simp_all

  ultimately show ?case by blast
next
  case (hCall vs ts Ts f frgt bs xs T gr v)

  have "\<forall>i<length ts. frgt \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>Ts ! i\<^esup>  Value (vs ! i)"
      using hCall trace_end_nontail_trace_leaf by fastforce
  then have "frgt \<turnstile> (hCall gr ts, bs, xs) \<Rightarrow>\<^bsup>T\<^esup> Value v" using hCall by blast

  then show ?case using leaf_state.simps(5) by blast
next
  case (hTail vs ts Ts f frgt bs xs n' T' v' T k)

  have "\<forall>i<length ts. frgt \<turnstile> (ts ! i, bs, xs) \<Rightarrow>\<^bsup>Ts ! i\<^esup>  Value (vs ! i)"
    using hTail trace_end_nontail_trace_leaf by fastforce
  with hTail have "frgt \<turnstile> (hTAIL ts, bs, xs) \<Rightarrow>\<^bsup>concat Ts\<^esup> Tail vs" by blast

  moreover have "(f, frgt) \<turnstile> (f, [], vs) \<Rightarrow>\<^bsup>(k - 1, T')\<^esup>  v'" using hTail by simp

  ultimately show ?case using hTail.hyps(4) leaf_state.simps(6) by blast
qed

(* the other form is nicer to present in the thesis *)
lemma trace_end_trace_leaf_equiv:
  assumes "(f, frgt) \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>(k, T)\<^esup> v"
  assumes "invar t"
  shows
    "((frgt \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>T\<^esup> Value v \<and> k = 0) \<or>
      (\<exists>T1 vs T2. (frgt \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>T1\<^esup> Tail vs) \<and> ((f, frgt) \<turnstile> (f, [], vs) \<Rightarrow>\<^bsup>(k - 1, T2)\<^esup> v) \<and> T = T1 @ T2))
     =
     (\<exists>T1 l.
         (frgt \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>T1\<^esup> l) \<and>
         (case l of Tail ts \<Rightarrow> (\<exists>T2. ((f, frgt) \<turnstile> (f, [], ts) \<Rightarrow>\<^bsup>(k - 1, T2)\<^esup> v) \<and> T = T1 @ T2)
          | Value v1 \<Rightarrow> k = 0 \<and> T1 = T \<and> v1 = v))"
proof (rule, goal_cases)
  case 1
  then obtain T1 vs T2 where *:
    "((frgt \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>T\<^esup> Value v) \<and> k = 0) \<or>
     ((frgt \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>T1\<^esup> Tail vs) \<and> ((f, frgt) \<turnstile> (f, [], vs) \<Rightarrow>\<^bsup>(k - 1, T2)\<^esup> v) \<and> T = T1 @ T2)"
    by blast
  then consider
    "frgt \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>T\<^esup> Value v" "k = 0" |
    "frgt \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>T1\<^esup> Tail vs" "(f, frgt) \<turnstile> (f, [], vs) \<Rightarrow>\<^bsup>(k - 1, T2)\<^esup> v" "T = T1 @ T2" by blast
  then show ?case
  proof cases
    case 1
    show ?thesis
    proof (rule exI, rule exI, rule conjI)
      from 1(1) show "(frgt \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>T\<^esup> Value v)" .
    qed (simp add: 1(2))
  next
    case 2
    show ?thesis
    proof (rule exI, rule exI, rule conjI)
      from 2(1) show "frgt \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>T1\<^esup> Tail vs" .
    qed (auto simp add: 2(2-) simp del: One_nat_def)
  qed
next
  case 2
  then obtain T1 l where *:
    "frgt \<turnstile> (t, bs, xs) \<Rightarrow>\<^bsup>T1\<^esup> l"
    "(case l of Value v1 \<Rightarrow> k = 0 \<and> T1 = T \<and> v1 = v
      | Tail ts \<Rightarrow> \<exists>T2. (f, frgt) \<turnstile> (f, [], ts) \<Rightarrow>\<^bsup>(k - 1, T2)\<^esup>  v \<and> T = T1 @ T2)" by blast
  show ?case
  proof (cases l)
    case (Value v)
    with * show ?thesis by simp
  next
    case (Tail vs)
    with *(2) obtain T2 where "(f, frgt) \<turnstile> (f, [], vs) \<Rightarrow>\<^bsup>(k - 1, T2)\<^esup>  v \<and> T = T1 @ T2" by auto
    with Tail *(1) show ?thesis by blast
  qed
qed




end
