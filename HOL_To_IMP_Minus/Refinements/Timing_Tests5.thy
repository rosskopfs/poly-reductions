
theory Timing_Tests5
  imports HOL_To_IMP_Minus_Primitives HOL_To_IMP_Minus_Arithmetics
    "HOL-Eisbach.Eisbach"
    "/home/simon/TUM/UseRewriteToTargetSimp/Rewrite"
  \<comment> \<open>Duplicate the timing stuff, I do not want the default setup, in particular I want non zero costs for primitives\<close>
  keywords "define_time_fun" :: thy_decl
    and    "define_time_function" :: thy_goal
    and    "equations"
    and    "define_time_0" :: thy_decl
  (*
  "HOL-Data_Structures.Define_Time_Function" *)
begin

context HOL_To_IMP_Minus
begin

function test_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"test_nat 0 m = m" |
"test_nat (Suc n) m = test_nat m n"
  by pat_completeness auto
termination by size_change
declare test_nat.simps[simp del]
case_of_simps test_nat_eq[simplified Nitpick.case_nat_unfold] : test_nat.simps
thm test_nat_eq
compile_nat test_nat_eq basename test
HOL_To_IMP_Minus_imp_minus_correct test_nat
  by (cook mode = tailcall)

end

ML_file "~~/src/HOL/Data_Structures/Define_Time_0.ML"
ML_file "~~/src/HOL/Data_Structures/Define_Time_Function.ML"

(* That's it! I'm gettin' me mallet
  Upper bound for all the technical stuff like variable copying, pattern matching, ... that is not
  captured in the timing function
*)
fun tcom_size :: "tcom \<Rightarrow> nat" where
  "tcom_size  tSKIP = 1"
| "tcom_size (tAssign _ _) = 2"
| "tcom_size (tSeq l r) = 1 + tcom_size l + tcom_size r"
| "tcom_size (tIf _ l r) = 1 + tcom_size l + tcom_size r"
(* Should not be necessary, covered by timing function*)
| "tcom_size (tCall b _) = 1"
| "tcom_size tTAIL = 1"



named_theorems tbig_step_accum_b

context
  notes neq0_conv[iff del, symmetric, iff]
begin
lemma tbig_step_t_determ:
  "c' \<turnstile> (c,s)\<Rightarrow>\<^bsup> x \<^esup> t \<Longrightarrow> c' \<turnstile> (c,s) \<Rightarrow>\<^bsup> x' \<^esup> t' \<Longrightarrow> x= x' \<and> t = t'"
proof (induction c' c s x t arbitrary: x' t' rule: tbig_step_t_induct)
  case (tCall C s z t c r)
  then show ?case
    using bigstep_det by blast
next
  case (tTail c s z t)
  then show ?case
    by blast
qed fastforce+
end

definition "in_bound c' c b s s' \<equiv> (\<exists>t . c' \<turnstile> (c,s) \<Rightarrow>\<^bsup>t\<^esup> s' \<and> t \<le> b)"

named_theorems tbig_step_in_bound
named_theorems tbig_step_in_bound_Calls

(* Just lift the previous lemmas, here we still do exact costs *)
lemma tSkip_in_bound[tbig_step_in_bound]: "Suc 0 = b \<Longrightarrow> s' = s \<Longrightarrow> in_bound c tSKIP b s s'"
  by (auto simp add: in_bound_def)
lemma tAssign_in_bound[tbig_step_in_bound]: "Suc (Suc 0) = b \<Longrightarrow> s' = s(x := aval a s) \<Longrightarrow> in_bound c (tAssign x a) b s s'"
  by (auto simp add: in_bound_def)
lemma tSeq_in_bound[tbig_step_in_bound]:
  "b = b1 + b2 \<Longrightarrow> in_bound c c1 b1 s1 s2 \<Longrightarrow> in_bound c c2 b2 s2 s3 \<Longrightarrow> in_bound c (tSeq c1 c2) b s1 s3"
  by (auto simp add: in_bound_def)
lemma tIf_in_bound[tbig_step_in_bound]: "
  t = (if s b \<noteq> 0 then t1 else t2) \<Longrightarrow>
  bo = Suc (if s b \<noteq> 0 then b1 else b2) \<Longrightarrow>
  (s b \<noteq> 0 \<Longrightarrow> in_bound c c1 b1 s t1) \<Longrightarrow>
  (s b = 0 \<Longrightarrow> in_bound c c2 b2 s t2) \<Longrightarrow>
  in_bound c (tIf b c1 c2) bo s t"
  by (auto simp add: in_bound_def split: if_splits)
lemma tCall_in_bound[]: "(C, s) \<Rightarrow>\<^bsup>z\<^esup> t \<Longrightarrow> z \<le> b \<Longrightarrow> s' = s(r := t r) \<Longrightarrow> in_bound c (tCall C r) b s s'"
  by (auto simp add: in_bound_def)
lemma tTail_in_bound[tbig_step_in_bound]: "b=5+b' \<Longrightarrow> in_bound c c b' s t \<Longrightarrow> in_bound c tTAIL b s t"
  by (auto simp add: in_bound_def)

(* Apply the above rules syntax directed, discharge the conditions immediately by simplifier *)
method in_bound_prover = ((rule tbig_step_in_bound_Calls, simp?) | (rule tSeq_in_bound tSkip_in_bound, solves simp) | (rule tAssign_in_bound, solves simp, solves simp)
     | (rule tIf_in_bound, solves \<open>simp split: if_splits\<close>, solves \<open>simp split: if_splits\<close>) | (rule tTail_in_bound, solves simp))

lemma halts_in_tailcall_to_IMP_Minus:
  assumes "invar C" "C \<turnstile> (C, s) \<Rightarrow>\<^bsup>t\<^esup> s'" obtains t' s' where "((tailcall_to_IMP_Minus C, s) \<Rightarrow>\<^bsup>t'\<^esup> s')"
    "t+7 \<le> t'" "t' \<le> ((7+t) + 1) * (1 + size\<^sub>c (compile C))"
proof-
  from assms obtain s'c  where step: "((compile C, s) \<Rightarrow>'\<^bsup>7+t\<^esup> s'c)"
    using compile_sound by metis
  obtain s_alt where s_alt_s: "s_alt = s on set (vars (inline (compile C)))"
    by blast
  hence s_alt_s': "s = s_alt on set (vars ((compile C)))"
    by (metis eq_on_def eq_on_subset inline_def vars_inline_S)
  with step obtain  t' s'_alt where
      step_inline: "(inline (compile C), s_alt) \<Rightarrow>\<^bsup>t'\<^esup> s'_alt" and
      s'_alt_s': "s'_alt = s'c on set (vars ( (compile C)))" and
      lower: "7+t \<le> t'" and
      upper: "t' \<le> ((7+t) + 1) * (1 + size\<^sub>c (compile C))"
    using inline_sound by metis
  obtain s'' where
    s'': "(inline (compile C), s) \<Rightarrow>\<^bsup>t'\<^esup> s''"
    using Vars.noninterference[OF step_inline _ s_alt_s] by blast
  with that lower upper show ?thesis
    by (auto simp add: tailcall_to_IMP_Minus_eq)
qed

corollary halts_in_tailcall_to_IMP_Minus_nicer:
  assumes "invar C" "C \<turnstile> (C, s) \<Rightarrow>\<^bsup>t\<^esup> s'" obtains t' s' where "((tailcall_to_IMP_Minus C, s) \<Rightarrow>\<^bsup>t'\<^esup> s')"
    "t+7 \<le> t'" "t' \<le> 8*(1 + size\<^sub>c (compile C)) + (1 + size\<^sub>c (compile C))* t"
  using halts_in_tailcall_to_IMP_Minus assms that
  by (smt (verit) add.commute add_mult_distrib left_add_mult_distrib mult.commute numeral_plus_one semiring_norm(2) semiring_norm(8))

(* Used for state resulting from tailcall*)
lemma in_bound_triv_wit: "(\<exists>s' . in_bound c' c b s s') \<longleftrightarrow> in_bound c' c b s  (THE s' . in_bound c' c b s s')"
  by (smt (verit) tbig_step_t_determ in_bound_def theI)

(* ... *)
lemma triv_wit: "\<exists>x. P x \<longleftrightarrow> P (SOME x . P x)"
  by auto


(* Push the inequality to the end*)
(* Could probably alternatively also do \<le> in all the rules, but probably does not help anything*)
lemma in_bound_weaken_bound: "in_bound c' c b s s' \<Longrightarrow> b \<le> b' \<Longrightarrow> in_bound c' c b' s s'"
  by (auto simp add: in_bound_def)


(* I assume the timing functions are always nonzero. I think that is ensured if I define the basic ones
  by hand. As soon as you call a non zero function (including recursive calls) costs are at least one
*)

(* Locale capturing the proof obligations for the refinements*)
locale bound_locale =
  fixes f :: "state \<Rightarrow> nat"

  fixes f_time :: "state \<Rightarrow> nat"
  (* I dream of not needing these *)
  fixes off :: nat (* Should always be size of the program, to cover pattern matching, copying of parameters, etc.*)
  fixes scale :: nat (* For each tCall in c add the corresponding slack *)

  fixes c :: tcom
  fixes ret_var :: string

  assumes f_time_non_zero_everywhere: "\<And>s . f_time s > 0" (* Timing function always non zero, should make things easier *)
  assumes scale_non_zero: "scale > 0" (* Avoid throwing away timing_function *)

  (* From cooking *)
  assumes cooked: "\<And>s t s' . (tailcall_to_IMP_Minus c, s) \<Rightarrow>\<^bsup>t \<^esup> s' \<Longrightarrow> s' ret_var = f s"

  (* Hopefully ensured by compiler :) *)
  assumes invar: "invar c"

  (* Main Proof obligation *)
  assumes in_bound': "\<And>s . \<exists>s' . in_bound c c (off + scale * f_time s) s s'"
begin


lemma tailcall_to_IMP_Minus_bound: "\<exists>t s'  . ((tailcall_to_IMP_Minus c, s) \<Rightarrow>\<^bsup>t\<^esup> s')
  \<and> t \<le>  8*(1 + size\<^sub>c (compile c)) + (1 + size\<^sub>c (compile c)) * (off + scale * f_time s)"
  using halts_in_tailcall_to_IMP_Minus_nicer invar in_bound' in_bound_def
proof-
  obtain ot os' where ot_os:"c \<turnstile> (c, s) \<Rightarrow>\<^bsup>ot\<^esup> os'" "ot \<le> (off + scale * f_time s)"
    using in_bound' by (simp add: in_bound_def) metis
  from this(1) invar obtain t s'  where t_s': "((tailcall_to_IMP_Minus c, s) \<Rightarrow>\<^bsup>t\<^esup> s')"
    "ot + 7 \<le> t" "t \<le> 8*(1 + size\<^sub>c (compile c)) + (1 + size\<^sub>c (compile c)) * ot"
    using halts_in_tailcall_to_IMP_Minus_nicer by blast
  from t_s'(3) ot_os(2) have "t \<le> 8*(1 + size\<^sub>c (compile c)) + (1 + size\<^sub>c (compile c)) * (off + scale * f_time s)"
     by (meson add_mono_thms_linordered_semiring(2) dual_order.trans nat_mult_le_cancel_disj)
  with t_s'(1) show ?thesis
    by blast
qed

corollary tailcall_to_IMP_Minus_bound_nicer: "\<exists>t s' . ((tailcall_to_IMP_Minus c, s) \<Rightarrow>\<^bsup>t\<^esup> s')
  \<and> t \<le> (8*(1 + size\<^sub>c (compile c)) + off * (1 + size\<^sub>c (compile c))) + ((1 + size\<^sub>c (compile c)) * scale) * f_time s"
proof-
  obtain t s' where "((tailcall_to_IMP_Minus c, s) \<Rightarrow>\<^bsup>t\<^esup> s')"
    "t \<le>  8*(1 + size\<^sub>c (compile c)) + (1 + size\<^sub>c (compile c)) * (off + scale * f_time s)"
    using tailcall_to_IMP_Minus_bound by blast
  thus ?thesis
    by (smt (verit, best) add_mult_distrib2 group_cancel.add1 mult.assoc mult.commute)
qed

corollary tailcall_to_IMP_Minus_slack': "\<exists>off_slack scale_slack t s'  . ((tailcall_to_IMP_Minus c, s) \<Rightarrow>\<^bsup>t\<^esup> s') \<and>
  (t \<le> off_slack + scale_slack * f_time s)"
  using tailcall_to_IMP_Minus_bound_nicer by blast

corollary tailcall_to_IMP_Minus_halts: "\<down>(tailcall_to_IMP_Minus c, s)"
  using tailcall_to_IMP_Minus_bound by blast

(* Constants are independent of state. Somehow I fell like I could do this less "pointed" *)
corollary tailcall_to_IMP_Minus_slack_ind: "\<exists>off_slack scale_slack . \<forall>s . \<exists>t s'  . ((tailcall_to_IMP_Minus c, s) \<Rightarrow>\<^bsup>t\<^esup> s') \<and>
  (t \<le> off_slack + scale_slack * f_time s)"
  apply (rule exI[of _ "(8*(1 + size\<^sub>c (compile c)) + off * (1 + size\<^sub>c (compile c)))"])
  apply (rule exI[of _ "((1 + size\<^sub>c (compile c)) * scale)"])
  apply (rule allI)
  apply (rule tailcall_to_IMP_Minus_bound_nicer)
  done

(* I do not even need the exs outside *)
definition "tailcall_to_IMP_Minus_off = 8*(1 + size\<^sub>c (compile c)) + off * (1 + size\<^sub>c (compile c))"
definition "tailcall_to_IMP_Minus_scale = (1 + size\<^sub>c (compile c)) * scale"

definition "slack = tailcall_to_IMP_Minus_off + tailcall_to_IMP_Minus_scale"

lemma slack_non_zero: "slack > 0"
  using bound_locale_axioms bound_locale_def slack_def tailcall_to_IMP_Minus_scale_def by auto

corollary tailcall_to_IMP_Minus_slack_ind_conc:
  "\<exists>t s'  . ((tailcall_to_IMP_Minus c, s) \<Rightarrow>\<^bsup>t\<^esup> s') \<and> (t \<le> tailcall_to_IMP_Minus_off + tailcall_to_IMP_Minus_scale * f_time s)"
  using tailcall_to_IMP_Minus_bound_nicer tailcall_to_IMP_Minus_off_def tailcall_to_IMP_Minus_scale_def by presburger

(* The stuff other refs should use *)
theorem out[]: "in_bound c' (tCall (tailcall_to_IMP_Minus c) ret_var)
  (tailcall_to_IMP_Minus_off + tailcall_to_IMP_Minus_scale * f_time s)
  s (s(ret_var:= f s))"
  by (metis tCall cooked in_bound_def tailcall_to_IMP_Minus_slack_ind_conc)

lemma slack_ge: "tailcall_to_IMP_Minus_off + tailcall_to_IMP_Minus_scale * f_time s \<le> slack * f_time s"
  using f_time_non_zero_everywhere slack_non_zero apply (auto simp add: slack_def)
   apply (metis add.commute mono_nat_linear_lb mult.commute nat_mult_less_cancel_disj)+ (* LOL *)
  done
(* The stuff other refs should use *)
theorem out2[tbig_step_in_bound_Calls]: "in_bound c' (tCall (tailcall_to_IMP_Minus c) ret_var)
  (slack * f_time s)
  s (s(ret_var:= f s))"
  using slack_ge out in_bound_weaken_bound by blast

end

context HOL_To_IMP_Minus
begin

lemma tCall_accum: "(C,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> s' = (s(r:=t r)) \<Longrightarrow> c \<turnstile> (tCall C r,s) \<Rightarrow>\<^bsup>z \<^esup> s'"
  by auto

(* These are "built in", do by hand. Also do not give abstract bounds, as those can also arise from pattern matching... which has not
  effect on timing  *)
lemma tCall_sub_IMP[tbig_step_in_bound_Calls]: "in_bound c (tCall sub_IMP ''sub.ret'') 2 s (s(''sub.ret'' := sub_nat (s ''sub.args.x'') (s ''sub.args.y'')))"
  apply (unfold in_bound_def sub_IMP_def)
  apply (rule  exI)
  apply (rule conjI)
  apply (rule tCall_accum)
   apply (rule AssignI)
   apply (rule refl)
   apply simp
  apply simp
  done
lemma tCall_add_IMP[tbig_step_in_bound_Calls]: "in_bound c (tCall add_IMP ''add.ret'') 2 s (s(''add.ret'' := add_nat (s ''add.args.x'') (s ''add.args.y'')))"
  apply (unfold in_bound_def add_IMP_def)
  apply (rule  exI)
  apply (rule conjI)
  apply (rule tCall_accum)
   apply (rule AssignI)
   apply (rule refl)
   apply simp
  apply simp
  done

lemma tCall_eq_IMP[tbig_step_in_bound_Calls]: "in_bound c (tCall eq_IMP ''eq.ret'') 9
  s (s(''eq.ret'' := eq_nat (s ''eq.args.x'') (s ''eq.args.y'')))"
  apply (unfold in_bound_def eq_IMP_def)
  apply (rule  exI)
  apply (rule conjI)
  apply (rule tCall_accum)
  apply (intro AssignI big_step_t.Seq refl) (* ? *)
   apply (rule AssignI)
   apply (rule refl)
   apply (rule AssignI)
        apply (rule refl)
       apply (rule refl)
      apply (rule AssignI)
      apply (rule refl)+
    apply (rule IfI)
       apply (rule AssignI)
  apply (rule refl)
       apply (rule AssignI)
  apply (rule refl)
      apply (rule refl)+
  apply (auto simp add: nat_of_bool_def)
  done

lemma tCall_suc_IMP[tbig_step_in_bound_Calls]: "in_bound c (tCall suc_IMP ''suc.ret'') 2 s (s(''suc.ret'' := Suc (s ''suc.args.x'')))"
    apply (unfold in_bound_def suc_IMP_def)
  apply (rule  exI)
  apply (rule conjI)
  apply (rule tCall_accum)
   apply (rule AssignI)
   apply (rule refl)
  apply auto
  done



(* Let's go! *)
end


definition [simp]: "T_eq (x::'a) (y::'a) = 9"
definition [simp]: "T_eq_nat (x::nat) y = T_eq  x y"
definition [simp]: "T_sub_nat x y = 2"
definition [simp]: "T_minus = T_sub_nat"
definition [simp]: "T_add_nat x y = 2"
definition [simp]: "T_plus = T_add_nat"

(* Already the first test here: Timing function is zero! This should not be allowed probably, needs to be at least a nonzero const *)
(* define_time_fun HOL_To_IMP_Minus.id_nat equations HOL_To_IMP_Minus.id_nat_def[THEN meta_eq_to_obj_eq] *)

definition "T_id_nat x = 1"

context HOL_To_IMP_Minus
begin

(* Abuse, happening here *)
sublocale bound_id: bound_locale "\<lambda>s . id_nat (s ''id.args.x'')" "\<lambda>s . T_id_nat (s ''id.args.x'')" 2 1 id_IMP_tailcall "''id.ret''"
  apply standard
      apply (simp add: T_id_nat_def)
  apply simp
    apply (fact id_nat_IMP_Minus_imp_minus_correct)
   apply (simp add: id_IMP_tailcall_def)
  subgoal for s
    apply (rule exI)
    apply (subst (2) id_IMP_tailcall_def)
    apply (rule in_bound_weaken_bound)
     apply in_bound_prover+
    apply simp
    done
  done
thm bound_id.out

end

(* Problem: Needs timing functions for nat_of_bool, eq. nat_of_bool seems to be just an artifact, is compiled to id?

  HOL.eq will be compiled later, so define T_le_nat by hand
*)
definition "T_nat_of_bool n = T_id_nat n"
(* define_time_fun HOL_To_IMP_Minus.nat_of_bool equations HOL_To_IMP_Minus.nat_of_bool_def[THEN meta_eq_to_obj_eq] *)

(* definition [simp]: "T_le_nat x y = 1 + T_id_nat (HOL_To_IMP_Minus.eq_nat x y)" (* Fix, uses eq_nat, doesn't matter really *)
 *)
define_time_fun HOL_To_IMP_Minus.le_nat equations HOL_To_IMP_Minus.le_nat_def[THEN meta_eq_to_obj_eq]
definition [simp]: "T_less_eq = T_le_nat"

lemma "(\<And>n . f n > 0) \<Longrightarrow>
  (\<forall>n :: nat . \<exists>off scale . g n \<le> off + scale * (f :: nat \<Rightarrow> nat) n) \<longleftrightarrow> (\<forall>n :: nat . \<exists>scale . g n \<le>  scale * f n)"
  apply auto
  subgoal for n apply (induction n) apply auto
     apply (meson div_less_iff_less_mult less_Suc_eq less_imp_le_nat)+
    done
  subgoal for n apply (induction n) apply auto
    using le_add1 apply blast+
    done
  done

context HOL_To_IMP_Minus
begin

sublocale bound_le: bound_locale "\<lambda>s . le_nat (s ''le.args.x'') (s ''le.args.y'')"
  "\<lambda>s . T_le_nat (s ''le.args.x'') (s ''le.args.y'')"
  "tcom_size le_IMP_tailcall" "bound_id.slack"
  le_IMP_tailcall "''le.ret''"
  apply standard
      apply (simp )
  using bound_id.slack_non_zero apply simp
     apply (fact le_nat_IMP_Minus_imp_minus_correct)
   apply (simp add: le_IMP_tailcall_def)
  subgoal for s
    apply (rule exI)
    apply (subst (2) le_IMP_tailcall_def)
    apply (rule in_bound_weaken_bound)
     apply in_bound_prover+
    apply (subst le_IMP_tailcall_def)
    apply (simp add: sub_IMP_def add_IMP_def eq_IMP_def T_id_nat_def)
    done
  done
end

(* Will be ignored... Constant *)
definition "T_false_nat = (1::nat)"
definition "T_true_nat = (1::nat)"
context HOL_To_IMP_Minus
begin



sublocale bound_false: bound_locale "\<lambda>s . false_nat"
  "\<lambda>s . T_false_nat"
  "tcom_size false_IMP_tailcall" 1
  false_IMP_tailcall "''false.ret''"
  apply standard
      apply (simp add: T_false_nat_def)
  apply simp
     apply (fact false_nat_IMP_Minus_imp_minus_correct)
   apply (simp add: false_IMP_tailcall_def)
  subgoal for s
    apply (rule exI)
    apply (subst (2) false_IMP_tailcall_def)
    apply (rule in_bound_weaken_bound)
     apply in_bound_prover+
    apply (subst false_IMP_tailcall_def)
    apply (simp add: )
    done
  done

sublocale bound_true: bound_locale "\<lambda>s . true_nat"
  "\<lambda>s . T_true_nat"
  "tcom_size true_IMP_tailcall" 1
  true_IMP_tailcall "''true.ret''"
  apply standard
      apply (simp add: T_true_nat_def)
  apply simp
     apply (fact true_nat_IMP_Minus_imp_minus_correct)
   apply (simp add: true_IMP_tailcall_def)
  subgoal for s
    apply (rule exI)
    apply (subst (2) true_IMP_tailcall_def)
    apply (rule in_bound_weaken_bound)
     apply in_bound_prover+
    apply (subst true_IMP_tailcall_def)
    apply (simp add: )
    done
  done


end

(* Bullshit *)
define_time_fun HOL_To_IMP_Minus.not_nat equations HOL_To_IMP_Minus.not_nat_def[THEN meta_eq_to_obj_eq]
definition [simp]: "T_Not = (T_not_nat o HOL_To_IMP_Minus.nat_of_bool)"

context HOL_To_IMP_Minus
begin

sublocale bound_not: bound_locale "\<lambda>s . not_nat (s ''not.args.n'')"
  "\<lambda>s . T_not_nat (s ''not.args.n'')"
  "tcom_size not_IMP_tailcall" "bound_id.slack+bound_false.slack"
  not_IMP_tailcall "''not.ret''"
  apply standard apply (simp add: )
      using bound_id.slack_non_zero bound_false.slack_non_zero apply simp
     apply (fact not_nat_IMP_Minus_imp_minus_correct)
   apply (simp add: not_IMP_tailcall_def)
  subgoal for s
    apply (rule exI)
    apply (subst (2) not_IMP_tailcall_def)
    apply (rule in_bound_weaken_bound)
     apply in_bound_prover+
    apply (subst not_IMP_tailcall_def)
    apply (auto simp add: T_nat_of_bool_def T_false_nat_def T_id_nat_def ring_distribs) (* Make those simp? *) (* Better: How far do we unfold everything. I feel like one level should be enough*)

    done
  done
end

define_time_fun HOL_To_IMP_Minus.max_nat equations HOL_To_IMP_Minus.max_nat_def[THEN meta_eq_to_obj_eq]
define_time_fun HOL_To_IMP_Minus.min_nat equations HOL_To_IMP_Minus.min_nat_def[THEN meta_eq_to_obj_eq]

definition [simp]: "T_max = T_max_nat"
definition [simp]: "T_min = T_min_nat"

context HOL_To_IMP_Minus
begin

sublocale bound_max: bound_locale "\<lambda>s . max_nat (s ''max.args.x'') (s ''max.args.y'')"
  "\<lambda>s . T_max_nat (s ''max.args.x'') (s ''max.args.y'')"
  "tcom_size max_IMP_tailcall" "bound_not.slack"
  max_IMP_tailcall "''max.ret''"
  apply standard apply (simp add: )
      using bound_not.slack_non_zero apply simp
     apply (fact max_nat_IMP_Minus_imp_minus_correct)
   apply (simp add: max_IMP_tailcall_def)
  subgoal for s
    apply (rule exI)
    apply (subst (2) max_IMP_tailcall_def)
    apply (rule in_bound_weaken_bound)
     apply in_bound_prover+
    apply simp
    apply (subst max_IMP_tailcall_def)
    apply (simp add: sub_IMP_def add_IMP_def eq_IMP_def T_nat_of_bool_def T_false_nat_def T_id_nat_def) (* Make those simp? *)
      (* Better: How far do we unfold everything. I feel like one level should be enough <- Comes from the ones where I just gave concrete bounds, fix*)
    done
  done

sublocale bound_min: bound_locale "\<lambda>s . min_nat (s ''min.args.x'') (s ''min.args.y'')"
  "\<lambda>s . T_min_nat (s ''min.args.x'') (s ''min.args.y'')"
  "tcom_size min_IMP_tailcall" "bound_not.slack"
  min_IMP_tailcall "''min.ret''"
  apply standard apply (simp add: )
      using bound_not.slack_non_zero apply simp
     apply (fact min_nat_IMP_Minus_imp_minus_correct)
   apply (simp add: min_IMP_tailcall_def)
  subgoal for s
    apply (rule exI)
    apply (subst (2) min_IMP_tailcall_def)
    apply (rule in_bound_weaken_bound)
     apply in_bound_prover+
    apply simp
    apply (subst min_IMP_tailcall_def)
    apply (simp add: sub_IMP_def add_IMP_def eq_IMP_def T_nat_of_bool_def T_false_nat_def T_id_nat_def) (* Make those simp? *) (* Better: How far do we unfold everything. I feel like one level should be enough*)
    done
  done
end

define_time_fun HOL_To_IMP_Minus.and_nat equations HOL_To_IMP_Minus.and_nat_def[THEN meta_eq_to_obj_eq]
define_time_fun HOL_To_IMP_Minus.or_nat equations HOL_To_IMP_Minus.or_nat_def[THEN meta_eq_to_obj_eq]
definition [simp]: "T_conj x y = T_and_nat (HOL_To_IMP_Minus.nat_of_bool x) (HOL_To_IMP_Minus.nat_of_bool y)"
definition [simp]: "T_disj x y = T_or_nat (HOL_To_IMP_Minus.nat_of_bool x) (HOL_To_IMP_Minus.nat_of_bool y)"

context HOL_To_IMP_Minus
begin

sublocale bound_and: bound_locale "\<lambda>s . and_nat (s ''and.args.x'') (s ''and.args.y'')"
  "\<lambda>s . T_and_nat (s ''and.args.x'') (s ''and.args.y'')"
  "tcom_size and_IMP_tailcall" "2 * bound_min.slack + bound_true.slack"
  and_IMP_tailcall "''and.ret''"
  apply standard apply (simp add: )
      using bound_true.slack_non_zero apply simp
     apply (fact and_nat_IMP_Minus_imp_minus_correct)
   apply (simp add: and_IMP_tailcall_def)
  subgoal for s
    apply (rule exI)
    apply (subst (2) and_IMP_tailcall_def)
    apply (rule in_bound_weaken_bound)
     apply in_bound_prover+
    apply simp
    apply (subst and_IMP_tailcall_def)
    apply simp
    apply (simp add: sub_IMP_def add_IMP_def eq_IMP_def T_nat_of_bool_def T_false_nat_def T_true_nat_def T_id_nat_def) (* Make those simp? *) (* Better: How far do we unfold everything. I feel like one level should be enough*)
    done
  done

sublocale bound_or: bound_locale "\<lambda>s . or_nat (s ''or.args.x'') (s ''or.args.y'')"
  "\<lambda>s . T_or_nat (s ''or.args.x'') (s ''or.args.y'')"
  "tcom_size or_IMP_tailcall" "bound_max.slack + bound_min.slack + bound_true.slack"
  or_IMP_tailcall "''or.ret''"
  apply standard apply (simp add: )
      using bound_true.slack_non_zero apply simp
     apply (fact or_nat_IMP_Minus_imp_minus_correct)
   apply (simp add: or_IMP_tailcall_def)
  subgoal for s
    apply (rule exI)
    apply (subst (2) or_IMP_tailcall_def)
    apply (rule in_bound_weaken_bound)
     apply in_bound_prover+
    apply simp
    apply (subst or_IMP_tailcall_def)
    apply (simp add: sub_IMP_def add_IMP_def eq_IMP_def T_nat_of_bool_def T_true_nat_def T_false_nat_def T_id_nat_def) (* Make those simp? *) (* Better: How far do we unfold everything. I feel like one level should be enough*)
    done
  done

end

define_time_fun HOL_To_IMP_Minus.lt_nat equations HOL_To_IMP_Minus.lt_nat_def[THEN meta_eq_to_obj_eq]

context HOL_To_IMP_Minus
begin

sublocale bound_lt: bound_locale "\<lambda>s . lt_nat (s ''lt.args.x'') (s ''lt.args.y'')"
  "\<lambda>s . T_lt_nat (s ''lt.args.x'') (s ''lt.args.y'')"
  "tcom_size lt_IMP_tailcall" "bound_le.slack + bound_not.slack + bound_and.slack + bound_id.slack"
  lt_IMP_tailcall "''lt.ret''"
  apply standard apply (simp add: )
      using bound_not.slack_non_zero apply simp
     apply (fact lt_nat_IMP_Minus_imp_minus_correct)
   apply (simp add: lt_IMP_tailcall_def)
  subgoal for s
    apply (rule exI)
    apply (subst (2) lt_IMP_tailcall_def)
    apply (rule in_bound_weaken_bound)
     apply in_bound_prover+
    apply simp
    apply (subst lt_IMP_tailcall_def)
    apply (simp add: sub_IMP_def add_IMP_def eq_IMP_def T_nat_of_bool_def T_false_nat_def T_true_nat_def T_id_nat_def) (* Make those simp? *) (* Better: How far do we unfold everything. I feel like one level should be enough*)
    done
  done

end



define_time_fun HOL_To_IMP_Minus.mul_acc_nat
declare T_mul_acc_nat.simps[simp del]

case_of_simps T_mul_acc_nat_simp: T_mul_acc_nat.simps

lemma T_mul_acc_nat_non_zero_everywhere: "T_mul_acc_nat x y z > 0"
  by (induction x y z rule: T_mul_acc_nat.induct) (auto simp add: T_mul_acc_nat.simps)

context HOL_To_IMP_Minus
begin

sublocale bound_mul_acc: bound_locale "\<lambda>s . mul_acc_nat (s ''mul_acc.args.x1a'') (s ''mul_acc.args.x2a'')  (s ''mul_acc.args.x3ba'')"
  "\<lambda>s . T_mul_acc_nat (s ''mul_acc.args.x1a'') (s ''mul_acc.args.x2a'')  (s ''mul_acc.args.x3ba'')"
  "tcom_size mul_acc_IMP_tailcall" "9+2+2" (* eq + add + sub, make constants *)
  mul_acc_IMP_tailcall "''mul_acc.ret''"
  apply standard
      using T_mul_acc_nat_non_zero_everywhere apply (simp add: )
         apply simp
     apply (fact mul_acc_nat_IMP_Minus_imp_minus_correct)
   apply (simp add: mul_acc_IMP_tailcall_def)
      subgoal for s
        apply (induction "s ''mul_acc.args.x1a''" "s ''mul_acc.args.x2a''" "s ''mul_acc.args.x3ba''" arbitrary: s rule: mul_acc_nat.induct)
        subgoal
    apply (rule exI)
    apply (subst (2) mul_acc_IMP_tailcall_def)
    apply (rule in_bound_weaken_bound)
     apply in_bound_prover+

    apply simp
    apply (subst mul_acc_IMP_tailcall_def)
    apply (simp add: sub_IMP_def add_IMP_def eq_IMP_def T_nat_of_bool_def T_false_nat_def T_true_nat_def T_id_nat_def) (* Make those simp? *) (* Better: How far do we unfold everything. I feel like one level should be enough*)
          done
        subgoal premises p for x s apply (insert p(2)) apply (rule exI)
    apply (subst (2) mul_acc_IMP_tailcall_def)
    apply (rule in_bound_weaken_bound)
     apply in_bound_prover+

    apply (rule iffD1[OF in_bound_triv_wit, OF p(1)])
             apply (simp add: nat_of_bool_def) apply simp apply simp

          (* simps do not fire, needs case splitting *)
          apply (rewrite in "_\<le>\<hole>" T_mul_acc_nat_simp)
          apply (simp split: nat.splits)
          done
        done
      done

end

define_time_fun HOL_To_IMP_Minus.mul_nat
definition [simp]: "T_times = T_mul_nat"

lemma T_mul_nat_non_zero_everywhere: "T_mul_nat x y > 0"
  using T_mul_acc_nat_non_zero_everywhere by simp


context HOL_To_IMP_Minus
begin

sublocale bound_mul: bound_locale "\<lambda>s . mul_nat (s ''mul.args.x'') (s ''mul.args.y'')"
  "\<lambda>s . T_mul_nat (s ''mul.args.x'') (s ''mul.args.y'')"
  "tcom_size mul_IMP_tailcall" "bound_mul_acc.slack"
  mul_IMP_tailcall "''mul.ret''"
  apply standard
      using T_mul_nat_non_zero_everywhere apply (simp add: )
      using bound_mul_acc.slack_non_zero apply simp
     apply (fact mul_nat_IMP_Minus_imp_minus_correct)
   apply (simp add: mul_IMP_tailcall_def)
      subgoal for s
    apply (rule exI)
    apply (subst (2) mul_IMP_tailcall_def)
    apply (rule in_bound_weaken_bound)
     apply in_bound_prover+

          apply (rewrite in "_\<le>\<hole>" T_mul_nat.simps)
    apply (subst mul_IMP_tailcall_def)
        apply (simp split: nat.splits)
        done
      done
end

definition [simp]: "T_less = T_lt_nat"

define_time_fun HOL_To_IMP_Minus.div_acc_nat

lemma T_div_acc_nat_non_zero_everywhere: "T_div_acc_nat x y z > 0"
  by (induction x y z rule: T_div_acc_nat.induct) auto
declare T_div_acc_nat.simps[simp del]
define_time_fun HOL_To_IMP_Minus.div_nat

lemma T_div_nat_non_zero_everywhere: "T_div_nat x y > 0"
  using T_div_acc_nat_non_zero_everywhere by simp


context HOL_To_IMP_Minus
begin

sublocale bound_div_acc: bound_locale "\<lambda>s . div_acc_nat (s ''div_acc.args.x'') (s ''div_acc.args.y'') (s ''div_acc.args.z'')"
  "\<lambda>s . T_div_acc_nat (s ''div_acc.args.x'') (s ''div_acc.args.y'') (s ''div_acc.args.z'')"
  "tcom_size div_acc_IMP_tailcall" "9+2+2+bound_lt.slack" (* eq + add + sub, make constants *)
  div_acc_IMP_tailcall "''div_acc.ret''"
  apply standard
      using T_div_acc_nat_non_zero_everywhere apply (simp add: )
         apply simp
     apply (fact div_acc_nat_IMP_Minus_imp_minus_correct)
   apply (simp add: div_acc_IMP_tailcall_def)
      subgoal for s
        apply (induction "s ''div_acc.args.x''" "s ''div_acc.args.y''" "s ''div_acc.args.z''" arbitrary: s rule: div_acc_nat.induct)

        subgoal premises p for s' thm p  apply (rule exI)
    apply (subst (2) div_acc_IMP_tailcall_def)
    apply (rule in_bound_weaken_bound)
     apply in_bound_prover+
    apply (rule iffD1[OF in_bound_triv_wit, OF p(1)])
               apply (simp) apply simp apply simp apply simp apply simp
        (* Not really nice, I basically do all possible choices for the if (and seemingly even more*)
          apply (rewrite in "_ \<le> \<hole>" T_div_acc_nat.simps)
          apply (simp add: ring_distribs split: nat.splits)
          done
        done
      done


sublocale bound_div: bound_locale "\<lambda>s . div_nat (s ''div.args.x'') (s ''div.args.y'')"
  "\<lambda>s . T_div_nat (s ''div.args.x'') (s ''div.args.y'')"
  "tcom_size div_IMP_tailcall" "bound_div_acc.slack"
  div_IMP_tailcall "''div.ret''"
  apply standard
      using T_div_nat_non_zero_everywhere apply (simp add: )
      using bound_div_acc.slack_non_zero apply simp
     apply (fact div_nat_IMP_Minus_imp_minus_correct)
   apply (simp add: div_IMP_tailcall_def)
      subgoal for s
    apply (rule exI)
    apply (subst (2) div_IMP_tailcall_def)
    apply (rule in_bound_weaken_bound)
     apply in_bound_prover+

    apply simp
        apply (subst div_IMP_tailcall_def)
        apply simp
        done
      done
end

define_time_fun HOL_To_IMP_Minus.square_nat equations HOL_To_IMP_Minus.square_nat_def[THEN meta_eq_to_obj_eq]
context HOL_To_IMP_Minus
begin

sublocale bound_square: bound_locale "\<lambda>s . square_nat (s ''square.args.x'')"
  "\<lambda>s . T_square_nat (s ''square.args.x'') "
  "tcom_size square_IMP_tailcall" "bound_mul.slack"
  square_IMP_tailcall "''square.ret''"
  apply standard
      using T_mul_nat_non_zero_everywhere apply (simp add: )
      using bound_mul.slack_non_zero apply simp
     apply (fact square_nat_IMP_Minus_imp_minus_correct)
   apply (simp add: square_IMP_tailcall_def)
      subgoal for s
    apply (rule exI)
    apply (subst (2) square_IMP_tailcall_def)
    apply (rule in_bound_weaken_bound)
     apply in_bound_prover+

    apply simp
        apply (subst square_IMP_tailcall_def)
        apply simp
        done
      done
end

definition [simp]: "T_divide = T_div_nat"
(*Timing function of Num.numeral_class.numeral is not defined, just goes to zero as the compiler drops it *)
definition [simp]: "T_numeral x = (0::nat)"
define_time_function HOL_To_IMP_Minus.sqrt_aux_nat
termination by (relation "Wellfounded.measure (\<lambda>(_, L, R). R - L)") auto
declare T_sqrt_aux_nat.simps[simp del]

lemma T_sqrt_aux_nat_non_zero_everywhere: "T_sqrt_aux_nat x y z > 0"
  by (induction x y z rule: T_sqrt_aux_nat.induct) (auto simp add: T_sqrt_aux_nat.simps)

define_time_fun HOL_To_IMP_Minus.sqrt_nat

lemma T_sqrt_nat_non_zero_everywhere: "T_sqrt_nat x > 0"
  using T_sqrt_aux_nat_non_zero_everywhere by simp

context HOL_To_IMP_Minus
begin

find_theorems name: Timing name: ".simps" name: T_
(* Atomic slack, also better output*)
lemma bound_locale_slack_no_descend_cong[cong]: "bound_locale.slack x y z = bound_locale.slack x y z"
  by (rule refl)

thm sqrt_aux_IMP_tailcall_def

sublocale bound_sqrt_aux: bound_locale "\<lambda>s . sqrt_aux_nat (s ''sqrt_aux.args.x'') (s ''sqrt_aux.args.L'') (s ''sqrt_aux.args.R'')"
  "\<lambda>s . T_sqrt_aux_nat (s ''sqrt_aux.args.x'') (s ''sqrt_aux.args.L'') (s ''sqrt_aux.args.R'')"
  "tcom_size (sqrt_aux_IMP_tailcall)" "2+2+2+bound_lt.slack + bound_le.slack + bound_div.slack + bound_square.slack"
  sqrt_aux_IMP_tailcall "''sqrt_aux.ret''"
  apply standard
      using T_sqrt_aux_nat_non_zero_everywhere apply (simp add: )
         apply simp
     apply (fact sqrt_aux_nat_IMP_Minus_imp_minus_correct)
   apply (simp add: sqrt_aux_IMP_tailcall_def)
      subgoal for s
        apply (induction "s ''sqrt_aux.args.x''" "s ''sqrt_aux.args.L''" "s ''sqrt_aux.args.R''" arbitrary: s rule: sqrt_aux_nat.induct)

        subgoal premises p for s' thm p  apply (rule exI)
    apply (subst (2) sqrt_aux_IMP_tailcall_def)
    apply (rule in_bound_weaken_bound)
     apply in_bound_prover+
    apply (rule iffD1[OF in_bound_triv_wit, OF p(1)])
               apply (simp) apply simp apply simp apply simp apply simp
     apply in_bound_prover+
    apply (rule iffD1[OF in_bound_triv_wit, OF p(2)])
               apply (simp) apply simp apply simp apply simp apply simp
     apply in_bound_prover+
          apply (rewrite in "_ \<le> \<hole>" T_sqrt_aux_nat.simps)
          apply (simp add: Let_def ring_distribs split: nat.splits)
          done
          done
        done

sublocale bound_sqrt: bound_locale "\<lambda>s . sqrt_nat (s ''sqrt.args.x'')"
  "\<lambda>s . T_sqrt_nat (s ''sqrt.args.x'')"
  "tcom_size sqrt_IMP_tailcall" "2+bound_sqrt_aux.slack"
  sqrt_IMP_tailcall "''sqrt.ret''"
  apply standard
      using T_sqrt_nat_non_zero_everywhere apply (simp add: )
      using bound_sqrt_aux.slack_non_zero apply simp
     apply (fact sqrt_nat_IMP_Minus_imp_minus_correct)
   apply (simp add: sqrt_IMP_tailcall_def)
      subgoal for s
    apply (rule exI)
    apply (subst (2) sqrt_IMP_tailcall_def)
    apply (rule in_bound_weaken_bound)
     apply in_bound_prover+

    apply simp
        apply (rewrite in "_ \<le> \<hole>"sqrt_IMP_tailcall_def)
        apply simp
        done
      done

end

context HOL_To_IMP_Minus
begin

thm tbig_step_in_bound_Calls

end


end