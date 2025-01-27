theory IMP_Tailcalls_Dynamic imports IMP_Calls begin

unbundle no com_syntax and com'_syntax
declare [[syntax_ambiguity_warning=false]]

datatype
  tcom = tSKIP
      | tAssign vname aexp
      | tSeq    tcom  tcom
      | tIf     vname tcom tcom
      | tCall   com vname
\<comment> \<open>Changes: No while, plus a tail-call command\<close>
      | tTAIL

open_bundle tcom_syntax begin
notation tAssign ("_ ::= _" [1000, 61] 61) and
         tSeq ("_;;/ _"  [60, 61] 60) and
         tIf ("(IF _/\<noteq>0 THEN _/ ELSE _)"  [0, 0, 61] 61) and
         tCall ("CALL _ RETURN _")
end
unbundle no com'_syntax

inductive
  tbig_step_t :: "tcom \<Rightarrow> tcom \<times> state \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool" ("_ \<turnstile> _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
tSkip: "c \<turnstile> (tSKIP,s) \<Rightarrow>\<^bsup>Suc (0::nat) \<^esup> s" |
tAssign: "c \<turnstile>(x ::= a,s) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> s(x := aval a s)" |
tSeq: "\<lbrakk>c \<turnstile> (c1,s1) \<Rightarrow>\<^bsup>x \<^esup> s2; c \<turnstile> (c2,s2) \<Rightarrow>\<^bsup>y \<^esup> s3 ; z=x+y \<rbrakk> \<Longrightarrow> c \<turnstile> (c1;;c2, s1) \<Rightarrow>\<^bsup>z \<^esup> s3" |
tIfTrue: "\<lbrakk> s b \<noteq> 0;  c \<turnstile> (c1,s) \<Rightarrow>\<^bsup>x \<^esup> t; y=x+1 \<rbrakk> \<Longrightarrow> c \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup>y \<^esup> t" |
tIfFalse: "\<lbrakk> s b = 0; c \<turnstile> (c2,s) \<Rightarrow>\<^bsup>x \<^esup> t; y=x+1  \<rbrakk> \<Longrightarrow> c \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup>y \<^esup> t" |
tCall: "(C,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> c \<turnstile> (CALL C RETURN r,s) \<Rightarrow>\<^bsup>z \<^esup> (s(r:=t r))" |
\<comment> \<open>New rule\<close>
tTail: "c \<turnstile> (c,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> c \<turnstile> (tTAIL,s) \<Rightarrow>\<^bsup>5 + z \<^esup> t"

code_pred tbig_step_t .

declare tbig_step_t.intros[intro]

lemmas tbig_step_t_induct = tbig_step_t.induct[split_format(complete)]


inductive_cases tSkip_tE[elim!]: "c \<turnstile> (tSKIP,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases tAssign_tE[elim!]: "c \<turnstile> (x ::= a,s) \<Rightarrow>\<^bsup>p \<^esup> t"
inductive_cases tSeq_tE[elim!]: "c \<turnstile> (c1;;c2,s1) \<Rightarrow>\<^bsup>p \<^esup> s3"
inductive_cases tIf_tE[elim!]: "c \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases tCall_tE[elim!]: "c \<turnstile> (CALL C RETURN v,s) \<Rightarrow>\<^bsup>z \<^esup> t"

inductive_cases tTail_tE[elim]: "c \<turnstile> (tTAIL,s) \<Rightarrow>\<^bsup>x \<^esup> t"


instantiation tcom :: vars
begin

fun vars_tcom :: "tcom \<Rightarrow> vname list" where
"vars_tcom (x ::= a)  = x # vars a" |
"vars_tcom (c\<^sub>1;;c\<^sub>2) = vars_tcom c\<^sub>1 @ vars_tcom c\<^sub>2" |
"vars_tcom (IF b\<noteq>0 THEN c1 ELSE c2) = b # vars_tcom c1 @ vars_tcom c2" |
"vars_tcom (CALL c RETURN r) = r#vars c" |
"vars_tcom _ = []"

instance ..

end

fun tails :: "tcom \<Rightarrow> bool" where
  "tails tTAIL \<longleftrightarrow> True" |
  "tails (c1;;c2) \<longleftrightarrow> tails c1 \<or> tails c2" |
  "tails (IF b\<noteq>0 THEN c1 ELSE c2) \<longleftrightarrow> tails c1 \<or> tails c2" |
  "tails _ \<longleftrightarrow> False"

fun invar :: "tcom \<Rightarrow> bool" where
  "invar (c\<^sub>1;;c\<^sub>2) \<longleftrightarrow> \<not>tails c\<^sub>1 \<and> invar c\<^sub>2" |
  "invar (IF b\<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2) \<longleftrightarrow> invar c\<^sub>1 \<and> invar c\<^sub>2" |
  "invar _ \<longleftrightarrow> True"

lemma no_tails_invar[simp]: "\<not>tails c \<Longrightarrow> invar c"
  by (induction c) auto


section \<open>Semantics for small-step-ish reasoning (loops)\<close>
text \<open>Big-step semantics that just returns true for Tail\<close>
inductive
  tail_step :: "(tcom \<times> state) \<Rightarrow> nat \<Rightarrow> (state \<times> bool) \<Rightarrow> bool" ("\<turnstile>_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
Skip: "\<turnstile> (tSKIP,s) \<Rightarrow>\<^bsup>Suc (0::nat) \<^esup> (s,False)" |
Assign: "\<turnstile>(x ::= a,s) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> (s(x := aval a s),False)" |
Seq: "\<lbrakk>\<turnstile> (c1,s1) \<Rightarrow>\<^bsup>x \<^esup> (s2, False); \<turnstile> (c2,s2) \<Rightarrow>\<^bsup>y \<^esup> (s3,CONT) ; z=x+y \<rbrakk> \<Longrightarrow> \<turnstile> (c1;;c2, s1) \<Rightarrow>\<^bsup>z \<^esup> (s3,CONT)" |
IfTrue: "\<lbrakk> s b \<noteq> 0;  \<turnstile> (c1,s) \<Rightarrow>\<^bsup>x \<^esup> (t,CONT); y=x+1 \<rbrakk> \<Longrightarrow> \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup>y \<^esup> (t,CONT)" |
IfFalse: "\<lbrakk> s b = 0; \<turnstile> (c2,s) \<Rightarrow>\<^bsup>x \<^esup> (t,CONT); y=x+1  \<rbrakk> \<Longrightarrow> \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup>y \<^esup> (t,CONT)" |
Call: "(C,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> \<turnstile> (CALL C RETURN r,s) \<Rightarrow>\<^bsup>z \<^esup> (s(r:=t r),False)" |
Tail: "\<turnstile> (tTAIL,s) \<Rightarrow>\<^bsup>5 \<^esup> (s,True)"

code_pred tail_step .

declare tail_step.intros[intro]

lemmas tail_step_induct = tail_step.induct[split_format(complete)]

inductive_cases tailSkip_tE[elim!]: "\<turnstile> (tSKIP,s) \<Rightarrow>\<^bsup>x \<^esup> (t,b)"
inductive_cases tailAssign_tE[elim!]: "\<turnstile> (x ::= a,s) \<Rightarrow>\<^bsup>p \<^esup> (t,b)"
inductive_cases tailSeq_tE[elim!]: "\<turnstile> (c1;;c2,s1) \<Rightarrow>\<^bsup>p \<^esup> (s3,b)"
inductive_cases tailIf_tE[elim!]: "\<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>x \<^esup> (t,CONT)"
inductive_cases tailCall_tE[elim!]: "\<turnstile> (CALL C RETURN v,s) \<Rightarrow>\<^bsup>z \<^esup> (t,b)"

inductive_cases tailTail_tE[elim]: "\<turnstile> (tTAIL,s) \<Rightarrow>\<^bsup>x \<^esup> (t,b)"

text \<open>Closure of tails\<close>
inductive
  tail_steps :: "tcom \<Rightarrow> tcom \<times> state \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool" ("_ \<turnstile>''_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55) for d
where
tFalse: "\<turnstile>(c,s) \<Rightarrow>\<^bsup>z \<^esup> (t,False) \<Longrightarrow> d \<turnstile>'(c,s)\<Rightarrow>\<^bsup>z \<^esup> t" |
tTrue: "\<turnstile>(c,s1) \<Rightarrow>\<^bsup>x \<^esup> (s2,True) \<Longrightarrow> d \<turnstile>'(d,s2)\<Rightarrow>\<^bsup>y \<^esup> s3 \<Longrightarrow> d \<turnstile>'(c,s1)\<Rightarrow>\<^bsup>x+y \<^esup> s3"

code_pred tail_steps .

declare tail_steps.intros[intro]
declare tail_steps.cases[elim]

lemmas tail_steps_induct = tail_steps.induct[split_format(complete)]

lemma no_tails_no_step: "\<turnstile>(c,s) \<Rightarrow>\<^bsup>z \<^esup> (t,b) \<Longrightarrow> \<not>tails c \<Longrightarrow> \<not>b"
  by (induction c s z t b rule: tail_step_induct) auto

lemma no_tails_sem: "\<turnstile>(c,s) \<Rightarrow>\<^bsup>z \<^esup> (t,b) \<Longrightarrow> \<not>tails c \<Longrightarrow> d \<turnstile> (c,s)\<Rightarrow>\<^bsup>z \<^esup> t"
  by (induction c s z t b rule: tail_step_induct) auto

lemma small_sound: "d \<turnstile> (c,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> invar c \<Longrightarrow> invar d \<Longrightarrow> d \<turnstile>' (c,s) \<Rightarrow>\<^bsup>z \<^esup> t"
proof (induction d c s z t rule: tbig_step_t_induct)
  case (tSeq c c1 s1 x s2 c2 y s3 z)
  hence "c \<turnstile>'(c1, s1) \<Rightarrow>\<^bsup>x\<^esup>  s2" "c \<turnstile>'(c2, s2) \<Rightarrow>\<^bsup>y\<^esup>  s3" by auto
  from this tSeq show ?case apply (cases) apply auto
    subgoal
      by (smt (verit) ab_semigroup_add_class.add_ac(1) tail_step.Seq tail_steps.simps)
    subgoal
      by (metis no_tails_no_step)
    done
next
  case (tIfTrue s b c c1 x t y c2)
  hence "c \<turnstile>'(c1, s) \<Rightarrow>\<^bsup>x\<^esup>  t" by auto
  from this tIfTrue show ?case apply (cases) apply auto apply force
    by (metis Suc_eq_plus1 local.tIfTrue(1) plus_nat.simps(2) tail_step.IfTrue tail_steps.intros(2))
next
  case (tIfFalse s b c c2 x t y c1)
  hence "c \<turnstile>'(c2, s) \<Rightarrow>\<^bsup>x\<^esup>  t" by auto
  from this tIfFalse show ?case apply (cases) apply auto apply force
    by (metis Suc_eq_plus1 add_Suc tTrue tail_step.IfFalse)
next
  case (tTail c s z t)
  hence " c \<turnstile>'(c, s) \<Rightarrow>\<^bsup>z\<^esup>  t" by simp
  moreover have "\<turnstile>(tTAIL,s) \<Rightarrow>\<^bsup>5 \<^esup> (s,True)"
    by (metis Tail)
  ultimately show ?case by auto
qed auto

lemma small_complete: "d \<turnstile>' (c,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> invar c \<Longrightarrow> invar d \<Longrightarrow> d \<turnstile> (c,s) \<Rightarrow>\<^bsup>z \<^esup> t"
proof (induction c s z t rule: tail_steps_induct)
  case (tFalse c s z t)
  then show ?case
    by (induction c s z t False rule: tail_step_induct) auto
next
  case (tTrue c s1 x s2 y s3)
  then show ?case
  proof (induction c s1 x s2 True arbitrary:  rule: tail_step_induct)
    case (Seq c1 s1 x s2 c2 y s3 z)
    then show ?case using no_tails_sem apply auto
      using ab_semigroup_add_class.add_ac(1) by blast
  qed auto
qed


unbundle no tcom_syntax and com'_syntax

lemma while'_unrolling:
  assumes "s b \<noteq> 0"
  shows "(c;;WHILE b\<noteq>0 DO c,s)\<Rightarrow>'\<^bsup>z\<^esup> t = (WHILE b\<noteq>0 DO c,s)\<Rightarrow>'\<^bsup>1+z\<^esup> t"
  using assms by auto

lemma tnoninterference:
  "\<lbrakk>c'\<turnstile>(c,s) \<Rightarrow>\<^bsup>x \<^esup> t; set (vars c) \<subseteq> S; set (vars c') \<subseteq> S; v \<notin> S \<rbrakk> \<Longrightarrow> c'\<turnstile>(c,s(v:=y)) \<Rightarrow>\<^bsup>x \<^esup> t(v:=y)"
proof (induction c' c s x t rule: tbig_step_t_induct)
  case (tAssign c x a s)
  hence " s(v := y, x := aval a (s(v := y))) = s(x := aval a s, v := y)" by force
  thus ?case using tbig_step_t.tAssign[of c x a "s(v:=y)"] by argo
next
  case (tCall C s z t c r)
  hence Call: "(C, s(v := y)) \<Rightarrow>\<^bsup>z \<^esup> t(v := y)" using fresh_var_changed by fastforce
  from tCall have state: " s(v := y, r := (t(v := y)) r) = s(r := t r, v := y)" by auto
  show ?case using tbig_step_t.tCall[OF Call, of c r] state by argo
qed (auto | force)+

lemma noninterference':
  "\<lbrakk>\<turnstile>(c,s) \<Rightarrow>\<^bsup>x \<^esup> (t,b); set (vars c) \<subseteq> S; set (vars c') \<subseteq> S; v \<notin> S \<rbrakk> \<Longrightarrow> \<turnstile>(c,s(v:=y)) \<Rightarrow>\<^bsup>x \<^esup> (t(v:=y),b)"
proof (induction c s x t b rule: tail_step_induct)
  case (Assign x a s)
  hence "s(v := y, x := aval a (s(v := y))) = s(x := aval a s, v := y)" by force
  then show ?case using tail_step.Assign[of x a "s(v:=y)"] by argo
next
  case (Call C s z t r)
   hence Call: "(C, s(v := y)) \<Rightarrow>\<^bsup>z \<^esup> t(v := y)" using fresh_var_changed by fastforce
   from tCall have state: " s(v := y, r := (t(v := y)) r) = s(r := t r, v := y)" by auto
   show ?case using tbig_step_t.tCall[OF Call, of c r] state
     by (metis local.Call tail_step.Call)
qed auto

lemma tnoninterference':
  "\<lbrakk>c'\<turnstile>'(c,s) \<Rightarrow>\<^bsup>x \<^esup> t; set (vars c) \<subseteq> S; set (vars c') \<subseteq> S; v \<notin> S \<rbrakk> \<Longrightarrow> c'\<turnstile>'(c,s(v:=y)) \<Rightarrow>\<^bsup>x \<^esup> t(v:=y)"
proof (induction c s x t rule: tail_steps_induct)
  case (tFalse c s z t)
  then show ?case
    using noninterference' by blast
next
  case (tTrue c s1 x s2 y s3)
  then show ?case
    by (meson noninterference' tail_steps.tTrue)
qed

section \<open>Translation between tail-call program and while\<close>

fun translate1 :: "vname \<Rightarrow> tcom \<Rightarrow> com'" where
  "translate1 CONT tTAIL = (CONT ::= A (N 1))" |
  "translate1 CONT (tSeq c1 c2) = (translate1 CONT c1);; translate1 CONT c2" |
  "translate1 CONT (tIf b c1 c2) = (IF b\<noteq>0 THEN translate1 CONT c1 ELSE translate1 CONT c2)" |
  "translate1 CONT (tSKIP) = SKIP'" |
  "translate1 CONT (tAssign v a) = (v ::= a)" |
  "translate1 CONT (tCall c r) = Call' c r"

definition translate :: "vname \<Rightarrow> tcom \<Rightarrow> com'" where
  "translate CONT c = WHILE CONT\<noteq>0 DO (CONT::=A (N 0);;translate1 CONT c)"

lemma set_vars_translate1_subs:
  "set (vars (translate1 CONT c)) \<subseteq> insert CONT (set (vars c))"
  by (induction CONT c rule: translate1.induct) auto

lemma subs_set_vars_translate1:
  "set (vars c) \<subseteq> set (vars (translate1 CONT c))"
  by (induction CONT c rule: translate1.induct) auto

lemma set_vars_translate:
  "set (vars (translate CONT c)) = insert CONT (set (vars c))"
  unfolding translate_def
  using set_vars_translate1_subs subs_set_vars_translate1
  by fastforce

lemma no_tail_cont1: "\<lbrakk>(translate1 CONT c,s)\<Rightarrow>'\<^bsup>z\<^esup> t; \<not>tails c; CONT \<notin> set (vars c)\<rbrakk> \<Longrightarrow> t CONT = s CONT"
  by (induction c arbitrary: s t z) (auto, metis)

lemma no_tail_complete1: "\<lbrakk> (translate1 CONT c,s)\<Rightarrow>'\<^bsup>z\<^esup>t; \<not>tails c \<rbrakk> \<Longrightarrow> d \<turnstile> (c,s)\<Rightarrow>\<^bsup>z\<^esup> t"
proof (induction "translate1 CONT c" s z t arbitrary: c rule: big_step_t'_induct)
  case (Skip' s)
  then show ?case by (cases c) auto
next
  case (Assign' x a s)
  then show ?case by (cases c) (auto simp del: fun_upd_apply)
next
  case (Seq' c1 s1 x s2 c2 y s3 z)
  then show ?case by (cases c) auto
next
  case (IfTrue' s b c1 x t y c2)
  then show ?case apply (cases c) using tIfTrue by auto
next
  case (IfFalse' s b c2 x t y c1)
  then show ?case apply (cases c) apply auto
    using Suc_eq_plus1 by blast
next
  case (WhileFalse' s b c)
  then show ?case by (cases c) auto
next
  case (WhileTrue' s1 b c x s2 y s3 z)
  then show ?case by (cases c) auto
next
  case (Call' c s z t r)
  then show ?case by (cases c) auto
qed

lemma no_tail_complete:
  assumes sem: "(translate1 CONT c;;translate CONT c',s)\<Rightarrow>'\<^bsup>2+z\<^esup>t"
      and no_tail: "\<not>tails c"
      and fresh: "CONT \<notin> set (vars c)"
      and start: "s CONT = 0"
    shows "d \<turnstile> (c,s)\<Rightarrow>\<^bsup>z\<^esup> t"
proof -
  from sem obtain t' x' y' where *:"(translate1 CONT c,s)\<Rightarrow>'\<^bsup>x'\<^esup>t'" "(translate CONT c',t')\<Rightarrow>'\<^bsup>y'\<^esup>t" "2 + z = x' + y'" by auto
  with fresh start have "t' CONT = 0"
    by (metis no_tail no_tail_cont1)
  with * have "t' = t" "y' = 2" by (auto simp: translate_def)
  with * no_tail no_tail_complete1 show ?thesis by auto
qed

lemma translate_sound_gen:
  "\<lbrakk> c' \<turnstile> (c,s) \<Rightarrow>\<^bsup>z\<^esup> t; invar c; invar c'; s CONT = 0; CONT \<notin> S; set (vars c) \<subseteq> S; set (vars c') \<subseteq> S\<rbrakk>
     \<Longrightarrow> (translate1 CONT c;;translate CONT c',s) \<Rightarrow>'\<^bsup>Suc(Suc 0)+z\<^esup> t"
proof (induction c' c s z t rule: tbig_step_t_induct)
  case (tAssign c x a s)
  then show ?case by (auto simp: translate_def simp del: fun_upd_apply) fastforce
next
  case (tSeq c c1 s1 x s2 c2 y s3 z)
  hence 1: "(translate1 CONT c1;; translate CONT c, s1) \<Rightarrow>'\<^bsup> Suc (Suc 0) + x\<^esup>  s2" by auto

  from 1 obtain s' x' y' where *:
    "(translate1 CONT c1, s1)\<Rightarrow>'\<^bsup> x'\<^esup>  s'"
    "(translate CONT c, s')\<Rightarrow>'\<^bsup> y'\<^esup> s2"
    "x' + y' = Suc (Suc 0) + x" by auto
  from * have s': "s' CONT = 0" using no_tail_cont1 using tSeq by auto (metis in_mono)
  with * have 11: "(translate1 CONT c1, s1) \<Rightarrow>'\<^bsup> x\<^esup>  s2"
    using translate_def by auto

  from s' * have "s2 CONT = 0"
    using tSeq by auto (metis "11" determ)
  with tSeq have 2: "(translate1 CONT c2;; translate CONT c, s2) \<Rightarrow>'\<^bsup> Suc (Suc 0) + y\<^esup>  s3"
    by auto

  from 11 2 have "(translate1 CONT c1 ;; (translate1 CONT c2;; translate CONT c), s1) \<Rightarrow>'\<^bsup> Suc (Suc 0) + z\<^esup>  s3"
    using \<open>z = x + y\<close> by auto

  then show ?case by auto
next
  case (tCall C s z t c r)
  then show ?case by (auto simp: translate_def simp del: fun_upd_apply) fastforce
next
  case (tTail c s z t)
  hence "(translate1 CONT c;; translate CONT c, s) \<Rightarrow>'\<^bsup> 2 + z\<^esup>  t" by auto
  moreover have "(CONT ::= A (N 0),s(CONT:=1)) \<Rightarrow>'\<^bsup> 2\<^esup> s"
  proof - (* wtf why is this not automatic *)
    have "(CONT ::= A (N 0),s(CONT:=1)) \<Rightarrow>'\<^bsup> 2\<^esup> s(CONT := 0)"
      using Assign'[of CONT "A (N 0)" "s(CONT:=1)"] by (auto simp: eval_nat_numeral)
    moreover from \<open>s CONT = 0\<close> have "s(CONT := 0) = s" by auto
    ultimately show ?thesis by simp
  qed
  ultimately have "((CONT ::= A (N 0);;translate1 CONT c);; translate CONT c, s(CONT:=1)) \<Rightarrow>'\<^bsup> 4 + z\<^esup>  t"
    by fastforce
  with while'_unrolling have "(translate CONT c, s(CONT:=1)) \<Rightarrow>'\<^bsup> 5 + z\<^esup>  t"
    unfolding translate_def by auto
  then show ?case by auto
qed (auto simp: translate_def)

lemma translate_sound:
  assumes c_sem: "c \<turnstile> (c,s) \<Rightarrow>\<^bsup>z\<^esup> t"
      and invar: "invar c"
      and start: "s CONT \<noteq> 0"
      and fresh: "CONT \<notin> set (vars c)"
    shows "(translate CONT c,s) \<Rightarrow>'\<^bsup>5+z\<^esup> t(CONT:=0)"
proof -
  from c_sem fresh have c_sem2: "c \<turnstile> (c,s(CONT := 0)) \<Rightarrow>\<^bsup>z\<^esup> t(CONT:= 0)"
    using tnoninterference by blast

  have "(CONT::=A (N 0),s) \<Rightarrow>'\<^bsup>Suc (Suc 0)\<^esup> s(CONT:=0)" using Assign'[of CONT "A (N 0)" s] by simp

  moreover have "(translate1 CONT c;; translate CONT c, s(CONT:=0)) \<Rightarrow>'\<^bsup> 2+z\<^esup> t(CONT := 0)"
    using translate_sound_gen c_sem2 invar fresh by simp

  ultimately have "((CONT::=A (N 0);;translate1 CONT c);; translate CONT c, s) \<Rightarrow>'\<^bsup> 4+z\<^esup> t(CONT := 0)"
    apply (simp add: numeral_eq_Suc)
    by (smt (verit, ccfv_SIG) Seq'_tE add.assoc add_2_eq_Suc big_step_t'.Seq' numeral_2_eq_2)
  then show "(translate CONT c,s) \<Rightarrow>'\<^bsup>5+z\<^esup> t(CONT := 0)" using while'_unrolling start translate_def by auto
qed

lemma translate1_complete:
  "\<lbrakk> (translate1 CONT c,s)\<Rightarrow>'\<^bsup>z\<^esup>t; s CONT = 0; invar c; set (vars c) \<subseteq> S; CONT \<notin> S \<rbrakk>
     \<Longrightarrow> (if t CONT \<noteq> 0 then \<turnstile>(c,s) \<Rightarrow>\<^bsup>3+z\<^esup> (t(CONT := s CONT),True) else \<turnstile>(c,s) \<Rightarrow>\<^bsup>z\<^esup> (t,False))"
proof (induction "translate1 CONT c" s z t arbitrary: c rule: big_step_t'_induct)
  case (Skip' s)
  then show ?case by (cases c) auto
next
  case (Assign' x a s)
  thus ?case apply (cases c) apply (auto split: if_splits)
    by (metis Tail fun_upd_triv)
next
  case (Seq' c1 s1 x s2 c2 y s3 z)
  then show ?case
    apply (cases c)
         apply (auto split: if_splits)
    subgoal
      by (smt (verit, best) Seq'.hyps(2) add.left_commute no_tails_invar no_tails_no_step tail_step.Seq)
    subgoal
      by (metis Seq'.hyps(2) no_tails_invar no_tails_no_step tail_step.Seq)

    done
next
  case (IfTrue' s b c1 x t y c2)
  then show ?case apply (cases c) apply (auto split: if_splits)
    subgoal
      by (smt (verit) IfTrue'.hyps(1) One_nat_def Suc_1 Suc_eq_plus1 numeral.simps(2) numeral_3_eq_3 plus_1_eq_Suc plus_nat.simps(2) tail_step.IfTrue)
    subgoal
      using IfTrue'.hyps by blast

    done
next
  case (IfFalse' s b c2 x t y c1)
  then show ?case apply (cases c) apply (auto split: if_splits)
    subgoal
          by (smt (verit, ccfv_threshold) One_nat_def Suc_1 Suc_eq_plus1 numeral.simps(2) numeral_3_eq_3 plus_1_eq_Suc plus_nat.simps(2) tail_step.IfFalse)
    subgoal using IfFalse'.hyps by blast

    done
next
  case (WhileFalse' s b c)
  then show ?case apply (cases c) apply auto done
next
  case (WhileTrue' s1 b c x s2 y s3 z)
  then show ?case apply (cases c) apply auto done
next
  case (Call' c s z t r)
  then show ?case apply (cases c) apply auto done
qed

lemma loop_min: "(WHILE b\<noteq>0 DO c, s) \<Rightarrow>'\<^bsup> z\<^esup>  t \<Longrightarrow> (c,s) \<Rightarrow>'\<^bsup>x\<^esup> s2 \<Longrightarrow> s b \<noteq> 0 \<Longrightarrow> z \<ge> 3+x"
  apply (induction "WHILE b\<noteq>0 DO c" s z t rule: big_step_t'_induct) apply simp using determ by fastforce

lemma translate_complete:
  "\<lbrakk> (translate CONT c,s)\<Rightarrow>'\<^bsup>5+z\<^esup>t; s CONT \<noteq> 0; invar c; CONT \<notin> set (vars c) \<rbrakk>
    \<Longrightarrow> c \<turnstile>'(c,s) \<Rightarrow>\<^bsup>z\<^esup> t(CONT:= s CONT)"
proof (induction "translate CONT c" s "5+z" t arbitrary: z rule: big_step_t'_induct)
  case (WhileTrue' s1 b c' x s2 y s3 )

  hence c'_def: "c' = CONT::=A (N 0);;translate1 CONT c" and b_def: "b = CONT" by (auto simp: translate_def)

  have 0: "(CONT::=A (N 0),s1) \<Rightarrow>'\<^bsup>Suc (Suc 0)\<^esup>s1(CONT := 0)"
    using Assign'[of CONT "A (N 0)" s1,simplified] by (simp add: numeral_eq_Suc)

  obtain x' where 1:
    "x' + Suc (Suc 0) = x" "(translate1 CONT c,s1(CONT:=0))\<Rightarrow>'\<^bsup> x'\<^esup>s2"
    using WhileTrue'.hyps (2)[unfolded c'_def] by auto

  show ?case proof (cases "s2 CONT = 0")
    case True
    hence "\<turnstile>(c,s1(CONT:=0)) \<Rightarrow>\<^bsup>x'\<^esup> (s2,False)" using translate1_complete 1 WhileTrue' by fastforce

    moreover from \<open>(WHILE b\<noteq>0 DO c', s2) \<Rightarrow>'\<^bsup> y\<^esup>  s3\<close> have "s2 = s3" "y = Suc (Suc 0)" using True b_def by auto
    ultimately have "\<turnstile>(c,s1) \<Rightarrow>\<^bsup>x'\<^esup> (s3(CONT := s1 CONT),False)"
      using WhileTrue' noninterference'
      by (smt (verit, ccfv_threshold) fun_upd_idem_iff fun_upd_upd order_le_less)
    hence "c \<turnstile>'(c, s1) \<Rightarrow>\<^bsup>x'\<^esup>  s3(CONT := s1 CONT)" by auto
    moreover from  \<open>x' + Suc (Suc 0) = x\<close> \<open>1 + x + y = 5+z\<close> \<open>y = Suc (Suc 0)\<close> have "x' = z" by simp
    ultimately show ?thesis by blast
  next
    case False
    with \<open>(WHILE b\<noteq>0 DO c', s2) \<Rightarrow>'\<^bsup> y\<^esup>  s3\<close> obtain s2' z' where "(c',s2) \<Rightarrow>'\<^bsup>z'\<^esup> s2'"
      using b_def by auto
    hence "z' \<ge> 2" unfolding c'_def by auto
    with loop_min have "y \<ge> 5"
      using False WhileTrue'.hyps(4) \<open>(c', s2) \<Rightarrow>'\<^bsup> z'\<^esup> s2'\<close> b_def by fastforce
    then obtain y' where y'_def: "y = 5 + y'"
      using nat_le_iff_add by blast
    from 1 have 2: "\<turnstile>(c,s1(CONT:=0)) \<Rightarrow>\<^bsup>1+x\<^esup> (s2(CONT := 0), True)"
      using translate1_complete[of CONT c "s1(CONT := 0)" x' s2] False WhileTrue' by (auto simp: numeral_eq_Suc)

    from False WhileTrue' y'_def have "c \<turnstile>'(c, s2) \<Rightarrow>\<^bsup>y'\<^esup>  s3(CONT := s2 CONT)" by auto
    hence 3: "c \<turnstile>'(c, s2(CONT := 0)) \<Rightarrow>\<^bsup>y'\<^esup>  s3(CONT := 0)"
      using tnoninterference' WhileTrue' by (metis fun_upd_upd order.refl)

    from \<open>1 + x + y = 5 + z\<close> y'_def have "c \<turnstile>'(c, s1(CONT := 0)) \<Rightarrow>\<^bsup>z\<^esup>  s3(CONT := 0)"
      using tTrue[OF 2 3] by simp

    then show ?thesis using  WhileTrue' tnoninterference'
      by (metis (mono_tags, lifting) dual_order.refl fun_upd_triv fun_upd_upd)
  qed
qed (auto simp: translate_def)


section \<open>Final compilation\<close>
definition compile :: "tcom \<Rightarrow> com'" where
  "compile c = (let CONT = fresh (vars c) ''CONTINUE'' in CONT::=A (N 1);;translate CONT c)"

lemma set_vars_compile:
  "set (vars (compile c)) = insert (fresh (vars c) ''CONTINUE'') (set (vars c))"
  unfolding compile_def Let_def by (simp add: set_vars_translate)

lemma compile_sound:
  assumes c_sem: "c \<turnstile> (c,s) \<Rightarrow>\<^bsup>z\<^esup> t"
      and invar: "invar c"
  obtains t' where "(compile c,s) \<Rightarrow>'\<^bsup>7+z\<^esup> t'" and "t = t' on set (vars c)"
proof -
  let ?CONT="fresh (vars c) ''CONTINUE''"
  have 1: "(?CONT::=A (N 1),s) \<Rightarrow>'\<^bsup>2\<^esup> s(?CONT:=1)"
    using Assign'[of ?CONT "A (N 1)" s] by (auto simp: eval_nat_numeral)
  from c_sem have "c \<turnstile> (c,s(?CONT:=1))\<Rightarrow>\<^bsup>z\<^esup> t(?CONT:=1)"
    using fresh tnoninterference by (meson dual_order.refl)

  hence "(translate ?CONT c, s(?CONT:=1)) \<Rightarrow>'\<^bsup> 5 + z\<^esup> t(?CONT := 0)"
    using translate_sound invar fresh by (fastforce simp: numeral_eq_Suc)

  hence "(compile c,s)\<Rightarrow>'\<^bsup> 7 + z\<^esup> t(?CONT := 0)" unfolding compile_def
    using 1 apply (simp add: numeral_eq_Suc)
    by (smt (verit, best) IMP_Calls.Seq'' add_2_eq_Suc numeral_2_eq_2)

  with that show ?thesis by simp
qed


lemma compile_complete_add:
  assumes sem: "(compile c,s) \<Rightarrow>'\<^bsup>z + 7\<^esup> t"
      and invar: "invar c"
  obtains t' where "c \<turnstile> (c,s)\<Rightarrow>\<^bsup>z\<^esup> t'" and "t = t' on set (vars c)"
proof -
  let ?CONT="fresh (vars c) ''CONTINUE''"
  have 1: "(?CONT::=A (N 1),s) \<Rightarrow>'\<^bsup>2\<^esup> s(?CONT:=1)"
    using Assign'[of ?CONT "A (N 1)" s] by (auto simp: eval_nat_numeral)

  with sem[unfolded compile_def] have "(translate ?CONT c, s(?CONT:=1)) \<Rightarrow>'\<^bsup> 5 + z\<^esup> t"
    unfolding compile_def apply (auto simp: numeral_eq_Suc) using Seq'_tE
    by (smt (verit, best) "1" Assign'_tE One_nat_def add_Suc add_left_imp_eq plus_1_eq_Suc)

  hence "c \<turnstile> (c,s(?CONT:=1)) \<Rightarrow>\<^bsup>z\<^esup> t(?CONT:=1)"
    using translate_complete small_complete fresh invar by (fastforce simp: numeral_eq_Suc)

  hence "c \<turnstile> (c,s) \<Rightarrow>\<^bsup>z\<^esup> t(?CONT:=s ?CONT)"
    using tnoninterference[where S="set (vars c)"] fresh invar apply auto
    by (smt (verit, best) dual_order.refl fresh fun_upd_triv fun_upd_upd)

  with that show ?thesis using fresh by auto
qed

lemma compile_time_7_le:
  assumes "(compile c,s) \<Rightarrow>'\<^bsup>z\<^esup> t"
  shows "7 \<le> z"
  using assms
proof (induction "compile c" s z t arbitrary: c rule: big_step_t'_induct)
case (Seq' c1 s1 x s2 c2 y s3 z)
then show ?case
  apply (auto simp: compile_def Let_def translate_def)
  apply (erule While'_tE)
  apply auto
  done
qed (auto simp: compile_def Let_def translate_def)

lemma compile_complete:
  assumes "(compile c,s) \<Rightarrow>'\<^bsup>z\<^esup> t"
      and "invar c"
  obtains t' where "c \<turnstile> (c,s)\<Rightarrow>\<^bsup>z - 7\<^esup> t'" and "t = t' on set (vars c)"
  using assms compile_complete_add compile_time_7_le
  by (metis add.commute le_add_diff_inverse)

end