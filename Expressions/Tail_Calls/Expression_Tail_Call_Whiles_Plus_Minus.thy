\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expression_Tail_Call_Whiles_Plus_Minus
  imports
    Expressions_Whiles_Plus_Minus
    Expression_Tail_Calls_Hom
begin

text\<open>Tail recursive WHILE programs with plus, minus, and atomic values\<close>
datatype ('si, 'sv, 'eic, 'ewc) exp_tail_call_while_plus_minus = ETCWPM
  "(('si, 'sv, 'eic, 'ewc) exp_while_plus_minus) exp_tcall_hom"

text \<open>TODO: generalise to take arbitrary evaluator for assignment expressions.\<close>
context
  fixes eval_eic :: "('t :: {zero,one,plus}, bool, 'si, 'sv :: {minus, plus}, 'eic) eval_time"
  and eval_ewc :: "('t, bool, 'si, 'sv, 'ewc) eval_time"
  and r_while :: "'sv"
  and eval_ewhile_tail_call_while_plus_minus
  defines [simp]: "eval_ewhile_tail_call_while_plus_minus \<equiv>
    eval_exp_while_plus_minus_assign_pure_state eval_eic eval_ewc r_while"
begin

definition "eval_etcall_tail_call_while_plus_minus \<equiv>
  eval_exp_tcall_hom eval_ewhile_tail_call_while_plus_minus"
definition "eval_efgcall_tail_call_while_plus_minus \<equiv>
  eval_efgcall_tcall_hom eval_ewhile_tail_call_while_plus_minus"

definition [exp_smart_constructor_def]: "FGCWPMV v \<equiv> FGCBase (WPMV v)"
definition [exp_smart_constructor_def]: "FGCWPMSI si \<equiv> FGCBase (WPMSI si)"
definition [exp_smart_constructor_def]: "FGCWPMPlus epl epr \<equiv> FGCBase (WPMPlus epl epr)"
definition [exp_smart_constructor_def]: "FGCWPMMinus eml emr \<equiv> FGCBase (WPMMinus eml emr)"
definition [exp_smart_constructor_def]: "FGCWPMAssign si ea \<equiv> FGCBase (WPMAssign si ea)"
definition [exp_smart_constructor_def]: "FGCWPMSeq esf esb \<equiv> FGCBase (WPMSeq esf esb)"
definition [exp_smart_constructor_def]: "FGCWPMIf eic eit eif \<equiv> FGCBase (WPMIf eic eit eif)"
definition [exp_smart_constructor_def]: "FGCWPMWhile ewc ew \<equiv> FGCBase (WPMWhile ewc ew)"

lemma eval_etcall_tail_call_while_plus_minus_TCI[intro]:
  assumes "eval_efgcall_tail_call_while_plus_minus (TC e) e s t s' v"
  shows "eval_etcall_tail_call_while_plus_minus (TC e) s t s' v"
  using assms unfolding eval_etcall_tail_call_while_plus_minus_def
    eval_efgcall_tail_call_while_plus_minus_def
  by blast

lemma eval_etcall_tail_call_while_plus_minus_TCE[elim]:
  assumes "eval_etcall_tail_call_while_plus_minus (TC e) s t s' v"
  obtains "eval_efgcall_tail_call_while_plus_minus (TC e) e s t s' v"
  using assms unfolding eval_etcall_tail_call_while_plus_minus_def
    eval_efgcall_tail_call_while_plus_minus_def
  by blast

lemma eval_efgcall_tail_call_while_plus_minus_FGCBaseI[intro]:
  assumes "eval_ewhile_tail_call_while_plus_minus eb s t s' v"
  shows "eval_efgcall_tail_call_while_plus_minus etc (FGCBase eb) s t s' v"
  using assms unfolding eval_efgcall_tail_call_while_plus_minus_def by auto

lemma eval_efgcall_tail_call_while_plus_minus_FGCBaseE[elim]:
  assumes "eval_efgcall_tail_call_while_plus_minus etc (FGCBase eb) s t s' v"
  obtains "eval_ewhile_tail_call_while_plus_minus eb s t s' v"
  using assms unfolding eval_efgcall_tail_call_while_plus_minus_def by auto

lemma eval_efgcall_tail_call_while_plus_minus_FGCWPMVI[intro]:
  assumes "s = s'"
  and "v = v'"
  and "t = 0"
  shows "eval_efgcall_tail_call_while_plus_minus etc (FGCWPMV v) s t s' v"
  using assms unfolding FGCWPMV_def eval_efgcall_tail_call_while_plus_minus_def by auto

lemma eval_efgcall_tail_call_while_plus_minus_FGCWPMVE[elim]:
  assumes "eval_efgcall_tail_call_while_plus_minus etc (FGCWPMV v) s t s' v'"
  obtains "s = s'" "v = v'" "t = 0"
  using assms unfolding FGCWPMV_def eval_efgcall_tail_call_while_plus_minus_def by auto

lemma eval_efgcall_tail_call_while_plus_minus_FGCWPMSII[intro]:
  assumes "s = s'"
  and "v' = s si"
  and "t = 1"
  shows "eval_efgcall_tail_call_while_plus_minus etc (FGCWPMSI si) s t s' v'"
  using assms unfolding FGCWPMSI_def eval_efgcall_tail_call_while_plus_minus_def by auto

lemma eval_efgcall_tail_call_while_plus_minus_FGCWPMSIE[elim]:
  assumes "eval_efgcall_tail_call_while_plus_minus etc (FGCWPMSI si) s t s' v'"
  obtains "s = s'" "v' = s si" "t = 1"
  using assms unfolding FGCWPMSI_def eval_efgcall_tail_call_while_plus_minus_def by auto

lemma eval_efgcall_tail_call_while_plus_minus_FGCWPMPlusI[intro]:
  assumes "eval_ewhile_tail_call_while_plus_minus epl s t1 s1 v1"
  and "eval_ewhile_tail_call_while_plus_minus epr s1 t2 s2 v2"
  and "s' = s2"
  and "v = v1 + v2"
  and "t = t1 + t2 + 1"
  shows "eval_efgcall_tail_call_while_plus_minus etc (FGCWPMPlus epl epr) s t s' v"
  using assms unfolding FGCWPMPlus_def eval_efgcall_tail_call_while_plus_minus_def by auto

lemma eval_efgcall_tail_call_while_plus_minus_FGCWPMPlusE[elim]:
  assumes "eval_efgcall_tail_call_while_plus_minus etc (FGCWPMPlus epl epr) s t s' v"
  obtains t1 s1 v1 t2 s2 v2 where "eval_ewhile_tail_call_while_plus_minus epl s t1 s1 v1"
    "eval_ewhile_tail_call_while_plus_minus epr s1 t2 s2 v2" "s' = s2" "v = v1 + v2" "t = t1 + t2 + 1"
  using assms unfolding FGCWPMPlus_def eval_efgcall_tail_call_while_plus_minus_def by fastforce

lemma eval_efgcall_tail_call_while_plus_minus_FGCWPMMinusI[intro]:
  assumes "eval_ewhile_tail_call_while_plus_minus eml s t1 s1 v1"
  and "eval_ewhile_tail_call_while_plus_minus emr s1 t2 s2 v2"
  and "s' = s2"
  and "v = v1 - v2"
  and "t = t1 + t2 + 1"
  shows "eval_efgcall_tail_call_while_plus_minus etc (FGCWPMMinus eml emr) s t s' v"
  using assms unfolding FGCWPMMinus_def eval_efgcall_tail_call_while_plus_minus_def by auto

lemma eval_efgcall_tail_call_while_plus_minus_FGCWPMMinusE[elim]:
  assumes "eval_efgcall_tail_call_while_plus_minus etc (FGCWPMMinus eml emr) s t s' v"
  obtains t1 s1 v1 t2 s2 v2 where "eval_ewhile_tail_call_while_plus_minus eml s t1 s1 v1"
    "eval_ewhile_tail_call_while_plus_minus emr s1 t2 s2 v2" "s' = s2" "v = v1 - v2" "t = t1 + t2 + 1"
  using assms unfolding FGCWPMMinus_def eval_efgcall_tail_call_while_plus_minus_def by fastforce

lemma eval_efgcall_tail_call_while_plus_minus_FGCWPMAssignI[intro]:
  assumes "eval_ewhile_tail_call_while_plus_minus ea s t' s'' v"
  and "s' = s(si := v)"
  and "t = t' + 1"
  shows "eval_efgcall_tail_call_while_plus_minus etc (FGCWPMAssign si ea) s t s' v"
  using assms unfolding FGCWPMAssign_def eval_efgcall_tail_call_while_plus_minus_def by auto

lemma eval_efgcall_tail_call_while_plus_minus_FGCWPMAssignE[elim]:
  assumes "eval_efgcall_tail_call_while_plus_minus etc (FGCWPMAssign si ea) s t s' v"
  obtains t' s'' v where "eval_ewhile_tail_call_while_plus_minus ea s t' s'' v" "s' = s(si := v)" "t = t' + 1"
  using assms unfolding FGCWPMAssign_def eval_efgcall_tail_call_while_plus_minus_def by fastforce

lemma eval_efgcall_tail_call_while_plus_minus_FGCWPMSeqI[intro]:
  assumes "eval_ewhile_tail_call_while_plus_minus (EWPM esf) s tf sf vf"
  assumes "eval_ewhile_tail_call_while_plus_minus (EWPM esb) sf tb s' v"
  and "t = tf + tb"
  shows "eval_efgcall_tail_call_while_plus_minus etc (FGCWPMSeq esf esb) s t s' v"
  using assms unfolding FGCWPMSeq_def eval_efgcall_tail_call_while_plus_minus_def by auto

lemma eval_efgcall_tail_call_while_plus_minus_FGCWPMSeqE[elim]:
  assumes "eval_efgcall_tail_call_while_plus_minus etc (FGCWPMSeq esf esb) s t s' v"
  obtains tf sf vf tb where "eval_ewhile_tail_call_while_plus_minus (EWPM esf) s tf sf vf"
    "eval_ewhile_tail_call_while_plus_minus (EWPM esb) sf tb s' v" "t = tf + tb"
  using assms unfolding FGCWPMSeq_def eval_efgcall_tail_call_while_plus_minus_def by fastforce

lemma eval_efgcall_tail_call_while_plus_minus_FGCWPMIf_trueI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "b"
  and "eval_ewhile_tail_call_while_plus_minus (EWPM eit) sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_efgcall_tail_call_while_plus_minus etc (FGCWPMIf eic eit eif) s t s' v"
  using assms unfolding FGCWPMIf_def eval_efgcall_tail_call_while_plus_minus_def by auto

lemma eval_efgcall_tail_call_while_plus_minus_FGCWPMIf_falseI[intro]:
  assumes "eval_eic eic s t1 sc b"
  and "\<not>b"
  and "eval_ewhile_tail_call_while_plus_minus (EWPM eif) sc t2 s' v"
  and "t = t1 + 1 + t2"
  shows "eval_efgcall_tail_call_while_plus_minus etc (FGCWPMIf eic eit eif) s t s' v"
  using assms unfolding FGCWPMIf_def eval_efgcall_tail_call_while_plus_minus_def by auto

lemma eval_efgcall_tail_call_while_plus_minus_FGCWPMIfE[elim]:
  assumes "eval_efgcall_tail_call_while_plus_minus etc (FGCWPMIf eic eit eif) s t s' v"
  obtains sc b t1 t2 where "eval_eic eic s t1 sc b" "b"
      "eval_ewhile_tail_call_while_plus_minus (EWPM eit) sc t2 s' v" "t = t1 + 1 + t2"
    | sc b t1 t2 where "eval_eic eic s t1 sc b" "\<not>b" "eval_ewhile_tail_call_while_plus_minus (EWPM eif) sc t2 s' v"
        "t = t1 + 1 + t2"
  using assms unfolding FGCWPMIf_def eval_efgcall_tail_call_while_plus_minus_def by (auto 0 3)

lemma eval_efgcall_tail_call_while_plus_minus_FGCWPMWhile_trueI[intro]:
  assumes "eval_ewc ewc s t1 sc b" "b"
  and "eval_ewhile_tail_call_while_plus_minus (EWPM ewpm) sc t2 s2 vew"
  and "eval_ewhile_tail_call_while_plus_minus (WPMWhile ewc ewpm) s2 t3 s' v"
  and "t = t1 + 1 + t2 + t3"
  shows "eval_efgcall_tail_call_while_plus_minus etc (FGCWPMWhile ewc ewpm) s t s' v"
  using assms unfolding FGCWPMWhile_def eval_efgcall_tail_call_while_plus_minus_def by auto

lemma eval_efgcall_tail_call_while_plus_minus_FGCWPMWhile_falseI[intro]:
  assumes "eval_ewc ewc s t' sc b" "\<not>b"
  and "t = t' + 1"
  and "s = s'"
  and "v = r_while"
  shows "eval_efgcall_tail_call_while_plus_minus etc (FGCWPMWhile ewc ewpm) s t s' v"
  using assms unfolding FGCWPMWhile_def eval_efgcall_tail_call_while_plus_minus_def by auto

lemma eval_efgcall_tail_call_while_plus_minus_FGCWPMWhileE[elim]:
  assumes "eval_efgcall_tail_call_while_plus_minus etc (FGCWPMWhile ewc ewpm) s t s' v"
  obtains t1 sc b t2 s2 vew t3 v3 where "eval_ewc ewc s t1 sc b" "b"
      "eval_ewhile_tail_call_while_plus_minus (EWPM ewpm) sc t2 s2 vew"
      "eval_ewhile_tail_call_while_plus_minus (WPMWhile ewc ewpm) s2 t3 s' v"
      "t = t1 + 1 + t2 + t3"
    | t' sc b where "eval_ewc ewc s t' sc b" "\<not>b" "s = s'" "v = r_while" "t = t' + 1"
  using assms unfolding FGCWPMWhile_def
  apply (elim eval_efgcall_tail_call_while_plus_minus_FGCBaseE)
  apply (unfold eval_ewhile_tail_call_while_plus_minus_def)
  apply (erule eval_exp_while_plus_minus_assign_pure_state_WPMWhileE)
  by blast+

lemma eval_efgcall_tail_call_while_plus_minus_FGCSeqI[intro]:
  assumes "eval_ewhile_tail_call_while_plus_minus esf s tf sf vf"
  and "eval_efgcall_tail_call_while_plus_minus etc esb sf tb s' v"
  and "t = tf + tb"
  shows "eval_efgcall_tail_call_while_plus_minus etc (FGCSeq esf esb) s t s' v"
  using assms unfolding eval_efgcall_tail_call_while_plus_minus_def by auto

lemma eval_efgcall_tail_call_while_plus_minus_FGCSeqE[elim]:
  assumes "eval_efgcall_tail_call_while_plus_minus etc (FGCSeq esf esb) s t s' v"
  obtains tf sf vf tb where "eval_ewhile_tail_call_while_plus_minus esf s tf sf vf"
    "eval_efgcall_tail_call_while_plus_minus etc esb sf tb s' v" "t = tf + tb"
  using assms unfolding eval_efgcall_tail_call_while_plus_minus_def by auto

lemma eval_efgcall_tail_call_while_plus_minus_FGCGlobal_CallI[intro]:
  assumes "eval_etcall_tail_call_while_plus_minus etc s t s' v"
  shows "eval_efgcall_tail_call_while_plus_minus etc FGCGlobal_Call s t s' v"
  using assms unfolding eval_etcall_tail_call_while_plus_minus_def eval_efgcall_tail_call_while_plus_minus_def
  by auto

lemma eval_efgcall_tail_call_while_plus_minus_FGCGlobal_CallE[elim]:
  assumes "eval_efgcall_tail_call_while_plus_minus etc FGCGlobal_Call s t s' v"
  obtains "eval_etcall_tail_call_while_plus_minus etc s t s' v"
  using assms unfolding eval_etcall_tail_call_while_plus_minus_def eval_efgcall_tail_call_while_plus_minus_def
  by auto

lemma not_eval_efgcall_tail_call_while_plus_minus_TC_FGCGlobal_Call_FGCGlobal_Call[iff]:
  "\<not>(eval_efgcall_tail_call_while_plus_minus (TC FGCGlobal_Call) FGCGlobal_Call s t s' v)"
  unfolding eval_efgcall_tail_call_while_plus_minus_def by blast

lemma not_eval_etcall_tail_call_while_plus_minus_TC_FGCGlobal_Call[iff]:
  "\<not>(eval_etcall_tail_call_while_plus_minus (TC FGCGlobal_Call) s t s' v)"
  unfolding eval_etcall_tail_call_while_plus_minus_def
  by (intro notI) blast

lemma eval_efgcall_tail_call_while_plus_minus_induct[induct pred : eval_efgcall_tail_call_while_plus_minus,
  case_names eq_TC FGCWPMV FGCWPSI FGCWPPlus FGCWPMinus FGCWPAssign FGCWPSeq FGCWPIf_true FGCWPIf_false
    FGCWPWhile_true FGCWPWhile_false FGCSeq FGCGlobal_Call]:
  assumes "eval_efgcall_tail_call_while_plus_minus etc e s t s' v"
  and "etc = TC efgc"
  and "\<And>v s. P (FGCWPMV v) s 0 s v"
  and "\<And>si s. P (FGCWPMSI si) s 1 s (s si)"
  and "\<And>epl s t1 s1 v1 epr t2 s2 v2. eval_ewhile_tail_call_while_plus_minus epl s t1 s1 v1 \<Longrightarrow>
    P (FGCBase epl) s t1 s1 v1 \<Longrightarrow> eval_ewhile_tail_call_while_plus_minus epr s1 t2 s2 v2 \<Longrightarrow>
    P (FGCBase epr) s1 t2 s2 v2 \<Longrightarrow> P (FGCWPMPlus epl epr) s (t1 + t2 + 1) s2 (v1 + v2)"
  and "\<And>eml s t1 s1 v1 emr t2 s2 v2. eval_ewhile_tail_call_while_plus_minus eml s t1 s1 v1 \<Longrightarrow>
    P (FGCBase eml) s t1 s1 v1 \<Longrightarrow> eval_ewhile_tail_call_while_plus_minus emr s1 t2 s2 v2 \<Longrightarrow>
    P (FGCBase emr) s1 t2 s2 v2 \<Longrightarrow> P (FGCWPMMinus eml emr) s (t1 + t2 + 1) s2 (v1 - v2)"
  and "\<And>ea s t s' v si. eval_ewhile_tail_call_while_plus_minus ea s t s' v \<Longrightarrow>
    P (FGCBase ea) s t s' v \<Longrightarrow> P (FGCWPMAssign si ea) s (t + 1) (s(si := v)) v"
  and "\<And>esf s tf sf vf esb tb sb vb. eval_ewhile_tail_call_while_plus_minus (EWPM esf) s tf sf vf \<Longrightarrow>
    P (FGCBase (EWPM esf)) s tf sf vf \<Longrightarrow> eval_ewhile_tail_call_while_plus_minus (EWPM esb) sf tb sb vb \<Longrightarrow>
    P (FGCBase (EWPM esb)) sf tb sb vb \<Longrightarrow> P (FGCWPMSeq esf esb) s (tf + tb) sb vb"
  and "\<And>eic s t1 sc b eit t2 s' v eif. eval_eic eic s t1 sc b \<Longrightarrow> b \<Longrightarrow>
    eval_ewhile_tail_call_while_plus_minus (EWPM eit) sc t2 s' v \<Longrightarrow>
    P (FGCBase (EWPM eit)) sc t2 s' v \<Longrightarrow> P (FGCWPMIf eic eit eif) s (t1 + 1 + t2) s' v"
  and "\<And>eic s t1 sc b eif t2 s' v eit. eval_eic eic s t1 sc b \<Longrightarrow> \<not>b \<Longrightarrow>
    eval_ewhile_tail_call_while_plus_minus (EWPM eif) sc t2 s' v \<Longrightarrow>
    P (FGCBase (EWPM eif)) sc t2 s' v \<Longrightarrow> P (FGCWPMIf eic eit eif) s (t1 + 1 + t2) s' v"
  and "\<And>ewc ewpm s1 t1 sc b t2 s2 vew t3 s3 v3. eval_ewc ewc s1 t1 sc b \<Longrightarrow> b \<Longrightarrow>
    eval_ewhile_tail_call_while_plus_minus (EWPM ewpm) sc t2 s2 vew \<Longrightarrow> P (FGCBase (EWPM ewpm)) sc t2 s2 vew \<Longrightarrow>
    eval_ewhile_tail_call_while_plus_minus (WPMWhile ewc ewpm) s2 t3 s3 v3 \<Longrightarrow>
    P (FGCWPMWhile ewc ewpm) s2 t3 s3 v3 \<Longrightarrow> P (FGCWPMWhile ewc ewpm) s1 (t1 + 1 + t2 + t3) s3 v3"
  and "\<And>ewc ew s t sc b. eval_ewc ewc s t sc b \<Longrightarrow> \<not>b \<Longrightarrow> P (FGCWPMWhile ewc ew) s (t + 1) s r_while"
  and "\<And>esf s tf sf vf esb tb sb vb. eval_ewhile_tail_call_while_plus_minus esf s tf sf vf \<Longrightarrow>
    P (FGCBase esf) s tf sf vf \<Longrightarrow> eval_efgcall_tail_call_while_plus_minus etc esb sf tb sb vb \<Longrightarrow>
    P esb sf tb sb vb \<Longrightarrow> P (FGCSeq esf esb) s (tf + tb) sb vb"
  and "\<And>s t s' v. eval_efgcall_tail_call_while_plus_minus etc efgc s t s' v \<Longrightarrow> P efgc s t s' v \<Longrightarrow>
    P FGCGlobal_Call s t s' v"
  shows "P e s t s' v"
  using assms(1) unfolding eval_efgcall_tail_call_while_plus_minus_def
proof (induction taking: efgc rule: eval_efgcall_tcall_hom_induct)
  case (FGCBase eb s t s' v)
  then show ?case unfolding eval_ewhile_tail_call_while_plus_minus_def
  proof (induction rule: eval_exp_while_plus_minus_assign_pure_state_induct)
    case (WAssign ea s t s' v si)
    then show ?case
    by (induction ea s t s' v rule: eval_exp_while_plus_minus_assign_pure_state_induct,
      fold exp_smart_constructor_def)
    (intro assms, fold exp_smart_constructor_def, auto)+
  qed (fold exp_smart_constructor_def eval_efgcall_tail_call_while_plus_minus_def, auto intro: assms)
next
  case (FGCSeq esf s tf sf vf esb tb sb vb)
  from this(1) have "P (FGCBase esf) s tf sf vf"
    unfolding eval_ewhile_tail_call_while_plus_minus_def
    by (induction esf s tf sf vf rule: eval_exp_while_plus_minus_assign_pure_state_induct,
      fold exp_smart_constructor_def eval_ewhile_tail_call_while_plus_minus_def)
    (blast intro: assms)+
  with FGCSeq show ?case
    by (fold eval_efgcall_tail_call_while_plus_minus_def) (blast intro: assms)
qed (fold eval_efgcall_tail_call_while_plus_minus_def, auto intro: assms)

corollary eval_etcall_tail_call_while_plus_minus_induct[induct pred : eval_etcall_tail_call_while_plus_minus,
  case_names V SI Plus Minus Assign WSeq If_true If_false While_true While_false TSeq]:
  assumes "eval_etcall_tail_call_while_plus_minus e s t s' v"
  and "\<And>v s. P e s 0 s v"
  and "\<And>si s. P e s 1 s (s si)"
  and "\<And>epl s t1 s1 v1 epr t2 s2 v2. eval_ewhile_tail_call_while_plus_minus epl s t1 s1 v1 \<Longrightarrow>
    P e s t1 s1 v1 \<Longrightarrow> eval_ewhile_tail_call_while_plus_minus epr s1 t2 s2 v2 \<Longrightarrow>
    P e s1 t2 s2 v2 \<Longrightarrow> P e s (t1 + t2 + 1) s2 (v1 + v2)"
  and "\<And>eml s t1 s1 v1 emr t2 s2 v2. eval_ewhile_tail_call_while_plus_minus eml s t1 s1 v1 \<Longrightarrow>
    P e s t1 s1 v1 \<Longrightarrow> eval_ewhile_tail_call_while_plus_minus emr s1 t2 s2 v2 \<Longrightarrow>
    P e s1 t2 s2 v2 \<Longrightarrow> P e s (t1 + t2 + 1) s2 (v1 - v2)"
  and "\<And>ea s t s' v si. eval_ewhile_tail_call_while_plus_minus ea s t s' v \<Longrightarrow>
    P e s t s' v \<Longrightarrow> P e s (t + 1) (s(si := v)) v"
  and "\<And>esf s tf sf vf esb tb sb vb. eval_ewhile_tail_call_while_plus_minus (EWPM esf) s tf sf vf \<Longrightarrow>
    P e s tf sf vf \<Longrightarrow> eval_ewhile_tail_call_while_plus_minus (EWPM esb) sf tb sb vb \<Longrightarrow>
    P e sf tb sb vb \<Longrightarrow> P e s (tf + tb) sb vb"
  and "\<And>eic s t1 sc b eit t2 s' v eif. eval_eic eic s t1 sc b \<Longrightarrow> b \<Longrightarrow>
    eval_ewhile_tail_call_while_plus_minus (EWPM eit) sc t2 s' v \<Longrightarrow>
    P e sc t2 s' v \<Longrightarrow> P e s (t1 + 1 + t2) s' v"
  and "\<And>eic s t1 sc b eif t2 s' v eit. eval_eic eic s t1 sc b \<Longrightarrow> \<not>b \<Longrightarrow>
    eval_ewhile_tail_call_while_plus_minus (EWPM eif) sc t2 s' v \<Longrightarrow>
    P e sc t2 s' v \<Longrightarrow> P e s (t1 + 1 + t2) s' v"
  and "\<And>ewc ewpm s1 t1 sc b t2 s2 vew t3 s3 v3. eval_ewc ewc s1 t1 sc b \<Longrightarrow> b \<Longrightarrow>
    eval_ewhile_tail_call_while_plus_minus (EWPM ewpm) sc t2 s2 vew \<Longrightarrow>
    P e sc t2 s2 vew \<Longrightarrow>
    eval_ewhile_tail_call_while_plus_minus (WPMWhile ewc ewpm) s2 t3 s3 v3 \<Longrightarrow>
    P e s2 t3 s3 v3 \<Longrightarrow> P e s1 (t1 + 1 + t2 + t3) s3 v3"
  and "\<And>ewc ew s t sc b. eval_ewc ewc s t sc b \<Longrightarrow> \<not>b \<Longrightarrow> P e s (t + 1) s r_while"
  and "\<And>esf s tf sf vf esb tb sb vb. eval_ewhile_tail_call_while_plus_minus esf s tf sf vf \<Longrightarrow>
    P e s tf sf vf \<Longrightarrow> eval_efgcall_tail_call_while_plus_minus e esb sf tb sb vb \<Longrightarrow>
    P e sf tb sb vb \<Longrightarrow> P e s (tf + tb) sb vb"
  shows "P e s t s' v"
proof -
  from assms(1) obtain efgc efgc' where "eval_efgcall_tail_call_while_plus_minus (TC efgc) efgc' s t s' v" "TC efgc = e"
    unfolding eval_efgcall_tcall_def by (cases e) auto
  then have "P (TC efgc) s t s' v"
  by (induction efgc' s t s' v rule: eval_efgcall_tail_call_while_plus_minus_induct)
    (simp; (rule assms[unfolded eval_ewhile_tail_call_while_plus_minus_def]; auto))+
  with \<open>TC efgc = e\<close> show ?thesis by simp
qed

end

lemma eval_efgcall_tail_call_while_plus_minus_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  and "\<And>e s t s' v. f2 e s t s' v \<longrightarrow> g2 e s t s' v"
  shows "eval_efgcall_tail_call_while_plus_minus f1 f2 r_while (TC efgc) e s t s' v \<longrightarrow>
    eval_efgcall_tail_call_while_plus_minus g1 g2 r_while (TC efgc) e s t s' v"
proof
  assume "eval_efgcall_tail_call_while_plus_minus f1 f2 r_while (TC efgc) e s t s' v"
  from this assms show "eval_efgcall_tail_call_while_plus_minus g1 g2 r_while (TC efgc) e s t s' v"
  proof (induction rule: eval_efgcall_tail_call_while_plus_minus_induct)
    case (FGCWPWhile_true ewc ewpm s1 t1 sc b t2 s2 vew t3 s3 v3)
      with eval_efgcall_tail_call_while_plus_minus_FGCWPMWhile_trueI show ?case
      by (metis FGCWPMWhile_def eval_efgcall_tail_call_while_plus_minus_FGCBaseE)
  qed fast+
qed

lemma eval_etcall_tail_call_while_plus_minus_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  and "\<And>e s t s' v. f2 e s t s' v \<longrightarrow> g2 e s t s' v"
  shows "eval_etcall_tail_call_while_plus_minus f1 f2 r_while e s t s' v \<longrightarrow> eval_etcall_tail_call_while_plus_minus g1 g2 r_while e s t s' v"
  apply (intro impI)
  apply (cases e, hypsubst)
  apply (rule eval_etcall_tail_call_while_plus_minus_TCI)
  apply (rule mp[OF eval_efgcall_tail_call_while_plus_minus_mono])
  by (rule assms)+ fast


context
  fixes eval_eic :: "('t :: {zero,one,plus}, bool, 'si, 'sv :: {minus, plus}, 'eic) eval_time"
  and eval_ewc :: "('t, bool, 'si, 'sv, 'ewc) eval_time"
  and r_while :: "'sv"
  and eval_ewhile_tail_call_while_plus_minus
  defines [simp]: "eval_ewhile_tail_call_while_plus_minus \<equiv>
    eval_exp_while_plus_minus_assign_pure_state eval_eic eval_ewc r_while"
begin

inductive eval_exp_tail_call_while_plus_minus ::
  "('t, 'sv, 'si, 'sv, ('si, 'sv, 'eic, 'ewc) exp_tail_call_while_plus_minus) eval_time"
where
  eval_exp_tail_call_while_plus_minus_ETCWPM[intro]:
    "eval_etcall_tail_call_while_plus_minus eval_eic eval_ewc r_while e s t s' v \<Longrightarrow>
    eval_exp_tail_call_while_plus_minus (ETCWPM e) s t s' v"

inductive_cases eval_exp_tail_call_while_plus_minus_ETCWPME[elim]:
  "eval_exp_tail_call_while_plus_minus (ETCWPM e) s t s' v"

corollary eval_exp_tail_call_while_plus_minus_induct[induct pred : eval_exp_tail_call_while_plus_minus,
  case_names eq_ETCWPM V SI Plus Minus Assign WSeq If_true If_false While_true While_false TSeq]:
  assumes "eval_exp_tail_call_while_plus_minus e s t s' v"
  and "e = ETCWPM etc"
  and "\<And>v s. P e s 0 s v"
  and "\<And>si s. P e s 1 s (s si)"
  and "\<And>epl s t1 s1 v1 epr t2 s2 v2. eval_ewhile_tail_call_while_plus_minus epl s t1 s1 v1 \<Longrightarrow>
    P e s t1 s1 v1 \<Longrightarrow> eval_ewhile_tail_call_while_plus_minus epr s1 t2 s2 v2 \<Longrightarrow>
    P e s1 t2 s2 v2 \<Longrightarrow> P e s (t1 + t2 + 1) s2 (v1 + v2)"
  and "\<And>eml s t1 s1 v1 emr t2 s2 v2. eval_ewhile_tail_call_while_plus_minus eml s t1 s1 v1 \<Longrightarrow>
    P e s t1 s1 v1 \<Longrightarrow> eval_ewhile_tail_call_while_plus_minus emr s1 t2 s2 v2 \<Longrightarrow>
    P e s1 t2 s2 v2 \<Longrightarrow> P e s (t1 + t2 + 1) s2 (v1 - v2)"
  and "\<And>ea s t s' v si. eval_ewhile_tail_call_while_plus_minus ea s t s' v \<Longrightarrow>
    P e s t s' v \<Longrightarrow> P e s (t + 1) (s(si := v)) v"
  and "\<And>esf s tf sf vf esb tb sb vb. eval_ewhile_tail_call_while_plus_minus (EWPM esf) s tf sf vf \<Longrightarrow>
    P e s tf sf vf \<Longrightarrow> eval_ewhile_tail_call_while_plus_minus (EWPM esb) sf tb sb vb \<Longrightarrow>
    P e sf tb sb vb \<Longrightarrow> P e s (tf + tb) sb vb"
  and "\<And>eic s t1 sc b eit t2 s' v eif. eval_eic eic s t1 sc b \<Longrightarrow> b \<Longrightarrow>
    eval_ewhile_tail_call_while_plus_minus (EWPM eit) sc t2 s' v \<Longrightarrow>
    P e sc t2 s' v \<Longrightarrow> P e s (t1 + 1 + t2) s' v"
  and "\<And>eic s t1 sc b eif t2 s' v eit. eval_eic eic s t1 sc b \<Longrightarrow> \<not>b \<Longrightarrow>
    eval_ewhile_tail_call_while_plus_minus (EWPM eif) sc t2 s' v \<Longrightarrow>
    P e sc t2 s' v \<Longrightarrow> P e s (t1 + 1 + t2) s' v"
  and "\<And>ewc ewpm s1 t1 sc b t2 s2 vew t3 s3 v3. eval_ewc ewc s1 t1 sc b \<Longrightarrow> b \<Longrightarrow>
    eval_ewhile_tail_call_while_plus_minus (EWPM ewpm) sc t2 s2 vew \<Longrightarrow>
    P e sc t2 s2 vew \<Longrightarrow>
    eval_ewhile_tail_call_while_plus_minus (WPMWhile ewc ewpm) s2 t3 s3 v3 \<Longrightarrow>
    P e s2 t3 s3 v3 \<Longrightarrow> P e s1 (t1 + 1 + t2 + t3) s3 v3"
  and "\<And>ewc ew s t sc b. eval_ewc ewc s t sc b \<Longrightarrow> \<not>b \<Longrightarrow> P e s (t + 1) s r_while"
  and "\<And>esf s tf sf vf esb tb sb vb. eval_ewhile_tail_call_while_plus_minus esf s tf sf vf \<Longrightarrow>
    P e s tf sf vf \<Longrightarrow> eval_efgcall_tail_call_while_plus_minus eval_eic eval_ewc r_while etc esb sf tb sb vb \<Longrightarrow>
    P e sf tb sb vb \<Longrightarrow> P e s (tf + tb) sb vb"
  shows "P e s t s' v"
  using assms(1)[simplified assms(2)]
  by (elim eval_exp_tail_call_while_plus_minus_ETCWPME eval_etcall_tail_call_while_plus_minus_induct)
  (blast intro: assms(3-)[unfolded eval_ewhile_tail_call_while_plus_minus_def])+

end

lemma eval_exp_tail_call_while_plus_minus_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  and "\<And>e s t s' v. f2 e s t s' v \<longrightarrow> g2 e s t s' v"
  shows "eval_exp_tail_call_while_plus_minus f1 f2 r_while e s t s' v \<longrightarrow> eval_exp_tail_call_while_plus_minus g1 g2 r_while e s t s' v"
  apply (intro impI)
  apply (cases e, hypsubst)
  apply (rule eval_exp_tail_call_while_plus_minus_ETCWPM)
  apply (rule mp[OF eval_etcall_tail_call_while_plus_minus_mono])
  by (rule assms)+ fast


end
