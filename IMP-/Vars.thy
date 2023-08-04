\<^marker>\<open>creator Fabian Huch\<close>
(* todo merge with existing vars *)
theory Vars imports Big_StepT Restricted_Equality
begin

class vars =
  fixes vars :: "'a \<Rightarrow> vname list"

class subst = vars +
  fixes subst :: "(vname \<Rightarrow> vname) \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes subst_vars[simp]: "set (vars (subst m c)) = m ` set (vars c)"

instantiation atomExp :: vars
begin

fun vars_atomExp :: "atomExp \<Rightarrow> vname list" where
"vars_atomExp (V var) = [var]" |
"vars_atomExp (N _) = []"

instance ..

end

instantiation atomExp :: subst
begin

fun subst_atomExp :: "(vname \<Rightarrow> vname) \<Rightarrow> atomExp \<Rightarrow> atomExp" where
"subst m (V var) = V (m var)" |
"subst m (N n) = N n"

instance
proof (standard, goal_cases)
  case (1 m c)
  then show ?case by (induction c) auto
qed

end

instantiation aexp :: vars
begin

fun vars_aexp :: "aexp \<Rightarrow> vname list" where
"vars (A e) = vars e" |
"vars (Plus e\<^sub>1 e\<^sub>2) = vars e\<^sub>1 @ vars e\<^sub>2" |
"vars (Sub e\<^sub>1 e\<^sub>2) = vars e\<^sub>1 @ vars e\<^sub>2" |
"vars (Parity e) = vars e" |
"vars (RightShift e) = vars e"

instance ..

end

instantiation aexp :: subst
begin

fun subst_aexp :: "(vname \<Rightarrow> vname) \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst m (A e) = A (subst m e)" |
"subst m (Plus e\<^sub>1 e\<^sub>2) = Plus (subst m e\<^sub>1) (subst m e\<^sub>2)" |
"subst m (Sub e\<^sub>1 e\<^sub>2) = Sub (subst m e\<^sub>1) (subst m e\<^sub>2)" |
"subst m (Parity e) = Parity (subst m e)" |
"subst m (RightShift e) = RightShift (subst m e)"

instance
proof (standard, goal_cases)
  case (1 m c)
  then show ?case by (induction c) auto
qed

end


lemma atomVal_eq_if_eq_on_vars[simp]:
  "s\<^sub>1 = s\<^sub>2 on set (vars a) \<Longrightarrow> atomVal a s\<^sub>1 = atomVal a s\<^sub>2"
  by (induction a) auto

lemma aval_eq_if_eq_on_vars [simp]:
  "s\<^sub>1 = s\<^sub>2 on set (vars a) \<Longrightarrow> aval a s\<^sub>1 = aval a s\<^sub>2"
  apply (induction a)
  apply auto 
  using atomVal_eq_if_eq_on_vars eq_on_subset
  apply (metis sup.cobounded1 sup.cobounded2)+
  done

fun lvars :: "com \<Rightarrow> vname set" where
"lvars SKIP = {}" |
"lvars (x::=e) = {x}" |
"lvars (c1;;c2) = lvars c1 \<union> lvars c2" |
"lvars (IF b\<noteq>0 THEN c1 ELSE c2) = lvars c1 \<union> lvars c2" |
"lvars (WHILE b\<noteq>0 DO c) = lvars c"

instantiation com :: vars
begin

fun vars_com :: "com \<Rightarrow> vname list" where
"vars SKIP = []" |
"vars (x::=e) = x#vars e" |
"vars (c1;;c2) = vars c1 @ vars c2" |
"vars (IF b\<noteq>0 THEN c1 ELSE c2) = b # vars c1 @ vars c2" |
"vars (WHILE b\<noteq>0 DO c) = b#vars c"

instance ..

end

instantiation com :: subst
begin

fun subst_com :: "(vname \<Rightarrow> vname) \<Rightarrow> com \<Rightarrow> com" where
"subst m SKIP = SKIP" |
"subst m (x::=e) = (m x) ::= subst m e" |
"subst m (c\<^sub>1;;c\<^sub>2) = subst m c\<^sub>1;; subst m c\<^sub>2" |
"subst m (IF b\<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2) = IF m b\<noteq>0 THEN subst m c\<^sub>1 ELSE subst m c\<^sub>2" |
"subst m (WHILE b\<noteq>0 DO c) = WHILE m b\<noteq>0 DO subst m c"

instance
proof (standard, goal_cases)
  case (1 m c)
  then show ?case by (induction c) auto
qed

end

lemma atomVal_subst[simp]: "inj_on m (set (vars a)) \<Longrightarrow> atomVal (subst m a) s = (atomVal a (s o m))"
  by (induction a) auto

lemma aval_subst[simp]: "inj_on m (set (vars a)) \<Longrightarrow> aval (subst m a) s = aval a (s o m)"
  by (induction a) (auto simp add: inj_on_Un)

lemma var_unchanged: "(c,s) \<Rightarrow>\<^bsup>z\<^esup> t \<Longrightarrow> v \<notin> set (vars c) \<Longrightarrow> s v = t v"
  by (induction c s z t arbitrary:  rule: big_step_t_induct) auto

lemma lvars_unchanged: "(c,s) \<Rightarrow>\<^bsup>z\<^esup> t \<Longrightarrow> v \<notin> lvars c \<Longrightarrow> s v = t v"
  by (induction c s z t arbitrary:  rule: big_step_t_induct) auto

lemma subst_sound:
  "\<lbrakk> (c,s) \<Rightarrow>\<^bsup>z\<^esup> t; s = s' o m on S; set (vars c) \<subseteq> S; inj_on m S \<rbrakk>
    \<Longrightarrow> \<exists>t'. (subst m c,s') \<Rightarrow>\<^bsup>z\<^esup> t' \<and> t = t' o m on S"
proof (induction c s z t arbitrary: s' rule: big_step_t_induct)
  case Assign then show ?case unfolding eq_on_def
    by (auto simp: subset_inj_on subsetD inj_on_contraD aval_eq_if_eq_on_vars[unfolded eq_on_def])
next
  case (WhileTrue s\<^sub>1 b c x s\<^sub>2 y s\<^sub>3 z s\<^sub>1')
  then obtain s\<^sub>2' where 1: "(subst m c, s\<^sub>1') \<Rightarrow>\<^bsup> x \<^esup> s\<^sub>2'" "s\<^sub>2 = s\<^sub>2' \<circ> m on S" unfolding eq_on_def by force
  with WhileTrue obtain s\<^sub>3' where 2: "(subst m (WHILE b\<noteq>0 DO c), s\<^sub>2') \<Rightarrow>\<^bsup> y \<^esup> s\<^sub>3'" "s\<^sub>3 = s\<^sub>3' \<circ> m on S" unfolding eq_on_def by force
  have "(WHILE m b\<noteq>0 DO (subst m c), s\<^sub>1') \<Rightarrow>\<^bsup> z \<^esup> s\<^sub>3'"
    apply (rule big_step_t.WhileTrue)
    using 1 2 WhileTrue by auto
  with 2 show ?case unfolding eq_on_def by auto
qed (auto | fastforce)+

lemma subst_complete:
  "\<lbrakk> (subst m c,s') \<Rightarrow>\<^bsup>z\<^esup> t'; s = s' o m on S; set (vars c) \<subseteq> S; inj_on m S \<rbrakk>
    \<Longrightarrow> \<exists>t. (c,s) \<Rightarrow>\<^bsup>z\<^esup> t \<and> t = t' o m on S"
proof (induction "subst m c" s' z t' arbitrary: c s rule: big_step_t_induct)
  case (Skip s c s')
  then show ?case by (cases c) auto
next
  case (Assign x a  s' c s)
  then obtain x' a' where defs: "c = x' ::= a'" "x = m x'" "a = subst m a'" by (cases c) auto
  moreover have "(x' ::= a',s) \<Rightarrow>\<^bsup>Suc (Suc 0)\<^esup> s(x' := aval a' s)" by auto
  moreover have "s(x' := aval a' s) = s'(x := aval a s') \<circ> m on S"
    by (smt (verit, ccfv_SIG) Assign.hyps Assign Assign_tE calculation(1) calculation(4) subst_sound)
  ultimately show ?case by blast
next
  case (Seq c\<^sub>1 s\<^sub>1 x s\<^sub>2 c\<^sub>2 y s\<^sub>3 z c s\<^sub>1') then show ?case by (cases c) (auto, fastforce)
next
  case (IfTrue s b c\<^sub>1 x t z c\<^sub>2 c s') then show ?case by (cases c) (auto, fastforce)
next
  case (IfFalse s b c\<^sub>2 x t z c\<^sub>1 c s') then show ?case by (cases c) (auto, fastforce)
next
  case (WhileFalse s b c\<^sub>1 c s') then show ?case by (cases c) (auto, fastforce)
next
  case (WhileTrue s\<^sub>1 b c\<^sub>1 x s\<^sub>2 y s\<^sub>3 z c s\<^sub>1')
  then obtain c\<^sub>1' b' where [simp]: "c = WHILE b'\<noteq>0 DO c\<^sub>1'" "m b' = b" "c\<^sub>1 = subst m c\<^sub>1'" by (cases c) auto
  with WhileTrue have "set (vars c\<^sub>1') \<subseteq> S" by auto
  with WhileTrue.hyps(3)[OF _ WhileTrue.prems(1) this WhileTrue.prems(3)] obtain s\<^sub>2' where
    1: "(c\<^sub>1', s\<^sub>1') \<Rightarrow>\<^bsup> x \<^esup> s\<^sub>2'" "s\<^sub>2' = s\<^sub>2 \<circ> m on S" by auto
  with WhileTrue.hyps(5)[OF _ this(2) WhileTrue.prems(2) WhileTrue.prems(3)] obtain s\<^sub>3' where
    2: "(WHILE b'\<noteq>0 DO c\<^sub>1', s\<^sub>2') \<Rightarrow>\<^bsup> y \<^esup> s\<^sub>3'" "s\<^sub>3' = s\<^sub>3 \<circ> m on S" by auto
  from 1 2 WhileTrue.hyps(1,6) WhileTrue.prems(1,2) have
    "(WHILE b'\<noteq>0 DO c\<^sub>1', s\<^sub>1') \<Rightarrow>\<^bsup> z \<^esup> s\<^sub>3'" "s\<^sub>3' = s\<^sub>3 \<circ> m on S" unfolding eq_on_def by auto
  thus ?case by auto
qed

lemma noninterference: 
  "(c,s) \<Rightarrow>\<^bsup> x \<^esup> t \<Longrightarrow> set (vars c) \<subseteq> S \<Longrightarrow> s = s' on S \<Longrightarrow> \<exists>t'. (c,s') \<Rightarrow>\<^bsup> x \<^esup> t' \<and> t = t' on S"
proof (induction c s x t arbitrary: s' rule: big_step_t_induct)
  case (Assign x a s)
  then show ?case 
    using aval_eq_if_eq_on_vars big_step_t.Assign eq_on_def eq_on_subset fun_upd_apply set_subset_Cons vars_com.simps(2) by fastforce
next
  case (WhileTrue s1 b c x s2 y s3 z)
  then show ?case apply auto
    by (metis (mono_tags, lifting) WhileTrue.hyps(1) WhileTrue.hyps(4) big_step_t.WhileTrue eq_onE)
qed fastforce+


end
