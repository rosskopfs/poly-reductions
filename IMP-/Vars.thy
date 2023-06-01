\<^marker>\<open>creator Fabian Huch\<close>

theory Vars imports Big_StepT
begin

abbreviation
  eq_on :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool"
 ("(_ =/ _/ on _)" [50,0,50] 50) where
"f = g on X == \<forall> x \<in> X. f x = g x"

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
apply(induction a)
apply simp_all
done

lemma aval_eq_if_eq_on_vars[simp]:
  "s\<^sub>1 = s\<^sub>2 on set (vars a) \<Longrightarrow> aval a s\<^sub>1 = aval a s\<^sub>2"
apply(induction a)
apply auto
apply (metis UnCI atomVal_eq_if_eq_on_vars)+
done


fun rvars :: "com \<Rightarrow> vname set" where
"rvars SKIP = {}" |
"rvars (x::=e) = {x}" |
"rvars (c1;;c2) = rvars c1 \<union> rvars c2" |
"rvars (IF b\<noteq>0 THEN c1 ELSE c2) = rvars c1 \<union> rvars c2" |
"rvars (WHILE b\<noteq>0 DO c) = rvars c"

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

lemma rvars_unchanged: "(c,s) \<Rightarrow>\<^bsup>z\<^esup> t \<Longrightarrow> v \<notin> rvars c \<Longrightarrow> s v = t v"
  by (induction c s z t arbitrary:  rule: big_step_t_induct) auto

lemma big_step_subst:
  "\<lbrakk>(c,s) \<Rightarrow>\<^bsup>z\<^esup> t; set (vars c) \<subseteq> S; s = s' o m on S ; inj_on m S; (subst m c,s') \<Rightarrow>\<^bsup>z'\<^esup> t'\<rbrakk>
     \<Longrightarrow> t = t' o m on S \<and> z = z'"
proof (induction c s z t arbitrary: s' z' t' rule: big_step_t_induct)
  case (Assign x a s)
  then show ?case 
    by (auto intro: rev_image_eqI simp: subset_inj_on subsetD dest: subsetD )
       (simp add: inj_on_contraD)
next
  case (Seq c\<^sub>1 s\<^sub>1 x s\<^sub>2 c\<^sub>2 y s\<^sub>3 z s\<^sub>1' s\<^sub>3')
  then show ?case by auto blast+
next
  case (IfTrue s b c1 x t y c2)
  then show ?case by auto
next
  case (IfFalse s b c2 x t y c1)
  then show ?case by auto
next
  case (WhileTrue s1 b c x s2 y s3 z)
  then show ?case by clarsimp (smt (verit) WhileTrue.hyps(1) While_tE)
qed auto

lemma subst_complete:
  "\<lbrakk>(c,s) \<Rightarrow>\<^bsup>z\<^esup> t; set (vars c) \<subseteq> S; s = s' o m on S ; inj_on m S\<rbrakk>
     \<Longrightarrow> \<down>(subst m c,s')"
proof (induction c s z t arbitrary: s' rule: big_step_t_induct)
  case (Seq c\<^sub>1 s\<^sub>1 x s\<^sub>2 c\<^sub>2 y s\<^sub>3 z s\<^sub>1')
  hence "\<down> (subst m c\<^sub>1, s\<^sub>1')" by auto
  then obtain s\<^sub>2' x' where 1: "(subst m c\<^sub>1, s\<^sub>1') \<Rightarrow>\<^bsup>x'\<^esup> s\<^sub>2'" by blast

  with Seq big_step_subst have "s\<^sub>2 = s\<^sub>2' o m on S" "x' = x" by auto blast+
  with Seq have  "\<down>(subst m c\<^sub>2, s\<^sub>2')" by auto
  then obtain s\<^sub>3' y' where 2: "(subst m c\<^sub>2, s\<^sub>2') \<Rightarrow>\<^bsup>y'\<^esup> s\<^sub>3'" by blast

  show ?case
    using "1" "2" by auto
next
  case (IfTrue s b c1 x t y c2)
  then show ?case apply auto using big_step_subst
    by (metis IfTrue.hyps(1) big_step_t.IfTrue)
next
  case (IfFalse s b c2 x t y c1)
  then show ?case apply auto using big_step_subst 
    by (metis big_step_t.IfFalse)
next
  case (WhileTrue s\<^sub>1 b c x s\<^sub>2 y s\<^sub>3 z s\<^sub>1')
  hence "\<down> (subst m c, s\<^sub>1')" by auto
  then obtain s\<^sub>2' x' where 1: "(subst m c, s\<^sub>1') \<Rightarrow>\<^bsup>x'\<^esup> s\<^sub>2'" by blast
  with WhileTrue big_step_subst have "s\<^sub>2 = s\<^sub>2' o m on S" "x' = x"
    apply auto
    apply blast
    apply metis
    done
  with WhileTrue have "\<down> (subst m (While b c), s\<^sub>2')" "s\<^sub>1' (m b) \<noteq> 0" by auto
  then obtain s\<^sub>3' y' where 2: "(subst m (While b c), s\<^sub>2')\<Rightarrow>\<^bsup>y'\<^esup> s\<^sub>3'" by blast
  from 1 2 \<open>s\<^sub>1' (m b) \<noteq> 0\<close> show ?case by auto
qed auto

end
