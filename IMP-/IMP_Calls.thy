\<^marker>\<open>creator Fabian Huch\<close>

theory IMP_Calls imports Vars begin

text \<open>IMP with calls to IMP- programs (explicitly stored).\<close>
datatype
  com' = SKIP'
      | Assign' vname aexp
      | Seq'    com'  com'
      | If'     vname com' com'
      | While'  vname com'
      | Call'   com vname

bundle com'_syntax begin
notation Assign' ("_ ::= _" [1000, 61] 61) and
         Seq' ("_;;/ _"  [60, 61] 60) and
         If' ("(IF _/\<noteq>0 THEN _/ ELSE _)"  [0, 0, 61] 61) and
         While' ("(WHILE _/\<noteq>0 DO _)"  [0, 61] 61) and
         Call' ("CALL _ RETURN _") end

bundle no_com'_syntax begin
no_notation Assign' ("_ ::= _" [1000, 61] 61) and
            Seq' ("_;;/ _"  [60, 61] 60) and
            If' ("(IF _/\<noteq>0 THEN _/ ELSE _)"  [0, 0, 61] 61) and
            While' ("(WHILE _/\<noteq>0 DO _)"  [0, 61] 61) and
            Call' ("CALL _ RETURN _") end

unbundle no_com_syntax
unbundle com'_syntax

inductive
  big_step_t' :: "com' \<times> state \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool"  ("_ \<Rightarrow>''\<^bsup> _ \<^esup> _" 55)
where
Skip: "(SKIP',s) \<Rightarrow>'\<^bsup> Suc (0::nat) \<^esup> s"|
Assign: "(x ::= a,s) \<Rightarrow>'\<^bsup> Suc (Suc 0) \<^esup> s(x := aval a s)" |
Seq: "\<lbrakk> (c1,s1) \<Rightarrow>'\<^bsup> x \<^esup> s2;  (c2,s2) \<Rightarrow>'\<^bsup> y \<^esup> s3 ; z=x+y \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow>'\<^bsup> z \<^esup> s3" |
IfTrue: "\<lbrakk> s b \<noteq> 0;  (c1,s) \<Rightarrow>'\<^bsup> x \<^esup> t; y=x+1 \<rbrakk> \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>'\<^bsup> y \<^esup> t" |
IfFalse: "\<lbrakk> s b = 0; (c2,s) \<Rightarrow>'\<^bsup> x \<^esup> t; y=x+1  \<rbrakk> \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>'\<^bsup> y \<^esup> t" |
WhileFalse: "\<lbrakk> s b = 0 \<rbrakk> \<Longrightarrow> (WHILE b \<noteq>0 DO c,s) \<Rightarrow>'\<^bsup> Suc (Suc 0) \<^esup> s" |
WhileTrue: "\<lbrakk> s1 b \<noteq> 0;  (c,s1) \<Rightarrow>'\<^bsup> x \<^esup> s2;  (WHILE b \<noteq>0 DO c, s2) \<Rightarrow>'\<^bsup> y \<^esup> s3; 1+x+y=z  \<rbrakk> 
    \<Longrightarrow> (WHILE b \<noteq>0 DO c, s1) \<Rightarrow>'\<^bsup> z \<^esup> s3" |
\<comment> \<open>The only change: The called program is executed on a state that agrees on all the variables in
    the subprogram. In the caller, only the result variable is affected.\<close>
Call: "\<lbrakk> (c,s') \<Rightarrow>\<^bsup> z \<^esup> t; s' = s on set (r#vars c) \<rbrakk>
    \<Longrightarrow> (CALL c RETURN r,s) \<Rightarrow>'\<^bsup> z \<^esup> (s(r:=t r))"

text \<open>For compilation to IMP-, skip to final proof.\<close>

code_pred big_step_t' .

declare big_step_t'.intros [intro]

lemmas big_step_t'_induct = big_step_t'.induct[split_format(complete)]

inductive_cases Skip'_tE[elim!]: "(SKIP',s) \<Rightarrow>'\<^bsup> x \<^esup> t"
inductive_cases Assign'_tE[elim!]: "(x ::= a,s) \<Rightarrow>'\<^bsup> p \<^esup> t"
inductive_cases Seq'_tE[elim!]: "(c1;;c2,s1) \<Rightarrow>'\<^bsup> p \<^esup> s3"
inductive_cases If'_tE[elim!]: "(IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>'\<^bsup> x \<^esup> t"
inductive_cases Call'_tE[elim!]: " (CALL c RETURN v,s) \<Rightarrow>'\<^bsup> z \<^esup> t"
inductive_cases While'_tE[elim]: "(WHILE b \<noteq>0 DO c,s) \<Rightarrow>'\<^bsup> x \<^esup> t"
lemma Seq'': "\<lbrakk> (c1,s1) \<Rightarrow>'\<^bsup> x \<^esup> s2;  (c2,s2) \<Rightarrow>'\<^bsup> y \<^esup> s3  \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow>'\<^bsup> x + y \<^esup> s3"
  by auto

instantiation com' :: vars
begin

fun vars_com' :: "com' \<Rightarrow> vname list" where
"vars SKIP' = []" |
"vars (x::=e) = x#vars e" |
"vars (c1;;c2) = vars c1 @ vars c2" |
"vars (IF b\<noteq>0 THEN c1 ELSE c2) = b # vars c1 @ vars c2" |
"vars (WHILE b\<noteq>0 DO c) = b#vars c" |
"vars (CALL c RETURN r) = r#vars c"

instance ..

end

definition fresh :: "vname list \<Rightarrow> vname \<Rightarrow> vname" where 
  "fresh S v = CHR ''.'' # concat S @ v"

lemma fresh_inj: "inj_on (fresh S) (set S)"
  by (induction S) (auto simp: inj_on_def fresh_def)

lemma fresh_len[simp]: "length (fresh S v) = Suc (length v + (\<Sum>xs\<leftarrow>S. length xs))"
  by (induction S) (auto simp: fresh_def)

lemma fresh[simp]: "fresh S v \<notin> set S"
proof
  have "\<forall>xs \<in> set S. length (fresh S v) > length xs"
    by (induction S) auto
  moreover assume "fresh S v \<in> set S"
  ultimately show False by blast
qed

fun size\<^sub>c :: "com' \<Rightarrow> nat" where
  "size\<^sub>c (c\<^sub>1;;c\<^sub>2) = size\<^sub>c c\<^sub>1 + size\<^sub>c c\<^sub>2" |
  "size\<^sub>c (IF b\<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2) = size\<^sub>c c\<^sub>1 + size\<^sub>c c\<^sub>2" |
  "size\<^sub>c (WHILE b\<noteq>0 DO c) = size\<^sub>c c" |
  "size\<^sub>c (CALL c RETURN r) = 2 * length (vars c) + 5" |
  "size\<^sub>c _ = 0"

unbundle no_com'_syntax
unbundle com_syntax

fun ssubst where
"ssubst m [] = SKIP" |
"ssubst m (v#vs) = (m v) ::= A (V v) ;; ssubst m vs"

lemma vars_ssubst[simp]: "set (vars (ssubst m vs)) = set vs \<union> m ` set vs"
  by (induction vs) auto

lemma rvars_ssubst[simp]: "rvars (ssubst m vs) = m ` set vs"
  by (induction vs) auto

lemma ssubst_unchanged: "(ssubst m vs,s) \<Rightarrow>\<^bsup>z\<^esup> t \<Longrightarrow> (\<forall>v\<in>set vs. m v \<notin> set vs) \<Longrightarrow> s = t on set vs"
  apply auto
  by (metis (mono_tags, opaque_lifting) image_iff rvars_ssubst rvars_unchanged)
  
lemma ssubst_sound:
  "\<lbrakk>(ssubst m vs,s) \<Rightarrow>\<^bsup>z\<^esup> t; inj_on m (set vs); (\<forall>v\<in>set vs. m v \<notin> set vs)\<rbrakk> \<Longrightarrow> 
s = t o m on set vs \<and> z = Suc (2 * length vs)"
proof (induction vs arbitrary: z s t )
  case (Cons v vs)
  hence "((m v) ::= A (V v) ;; ssubst m vs, s) \<Rightarrow>\<^bsup> z \<^esup> t" by simp
  then obtain z' where *: "Suc (Suc z') = z" and **: "(ssubst m vs, s(m v := s v)) \<Rightarrow>\<^bsup> z' \<^esup> t" by auto
  from Cons have ***: "\<forall>v\<in>set vs. m v \<notin> set vs" by simp
  from Cons have ****: "inj_on m (set vs)" by simp
  from Cons.IH[OF ** **** ***] have step: "s(m v := s v) = t \<circ> m on set vs" and z: "z' = Suc (2 * length vs)" by auto
  hence "s(m v := s v) = t \<circ> m on set (v#vs)"
  proof (cases "v\<in>set vs")
    case True
    then show ?thesis
      using local.step by auto
  next
    case False
    with Cons.prems(3) have a: "v \<notin> set (vars (ssubst m vs))" by (induction vs) auto
    hence " v \<notin> m ` set vs" by fastforce
    with False have "m v \<notin> m ` set vs" using \<open>\<forall>va\<in>set (v # vs). m va \<notin> set (v # vs)\<close>
      using Cons.prems(2) by force
    with a have "m v \<notin> set (vars (ssubst m vs))" apply auto 
      using Cons.prems(3) by force
    hence "(s(m v := s v)) (m v) = t (m v)" using var_unchanged apply auto
      using "**" by fastforce
    then show ?thesis using step by auto
  qed
  from z have "z = Suc (2 * length (v # vs))"
    using "*" by force
  then show ?case
    by (metis Cons.prems(3) \<open>s(m v := s v) = t \<circ> m on set (v # vs)\<close> fun_upd_other list.set_intros(1))
qed auto

lemma ssubst_complete:
  "\<down>(ssubst m vs,s)"
  by (induction vs arbitrary: s) fastforce+

corollary subst_sound:
  "\<lbrakk>(c,s) \<Rightarrow>\<^bsup>z\<^esup> t; s = s' o m on set (vars c) ; inj_on m (set (vars c)); (subst m c,s') \<Rightarrow>\<^bsup>z'\<^esup> t'\<rbrakk>
     \<Longrightarrow> t = t' o m on set (vars c) \<and> z = z'"
  using big_step_subst by blast

definition [simp]: "transfer m c = ssubst m (vars c);;subst m c"

lemma set_transfer[simp]: "set (vars (transfer m c)) = set (vars c) \<union> m ` set (vars c)"
  unfolding transfer_def by auto


lemma transfer_sound:
  assumes c_sem: "(c,s) \<Rightarrow>\<^bsup>z\<^esup> t"
      and s: "s = s' on set (vars c)"
      and transfer_sem: "(transfer m c,s')\<Rightarrow>\<^bsup>z'\<^esup> t'"
      and inj: "inj_on m (set (vars c))"
      and disj: "(\<forall>v\<in>set (vars c). m v \<notin> set (vars c))"
    shows "t = t' o m on set (vars c) \<and> Suc (2 * length (vars c)) + z = z'"
      and "s' = t' on UNIV - m ` set (vars c)"
proof -
  from transfer_sem obtain s'' x y where ssubst_sem: "(ssubst m (vars c),s')\<Rightarrow>\<^bsup>x\<^esup> s''" and subst_sem: "(subst m c,s'') \<Rightarrow>\<^bsup>y\<^esup> t'" "x + y = z'"
    unfolding transfer_def by blast
  show "t = t' o m on set (vars c) \<and> Suc (2 * length (vars c)) + z = z'" using ssubst_sound[OF ssubst_sem inj disj] subst_sound[OF c_sem _ inj subst_sem(1)]
    using s subst_sem(2) by force
  have "s' = s'' on UNIV - m ` set (vars c)"
    using disj ssubst_sem ssubst_unchanged
    by (simp add: rvars_unchanged)
  moreover have "s'' = t'  on UNIV - m ` set (vars c)" using var_unchanged apply auto
    using subst_sem(1) by auto
  ultimately show "s' = t' on UNIV - m ` set (vars c)" by auto
qed

lemma transfer_complete:
  assumes c_sem: "(c,s) \<Rightarrow>\<^bsup>z\<^esup> t"
      and s: "s = s' on set (vars c)"
      and inj: "inj_on m (set (vars c))"
      and disj: "(\<forall>v\<in>set (vars c). m v \<notin> set (vars c))"
    shows "\<down>(transfer m c,s')"
proof -
  from ssubst_complete have "\<down>(ssubst m (vars c), s')" by simp
  then obtain s'' x where ssubst_sem: "(ssubst m (vars c),s')\<Rightarrow>\<^bsup>x\<^esup> s''" by auto
  from ssubst_sound have "s' = s'' \<circ> m on set (vars c)" using assms ssubst_sem by blast
  with c_sem have "\<down>(subst m c,s'')" using subst_complete
    by (metis inj order_refl s)
  with ssubst_sem show ?thesis
    unfolding transfer_def by auto
qed

context notes Let_def[simp] begin
definition [simp]: "inline1 S c r = (let m = fresh S in (m r) ::= A (V r);;transfer m c;;r ::= A (V (m r)))"

lemma inline1_vars_c[simp]: "set (vars c) \<subseteq> set (vars (inline1 S c r))"
  unfolding inline1_def by auto

lemma inline1_vars_r[simp]: "r \<in> set (vars (inline1 S c r))"
  unfolding inline1_def by auto

lemma inline1_sound:
  assumes c_sem: "(c,s) \<Rightarrow>\<^bsup>z\<^esup> t"
      and s: "s = s' on set (r#vars c)"
      and S: "set (r#vars c) \<subseteq> set S"
      and inline1_sem: "(inline1 S c r,s') \<Rightarrow>\<^bsup>zr\<^esup> tr"
    shows "t r = tr r" and "s' = tr on set S - {r}" and "2 * length (vars c) + z + 5 = zr"
proof -
  let ?m = "fresh S"
  have inj: "inj_on ?m (set (vars c))"
    using S fresh_inj inj_on_subset by auto
  have disj: "(\<forall>v\<in>set (vars c). ?m v \<notin> set (vars c))"
    using S fresh by auto
  
  from inline1_sem obtain s\<^sub>1' z\<^sub>1' z\<^sub>2' where def1: 
    "((?m r) ::= A (V r),s') \<Rightarrow>\<^bsup>z\<^sub>1'\<^esup> s\<^sub>1'"
    "(transfer ?m c;;r ::= A (V (?m r)),s\<^sub>1')\<Rightarrow>\<^bsup>z\<^sub>2'\<^esup> tr"
    "z\<^sub>1' + z\<^sub>2' = zr"
    unfolding inline1_def by fastforce
  from def1(2) obtain s\<^sub>2' z' z\<^sub>3' where def2:
    "(transfer ?m c,s\<^sub>1')\<Rightarrow>\<^bsup>z'\<^esup> s\<^sub>2'"
    "(r ::= A (V (?m r)),s\<^sub>2')\<Rightarrow>\<^bsup>z\<^sub>3'\<^esup> tr"
    "z' + z\<^sub>3' = z\<^sub>2'"
    by fastforce    

  from def1(1) have "z\<^sub>1' = Suc (Suc 0)" and s\<^sub>1': "s\<^sub>1' = s'(?m r := s' r)" by auto
  from s have s': "s=s\<^sub>1' on set (vars c)"
    using S s\<^sub>1' by auto
  from def2(1) have **:"t = s\<^sub>2' o ?m on set (vars c) \<and> Suc (2 * length (vars c)) + z = z'" 
    and ***: "s\<^sub>1' = s\<^sub>2' on UNIV - ?m ` set (vars c)"
    using transfer_sound[OF c_sem s' _ inj disj] by auto

  from def2 have "z\<^sub>3' = Suc (Suc 0)" and tr: "tr = s\<^sub>2'(r := s\<^sub>2'(?m r))" by auto

  have "zr = Suc (Suc 0) + Suc (2 * length (vars c)) + z + Suc (Suc 0)"
    using \<open>z\<^sub>1' = Suc (Suc 0)\<close> \<open>z\<^sub>3' = Suc (Suc 0)\<close> def1(3) def2(3) ** by auto
  from this[symmetric] show "2 * length (vars c) + z + 5 = zr" by linarith

  from def2 have "tr r = (s\<^sub>2' o ?m) r" by auto
  show "t r = tr r"
  proof (cases "r \<in> set (vars c)")
    case True
    then show ?thesis
      by (simp add: "**" \<open>tr r = (s\<^sub>2' \<circ> fresh S) r\<close>)
  next
    case False
    hence "?m r \<notin> set (vars (transfer ?m c))"
      by (smt (verit, best) S Un_iff fresh fresh_inj inj_on_image_mem_iff list.set_intros(1) set_subset_Cons set_transfer subsetD subset_inj_on)
    
    with def2(1) have "s\<^sub>1' (?m r) = s\<^sub>2' (?m r)"
      using var_unchanged by blast

    then show ?thesis
      by (metis False c_sem fun_upd_same list.set_intros(1) s s\<^sub>1' tr var_unchanged)
  qed

  from *** have "s\<^sub>1' = s\<^sub>2' on set S" by auto

  show "s' = tr on set S - {r}"
    by (metis DiffE \<open>s\<^sub>1' = s\<^sub>2' on set S\<close> fresh fun_upd_other s\<^sub>1' singleton_iff tr)
qed

lemma inline1_complete:
    assumes c_sem: "(c,s) \<Rightarrow>\<^bsup>z\<^esup> t"
      and s: "s = s' on set (r#vars c)"
      and S: "set (r#vars c) \<subseteq> set S"
    shows "\<down>(inline1 S c r,s')"
proof -
  let ?m = "fresh S"
  have inj: "inj_on ?m (set (vars c))"
    using S fresh_inj inj_on_subset by auto
  have disj: "(\<forall>v\<in>set (vars c). ?m v \<notin> set (vars c))"
    using S fresh by auto

  have 1: "((?m r) ::= A (V r),s') \<Rightarrow>\<^bsup>Suc (Suc 0)\<^esup> s'((?m r) := s' r)"
    using big_step_t.Assign[of "?m r" "A (V r)" s'] by auto

  have s': "s = s'((?m r) := s' r) on set (vars c)"
    using S s by auto

  have 2: "\<down> (transfer (fresh S) c, s'(fresh S r := s' r))"
    using transfer_complete[OF c_sem s' inj disj] .

  hence 3: "\<down> (transfer (fresh S) c;;r ::= A (V (?m r)), s'(fresh S r := s' r))" by auto
  then obtain z t where "(transfer (fresh S) c;;r ::= A (V (?m r)), s'(fresh S r := s' r))\<Rightarrow>\<^bsup>z\<^esup> t" by blast
  
  with 1 s' have "((?m r) ::= A (V r);;transfer ?m c;;r ::= A (V (?m r)),s')\<Rightarrow>\<^bsup>Suc (Suc 0) + z\<^esup> t"
    by (smt (verit, best) Seq_tE add.assoc compose_programs_2)

  then show ?thesis unfolding inline1_def by fastforce
qed

fun inline_S :: "vname list \<Rightarrow> com' \<Rightarrow> com" where
  "inline_S S SKIP' = SKIP" |
  "inline_S S (Assign' x a) = (x::=a)" |
  "inline_S S (Seq' c\<^sub>1' c\<^sub>2') = (let
    c\<^sub>1 = inline_S S c\<^sub>1';
    c\<^sub>2 = inline_S (S @ vars c\<^sub>1) c\<^sub>2'
  in c\<^sub>1;;c\<^sub>2)" |
  "inline_S S (If' b c\<^sub>1' c\<^sub>2') = (let
    c\<^sub>1 = inline_S S c\<^sub>1';
    c\<^sub>2 = inline_S S c\<^sub>2'
  in IF b\<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2)" |
  "inline_S S (While' b c') = WHILE b\<noteq>0 DO inline_S S c'" |  
  "inline_S S (Call' c r) = inline1 S c r"

lemma vars_inline_S[simp]: "set (vars c) \<subseteq> set (vars (inline_S S c))"
  by (induction c arbitrary: S) auto

lemma inline_S_sound: 
  "\<lbrakk> (c',s') \<Rightarrow>'\<^bsup>z'\<^esup> t'; s'= s on T; set (vars c') \<subseteq> set S; set (vars c') \<subseteq> T; T \<subseteq> set S; (inline_S S c',s)\<Rightarrow>\<^bsup>z\<^esup> t \<rbrakk>
    \<Longrightarrow> t = t' on T \<and> z \<le> z' + (z' + 1) * size\<^sub>c c'"
proof(induction c' s' z' t' arbitrary: S s z t rule: big_step_t'_induct)
  case (Assign x a s)
  then show ?case by (auto simp: subset_iff)
next
  case (Seq c\<^sub>1' s\<^sub>1' x' s\<^sub>2' c\<^sub>2' y' s\<^sub>3' z' S s\<^sub>1 z t)
  let ?S = "(S @ vars (inline_S S c\<^sub>1'))"
  from Seq obtain s\<^sub>2 x s\<^sub>3 y where "(inline_S S c\<^sub>1' ,s\<^sub>1) \<Rightarrow>\<^bsup>x\<^esup> s\<^sub>2" and 2:"(inline_S ?S c\<^sub>2' ,s\<^sub>2) \<Rightarrow>\<^bsup>y\<^esup> s\<^sub>3" and "x + y = z" by auto
  with Seq have s2: "s\<^sub>2' = s\<^sub>2 on T" and t2: "x \<le> x' + (x' + 1) * size\<^sub>c c\<^sub>1'" apply auto by fastforce
  have "set (vars c\<^sub>2') \<subseteq> set (S @ vars (inline_S S c\<^sub>1'))"
    using Seq.prems(2) by force
  with Seq.IH(2)[OF s2 _ _ _ 2]  have "s\<^sub>3 = s\<^sub>3' on T" and t3: " y \<le> y' + (y' + 1) * size\<^sub>c c\<^sub>2'" apply auto
    using Seq.prems(3) \<open>set (vars c\<^sub>2') \<subseteq> set (S @ vars (inline_S S c\<^sub>1'))\<close>  apply auto
    using Seq.prems(4) apply blast+ done
  have *: " t = s\<^sub>3' on T"
    by (smt (verit, ccfv_SIG) "2" Seq.prems(5) \<open>(inline_S S c\<^sub>1', s\<^sub>1) \<Rightarrow>\<^bsup> x \<^esup> s\<^sub>2\<close> \<open>s\<^sub>3 = s\<^sub>3' on T\<close> big_step_t.Seq big_step_t_determ2 inline_S.simps(3))

  from Seq.hyps have "x' + y' = z'" by simp
  with \<open>x + y = z\<close> t2 t3
  have **: "z \<le> z' + (z' + 1) * (size\<^sub>c c\<^sub>1' + size\<^sub>c c\<^sub>2')" by (auto simp: algebra_simps)

  from * ** show ?case by simp
next
  case (IfTrue s' b c\<^sub>1' x' t' y' c\<^sub>2' S s y t) 
  then obtain x where step: "(inline_S S c\<^sub>1' ,s) \<Rightarrow>\<^bsup>x\<^esup> t" and y_def: "1 + x = y" by auto
  from IfTrue have prems: "set (vars c\<^sub>1') \<subseteq> set S" "set (vars c\<^sub>1') \<subseteq> T" by auto
  from IfTrue.IH[OF IfTrue.prems(1) prems IfTrue.prems(4) step] have "t = t' on T \<and> x \<le> x' + (x' + 1) * size\<^sub>c c\<^sub>1'" .
  with y_def IfTrue.hyps(3) show ?case by (auto simp: algebra_simps)
next
  case (IfFalse s' b c\<^sub>2' x' t' y' c\<^sub>1' S s y t) 
  then obtain x where step: "(inline_S S c\<^sub>2' ,s) \<Rightarrow>\<^bsup>x\<^esup> t" and y_def: "1 + x = y" by auto
  from IfFalse have prems: "set (vars c\<^sub>2') \<subseteq> set S" "set (vars c\<^sub>2') \<subseteq> T" by auto
  from IfFalse.IH[OF IfFalse.prems(1) prems IfFalse.prems(4) step] have "t = t' on T \<and> x \<le> x' + (x' + 1) * size\<^sub>c c\<^sub>2'" .
  with y_def IfFalse.hyps(3) show ?case by (auto simp: algebra_simps)
next
  case (WhileTrue s\<^sub>1' b c' x' s\<^sub>2' y' s\<^sub>3' z' S s\<^sub>1 z s\<^sub>3) thm WhileTrue.prems
  then obtain x y s\<^sub>2 where step: 
    "(inline_S S c',s\<^sub>1)\<Rightarrow>\<^bsup>x\<^esup> s\<^sub>2" 
    "(inline_S S (While' b c'), s\<^sub>2) \<Rightarrow>\<^bsup> y \<^esup> s\<^sub>3"
  and z_def: "1 + x + y = z" by auto
  from WhileTrue have prems: 
    "set (vars c') \<subseteq> set S" "set (vars c') \<subseteq> T"
    "set (vars (While' b c')) \<subseteq> set S" "set (vars (While' b c')) \<subseteq> T" by auto
  from WhileTrue.IH(1)[OF WhileTrue.prems(1) prems(1,2) WhileTrue.prems(4) step(1)]
  have "s\<^sub>2' = s\<^sub>2 on T" "x \<le> x' + (x' + 1) * size\<^sub>c c'" by auto
  moreover from WhileTrue.IH(2)[OF this(1) prems(3,4) WhileTrue.prems(4) step(2)]
  have "s\<^sub>3 = s\<^sub>3' on T" " y \<le> y' + (y' + 1) * size\<^sub>c (While' b c')" by auto
  ultimately show ?case using z_def WhileTrue.hyps(4) by (auto simp: algebra_simps)
next
  case (Call c s z t s' r S s'' z' t')

  from Call have prems: "s = s'' on set (r # vars c)" "set (r # vars c) \<subseteq> set S" "(inline1 S c r, s'') \<Rightarrow>\<^bsup> z' \<^esup> t'" by auto

  have tr: "t r = t' r" and t: "2 * length (vars c) + z + 5 = z'" using inline1_sound[OF \<open>(c, s) \<Rightarrow>\<^bsup> z \<^esup> t\<close> prems] by auto

  from Call.hyps(1) prems(3) have "t' = s''(r := t' r) on T"
    by (smt (verit, ccfv_SIG) Call.prems(4) DiffI empty_iff fun_upd_apply inline1_sound(2) insert_iff prems(1) prems(2) subsetD)

  with tr Call have "t' = s'(r := t r) on T" by fastforce
  with t show ?case by simp
qed auto

lemma inline_S_complete:
  "\<lbrakk> (c',s') \<Rightarrow>'\<^bsup>z'\<^esup> t'; s'= s on T; set (vars c') \<subseteq> set S; set (vars c') \<subseteq> T; T \<subseteq> set S \<rbrakk>
    \<Longrightarrow>  \<down> (inline_S S c',s)"
proof(induction c' s' z' t' arbitrary: S s rule: big_step_t'_induct)
  case (Seq c\<^sub>1' s\<^sub>1' x' s\<^sub>2' c\<^sub>2' y' s\<^sub>3' z' S s\<^sub>1)
  hence "\<down> (inline_S S c\<^sub>1', s\<^sub>1)" by auto
  then obtain x s\<^sub>2 where 1: "(inline_S S c\<^sub>1', s\<^sub>1) \<Rightarrow>\<^bsup>x\<^esup> s\<^sub>2" by auto
  let ?S = "(S @ vars (inline_S S c\<^sub>1'))"
  from Seq have "s\<^sub>2' = s\<^sub>2 on T" "set (vars c\<^sub>2') \<subseteq> set ?S" "set (vars c\<^sub>2') \<subseteq> T" "T \<subseteq> set ?S"
    using inline_S_sound[OF \<open> (c\<^sub>1', s\<^sub>1') \<Rightarrow>'\<^bsup> x' \<^esup> s\<^sub>2'\<close> _ _ _ _ 1] by auto
  with Seq.IH(2) have "\<down> (inline_S ?S c\<^sub>2', s\<^sub>2)" by auto
  with 1 show ?case by auto 
next
  case (IfTrue s b c1 x t y c2)
  then show ?case apply auto
    by (metis IfTrue.hyps(1) big_step_t.IfTrue)
next
  case (IfFalse s b c2 x t y c1)
  then show ?case apply auto
    by (metis big_step_t.IfFalse)
next
  case (WhileTrue s\<^sub>1' b c' x' s\<^sub>2' y' s\<^sub>3' z' S s\<^sub>1)
  hence "\<down> (inline_S S c',s\<^sub>1)" by auto
  then obtain x s\<^sub>2  where 1: "(inline_S S c', s\<^sub>1) \<Rightarrow>\<^bsup>x\<^esup> s\<^sub>2" by auto
  from WhileTrue have "s\<^sub>2' = s\<^sub>2 on T" "set (vars (While' b c')) \<subseteq> set S" "set (vars (While' b c')) \<subseteq> T" "T \<subseteq> set S"
    using inline_S_sound[OF \<open>(c', s\<^sub>1') \<Rightarrow>'\<^bsup> x' \<^esup> s\<^sub>2'\<close> _ _ _ _ 1] by auto
  with WhileTrue.IH(2) have "\<down> (inline_S S (While' b c'), s\<^sub>2)" by auto
  with 1 show ?case by auto blast
next
  case (Call c s z t t' r S s')
  then have prems: "set (r#vars c) \<subseteq> set S" "s = s' on set (r # vars c)" by auto
  (* why does the unifier not find the s' with just prems? *)
  show ?case using inline1_complete[OF Call.hyps(1) _ prems(1), of s', OF prems(2)] by simp
qed auto

end

definition inline :: "com' \<Rightarrow> com" where
  [simp]: "inline c = inline_S (vars c) c"

corollary inline_sound:
  assumes c_sem: "(c,s) \<Rightarrow>'\<^bsup>z'\<^esup> t'"
      and inline_sem: "(inline c,s)\<Rightarrow>\<^bsup>z\<^esup> t"
    shows "t = t' on set (vars c) \<and> z \<le> z' + (z' + 1) * size\<^sub>c c"
proof -
  have hyps:"s = s on set (vars c)" "set (vars c) \<subseteq> set (vars c)" by auto
  show ?thesis unfolding inline_def using inline_S_sound[OF c_sem hyps hyps(2) hyps(2) inline_sem[unfolded inline_def]] by blast
qed

lemma inline_complete:
  assumes c_sem: "(c,s) \<Rightarrow>'\<^bsup>z'\<^esup> t'"
    shows "\<down> (inline c,s)"
proof -
  have hyps:"s = s on set (vars c)" "set (vars c) \<subseteq> set (vars c)" by auto
  show ?thesis unfolding inline_def using inline_S_complete[OF c_sem hyps] by auto
qed

text \<open>Final correctness theorem\<close>
theorem inline_correct:
  assumes "(c,s) \<Rightarrow>'\<^bsup>z'\<^esup> t'"
  obtains z t 
  where "(inline c,s)\<Rightarrow>\<^bsup>z\<^esup> t" 
    and "t = t' on set (vars c)" 
    and "z \<le> (z' + 1) * (1 + size\<^sub>c c)"
  using assms inline_complete[OF assms] inline_sound[OF assms] by (fastforce simp: algebra_simps)

end