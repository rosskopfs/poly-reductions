\<^marker>\<open>creator Fabian Huch\<close>

theory IMP_Calls imports Vars begin

section "IMP"

text \<open>IMP with calls to IMP- programs (explicitly stored).\<close>
datatype
  com' = SKIP'
      | Assign' vname aexp
      | Seq'    com'  com'
      | If'     vname com' com'
      | While'  vname com'
\<comment> \<open>The only change: A call to an IMP- @{typ com}, storing its result in the return @{typ vname}.\<close>
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
  big_step_t' :: "com' \<times> state \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool"  ("_ \<Rightarrow>''\<^bsup> _\<^esup>  _" 55)
where
Skip': "(SKIP',s) \<Rightarrow>'\<^bsup> Suc (0::nat) \<^esup> s"|
Assign': "(x ::= a,s) \<Rightarrow>'\<^bsup> Suc (Suc 0) \<^esup> s(x := aval a s)" |
Seq': "\<lbrakk> (c1,s1) \<Rightarrow>'\<^bsup> x \<^esup> s2;  (c2,s2) \<Rightarrow>'\<^bsup> y \<^esup> s3 ; z=x+y \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow>'\<^bsup> z \<^esup> s3" |
IfTrue': "\<lbrakk> s b \<noteq> 0;  (c1,s) \<Rightarrow>'\<^bsup> x \<^esup> t; y=x+1 \<rbrakk> \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>'\<^bsup> y \<^esup> t" |
IfFalse': "\<lbrakk> s b = 0; (c2,s) \<Rightarrow>'\<^bsup> x \<^esup> t; y=x+1  \<rbrakk> \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>'\<^bsup> y \<^esup> t" |
WhileFalse': "\<lbrakk> s b = 0 \<rbrakk> \<Longrightarrow> (WHILE b \<noteq>0 DO c,s) \<Rightarrow>'\<^bsup> Suc (Suc 0) \<^esup> s" |
WhileTrue': "\<lbrakk> s1 b \<noteq> 0;  (c,s1) \<Rightarrow>'\<^bsup> x \<^esup> s2;  (WHILE b \<noteq>0 DO c, s2) \<Rightarrow>'\<^bsup> y \<^esup> s3; 1+x+y=z  \<rbrakk>
    \<Longrightarrow> (WHILE b \<noteq>0 DO c, s1) \<Rightarrow>'\<^bsup> z \<^esup> s3" |
\<comment> \<open>The only change: The called program is executed on a state that agrees on all the variables in
    the subprogram. In the caller, only the result variable is affected.\<close>
Call': "(c,s) \<Rightarrow>\<^bsup> z \<^esup> t \<Longrightarrow> (CALL c RETURN r,s) \<Rightarrow>'\<^bsup> z \<^esup> (s(r:=t r))"

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

section "Inlining"

subsection "Memory mapping"

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

lemma ssubst_correct:
  "\<lbrakk> inj_on m (set vs); (\<forall>v\<in>set vs. m v \<notin> set vs) \<rbrakk>
    \<Longrightarrow> \<exists>t. (ssubst m vs,s) \<Rightarrow>\<^bsup>Suc (2 * length vs)\<^esup> t \<and> s = t o m on set vs"
proof (induction vs arbitrary: s)
  case (Cons v vs)
  have 1: "(Assign (m v) (A (V v)),s) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> s(m v := s v)"
    using Assign[of _ "A (V v)"] by simp
  from Cons obtain t where
    2: "(ssubst m vs, s(m v := s v)) \<Rightarrow>\<^bsup>Suc (2 * length (vs)) \<^esup> t" and
    s: "s(m v := s v) = t \<circ> m on set vs" by fastforce
  hence "s(m v := s v) = t \<circ> m on set (v#vs)"
  proof (cases "v\<in>set vs")
    case True then show ?thesis using s by auto
  next
    case False
    with Cons.prems(2) have a: "v \<notin> set (vars (ssubst m vs))" by (induction vs) auto
    hence " v \<notin> m ` set vs" by fastforce
    with False have "m v \<notin> m ` set vs" using \<open>\<forall>va\<in>set (v # vs). m va \<notin> set (v # vs)\<close>
      using Cons.prems(1) by force
    with a have "m v \<notin> set (vars (ssubst m vs))" apply auto
      using Cons.prems(2) by force
    hence "(s(m v := s v)) (m v) = t (m v)" using var_unchanged[OF 2] by blast
    then show ?thesis using s by auto
  qed
  hence "s = t \<circ> m on set (v # vs)"
    by (metis Cons.prems(2) fun_upd_other list.set_intros(1))
  with 1 2 show ?case by fastforce
qed auto


subsection "Command transfer"

definition [simp]: "transfer m c = ssubst m (vars c);;subst m c"

lemma set_transfer[simp]: "set (vars (transfer m c)) = set (vars c) \<union> m ` set (vars c)"
  unfolding transfer_def by auto

lemma transfer_sound:
  assumes c_sem: "(c,s) \<Rightarrow>\<^bsup>z\<^esup> t"
      and s: "s = s' on set (vars c)"
      and inj: "inj_on m (set (vars c))"
      and disj: "(\<forall>v\<in>set (vars c). m v \<notin> set (vars c))"
    obtains t'
    where "(transfer m c,s')\<Rightarrow>\<^bsup>Suc (2 * length (vars c)) + z\<^esup> t'"
      and "t = t' o m on set (vars c)"
proof -
  from ssubst_correct[OF inj disj] obtain s\<^sub>2 where ssubst_sem:
    "(ssubst m (vars c),s')\<Rightarrow>\<^bsup>Suc (2 * length (vars c))\<^esup> s\<^sub>2" and
    "s' = s\<^sub>2 \<circ> m on set (vars c)" by auto
  with s have s\<^sub>2: "s = s\<^sub>2 o m on set (vars c)" by simp

  from subst_sound[OF c_sem this _ inj] obtain t' where
    subst_sem: "(subst m c, s\<^sub>2) \<Rightarrow>\<^bsup> z \<^esup> t'" and t': "t = t' \<circ> m on set (vars c)" by auto
  with ssubst_sem have "(transfer m c,s')\<Rightarrow>\<^bsup>Suc (2 * length (vars c)) + z\<^esup> t'" by auto

  with t' that show ?thesis by blast
qed

lemma transfer_complete:
  assumes transfer_sem: "(transfer m c,s')\<Rightarrow>\<^bsup>z'\<^esup> t'"
      and s: "s' = s on set (vars c)"
      and inj: "inj_on m (set (vars c))"
      and disj: "(\<forall>v\<in>set (vars c). m v \<notin> set (vars c))"
  obtains t z
    where "(c,s) \<Rightarrow>\<^bsup>z\<^esup> t" "z' = Suc (2 * length (vars c)) + z" "t = t' o m on set (vars c)"
proof -
  from ssubst_correct[OF inj disj] obtain s\<^sub>2' where
     s\<^sub>2': "(ssubst m (vars c), s') \<Rightarrow>\<^bsup> Suc (2 * length (vars c)) \<^esup> s\<^sub>2'" "s' = s\<^sub>2' \<circ> m on set (vars c)"
    by auto
  with transfer_sem[unfolded transfer_def] obtain z where
   subst_sem: "(subst m c,s\<^sub>2') \<Rightarrow>\<^bsup>z\<^esup> t'" and z: "z' = Suc (2 * length (vars c)) + z"
    using big_step_t_determ2 by fastforce
  from s s\<^sub>2' have "s = s\<^sub>2' o m on set (vars c)" by simp
  from subst_complete[OF subst_sem this _ inj] that z show ?thesis by auto
qed

lemma transfer_unchanged:
  assumes transfer_sem: "(transfer m c,s) \<Rightarrow>\<^bsup>z\<^esup> t"
      and inj: "inj_on m (set (vars c))"
      and disj: "(\<forall>v\<in>set (vars c). m v \<notin> set (vars c))"
    shows "s = t on UNIV - m ` set (vars c)"
proof -
  from transfer_sem obtain s\<^sub>2 x y where ssubst_sem: "(ssubst m (vars c),s)\<Rightarrow>\<^bsup>x\<^esup> s\<^sub>2" and subst_sem: "(subst m c,s\<^sub>2)\<Rightarrow>\<^bsup>y\<^esup> t" by auto
  from ssubst_correct[OF inj disj] have "s = s\<^sub>2 o m on set (vars c)"
    using \<open>(ssubst m (vars c), s) \<Rightarrow>\<^bsup> x \<^esup> s\<^sub>2\<close> bigstep_det by blast

  have "s = s\<^sub>2 on UNIV - m ` set (vars c)"
    using disj ssubst_sem ssubst_unchanged
    by (simp add: rvars_unchanged)
  moreover have "s\<^sub>2 = t  on UNIV - m ` set (vars c)" using var_unchanged apply auto
    using subst_sem(1) by auto
  ultimately show "s = t on UNIV - m ` set (vars c)" by auto
qed

definition [simp]: "inline1 S c r =  (fresh S r) ::= A (V r);;transfer (fresh S) c;;r ::= A (V ((fresh S) r))"

lemma inline1_vars_c[simp]: "set (vars c) \<subseteq> set (vars (inline1 S c r))"
  unfolding inline1_def by auto

lemma inline1_vars_r[simp]: "r \<in> set (vars (inline1 S c r))"
  unfolding inline1_def by auto

lemma inline1_unchanged:
  assumes inline1_sem: "(inline1 S c r,s) \<Rightarrow>\<^bsup>z\<^esup> t"
      and S: "set (r#vars c) \<subseteq> set S"
    shows "s = t on set S - {r}"
proof -
  let ?m = "fresh S"
  have inj: "inj_on ?m (set (vars c))" and disj: "(\<forall>v\<in>set (vars c). ?m v \<notin> set (vars c))"
    using S fresh fresh_inj inj_on_subset by auto

  from inline1_sem obtain s\<^sub>1 z\<^sub>1 z\<^sub>2  s\<^sub>2 z z\<^sub>3 where
    to_sem: "((?m r) ::= A (V r),s) \<Rightarrow>\<^bsup>z\<^sub>1\<^esup> s\<^sub>1" and
    "(transfer ?m c;;r ::= A (V (?m r)),s\<^sub>1)\<Rightarrow>\<^bsup>z\<^sub>2\<^esup> t" and
    transfer_sem: "(transfer ?m c,s\<^sub>1)\<Rightarrow>\<^bsup>z\<^esup> s\<^sub>2" and
    from_sem: "(r ::= A (V (?m r)),s\<^sub>2)\<Rightarrow>\<^bsup>z\<^sub>3\<^esup> t"
    unfolding inline1_def by fastforce

  hence s\<^sub>1: "s\<^sub>1 = s(?m r := s r)" "t = s\<^sub>2(r := s\<^sub>2(?m r))" by auto
  moreover have "s\<^sub>1 = s\<^sub>2 on set S" using transfer_unchanged[OF transfer_sem inj disj] by auto

  ultimately show "s = t on set S - {r}"
    by (metis DiffE fresh fun_upd_other singleton_iff)
qed

lemma inline1_sound:
  assumes c_sem: "(c,s) \<Rightarrow>\<^bsup>z\<^esup> t"
      and s: "s = s' on set (r#vars c)"
      and S: "set (r#vars c) \<subseteq> set S"
  obtains zr tr
    where "(inline1 S c r,s') \<Rightarrow>\<^bsup>zr\<^esup> tr"
      and "t r = tr r" "2 * length (vars c) + z + 5 = zr"
proof -
  let ?m = "fresh S" let ?s\<^sub>1' = "s'((?m r) := s' r)" let ?z' = "Suc (2 * length (vars c)) + z"

  have inj: "inj_on ?m (set (vars c))" using S fresh_inj inj_on_subset by auto
  have disj: "(\<forall>v\<in>set (vars c). ?m v \<notin> set (vars c))" using S fresh by auto

  have 1: "((?m r) ::= A (V r),s') \<Rightarrow>\<^bsup>Suc (Suc 0)\<^esup> ?s\<^sub>1'"
    using big_step_t.Assign[of "?m r" "A (V r)" s'] by auto
  have s\<^sub>1': "s = ?s\<^sub>1' on set (vars c)" using S s by auto

  obtain s\<^sub>2' where
    2: "(transfer ?m c, ?s\<^sub>1') \<Rightarrow>\<^bsup>?z'\<^esup> s\<^sub>2'" and s\<^sub>2': "t = s\<^sub>2' \<circ> ?m on set (vars c)"
    using transfer_sound[OF c_sem s\<^sub>1' inj disj] by blast

  then obtain tr where
    3: "(r ::= A (V (?m r)),s\<^sub>2')\<Rightarrow>\<^bsup>Suc (Suc 0)\<^esup> tr" and tr: "tr = s\<^sub>2'(r := s\<^sub>2'(?m r))"
    by fastforce

  from 1 2 3 s\<^sub>1' have res: "(inline1 S c r,s')\<Rightarrow>\<^bsup>Suc (Suc 0) + ?z' + Suc (Suc 0)\<^esup> tr"
    unfolding inline1_def using Seq by meson

  have "t r = tr r"
  proof (cases "r \<in> set (vars c)")
    case True
    from tr have "tr r = (s\<^sub>2' o ?m) r" by auto
    with True show ?thesis using s\<^sub>2' by simp
  next
    case False
    hence "?m r \<notin> set (vars (transfer ?m c))"
      by (smt (verit, best) S Un_iff fresh fresh_inj inj_on_image_mem_iff list.set_intros(1) set_subset_Cons set_transfer subsetD subset_inj_on)

    with 2 have "?s\<^sub>1' (?m r) = s\<^sub>2' (?m r)"
      using var_unchanged by blast

    then show ?thesis by (metis False c_sem fun_upd_same list.set_intros(1) s tr var_unchanged)
  qed
  then show ?thesis using that res by auto
qed

lemma inline1_complete:
  assumes inline_sem: "(inline1 S c r,s') \<Rightarrow>\<^bsup>zr\<^esup> tr"
      and s: "s = s' on set (r#vars c)"
      and S: "set (r#vars c) \<subseteq> set S"
  obtains z t
    where "(c,s) \<Rightarrow>\<^bsup>z\<^esup> t \<and> tr r = t r \<and> 2 * length (vars c) + z + 5 = zr"
proof -
  let ?m = "fresh S" let ?s\<^sub>1' = "s'((?m r) := s' r)"

  have inj: "inj_on ?m (set (vars c))" using S fresh_inj inj_on_subset by auto
  have disj: "(\<forall>v\<in>set (vars c). ?m v \<notin> set (vars c))" using S fresh by auto

  have 1: "((?m r) ::= A (V r),s') \<Rightarrow>\<^bsup>Suc (Suc 0)\<^esup> ?s\<^sub>1'"
    using big_step_t.Assign[of "?m r" "A (V r)" s'] by auto
  have s\<^sub>1': "?s\<^sub>1' = s on set (vars c)" using S s by auto

  from inline_sem obtain t' z' where
    2: "(transfer ?m c,?s\<^sub>1') \<Rightarrow>\<^bsup>z'\<^esup> t'" and z': "z' + 4 = zr" by fastforce
  from transfer_complete[OF 2 s\<^sub>1' inj disj] obtain t z where
    c_sem: "(c, s) \<Rightarrow>\<^bsup> z \<^esup> t" and
    z: "z' = Suc (2 * length (vars c)) + z" and
    t: "t = t' \<circ> fresh S on set (vars c)" by metis

  obtain tr' where
    3: "(r ::= A (V (?m r)),t')\<Rightarrow>\<^bsup>Suc (Suc 0)\<^esup> tr'" and tr: "tr' = t'(r := t'(?m r))"
    by fastforce

  moreover from z have "(inline1 S c r,s')\<Rightarrow>\<^bsup>Suc (Suc 0) + Suc (2 * length (vars c)) + z + Suc (Suc 0)\<^esup> tr'"
    unfolding inline1_def using Seq[OF 1 2] Seq[OF _ 3] by auto

  ultimately have tr': "tr' = tr"
    using bigstep_det inline_sem by blast

  have "tr' r = t r"
  proof (cases "r \<in> set (vars c)")
    case True
    from tr have "tr' r = (t' o ?m) r" by auto
    with True show ?thesis using t by simp
  next
    case False
    hence "?m r \<notin> set (vars (transfer ?m c))"
      by (smt (verit, best) S Un_iff fresh fresh_inj inj_on_image_mem_iff list.set_intros(1) set_subset_Cons set_transfer subsetD subset_inj_on)

    with 2 have "?s\<^sub>1' (?m r) = t' (?m r)"
      using var_unchanged by blast

     show ?thesis
       by (metis False \<open>(s'(fresh S r := s' r)) (fresh S r) = t' (fresh S r)\<close> c_sem fun_upd_same list.set_intros(1) s tr var_unchanged)
   qed

  then show ?thesis using that c_sem z z' tr' by auto
qed


section \<open>Program inlining\<close>

fun inline_S :: "vname list \<Rightarrow> com' \<Rightarrow> com" where
  "inline_S S SKIP' = SKIP" |
  "inline_S S (Assign' x a) = (x::=a)" |
  "inline_S S (Seq' c\<^sub>1' c\<^sub>2') = inline_S S c\<^sub>1';;inline_S S c\<^sub>2'" |
  "inline_S S (If' b c\<^sub>1' c\<^sub>2') = IF b\<noteq>0 THEN inline_S S c\<^sub>1' ELSE inline_S S c\<^sub>2'" |
  "inline_S S (While' b c') = WHILE b\<noteq>0 DO inline_S S c'" |
  "inline_S S (Call' c r) = inline1 S c r"

lemma vars_inline_S[simp]: "set (vars c) \<subseteq> set (vars (inline_S S c))"
  by (induction c arbitrary: S) auto

lemma inline_S_sound:
  "\<lbrakk> (c',s') \<Rightarrow>'\<^bsup>z'\<^esup> t'; s'= s on set S; set (vars c') \<subseteq> set S \<rbrakk>
    \<Longrightarrow> \<exists>t z. (inline_S S c',s)\<Rightarrow>\<^bsup>z\<^esup> t \<and> t = t' on set S \<and> z \<le> z' + (z' + 1) * size\<^sub>c c'"
proof(induction c' s' z' t' arbitrary: s rule: big_step_t'_induct)
  case (Assign' x a s' s)
  hence "s(x := aval a s) = s'(x := aval a s') on set S" by (auto simp: in_mono)
  moreover have "(inline_S S (Assign' x a), s) \<Rightarrow>\<^bsup> Suc (Suc 0) \<^esup> s(x := aval a s)" by auto
  ultimately show ?case by fastforce
next
  case (Seq' c\<^sub>1 s\<^sub>1 x s\<^sub>2 c\<^sub>2 y s\<^sub>3 z s\<^sub>1')
  then obtain s\<^sub>2' x' where
    1: "(inline_S S c\<^sub>1, s\<^sub>1') \<Rightarrow>\<^bsup> x' \<^esup> s\<^sub>2' \<and> s\<^sub>2' = s\<^sub>2 on set S \<and> x' \<le> x + (x + 1) * size\<^sub>c c\<^sub>1"
    by fastforce
  hence prems2: "s\<^sub>2 = s\<^sub>2' on set S" by auto
  from Seq' obtain s\<^sub>3' y' where
    2: "(inline_S S c\<^sub>2, s\<^sub>2') \<Rightarrow>\<^bsup> y' \<^esup> s\<^sub>3' \<and> s\<^sub>3' = s\<^sub>3 on set S \<and> y' \<le> y + (y + 1) * size\<^sub>c c\<^sub>2"
    using Seq'.IH(2)[OF prems2 ] by auto
  from 1 2 Seq'.hyps(3) show ?case by (fastforce simp: algebra_simps)
next
  case (IfTrue' s b c\<^sub>1' x t y c\<^sub>2' s')
  then obtain x' t' where "(inline_S S c\<^sub>1', s') \<Rightarrow>\<^bsup> x' \<^esup> t' \<and> t' = t on set S \<and> x' \<le> x + (x + 1) * size\<^sub>c c\<^sub>1'" by fastforce
  with IfTrue'.hyps(1,3) IfTrue'.prems have
    "(inline_S S (If' b c\<^sub>1' c\<^sub>2'), s') \<Rightarrow>\<^bsup> x' + 1 \<^esup> t' \<and> t' = t on set S \<and> x' + 1 \<le> y + (y + 1) * size\<^sub>c (If' b c\<^sub>1' c\<^sub>2')"
    by (auto simp: algebra_simps)
  thus ?case by blast
next
  case (IfFalse' s b c\<^sub>2' x t y c\<^sub>1' s')
  then obtain x' t' where "(inline_S S c\<^sub>2', s') \<Rightarrow>\<^bsup> x' \<^esup> t' \<and> t' = t on set S \<and> x' \<le> x + (x + 1) * size\<^sub>c c\<^sub>2'" by fastforce
  with IfFalse'.hyps(1,3) IfFalse'.prems have
    "(inline_S S (If' b c\<^sub>1' c\<^sub>2'), s') \<Rightarrow>\<^bsup> x' + 1 \<^esup> t' \<and> t' = t on set S \<and> x' + 1 \<le> y + (y + 1) * size\<^sub>c (If' b c\<^sub>1' c\<^sub>2')"
    by (auto simp: algebra_simps)
  thus ?case by blast
next
  case (WhileTrue' s\<^sub>1 b c\<^sub>1 x s\<^sub>2 y s\<^sub>3 z s\<^sub>1')
  hence prems1: "set (vars c\<^sub>1) \<subseteq> set S" by simp
  obtain s\<^sub>2' x' where 1: "(inline_S S c\<^sub>1, s\<^sub>1') \<Rightarrow>\<^bsup> x' \<^esup> s\<^sub>2' \<and> s\<^sub>2' = s\<^sub>2 on set S \<and> x' \<le> x + (x + 1) * size\<^sub>c c\<^sub>1"
    using WhileTrue'.IH(1)[OF WhileTrue'.prems(1) prems1] by blast
  with WhileTrue' have prems2: "s\<^sub>2 = s\<^sub>2' on set S" "set (vars (While' b c\<^sub>1)) \<subseteq> set S" by auto
  obtain s\<^sub>3' y' where 2: "(inline_S S (While' b c\<^sub>1), s\<^sub>2') \<Rightarrow>\<^bsup> y' \<^esup> s\<^sub>3' \<and> s\<^sub>3' = s\<^sub>3 on set S \<and> y' \<le> y + (y + 1) * size\<^sub>c (While' b c\<^sub>1)"
    using WhileTrue'.IH(2)[OF prems2] by auto
  from WhileTrue' have "s\<^sub>1' b \<noteq> 0" by simp
  with 1 2 WhileTrue'.hyps(4) have "(inline_S S (While' b c\<^sub>1), s\<^sub>1') \<Rightarrow>\<^bsup> 1 + x' + y' \<^esup> s\<^sub>3' \<and> s\<^sub>3' = s\<^sub>3 on set S \<and> 1 + x' + y' \<le> z + (z + 1) * size\<^sub>c (While' b c\<^sub>1)"
    by (auto simp: algebra_simps)
  thus ?case by blast
next
  case (Call' c s z t r s')
  hence prems: "s = s' on set (r # vars c)" "set (r # vars c) \<subseteq> set S" by auto
  then obtain zr tr where
    inline: "(inline1 S c r, s') \<Rightarrow>\<^bsup> zr \<^esup> tr" "t r = tr r" "2 * length (vars c) + z + 5 = zr"
    using inline1_sound[OF Call'.hyps] by blast
  with Call'.prems(1) inline1_unchanged[OF inline(1) prems(2)] have "tr = s(r := tr r) on set S"
    by simp
  with inline have " (inline_S S (Call' c r), s') \<Rightarrow>\<^bsup> zr \<^esup> tr \<and> tr = s(r := t r) on set S \<and> zr \<le> z + (z + 1) * size\<^sub>c (Call' c r)" by simp
  then show ?case by blast
qed auto

lemma inline_S_complete:
  assumes "(inline_S S c',s) \<Rightarrow>\<^bsup>z\<^esup> t" "s= s' on set S" "set (vars c') \<subseteq> set S"
  shows "\<exists>z' t'. (c',s') \<Rightarrow>'\<^bsup>z'\<^esup> t' \<and> t = t' on set S \<and> z' \<le> z"
  using assms proof (induction "inline_S S c'" s z t arbitrary: c' s' rule: big_step_t_induct)
  case (Skip s)
  then show ?case by (cases c') auto
next
  case (Assign x a s)
  then show ?case apply (cases c') apply auto
    by (metis Assign' aval_eq_if_eq_on_vars eq_imp_le fun_upd_apply subset_iff)
next
  case (Seq c\<^sub>1 s\<^sub>1 x s\<^sub>2 c\<^sub>2 y s\<^sub>3 z c')
  then show ?case
  proof (cases c')
    case (Seq' c\<^sub>1' c\<^sub>2') with Seq show ?thesis by fastforce
  next
    case (Call' c r)
    with Seq.prems Seq.hyps(1,3,5,6) have 1: "(inline1 S c r,s\<^sub>1)\<Rightarrow>\<^bsup> z \<^esup> s\<^sub>3"  "s' = s\<^sub>1 on set (r # vars c)" "set (r # vars c) \<subseteq> set S"
      by auto
    from inline1_complete[OF this] obtain z' t where
      c_sem: "(c, s') \<Rightarrow>\<^bsup> z' \<^esup> t" and t: "s\<^sub>3 r = t r" and z': "2 * length (vars c) + z' + 5 = z" by metis
    with big_step_t'.Call' Call' have "(c',s') \<Rightarrow>'\<^bsup> z' \<^esup> s'(r := t r)" by simp
    have "s\<^sub>1 = s\<^sub>3 on set S - {r}" using inline1_unchanged[OF 1(1) 1(3)] .
    show ?thesis
      using Seq.prems(1) \<open>(c', s') \<Rightarrow>'\<^bsup> z' \<^esup> s'(r := t r)\<close> \<open>s\<^sub>1 = s\<^sub>3 on set S - {r}\<close> t z' by fastforce
  qed (use Seq.hyps(6) in auto)
next
  case (IfTrue s b c\<^sub>1 x t y c\<^sub>2)
  then obtain c\<^sub>1' c\<^sub>2' where c': "c' = If' b c\<^sub>1' c\<^sub>2'" by (cases c') auto
  with IfTrue obtain x' t' where "(c\<^sub>1', s') \<Rightarrow>'\<^bsup>x'\<^esup> t' \<and> (t = t' on set S) \<and> x' \<le> x" by fastforce
  with c' IfTrue show ?case by fastforce
next
  case (IfFalse s b c\<^sub>2 x t y c\<^sub>1)
  then obtain c\<^sub>1' c\<^sub>2' where c': "c' = If' b c\<^sub>1' c\<^sub>2'" by (cases c') auto
  with IfFalse obtain x' t' where "(c\<^sub>2', s') \<Rightarrow>'\<^bsup>x'\<^esup> t' \<and> (t = t' on set S) \<and> x' \<le> x" by fastforce
  with c' IfFalse show ?case by fastforce
next
  case (WhileFalse s b c)
  then show ?case by (cases c') auto
next
  case (WhileTrue s\<^sub>1 b c\<^sub>1 x s\<^sub>2 y s\<^sub>3 z c' s\<^sub>1')
  then obtain c\<^sub>1' where c'[simp]: "c' = While' b c\<^sub>1'" by (cases c') auto
  with WhileTrue obtain s\<^sub>2' x' where 1: "(c\<^sub>1', s\<^sub>1') \<Rightarrow>'\<^bsup> x' \<^esup> s\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2' on set S \<and> x' \<le> x" by fastforce
  with WhileTrue c' obtain s\<^sub>3' y' where 2: "(While' b c\<^sub>1', s\<^sub>2') \<Rightarrow>'\<^bsup> y' \<^esup> s\<^sub>3' \<and> s\<^sub>3 = s\<^sub>3' on set S \<and> y' \<le> y" by fastforce
  from c' WhileTrue.prems WhileTrue.hyps(1) have b: "s\<^sub>1' b \<noteq> 0" by auto
  with 1 2 c' have "(While' b c\<^sub>1', s\<^sub>1') \<Rightarrow>'\<^bsup> 1 + x' + y' \<^esup> s\<^sub>3'" "1 + x' + y' \<le> 1 + x + y" using WhileTrue'[of s\<^sub>1', OF b] by auto
  with c' WhileTrue.hyps(6) show ?case using 2 by blast
qed

definition inline :: "com' \<Rightarrow> com" where
  [simp]: "inline c = inline_S (vars c) c"


theorem inline_sound:
  assumes c_sem: "(c,s') \<Rightarrow>'\<^bsup>z'\<^esup> t'"
      and s: "s' = s on set (vars c)"
  obtains z t
    where "(inline c,s)\<Rightarrow>\<^bsup>z\<^esup> t"
      and "t = t' on set (vars c)"
      and "z \<le> (z' + 1) * (1 + size\<^sub>c c)"
  unfolding inline_def using inline_S_sound[OF c_sem s] by auto

theorem inline_complete:
  assumes inline_sem: "(inline c,s)\<Rightarrow>\<^bsup>z\<^esup> t"
      and s: "s = s' on set (vars c)"
  obtains z' t'
   where "(c,s') \<Rightarrow>'\<^bsup>z'\<^esup> t'"
     and "t = t' on set (vars c)" "z' \<le> z"
  unfolding inline_def using inline_S_complete[OF inline_sem[unfolded inline_def] s] by auto


text \<open>Final correctness theorem (for refinements)\<close>
corollary inline:
  assumes "(inline c,s)\<Rightarrow>\<^bsup>z\<^esup> t"
  obtains z' t'
    where "(c,s) \<Rightarrow>'\<^bsup>z'\<^esup> t'"
      and "t = t' on set (vars c)"
      and "z' \<le> z"
  using inline_complete[where ?s'=s,OF assms] by auto

end