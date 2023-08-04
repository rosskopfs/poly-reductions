theory IMP_Tailcalls imports IMP_Calls begin

unbundle no_com_syntax
unbundle com'_syntax
declare [[syntax_ambiguity_warning=false]]

datatype tcom = TCall (cond: aexp) (body: com')

inductive
  tail_step_t :: "tcom \<times> state \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool"  ("_ \<Rightarrow>''''\<^bsup> _\<^esup>  _" 55)
where
TCallFalse': "\<lbrakk> aval b s = 0 \<rbrakk> \<Longrightarrow> (TCall b g,s) \<Rightarrow>''\<^bsup> 4 \<^esup> s" |
TCallTrue': "\<lbrakk> aval b s1 \<noteq> 0; (g,s1) \<Rightarrow>'\<^bsup> x \<^esup> s2;  (TCall b g, s2) \<Rightarrow>''\<^bsup> y \<^esup> s3; 3+x+y=z  \<rbrakk>
    \<Longrightarrow> (TCall b g, s1) \<Rightarrow>''\<^bsup> z \<^esup> s3"

code_pred tail_step_t .

declare tail_step_t.intros[intro]

lemmas tail_step_t_induct = tail_step_t.induct[split_format(complete)]

inductive_cases TCall_tE[elim]: "(TCall b g,s) \<Rightarrow>''\<^bsup> z \<^esup> s"


instantiation tcom :: vars
begin

fun vars_tcom :: "tcom \<Rightarrow> vname list" where
"vars_tcom (TCall a c) = vars a @ vars c"

instance ..

end

lemma noninterference: 
  "(c,s) \<Rightarrow>''\<^bsup> x \<^esup> t \<Longrightarrow> s = s' on set (vars c) \<Longrightarrow> \<exists>t'. (c,s') \<Rightarrow>''\<^bsup> x \<^esup> t' \<and> t = t' on set (vars c)"
  apply (induction c s x t arbitrary: s' rule: tail_step_t_induct)
  apply (auto)
  apply (metis TCallFalse' aval_eq_if_eq_on_vars eq_on_subset sup.cobounded1)
  apply (smt (verit) IMP_Calls.noninterference TCallTrue' aval_eq_if_eq_on_vars bot_nat_0.not_eq_extremum eq_on_subset sup.cobounded1 sup.cobounded2)
  done

lemma TCall_sem:
  fixes f :: "'a \<Rightarrow> 'a"
  fixes f_m :: "'a \<Rightarrow> nat"
  fixes g :: "'a \<Rightarrow> 'a"
  fixes g_t :: "'a \<Rightarrow> nat"
  fixes b :: "'a \<Rightarrow> bool"
  fixes \<alpha> :: "state \<Rightarrow> 'a"
  fixes b_e :: aexp
  fixes g_c :: com'

  assumes tc_sem: "(TCall b_e g_c,ss) \<Rightarrow>''\<^bsup> z \<^esup> st"
  assumes ss: "\<alpha> ss = x"
  assumes tr: "\<And>x. f x = (if b x then f (g x) else x)"
  assumes gt_less: "\<And>x. g_t (g x) \<le> g_t x"
  assumes terminate: "\<And>x. b x \<Longrightarrow> f_m (g x) < f_m x"
  assumes g_correct: 
    "\<And>x y ss. \<lbrakk> g x = y; \<alpha> ss = x \<rbrakk> \<Longrightarrow> \<exists>st z. (g_c,ss)\<Rightarrow>'\<^bsup> z \<^esup> st \<and> \<alpha> st = y \<and> z\<le> g_t x"
  assumes b_correct: "\<And>s x. \<alpha> s = x \<Longrightarrow> (aval b_e s) \<noteq> 0 \<longleftrightarrow> b x"

    shows st: "\<alpha> st = f x \<and> z \<le> 4+f_m x*(3 + g_t x)"

  using tc_sem ss tr[symmetric] gt_less terminate g_correct b_correct
proof (induction "TCall b_e g_c" ss z st arbitrary: x rule: tail_step_t_induct)
  case (TCallFalse' s)
  hence "\<alpha> s = x" "f x = x" by metis+
  then show ?case by auto
next
  case (TCallTrue' s\<^sub>1 z\<^sub>1 s\<^sub>2 z\<^sub>2 s\<^sub>3 z x) 
  hence "b x" "f_m (g x) < f_m x" by auto
  from TCallTrue' obtain x' where x': "\<alpha> s\<^sub>2 = x'" by auto
  with TCallTrue' have f: "\<alpha> s\<^sub>3 = f x'" and z2: "z\<^sub>2 \<le> 4 + f_m x' * (3 + g_t x')" by auto 
  from x' TCallTrue' determ have x'_def: "x' = g x" by blast
  from x' TCallTrue' determ have z1: "z\<^sub>1 \<le> g_t x" by blast
  from z1 z2 \<open>3 + z\<^sub>1 + z\<^sub>2 = z\<close> have "z \<le> 3+ g_t x + 4 + f_m x' * (3 + g_t x')" by simp
  also have "\<dots> \<le> 3 + g_t x + 4 + f_m x' * (3 + g_t x)" using TCallTrue'.prems(3) x'_def by simp
  also have "\<dots> = 4 + (Suc (f_m (g x)) )* (3 + g_t x)" by (simp add: x'_def numeral_eq_Suc)
  also have "\<dots> \<le> 4 + f_m x * (3 + g_t x)" using \<open>f_m (g x) < f_m x\<close>
    by (metis Suc_leI add_left_mono mult.commute mult_le_mono2)
  moreover from f TCallTrue'.prems(2) \<open>b x\<close> x'_def have "\<alpha> s\<^sub>3 = f x" by presburger
  ultimately show ?case by simp
qed

fun loop :: "tcom \<Rightarrow> com'" where
  "loop (TCall b c) = (let CONT = fresh (vars (TCall b c)) ''CONTINUE'' in
     CONT ::= b;;WHILE CONT\<noteq>0 DO (c;;CONT ::= b))"

lemma loop:
  assumes "(loop c,s) \<Rightarrow>'\<^bsup> z \<^esup> t"
  obtains t'
    where "(c,s) \<Rightarrow>''\<^bsup> z \<^esup> t'"
      and "t = t' on set (vars c)"
proof (cases c)
  case (TCall b c')

  define CONT where "CONT=fresh (vars (TCall b c')) ''CONTINUE''"
  note sem = assms(1)[unfolded TCall,simplified,unfolded Let_def]
  from TCall have vars: "CONT \<notin> set (vars c')" "CONT \<notin> set (vars b)"
    unfolding CONT_def using set_append fresh by fastforce+

  from sem obtain z' where
    1: "(CONT::=b,s) \<Rightarrow>'\<^bsup> Suc (Suc 0) \<^esup> s(CONT := aval b s)" and
    2: "(WHILE CONT\<noteq>0 DO (c';;CONT ::= b),s(CONT := aval b s)) \<Rightarrow>'\<^bsup> z' \<^esup> t" and
    z: "z = Suc (Suc 0) + z'"
    unfolding CONT_def by fastforce

  from 2 have "s = s' on set (vars c) \<Longrightarrow> \<exists>t'. (TCall b c',s') \<Rightarrow>''\<^bsup> Suc (Suc 0) + z' \<^esup> t' \<and> t = t' on set (vars c)" for s'
  proof (induction "WHILE CONT\<noteq>0 DO (c';;CONT ::= b)" "s(CONT := aval b s)" z' t arbitrary: s s' rule: big_step_t'_induct)
    case WhileFalse'
    hence b: "aval b s = 0" by simp
    hence "s(CONT := aval b s) = s on set (vars c)" using vars TCall by simp
    moreover from b have"(TCall b c',s) \<Rightarrow>''\<^bsup> 4 \<^esup> s" by auto
    ultimately show ?case apply (auto simp: numeral_eq_Suc)
      by (metis CONT_def IMP_Tailcalls.noninterference TCall WhileFalse'.prems eq_on_fupd1 fresh)
  next
    case (WhileTrue' x s2 y s3 z)
    from WhileTrue'.hyps(2) obtain x' s2' where 
      c'_sem: "(c', s(CONT := aval b s)) \<Rightarrow>'\<^bsup> x'\<^esup>  s2'" and
      CONT_sem: "(CONT ::= b,s2')\<Rightarrow>'\<^bsup> Suc (Suc 0)\<^esup>  s2" and
      x': "x = x' + (Suc (Suc 0))"
      by fastforce

    have "s2 = (s2'(CONT := s CONT))(CONT := aval b (s2'(CONT := s CONT)))" 
      using vars CONT_sem by auto
    
    from WhileTrue'.hyps(4)[OF this] obtain t' where 
      "(TCall b c', s2') \<Rightarrow>''\<^bsup> Suc (Suc 0) + y\<^esup>  t' \<and> s3 = t' on set (vars c)"
      using TCall vars by fastforce
    moreover have "aval b (s(CONT := aval b s)) \<noteq> 0"
      using WhileTrue'.hyps(1) vars apply auto
      by (metis aval_eq_if_eq_on_vars eq_onI eq_on_fupd2)
    ultimately have "(TCall b c', s(CONT := aval b s)) \<Rightarrow>''\<^bsup> Suc (Suc 0) + z\<^esup>  t'" "s3 = t' on set (vars c)"
      using c'_sem x' \<open>1 + x + y = z\<close> by auto

    then show ?case using noninterference[of c "s(CONT := aval b s)" " Suc (Suc 0) + z" t' s ] TCall WhileTrue'.prems(1) vars
      by (smt (verit, ccfv_SIG) CONT_def IMP_Tailcalls.noninterference eq_on_def fresh fun_upd_other) 
  qed

  then show ?thesis using that TCall z by auto
qed

definition compile :: "tcom \<Rightarrow> com" where
  "compile c = inline (loop c)"

lemma compile:
    assumes "(compile c,s) \<Rightarrow>\<^bsup> z \<^esup> t"
  obtains z' t'
    where "(c,s) \<Rightarrow>''\<^bsup> z' \<^esup> t'"
      and "t = t' on set (vars c)"
      and "z' \<le> z" "z \<le> (z' + 1) * (1 + size\<^sub>c (body c))"
proof -
  from inline[OF assms[unfolded compile_def]] obtain z' t' where
     loop_sem: "(loop c,s) \<Rightarrow>'\<^bsup>z'\<^esup> t'" and 
     t': "t = t' on set (vars (loop c))" and 
     z': "z' \<le> z" "z \<le> (z' + 1) * (1 + size\<^sub>c (loop c))" by blast
  from loop[OF loop_sem] obtain t'' where
    c_sem: "(c,s) \<Rightarrow>''\<^bsup> z' \<^esup> t''" and 
    t'': "t' = t'' on set (vars c)" by blast
  moreover from t' t'' have "t = t'' on set (vars c)" by (cases c) (fastforce simp: Let_def)
  ultimately show ?thesis using z' that by (cases c) (auto simp: Let_def)
qed

definition "comp_time f_m g_t x c = (5 + f_m x * (3 + g_t x)) * (1 + size\<^sub>c (body c))"

lemma final: 
  fixes c :: tcom
  fixes \<alpha> :: "state \<Rightarrow> 'a"
  fixes b :: "'a \<Rightarrow> bool"
  fixes f :: "'a \<Rightarrow> 'a"
  fixes g :: "'a \<Rightarrow> 'a"
  fixes g_t :: "'a \<Rightarrow> nat"
  fixes f_m :: "'a \<Rightarrow> nat"

assumes measure: "\<And>x. b x \<Longrightarrow> f_m (g x) < f_m x"
assumes tr: "\<And>x. f x = (if b x then f (g x) else x)"
assumes mono: "\<And>x .g_t (g x) \<le> g_t x"
assumes vars: "\<And>s t. s = t on set (vars c) \<Longrightarrow> \<alpha> s = \<alpha> t"
assumes g_correct: 
  "\<And>x y ss. \<lbrakk> y = g x; x = \<alpha> ss \<rbrakk> \<Longrightarrow> (\<exists>st z. (body c,ss) \<Rightarrow>'\<^bsup> z \<^esup> st \<and> \<alpha> st = y \<and> z \<le> g_t x)"
assumes b_correct: "\<And>s x. \<alpha> s = x \<Longrightarrow> (aval (cond c) s) \<noteq> 0 \<longleftrightarrow> b x"

  shows "(compile c,ss) \<Rightarrow>\<^bsup>z\<^esup> st \<Longrightarrow> \<alpha> st = f (\<alpha> ss) \<and> z \<le> comp_time f_m g_t (\<alpha> ss) c"
proof -
  assume "(compile c,ss) \<Rightarrow>\<^bsup>z\<^esup> st"
  with compile obtain z' st' where
    sem': "(c,ss) \<Rightarrow>''\<^bsup>z'\<^esup> st'" and
     st': "st = st' on set (vars c)" and
      z': "z \<le> (z' + 1) * (1 + size\<^sub>c (body c))" by blast

  define x :: 'a where "x = \<alpha> ss"

  have 1: "(TCall (cond c) (body c), ss) \<Rightarrow>''\<^bsup> z'\<^esup>  st'" using sem' by simp
  have *: "(\<alpha> st' = f x) \<and> (z' \<le> 4 + f_m x * (3 + g_t x))"
    using TCall_sem[of "cond c" "body c" ss z' st' \<alpha> x f b g g_t f_m, OF 1 x_def[symmetric]] assms by blast

  define z'' where "z'' = 4 + f_m x * (3 + g_t x)"
  with * have "z' \<le> z''" by simp
  with z' have "z \<le> (z'' + 1) * (1 + size\<^sub>c (body c))"
    by (metis One_nat_def Suc_le_mono add.right_neutral add_Suc_right dual_order.trans mult_le_mono1)
  hence "z \<le> comp_time f_m g_t (\<alpha> ss) c" unfolding comp_time_def x_def z''_def by auto

  moreover from * st' z' vars x_def have "\<alpha> st = f (\<alpha> ss)" by auto  
  ultimately show ?thesis unfolding comp_time_def by auto
qed

end