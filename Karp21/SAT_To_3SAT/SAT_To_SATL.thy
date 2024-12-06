theory SAT_To_SATL
imports "Poly_Reductions_Lib.SAT_Definition" "../Reductions"
begin

text "the reduction to AT_MOST_3SAT is easier if  we work with lists"

section "SAT lib for lists"

subsection "definitions"

type_synonym 'a clause\<^sub>l = "'a lit list"

definition models :: "('a \<Rightarrow> bool) \<Rightarrow> 'a clause\<^sub>l list \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>l" 55) where
  "\<sigma> \<Turnstile>\<^sub>l F \<equiv> \<forall>cls \<in> set F. \<exists>l \<in> set cls. (\<sigma>\<up>) l"

abbreviation sat\<^sub>l :: "'a clause\<^sub>l list \<Rightarrow> bool" where
  "sat\<^sub>l F \<equiv> \<exists>\<sigma>. \<sigma> \<Turnstile>\<^sub>l F"

definition SAT\<^sub>l where
  "SAT\<^sub>l = {F. sat\<^sub>l F}"

fun flip where
  "flip (Pos a) = (Neg a)"
| "flip (Neg a) = (Pos a)"

fun var where
  "var (Pos a) = a"
| "var (Neg a) = a"

definition vars_cls where
  "vars_cls cls = set (map var cls)"  

definition vars where 
  "vars F = \<Union> (set (map vars_cls F))"


subsection "var(s) lemmas"

lemma var_map_lit[simp]:
  "var (map_lit f x) = f (var x)" for x
  by (cases x) (auto)

lemma vars_cons:
  "vars (x#xs) =  (vars_cls x) \<union> (vars xs)"
  by (simp add: vars_def)

lemma var_flip[simp]:
  "var (flip d) = var d"
  by (cases d) auto

lemma vars_append:
  "vars (a@b) = vars a \<union> vars b"
  by (simp add: vars_def)

subsection "models lemmas"

lemma models_list_models:
    "\<sigma> \<Turnstile>\<^sub>l F = \<sigma> \<Turnstile> (map set F)"
  unfolding models_def SAT_Definition.models_def
  by auto

lemma models_cong:
  assumes "\<forall>x \<in> vars F. \<sigma>1 x = \<sigma>2 x"
  "\<sigma>2 \<Turnstile>\<^sub>l F"
  shows "\<sigma>1 \<Turnstile>\<^sub>l F" 
proof (unfold models_def, intro ballI)
  fix cls assume "cls \<in> set F"
  then obtain l where "(\<sigma>2\<up>) l" "l \<in> set cls"
    using \<open>\<sigma>2 \<Turnstile>\<^sub>l F\<close>  models_def by blast
  moreover then have "var l \<in> vars F"
    using \<open>cls \<in> set F\<close>  vars_def vars_cls_def
    by fastforce
  ultimately have "(\<sigma>1\<up>) l"
    using assms(1)
    by (cases l) (auto simp add: lift_def)
  then show "\<exists>l\<in>set cls. (\<sigma>1\<up>) l"  
    using \<open>l \<in> set cls\<close> 
    by blast
qed

lemma models_cons:  
  "\<sigma> \<Turnstile>\<^sub>l  x # xs \<longleftrightarrow> \<sigma> \<Turnstile>\<^sub>l [x] \<and> \<sigma> \<Turnstile>\<^sub>l xs"
  by (simp add: models_def)

lemma models_append:  
  shows "\<sigma> \<Turnstile>\<^sub>l (a @ b) = (\<sigma> \<Turnstile>\<^sub>l a \<and> \<sigma> \<Turnstile>\<^sub>l b)"
  by (auto simp add: models_def)


section "The Reduction"

lemma set_to_list:
  assumes "finite s"
  shows  "set ((\<lambda> s. SOME l. set l = s) s) = s"
  by (meson assms finite_list someI_ex)

definition sat_to_satl where
  "sat_to_satl F = (if (\<forall>cls \<in> set F. finite cls)
                   then map (\<lambda> s. SOME l. set l = s) F
                   else [[]])"
    

section "Soundness"
 
lemma sat_to_satl_sound:
  assumes "F \<in> SAT"
  shows "sat_to_satl F \<in> SAT\<^sub>l"
  using assms
  unfolding SAT_def SAT\<^sub>l_def sat_def sat_to_satl_def
            models_def 
  by (auto) (metis SAT_Definition.models_def set_to_list)

section "Completeness"

lemma sat_to_satl_complete:
  assumes "sat_to_satl F \<in> SAT\<^sub>l"
  shows "F \<in> SAT"
  using assms 
  unfolding SAT_def SAT\<^sub>l_def sat_def sat_to_satl_def
            models_def SAT_Definition.models_def
  by (cases "\<forall>x\<in>set F. finite x")
     (auto simp add: set_to_list)

section "Conclusion"

theorem is_reduction_sat_to_satl:
  "is_reduction sat_to_satl SAT SAT\<^sub>l"
  unfolding is_reduction_def 
  using sat_to_satl_sound sat_to_satl_complete
  by auto

end