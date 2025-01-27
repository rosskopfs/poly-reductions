theory SAT_To_XC_Aux
  imports
    SAT_Definition
    XC_Definition
begin

datatype 'a xc_element = V 'a | C "'a lit set" | L "'a lit" "'a lit set"

fun var :: "'a lit \<Rightarrow> 'a" where
"var (Neg a) = a" |
"var (Pos a) = a"

definition "vars F \<equiv> var ` \<Union> (set F)"

definition vars_of_sat :: "'a sat \<Rightarrow> 'a xc_element set" where
  "vars_of_sat F = {V v |v. v \<in> vars F}"

lemma vars_of_sat_finite: "\<forall>cls\<in>set F. finite cls \<Longrightarrow> finite (vars_of_sat F)"
  proof -
    assume "\<forall>cls\<in>set F. finite cls"
    hence "finite (\<Union> (set F))" by simp
    hence "finite (var ` (\<Union> (set F)))" using finite_imageI by blast
    moreover have "vars F = (var ` (\<Union> (set F)))" unfolding vars_def by blast
    ultimately show ?thesis unfolding vars_of_sat_def by auto
  qed

definition clauses_of_sat :: "'a sat \<Rightarrow> 'a xc_element set" where
  "clauses_of_sat F = {C c| c. c\<in> set F}"

lemma clauses_of_sat_correct[simp]:
  "c \<in> set F \<Longrightarrow> C c \<in> clauses_of_sat F"
  unfolding clauses_of_sat_def by blast

lemma clauses_of_sat_finite:
  "finite (clauses_of_sat F)"
  unfolding clauses_of_sat_def by simp

definition literals_of_sat :: "'a sat \<Rightarrow> 'a xc_element set" where
"literals_of_sat F = {L l c| l c. c \<in> set F \<and> l \<in> c}"

lemma literals_of_sat_correct[simp]:
  "\<lbrakk>c \<in> set F; l \<in> c\<rbrakk> \<Longrightarrow> L l c \<in> literals_of_sat F"
  unfolding literals_of_sat_def by simp

lemma literals_of_sat_finite:
  "\<forall>cls\<in>set F. finite cls \<Longrightarrow> finite (literals_of_sat F)"
  proof -
    assume "\<forall>cls\<in>set F. finite cls"
    then have "\<forall>c \<in> set F. finite {L l c |l. l \<in> c}"
      by fastforce
    moreover have "{L l c |l c. c \<in> set F \<and> l \<in> c} = \<Union> {{L l c |l. l \<in> c} | c. c \<in> set F}"
      by blast
    ultimately have "finite {L l c |l c. c \<in> set F \<and> l \<in> c}" by fastforce
   then show ?thesis unfolding literals_of_sat_def by simp
  qed

fun lift_xc_element :: "('a \<Rightarrow> bool) \<Rightarrow> 'a xc_element \<Rightarrow> bool" ("_\<Up>" 60) where
 "lift_xc_element \<sigma> (V v) = \<sigma> v" |
 "lift_xc_element \<sigma> (C c) \<longleftrightarrow> (\<exists> l\<in>c. (\<sigma>\<up>) l)" |
 "lift_xc_element \<sigma> (L x c) = (\<sigma>\<up>) x"

end