\<^marker>\<open>creator Bilel Ghorbel\<close>
chapter \<open>defining reductions using IMP- programs\<close>
paragraph \<open>Summary\<close>
text \<open>
Reductions could be informally seen as transitions from a decision problem to another.

Although some existing theory makes a general definition of reductions using functions,
we do restrict our definition to computable reductions AND hence use IMP- programs instead 
of functions
\<close>
theory "IMP-_Reductions"
  imports Abstractions Bounds 
begin

subsection \<open>Definition\<close>
paragraph \<open>Defining computable reductions using IMP-\<close>
text \<open>A reduction is a program that always computes a result based uniquely on the input.
Hence computing a total function.
for a reduction c from D to D',  an input x AND a result r we have: x \<in> D iff r \<in>D'.

As a convention, the reduction should conserve the certificate. 
This convention is necessary while working on verifiers.\<close>


definition is_reduction :: "com \<Rightarrow> lang \<Rightarrow> lang \<Rightarrow> bool" where
  "is_reduction c D D' \<equiv> cons_certif c \<and>( \<forall>x. \<exists>r. comp' c x r \<and>( x \<in> D \<longleftrightarrow> r \<in> D'))"

lemma is_reductionI:
  assumes "cons_certif c"
    and "\<And>x. \<exists>r. comp' c x r \<and>( x \<in> D \<longleftrightarrow> r \<in> D')"
  shows "is_reduction c D D'"
  using assms unfolding is_reduction_def by auto

subsection \<open>Reductions composed with deciders/verifiers/other reductions\<close>

lemma reduction_decision_correct: 
  assumes "is_reduction f D D'" "decides g D'"
  shows "decides (f;;g) D "
proof (auto simp add: is_reduction_def decides_def)
  fix x
  obtain y where f_part:"comp' f x y" " x \<in> D \<longleftrightarrow> y \<in> D'" using assms(1) is_reduction_def by metis
  obtain z where g_part:"comp' g y z" "y \<in> D' \<longleftrightarrow> z = 0" using assms(2) decides_def by meson
  have "comp' (f;;g) x z" using comp'_comp' f_part(1)_g_part(1) by auto
  moreover have "x \<in>D \<longleftrightarrow> 0 = z" using f_part(2) g_part(2) by blast
  ultimately show "\<exists>r. comp' (f;; g) x r \<and> (x \<in> D) = (r = 0)" by blast
qed

lemma reduction_verification_correct:
  assumes "is_reduction f D D'" "is_verif g D'"
  shows "is_verif (f;;g) D"     
proof (intro is_verifI)
  fix x  z
  from assms(1) obtain y where  "comp' f x y " using is_reduction_def by meson
  moreover have "cons_certif f" using assms(1) is_reduction_def  by simp
  ultimately have 
    "comp f [(''input'',x),(''certificate'',z)] [(''input'',y),(''certificate'',z)]"
    using  cons_certif_effect by(auto simp add: comp'_def)
  moreover from assms(2) obtain r where  "verif g y z r" using is_verif_def by meson
  ultimately show "\<exists>r. verif (f;;g) x z r" using comp_comp cons_certif_def verif_def
    by meson
next
  fix x 
  from assms(1) obtain y where y_def:  "comp' f x y " " (x\<in>D) = (y\<in>D')" 
    using is_reduction_def by meson
  moreover have "cons_certif f" using assms(1) is_reduction_def  by simp
  ultimately have 
    as1: "\<forall>z. comp f [(''input'',x),(''certificate'',z)] [(''input'',y),(''certificate'',z)]"
    using  cons_certif_effect by(auto simp add:comp'_def)
  from assms(2) have "(y\<in>D')  = (\<exists>z. verif g y z 0)" 
    using is_verif_def by simp 
  hence  as2:"(x \<in> D) = (\<exists>z. verif g y z 0) " using y_def(2) by simp
  show "(x \<in> D) = (\<exists>z. verif (f;; g) x z 0)"
  proof safe
    assume "x \<in> D"
    then obtain z where "verif g y z 0" using as2 by blast
    moreover have "comp f [(''input'',x),(''certificate'',z)] [(''input'',y),(''certificate'',z)]"
      using as1 by simp
    ultimately have" verif (f;; g) x z 0" using as1 comp_comp verif_def by blast
    thus "\<exists>z. verif (f;; g) x z 0" by auto
  next
    fix z
    assume asm: "verif (f;; g) x z 0"
    from as1
    have " comp f [(''input'',x),(''certificate'',z)] [(''input'',y),(''certificate'',z)]"
      by auto
    moreover from assms(2) obtain r where r_def:  "verif g y z r" using is_verif_def by meson
    ultimately have "verif (f;; g) x z r" using verif_def comp_comp by meson
    hence "r=0" using asm verif_def comp_det
      by (smt fst_conv 
          iszero_primfun_list.simps(1) iszero_primfun_list.simps(2) list.simps(9) pair_list_eqI)
    hence "verif g y z 0" using r_def by auto
    thus "x \<in> D" using as2 by blast
  qed
qed


lemma is_reduction_compose:
  assumes "is_reduction f D D'" "is_reduction g D' D''"
  shows "is_reduction (f;;g) D D''"
  unfolding is_reduction_def
  apply safe
  subgoal using assms apply(simp add: cons_certif_def is_reduction_def) by fastforce
proof -
  fix x
   obtain y where y_def: "comp' f x y" "(x\<in>D) =(y\<in>D')"
     using assms(1) by (auto simp add:is_reduction_def)
   obtain z where z_def: "comp' g y z" "(y\<in>D') =(z\<in>D'')"
     using assms(2) by (auto simp add:is_reduction_def)    
   have  "comp' (f;; g) x z  \<and> (x \<in> D) = (z \<in> D'')"
     using y_def z_def comp_comp comp'_def by simp
   thus  "\<exists>r. comp' (f;; g) x r \<and> (x \<in> D) = (r \<in> D'')" by blast
 qed

subsection \<open>Polynomial reductions\<close>
paragraph \<open>Definition\<close>
text \<open>
A polyreduction is a reduction that is also polynomially bounded in time (in most literature)

A necessary condition also for polyreduction is to be polynomially result-bounded
(otherwise polyreduction would not be transitive)
Yet, this condition is generally omitted in most literature, as TM is the commonly used model
of computation, where the limitation in time implies a limitation in space. 
As it is not the case in our model, we choose to add explicitly this condition.

It is yet worth the mention, that given that program is a reduction hence
depends on only one register. the time bound would imply a result bound.
This yet would involve a bit of digging into the semantics to be proven.
This could be done as a future step in the project.
\<close>

definition is_polyreduction :: "com \<Rightarrow> lang \<Rightarrow> lang  \<Rightarrow> bool" where
"is_polyreduction c D D' \<equiv> poly_time_bounded c [''input'']
                               \<and> is_reduction c D D'
                               \<and> poly_result_bounded c [''input''] [''input''] "

paragraph \<open>poly-reductions as a binary relation over languages\<close>

definition poly_reduces :: "lang \<Rightarrow> lang \<Rightarrow> bool" where
"poly_reduces D D' \<equiv> \<exists>c. is_polyreduction c D D'"

paragraph \<open>Properties of the polyreduction relation\<close>

text \<open>Reflexivity\<close>

lemma "poly_reduces D D"
  apply(simp add: poly_reduces_def is_polyreduction_def)
proof
  let ?c=SKIP
  show "poly_time_bounded ?c [''input''] \<and> is_reduction ?c D D 
              \<and> poly_result_bounded ?c [''input''] [''input'']" 
    apply (auto)
    apply(auto simp add:poly_time_bounded_def)
    subgoal
    proof
      let ?p = "(\<lambda>x. 1)"
      have "poly ?p" by simp 
      moreover have "time_bounded SKIP [''input''] ?p "
        using time_bounded_def by auto 
      ultimately show "poly ?p \<and> time_bounded SKIP [''input''] ?p" by simp
    qed
     apply (auto simp add: is_reduction_def cons_certif_def comp_def poly_result_bounded_def)
    subgoal for x
    proof -
      have "(\<forall>s. s ''input'' = x \<longrightarrow> (\<exists>t s'. (SKIP, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = x)) \<and> (x \<in> D) = (x \<in> D)"
        by auto
      thus ?thesis by (auto simp add:comp'_def comp_def)
    qed
  proof
    let ?p= "(\<lambda>a .a)"
    show "poly ?p \<and> result_bounded SKIP [''input''] [''input''] ?p" 
      apply(auto simp add:poly_linear result_bounded_def)
      subgoal for x 
      proof -
        assume "length x = Suc 0"
        then have "length x = Suc 0 \<and> comp SKIP (zip [''input''] x) (zip [''input''] x) \<and> bit_size x \<le> bit_size x "
          by (auto simp add: comp'_def comp_def)
        thus  ?thesis by auto
      qed
      done
  qed
qed

text \<open>Transitivity\<close>

lemma "poly_reduces_trans":
  assumes "poly_reduces D D'"  "poly_reduces D' D''" 
  shows "poly_reduces D D''"
proof -
  from assms obtain f g where fg_def: "is_polyreduction f D D'" "is_polyreduction g D' D''" 
    by (auto simp add:poly_reduces_def)
  let ?c= "f;;g"
  have  "is_polyreduction ?c D D''" 
    apply (auto simp add:is_polyreduction_def  reduction_poly)
    using fg_def apply (simp add: is_polyreduction_def reduction_poly)
    using reduction_poly apply blast 
    using fg_def is_reduction_compose apply (simp add: is_polyreduction_def) apply blast
    using fg_def apply (auto simp add:is_polyreduction_def reduction_poly)
    using poly_result_compose apply blast
    done
  thus "poly_reduces D D''" by (auto simp add:poly_reduces_def)
qed


end

