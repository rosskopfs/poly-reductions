\<^marker>\<open>creator Bilel Ghorbel\<close>
chapter \<open>Complexity classes definitions\<close>
paragraph \<open>Summary\<close>
text \<open>

\<bullet> Stating definitions of P AND NP based on the defined abstractions AND bounds.
\<bullet> Sanity checks: Proving that problems having polyreductions to P/NP problems are P/NP
\<bullet> Stating definitions of NP-Hard AND NP-complete using polyreductions
\<close>
theory Complexity_Classes
  imports
    "Karp21.Polynomial_Growth_Functions"
    "Karp21.SAT_Definition" Bounds Abstractions
    "IMP_Reductions"

begin
paragraph \<open>Conventions\<close>
text \<open>
We consider natural numbers sets as our languages.
A Complexity class is a set containing languages hence a set containing natural numbers sets.

hence we are only interested with decision problems over natural numbers.
\<close>
subsection \<open>P\<close>
paragraph \<open>Definition\<close>
text \<open>A language is \<in> P iff. it can be decided by a program that is polynomially time bounded.\<close>
definition P :: "lang set" where
  "P \<equiv> {L. \<exists>c. poly_time_bounded c  [''input''] \<and> decides c L}"

subsection \<open>NP\<close>
paragraph \<open>Polyverifiers\<close>
text \<open>A polyverifier c of a language L is a verifier of that language that has following bounds:
\<bullet> polynomial time bound respectively to the input AND certificate size.
\<bullet> polynomial valid-certificate bound
 \<close>
definition is_poly_verif :: "com \<Rightarrow> lang \<Rightarrow> bool" where
  "is_poly_verif c L \<equiv> is_verif c L \<and> poly_time_bounded c [''input'',''certificate'']
                                  \<and> poly_certif_bounded c"

paragraph \<open>NP definition\<close>
text \<open>NP is the set of languages having a polyverifier\<close>
definition NP :: "lang set" where
"NP \<equiv> {L. \<exists>c. is_poly_verif c L}"




subsection \<open>Reduction to a P/NP problem\<close>
lemma p_sanity:
  assumes "D' \<in> P" "poly_reduces D D'"
  shows "D \<in> P"
  using assms apply (auto simp add: P_def poly_reduces_def)
proof
  fix g f
  assume assms: "is_polyreduction f D D'"
    "poly_time_bounded g [''input'']" "decides g D'"
  show "poly_time_bounded (f;;g)[''input''] \<and> decides (f;;g) D "
  proof
    show "poly_time_bounded (f;;g)[''input'']"
      using assms is_polyreduction_def reduction_poly by auto
  next
    show "decides (f;;g) D"
      using assms(1) assms(3) reduction_decision_correct is_polyreduction_def by blast
  qed
qed


lemma np_sanity:
  assumes "poly_reduces D D'" "D' \<in> NP"
  shows "D \<in> NP"
proof -
  from assms(1) obtain f
    where f_def: "is_reduction f D D'" "poly_time_bounded f [''input'']"
                                      "poly_result_bounded f [''input''] [''input'']"
    using is_polyreduction_def poly_reduces_def by auto
  from assms(2) obtain g
    where g_def: "is_verif g D'" "poly_time_bounded g [''input'',''certificate'']"
                                "poly_certif_bounded g"
    using NP_def is_poly_verif_def by blast
  from f_def(1) have cf:"cons_certif f" by (simp add: is_reduction_def)
  moreover from g_def(1) have "\<forall>y z. \<exists>r. verif g y z r " by (simp add: is_verif_def)
  ultimately have "poly_certif_bounded (f;;g)" using f_def(3) g_def(3)
      poly_result_bounded_poly_certif_bounded   by blast
  moreover from f_def(1) g_def(1) have "is_verif (f;;g) D" using reduction_verification_correct by simp
  moreover from f_def(2) have p1: "poly_time_bounded f [''input'',''certificate'']"
    using extend_poly_time_bounded
    by fastforce
  from f_def(3) have p2:
              "poly_result_bounded f [''input'',''certificate''][''input'',''certificate'']"
    using assms(2) cf cons_certif_poly_result_bounded by blast
  from g_def(2)  p1 p2 have p3:"poly_time_bounded (f;;g)[''input'',''certificate'']"
    using reduction_poly by blast
  ultimately show  ?thesis using NP_def is_poly_verif_def  by auto
qed

subsection \<open>NP-Hard AND NP-Complete Definitions\<close>
definition NP_hard :: "lang set" where
"NP_hard \<equiv> {L'. \<forall>L\<in>NP. poly_reduces L L'}"

definition NP_complete :: "lang set" where
"NP_complete \<equiv> NP_hard \<inter> NP"

subsection \<open>Defining NP using P\<close>
paragraph \<open>Idea AND Intuition\<close>
text \<open>
Disclaimer: This is not a proof of P = NP.

Verifiers AND deciders are a lot a like. While within P, it's about the existence of polynomially
bounded decider, within NP it's about polynomially bounded verifiers.
Hence if we encode the input AND certificate in one value. We could do the work of a verifier
using a decider who's able to decode them.
\<close>

paragraph \<open>Assumptions\<close>
text \<open>
For this definition we will need an encoding/entupling AND decoding/detupling programs that convert
couples of natural numbers into one natural number AND vice versa.

Since we don't care what the programs are as long they satisfy some assumptions/properties
we just state them AND assume them IN a local context.

A next step could be proving that the cantor pairing function satifies them.

The assumptions are:
\<bullet> the entupling happens in polynomial time.
\<bullet> the detupling happens in polynomial time AND produces a couple that's polynomially bounded w.r.t
the bitsize of the encoded couple.
\<bullet> The entupling AND detupling are both total and computable. The computation always gives a result
that is depending only the input.
\<bullet> entupling AND detupling are inverse operations.
\<close>
definition rev_verif:: "com \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" where
  "rev_verif c x z r \<equiv> comp c [(''input'',r)] [(''input'',x),(''certificate'',z)]"

locale NP_using_P =
  fixes entuple::com
  fixes detuple::com
  assumes en_bound:"poly_time_bounded entuple [''input'',''certificate'']"
                  "poly_result_bounded entuple [''input'',''certificate''] [''input'']"
   and de_bound:"poly_time_bounded detuple [''input'']"
                            "poly_result_bounded detuple [''input''] [''input'',''certificate'']"
   and total_en:"\<forall>x z. \<exists>r. verif entuple x z r"
   and total_de:"\<forall>r. \<exists>x z. rev_verif detuple x z r"
   and  equiv_en_de:"verif entuple x z r \<longleftrightarrow> rev_verif detuple x z r "
begin

paragraph \<open>Certificate language of a verifier\<close>
text \<open>This is in the heart of the alternative definition.

The certificate language of a verifier v is the set of encoded couples of input AND certificate that
are accepted by v.
\<close>
definition cert_lang_of :: "com \<Rightarrow> lang" where
  "cert_lang_of v \<equiv> {tuple. \<exists>x z. verif entuple x z tuple \<and> verif v x z 0 }"


text \<open>Helping lemma\<close>
lemma verif_entuple_det:
  assumes "verif entuple x z r"
  assumes "verif entuple x' z' r"
  shows "x=x' \<and> z=z'"
  using assms equiv_en_de rev_verif_def comp_comp verif_def
  by (smt comp_det list.inject list.simps(9) prod.sel(1) prod.sel(2))

text \<open>Proving that the certificate language of a polyverifier is decidable in polynomial time,
we would obtain that an alternative definition for NP.\<close>

paragraph \<open>Helping lemmas \<close>

lemma NP_to_P: "is_verif v L \<Longrightarrow> decides (detuple;;v) (cert_lang_of v)"
proof (auto simp add: decides_def)
  fix tu
  assume asm:"is_verif v L"
  then obtain x z where xz_def: "rev_verif detuple x z tu" using total_de by blast
  hence entuple_rel:"verif entuple x z tu" using equiv_en_de by simp
  obtain r where r_def: "verif v x z r" using asm is_verif_def by metis
  have "(tu \<in> cert_lang_of v) = (0 = r)"
  proof
    assume "tu \<in> cert_lang_of v"
    then obtain x' z'  where def':"verif entuple x' z' tu" " verif v x' z' 0"
      using cert_lang_of_def by blast
    then have "x=x'" "z=z'" using entuple_rel verif_entuple_det by auto
    hence "verif v x z 0" using def'(2) by simp
    thus "0=r" using r_def verif_def comp_comp
      by (smt comp_det list.inject list.map(2) prod.sel(1) prod.sel(2))
  next
    assume "0 = r"
    thus " tu \<in> cert_lang_of v" using r_def entuple_rel cert_lang_of_def by blast
  qed
  moreover have "comp' (detuple;; v) tu r" using r_def xz_def
                      verif_def rev_verif_def comp'_def comp_comp by auto
  ultimately show " \<exists>r. comp' (detuple;; v) tu r \<and> (tu \<in> cert_lang_of v) = (r = 0)"
    by blast
qed

lemma P_to_NP:
  assumes "decides c L'"
  assumes "\<forall>x. x\<in>L \<longleftrightarrow> (\<exists>tu z. tu\<in>L' \<and> verif entuple x z tu)"
  shows "is_verif (entuple;;c) L"
proof (auto simp add:is_verif_def)
  fix x z
  obtain tu where "verif entuple x z tu " using total_en by auto
  moreover obtain r where "comp' c tu r" using assms(1) decides_def by blast
  ultimately have "verif (entuple;;c) x z r" using verif_def comp'_def comp_comp by simp
  thus "\<exists>r. verif (entuple;; c) x z r" by auto
next
  fix x
  assume "x\<in>L"
  then obtain tu z where tu_z_def: "tu \<in> L'" "verif entuple x z tu"  using assms(2) by blast
  hence r_def:"comp' c tu 0"  using assms(1) decides_def by blast
  from tu_z_def(2) r_def(1) have "verif (entuple;; c) x z 0"
      using verif_def comp'_def comp_comp by simp
  thus "\<exists>z. verif (entuple;; c) x z 0" using r_def by blast
next
  fix x z r
  assume asm: "verif (entuple;; c) x z 0"
  obtain tu where tu_def: "verif entuple x z tu" using total_en by blast
  moreover obtain r' where r'_def:"comp' c tu r'" "(tu \<in> L') \<longleftrightarrow> (r' = 0)"
    using assms(1) decides_def by blast
  ultimately have "verif (entuple;;c) x z r'" using verif_def comp'_def comp_comp by simp
  hence "r'= 0" using asm verif_def comp_det
    by (smt fstI iszero_primfun_list.simps(1) iszero_primfun_list.simps(2)
                  iszero_primfun_list_iff list.simps(9))
  hence "tu \<in> L'" using r'_def(2) by simp
  thus  "x\<in>L" using tu_def assms(2) by blast
qed
paragraph \<open>NP alternative definition \<close>
text \<open>A language is NP, iff. there EXISTS a  language of  (input,certifiate) tuples IN P, such that
1) every input existing IN the language has at least one corresponding certificate that is
    polynomially bounded
2) the set of inputs is  exactly the NP language.
 \<close>
theorem NP_alter_def:
      "L \<in> NP \<longleftrightarrow> (\<exists>L' p. L' \<in> P \<and> poly p \<and>
                    certif_bounded_to_goal entuple p L' \<and>
                  (\<forall>x. x\<in>L \<longleftrightarrow> (\<exists>tu z. tu\<in>L' \<and> verif entuple x z tu)))"

proof safe
  assume " L \<in> NP"
  then obtain v where v_def: "is_poly_verif v L" using NP_def by blast
  let ?L' = "cert_lang_of v"
  obtain p where p_def: "poly p" "certif_bounded v p"
    using v_def is_poly_verif_def poly_certif_bounded_def by blast
  have "decides (detuple;;v) ?L'" using v_def is_poly_verif_def NP_to_P by blast
  moreover have "poly_time_bounded (detuple;;v) [''input'']"
    using v_def is_poly_verif_def de_bound reduction_poly by blast
  ultimately have "?L' \<in> P" using P_def by blast

  moreover have "\<forall>x.(x \<in> L) = (\<exists>tu z. tu \<in> ?L' \<and> verif entuple x z tu)"
  proof auto
    fix x
    assume "x \<in> L"
    then obtain z where zr_def: "verif v x z 0"
      using v_def is_poly_verif_def is_verif_def by force
    obtain tu where tu_def:"verif entuple x z tu" using total_en by blast
    hence "tu \<in> ?L'" using zr_def cert_lang_of_def by blast
    thus "\<exists>tu. tu \<in> ?L' \<and> (\<exists>z. verif entuple x z tu)" using tu_def  by blast
  next
    fix x tu z
    assume asm: "tu \<in> ?L'" "verif entuple x z tu"
    then obtain x' z' where defs: "verif entuple x' z' tu"  "verif v x' z' 0"
      using cert_lang_of_def by auto
    hence "x=x'" "z=z'" using asm(2) verif_entuple_det by auto
    thus "x \<in> L" using defs(2) v_def is_poly_verif_def is_verif_def by blast
  qed

  moreover have "certif_bounded_to_goal entuple p ?L'"
    unfolding certif_bounded_to_goal_def
  proof safe
    fix tu x z
    assume asm:"tu \<in> cert_lang_of v" " verif entuple x z tu"
    then obtain x' z' where def': "verif entuple x' z' tu" "verif v x' z' 0"
      using cert_lang_of_def by blast
    hence "x' =x " using asm(2)  verif_entuple_det by blast
    hence "verif v x z' 0" using def'(2) by blast
    then obtain z'' where def'':"verif v x z'' 0" "bit_length z'' \<le> p (bit_length x)"
      using p_def certif_bounded_def def'(2) certif_bounded_to_goal_def by auto
    obtain tu'' where tu''_def: "verif entuple x z'' tu''" using total_en by fast
    moreover have "tu'' \<in> cert_lang_of v "
      using def''(1) def''(2) tu''_def cert_lang_of_def by blast
    ultimately  show
      " \<exists>z' tu'. verif entuple x z' tu' \<and> bit_length z' \<le> p (bit_length x) \<and>  tu' \<in> cert_lang_of v"
      using def''(2) def''(2) by blast
  qed
  ultimately show "\<exists>L' p. L' \<in> P \<and> poly p \<and> certif_bounded_to_goal entuple p L'
                       \<and> (\<forall>x. (x \<in> L) = (\<exists>tu z. tu \<in> L' \<and> verif entuple x z tu))"
    using p_def(1) by force
next
  fix L' p
  assume L'_def: "L' \<in> P" "poly p" "certif_bounded_to_goal entuple p L'"
          "\<forall>x. (x \<in> L) = (\<exists>tu z. tu \<in> L' \<and>  verif entuple x z tu)"
  then obtain c where c_def:"decides c L'" "poly_time_bounded c [''input'']" using P_def by blast

  from L'_def(4) c_def(1) P_to_NP have "is_verif (entuple;;c) L" by auto

  moreover have  "poly_time_bounded (entuple;;c)[''input'',''certificate'']"
    using c_def(2) en_bound reduction_poly by simp

  moreover have "poly_certif_bounded (entuple;;c)"
  proof (auto simp add: poly_certif_bounded_def certif_bounded_def)
    have "(\<forall>x. (\<exists>z r. verif (entuple;; c) x z 0) \<longrightarrow>
             (\<exists>z r. verif (entuple;; c) x z 0 \<and> bit_length z \<le> p (bit_length x)))"
    proof auto
      fix x z
      assume asm: "verif (entuple;;c) x z 0"
      obtain tu where tu_def: "verif entuple x z tu" using total_en by blast
      obtain r' where r'_def:"comp' c tu r'" "tu \<in> L' \<longleftrightarrow> r'= 0" using c_def decides_def by blast
      from tu_def r'_def(1) have "verif (entuple;;c) x z r'"
        using comp_comp verif_def comp'_def by simp
      hence "r' = 0" using asm(1) verif_def comp_det
                 by (smt fstI iszero_primfun_list.simps(1) iszero_primfun_list.simps(2)
                  iszero_primfun_list_iff list.simps(9))
      hence "tu \<in> L'" using r'_def(2)  asm by blast
      then obtain tu' z'
        where tuz'_def: "tu' \<in> L'" " verif entuple x z' tu'" "bit_length z' \<le> p (bit_length x)"
        using L'_def(3)[unfolded certif_bounded_to_goal_def] tu_def by blast
      then obtain r''
        where r''_def: "comp' c tu' r''" "tu' \<in> L' \<longleftrightarrow> r''=0" using c_def decides_def by blast
      have "verif (entuple;;c) x z' r''" using r''_def(1) tuz'_def(2) verif_def comp'_def comp_comp
        by blast
      moreover have "r'' = 0" using r''_def(2) tuz'_def(1) by simp
      ultimately show "\<exists>z. verif (entuple;; c) x z 0 \<and> bit_length z \<le> p (bit_length x)"
        using tuz'_def(3) by blast
    qed
    thus "\<exists>p. poly p \<and> certif_bounded_to_goal (entuple;; c) p {0}"
      using L'_def(2) certif_bounded_to_goal_def by auto
  qed
  ultimately show "L \<in> NP" using NP_def is_poly_verif_def by auto
qed

end

end

