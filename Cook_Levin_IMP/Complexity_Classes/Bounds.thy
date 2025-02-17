theory Bounds
  imports Bit_Length  Abstractions "IMP.Big_StepT"  "Karp21.Polynomial_Growth_Functions"
begin
paragraph \<open>Bounding functions\<close>
text \<open> We restrict/over-approximate the behaviour of our programs by defining
 an upper bound to the execution time/result etc. depending on the input size.
The upper bound function is hence nothing but a function over natural numbers (input size)
to natural numbers (time steps/result size/ certificate size)\<close>

type_synonym bound_fun = "nat \<Rightarrow> nat"
paragraph \<open>Bit size of register set\<close>
text \<open> used to refer to input size / result size.\<close>
fun bit_size :: "val list \<Rightarrow> nat" where
"bit_size [] = 0"|
"bit_size (l#ls) = bit_length l + bit_size ls"

lemma bit_size_concat : "bit_size (xs@ys) = bit_size xs + bit_size ys"
  by (induction xs) auto

subsection \<open>Time bounded programs\<close>
paragraph \<open>Definition\<close>
text \<open>We are only interested in programs that always terminate.
A program c is bounded by a function p, if it does always terminate AND the termination time t is
always less than p(l). l being the input size.\<close>
definition time_bounded :: "com \<Rightarrow> vname list \<Rightarrow> bound_fun \<Rightarrow> bool" where
"time_bounded c l p \<equiv> (\<forall>s. \<exists>t s'. ((c,s) \<Rightarrow>\<^bsup>t\<^esup> s') \<and> t \<le> p (bit_size (map s l)))"

lemma time_boundedI:
  assumes "\<And>s. \<exists>t s'. ((c,s) \<Rightarrow>\<^bsup>t\<^esup> s') \<and> t \<le> p (bit_size (map s l))"
  shows "time_bounded c l p"
  using assms unfolding time_bounded_def by auto

definition poly_time_bounded :: "com \<Rightarrow> vname list \<Rightarrow> bool" where
"poly_time_bounded c l \<equiv> \<exists>p. poly p \<and> time_bounded c l p"

lemma poly_time_boundedD:
  assumes "poly_time_bounded c l"
  obtains p where "poly p" "time_bounded c l p"
  using assms unfolding poly_time_bounded_def by auto

lemma poly_time_boundedI:
  assumes "poly p" "time_bounded c l p"
  shows "poly_time_bounded c l"
  using assms unfolding poly_time_bounded_def by auto

subsection \<open>Result bounded programs \<close>
paragraph \<open>Definition\<close>
text \<open>Given the result's registers depend only on the input register.
That output/result is bounded by p(l) , l being the bit-size of the input.\<close>
definition result_bounded :: "com \<Rightarrow> vname list \<Rightarrow> vname list \<Rightarrow> bound_fun \<Rightarrow> bool" where
"result_bounded c input output p \<equiv> \<forall>x. length x = length input \<longrightarrow>
                                      (\<exists>r. length r = length output \<and>
                                               comp c (zip input x) (zip output r) \<and>
                                               bit_size r  \<le> p (bit_size x))"
definition poly_result_bounded :: "com \<Rightarrow> vname list \<Rightarrow> vname list \<Rightarrow> bool" where
"poly_result_bounded c input output \<equiv> \<exists>p. poly p \<and> result_bounded c input output p"

subsection \<open>Sequencing two polynomially bounded programs \<close>
lemma reduction_poly:
  assumes "poly_time_bounded f nxs" "poly_time_bounded g nys"  "poly_result_bounded f nxs nys"
  shows "poly_time_bounded (f;;g) nxs"
proof -
  from assms(1) obtain pf where pf_props: "poly pf" "time_bounded f nxs pf"
    apply(rule poly_time_boundedD) ..
  from assms(2) obtain pg where pg_props: "poly pg" "time_bounded g nys pg"
    apply(rule poly_time_boundedD) ..
  from assms(3) obtain pd  where "poly pd" and pd_fact: "\<forall>x. length x = length nxs
    \<longrightarrow> (\<exists>r. length r = length nys \<and> comp f (zip nxs x) (zip nys r) \<and>
                                                     bit_size r \<le> pd (bit_size x)) "
    using poly_result_bounded_def result_bounded_def by auto
  let ?p = "\<lambda>x. pf x + (make_mono pg o pd) x"
  have "poly ?p"
    using poly_add pf_props(1) pg_props(1) poly_compose `poly pd` poly_make_mono_iff by metis
  moreover have "time_bounded (f;; g) nxs ?p"
  proof (intro time_boundedI)
    fix s
    obtain x::"val list" where x_def: "x = map s nxs"  "length x = length nxs"  by simp
    then obtain sf tf where stepf:"(f,s) \<Rightarrow>\<^bsup> tf \<^esup> sf" "tf \<le> pf (bit_size x)"
      using pf_props(2)  by (simp add: time_bounded_def) blast
    obtain y where stepd: "comp f (zip nxs x) (zip nys y)"
      "bit_size y \<le> pd (bit_size x)" "length y = length nys" using pd_fact x_def(2)
      by auto
    then obtain s1 t1 where step':"(f,s) \<Rightarrow>\<^bsup> t1 \<^esup> s1" "map s1 nys = y" using comp_def x_def
        stepd(2) zip_eq_conv  by (smt list.map_comp)
    hence "s1 = sf" using big_step_t_determ2 stepf(1) by simp
    then obtain  sg tg where g_def: "(g,sf)\<Rightarrow>\<^bsup> tg \<^esup> sg" "tg \<le> pg(bit_size y)"
      using pg_props(2) time_bounded_def step'(2) by blast
    hence "tg \<le> make_mono pg (bit_size y)" using le_trans by blast
    moreover have "make_mono pg (bit_size y) \<le> make_mono pg (pd (bit_size x))"
      using stepd(2) mono_make_mono[of pg] incseq_def  by blast
    ultimately have t2_ineq: "tg \<le> (make_mono pg o pd)(bit_size x)" by fastforce
    hence "(f;;g,s) \<Rightarrow>\<^bsup> tf+tg \<^esup> sg"
      "tf+tg \<le> pf (bit_size x) + (make_mono pg o pd) (bit_size x)"
      using stepf(1) g_def (1) apply blast
      using add_mono stepf(2) t2_ineq by blast
    thus "\<exists>t s'. ((f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and>
             t \<le> pf (bit_size (map s nxs)) + (make_mono pg \<circ> pd) (bit_size (map s nxs)) "
      using x_def by blast
  qed
  ultimately show ?thesis
    by (rule poly_time_boundedI)
qed

subsection \<open>Valid certificate bounds\<close>
paragraph \<open>Definition\<close>
text \<open>
Given a program c AND an input x, a valid certificate z is a certificate for which the verifier c,
will return 0.
p is valid-certificate-bounded iff for every input x that has a corresponding valid certificate,
there EXISTS a valid certificate limited by p(l), l being the input size (''input'' register)
\<close>

definition certif_bounded_to_goal :: "com \<Rightarrow> bound_fun \<Rightarrow> lang \<Rightarrow> bool" where
"certif_bounded_to_goal c p L \<equiv>  \<forall>x. (\<exists>z r. verif c x z r \<and> r \<in> L)
                             \<longrightarrow> (\<exists>z r. verif c x z r \<and> bit_length z \<le> p (bit_length x) \<and> r \<in> L)"

definition certif_bounded :: "com \<Rightarrow> bound_fun \<Rightarrow> bool" where
"certif_bounded c p \<equiv> certif_bounded_to_goal c p {0} "

definition poly_certif_bounded :: "com \<Rightarrow> bool" where
"poly_certif_bounded c \<equiv> \<exists>p. poly p \<and> certif_bounded c p "

lemma summing: "bit_length x = bit_size [x]" by auto

lemma cons_certif_effect :
  assumes "comp f [(''input'',x)] [(''input'',y)]" "cons_certif f"
  shows   "comp f [(''input'',x),(''certificate'',z)] [(''input'',y),(''certificate'',z)]"
proof (auto simp add: comp_def)
  fix s
  assume " x = s ''input'' " "z = s ''certificate''"
  then obtain t s' where "(f, s) \<Rightarrow>\<^bsup> t \<^esup> s'" "s' ''input''= y" using assms(1) comp_def by auto
  then show "\<exists>t s'. (f, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = y \<and> s' ''certificate'' = s ''certificate''"
    using assms(2) cons_certif_def by metis
qed

lemma extend_time_bounded :
  assumes "time_bounded f xs p"
  shows "time_bounded f (xs@ys) (make_mono p)"
proof (auto simp add: time_bounded_def)
  fix s
  from assms obtain t s' where def:"(f, s) \<Rightarrow>\<^bsup> t \<^esup> s'" "t \<le> p (bit_size (map s xs))"
    apply (auto simp add: time_bounded_def) by blast
  from def(2) have "t \<le> make_mono p (bit_size (map s xs))"
    using le_trans by blast
  hence " t \<le> make_mono p (bit_size (map s xs) + bit_size (map s ys))"
    by (meson incseq_def le_add1 le_trans mono_make_mono)
  thus " \<exists>t. (\<exists>s'. (f, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and>
             t \<le> make_mono p (bit_size(map s xs @ map s ys))"
    using def(1) bit_size_concat by auto
qed

lemma extend_poly_time_bounded:
  assumes "poly_time_bounded f xs "
  shows "poly_time_bounded f (xs@ys)"
proof -
  from assms obtain p where "poly p" "time_bounded f xs p" by (auto simp add: poly_time_bounded_def)
  hence "time_bounded f (xs@ys) (make_mono p) "  "poly (make_mono p)"
    by(auto simp add: extend_time_bounded  poly_make_mono_iff)
  thus ?thesis by (auto simp add:poly_time_bounded_def)
qed


lemma cons_certif_result_bounded:
  assumes "result_bounded f [''input''] [''input''] p" "cons_certif f"
  shows "result_bounded f [''input'',''certificate''] [''input'',''certificate'']
                                                                           (\<lambda>x. make_mono p x + x) "
proof (auto simp add:result_bounded_def)
  fix xs::"val list"
  assume "length xs = Suc (Suc 0)"
  then obtain x z where xs_def: "xs = [x,z]"
    by (metis (no_types, lifting) Suc_length_conv length_0_conv)
  have "length [x] = length [''input'']" by auto
  then obtain ys where ys_def: "comp f [(''input'',x)] (zip [''input''] ys)"
                        "length ys = length [''input'']"
                        "bit_size ys \<le> p (bit_length x)"
    using assms(1) result_bounded_def
    by (smt summing zip.simps(1) zip_Cons_Cons)
  from ys_def(2) obtain y where y_def: "ys = [y]"
    by (metis Suc_length_conv length_0_conv length_Cons)
  hence "comp f [(''input'',x)] [(''input'',y)]" using ys_def(1) by auto
  hence whole:"comp f [(''input'',x),(''certificate'',z)] [(''input'',y),(''certificate'',z)]"
    using assms(2) cons_certif_effect by fast
  obtain r where r_def: "r = [y,z]" by simp
  hence "length r = Suc (Suc 0)" by auto
  moreover have "comp f (zip [''input'', ''certificate''] xs)
              (zip [''input'', ''certificate''] r)" using r_def whole xs_def by auto
  moreover have "bit_length y \<le> p(bit_length x)" using y_def ys_def(3) by auto
  hence "bit_length y + bit_length z \<le> p (bit_length x) + bit_length x + bit_length z"
    by auto
  hence "bit_length y + bit_length z \<le> make_mono p (bit_length x)
                                               + bit_length x + bit_length z"
    by (simp add: le_make_mono order_trans)
  hence "bit_length y + bit_length z \<le> make_mono p (bit_length x + bit_length z)
                                               + bit_length x + bit_length z"
    by (meson add_right_mono incseq_def le_add1 le_trans mono_make_mono)
  hence "bit_size r \<le> make_mono p (bit_size xs) + bit_size xs"  using xs_def r_def by force
  ultimately show " \<exists>r. length r = Suc (Suc 0) \<and>
             comp f (zip [''input'', ''certificate''] xs)
              (zip [''input'', ''certificate''] r) \<and>
             bit_size r \<le> make_mono p (bit_size xs) + bit_size xs" by blast
qed
lemma cons_certif_poly_result_bounded:
  assumes "poly_result_bounded f [''input''] [''input'']" "cons_certif f"
  shows "poly_result_bounded f [''input'',''certificate''] [''input'',''certificate'']"
proof -
  from assms(1) obtain p where p_def: "poly p" "result_bounded f [''input''] [''input''] p"
    by (auto simp add:poly_result_bounded_def)
  hence "result_bounded f [''input'',''certificate''] [''input'',''certificate'']
                                                                       (\<lambda>x. make_mono p x +x)"
    using assms(2) cons_certif_result_bounded by fast
  moreover have "poly (\<lambda>x. make_mono p x + x)" using p_def(1)
    by (simp add: poly_add poly_linear poly_make_mono_iff)
  ultimately show ?thesis by (auto simp add:poly_result_bounded_def)
qed
lemma result_bounded_certif_bounded :
  assumes "result_bounded f [''input''] [''input''] q"
          "cons_certif f" "certif_bounded g p" "\<forall>y z. \<exists>r. verif g y z r "
        shows "certif_bounded (f;;g) (make_mono p o q)"
proof (auto simp add: certif_bounded_def certif_bounded_to_goal_def)
  fix x z
  assume local_asm:"verif (f;; g) x z 0"
  have "length [''input''] = length [x]" "[(''input'',x)] = zip [''input''] [x]"
    by auto
  then obtain ys where ys_def: "comp f ( zip [''input''] [x]) (zip [''input''] ys)"
              "bit_size ys \<le> q (bit_size [x])" "length ys = length [''input''] "
                      using assms(1) result_bounded_def summing
                      by metis

 from ys_def(3) obtain y where y_def: "ys = [y]"
   by (metis length_0_conv length_Suc_conv)
  have  red_part: "comp f  [(''input'',x),(''certificate'',z)] [(''input'',y),(''certificate'',z)]"
    using assms(2) cons_certif_effect y_def ys_def(1) by auto
  from assms(4) obtain r where r'_def: "verif g y z r"  using certif_bounded_def by presburger
  moreover from red_part y_def ys_def(1) r'_def assms(1) have "verif (f;; g) x z r"
    using comp_comp by (auto simp add:verif_def)
  hence  "r = 0" using local_asm comp_det apply(auto simp add:verif_def) by fastforce
  ultimately obtain z'  where  z'r'_def: " verif g y z' 0" "bit_length z' \<le> p (bit_length y)"
    using assms(3) certif_bounded_def certif_bounded_to_goal_def by auto
  from z'r'_def(2) have "bit_length z' \<le> make_mono p (bit_length y)"
    using le_trans less_imp_le_nat by blast
  moreover have "make_mono p (bit_length y) \<le> make_mono p (q (bit_length x))"
    using ys_def(2) mono_make_mono y_def by (simp add: incseqD)
  ultimately have "bit_length z' \<le>  make_mono p (q (bit_length x)) " by simp
  moreover  have  red_part':
    "comp f  [(''input'',x),(''certificate'',z')] [(''input'',y),(''certificate'',z')]"
    using assms(2) cons_certif_effect y_def ys_def(1) by auto
  hence "verif (f;;g) x z' 0"  using z'r'_def(1) comp_comp by (auto simp add:verif_def)
  ultimately show "\<exists>z. verif (f;; g) x z 0 \<and> bit_length z \<le> make_mono p (q (bit_length x))"
    using z'r'_def(2) by blast
qed

lemma poly_result_bounded_poly_certif_bounded:
  assumes "poly_result_bounded f [''input''] [''input'']"
                  "cons_certif f" "poly_certif_bounded g"
                          "\<forall>y z. \<exists>r. verif g y z r "
  shows "poly_certif_bounded (f;;g)"
proof (auto simp add: poly_certif_bounded_def)

  show "\<exists>p. poly p \<and> certif_bounded (f;; g) p "
  proof -
    from assms(1) obtain q where q_def: "poly q" "result_bounded f  [''input''] [''input''] q"
      using poly_result_bounded_def by blast
    from  assms(3) obtain p where p_def: "poly p" "certif_bounded g p" using poly_certif_bounded_def
      by meson
    let ?p = "make_mono p o q"
    from q_def(1) p_def(1) have "poly ?p"
      by (simp add: poly_compose poly_make_mono_iff)
    moreover have "certif_bounded (f;;g) ?p" using q_def(2) p_def(2) assms(2) assms(4)
     result_bounded_certif_bounded by simp
    ultimately show ?thesis by blast
  qed
qed

lemma result_bounded_compose:
  assumes "result_bounded f xs ys pf" "result_bounded g ys zs pg"
  shows "result_bounded (f;;g) xs zs (make_mono pg o pf)"
  apply(auto simp add:result_bounded_def)
proof -
  fix x::"val list"
  assume "length x = length xs"
  then obtain y z
    where yz_def:"comp f (zip xs x) (zip ys y)" "comp g (zip ys y) (zip zs z)"
                "bit_size y \<le> pf (bit_size x)" "bit_size z \<le> pg(bit_size y)"
                "length z = length zs" "length y = length ys"
   using assms result_bounded_def by blast
  hence  "comp (f;;g) (zip xs x) (zip zs z)" using comp_comp by simp
  moreover have  "bit_size z \<le> make_mono pg (bit_size y)" using yz_def(4) le_trans by blast
  hence  " bit_size z \<le> make_mono pg (pf (bit_size x))"
    using yz_def mono_make_mono  le_trans monoD by blast
  ultimately show "\<exists>r. length r = length zs \<and>comp (f;; g) (zip xs x) (zip zs r)
                      \<and> bit_size r \<le> make_mono pg (pf (bit_size x))" using yz_def(5) by auto
qed


lemma poly_result_compose :
  assumes "poly_result_bounded f xs ys" "poly_result_bounded g ys zs"
  shows "poly_result_bounded (f;;g) xs zs"
   proof -
     obtain pf pg where pf_pg_def: "poly pf" "poly pg" "result_bounded f xs ys pf"
                                    "result_bounded g ys zs pg"
      using assms poly_result_bounded_def by auto
    have "poly (make_mono pg o pf)"
      by (simp add: pf_pg_def(1) pf_pg_def(2) poly_compose poly_make_mono_iff)
    moreover have "result_bounded (f;;g) xs zs (make_mono pg o pf)"
      using result_bounded_compose pf_pg_def by auto
    ultimately show ?thesis by (auto simp add:poly_result_bounded_def)
  qed


end