theory Lifting_Nat
  imports Main "HOL-Library.Nat_Bijection" "HOL-Library.Simps_Case_Conv"
begin

section \<open>Lifting to \<^typ>\<open>nat\<close>\<close>

class lift_nat =
  fixes Abs_nat :: "'a \<Rightarrow> nat"
  fixes Rep_nat :: "nat \<Rightarrow> 'a"
  assumes Rep_nat_Abs_nat_id[simp]: "\<And>x. Rep_nat (Abs_nat x) = x"
begin

lemma inj_Abs_nat: "inj Abs_nat"
  using Rep_nat_Abs_nat_id unfolding inj_def by metis

definition cr_nat :: "nat \<Rightarrow> 'a \<Rightarrow> bool" where
  "cr_nat \<equiv> (\<lambda>n l. n = Abs_nat l)"

lemma typedef_nat: "type_definition Abs_nat Rep_nat (Abs_nat ` UNIV)"
  by (unfold_locales) auto
 
lemmas typedef_nat_transfer[OF typedef_nat cr_nat_def, transfer_rule] =
  typedef_bi_unique typedef_right_unique typedef_left_unique typedef_right_total

lemma cr_nat_Abs_nat[transfer_rule]:
  "cr_nat (Abs_nat x) x"
  unfolding cr_nat_def by simp

end

text \<open>
  This locale needs to instantiated for every base type.
  The first axiom probably has to be proved by the user.
  The second axiom is already proved automatically.
\<close>

abbreviation "fstP x \<equiv> fst (prod_decode x)"
abbreviation "sndP x \<equiv> snd (prod_decode x)"


section \<open>Lifting from \<^typ>\<open>bool\<close>\<close>

instantiation bool :: lift_nat
begin

definition Abs_nat_bool_def: "Abs_nat b \<equiv> if b then 1 else 0"

definition Rep_nat_bool_def: "Rep_nat n \<equiv> if n = 0 then False else True"

instance 
  apply (intro_classes)
   apply (auto simp: Abs_nat_bool_def Rep_nat_bool_def)
  done

end

lemma Domainp_nat_bool_rel[transfer_domain_rule]:
  "Domainp (cr_nat :: _ \<Rightarrow> bool \<Rightarrow> _) = (\<lambda>x. x = 0 \<or> x = 1)"
  unfolding cr_nat_def Abs_nat_bool_def by auto

context includes lifting_syntax
begin

\<comment> \<open>Needs to be provided by the datatype compiler\<close>
lemma cr_nat_bool_True[transfer_rule]:
  "cr_nat 1 True"
  unfolding cr_nat_def Abs_nat_bool_def by auto

\<comment> \<open>Needs to be provided by the datatype compiler\<close>
lemma cr_nat_bool_False[transfer_rule]:
  "cr_nat 0 False"
  unfolding cr_nat_def Abs_nat_bool_def by auto

lemma nat_bool_rel_conj[transfer_rule]:
  "(cr_nat ===> cr_nat ===> cr_nat) min (\<and>)"
  unfolding cr_nat_def Abs_nat_bool_def
  by (auto simp: rel_fun_def)

lemma nat_bool_rel_disj[transfer_rule]:
  "(cr_nat ===> cr_nat ===> cr_nat) max (\<or>)"
  unfolding cr_nat_def Abs_nat_bool_def
  by (auto simp: rel_fun_def)

end

schematic_goal
  shows "cr_nat ?t (a \<and> (b \<or> c))"
  apply transfer_prover_start
       apply transfer_step+
  apply (rule HOL.refl)
  done


section \<open>Lifting from \<^typ>\<open>'a list\<close>\<close>

\<comment> \<open>Already provided by the datatype compiler\<close>
definition "case_list_nat f g xs \<equiv>
  let
    (t, as) = prod_decode xs
  in
    if t = 0
      then f
      else let (x, xs) = prod_decode as in g x xs
"

lemma case_list_nat_cong[fundef_cong]:
  assumes "xs1 = xs2"
  assumes "fstP xs2 = 0 \<Longrightarrow> f1 = f2"
  assumes "fstP xs2 \<noteq> 0
    \<Longrightarrow> g1 (fstP (sndP xs2)) (sndP (sndP xs2)) = g2 (fstP (sndP xs2)) (sndP (sndP xs2))"
  shows "case_list_nat f1 g1 xs1 = case_list_nat f2 g2 xs2"
  using assms unfolding case_list_nat_def
  by (auto split: prod.splits simp: Let_def)

lemma fst_prod_decode_aux_lt:
  "0 < n \<Longrightarrow> fst (prod_decode_aux k n) < k + n"
proof(induction k n rule: prod_decode_aux.induct)
  case (1 k m)
  then show ?case
    apply (subst prod_decode_aux.simps)
    apply simp
    using prod_decode_aux.simps by fastforce
qed

lemma snd_prod_decode_aux_lt:
  "1 < n \<Longrightarrow> snd (prod_decode_aux k n) < k + n"
proof(induction k n rule: prod_decode_aux.induct)
  case (1 k m)
  then show ?case
    apply (subst prod_decode_aux.simps)
    apply simp
    using prod_decode_aux.simps by fastforce
qed

lemma fstP_lt: "0 < n \<Longrightarrow> fstP n < n"
  unfolding prod_decode_def using fst_prod_decode_aux_lt[where ?k=0] by simp

lemma sndP_lt: "1 < n \<Longrightarrow> sndP n < n"
  unfolding prod_decode_def using snd_prod_decode_aux_lt[where ?k=0] by simp

instantiation list :: (lift_nat) lift_nat
begin

\<comment> \<open>Already provided by the datatype compiler\<close>
fun Abs_nat_list :: "'a list \<Rightarrow> nat" where
  "Abs_nat_list [] = prod_encode (0, 0)"
| "Abs_nat_list (x # xs) =
    prod_encode (1, prod_encode (Abs_nat x, Abs_nat_list xs))"

\<comment> \<open>Already provided by the datatype compiler\<close>
function Rep_nat_list :: "nat \<Rightarrow> 'a list" where
  "Rep_nat_list n = case_list_nat [] (\<lambda>x xs. Rep_nat x # Rep_nat_list xs) n"
  by auto
termination
proof -
  have "0 < fstP n \<Longrightarrow> sndP (sndP n) < n" for n
    apply (cases n) apply(auto)
     apply (metis le_prod_encode_1 linorder_not_le prod.exhaust_sel prod_decode_inverse)
    by (metis bot_nat_0.not_eq_extremum fstP_lt le_prod_encode_2 less_add_same_cancel1 not_less_eq
        order_less_le_trans plus_1_eq_Suc prod.exhaust_sel prod_decode_inverse sndP_lt)
  then show ?thesis
    apply (relation "measure (\<lambda>n. size n)")
     apply (auto)
    done
qed
declare Rep_nat_list.simps[simp del]

instance
proof(intro_classes)
  show "Rep_nat (Abs_nat xs) = xs" for xs :: "'a list"
    apply (induction xs)
     apply (subst Rep_nat_list.simps, simp add: case_list_nat_def)+
    done
qed

end

fun rev_tr :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_tr acc [] = acc"
| "rev_tr acc (x # xs) = rev_tr (x # acc) xs"

case_of_simps rev_tr_case_def: rev_tr.simps

\<comment> \<open>Can be lifted with Kevin's transport framework\<close>
definition rev_tr_nat :: "'a::lift_nat itself \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "rev_tr_nat _ acc xs \<equiv> (Abs_nat :: 'a list \<Rightarrow> nat) (rev_tr (Rep_nat acc) (Rep_nat xs))"

context includes lifting_syntax
begin

\<comment> \<open>
  Needs to be provided by the datatype compiler.
  We probably should introduce definitions for the nat versions of
  each constructor.
\<close>
lemma cr_nat_list_Nil[transfer_rule]:
  "cr_nat (prod_encode (0, 0)) []"
  unfolding cr_nat_def by simp

\<comment> \<open>Needs to be provided by the datatype compiler\<close>
lemma cr_nat_list_Cons[transfer_rule]:
  "(cr_nat ===> cr_nat ===> cr_nat) (\<lambda>x xs. prod_encode (1, prod_encode (x, xs))) (#)"
  unfolding cr_nat_def by (auto simp: rel_fun_def)

\<comment> \<open>Needs to be provided by the datatype compiler\<close>
lemma cr_nat_list_case_list[transfer_rule]:
  "(R ===> (cr_nat ===> cr_nat ===> R) ===> cr_nat ===> R) case_list_nat case_list"
  unfolding cr_nat_def case_list_nat_def
  by (auto simp: rel_fun_def split: prod.splits list.splits)

\<comment> \<open>Can be proved with Kevin's transport framework\<close>
lemma rev_tr_nat_lifting[transfer_rule]:
  includes lifting_syntax
  shows "(cr_nat ===> cr_nat ===> cr_nat) (rev_tr_nat TYPE('a::lift_nat)) (rev_tr :: 'a list \<Rightarrow> _)"
  unfolding rev_tr_nat_def cr_nat_def
  apply(auto simp: rel_fun_def)
  done

end

schematic_goal rev_tr_nat_synth:
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a list \<Rightarrow> bool) accn (Rep_nat accn)"
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a list \<Rightarrow> bool) xsn (Rep_nat xsn)"
  shows "cr_nat ?t ((rev_tr :: 'a::lift_nat list \<Rightarrow> _) (Rep_nat accn) (Rep_nat xsn))"
  apply (subst rev_tr_case_def)
  apply transfer_prover_start
        apply transfer_step+
  apply (rule HOL.refl)
  done

lemma rev_tr_nat_synth_def:
  fixes acc :: "'a::lift_nat list" and xs :: "'a list"
  assumes "accn = Abs_nat acc"
  assumes "xsn = Abs_nat xs"
  shows "rev_tr_nat TYPE('a) accn xsn
    = case_list_nat accn (\<lambda>x3a. rev_tr_nat TYPE('a) (prod_encode (1, prod_encode (x3a, accn)))) xsn"
  apply(rule HOL.trans[OF _ rev_tr_nat_synth[unfolded cr_nat_def, symmetric]])
  apply(use assms in \<open>simp_all add: rev_tr_nat_def\<close>)
  done

\<comment> \<open>Final theorem that can be passed to the IMP compiler\<close>
thm rev_tr_nat_synth_def[unfolded case_list_nat_def]

end
