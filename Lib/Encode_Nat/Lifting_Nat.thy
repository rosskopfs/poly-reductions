theory Lifting_nat
  imports Main "HOL-Library.Nat_Bijection" "HOL-Library.Simps_Case_Conv"
begin

section \<open>Lifting to \<^typ>\<open>nat\<close>\<close>

definition cr_nat :: "('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool" where
  "cr_nat Abs_nat \<equiv> (\<lambda>n l. n = Abs_nat l)"

text \<open>
  This locale needs to instantiated for every base type.
  The first axiom probably has to be proved by the user.
  The second axiom is already proved automatically.
\<close>
locale type_definition_nat =
  fixes Abs_nat :: "'a \<Rightarrow> nat"
  fixes Rep_nat :: "nat \<Rightarrow> 'a"

  assumes inj_Rep_nat: "inj Abs_nat"
  assumes Abs_nat_Rep_nat_id: "\<And>x. Rep_nat (Abs_nat x) = x"
begin

lemma typedef_nat: "type_definition Abs_nat Rep_nat (Abs_nat ` UNIV)"
  apply(unfold_locales)
    apply(use inj_Rep_nat Abs_nat_Rep_nat_id in auto)
  done

definition "cr_nat' \<equiv> cr_nat Abs_nat"

lemmas typedef_nat_transfer[OF typedef_nat cr_nat'_def[unfolded cr_nat_def], transfer_rule] =
  typedef_bi_unique typedef_right_unique typedef_left_unique typedef_right_total

lemma cr_nat_Abs_nat[transfer_rule]:
  "cr_nat' (Abs_nat x) x"
  unfolding cr_nat'_def cr_nat_def by simp

end

abbreviation "fstP x \<equiv> fst (prod_decode x)"
abbreviation "sndP x \<equiv> snd (prod_decode x)"


section \<open>Lifting from \<^typ>\<open>bool\<close>\<close>

\<comment> \<open>Provided by the datatype compiler\<close>
definition Abs_nat_bool :: "bool \<Rightarrow> nat" where
  "Abs_nat_bool b \<equiv> if b then 1 else 0"

\<comment> \<open>Provided by the datatype compiler\<close>
definition Rep_nat_bool :: "nat \<Rightarrow> bool" where
  "Rep_nat_bool n \<equiv> if n = 0 then False else True"

global_interpretation nat_bool:
  type_definition_nat Abs_nat_bool Rep_nat_bool
  defines cr_nat_bool_raw_def: cr_nat_bool = nat_bool.cr_nat'
  apply(unfold_locales)
   apply(auto simp: inj_on_def Abs_nat_bool_def Rep_nat_bool_def)
  done
lemmas cr_nat_bool_def = nat_bool.cr_nat'_def[unfolded cr_nat_def]

lemma Domainp_nat_bool_rel[transfer_domain_rule]:
  "Domainp cr_nat_bool = (\<lambda>x. x = 0 \<or> x = 1)"
  unfolding cr_nat_bool_def Abs_nat_bool_def by auto

context includes lifting_syntax
begin

\<comment> \<open>Needs to be provided by the datatype compiler\<close>
lemma cr_nat_bool_True[transfer_rule]:
  "cr_nat_bool 1 True"
  unfolding cr_nat_bool_def Abs_nat_bool_def by auto

\<comment> \<open>Needs to be provided by the datatype compiler\<close>
lemma cr_nat_bool_False[transfer_rule]:
  "cr_nat_bool 0 False"
  unfolding cr_nat_bool_def Abs_nat_bool_def by auto

lemma nat_bool_rel_conj[transfer_rule]:
  "(cr_nat_bool ===> cr_nat_bool ===> cr_nat_bool) min (\<and>)"
  unfolding cr_nat_bool_def Abs_nat_bool_def
  by (auto simp: rel_fun_def)

lemma nat_bool_rel_disj[transfer_rule]:
  "(cr_nat_bool ===> cr_nat_bool ===> cr_nat_bool) max (\<or>)"
  unfolding cr_nat_bool_def Abs_nat_bool_def
  by (auto simp: rel_fun_def)

end

schematic_goal
  shows "cr_nat_bool ?t (a \<and> (b \<or> c))"
  apply transfer_prover_start
       apply transfer_step+
  apply (rule HOL.refl)
  done


section \<open>Lifting from \<^typ>\<open>'a list\<close>\<close>

\<comment> \<open>Already provided by the datatype compiler\<close>
fun Rep_nat_list where
  "Rep_nat_list Rep_nat [] = prod_encode (0, 0)"
| "Rep_nat_list Rep_nat (x # xs) =
    prod_encode (1, prod_encode (Rep_nat x, Rep_nat_list Rep_nat xs))"

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

\<comment> \<open>Already provided by the datatype compiler\<close>
function Abs_nat_list where
  "Abs_nat_list Abs_nat n = case_list_nat [] (\<lambda>x xs. Abs_nat x # Abs_nat_list Abs_nat xs) n"
  by auto
termination
proof -
  have "0 < fstP n \<Longrightarrow> sndP (sndP n) < n" for n
    apply (cases n) apply(auto)
     apply (metis le_prod_encode_1 linorder_not_le prod.exhaust_sel prod_decode_inverse)
    by (metis bot_nat_0.not_eq_extremum fstP_lt le_prod_encode_2 less_add_same_cancel1 not_less_eq
        order_less_le_trans plus_1_eq_Suc prod.exhaust_sel prod_decode_inverse sndP_lt)
  then show ?thesis
    apply (relation "measure (\<lambda>(Abs_nat, n). size n)")
     apply (auto)
    done
qed
declare Abs_nat_list.simps[simp del]

\<comment> \<open>User has to provide this to the datatype compiler\<close>
lemma inj_Rep_nat_list:
  "inj Rep_nat \<Longrightarrow> inj (Rep_nat_list Rep_nat)"
  apply(intro injI)
  subgoal for xs ys
    apply(induction xs ys rule: list_induct2')
       apply(auto dest: inj_onD)
    done
  done

\<comment> \<open>Already provided by the datatype compiler\<close>
lemma Abs_nat_list_Rep_nat_list:
  assumes "\<And>x. Abs_nat (Rep_nat x) = x"
  shows "Abs_nat_list Abs_nat (Rep_nat_list Rep_nat xs) = xs"
  using assms
proof(induction xs)
  case Nil
  then show ?case
    apply(subst Abs_nat_list.simps)
    apply(auto simp: case_list_nat_def)
    done
next
  case (Cons x xs)
  then show ?case
    apply(subst Abs_nat_list.simps)
    apply(auto simp: case_list_nat_def)
    done
qed

fun rev_tr :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_tr acc [] = acc"
| "rev_tr acc (x # xs) = rev_tr (x # acc) xs"

case_of_simps rev_tr_case_def: rev_tr.simps

context
  fixes Rep_nat :: "'a \<Rightarrow> nat"
  fixes Abs_nat :: "nat \<Rightarrow> 'a"
begin

\<comment> \<open>Can be lifted with Kevin's transport framework\<close>
definition "rev_tr_nat acc xs \<equiv>
  Rep_nat_list Rep_nat (rev_tr (Abs_nat_list Abs_nat acc) (Abs_nat_list Abs_nat xs))"

context
  assumes inj_Rep_nat: "inj Rep_nat"
  assumes Abs_nat_Rep_nat: "\<And>x. Abs_nat (Rep_nat x) = x"
begin

global_interpretation nat_list: type_definition_nat "Rep_nat_list Rep_nat" "Abs_nat_list Abs_nat"
  defines cr_nat_list_raw_def: cr_nat_list = "nat_list.cr_nat'"
  using inj_Rep_nat_list[OF inj_Rep_nat] Abs_nat_list_Rep_nat_list[OF Abs_nat_Rep_nat]
  by (unfold_locales)
lemmas cr_nat_list_def = nat_list.cr_nat'_def[unfolded cr_nat_def]

context includes lifting_syntax
begin

\<comment> \<open>
  Needs to be provided by the datatype compiler.
  We probably should introduce definitions for the nat versions of
  each constructor.
\<close>
lemma cr_nat_list_Nil[transfer_rule]:
  "cr_nat_list (prod_encode (0, 0)) []"
  unfolding cr_nat_list_def by simp

\<comment> \<open>Needs to be provided by the datatype compiler\<close>
lemma cr_nat_list_Cons[transfer_rule]:
  "(cr_nat Rep_nat ===> cr_nat_list ===> cr_nat_list)
    (\<lambda>x xs. prod_encode (1, prod_encode (x, xs))) (#)"
  unfolding cr_nat_list_def cr_nat_def by (auto simp: rel_fun_def)

\<comment> \<open>Needs to be provided by the datatype compiler\<close>
lemma cr_nat_list_case_list[transfer_rule]:
  "(R ===> (cr_nat Rep_nat ===> cr_nat_list ===> R) ===> cr_nat_list
  ===> R) case_list_nat case_list"
  unfolding cr_nat_def cr_nat_list_def case_list_nat_def
  by (auto simp: rel_fun_def split: prod.splits list.splits)

end

\<comment> \<open>Can be proved with Kevin's transport framework\<close>
lemma rev_tr_nat_lifting[transfer_rule]:
  includes lifting_syntax
  shows "(cr_nat_list ===> cr_nat_list ===> cr_nat_list) rev_tr_nat rev_tr"
  unfolding rev_tr_nat_def cr_nat_list_def
  using Abs_nat_list_Rep_nat_list[OF Abs_nat_Rep_nat]
  apply(auto simp: rel_fun_def)
  done

schematic_goal rev_tr_nat_synth:
  assumes [transfer_rule]: "cr_nat_list accn (Abs_nat_list Abs_nat accn)"
  assumes [transfer_rule]: "cr_nat_list xsn (Abs_nat_list Abs_nat xsn)"
  shows "cr_nat_list ?t (rev_tr (Abs_nat_list Abs_nat accn) (Abs_nat_list Abs_nat xsn))"
  apply (subst rev_tr_case_def)
  apply transfer_prover_start
        apply transfer_step+
  apply (rule HOL.refl)
  done

\<comment> \<open>Final theorem that can be passed to the IMP compiler\<close>
lemma rev_tr_nat_synth_def:
  assumes "accn = Rep_nat_list Rep_nat acc"
  assumes "xsn = Rep_nat_list Rep_nat acc"
  shows "rev_tr_nat accn xsn
    = case_list_nat accn (\<lambda>x3a. rev_tr_nat (prod_encode (1, prod_encode (x3a, accn)))) xsn"
  using assms rev_tr_nat_def rev_tr_nat_synth[unfolded cr_nat_list_def]
  by (metis nat_list.Abs_nat_Rep_nat_id)
  
end

end

end
