theory Lifting_Nat
  imports
    Main
    "HOL-Library.Nat_Bijection"
    "HOL-Library.Simps_Case_Conv"
    Encode_Nat
    Transport.Transport_Prototype
    Transport.HOL_Alignment_Functions
begin

unbundle lifting_syntax


(* TODO: still necessary? *)
lemma Domainp_nat_bool_rel[transfer_domain_rule]:
  "Domainp (cr_nat :: _ \<Rightarrow> bool \<Rightarrow> _) = (\<lambda>x. x = False_nat \<or> x = True_nat)"
  unfolding cr_nat_def Abs_nat_bool.simps
  by (auto split:bool.split)

(* TODO: still necessary? *)
lemma nat_bool_rel_conj[transfer_rule]:
  "(cr_nat ===> cr_nat ===> cr_nat) max (\<and>)"
  unfolding cr_nat_def Abs_nat_bool.simps
  by (simp add: pair_def True_nat_def prod_encode_0 rel_fun_def split: bool.split)

(* TODO: still necessary? *)
lemma nat_bool_rel_disj[transfer_rule]:
  "(cr_nat ===> cr_nat ===> cr_nat) min (\<or>)"
  unfolding cr_nat_def Abs_nat_bool.simps
  by (simp add: pair_def True_nat_def prod_encode_0 rel_fun_def split: bool.split)

(* Example? *)
schematic_goal
  shows "cr_nat ?t (a \<and> (b \<or> c))"
  by transfer_prover



(* lift_nat *)

fun rev_tr :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_tr acc [] = acc"
| "rev_tr acc (x # xs) = rev_tr (x # acc) xs"

case_of_simps rev_tr_case_def: rev_tr.simps
print_theorems


(*PER for lift_nat class*)
lemmas lift_nat_partial_equivalence_rel_equivalence = iffD1[OF
  transport.partial_equivalence_rel_equivalence_right_left_iff_partial_equivalence_rel_equivalence_left_right
  lift_nat_type_def.partial_equivalence_rel_equivalenceI]

(*register PER*)
declare lift_nat_partial_equivalence_rel_equivalence[per_intro]
(*nicer relatedness theorem output*)
declare Galois_eq_range_Abs_nat_Rep_nat_eq_inv_cr_nat[trp_relator_rewrite]

(*only relation-respecting functions can be transported*)
lemma rev_tr_related_self [trp_in_dom]:
  "(lift_nat_type_def.R \<Rrightarrow> lift_nat_type_def.R \<Rrightarrow> lift_nat_type_def.R) rev_tr rev_tr"
  by auto

trp_term rev_tr_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where x = "rev_tr :: ('a :: lift_nat) list \<Rightarrow> _"
  by trp_prover

(*here are the theorems*)
print_theorems

lemma rev_tr_nat_lifting[transfer_rule]:
  "(cr_nat ===> cr_nat ===> cr_nat) (rev_tr_nat TYPE('a::lift_nat)) (rev_tr :: 'a list \<Rightarrow> _)"
  unfolding rel_fun_eq_Fun_Rel_rel
  by (fact rev_tr_nat_related'[unfolded rel_inv_Dep_Fun_Rel_rel_eq[symmetric] rel_inv_iff_rel])

schematic_goal rev_tr_nat_synth:
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a list \<Rightarrow> bool) accn (Rep_nat accn)"
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a list \<Rightarrow> bool) xsn (Rep_nat xsn)"
  shows "cr_nat ?t ((rev_tr :: 'a::lift_nat list \<Rightarrow> _) (Rep_nat accn) (Rep_nat xsn))"
  apply (subst rev_tr_case_def)
  by transfer_prover


lemma rev_tr_nat_synth_def:
  fixes acc :: "'a::lift_nat list" and xs :: "'a list"
  assumes "accn = Abs_nat acc"
  assumes "xsn = Abs_nat xs"
  shows "rev_tr_nat TYPE('a) accn xsn
    = case_list_nat accn (\<lambda>x3a. rev_tr_nat TYPE('a) (Cons_nat x3a accn)) xsn"
  apply(rule HOL.trans[OF _ rev_tr_nat_synth[unfolded cr_nat_def, symmetric]])
    apply(use assms in \<open>simp_all add: rev_tr_nat_app_eq\<close>)
  done


\<comment> \<open>Final theorem that can be passed to the IMP compiler\<close>
thm rev_tr_nat_synth_def[unfolded case_list_nat_def]



fun elemof :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "elemof _ [] = False"
| "elemof y (x#xs) = (if (y = x) then True else elemof y xs)"

case_of_simps elemof_case_def: elemof.simps

lemma elemof_related_self [trp_in_dom]:
  "(lift_nat_type_def.R \<Rrightarrow> lift_nat_type_def.R \<Rrightarrow> lift_nat_type_def.R) elemof elemof"
  by auto

trp_term elemof_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where x = "elemof :: ('a :: lift_nat) \<Rightarrow> _"
  by trp_prover

lemma elemof_nat_lifting[transfer_rule]:
  shows "(cr_nat ===> cr_nat ===> cr_nat) (elemof_nat TYPE('a::lift_nat)) (elemof :: 'a \<Rightarrow> _)"
  unfolding rel_fun_eq_Fun_Rel_rel
  by (fact elemof_nat_related'[unfolded rel_inv_Dep_Fun_Rel_rel_eq[symmetric] rel_inv_iff_rel])

schematic_goal elemof_nat_synth:
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a \<Rightarrow> bool) xn (Rep_nat xn)"
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a list \<Rightarrow> bool) xsn (Rep_nat xsn)"
  shows "cr_nat ?t ((elemof :: 'a::lift_nat \<Rightarrow> _) (Rep_nat xn) (Rep_nat xsn))"
  apply (subst elemof_case_def)
  by transfer_prover

lemma elemof_nat_synth_def:
  fixes x :: "'a::lift_nat " and xs :: "'a list"
  assumes "xn = Abs_nat x"
  assumes "xsn = Abs_nat xs"
  shows "elemof_nat TYPE('a) xn xsn
    = case_list_nat False_nat (\<lambda>y ys. if xn = y then True_nat else elemof_nat TYPE('a) xn ys) xsn"
  apply(rule HOL.trans[OF _ elemof_nat_synth[unfolded cr_nat_def, symmetric]])
    apply(use assms in \<open>simp_all add: elemof_nat_app_eq\<close>)
  done

thm elemof_nat_synth_def[unfolded case_list_nat_def]

lemma if_related_self [trp_in_dom]:
  "(lift_nat_type_def.R \<Rrightarrow> lift_nat_type_def.R \<Rrightarrow> lift_nat_type_def.R \<Rrightarrow> lift_nat_type_def.R)
  HOL.If HOL.If"
  by auto

trp_term If_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where x = "HOL.If :: bool \<Rightarrow> ('a :: lift_nat) \<Rightarrow> _"
  by trp_prover

lemma If_nat_lifting[transfer_rule]: "(cr_nat ===> cr_nat ===> cr_nat ===> cr_nat)
  (If_nat TYPE('a::lift_nat)) (HOL.If :: bool \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a)"
  unfolding rel_fun_eq_Fun_Rel_rel
  by (fact If_nat_related'[unfolded rel_inv_Dep_Fun_Rel_rel_eq[symmetric] rel_inv_iff_rel])

lemma If_case_def: "HOL.If c t f = (case c of True \<Rightarrow> t | False \<Rightarrow> f)" by simp

schematic_goal If_nat_synth:
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> bool \<Rightarrow> bool) c (Rep_nat c)"
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a \<Rightarrow> bool) t (Rep_nat t)"
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a \<Rightarrow> bool) f (Rep_nat f)"
  shows "cr_nat ?t ((HOL.If :: bool \<Rightarrow> 'a::lift_nat \<Rightarrow> 'a \<Rightarrow> 'a) (Rep_nat c) (Rep_nat t) (Rep_nat f))"
  apply (subst If_case_def)
  by transfer_prover

lemma If_nat_synth_def:
  fixes c :: "bool" and t :: "'a::lift_nat" and f :: "'a"
  assumes "cn = Abs_nat c"
  assumes "tn = Abs_nat t"
  assumes "fn = Abs_nat f"
  shows "If_nat TYPE('a) cn tn fn = case_bool_nat tn fn cn"
  apply(rule HOL.trans[OF _ If_nat_synth[unfolded cr_nat_def, symmetric]])
  unfolding If_nat_app_eq assms by simp+

thm If_nat_synth_def[unfolded case_bool_nat_def]


fun takeWhile :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "takeWhile P [] = []" |
  "takeWhile P (x # xs) = (if P x then x # takeWhile P xs else [])"

case_of_simps takeWhile_case_def: takeWhile.simps

unbundle no_comp_syntax

lemma takeWhile_related_self [trp_in_dom]:
  "((lift_nat_type_def.R \<Rrightarrow> lift_nat_type_def.R) \<Rrightarrow> lift_nat_type_def.R \<Rrightarrow> lift_nat_type_def.R)
  takeWhile takeWhile"
  by auto

trp_term takeWhile_nat :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where x = "takeWhile :: (('a :: lift_nat) \<Rightarrow> bool) \<Rightarrow> _"
  by trp_prover

lemma takeWhile_nat_lifting[transfer_rule]:
  "((cr_nat ===> cr_nat) ===> cr_nat ===> cr_nat)
  (takeWhile_nat TYPE('a::lift_nat)) ((takeWhile :: ('a \<Rightarrow> bool) \<Rightarrow> _))"
  unfolding rel_fun_eq_Fun_Rel_rel
  by (fact takeWhile_nat_related'[unfolded rel_inv_Dep_Fun_Rel_rel_eq[symmetric] rel_inv_iff_rel])


schematic_goal takeWhile_nat_synth:
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a list \<Rightarrow> bool) xsn (Rep_nat xsn)"
  assumes [transfer_rule]:"(cr_nat ===> cr_nat) P_nat P"
  shows "cr_nat ?t ((takeWhile :: ('a::lift_nat \<Rightarrow> bool) \<Rightarrow> _) P (Rep_nat xsn))"
  apply (subst takeWhile_case_def)
  by transfer_prover

lemma takeWhile_nat_synth_def:
  fixes P :: "'a::lift_nat \<Rightarrow> bool" and xs :: "'a list"
  assumes "(cr_nat ===> cr_nat) P_nat P"
  assumes "xsn = Abs_nat xs"
  shows "takeWhile_nat TYPE('a) P_nat xsn
    = case_list_nat Nil_nat (\<lambda>x3a x2ba. If_nat TYPE('a list) (P_nat x3a)
          (Cons_nat x3a (takeWhile_nat TYPE('a) P_nat x2ba)) Nil_nat) xsn"
  apply(rule HOL.trans[OF _ takeWhile_nat_synth[unfolded cr_nat_def, symmetric]])
  using assms apply(simp add: takeWhile_nat_app_eq rel_fun_def cr_nat_def)+
  done

thm takeWhile_nat_synth_def[unfolded case_list_nat_def]

fun head :: "'a list \<Rightarrow> 'a" where
  "head [] = undefined" |
  "head (x # _) = x"

case_of_simps head_case_def: head.simps

definition head_nat :: "'a::lift_nat itself \<Rightarrow> nat \<Rightarrow> nat" where
  "head_nat _ xsn \<equiv> (Abs_nat :: 'a \<Rightarrow> nat) (head (Rep_nat xsn))"

lemma head_nat_lifting[transfer_rule]:
  shows "(cr_nat ===> cr_nat) (head_nat TYPE('a::lift_nat)) (head :: 'a list \<Rightarrow> _)"
  unfolding head_nat_def cr_nat_def
  by(simp add: rel_fun_def)

schematic_goal head_nat_synth:
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a list \<Rightarrow> bool) xsn (Rep_nat xsn)"
  shows "cr_nat ?t ((head :: 'a::lift_nat list \<Rightarrow> _) (Rep_nat xsn))"
  apply (subst head_case_def)
  by transfer_prover

lemma head_nat_synth_def:
  fixes xs :: "'a::lift_nat list"
  assumes "xsn = Abs_nat xs"
  shows "head_nat TYPE('a) xsn
    = case_list_nat (Abs_nat (undefined::'a)) (\<lambda>x2a x1a. x2a) xsn"
  apply(rule HOL.trans[OF _ head_nat_synth[unfolded cr_nat_def, symmetric]])
  using assms apply(simp add: head_nat_def rel_fun_def cr_nat_def)+
  done
thm head_nat_synth_def[unfolded case_list_nat_def]

fun append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "append xs [] = xs" |
  "append xs ys = rev_tr ys (rev_tr [] xs)"


case_of_simps append_case_def: append.simps

definition append_nat :: "'a::lift_nat itself \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "append_nat _ xsn ysn \<equiv> (Abs_nat :: 'a list \<Rightarrow> nat) (append (Rep_nat xsn) (Rep_nat ysn))"

lemma append_nat_lifting[transfer_rule]:
  shows "(cr_nat ===> cr_nat ===> cr_nat) (append_nat TYPE('a::lift_nat))
  (append :: 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list)"
  by(simp add: append_nat_def rel_fun_def Fun.comp_def cr_nat_def)

schematic_goal append_nat_synth:
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a list \<Rightarrow> bool) xsn (Rep_nat xsn)"
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a list \<Rightarrow> bool) ysn (Rep_nat ysn)"
  shows "cr_nat ?t ((append :: 'a::lift_nat list \<Rightarrow> _) (Rep_nat xsn) (Rep_nat ysn))"
  apply (subst append_case_def)
  by transfer_prover

lemma append_nat_synth_def:
  fixes xs :: "'a::lift_nat list" and ys :: "'a list"
  assumes "xsn = Abs_nat xs"
  assumes "ysn = Abs_nat ys"
  shows "append_nat TYPE('a) xsn ysn = case_list_nat xsn (\<lambda>x3a x2ba. rev_tr_nat TYPE('a)
                (Cons_nat x3a x2ba) (rev_tr_nat TYPE('a) Nil_nat xsn)) ysn"
  apply(rule HOL.trans[OF _ append_nat_synth[unfolded cr_nat_def, symmetric]])
  using assms apply(simp add: append_nat_def rel_fun_def cr_nat_def)+
  done




fun plus :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "plus m 0 = m" |
  "plus m (Suc n) = Suc (plus m n)"

case_of_simps plus_case_def: plus.simps

definition plus_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "plus_nat m n \<equiv> Abs_nat (plus (Rep_nat m) (Rep_nat n))"

lemma plus_nat_lifting[transfer_rule]:
  shows "(cr_nat ===> cr_nat ===> cr_nat) plus_nat plus"
  unfolding plus_nat_def cr_nat_def
  by(simp add: rel_fun_def)

schematic_goal plus_nat_synth:
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> nat \<Rightarrow> bool) mn (Rep_nat mn)"
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> nat \<Rightarrow> bool) nn (Rep_nat nn)"
  shows "cr_nat ?t (plus (Rep_nat mn) (Rep_nat nn))"
  apply (subst plus_case_def)
  by transfer_prover

lemma plus_nat_synth_def:
  fixes m :: nat and n :: nat
  assumes "mn = Abs_nat m"
  assumes "nn = Abs_nat n"
  shows "plus_nat mn nn
    = case_nat_nat mn (\<lambda>x2ba. Suc_nat (plus_nat mn x2ba)) nn"
  apply(rule HOL.trans[OF _ plus_nat_synth[unfolded cr_nat_def, symmetric]])
  using assms cr_nat_nat_equiv
    apply(simp add: plus_nat_def rel_fun_def cr_nat_def)+
  done

thm plus_nat_synth_def[unfolded case_nat_nat_def]

end
