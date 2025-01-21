\<^marker>\<open>creator "Jay Neubrand"\<close>
\<^marker>\<open>creator "Andreas Vollert"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
section\<open>HOL with Datatypes to HOL on Natural Numbers\<close>
theory HOL_To_HOL_Nat_Base
  imports
    "HOL-Library.Nat_Bijection"
    "HOL-Library.Simps_Case_Conv"
    Transport.HOL_Alignment_Functions
    Transport.HOL_Syntax_Bundles_Base
    Transport.Transport_Prototype
    Transport.Transport_Typedef_Base
  keywords "datatype_compile_nat" :: thy_decl
  and "function_compile_nat" :: thy_decl
  and "unconditional_nat" :: thy_decl
  and "basename"
begin

unbundle no converse_syntax
unbundle lifting_syntax

named_theorems "Rel_nat"
  "Rel_nat relatedness theorems"

text \<open>Types with encodings as natural numbers.\<close>
class compile_nat =
  fixes natify :: "'a \<Rightarrow> nat"
  and denatify :: "nat \<Rightarrow> 'a"
  (*natify is injective*)
  assumes denatify_natify_eq_self [simp]: "\<And>x. denatify (natify x) = x"
begin

sublocale compile_nat_type_def: type_definition natify denatify "range natify"
  by unfold_locales auto
declare compile_nat_type_def.Rep_induct[induct del] compile_nat_type_def.Abs_induct[induct del]

lemma inj_natify: "inj natify"
  by (rule inj_on_inverseI[where ?g=denatify]) simp

lemma eq_if_natify_eq: "natify x = natify y \<Longrightarrow> x = y"
  using inj_natify by (blast dest: injD)

definition Rel_nat :: "nat \<Rightarrow> 'a \<Rightarrow> bool" where
  "Rel_nat n x \<equiv> n = natify x"

lemma Rel_nat_iff_eq_natify: "Rel_nat n x \<longleftrightarrow> n = natify x"
  unfolding Rel_nat_def by simp

lemmas
  typedef_Rel_nat_transfer[OF compile_nat_type_def.type_definition_axioms,
    OF eq_reflection, OF ext, OF ext, OF Rel_nat_iff_eq_natify] =
  typedef_bi_unique typedef_right_unique typedef_left_unique typedef_right_total

lemma right_unique_Rel_nat: "Transfer.right_unique Rel_nat"
  by (fact typedef_Rel_nat_transfer)

lemma left_unique_Rel_nat: "left_unique Rel_nat"
  by (fact typedef_Rel_nat_transfer)

(*not registered by default since terms should not be transferred to their
natify blackbox partner but their whitebox-transfer parnter*)
lemma Rel_nat_natify_self: "Rel_nat (natify x) x"
  by (simp add: Rel_nat_iff_eq_natify)

lemma Rel_nat_denatify_natify [Rel_nat]: "(Rel_nat ===> Rel_nat\<inverse>) denatify natify"
  by (intro rel_funI) (auto iff: Rel_nat_iff_eq_natify)

interpretation flip : transport compile_nat_type_def.R compile_nat_type_def.L natify denatify .

lemma Galois_eq_inv_Rel_nat: "flip.Galois = Rel_nat\<inverse>"
  by (intro ext) (fastforce iff: Rel_nat_iff_eq_natify)

lemma compile_nat_flip_partial_equivalence_rel_equivalence:
  "flip.partial_equivalence_rel_equivalence"
  using compile_nat_type_def.partial_equivalence_rel_equivalenceI
  flip.partial_equivalence_rel_equivalence_right_left_iff_partial_equivalence_rel_equivalence_left_right
  by blast

end

(*register PER*)
declare compile_nat_flip_partial_equivalence_rel_equivalence[per_intro]

(*nicer relatedness theorem output*)
declare Galois_eq_inv_Rel_nat[trp_relator_rewrite, trp_uhint]
lemma eq_eq_Fun_Rel_eq_eq_uhint [trp_uhint]: "P \<equiv> (=) \<Longrightarrow> P \<equiv> (=) \<Rrightarrow> (=)" by simp

definition pair_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "pair_nat a b = prod_encode (a, b)"

lemma pair_nat_eq: "pair_nat a b = prod_encode (a, b)"
  unfolding pair_nat_def by simp

lemma pair_nat_zero_zero_eq_zero [simp]: "pair_nat 0 0 = 0"
  by (simp add: pair_nat_def prod_encode_def)

definition "unpair_nat \<equiv> prod_decode"

lemma unpair_nat_eq: "unpair_nat p = prod_decode p"
  unfolding unpair_nat_def by simp

lemma unpair_nat_pair_nat_eq [simp]: "unpair_nat (pair_nat a b) = (a, b)"
  unfolding unpair_nat_eq pair_nat_eq by simp

lemma pair_nat_unpair_nat_eq [simp]: "(\<lambda>(a, b). pair_nat a b) (unpair_nat p) = p"
  unfolding unpair_nat_eq pair_nat_eq by simp

lemma unpair_nat_zero_eq_zero_zero [simp]: "unpair_nat 0 = (0, 0)"
  by (subst pair_nat_zero_zero_eq_zero[symmetric], subst unpair_nat_pair_nat_eq) simp

definition fst_nat :: "nat \<Rightarrow> nat" where
  "fst_nat p = fst (unpair_nat p)"

lemma fst_nat_eq: "fst_nat p = fst (unpair_nat p)"
  unfolding fst_nat_def by simp

lemma fst_nat_pair_eq [simp]: "fst_nat (pair_nat a b) = a"
  unfolding fst_nat_eq by simp

lemma fst_nat_zero_eq [simp]: "fst_nat 0 = 0"
  unfolding fst_nat_eq by simp

definition snd_nat :: "nat \<Rightarrow> nat" where
  "snd_nat p = snd (unpair_nat p)"

lemma snd_nat_eq: "snd_nat p = snd (unpair_nat p)"
  unfolding snd_nat_def by simp

lemma snd_nat_pair_eq [simp]: "snd_nat (pair_nat a b) = b"
  unfolding snd_nat_eq by simp

lemma snd_nat_zero_eq [simp]: "snd_nat 0 = 0"
  unfolding snd_nat_eq by simp

lemma fst_nat_le_if_le [termination_simp]: "p \<le> p' \<Longrightarrow> fst_nat p \<le> p'"
  unfolding fst_nat_eq unpair_nat_eq
  by (cases "prod_decode p") (metis fst_conv le_prod_encode_1 order.trans prod_decode_inverse)

lemma snd_nat_le_if_le [termination_simp]: "p \<le> p' \<Longrightarrow> snd_nat p \<le> p'"
  unfolding snd_nat_eq unpair_nat_eq
  by (cases "prod_decode p") (metis le_prod_encode_2 order.trans prod_decode_inverse split_pairs)

lemma [termination_simp]:
  assumes "p < p'"
  shows fst_nat_lt_if_lt: "fst_nat p < p'"
  and snd_nat_lt_if_lt: "snd_nat p < p'"
  using assms le_prod_encode_1[of "fst_nat p" "snd_nat p"] le_prod_encode_2[of "snd_nat p" "fst_nat p"]
  by (simp_all add: fst_nat_eq snd_nat_eq pair_nat_eq unpair_nat_eq)

lemma
  assumes "0 < a"
  shows fst_lt_pair_nat_if_zero_lt: "a < pair_nat a b"
  and snd_lt_pair_nat_if_zero_lt: "b < pair_nat a b"
  using assms by (cases a; simp add: pair_nat_eq prod_encode_def)+

corollary [termination_simp]:
  assumes "0 < fst_nat p"
  shows fst_nat_lt_self_if_lt_fst_nat: "fst_nat p < p"
  and snd_nat_lt_self_if_lt_fst_nat: "snd_nat p < p"
  using assms pair_nat_unpair_nat_eq[of p]
  by (cases "unpair_nat p"; auto simp: fst_lt_pair_nat_if_zero_lt snd_lt_pair_nat_if_zero_lt)+

lemma rel_inv_Fun_Rel_rel_eq: "(R \<Rrightarrow> S)\<inverse> = (R\<inverse> \<Rrightarrow> S\<inverse>)"
  by (urule rel_inv_Dep_Fun_Rel_rel_eq)

ML_file \<open>hol_to_hol_nat_util.ML\<close>

text \<open>Encoding of datatypes as natural numbers.
Restrictions:
(1) (technical limitation) Recursive constructors must not be the first constructor (due to termination proofs).
(2) Recursively used types must be compiled already (note: the function type cannot
be made an instance of @{class compile_nat} and hence no higher-order arguments may be used).
(3) As a consequence of (2): Recursive datatypes may not be nested inside of another datatype.
\<close>

named_theorems "Rel_nat_compile_nat"
  "Rel_nat relatedness theorems for terms compiled from HOL to HOL on natural numbers"

ML_file \<open>datatype_to_nat.ML\<close>
ML_file \<open>hol_fun_to_hol_nat_fun.ML\<close>

end
