\<^marker>\<open>creator "Jay Neubrand"\<close>
\<^marker>\<open>creator "Andreas Vollert"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
section\<open>HOL with Datatypes to HOL on Natural Numbers\<close>
theory HOL_To_HOL_Nat_Setup
  imports
    "HOL-Library.Nat_Bijection"
    "HOL-Library.Simps_Case_Conv"
    Transport.HOL_Alignment_Functions
    Transport.HOL_Syntax_Bundles_Base
    Transport.Transport_Prototype
    Transport.Transport_Typedef_Base
  keywords "datatype_compile_nat" :: thy_decl
  and "function_compile_nat" :: thy_decl
begin

unbundle no_HOL_relation_syntax

text \<open>Types with encodings as natural numbers.\<close>
class compile_nat =
  fixes natify :: "'a \<Rightarrow> nat"
  and denatify :: "nat \<Rightarrow> 'a"
  assumes denatify_natify_eq_self[simp]: "\<And>x. denatify (natify x) = x"
begin

sublocale compile_nat_type_def: type_definition natify denatify "range natify"
  by unfold_locales auto

lemma inj_natify: "inj natify"
  by (rule inj_on_inverseI[where ?g=denatify]) simp

definition Rel_nat :: "nat \<Rightarrow> 'a \<Rightarrow> bool" where
  "Rel_nat n x \<equiv> n = natify x"

lemma Rel_nat_iff_eq_natify: "Rel_nat n x \<longleftrightarrow> n = natify x"
  by (simp add: Rel_nat_def)

lemmas
  typedef_nat_transfer[OF compile_nat_type_def.type_definition_axioms,
    OF eq_reflection, OF ext, OF ext, OF Rel_nat_iff_eq_natify, transfer_rule] =
  typedef_bi_unique typedef_right_unique typedef_left_unique typedef_right_total

lemma Rel_nat_natify_self [transfer_rule]: "Rel_nat (natify x) x"
  by (simp add: Rel_nat_iff_eq_natify)

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

definition pair :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "pair l r = prod_encode (l, r)"

definition fstP :: "nat \<Rightarrow> nat" where
  "fstP v = fst (prod_decode v)"

definition sndP :: "nat \<Rightarrow> nat" where
  "sndP v = snd (prod_decode v)"

lemmas [termination_simp] = fstP_def sndP_def

lemma prod_encode_zero_eq_zero [simp]: "prod_encode (0, 0) = 0"
  by (simp add: prod_encode_def)

lemma [termination_simp]:
  assumes "v < v'"
  shows fst_prod_decode_le: "fst (prod_decode v) < v'"
    and snd_prod_decode_le: "snd (prod_decode v) < v'"
  using assms le_prod_encode_1[of "fstP v" "sndP v"] le_prod_encode_2[of "sndP v" "fstP v"]
  by (simp_all add: fstP_def sndP_def)

lemma
  assumes "0 < a"
  shows fst_le_prod_encode: "a < prod_encode (a, b)"
    and snd_le_prod_encode: "b < prod_encode (a, b)"
  using assms by (induction a; simp add: prod_encode_def)+

corollary [termination_simp]:
  assumes "0 < fstP v"
  shows fst_prod_decode_le_self: "fst (prod_decode v) < v"
    and snd_prod_decode_le_self: "snd (prod_decode v) < v"
  using assms prod_decode_inverse[of v]
  by (cases "prod_decode v"; fastforce simp add: fstP_def fst_le_prod_encode snd_le_prod_encode)+

lemma fst_prod_decode_zero_eq [simp]: "fst (prod_decode 0) = 0" using fst_prod_decode_le by auto
lemma snd_prod_decode_zero_eq [simp]: "snd (prod_decode 0) = 0" using snd_prod_decode_le by auto

lemma rel_inv_Fun_Rel_rel_eq: "(R \<Rrightarrow> S)\<inverse> = (R\<inverse> \<Rrightarrow> S\<inverse>)"
  by (urule rel_inv_Dep_Fun_Rel_rel_eq)

ML_file \<open>hol_to_hol_nat.ML\<close>


end