\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Pairs
  imports
    HOL_To_IMP_Arithmetics
begin

context HOL_To_HOL_Nat
begin

function_compile_nat fst_def
function_compile_nat snd_def

definition "rpair y x \<equiv> (x, y)"

function_compile_nat rpair_def

end

context HOL_Nat_To_IMP
begin

declare Rel_nat_selector_prod[Rel_nat]

compile_nat Pair_nat_def
HOL_To_IMP_correct Pair_nat by cook

lemmas fst_nat_eq = HTHN.fst_nat_eq_unfolded[unfolded case_prod_nat_def]
compile_nat fst_nat_eq
HOL_To_IMP_correct HOL_To_HOL_Nat.fst_nat by cook

lemmas snd_nat_eq = HTHN.snd_nat_eq_unfolded[unfolded case_prod_nat_def]
compile_nat snd_nat_eq
HOL_To_IMP_correct HOL_To_HOL_Nat.snd_nat by cook

compile_nat HTHN.rpair_nat_eq_unfolded
HOL_To_IMP_correct HOL_To_HOL_Nat.rpair_nat by cook

end

end