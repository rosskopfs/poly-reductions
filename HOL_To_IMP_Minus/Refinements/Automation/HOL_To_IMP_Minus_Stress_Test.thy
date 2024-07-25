theory HOL_To_IMP_Minus_Stress_Test
  imports
    HOL_To_IMP_Minus_Fun_Pattern_Setup
    "HOL-Library.Discrete"
begin

context HOL_To_IMP_Minus
begin

(* first recursive argument is used in calculation of second recursive argument *)

fun prod_decode_aux1 :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "prod_decode_aux1 k m =
    (if m \<le> k then m else prod_decode_aux1 (Suc k) (m - Suc k))"
declare prod_decode_aux1.simps[simp del]  (* NOTE: prevents simplifier loop *)

compile_nat prod_decode_aux1.simps
HOL_To_IMP_Minus_func_correct prod_decode_aux1 by (cook mode = tailcall)

(* right-nested calls to same function *)

fun right_nest :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "right_nest x y z = x - (y - z)"

compile_nat right_nest.simps
HOL_To_IMP_Minus_func_correct right_nest by cook

end

end
