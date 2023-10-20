theory Compile_Nat_Examples
  imports Compile_Nat
begin

definition max_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "max_nat x y \<equiv> if x - y \<noteq> 0 then x else y"

definition max3_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "max3_nat x y z \<equiv> max_nat (max_nat x y) z"

fun nat_add :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nat_add x y z =
    (if x \<noteq> 0
      then nat_add (x - 1) y (z + 1)
      else (if y \<noteq> 0 then nat_add x (y - 1) (z + 1) else z))"

definition test_let :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "test_let x y \<equiv> let u = 10; v = u + y in v + x"

context
  includes tcom_syntax com_syntax
begin

compile_nat max_nat_def basename max
compile_nat max3_nat_def basename max3
compile_nat nat_add.simps(1)
compile_nat test_let_def

end

context includes com_syntax aexp_syntax no_com'_syntax
begin

declare_compiled_const Suc
  return_register "Suc_ret"
  argument_registers "Suc_x"
  compiled \<open>''Suc_ret'' ::= ((V ''Suc_x'') \<oplus> N 1)\<close>

end

definition "Suc2_nat x \<equiv> Suc (Suc x)"

compile_nat Suc2_nat_def basename Suc2

context includes tcom_syntax com_syntax aexp_syntax
begin
print_compiled_consts
print_compiled_consts!
thm compiled_const_defs
end


end