\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Compile_Problem
  imports
    HOL_To_IMP_Minus_Primitives
begin

context HOL_To_IMP_Minus
begin

text \<open>The following causes variable name clashes and
thus changes the intended semantics.\<close>

definition "foo_bar x y \<equiv> x - (y :: nat)"
compile_nat foo_bar_def

definition "foo bar_x bar_y \<equiv> foo_bar bar_y bar_x"
compile_nat foo_def

HOL_To_IMP_Minus_func_correct foo_bar by cook

HOL_To_IMP_Minus_func_correct foo
  apply cook \<comment> \<open>unprovable goal\<close>
  oops

end

end

