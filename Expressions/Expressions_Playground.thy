\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expressions_Playground
  imports
    Expression_Tail_Call_Whiles_Plus_Minus
begin

free_constructors case_exp_seq_assign_base for SABBase | SABAssign | SABSeq
  unfolding exp_smart_constructor_def
  apply auto
  apply (metis exp_assign_base.exhaust exp_seq_assign_base.exhaust exp_seq_base.exhaust)
  done

fun test :: "('b, 'a, 'c, 'd, 'e) exp_seq_assign_base \<Rightarrow> nat" where
  "test x = (case x of
    SABBase b \<Rightarrow> 0
  | SABAssign x ea \<Rightarrow> 0
  | SABSeq esf esb \<Rightarrow> 1)"

text\<open>WHILE programs with plus, minus, and atomic values\<close>
typ "('si, 'sv, 'eic, 'ewc) exp_while_plus_minus"
term "WPMPlus (WPMV 1) (WPMV 2)"
term "WPMAssign x (WPMPlus (WPMV 1) (WPMV 2))"
term "WPMSI x"
term "WPMSeq
  (WPMBSeq (WPMBSeq x1 x2) y)
    (WPMBSeq s (WPMBPlus (WPMV 1) (WPMSI n)))"
term "WPMSeq
  (WAssign x (WPMPlus (WPMV 1) (WPMV 2)))
  (WPMBV v)"
term "WPMSeq
  (WPMBWhile b (WPMBV 1))
  (WPMBSI ''x'')"

text\<open>Tail recursive WHILE programs with plus, minus, and atomic values\<close>
typ "('si, 'sv, 'eic, 'ewc) exp_tail_call_while_plus_minus"
term "WPMV"
term "ETCWPM (TC (FGCWPMPlus (WPMV 1) (WPMV 2)))"
term "ETCWPM (TC (FGCWPMAssign x (WPMPlus (WPMV 1) (WPMV 2))))"
term "ETCWPM (TC (FGCWPMSI x))"
term "ETCWPM (TC (FGCSeq
  (WPMSeq
    (WPMBSeq
      x1
      x2)
    (WPMBV n))
  k))"
term "ETCWPM (TC (FGCWPMSeq
  (WAssign x (WPMPlus (WPMV 1) (WPMV 2)))
  (WPMBSI ''x'')))"
term "ETCWPM (TC (FGCSeq
  (WPMWhile b (WPMBV 1))
  FGCGlobal_Call))"

end
