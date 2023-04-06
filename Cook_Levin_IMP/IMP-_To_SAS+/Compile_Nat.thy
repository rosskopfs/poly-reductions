theory Compile_Nat
  imports Primitives_IMP_Minus
begin

ML \<open>
  datatype tc_ast = If of (tc_ast * tc_ast * tc_ast) |
                    App of (int * term * tc_ast list)

  datatype instr = 
    Assign of (indexname * term * indexname list)
  | Copy of (indexname * indexname)
  | IfNeqZero of (indexname * instr list * instr list * instr list)

  fun tc_ast_of_term index t =
    let
      fun fold_step a (index, args_ast) =
            let val (index', a_ast) = tc_ast_of_term index a
            in (index', a_ast :: args_ast) end
    in
      case Term.strip_comb t of
        (\<^Const>\<open>HOL.If \<^typ>\<open>nat\<close>\<close>
        , [\<^Const>\<open>HOL.Not for \<open>\<^Const>\<open>HOL.eq \<^typ>\<open>nat\<close> for c \<open>\<^Const>\<open>Groups.zero \<^typ>\<open>nat\<close>\<close>\<close>\<close>\<close>\<close>, e1, e2]) =>
          let
            val (index', [c_ast, e1_ast, e2_ast]) = fold_rev fold_step [c, e1, e2] (index, [])
          in
            (index', If (c_ast, e1_ast, e2_ast))
          end
      | (f, args) =>
          let
            val (index', args_ast) = fold_rev fold_step args (index, [])
          in
            (index' + 1, App (index, f, args_ast))
          end
    end

  fun last [x] = x
    | last (_ :: xs) = last xs

  fun concat [] = []
    | concat (x :: xs) = x @ concat xs
  
  fun reg_of_term _ (Var ((s, idx), _)) = (s, idx)
    | reg_of_term idx (Const (s, _)) = (s, idx)

  fun tc_seq_of_tc_ast fn_ret_reg (App (index, t, args)) =
    let
      val args_instrs = map (tc_seq_of_tc_ast fn_ret_reg) args
      val arg_regs = map fst args_instrs;
      val ret_reg = reg_of_term index t
      val instr = Assign (ret_reg, t, arg_regs)
    in
      (ret_reg, concat (map snd args_instrs) @ [instr])
    end
   | tc_seq_of_tc_ast fn_ret_reg (If (astc, ast1, ast2)) =
    let
      val [seqc, seq1, seq2] = map (tc_seq_of_tc_ast fn_ret_reg) [astc, ast1, ast2]
    in
      (fn_ret_reg, [IfNeqZero
        (fst seqc
        , snd seqc
        , snd seq1 @ [Copy (fn_ret_reg, fst seq1)]
        , snd seq2 @ [Copy (fn_ret_reg, fst seq2)]
        )
      ])
    end
\<close>

ML \<open>
  Thm.term_of
\<close>

definition "test (x :: nat) y \<equiv> if x + y \<noteq> 0 then x else 0"

ML \<open>
  tc_ast_of_term (Thm.cprop_of @{thm test_def} |> Thm.maxidx_of_cterm) (@{thm test_def} |> Thm.rhs_of |> Thm.term_of)
  |> snd |> tc_seq_of_tc_ast ("test_ret", 0) |> snd
\<close>

end
