theory Compile_Nat
  imports IMP_Minus.Call_By_Prefixes
begin

ML \<open>
  datatype tc_ast = If of (int * (tc_ast * tc_ast * tc_ast)) |
                    App of (int * (term * tc_ast list))

  datatype imp =
    Skip
  | Seq of (imp * imp)
  | Assign of (indexname * (term * indexname list))
  | Copy of (indexname * indexname)
  | IfNeqZero of (indexname * (indexname * imp * imp))

  fun tc_ast_of_term t =
    let
      fun fold_step a (index, args_ast) =
            let val (index', a_ast) = index_tc_ast index a
            in (index', a_ast :: args_ast) end
      and index_tc_ast index (App (_, (f, args))) =
        let
          val (index', rev_args') = fold fold_step args (index, [])
        in
          (index' + 1, App (index', (f, rev rev_args')))
        end
        | index_tc_ast index (If (_, (c, e1, e2))) =
        let
          val (index', [e2', e1', c']) = fold fold_step [c, e1, e2] (index, [])
        in
          (index' + 1, If (index', (c', e1', e2')))
        end
        

      fun build_tc_ast t =
        case Term.strip_comb t of
          (\<^Const>\<open>HOL.If \<^typ>\<open>nat\<close>\<close>
          , [\<^Const>\<open>HOL.Not for \<open>\<^Const>\<open>HOL.eq \<^typ>\<open>nat\<close> for c \<open>\<^Const>\<open>Groups.zero \<^typ>\<open>nat\<close>\<close>\<close>\<close>\<close>\<close>, e1, e2]) =>
            If (~1, @{apply 3} build_tc_ast (c, e1, e2))
        (* Only allow condition of the form _ != 0 *)
        | (\<^Const>\<open>HOL.If \<^typ>\<open>nat\<close>\<close>, _) => @{undefined}
        | (f, args) => App (~1, (f, map build_tc_ast args))
    in
      t |> build_tc_ast |> index_tc_ast 0 |> snd
    end

  fun reg_of_term idx (Const (s, _)) = (s, idx)
    | reg_of_term idx (Free (s, _)) = (s, idx)
    | reg_of_term idx (Var ((s, _), _)) = (s, idx)

  fun imp_of_tc_ast (App (index, (t, args))) =
    let
      val args_instrs = map imp_of_tc_ast args
      val arg_regs = map fst args_instrs;
      val ret_reg = (Term.term_name t, index)
      val assign_ret = Assign (ret_reg, (t, arg_regs))
      val seq_args_instrs = List.foldr (op Seq) Skip (map snd args_instrs)
    in
      (ret_reg, Seq (seq_args_instrs, assign_ret))
    end
   | imp_of_tc_ast (If (idx, (astc, ast1, ast2))) =
    let
      val ret_reg = ("IfNeqZero", idx)
      val (impc, imp1, imp2) = @{apply 3} imp_of_tc_ast (astc, ast1, ast2)
    in
      (ret_reg, Seq (snd impc,
        IfNeqZero (ret_reg,
          ( fst impc
          , Seq (snd imp1, Copy (ret_reg, fst imp1))
          , Seq (snd imp2, Copy (ret_reg, fst imp2))
          ))
      ))
    end

  fun let_of_imp (ret_reg, imp) =
    let
      val natT = \<^typ>\<open>nat\<close>

      (* FIXME: this variable name might not be fresh *)
      fun reg_var_of_indexname (n, i) = Free (n ^ "_" ^ Int.toString i, natT)
      
      fun go target Skip = target
        | go target (Seq (imp1, imp2)) = go (go target imp2) imp1
        | go target (Copy (reg1, reg2)) =
        let
          val (reg1_var, reg2_var) = apply2 reg_var_of_indexname (reg1, reg2)
        in
          \<^Const>\<open>Let natT natT for reg2_var \<open>lambda reg1_var target\<close>\<close>
        end
        | go target (Assign (reg, (f, args))) =
        let
          val reg_var = reg_var_of_indexname reg
          val args_var = map reg_var_of_indexname args
        in
          \<^Const>\<open>Let natT natT for \<open>list_comb (f, args_var)\<close> \<open>lambda reg_var target\<close>\<close>
        end
        (* Ignoring target should work since we can't sequence If in HOL *)
        | go target (IfNeqZero (ret_reg, (cond_reg, e1, e2))) =
        let
          val (ret_reg_var, cond_reg_var) =
            apply2 reg_var_of_indexname (ret_reg, cond_reg)
          val (e1_let, e2_let) = apply2 (go ret_reg_var) (e1, e2)
          val condt = \<^Const>\<open>HOL.Not for
            \<^Const>\<open>HOL.eq natT for cond_reg_var \<^Const>\<open>Groups.zero natT\<close>\<close>\<close>
        in
          \<^Const>\<open>HOL.If natT for condt e1_let e2_let\<close>
        end
        
    in
      go (reg_var_of_indexname ret_reg) imp
    end

  fun match_first a [] = raise Match
    | match_first a (f :: fs) = case try f a of SOME b => b | NONE => match_first a fs

  fun while_of_imp (f_name, f_typ) f_args (ret_reg, imp) =
    let
      fun string_of_indexname (n, i) = HOLogic.mk_string (n ^ "_" ^ Int.toString i)
      fun mk_num n = \<^Const>\<open>N for \<open>HOLogic.mk_number \<^typ>\<open>nat\<close> n\<close>\<close>
      fun mk_var n = \<^Const>\<open>V for n\<close>
      val mk_local_var = mk_var o string_of_indexname
      fun mk_atom a = \<^Const>\<open>A for a\<close>
      
      val cont_reg = HOLogic.mk_string "continue"
      fun mk_continue n = \<^Const>\<open>Assign for cont_reg \<open>mk_atom (mk_num n)\<close>\<close>

      fun while_of_call f args = @{undefined}
      fun while_of_tailcall args = @{undefined}

      fun go Skip = \<^Const>\<open>SKIP\<close>
        | go (Seq (imp1, imp2)) = \<^Const>\<open>Seq for \<open>go imp1\<close> \<open>go imp2\<close>\<close>
        | go (Copy (reg1, reg2)) =
            \<^Const>\<open>Assign for \<open>string_of_indexname reg1\<close> \<open>mk_atom (mk_local_var reg2)\<close>\<close>
        | go (IfNeqZero (_, (reg, imp1, imp2))) =
            \<^Const>\<open>If for \<open>string_of_indexname reg\<close> \<open>go imp1\<close> \<open>go imp2\<close>\<close>
        | go (Assign (reg, (g, args))) =
            let
              val nocall_cases =
                [ mk_atom o mk_num o snd o HOLogic.dest_number
                , (fn \<^Const>\<open>Groups.plus \<^typ>\<open>nat\<close>\<close> =>
                    case args of [arg1, arg2] => \<^Const>\<open>Plus for \<open>mk_local_var arg1\<close> \<open>mk_local_var arg2\<close>\<close>)
                , (fn \<^Const>\<open>Groups.minus \<^typ>\<open>nat\<close>\<close> =>
                    case args of [arg1, arg2] => \<^Const>\<open>Sub for \<open>mk_local_var arg1\<close> \<open>mk_local_var arg2\<close>\<close>)
                , (fn (Var ((n, _), _)) => Long_Name.base_name f_name ^ "_" ^ n
                                           |> HOLogic.mk_string |> mk_var |> mk_atom)
                ]
              fun mk_assign rhs = \<^Const>\<open>Assign for \<open>string_of_indexname reg\<close> rhs\<close>

              fun mk_tailcall () =
                let
                  fun mk_assign_arg (f_arg, arg) =
                    \<^Const>\<open>Assign for \<open>HOLogic.mk_string f_arg\<close> \<open>string_of_indexname arg\<close>\<close>
                  val mk_assign_args = 
                    map mk_assign_arg (f_args ~~ args)
                    |> (fn ass => fold (fn e1 => fn e2 => \<^Const>\<open>Seq for e1 e2\<close>) ass \<^Const>\<open>SKIP\<close>)
                in
                  \<^Const>\<open>Seq for mk_assign_args \<open>mk_continue 1\<close>\<close>
                end
              val call_cases =  
                [ (fn Const (f_name, f_typ) => mk_tailcall ())
                ]
            in
              match_first g
                (map (curry (op o) mk_assign) nocall_cases @ call_cases)
            end
    in
      \<^Const>\<open>Seq for \<open>mk_continue 1\<close> \<^Const>\<open>While for cont_reg \<^Const>\<open>Seq for \<open>mk_continue 0\<close> \<open>go imp\<close>\<close>\<close>\<close>
    end

  fun define_let_of_def def binding lthy =
    let
      val (args, def_body) =
        Local_Defs.abs_def_rule lthy def
        |> Thm.rhs_of |> Thm.term_of |> Term.strip_abs
      val args_vars = map (Var o @{apply 2 (1)} (fn s => (s, 0))) args
      val let_def =
           def_body
        |> curry Term.subst_bounds (args_vars |> rev)
        |> tc_ast_of_term
        |> @{print}
        |> imp_of_tc_ast
        |> let_of_imp
        |> fold_rev lambda args_vars
    in
      Local_Theory.define ((binding, NoSyn), ((Thm.def_binding binding, []), let_def)) lthy
      |> snd
    end
\<close>

definition "test (x :: nat) \<equiv> \<lambda>y. if x + y \<noteq> 0 then if y \<noteq> 0 then y else x else 0"

ML \<open>
    let
      val (args, def_body) =
        Local_Defs.abs_def_rule @{context} @{thm test_def}
        |> Thm.rhs_of |> Thm.term_of |> Term.strip_abs
      val args_vars = map (Var o @{apply 2 (1)} (fn s => (s, 0))) args
    in
           def_body
        |> curry Term.subst_bounds (args_vars |> rev)
        |> tc_ast_of_term
        |> @{print}
        |> imp_of_tc_ast
        |> @{print}
        |> while_of_imp (\<^Const>\<open>test\<close> |> Term.dest_Const) (map fst args)
        |> Thm.cterm_of @{context}
    end
\<close>

local_setup \<open>
  define_let_of_def @{thm test_def} \<^binding>\<open>test_let\<close>
\<close>
print_theorems
       
lemma "test x y = test_let x y"
  unfolding test_def test_let_def by (simp add: Let_def)

end
