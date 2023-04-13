theory Compile_Nat
  imports IMP_Minus.Call_By_Prefixes IMP_Minus.Big_Step_Small_Step_Equivalence
begin

fun measure_assoc where
  "measure_assoc (Seq i1 i2) = Suc (measure_assoc i1 + measure_assoc i1 + measure_assoc i2)"
| "measure_assoc (If _ i1 i2) = Suc (measure_assoc i1 + measure_assoc i2)"
| "measure_assoc (While _ i) = Suc (measure_assoc i)"
| "measure_assoc _ = 0"

(* We could use this function instead of using ML but we should prove its correctness then *)
function (sequential) assoc_right_Seq where
  "assoc_right_Seq (Seq (Seq i1 i2) i3) = assoc_right_Seq (Seq i1 (Seq i2 i3))"
| "assoc_right_Seq (Seq i1 i2) = Seq i1 (assoc_right_Seq i2)"
| "assoc_right_Seq (If r i1 i2) = If r (assoc_right_Seq i1) (assoc_right_Seq i2)"
| "assoc_right_Seq (While r i) = While r (assoc_right_Seq i)"
| "assoc_right_Seq i = i"
  by pat_completeness auto
termination by (relation "measure measure_assoc") auto

lemma big_step_t_Seq_assoc: "((c1 ;; c2) ;; c3, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<longleftrightarrow> (c1 ;; (c2 ;; c3), s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  using compose_programs_1 by auto

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
        | (\<^Const_>\<open>If\<close>, _) => @{undefined}
        | (f, args) => App (~1, (f, map build_tc_ast args))
    in
      t |> build_tc_ast |> index_tc_ast 0 |> snd
    end

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
        |> imp_of_tc_ast
        |> let_of_imp
        |> fold_rev lambda args_vars
    in
      Local_Theory.define ((binding, NoSyn), ((Thm.def_binding binding, []), let_def)) lthy
      |> snd
    end

  fun match_first a [] = raise TERM ("No match", [a])
    | match_first a (f :: fs) = case try f a of SOME b => b | NONE => match_first a fs

  fun IMP_Minus_of_imp f (f_ret_name, f_arg_names) lookup_fn (ret_reg, imp) =
    let
      fun string_of_indexname (n, i) = HOLogic.mk_string (n ^ "_" ^ Int.toString i)
      fun mk_local_V n = \<^Const>\<open>V for \<open>string_of_indexname n\<close>\<close>
  
      fun mk_N n = \<^Const>\<open>N for \<open>HOLogic.mk_number \<^typ>\<open>nat\<close> n\<close>\<close>
  
      val cont_reg = HOLogic.mk_string "continue"
      fun mk_continue n = \<^Const>\<open>Assign for cont_reg \<^Const>\<open>A for \<open>mk_N n\<close>\<close>\<close>
      fun mk_While p =
        \<^Const>\<open>Seq for \<open>mk_continue 1\<close>
                      \<^Const>\<open>While for cont_reg \<^Const>\<open>Seq for \<open>mk_continue 0\<close> p\<close>\<close>\<close>
  
      fun mk_bop bop [arg1, arg2] = bop $ mk_local_V arg1 $ mk_local_V arg2

      fun mk_Seq es = fold_rev (fn e1 => fn e2 => \<^Const>\<open>Seq for e1 e2\<close>) es \<^Const>\<open>SKIP\<close>

      fun mk_assign_arg (arg_name, arg) =
        \<^Const>\<open>Assign for arg_name \<^Const>\<open>A for \<open>mk_local_V arg\<close>\<close>\<close>

      fun mk_tailcall args =
        map mk_assign_arg (map HOLogic.mk_string f_arg_names ~~ args) @ [mk_continue 1]
        |> mk_Seq

      fun mk_fun_arg prefix arg_name =
        \<^Const>\<open>List.append \<^typ>\<open>char list\<close> for \<open>HOLogic.mk_string prefix\<close> \<open>HOLogic.mk_string arg_name\<close>\<close>

      fun mk_call reg g args (prefix, (ret_name, args_names)) =
        map mk_assign_arg (map (mk_fun_arg prefix) args_names ~~ args) @
        [ \<^Const>\<open>com_add_prefix for \<open>HOLogic.mk_string prefix\<close> \<open>Const g\<close>\<close>
        , \<^Const>\<open>Assign for reg \<^Const>\<open>A for \<^Const>\<open>V for \<open>HOLogic.mk_string ret_name\<close>\<close>\<close>\<close>
        ]
        |> mk_Seq
        

      fun go Skip = \<^Const>\<open>SKIP\<close>
        | go (Seq (imp1, imp2)) = \<^Const>\<open>Seq for \<open>go imp1\<close> \<open>go imp2\<close>\<close>
        | go (Copy (reg1, reg2)) =
            \<^Const>\<open>Assign for \<open>string_of_indexname reg1\<close> \<^Const>\<open>A for \<open>mk_local_V reg2\<close>\<close>\<close>
        | go (IfNeqZero (_, (reg, imp1, imp2))) =
            \<^Const>\<open>If for \<open>string_of_indexname reg\<close> \<open>go imp1\<close> \<open>go imp2\<close>\<close>
        | go (Assign (reg, (g, args))) =
            let
              val base_cases_rhs =
                [ (fn n => \<^Const>\<open>A for \<open>n |> HOLogic.dest_number |> snd |> mk_N\<close>\<close>)
                , (fn \<^Const>\<open>Groups.plus \<^typ>\<open>nat\<close>\<close> => mk_bop \<^Const>\<open>Plus\<close> args)
                , (fn \<^Const>\<open>Groups.minus \<^typ>\<open>nat\<close>\<close> => mk_bop \<^Const>\<open>Sub\<close> args)
                , (fn (Var ((n, _), _)) =>
                    \<^Const>\<open>A for \<^Const>\<open>V for \<open>HOLogic.mk_string n\<close>\<close>\<close>)
                ]
              fun mk_assign rhs = \<^Const>\<open>Assign for \<open>string_of_indexname reg\<close> rhs\<close>
              val base_cases = map (curry (op o) mk_assign) base_cases_rhs

              val call_cases =  
                [ (fn Const f' => if f' = f then mk_tailcall args else raise Match)
                , (fn Const f' => mk_call (string_of_indexname reg) f' args (lookup_fn f'))
                ]
            in
              match_first g (base_cases @ call_cases)
            end
    in
      \<^Const>\<open>Seq for \<open>go imp |> mk_While\<close>
                    \<^Const>\<open>Assign for \<open>HOLogic.mk_string f_ret_name\<close> \<^Const>\<open>A for \<open>mk_local_V ret_reg\<close>\<close>\<close>\<close>
    end

  fun rm_SKIP \<^Const>\<open>Seq for \<^Const>\<open>SKIP\<close> e2\<close> = rm_SKIP e2
    | rm_SKIP \<^Const>\<open>Seq for e1 \<^Const>\<open>SKIP\<close>\<close> = rm_SKIP e1
    | rm_SKIP \<^Const>\<open>Seq for e1 e2\<close> = \<^Const>\<open>Seq for \<open>rm_SKIP e1\<close> \<open>rm_SKIP e2\<close>\<close>
    | rm_SKIP \<^Const>\<open>If for r e1 e2\<close> = \<^Const>\<open>If for r \<open>rm_SKIP e1\<close> \<open>rm_SKIP e2\<close>\<close>
    | rm_SKIP \<^Const>\<open>While for r e\<close> = \<^Const>\<open>While for r \<open>rm_SKIP e\<close>\<close>
    | rm_SKIP t = t

  fun assoc_right_Seq \<^Const>\<open>Seq for \<^Const>\<open>Seq for e1 e2\<close> e3\<close> =
        assoc_right_Seq \<^Const>\<open>Seq for e1 \<^Const>\<open>Seq for e2 e3\<close>\<close>
    | assoc_right_Seq \<^Const>\<open>Seq for e1 e2\<close> = \<^Const>\<open>Seq for e1 \<open>assoc_right_Seq e2\<close>\<close>
    | assoc_right_Seq \<^Const>\<open>If for r e1 e2\<close> =
        \<^Const>\<open>If for r \<open>assoc_right_Seq e1\<close> \<open>assoc_right_Seq e2\<close>\<close>
    | assoc_right_Seq \<^Const>\<open>While for r e\<close> = \<^Const>\<open>While for r \<open>assoc_right_Seq e\<close>\<close>
    | assoc_right_Seq e = e
  
\<close>

ML \<open>Library.foldr\<close>

definition "test (x :: nat) \<equiv> \<lambda>y. if x + y \<noteq> 0 then if y \<noteq> 0 then y else x else 0"

fun test1 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "test1 x y = (if x \<noteq> 0 then test1 (x - 1 - 1) (y + 1) else y)"

declare [[ML_print_depth=500]]
ML \<open>
    let
      val f_def = @{thm eq_reflection[OF test1.simps(1)]}
      val (args, def_body) =
        Local_Defs.abs_def_rule @{context} f_def
        |> Thm.rhs_of |> Thm.term_of |> Term.strip_abs

      val (f_name, f_typ) = f_def |> Thm.lhs_of |> Thm.term_of |> Term.head_of |> Term.dest_Const
      val f_ret_name = Long_Name.base_name f_name ^ "_ret"
      fun mk_arg_name arg_name = Long_Name.base_name f_name ^ "_" ^ arg_name
      val f_args = map (@{apply 2 (1)} mk_arg_name) args
      val f_arg_vars = map (Var o @{apply 2 (1)} (fn n => (n, 0))) f_args
    in
           def_body
        |> curry Term.subst_bounds (f_arg_vars |> rev)
        |> tc_ast_of_term
        |> imp_of_tc_ast
        |> @{print}
        |> IMP_Minus_of_imp (f_name, f_typ) (f_ret_name, map fst f_args) (fn _ => @{undefined})
        |> rm_SKIP
        |> assoc_right_Seq
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
