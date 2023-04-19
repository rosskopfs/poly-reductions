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
  datatype tc_ast = If of int * (tc_ast * tc_ast * tc_ast) |
                    Number of int |
                    Arg of int |
                    Call of int * ((string * typ) * tc_ast list) |
                    TailCall of tc_ast list

  fun tc_ast_of_term (f_name, f_typ) f_args t =
    let
      fun fold_step a (index, args_ast) =
          let val (index', a_ast) = index_tc_ast index a
          in (index', a_ast :: args_ast) end

      and index_tc_ast index (Call (_, (g, args))) =
          let val (index', rev_args') = fold fold_step args (index, [])
          in (index' + 1, Call (index', (g, rev rev_args'))) end
        | index_tc_ast index (If (_, (c, e1, e2))) =
          let val (index', [e2', e1', c']) = fold fold_step [c, e1, e2] (index, [])
          in (index' + 1, If (index', (c', e1', e2'))) end
        | index_tc_ast index (TailCall args) =
          let val (index', rev_args') = fold fold_step args (index, [])
          in (index', TailCall (rev rev_args')) end
        | index_tc_ast index t = (index, t)
        
      fun build_tc_ast t =
        if can HOLogic.dest_number t then Number (HOLogic.dest_number t |> snd)
        else
          case Term.head_of t of
            \<^Const_>\<open>HOL.If _\<close> =>
              (case Term.args_of t of
                [\<^Const>\<open>HOL.Not for \<^Const>\<open>HOL.eq \<^typ>\<open>nat\<close> for c \<^Const>\<open>Groups.zero \<^typ>\<open>nat\<close>\<close>\<close>\<close>, e1, e2] =>
                  If (~1, @{apply 3} build_tc_ast (c, e1, e2))
              | c :: _ => raise TERM ("Only conditions of the form x != 0 are allowed, got:", [c]))
          | Var ((n, _), t) => Arg (Library.find_index (fn v' => (n, t) = v') f_args)
          | Const (g_name, g_typ) =>
            if (g_name, g_typ) = (f_name, f_typ)
              then TailCall (map build_tc_ast (Term.args_of t))
              else Call (~1, ((g_name, g_typ), map build_tc_ast (Term.args_of t)))
          | h => raise TERM ("Unexpected head of term:", [h]) 
    in
      t |> build_tc_ast |> index_tc_ast 0 |> snd
    end

  fun IMP_Minus_of_tc_ast (f_ret_name, f_arg_names) lookup_fn e =
    let
      fun f_arg_reg i = nth f_arg_names i |> HOLogic.mk_string

      fun mk_Seq es = fold_rev (fn e1 => fn e2 => \<^Const>\<open>Seq for e1 e2\<close>) es \<^Const>\<open>SKIP\<close>

      fun mk_N n = \<^Const>\<open>N for \<open>HOLogic.mk_number \<^typ>\<open>nat\<close> n\<close>\<close>
  
      val cont_reg = HOLogic.mk_string "continue"
      fun mk_continue n = \<^Const>\<open>Assign for cont_reg \<^Const>\<open>A for \<open>mk_N n\<close>\<close>\<close>
      fun mk_While p =
        mk_Seq [ mk_continue 1
               , \<^Const>\<open>While for cont_reg \<open>mk_Seq [mk_continue 0, p]\<close>\<close>
               ]

      fun go cont (Number i) = cont \<^Const>\<open>A for \<open>mk_N i\<close>\<close>
        | go cont (Arg i) = cont \<^Const>\<open>A for \<^Const>\<open>V for \<open>f_arg_reg i\<close>\<close>\<close>
        | go cont (If (idx, (cond, e1, e2))) =
          let
            val cond_reg = "IfNeqZeroCond_" ^ Int.toString idx |> HOLogic.mk_string
            val cond_IMP = go (fn rhs => \<^Const>\<open>Assign for cond_reg rhs\<close>) cond
            val ret_reg = "IfNeqZero_" ^ Int.toString idx |> HOLogic.mk_string
            val (e1_IMP, e2_IMP) = @{apply 2} (go (fn rhs => \<^Const>\<open>Assign for ret_reg rhs\<close>)) (e1, e2)
            val if_IMP = \<^Const>\<open>If for cond_reg e1_IMP e2_IMP\<close>
          in
            mk_Seq [cond_IMP, if_IMP, cont \<^Const>\<open>A for \<^Const>\<open>V for ret_reg\<close>\<close>]
          end
        | go _ (TailCall es) =
          let
            val es_IMP =
              map_index (fn (i, e) => go (fn rhs => \<^Const>\<open>Assign for \<open>f_arg_reg i\<close> rhs\<close>) e) es
          in
            mk_Seq (es_IMP @ [mk_continue 1])
          end
        | go cont (Call (idx, ((g_name, g_typ), es))) =
          let
            fun mk_bop_hs bop (hs_name, e) =
              let
                val reg =
                  Term.term_name bop ^ hs_name ^ "_" ^ Int.toString idx
                  |> HOLogic.mk_string
              in
                (reg, go (fn rhs => \<^Const>\<open>Assign for reg rhs\<close>) e)
              end
            fun mk_bop bop (e1, e2) =
              let
                val ((lhs_reg, lhs_IMP), (rhs_reg, rhs_IMP)) =
                  @{apply 2} (mk_bop_hs bop) (("Lhs", e1), ("Rhs", e2))
              in
                mk_Seq [ lhs_IMP, rhs_IMP
                       , cont (bop $ \<^Const>\<open>V for lhs_reg\<close> $ \<^Const>\<open>V for rhs_reg\<close>)
                       ]
              end
        in
          case (Const (g_name, g_typ), es) of
            (\<^Const>\<open>Groups.plus \<^typ>\<open>nat\<close>\<close>, [e1, e2]) => mk_bop \<^Const>\<open>Plus\<close> (e1, e2)
          | (\<^Const>\<open>Groups.minus \<^typ>\<open>nat\<close>\<close>, [e1, e2]) => mk_bop \<^Const>\<open>Sub\<close> (e1, e2)
          | _ =>
            let
              val (g_prefix, (g_ret_name, g_arg_names)) = lookup_fn (g_name, g_typ)
              fun g_arg_reg i = nth g_arg_names i |> HOLogic.mk_string
              val g_args_IMP =
                map_index (fn (i, e) => go (fn rhs => \<^Const>\<open>Assign for \<open>g_arg_reg i\<close> rhs\<close>) e) es
            in
              g_args_IMP @
              [ \<^Const>\<open>com_add_prefix for \<open>HOLogic.mk_string g_prefix\<close> \<open>Const (g_name, g_typ)\<close>\<close>
              , cont \<^Const>\<open>A for \<^Const>\<open>V for \<open>HOLogic.mk_string g_ret_name\<close>\<close>\<close>
              ] |> mk_Seq
            end
        end
    in
      go (fn rhs => \<^Const>\<open>Assign for \<open>HOLogic.mk_string f_ret_name\<close> rhs\<close>) e
      |> mk_While
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

definition "test (x :: nat) \<equiv> \<lambda>y. if x + y \<noteq> 0 then if y \<noteq> 0 then y else x else 0"

fun test1 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "test1 x y = (if x \<noteq> 0 then test1 (x - 1 - 1) (y + 1) else y)"

declare [[ML_print_depth=500]]
ML \<open>
    let
      val f_def = @{thm test_def}
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
        |> tc_ast_of_term (f_name, f_typ) f_args
        |> @{print}
        |> IMP_Minus_of_tc_ast (f_ret_name, map fst f_args) (fn (f, ty) => @{undefined})
        |> rm_SKIP
        |> assoc_right_Seq
        |> Thm.cterm_of @{context}
    end
\<close>

end
