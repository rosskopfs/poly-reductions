theory Compile_HOL_to_IMP_Minus_Calls
  imports
    IMP_Minus.IMP_Calls
begin

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
              \<^Const_>\<open>HOL.If _\<close> => (case Term.args_of t of
                [\<^Const>\<open>HOL.Not for \<^Const>\<open>HOL.eq \<^typ>\<open>nat\<close>
                  for c \<^Const>\<open>Groups.zero \<^typ>\<open>nat\<close>\<close>\<close>\<close>, e1, e2] =>
                  If (~1, @{apply 3} build_tc_ast (c, e1, e2))
            | c :: _ => raise TERM ("Only conditions of the form x \<noteq> 0 are allowed, got:", [c]))
          | Var ((n, _), t) => Arg (Library.find_index (fn v' => (n, t) = v') f_args)
          | Const (g_name, g_typ) =>
            if (g_name, g_typ) = (f_name, f_typ)
              then TailCall (map build_tc_ast (Term.args_of t))
              else Call (~1, ((g_name, g_typ), map build_tc_ast (Term.args_of t)))
          | h => raise TERM ("Unexpected head of term:", [h])
    in t |> build_tc_ast |> index_tc_ast 0 |> snd end

  fun IMP_Minus_of_tc_ast (f_ret_name, f_arg_names) lookup_fn e =
    let
      fun f_arg_reg i = nth f_arg_names i |> HOLogic.mk_string

      fun mk_Seq [] = raise ERROR "Cannot create empty command sequence"
        | mk_Seq (c :: cs) = fold (fn cb => fn cf => \<^Const>\<open>Seq' for cf cb\<close>) cs c

      fun mk_N n = \<^Const>\<open>N for \<open>HOLogic.mk_number \<^typ>\<open>nat\<close> n\<close>\<close>

      val cont_reg = HOLogic.mk_string "continue"
      fun mk_continue n = \<^Const>\<open>Assign' for cont_reg \<^Const>\<open>A for \<open>mk_N n\<close>\<close>\<close>
      fun mk_While p = mk_Seq [
          mk_continue 1,
          \<^Const>\<open>While' for cont_reg \<open>mk_Seq [mk_continue 0, p]\<close>\<close>
        ]

      fun go cont (Number i) = cont \<^Const>\<open>A for \<open>mk_N i\<close>\<close>
        | go cont (Arg i) = cont \<^Const>\<open>A for \<^Const>\<open>V for \<open>f_arg_reg i\<close>\<close>\<close>
        | go cont (If (idx, (cond, e1, e2))) =
          let
            val cond_reg = "IfNeqZeroCond_" ^ Int.toString idx |> HOLogic.mk_string
            val cond_IMP = go (fn rhs => \<^Const>\<open>Assign' for cond_reg rhs\<close>) cond
            val ret_reg = "IfNeqZero_" ^ Int.toString idx |> HOLogic.mk_string
            val (e1_IMP, e2_IMP) =
              @{apply 2} (go (fn rhs => \<^Const>\<open>Assign' for ret_reg rhs\<close>)) (e1, e2)
            val if_IMP = \<^Const>\<open>If' for cond_reg e1_IMP e2_IMP\<close>
          in
            mk_Seq [cond_IMP, if_IMP, cont \<^Const>\<open>A for \<^Const>\<open>V for ret_reg\<close>\<close>]
          end
        | go _ (TailCall es) =
          let
            val es_IMP =
              map_index (fn (i, e) => go (fn rhs => \<^Const>\<open>Assign' for \<open>f_arg_reg i\<close> rhs\<close>) e) es
          in
            mk_Seq (es_IMP @ [mk_continue 1])
          end
        | go cont (Call (idx, ((g_name, g_typ), es))) =
          let
            fun mk_bop_hs bop (hs_name, e) =
              let val reg = Term.term_name bop ^ hs_name ^ "_" ^ Int.toString idx
                |> HOLogic.mk_string
              in (reg, go (fn rhs => \<^Const>\<open>Assign' for reg rhs\<close>) e) end
            fun mk_bop bop (e1, e2) =
              let
                val ((lhs_reg, lhs_IMP), (rhs_reg, rhs_IMP)) =
                  @{apply 2} (mk_bop_hs bop) (("Lhs", e1), ("Rhs", e2))
              in
                mk_Seq [
                  lhs_IMP,
                  rhs_IMP,
                  cont (bop $ \<^Const>\<open>V for lhs_reg\<close> $ \<^Const>\<open>V for rhs_reg\<close>)
                ]
              end
          in case (Const (g_name, g_typ), es) of
              (\<^Const>\<open>Groups.plus \<^typ>\<open>nat\<close>\<close>, [e1, e2]) => mk_bop \<^Const>\<open>Plus\<close> (e1, e2)
            | (\<^Const>\<open>Groups.minus \<^typ>\<open>nat\<close>\<close>, [e1, e2]) => mk_bop \<^Const>\<open>Sub\<close> (e1, e2)
            | _ =>
              let
                val (g_IMP_Minus_program, (g_ret_name, g_arg_names)) = lookup_fn (g_name, g_typ)
                fun g_arg_reg i = nth g_arg_names i |> HOLogic.mk_string
                val g_args_IMP =
                  map_index (fn (i, e) => go (fn rhs => \<^Const>\<open>Assign' for \<open>g_arg_reg i\<close> rhs\<close>) e) es
                val _ = @{print} (lookup_fn (g_name, g_typ))
              in
                g_args_IMP @ [
                  \<^Const>\<open>Call' for g_IMP_Minus_program \<open>HOLogic.mk_string g_ret_name\<close>\<close>,
                  cont \<^Const>\<open>A for \<^Const>\<open>V for \<open>HOLogic.mk_string g_ret_name\<close>\<close>\<close>
                ] |> mk_Seq
              end
          end
    in
      go (fn rhs => \<^Const>\<open>Assign' for \<open>HOLogic.mk_string f_ret_name\<close> rhs\<close>) e
      |> mk_While
    end

  fun assoc_right_Seq \<^Const>\<open>Seq' for \<^Const>\<open>Seq' for e1 e2\<close> e3\<close> =
        assoc_right_Seq \<^Const>\<open>Seq' for e1 \<^Const>\<open>Seq' for e2 e3\<close>\<close>
    | assoc_right_Seq \<^Const>\<open>Seq' for e1 e2\<close> = \<^Const>\<open>Seq' for \<open>assoc_right_Seq e1\<close> \<open>assoc_right_Seq e2\<close>\<close>
    | assoc_right_Seq \<^Const>\<open>If' for r e1 e2\<close> =
        \<^Const>\<open>If' for r \<open>assoc_right_Seq e1\<close> \<open>assoc_right_Seq e2\<close>\<close>
    | assoc_right_Seq \<^Const>\<open>While' for r e\<close> = \<^Const>\<open>While' for r \<open>assoc_right_Seq e\<close>\<close>
    | assoc_right_Seq e = e
\<close>

definition "test (x :: nat) \<equiv> \<lambda>y. if x + y \<noteq> 0 then if y \<noteq> 0 then y else x else 0"

definition "test_IMP_Minus \<equiv> SKIP"

fun test1 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "test1 x y = (if x \<noteq> 0 then test1 (x - 1 - 1) (y + 1) else test y y)"

ML \<open>
  val dest_HOL_program_const =
    Thm.lhs_of #> Thm.term_of #> Term.head_of #> Term.dest_Const
  val base_name = Long_Name.base_name

  fun HOL_to_IMP_Minus_Calls lookup_fn ctxt HOL_program_def =
    let
      val (args, def_body) = HOL_program_def
        |> Local_Defs.abs_def_rule ctxt |> Thm.rhs_of |> Thm.term_of |> Term.strip_abs
      val (name, typ) = dest_HOL_program_const HOL_program_def
      val base_name = base_name name
      val ret_name = base_name ^ "_ret"
      fun mk_arg_name arg_name = base_name ^ "_" ^ arg_name
      val args = map (@{apply 2 (1)} mk_arg_name) args
      val arg_vars = map (Var o @{apply 2 (1)} (rpair 0)) args
    in def_body
      |> curry Term.subst_bounds (rev arg_vars)
      |> tc_ast_of_term (name, typ) args
      |> IMP_Minus_of_tc_ast (ret_name, map fst args) lookup_fn
      |> assoc_right_Seq
    end
  fun HOL_to_IMP_Minus_binding HOL_program_def =
    let val (name, _) = dest_HOL_program_const HOL_program_def
    in Binding.make (base_name name ^ "_IMP_Minus_Calls", @{here}) end

  fun define_HOL_to_IMP_Minus_Calls lookup_fn ctxt HOL_program_def =
    let
      val binding = HOL_to_IMP_Minus_binding HOL_program_def
      val t = HOL_to_IMP_Minus_Calls lookup_fn ctxt HOL_program_def
    in Local_Theory.define ((binding, NoSyn), ((Thm.def_binding binding, []), t)) #> snd end

  val lookup_fn = (fn (f, ty) =>
    (@{term test_IMP_Minus}, ("test_ret", ["test_y1", "test_y2"])))
  val HOL_program_def = @{thm test1.simps[THEN eq_reflection]}
\<close>

local_setup \<open>define_HOL_to_IMP_Minus_Calls lookup_fn @{context} HOL_program_def\<close>

unbundle Com.no_com_syntax
unbundle IMP_Calls.com'_syntax

thm test1_IMP_Minus_Calls_def

end

