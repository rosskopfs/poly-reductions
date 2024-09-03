(*  Title:      hol_fun_to_hol_nat_fun.ML
    Author:     Jay Neubrand, TU Muenchen
    Author:     Andreas Vollert, TU Muenchen
    Author:     Kevin Kappelmann, TU Muenchen
*)
signature HOL_FUN_TO_HOL_NAT_FUN =
sig
end

structure HOL_Fun_To_HOL_Nat_Fun : HOL_FUN_TO_HOL_NAT_FUN =
struct

structure HU = HOLogic
structure TrpUtil = Transport_Util
structure Trp = Transport
open HOL_To_HOL_Nat_Util

val mk_natT = map_fun_types (K natT)

val related_self_binding = @{binding related_self}
fun mk_related_self_binding t = TrpUtil.add_suffix (term_binding t) related_self_binding

val related_transfer_binding = @{binding related_transfer}
fun mk_related_transfer_binding t = TrpUtil.add_suffix (term_binding t) related_transfer_binding

fun mk_fun_nat_binding t = type_suffix_binding (term_binding t) natT

val unfolded_binding = @{binding unfolded}
fun mk_related_unfolded_binding t =
  TrpUtil.add_suffix (TrpUtil.add_suffix Rel_nat_binding (mk_fun_nat_binding t)) unfolded_binding

val eq_binding = @{binding eq}
fun mk_eq_unfolded_binding t =
  TrpUtil.add_suffix (TrpUtil.add_suffix (mk_fun_nat_binding t) eq_binding) unfolded_binding

fun register_related_self_thm f lthy =
  let
    val binding = mk_related_self_binding f
    val rel = fastype_of f |>
      mk_Rel_fun_from_type (app o app mk_transport_rel_fun_dummyT)
      (Trp.map_dummyT \<^term>\<open>compile_nat_type_def.R\<close> |> K)
    fun solve_tac ctxt = HEADGOAL (TRY o fun_rel_intro_tac transport_fun_RelI ctxt
      THEN' solve_fun_rel_tac transport_fun_RelD ctxt)
    val thm = rel $ Trp.map_dummyT f $ Trp.map_dummyT f
      |> Syntax.check_term lthy
      |> prove_goal solve_tac lthy
  in register_attrs_thms @{attributes [trp_in_dom]} binding [thm] lthy end

fun wrapper_trp_api binding cx yT lthy =
  let
    val lthy = Local_Theory.begin_nested lthy |> snd
    val ctxt = TrpUtil.set_proof_mode_schematic lthy
    val ([L, R, y], maxidx) = Trp.setup_goal_terms [NONE, NONE, NONE] ctxt cx yT
    val thms = Trp.setup_goals_blackbox ctxt (L, R, cx) maxidx
      |> prove_goals (fn ctxt => HEADGOAL (Goal.conjunction_tac THEN' Trp.transport_prover ctxt))
        ctxt
  in Trp.after_qed_blackbox (binding, NoSyn) [thms] lthy |> snd |> Local_Theory.end_nested end

fun register_transport_term f lthy =
  let
    val binding = mk_fun_nat_binding f
    val yT = fastype_of f |> mk_natT
    val ct = Thm.cterm_of lthy f
  in wrapper_trp_api binding ct yT lthy end

(*TODO: not super stable; needs better transport API*)
fun get_transport_related_thm t lthy =
  let val t_binding = mk_fun_nat_binding t
  in
    TrpUtil.add_suffix t_binding Trp.binding_related_rewritten
    |> Binding.name_of
    |> Proof_Context.get_thm lthy
  end

fun register_related_transfer_thm f lthy =
  let
    val binding = mk_related_transfer_binding f
    val related_thm = get_transport_related_thm f lthy
  in
    register_attrs_thms
      @{attributes [folded rel_inv_Fun_Rel_rel_eq rel_inv_iff_rel[symmetric] rel_fun_eq_Fun_Rel_rel,
        transfer_rule]}
      binding [related_thm] lthy
    |>> apsnd the_single
  end

fun mk_related_unfolded_assms Ts ctxt =
  let
    val (xbinders, ctxt) = Binders.fix_binders (map (K ("x", dummyT)) Ts) ctxt
    val (ybinders, ctxt) = Binders.fix_binders (map (pair "y") Ts) ctxt
    fun mk_asm (_, x) ((_, T), y) =
      mk_Rel_fun_from_type (app o app mk_transfer_rel_fun_dummyT) (mk_Rel_nat dummyT |> K) T $ x $ y
      |> HU.mk_Trueprop
    val assms = map2 mk_asm xbinders ybinders
  in (assms, xbinders, ybinders, ctxt) end

fun register_related_unfolded_thm f f_eq lthy =
  let
    val lthy = Local_Theory.begin_nested lthy |> snd |> TrpUtil.set_proof_mode_schematic
    val Ts = term_binder_types f
    val (gbinder, lthy) = Binders.fix_binder ("g", dummyT) lthy
      |>> apsnd (dest_Free #> apfst (rpair 0) #> Var) (*TODO: could there be any name clashes here?*)
    val (assms, _, ybinders, lthy) = mk_related_unfolded_assms Ts lthy
    val concl = mk_Rel_nat dummyT $ snd gbinder $ list_comb (f, map snd ybinders) |> HU.mk_Trueprop
    val (concl :: assms, lthy) = Syntax.check_terms lthy (concl :: assms)
      |> (fn ts => Variable.importT_terms ts lthy)
    val thm = Goal.prove lthy [] assms concl (fn {prems = prems, context = ctxt,...} =>
      let val ctxt = fold (snd oo Thm.apply_attribute Transfer.transfer_add) prems (Context.Proof ctxt)
        |> Context.proof_of
      in
        (EqSubst.eqsubst_tac ctxt [1] [f_eq]
        THEN' Transfer.transfer_prover_tac ctxt)
        |> HEADGOAL
      end)
    val binding = mk_related_unfolded_binding f
    val ([thm], lthy) =
      register_attrs_thms @{attributes [transfer_rule]} binding [thm] lthy |>> snd
    val (lthy, old_lthy) = `Local_Theory.end_nested lthy
    val phi = Proof_Context.export_morphism old_lthy lthy
    val thm = Morphism.thm phi thm
  in (thm, lthy) end

fun register_eq_unfolded_thm t related_transfer_thm related_unfolded_thm lthy =
  let
    val lthy = Local_Theory.begin_nested lthy |> snd |> TrpUtil.set_proof_mode_schematic
    val binding = mk_eq_unfolded_binding t
    val nargs = fun_nargs t
    val (assms, _, _, lthy) = mk_related_unfolded_assms (term_binder_types t) lthy
    val (assms, lthy) = Syntax.check_terms lthy assms
      |> (fn ts => Variable.importT_terms ts lthy)
      |>> map (Thm.cterm_of lthy)
    val ((assms, lthy), old_lthy) = `(Assumption.add_assumes assms) lthy
    val thm = @{thm left_uniqueD} OF [
        @{thm left_unique_Rel_nat},
        (funpow nargs (fn thm => transfer_fun_RelD OF [thm]) related_transfer_thm) OF assms,
        related_unfolded_thm OF assms
      ]
    val thm = Assumption.export lthy old_lthy thm
    val (lthy, old_lthy) = `Local_Theory.end_nested old_lthy
    val phi = Proof_Context.export_morphism old_lthy lthy
    val thm = Morphism.thm phi thm
  in register_thms binding [thm] lthy end

fun function_compile_nat_cmd f_eq lthy =
  let
    val f = f_eq |> dest_eq_equals_thm |> fst |> Term.head_of
    val f_with_sort = f |> map_types add_compile_nat_sort
    (*TODO: re-use more theorems/terms created in below functions instead of re-retrieving them
    from the context*)
    val ((_, related_transfer_thm), lthy) = lthy
      |> register_related_self_thm f |> snd
      |> register_transport_term f_with_sort
      |> register_related_transfer_thm f
    val (related_unfolded_thm, lthy) = register_related_unfolded_thm f_with_sort f_eq lthy
    val lthy =
      register_eq_unfolded_thm f_with_sort related_transfer_thm related_unfolded_thm lthy |> snd
  in lthy end

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>function_compile_nat\<close>
    "Compile HOL equation to HOL equation on natural numbers"
    (Parse.thm >> (fn (thm_ref, _) => fn lthy =>
      let val thm = Proof_Context.get_fact lthy thm_ref |> the_single
      in function_compile_nat_cmd thm lthy end))


fun unrelate_nat_command f_eq _ lthy =
  let
    val (lhs, rhs) =
      (* import to avoid free variable name clashes *)
      yield_singleton (Variable.import_terms false) (Thm.prop_of f_eq) lthy |> fst
      |> Logic.strip_imp_concl |> dest_eq_equals_prop
    val f = lhs |> Term.head_of |> Term.dest_Const

    fun is_typrep (Type (@{type_name itself}, [_])) = true | is_typrep _ = false
    val (typrep_arg_count, rem_args) =
      lhs |> Term.args_of |> chop_prefix (is_typrep o Term.fastype_of) |>> List.length

    val f'_typ = List.map Term.fastype_of rem_args ---> Term.fastype_of lhs

    val f'_binding =
      Transport_Util.add_suffix (Const f |> term_binding) (@{binding unconditional})
    val f'_name = f'_binding |> Binding.name_of
    val f' = Free (f'_name, f'_typ)

    (* at each recursive call f TYPE('a) ... TYPE('b) x1 ... xn, strip the leading TYPE arguments *)
    fun rewrite_rhs t =
      let
        val (head, args) = Term.strip_comb t
        val is_rec_call = case head of Const g => f = g | _ => false
        val _ = (is_rec_call andalso length args < typrep_arg_count)
          andalso raise TERM ("Can't strip all '_ itself' arguments", [t])
      in
        (if is_rec_call then (f', drop typrep_arg_count args) else (head, args))
        ||> map rewrite_rhs |> Term.list_comb
      end

    val lhs' = Term.list_comb (f', rem_args)
    val rhs' = rewrite_rhs rhs
    val _ = @{print} (lhs', rhs')
    val lthy' = register_fun f'_binding lhs' rhs' lthy

  in lthy' end

local
  (* TODO: basename support *)
  val parser = Parse.thm -- Scan.option (\<^keyword>\<open>basename\<close> |-- Parse.name_position)
in
  val _ = Outer_Syntax.local_theory
    \<^command_keyword>\<open>unconditional_nat\<close>
    "remove Rel_nat/rel_fun assumptions and TYPE(_) args"
    (parser >> (fn ((thm_ref, _), namepos_opt) => fn lthy =>
      let val thm = Proof_Context.get_fact lthy thm_ref |> the_single
      in unrelate_nat_command thm namepos_opt lthy end))
end

end