(*  Title:      datatype_to_nat.ML
    Author:     Jay Neubrand, TU Muenchen
    Author:     Andreas Vollert, TU Muenchen
    Author:     Kevin Kappelmann, TU Muenchen
*)
signature DATATYPE_TO_NAT =
sig
end

structure Datatype_To_Nat : DATATYPE_TO_NAT =
struct

structure BU = BNF_Util
structure HU = HOLogic
structure TrpUtil = Transport_Util
structure Trp = Transport
structure TacU = Tactic_Util
open HOL_To_HOL_Nat_Util

fun mk_denatify T = \<^Const>\<open>denatify T\<close>
val mk_denatify_binding  = type_suffix_binding (const_binding @{term denatify})

fun mk_natify T = \<^Const>\<open>natify T\<close>
val mk_natify_binding = type_suffix_binding (const_binding @{term natify})

val fst_nat = \<^Const>\<open>fst_nat\<close>
val pair_nat = \<^Const>\<open>pair_nat\<close>

fun mk_ctr_binding ctr = type_suffix_binding (const_binding ctr) natT

val mk_ctr_tag = mk_nat

fun find_ctr_tag ctrs ctxt t = find_index (can (Ctr_Sugar_Util.fo_match ctxt t)) ctrs
val find_mk_ctr_tag = mk_ctr_tag ooo find_ctr_tag

val case_binding = @{binding case}
val mk_case_binding = type_suffix_binding case_binding #> (fn b => type_suffix_binding b natT)

fun mk_ctr_rhs ctr_tag [] = mk_ctr_rhs ctr_tag [mk_nat 0] (*arbitrary number for empty argument list*)
  | mk_ctr_rhs ctr_tag args =
    let fun mk_arg [] = error "oops, this should not happen - unreachable code."
          | mk_arg [t] = t
          | mk_arg (t :: ts) = pair_nat $ t $ mk_arg ts
    in pair_nat $ ctr_tag $ mk_arg args end

fun nat_selector ctr_nargs t i = \<^Const>\<open>nat_selector for \<open>mk_nat i\<close> \<open>mk_nat ctr_nargs\<close> t\<close>

fun mk_ctr_condition t i = HU.mk_eq (fst_nat $ t, mk_ctr_tag i)

fun register_ctr ctrs ctr lthy =
  let
    val (binders, _) = Binders.fix_binders (map (K ("x", natT)) (term_binder_types ctr)) lthy
    val args = map snd binders
    val rhs = mk_ctr_rhs (find_mk_ctr_tag ctrs lthy ctr) args
    val lhs = Free (mk_ctr_binding ctr |> Binding.name_of, map (snd o fst) binders ---> natT)
    val eq = BU.mk_Trueprop_eq (list_comb (lhs, args), rhs)
  in register_def [] eq lthy end

fun register_ctrs ctrs = fold_map (register_ctr ctrs) ctrs

fun mk_trport_fun transf lhs ctrs casex lthy =
  let
    val transf = Trp.map_dummyT transf
    fun mk_case ctr =
      let
        val ctr_nargs = fun_nargs ctr
        val (binders, _) = Binders.fix_binders (map_range (K ("x", dummyT)) ctr_nargs) lthy
        val trp_args = map (app transf o Bound) (ctr_nargs - 1 downto 0)
      in list_comb (Trp.map_dummyT ctr, trp_args) |> curry Logic.rlist_abs (map fst (rev binders)) end
    val (free, _) = Binders.fix_binder ("x", dummyT) lthy |>> snd
    val lhs = lhs $ free
    val rhs = list_comb (Trp.map_dummyT casex, map mk_case ctrs @ [free])
  in (lhs, rhs) end

fun register_trport_fun binding transf lhs ctrs casex lthy =
  mk_trport_fun transf lhs ctrs casex lthy
  |> (fn (lhs, rhs) => register_fun binding lhs rhs lthy)

fun register_natify T = register_trport_fun (mk_natify_binding T) (mk_natify T)
  (mk_natify dummyT)
fun register_denatify T = register_trport_fun (mk_denatify_binding T) (mk_denatify T)
  (mk_denatify dummyT)

fun prove_instantiation solve_tac =
  let fun tac ctxt concl =
    let val var = dest_comb concl |> snd |> dest_comb |> snd
    in induction_var_tac ctxt var THEN_ALL_NEW solve_tac ctxt end
  in
    Class.prove_instantiation_instance (fn ctxt =>
      Class.intro_classes_tac ctxt []
      THEN HEADGOAL (TacU.FOCUS_PARAMS_CTXT' (TacU.SUBGOAL_STRIPPED (snd o snd) o tac) ctxt))
  end

fun mk_ctr_Rel ctxt ctr =
  let
    val ctr_nat = mk_ctr_binding ctr |> const_from_binding ctxt
    val ctrT = fastype_of ctr |> map_atyps (add_compile_nat_sort dummyT |> K)
  in
    mk_Rel_fun_from_type mk_transfer_rel_fun mk_Rel_nat ctrT $ ctr_nat $ Trp.map_dummyT ctr
    |> Syntax.check_term ctxt
  end

fun mk_ctrl_Rel_thm ctr ctxt = mk_ctr_Rel ctxt ctr
  |> prove_goal (fn ctxt => HEADGOAL
      (TacU.TRY' (fun_rel_intro_tac transfer_fun_RelI ctxt)
      THEN' solve_compiled_Rel_nat_tac transfer_fun_RelD ctxt))
    ctxt

fun register_ctr_Rel_thm ctr lthy =
  let
    val ctrl_Rel_thm = mk_ctrl_Rel_thm ctr lthy
    val binding = TrpUtil.add_suffix Rel_nat_binding (mk_ctr_binding ctr)
  in register_Rel_nat_thms binding [ctrl_Rel_thm] lthy end

fun register_ctr_Rel_thms ctrs = fold_map (fn ctr => register_ctr_Rel_thm ctr #>> snd) ctrs

val selector_binding = @{binding selector}
val Rel_nat_selector_binding = (TrpUtil.add_suffix Rel_nat_binding selector_binding)
val mk_Rel_nat_selector_type_binding = type_suffix_binding Rel_nat_selector_binding
fun mk_Rel_nat_selector_ctr_binding ctr = TrpUtil.add_suffix
  (TrpUtil.add_suffix Rel_nat_binding selector_binding) (const_binding ctr)

fun register_nat_selector_Rel_thm natify_simps (ctrs_nat_def, ctr) lthy =
  let
    val (argTs, headT) = dest_Const_type ctr |> strip_type
    val ctr_nargs = length argTs
    val (args, lthy) =
      Variable.variant_fixes (map (K "x") argTs) lthy
      |>> (fn vars => map2 (curry Free) vars argTs)
    val (prem_freet, lthy) = yield_singleton Variable.variant_fixes "n" lthy |>> (rpair natT #> Free)
    val prem = mk_Rel_nat headT $ prem_freet $ list_comb (ctr, args) |> HOLogic.mk_Trueprop
    fun reg_ctr_des_Rel_thm_arg (i, arg) =
      let
        fun tac ctxt = solve_compiled_Rel_nat_tac transfer_fun_RelD
          (ctxt addsimps (@{thm nat_selector_eq} :: ctrs_nat_def :: natify_simps))
        val (goal, lthy) = mk_Rel_nat (fastype_of arg) $ nat_selector ctr_nargs prem_freet i $ arg
          |> HOLogic.mk_Trueprop
          |> curry Logic.mk_implies prem
          |> map_types add_compile_nat_sort
          |> (fn t => yield_singleton (Variable.import_terms false) t lthy)
      in Goal.prove lthy [] [] goal (#context #> tac #> HEADGOAL) end
    val binding = mk_Rel_nat_selector_ctr_binding ctr
  (*since these theorems make transfer loop in most cases, they are not registered by default as
  Rel_nat relatedness theorems*)
  in register_thms binding (map_index reg_ctr_des_Rel_thm_arg args) lthy |>> snd end

fun register_nat_selector_Rel_thms T ctrs natify_simps ctrs_nat_defs =
  fold_map (register_nat_selector_Rel_thm natify_simps) (map2 pair ctrs_nat_defs ctrs)
  #> (fn (thms, lthy) => register_attrs_thms @{attributes [Rel_nat_compile_nat_selector]}
      (mk_Rel_nat_selector_type_binding T) (flat thms) lthy
    |> snd |> pair thms)

val mk_Rel_nat_eq_fst_nat_case_binding = type_suffix_binding @{binding "Rel_nat_eq_fst_nat_case"}

fun register_Rel_nat_eq_fst_nat_case_thm ctrs casex simps split lthy =
  let
    val rel = mk_transfer_rel_fun_dummyT $ mk_Rel_nat dummyT $ Trp.map_dummyT @{term "(=)"}
    fun create_lambdas (i, ctr) =
      fastype_of ctr |> strip_type |> fst |> map (map_atyps add_compile_nat_sort)
      |> List.foldr (uncurry absdummy) (mk_nat i)
    val caset = list_comb (casex |> map_types (K dummyT), map_index create_lambdas ctrs)
    val (goal, lthy) = rel $ fst_nat $ caset |> HOLogic.mk_Trueprop
      |> (fn goal => yield_singleton (Variable.import_terms false) goal lthy)
      |>> Syntax.check_prop lthy
    fun tac ctxt =
      solve_compiled_Rel_nat_tac transfer_fun_RelD (ctxt addsimps simps |> Splitter.add_split split)
    val thm = Goal.prove lthy [] [] goal (#context #> tac #> HEADGOAL)
    val binding = ctrs |> hd |> fastype_of |> strip_type |> snd |> mk_Rel_nat_eq_fst_nat_case_binding
  in register_Rel_nat_thms binding [thm] lthy |>> snd end

fun register_case T ctrs casex ctxt =
  let
    val case_args_Ts = fastype_of casex |> strip_type |> fst
    val (case_binders, ctxt) = case_args_Ts |> split_last |> fst
      |> (fn Ts => Binders.fix_binders (map (K (pair "f" dummyT)) Ts) ctxt)
    val (case_arg_binder, ctxt) = Binders.fix_binder ("n", natT) ctxt
    val case_arg_free = snd case_arg_binder
    val ctrs_conditions = map_index (fst #> mk_ctr_condition case_arg_free) ctrs
    fun mk_case case_free ctr_nargs =
      map_range (nat_selector ctr_nargs case_arg_free) ctr_nargs
      |> curry list_comb case_free
    val all_case_binders = case_arg_binder :: rev case_binders
    val case_rhs = (ctrs_conditions, map2 mk_case (map snd case_binders) (map fun_nargs ctrs))
      |-> BU.mk_IfN dummyT
      |> Binders.replace_frees all_case_binders
      |> curry Logic.rlist_abs (map fst all_case_binders)
      |> Syntax.check_term ctxt
    val case_lhs = Free (mk_case_binding T |> Binding.name_of, dummyT)
    val case_eq = BU.mk_Trueprop_eq (case_lhs, case_rhs) |> Syntax.check_term ctxt
  in register_def @{attributes [simp]} case_eq ctxt end

fun mk_case_Rel casex case_nat ctxt =
  let
    val (R, ctxt) = Binders.fix_binder ("R", dummyT) ctxt
    val caseT = fastype_of casex
    val case_toT = caseT |> strip_type |> snd
  in
    mk_Rel_fun_from_type (app o app mk_transfer_rel_fun_dummyT)
      (fn T => if T = case_toT then snd R else mk_Rel_nat dummyT) caseT
      $ Trp.map_dummyT case_nat $ Trp.map_dummyT casex
    |> Syntax.check_term ctxt
    |> rpair R
  end

fun mk_case_Rel_thm casex case_nat case_nat_def ctxt =
  let
    fun induction_tac ctxt concl =
      let val var = HU.dest_Trueprop concl |> dest_comb |> snd |> strip_comb |> snd |> List.last
      in induction_var_tac ctxt var end
    fun tac ctxt =
      EqSubst.eqsubst_tac ctxt [1] [case_nat_def]
      THEN' fun_rel_intro_tac transfer_fun_RelI ctxt
      THEN_ALL_NEW TacU.FOCUS_PARAMS_CTXT' (TacU.SUBGOAL_STRIPPED (snd o snd) o induction_tac) ctxt
      THEN_ALL_NEW solve_compiled_Rel_nat_tac transfer_fun_RelD ctxt
  in
    mk_case_Rel casex case_nat ctxt
    |> (fn (t, binder) => prove_goal_schematics [fst (fst binder)] (HEADGOAL o tac) ctxt t)
  end

fun register_case_Rel_thm T casex case_nat case_nat_def lthy =
  let
    val case_Rel_thm = mk_case_Rel_thm casex case_nat case_nat_def lthy
    val binding = TrpUtil.add_suffix Rel_nat_binding (mk_case_binding T)
  in register_Rel_nat_thms binding [case_Rel_thm] lthy end

fun datatype_compile_nat T ctrs casex split thy =
  let
    val lthy = Named_Target.theory_init thy
    (*create constructors*)
    val (ctrs_nat, lthy) = register_ctrs ctrs lthy
    fun morph_def_thm phi (t, (_, thm)) = (Morphism.term phi t, Morphism.thm phi thm)
    (*create case expression*)
    val (case_nat, lthy) = register_case T ctrs casex lthy
    val ((ctrs_nat, (case_nat, case_nat_def)), thy) = ((ctrs_nat, case_nat), lthy)
      |> Local_Theory.exit_result_global (fn phi => fn (ctrs_nat, case_nat) =>
        (map (morph_def_thm phi) ctrs_nat, morph_def_thm phi case_nat))
    val (ctrs_nat, ctrs_nat_def) = split_list ctrs_nat

    (*start instantiation*)
    val Tname = dest_Type T |> fst
    val Tfrees = Proof_Context.init_global thy
      |> Variable.invent_types (map (K compile_natS) (Term.add_tvarsT T [])) |> fst
    val lthy = thy
      |> Class.instantiation ([Tname], Tfrees, compile_natS)
      |> Local_Theory.begin_nested |> snd

    (*create transport functions*)
    val lthy = register_natify T ctrs_nat casex lthy
      (*we pass the rhs of case_nat to create denatify due to termination issues: we do not have a
      congruence rule for case_nat. As a result, the function package's termination checker cannot
      prove termination if we pass case_nat instead of its rhs definition (which uses if-then-elses).*)
      |> register_denatify T ctrs (Thm.concl_of case_nat_def |> dest_eq_equals_prop |> snd)

    (*remove simps from simp set since they create loops*)
    val (natify, denatify) = (mk_natify_binding, mk_denatify_binding)
      |> apply2 (fn f => f T |> const_from_binding lthy)
    val (natify_simps, denatify_simps) = (natify, denatify)
      |> apply2 (get_fun_simps lthy #> cat_options #> flat)
    val lthy = del_simps (natify_simps @ denatify_simps) lthy

    (*prove the desired definition of denatify in terms of case_nat*)
    fun denatify_eq_case_tac ctxt = resolve_tac lthy @{thms ext}
      THEN' EqSubst.eqsubst_tac ctxt [1] denatify_simps
      THEN' simp_tac (clear_simpset ctxt addsimps [case_nat_def])
    val (denatify_def, lthy) = mk_trport_fun (mk_denatify T) (mk_denatify dummyT) ctrs case_nat lthy
      |> snd |> dest_comb |> fst
      |> HU.mk_eq o pair denatify
      |> Syntax.check_term lthy
      |> prove_goal (HEADGOAL o denatify_eq_case_tac) lthy
      |> (fn thm =>
        let val binding = TrpUtil.add_suffix
          (TrpUtil.add_suffix (mk_denatify_binding T) @{binding "eq"})
          (mk_case_binding T)
        in register_thms binding [thm] lthy end)
      |>> snd

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy
    val phi = Proof_Context.export_morphism old_lthy lthy
    val (natify_simps, denatify_simps) = (natify_simps, denatify_def)
      |> apply2 (map (Morphism.thm phi))

    (*prove instantiation*)
    fun solve_instantiation_tac ctxt =
      let val simps = @{thm nat_selector_eq} :: ctrs_nat_def @ natify_simps
      in
        EqSubst.eqsubst_tac ctxt [1] denatify_simps
        THEN' asm_full_simp_tac (ctxt addsimps simps)
      end
    val lthy = prove_instantiation solve_instantiation_tac lthy

    (*create relator theorems for case*)
    val phi = Proof_Context.export_morphism lthy (Proof_Context.init_global thy)
    val natify_simps = map (Morphism.thm phi) natify_simps
    val lthy = Local_Theory.begin_nested lthy |> snd
    val lthy = lthy addsimps @{thm nat_selector_eq} :: ctrs_nat_def @ natify_simps
    (*create relator theorem for case*)
    val (case_Rel_thm, lthy) = register_case_Rel_thm T casex case_nat case_nat_def lthy |>> snd
    (*create relator theorems for constructors*)
    val (ctr_Rel_thms, lthy) = register_ctr_Rel_thms ctrs lthy
    val lthy = Local_Theory.end_nested lthy
    (*create discriminator/selectors relatedness theorems*)
    val (nat_selector_Rel_thms, lthy) =
      register_nat_selector_Rel_thms T ctrs natify_simps ctrs_nat_def lthy
    val (Rel_nat_eq_fst_nat_case_thm, lthy) =
      register_Rel_nat_eq_fst_nat_case_thm ctrs casex (natify_simps @ ctrs_nat_def) split lthy

    (*create bundle of relatedness theorems*)
    val (_, lthy) = register_attrs_thms (@{attributes [Rel_nat_compile_nat]}) (mk_Rel_nat_type_binding T)
      (flat (Rel_nat_eq_fst_nat_case_thm :: case_Rel_thm :: ctr_Rel_thms @ nat_selector_Rel_thms)) lthy
  in lthy end

fun datatype_compile_nat_cmd T thy =
  let
    val ctxt = Proof_Context.init_global thy
    val Tname = T |> Proof_Context.read_type_name {proper = true, strict = false} ctxt
      |> dest_Type |> fst
  in case Ctr_Sugar.ctr_sugar_of ctxt Tname of
      NONE => error ("Unknown datatype " ^ Tname)
    | SOME sugar => datatype_compile_nat (#T sugar) (#ctrs sugar) (#casex sugar) (#split sugar) thy
  end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>datatype_compile_nat\<close>
    "Create datatype encoding of datatype"
    (Parse.typ >> datatype_compile_nat_cmd >> Toplevel.begin_main_target false)

end