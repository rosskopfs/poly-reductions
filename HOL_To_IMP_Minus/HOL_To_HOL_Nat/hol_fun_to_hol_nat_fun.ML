(*  Title:      hol_fun_to_hol_nat_fun.ML
    Author:     Jay Neubrand, TU Muenchen
    Author:     Andreas Vollert, TU Muenchen
    Author:     Kevin Kappelmann, TU Muenchen
*)
signature HOL_FUN_TO_HOL_NAT_FUN =
sig
  include HAS_LOGGER
  val mk_eq_unfolded_binding : term -> binding

  type compiled_HOL_nat = {related_HOL : term, eq_unfolded : thm}
  val get_compiled_HOL_nat : Proof.context -> term -> compiled_HOL_nat list
  val get_compiled_eq_unfolded  : Proof.context -> term -> thm option
  val get_compiled_related_HOL  : Proof.context -> term -> term option

  val mk_unconditional_eq : term -> term * term
end

structure HOL_Fun_To_HOL_Nat_Fun : HOL_FUN_TO_HOL_NAT_FUN =
struct

val logger = Logger.setup_new_logger Logger.root "HOL_Fun_To_HOL_Nat_Fun"

structure HU = HOLogic
structure TrpUtil = Transport_Util
structure Trp = Transport
open HOL_To_HOL_Nat_Util

val mk_natT = map_fun_types (K natT)

val related_self_binding = @{binding related_self}
fun mk_related_self_binding f = TrpUtil.add_suffix (const_binding f) related_self_binding

val related_transfer_binding = @{binding related_transfer}
fun mk_related_transfer_binding f = TrpUtil.add_suffix (const_binding f) related_transfer_binding

fun mk_fun_nat_binding f = type_suffix_binding (const_binding f) natT

val unfolded_binding = @{binding unfolded}
fun mk_related_unfolded_binding f =
  TrpUtil.add_suffix (TrpUtil.add_suffix Rel_nat_binding (mk_fun_nat_binding f)) unfolded_binding

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
fun get_transport_related_thm f lthy =
  let val f_binding = mk_fun_nat_binding f
  in
    TrpUtil.add_suffix f_binding Trp.binding_related_rewritten
    |> Binding.name_of
    |> Proof_Context.get_thm lthy
  end

fun register_related_transfer_thm f lthy =
  let
    val binding = mk_related_transfer_binding f
    val related_thm = get_transport_related_thm f lthy
      |> Local_Defs.fold lthy
        @{thms rel_inv_Fun_Rel_rel_eq rel_inv_iff_rel[symmetric]  rel_fun_eq_Fun_Rel_rel}
  in
    register_attrs_Rel_nat_thms @{attributes [Rel_nat_compile_nat]} binding [related_thm] lthy
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
      (EqSubst.eqsubst_tac ctxt [1] [f_eq]
      THEN' Rel_nat_transfer_prover prems ctxt)
      |> HEADGOAL)
    val binding = mk_related_unfolded_binding f
    val ([thm], lthy) = register_thms binding [thm] lthy |>> snd
    val (lthy, old_lthy) = `Local_Theory.end_nested lthy
    val phi = Proof_Context.export_morphism old_lthy lthy
    val thm = Morphism.thm phi thm
  in (thm, lthy) end

type compiled_HOL_nat = {related_HOL : term, eq_unfolded : thm}

fun eq_compiled_HOL_nat ({related_HOL = related_HOL1, eq_unfolded = eq_unfolded1},
  {related_HOL = related_HOL2, eq_unfolded = eq_unfolded2}) =
  related_HOL1 aconv related_HOL2
  andalso Thm.eq_thm (eq_unfolded1, eq_unfolded2)

fun morph_update_compiled_HOL_nat morph {related_HOL, eq_unfolded} = {
  related_HOL = Morphism.term morph related_HOL,
  eq_unfolded = Morphism.thm morph eq_unfolded}

structure Compiled_HOL_Nat = Generic_Data(
  type T = compiled_HOL_nat Net.net
  val empty = Net.empty
  val merge = Net.merge eq_compiled_HOL_nat
)

fun get_compiled_HOL_nat ctxt = Net.match_term (Compiled_HOL_Nat.get (Context.Proof ctxt))

fun get_compiled_eq_unfolded ctxt t = case get_compiled_HOL_nat ctxt t of
    [] => NONE
  | {eq_unfolded,...} :: xs =>
      let val _ = if null xs then () else
        @{log Logger.WARN} ctxt (fn _ => Pretty.block [
            Pretty.str "Found multiple eq_unfolded theorems for ",
            Syntax.pretty_term ctxt t,
            Pretty.str ". Picking the first one.",
            Thm.pretty_thm ctxt eq_unfolded
        ] |> Pretty.string_of)
      in SOME eq_unfolded end

fun get_compiled_related_HOL ctxt t = case get_compiled_HOL_nat ctxt t of
    [] => NONE
  | {related_HOL,...} :: xs =>
      let val _ = if null xs then () else
        @{log Logger.WARN} ctxt (fn _ => Pretty.block [
            Pretty.str "Found multiple related HOL terms for ",
            Syntax.pretty_term ctxt t,
            Pretty.str ". Picking the first one.",
            Syntax.pretty_term ctxt related_HOL
        ] |> Pretty.string_of)
      in SOME related_HOL end

val compiled_HOL_nat_term_from_eq_unfolded =
  Thm.concl_of #> dest_eq_equals_prop #> fst #> Term.head_of

fun update_compiled_HOL_nat (x as {eq_unfolded,...}) =
  let val key = compiled_HOL_nat_term_from_eq_unfolded eq_unfolded
  in Compiled_HOL_Nat.map (Net.insert_term eq_compiled_HOL_nat (key, x)) end

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
    val thm = @{thm left_uniqueD} OF [@{thm left_unique_Rel_nat},
      (funpow nargs (fn thm => transfer_fun_RelD OF [thm]) related_transfer_thm) OF assms]
    val thm = thm OF [related_unfolded_thm OF assms]
    val thm = Assumption.export lthy old_lthy thm
    val (lthy, old_lthy) = `Local_Theory.end_nested old_lthy
    val phi = Proof_Context.export_morphism old_lthy lthy
    val thm = Morphism.thm phi thm
    (*TODO: registration of compiled_HOL_nat at this point is not particularly pretty and should
    be moved into a separate declaration*)
    val attr = Attrib.internal (Binding.pos_of binding) (fn morph =>
      Thm.declaration_attribute (fn thm => {eq_unfolded = thm, related_HOL = t}
        |> morph_update_compiled_HOL_nat morph
        |> update_compiled_HOL_nat))
  in register_attrs_thms [attr] binding [thm] lthy end

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
    val (_, lthy) = register_eq_unfolded_thm f_with_sort related_transfer_thm related_unfolded_thm lthy
  in lthy end

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>function_compile_nat\<close>
    "Compile HOL equation to HOL equation on natural numbers"
    (Parse.thm >> (fn (thm_ref, _) => fn lthy =>
      let val thm = Proof_Context.get_fact_single lthy thm_ref
      in function_compile_nat_cmd thm lthy end))

val unconditional_nat_binding = @{binding "unconditional"}
fun mk_unconditional_nat_binding b = TrpUtil.add_suffix b unconditional_nat_binding

fun mk_unconditional_eq f_eq =
  let
    val (lhs, rhs) = f_eq |> Logic.strip_imp_concl |> dest_eq_equals_prop
    val f = lhs |> Term.head_of
    val (typrep_arg_count, rem_args) =
      lhs |> Term.args_of |> chop_prefix (is_itself o Term.fastype_of) |>> List.length
    val f'_typ = List.map Term.fastype_of rem_args ---> Term.fastype_of lhs
    val f' = f |> Term.map_types (K f'_typ)
    fun rewrite_rhs t =
      let
        val (head, args) = Term.strip_comb t
        val is_rec_call = (f = head)
        val _ = (is_rec_call andalso length args < typrep_arg_count)
          andalso raise TERM ("Can't strip all '_ itself' arguments", [t])
      in
        (if is_rec_call then (f', drop typrep_arg_count args) else (head, args))
        ||> map rewrite_rhs |> Term.list_comb
      end
    val lhs' = Term.list_comb (f', rem_args)
    val rhs' = rewrite_rhs rhs
  in (lhs', rhs') end

fun unconditional_nat_command f_eq basename lthy =
  let
    val (f_eq, _) =
      Thm.prop_of f_eq |> (fn t => yield_singleton (Variable.import_terms false) t lthy)

    val eq as (lhs, _) = mk_unconditional_eq f_eq
    val f = Term.head_of lhs

    val base_binding = case basename of
        SOME (name, _) => Binding.name name
      | NONE => const_binding f
    val f'_binding = mk_unconditional_nat_binding base_binding
    val f' = Free (Binding.name_of f'_binding, fastype_of f)
    val f_to_f' = Term.map_aterms (fn t => if t = f then f' else t)
    val (lhs, rhs) = apply2 f_to_f' eq
  in register_fun (f'_binding) lhs rhs lthy end

local
  val parser = Parse.thm -- Scan.option (\<^keyword>\<open>basename\<close> |-- Parse.name_position)
in
  val _ = Outer_Syntax.local_theory
    \<^command_keyword>\<open>unconditional_nat\<close>
    "create function without Rel_nat/rel_fun assumptions and TYPE(_) args"
    (parser >> (fn ((thm_ref, _), namepos_opt) => fn lthy =>
      let val thm = Proof_Context.get_fact_single lthy thm_ref
      in unconditional_nat_command thm namepos_opt lthy end))
end

end
