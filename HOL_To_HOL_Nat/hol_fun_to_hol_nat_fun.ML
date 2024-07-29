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

open BNF_Util
open HOLogic
structure TrpUtil = Transport_Util
structure Trp = Transport
structure TacU = Tactic_Util
open HOL_To_HOL_Nat_Util

fun mk_Fun_Rel R S =
  let
    val ((RA, RB), RT) = `BNF_Util.dest_pred2T (fastype_of R);
    val ((SA, SB), ST) = `BNF_Util.dest_pred2T (fastype_of S);
  in
    Const (\<^const_name>\<open>Fun_Rel_rel\<close>, RT --> ST --> (RA --> SA) --> (RB --> SB) --> \<^typ>\<open>bool\<close>) $ R $ S
  end;

fun mk_related_self_thm t lthy =
  let
    val (_, lthy) = (Local_Theory.begin_nested lthy);

    val rel_const_name = fst (dest_Const \<^term>\<open>compile_nat_type_def.R\<close>)
    fun mk_rel T =
      let
        val (Ts, T) = strip_type T
        val t = Const (rel_const_name, TrpUtil.mk_hom_rel_type T)
      in fold_rev mk_Fun_Rel (map mk_rel Ts) t end
    val goal = mk_rel (fastype_of t) $ t $ t  |> mk_Trueprop

    val thm = Goal.prove lthy [] [] goal (fn {context=ctxt, ...} => asm_full_simp_tac ctxt 1);

    val name = Term.term_name t ^ "_related_self";
    val lthy = Local_Theory.note ((Binding.name name, @{attributes [trp_in_dom]}), [thm]) lthy |> snd

  in
    Local_Theory.end_nested lthy
  end;

fun wrapper_trport_api binding yT cx lthy =
  let
    val (_, lthy) = (Local_Theory.begin_nested lthy);
    val ctxt = TrpUtil.set_proof_mode_schematic lthy;

    val ([L, R, y], maxidx) =
      let
        val opts_constraints =
          [TrpUtil.mk_hom_rel_type (Thm.typ_of_cterm cx), TrpUtil.mk_hom_rel_type yT, yT]
          |> map Type.constraint;
        val params_maxidx = ~1;
        fun create_var n maxidx = Term_Util.fresh_var n dummyT params_maxidx ||> Integer.max maxidx;
        val (ts, maxidx) =
          fold_map create_var ["L", "R", "y"] params_maxidx
          |>> map2 I opts_constraints;
      in (ts, maxidx) end;

    val goals =
      Trp.setup_goals_blackbox ctxt (L, R, cx) maxidx
      |> map fst;

    val thms = Goal.prove_common ctxt NONE [] [] goals (fn {context=ctxt, ...} =>
      HEADGOAL Goal.conjunction_tac
      THEN HEADGOAL (Trp.transport_prover ctxt))

    val lthy = Trp.after_qed_blackbox (binding, NoSyn) [thms] lthy

  in Local_Theory.end_nested lthy end;

fun mk_natT T = let val (Ts, T) = strip_type T
  in (map mk_natT Ts) ---> natT end

fun mk_trp_term t ctxt =
  let
    val binding = type_suffix_binding (term_binding t) natT
    val yT = mk_natT (fastype_of t)
    val ct = Thm.cterm_of ctxt t;
  in wrapper_trport_api binding yT ct ctxt end;

fun mk_itself_natT T = let val Ts = fold_atyps (insert (op =)) T [] |> rev
  in map Term.itselfT Ts ---> mk_natT T end;

fun mk_lifting_thm t lthy =
  let
    val (_, lthy) = (Local_Theory.begin_nested lthy);

    val t_nat_name = dest_Const t |> fst |> suffix "_nat";
    val nat_base_name = Long_Name.base_name t_nat_name

    val T = fastype_of t;
    val t_nat = Const (Local_Theory.full_name lthy (Binding.name nat_base_name), mk_itself_natT T)
    val Ts = fold_atyps (insert (op =)) T [] |> rev;
    val t_nat_app = list_comb (t_nat, map (fn T => \<^Const>\<open>Pure.type T\<close>) Ts);

    fun mk_rel T =
      let
        val (Ts, T) = strip_type T
        val t = mk_Rel_nat T
      in fold_rev mk_rel_fun (map mk_rel Ts) t end
    val goal = mk_Trueprop (mk_rel T $ t_nat_app $ t);

    val related_thm = Proof_Context.get_thm lthy (nat_base_name ^ "_related'");
    fun solve_tac ctxt = asm_full_simp_tac (clear_simpset ctxt addsimps
      @{thms rel_fun_eq_Fun_Rel_rel rel_inv_iff_rel rel_inv_Fun_Rel_rel_eq[symmetric]})
    val thm = Goal.prove lthy [] [] goal (fn {context=ctxt, ...} =>
      Method.insert_tac ctxt [related_thm] 1
      THEN solve_tac ctxt 1);

    val binding_name = Binding.name (nat_base_name ^ "_lifting");
    val (_, lthy) = Local_Theory.note ((binding_name, @{attributes [transfer_rule]}), [thm]) lthy;
    val lthy = Local_Theory.end_nested lthy;
  in lthy end;

fun mk_case_defs t lthy =
  let
    val fun_name = Term.term_name t
    val case_name = fun_name ^ "_case_def"
    val fun_simps = if is_Const t
      then Proof_Context.get_thms lthy (fun_name ^ ".simps")
      else error ("Undefined function name: " ^ fun_name)
    val case_thm = Simps_Case_Conv.to_case lthy fun_simps
  in Local_Theory.note ((Binding.name case_name, []), [case_thm]) lthy |> snd end;


fun mk_nat_synth t lthy =
  let
    val (_, lthy) = (Local_Theory.begin_nested lthy);

    val T = fastype_of t;
    val (binder_Ts, body_T) = strip_type T;
    val free_Ts = fold_atyps (insert (op =)) T [] |> rev;

    val t_name = dest_Const t |> fst;
    val t_base_name = Long_Name.base_name t_name;
    val t_nat_base_name = t_base_name ^ "_nat";
    val t_nat_name = Local_Theory.full_name lthy (Binding.name t_nat_base_name);
    val t_nat = Const (t_nat_name, mk_itself_natT T);


    val (arg_ts, (arg_nat_ts, lthy)) =
      mk_Frees "x" binder_Ts lthy ||> mk_Frees "n" (map mk_natT binder_Ts);
    val abs_ts = map2 (fn T => fn t => \<^Const>\<open>natify T for t\<close>) binder_Ts arg_ts;
    val rep_ts = map2 (fn T => fn t => \<^Const>\<open>denatify T for t\<close>) binder_Ts arg_nat_ts;

    fun mk_rels \<^Type>\<open>fun A B\<close> = mk_rel_fun (mk_rels A) (mk_rels B)
      | mk_rels T = mk_Rel_nat T;

    val assms_synth_thm =
      map2 (fn T => fn (arg1, arg2) =>
        if Lifting_Util.is_fun_type T
        then mk_Trueprop \<^Const>\<open>Rel_nat T for arg1 arg2\<close>
        else mk_Trueprop \<^Const>\<open>Rel_nat T for arg1 arg2\<close>) binder_Ts (arg_nat_ts ~~ arg_ts);

    val assms_synth_thm =
      map2 (fn T => fn (arg1, arg2) =>
        mk_rels T $ arg1 $ arg2 |> mk_Trueprop) binder_Ts (arg_nat_ts ~~ arg_ts);

    val max_idx =
      fold Variable.declare_term (t :: rep_ts @ arg_nat_ts) lthy
      |> Variable.maxidx_of;

    val (var, lthy) =
      mk_fresh_names lthy 1 "t" |>> the_single
      |>> (fn s => Var ((s, max_idx + 1), natT));

    val goal = mk_Trueprop \<^Const>\<open>Rel_nat body_T for var \<open>list_comb (t, arg_ts)\<close>\<close>;

    val case_thm = Proof_Context.get_thms lthy (t_base_name ^ "_case_def");

    (* Is this necessary? Seems to work without *)
    (* val lthy = Proof_Context.set_mode (Proof_Context.mode_schematic) lthy; *)

    val synth_thm =
      Goal.prove lthy [] assms_synth_thm goal (fn {prems=prems, context=ctxt, ...} =>
        let
          val (_, ctxt) =
            Proof_Context.note_thms "" (Binding.empty_atts, [(prems, [Transfer.transfer_add])]) ctxt
        in EqSubst.eqsubst_tac ctxt [0] case_thm 1 THEN Transfer.transfer_prover_tac ctxt 1 end);

    val binding_name = Binding.name (t_base_name ^ "_nat_synth");
    val ((_, synth_thm), lthy) =
      Local_Theory.note ((binding_name, []), [synth_thm]) lthy
      |>> apsnd the_single;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;
    val synth_thm = Morphism.thm phi synth_thm;
    val (_, lthy) = (Local_Theory.begin_nested lthy);

    val lhs_synth_def = list_comb (t_nat, map (fn T => \<^Const>\<open>Pure.type T\<close>) free_Ts @ arg_nat_ts);

    val synth_t =
      Thm.concl_of synth_thm |> dest_Trueprop |> \<^Const_fn>\<open>Rel_nat _ for arg _ => arg\<close>;
    val schem_Ts =
      fold_types (insert (op =)) synth_t []
      |> fold (fold_atyps (fn TVar a => insert (op =) (TVar a) | _ => I))
      |> curry (op |>) [];

    val schem_ts =
      fold_aterms (fn Var a => insert (op =) (Var a) | _ => I) synth_t [] |> rev


     val tyenv =
      if length schem_Ts > 0
      then
        fold (Sign.typ_match (Proof_Context.theory_of lthy)) (schem_Ts ~~ free_Ts) Vartab.empty
      else Vartab.empty;

    val a =
    fold (Pattern.match (Proof_Context.theory_of lthy))
      (schem_ts ~~ arg_nat_ts) (tyenv, Vartab.empty)

    val rhs_synth_def = Envir.subst_term a synth_t

    val goal = mk_Trueprop_eq (lhs_synth_def, rhs_synth_def);
    val assms_synth_def_thm = map mk_Trueprop_eq (arg_nat_ts ~~ abs_ts);

    val synth_mod_thm =
      (Local_Defs.unfold lthy @{thms Rel_nat_def} synth_thm RS @{thm sym})


    val rule_thm = (@{thm trans} OF [@{thm _}, synth_mod_thm])

(*     val b = (map (fst o dest_TVar) schem_Ts) ~~ (map (Thm.cterm_of lthy) arg_nat_ts)
    val d = Drule.infer_instantiate lthy b rule_thm *)

    val app_eq_thm = Proof_Context.get_thms lthy (t_nat_base_name ^ "_app_eq");

    val schem_Ts =
      fold_types (insert (op =)) (the_single app_eq_thm |> Thm.full_prop_of) []
      |> fold (fold_atyps (fn TVar a => insert (op =) (TVar a) | _ => I))
      |> curry (op |>) []

(*     val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;
    val synth_thm = Morphism.thm phi synth_thm;
    val (_, lthy) = (Local_Theory.begin_nested lthy);

    val foo =
      synth_thm
      |> `(Morphism.thm phi)
      |> apply2 (Thm.cterm_of lthy o Thm.full_prop_of) *)

    val ct =
      the_single app_eq_thm |> Thm.full_prop_of
      |> \<^Const_fn>\<open>Pure.eq _ for A _ => A\<close>
      |> Thm.cterm_of lthy
    val ct' = lhs_synth_def |> Thm.cterm_of lthy
    val a : ctyp TVars.table * cterm Vars.table = Thm.match (ct, ct')

    val var_names = map (fst o dest_Free) (arg_ts @ arg_nat_ts);

    val synth_def_thm =
      Goal.prove lthy var_names assms_synth_thm goal (fn {prems=prems, context=ctxt, ...} =>
        Classical.rule_tac ctxt [rule_thm] [] 1
        THEN ALLGOALS (Method.insert_tac ctxt prems)
        THEN auto_tac (ctxt addsimps app_eq_thm addsimps @{thms rel_fun_def Rel_nat_def})
        );
    val binding_name = Binding.name (t_base_name ^ "_nat_synth_def");
    val (_, lthy) = Local_Theory.note ((binding_name, []), [synth_def_thm]) lthy;

    val lthy = Local_Theory.end_nested lthy;
  in lthy end;

val tvars_to_tfrees_add_sort = map_atyps
  (dest_TFree_or_TVar
  ##> (fn \<^sort>\<open>type\<close> => compile_natS | s => insert (op =) compile_natC s)
  #> TFree)

val tvars_to_tfrees_add_sort_term = map_types tvars_to_tfrees_add_sort

(*TODO: not stable; may clash a Var name with an existing Free*)
val vars_to_frees = map_aterms (fn Var ((s, _), T) => Free (s, T) | x => x)

fun function_compile_nat_cmd t lthy =
  let
    val t = Syntax.read_term lthy t |> vars_to_frees |> tvars_to_tfrees_add_sort_term
    val lthy = lthy
      |> mk_case_defs t
      |> mk_related_self_thm t
      |> mk_trp_term t
      |> mk_lifting_thm t
      |> mk_nat_synth t
  in lthy end

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>function_compile_nat\<close>
    "Compile HOL function to HOL function on natural numbers"
    (Parse.term >> function_compile_nat_cmd)

end