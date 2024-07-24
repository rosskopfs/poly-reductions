(*  Title:      hol_to_hol_nat.ML
    Author:     Jay Neubrand, TU Muenchen
    Author:     Andreas Vollert, TU Muenchen
    Author:     Kevin Kappelmann, TU Muenchen
*)
signature HOL_TO_HOL_NAT =
sig
end

structure HOL_To_HOL_Nat : HOL_TO_HOL_NAT =
struct

open BNF_Util
open HOLogic
structure TranspUtil = Transport_Util
structure TacUtil = Tactic_Util

val print_term = @{print} oo Thm.cterm_of

fun cat_options opts = fold (fn NONE => I | SOME x => cons x) opts []

fun del_simps simps = Local_Theory.note ((Binding.empty, @{attributes [simp del]}), simps) #> snd

fun get_fun_simps ctxt = Function_Common.retrieve_function_data ctxt #> map (snd #> #simps)
(* fun get_datatype_induct ctxt = Function_Common.retrieve_function_data ctxt #> map (snd #> #inducts) *)

val read_const = Proof_Context.read_const {proper = false, strict = false};
fun const_from_binding ctxt = Binding.name_of #> read_const ctxt

val app = curry (op $)

val term_binder_types = fastype_of #> binder_types

val lhs_of_term = dest_Trueprop #> dest_eq #> fst;

val rhs_of_term = dest_Trueprop #> dest_eq #> snd;

val pair_defs = @{thms pair_def fstP_def sndP_def};

val subscript = implode o map (prefix "\<^sub>") o Symbol.explode;

fun argname i = "arg" ^ subscript (string_of_int (i + 1));

fun funname i = "f" ^ subscript (string_of_int (i + 1));

val argnames = map_range argname;

val binding_from_long_name = Long_Name.base_name #> Binding.name
val type_binding = dest_Type #> fst #> binding_from_long_name
val const_binding = binding_from_long_name
val term_binding = Term.term_name #> Binding.name

fun type_suffix_binding base_binding = type_binding #> TranspUtil.add_suffix base_binding

fun mk_denatify T = \<^Const>\<open>denatify T\<close>
val mk_denatify_binding  = type_suffix_binding (const_binding @{const_name denatify})

fun mk_natify T = \<^Const>\<open>natify T\<close>
val mk_natify_binding = type_suffix_binding (const_binding @{const_name natify})

val fstP = \<^Const>\<open>fstP\<close>
val sndP = \<^Const>\<open>sndP\<close>
val pair_const = \<^Const>\<open>pair\<close>

val natT = \<^typ>\<open>nat\<close>
val pair_reprT = natT
val compile_natS = \<^sort>\<open>compile_nat\<close>
val compile_natC = \<^class>\<open>compile_nat\<close>

val nat_suffix = @{binding nat}

fun mk_ctr_binding ctr = TranspUtil.add_suffix (term_binding ctr) nat_suffix

fun mk_Rel_nat T = \<^Const>\<open>Rel_nat T\<close>
val Rel_nat_binding  = const_binding @{const_name Rel_nat}
val mk_Rel_nat_type_binding  = type_suffix_binding Rel_nat_binding

fun mk_Rel_fun base T = case T of
    \<^Type>\<open>fun A B\<close> => mk_rel_fun (mk_Rel_fun base A) (mk_Rel_fun base B)
  | T => base T

val fun_RelD = @{thms rel_funD}

val mk_Rel_nat_Rel = mk_Rel_fun mk_Rel_nat

(*TODO: not stable; may clash a TVar name with an existing TFree*)
val mk_tfrees_add_sort = map_atyps
  (dest_TFree_or_TVar
  ##> (fn \<^sort>\<open>type\<close> => compile_natS | s => insert (op =) compile_natC s)
  #> TFree)

(*TODO: not stable; may clash a Var name with an existing Free*)
val mk_frees_add_sort =
  map_aterms (fn Var ((s, _), T) => Free (s, T) | x => x)
  #> map_types mk_tfrees_add_sort

fun register_fun binding_name lhs rhs lthy =
  let
    val fixes = [(binding_name, NONE, NoSyn)]
    val specs = [((Binding.empty_atts, mk_Trueprop_eq (lhs, rhs)), [], [])]
  in Function_Fun.add_fun fixes specs Function_Fun.fun_config lthy end

datatype pairing_path =
  DONE |
  FST of pairing_path |
  SND of pairing_path;

datatype patmatch_term =
  CONSTRUCTOR of term * (patmatch_term list) |
  VARIABLE of term;

datatype pairing_tree =
  LEAF |
  VAR of term |
  NODE of (pairing_tree * pairing_tree);

fun mk_unpairing t DONE = t
  | mk_unpairing t (FST x) = fstP $ mk_unpairing t x
  | mk_unpairing t (SND x) = sndP $ mk_unpairing t x

fun mk_unpairing_from_idx t i nargs =
  funpow (i + 1) (app sndP) t |> (i <> nargs - 1 ? app fstP)

val mk_nat = mk_number natT
val mk_constructor_tag = mk_nat

fun find_constructor_tag ctrs ctxt t = find_index (can (Ctr_Sugar_Util.fo_match ctxt t)) ctrs
val find_mk_constructor_tag = mk_constructor_tag ooo find_constructor_tag

fun mk_ctr_rhs ctr_tag [] = mk_ctr_rhs ctr_tag [mk_nat 0] (*arbitrary number for empty argument list*)
  | mk_ctr_rhs ctr_tag args =
    let fun mk_arg [] = error "oops, this should not happen - unreachable code."
          | mk_arg [t] = t
          | mk_arg (t::ts) = pair_const $ t $ mk_arg ts
    in pair_const $ ctr_tag $ mk_arg args end

fun mk_patmatch_term t =
  if is_Free t orelse is_Var t then VARIABLE t
  else strip_comb t ||> (map mk_patmatch_term) |> CONSTRUCTOR;

fun mk_pairing_tree [] = LEAF
  | mk_pairing_tree [(VARIABLE n)] = VAR n
  | mk_pairing_tree ((VARIABLE n) :: xs) = NODE (VAR n, mk_pairing_tree xs)
  | mk_pairing_tree ((CONSTRUCTOR (_, [])) :: xs) = NODE (NODE (LEAF, LEAF), mk_pairing_tree xs)
  | mk_pairing_tree ((CONSTRUCTOR (_, args)) :: xs) =
      NODE (NODE (LEAF, mk_pairing_tree args), mk_pairing_tree xs);

fun mk_path t =
  let
    fun mk_path p (VAR n) = [(n, p)]
      | mk_path _ LEAF = []
      | mk_path p (NODE (l, r)) = (mk_path (FST p) l) @ (mk_path (SND p) r);
  in mk_path DONE t end;

fun mk_variable_paths (VARIABLE n) = [(n, DONE)]
  | mk_variable_paths (CONSTRUCTOR (_, args)) = mk_path (NODE (LEAF, mk_pairing_tree args));

fun mk_condition_paths (CONSTRUCTOR (c, args)) = (c, FST DONE) :: (maps (mk_condition_paths) args)
  | mk_condition_paths (VARIABLE _) = [];

fun register_ctr ctrs ctr ctxt =
  let
    val (binders, _) = Binders.fix_binders (map (K ("x", natT)) (term_binder_types ctr)) ctxt
    val ctr_nat_args = map snd binders
    val ctr_nat_rhs = mk_ctr_rhs (find_mk_constructor_tag ctrs ctxt ctr) ctr_nat_args
    val ctr_nat_head =
      Free (mk_ctr_binding ctr |> Binding.name_of, map (snd o fst) binders ---> natT)
    val ctr_nat_equ = mk_Trueprop_eq (list_comb (ctr_nat_head, ctr_nat_args), ctr_nat_rhs)
  in Specification.definition NONE [] [] (Binding.empty_atts, ctr_nat_equ) ctxt |>> snd o snd end

fun register_ctrs ctrs lthy =
  Local_Theory.begin_nested lthy
  |> snd
  |> fold_map (register_ctr ctrs) ctrs
  ||> `Local_Theory.end_nested
  ||> (fn (lthy, old_lthy) => (Proof_Context.export_morphism old_lthy lthy, lthy))
  |> (fn (ctrs_nat_defs, (phi, lthy)) => (map (Morphism.thm phi) ctrs_nat_defs, lthy))

fun mk_ctr_Rel ctxt ctr =
  let val ctr_nat = mk_ctr_binding ctr |> const_from_binding ctxt
  in mk_Rel_nat_Rel (fastype_of ctr) $ ctr_nat $ ctr end

fun register_natify_fun T casex ctrs lthy =
  let
    val binding = mk_natify_binding T
    fun mk_case ctr =
      let
        val ctr_args_Ts = term_binder_types ctr
        val ctr_nat = mk_ctr_binding ctr |> const_from_binding lthy
        val (binders, _) = Binders.fix_binders (map (pair "x") ctr_args_Ts) lthy
        val natified_args =
          map2 (fn T => app (mk_natify T) o Bound) ctr_args_Ts (length ctr_args_Ts - 1 downto 0)
      in
        list_comb (ctr_nat, natified_args)
        |> fold_rev (fn ((n, T), _) => fn t => Abs (n, T, t)) binders
      end
    val (free, _) = Binders.fix_binder ("x", T) lthy |>> snd
    val lhs = mk_natify T $ free
    val cases = map mk_case ctrs
    val rhs = list_comb (casex, cases @ [free])
  in register_fun binding lhs rhs lthy end

fun register_denatify_fun T ctrs lthy =
  let
    val binding = mk_denatify_binding T
    val (free, _) = Binders.fix_binder ("x", natT) lthy |>> snd
    fun mk_case ctr =
      let
        val ctr_args_Ts = term_binder_types ctr
        val nargs = length ctr_args_Ts
        val args_decoded =
          map_index (fn (i, T) => mk_denatify T $ mk_unpairing_from_idx free i nargs) ctr_args_Ts
      in list_comb (ctr, args_decoded) end;
    val lhs = mk_denatify T $ free
    val conditions = map_index (fst #> mk_constructor_tag #> curry mk_eq (fstP $ free)) ctrs
    val cases = map mk_case ctrs
    val rhs = Ctr_Sugar_Util.mk_IfN T conditions cases
  in register_fun binding lhs rhs lthy end

fun build_nat_condition ctrs ctxt t =
  let
    fun mk_condition arg (match, path) =
      mk_eq (mk_unpairing arg path, find_mk_constructor_tag ctrs ctxt match);
    fun mk_conditions (arg, paths) = map (mk_condition arg) paths;
    val args_t = Term.args_of (lhs_of_term t);
    val new_args_t = map (fn s => Free (s, pair_reprT)) (argnames (length args_t));
  in
    map (mk_condition_paths o mk_patmatch_term) args_t
    |> (curry op ~~) new_args_t
    |> maps mk_conditions
    |> foldl1 mk_conj
  end;

fun if_exp_of_case_exp T ctrs casex ctxt =
  let
    val args =
      map term_binder_types ctrs
      |> map (map_index (fn (i, T) => Free (argname i,  T)));
    val end_T = body_type (fastype_of casex);
    val T_base_name = Long_Name.base_name (fst (dest_Type T));
    val case_nat_binding_name = Binding.name ("case_" ^ T_base_name ^ "_nat");

    val fun_ts =
      term_binder_types casex
      |> fst o split_last
      |> map_index (fn (i, T) => Free (funname i, T));

    val fun_ts2 =
      term_binder_types casex
      |> fst o split_last
      |> map (length o fst o strip_type)
      |> map (fn i => (replicate i pair_reprT) ---> pair_reprT)
      |> map_index (fn (i, T) => Free (funname i, T));

    fun arguments_and_paths t =
      Term.args_of (lhs_of_term t)
      |> map (mk_variable_paths o mk_patmatch_term)
      |> flat o map_index (fn (i, x) => map (pair (argname i)) x);

    fun nat_encode_term with_rep t =
      let
        fun maybe_abs t' = with_rep ? ((curry op $) (mk_denatify (fastype_of t')));
        fun mk_arg name path = mk_unpairing (Free (name, pair_reprT)) path;
        val wrappers =
          map (fn (name, (t', path)) => fn term =>
            term $ maybe_abs t' (mk_arg name path))
          (arguments_and_paths t);
      in fold (fn f => fn x => f x) wrappers (rhs_of_term t) end;

    val case_exp =
      (list_comb (casex, fun_ts)) $ (\<^Const>\<open>denatify T\<close> $ Free (argname 0, pair_reprT));

    val if_exp =
      map list_comb (ctrs ~~ args) ~~ fun_ts
      |> map (fn (t, rhs) => mk_Trueprop_eq (Term.dummy_pattern (fastype_of t --> end_T) $ t, rhs))
      |> (fn ts => (map (build_nat_condition ctrs ctxt) ts, map (nat_encode_term true) ts))
      |-> mk_IfN end_T;

    val if_exp_2 =
      map list_comb (ctrs ~~ args) ~~ fun_ts2
      |> map (fn (t, rhs) =>
        mk_Trueprop_eq (Term.dummy_pattern (fastype_of t --> pair_reprT) $ t, rhs))
      |> (fn ts => (map (build_nat_condition ctrs ctxt) ts, map (nat_encode_term false) ts))
      |-> mk_IfN pair_reprT
      |> fold lambda ((Free (argname 0, pair_reprT))::(rev fun_ts2));

    val ((_, (_, case_nat_def_thm)), ctxt) =
      Local_Theory.define
        ((case_nat_binding_name, NoSyn),
          ((Binding.suffix_name "_def" case_nat_binding_name, []), if_exp_2))
        ctxt;

    val goal = mk_Trueprop_eq (case_exp, if_exp);

    val decoder_simps = Proof_Context.get_thms ctxt ("denatify_" ^ T_base_name ^ ".simps");

    val schemvars = argname 0 :: map (fst o dest_Free) fun_ts;

    val thm =
      Goal.prove ctxt schemvars [] goal
        (fn {context=ctxt, ...} => asm_full_simp_tac (ctxt addsimps decoder_simps) 1);

    val name = "case_" ^ T_base_name ^ "_eq_if";
    val _ = @{print} thm
  in
    Local_Theory.note ((Binding.name name, []), [thm]) ctxt |>> snd |>> cons case_nat_def_thm
  end;

fun Rel_nat_case_nat_equiv thms T ctxt =
  let
    fun mk_Rel_nat_case_nat_equiv free_T (T as Type (\<^type_name>\<open>fun\<close>, _)) =
          dest_funT T |> apply2 (mk_Rel_nat_case_nat_equiv free_T) |-> mk_rel_fun
      | mk_Rel_nat_case_nat_equiv free_T T =
          if T = free_T then Free ("R", [\<^typ>\<open>nat\<close>, T] ---> \<^typ>\<open>bool\<close>) else mk_Rel_nat T;

    val T_base_name = Long_Name.base_name (fst (dest_Type T));
    val case_t = read_const ctxt ("case_" ^ T_base_name) |> mk_frees_add_sort;
    val case_t_T = fastype_of case_t;
    val case_nat_t = read_const ctxt ("case_" ^ T_base_name ^ "_nat");
    val body_T = body_type case_t_T;

    val goal =
      list_comb (mk_Rel_nat_case_nat_equiv body_T case_t_T, [case_nat_t, case_t]) |> mk_Trueprop;

    val simps = Proof_Context.get_thm ctxt (T_base_name ^ ".split") :: thms;
    val thm =
      Goal.prove ctxt ["R"] [] goal
        (fn {context=ctxt, ...} => asm_full_simp_tac (ctxt addsimps simps) 1);
    val name = "Rel_nat_" ^ T_base_name ^ "_case_" ^ T_base_name;
  in Local_Theory.note ((Binding.name name, @{attributes [transfer_rule]}), [thm]) ctxt end;


fun prove_instantiation solve_tac =
  let fun tac ctxt concl =
    let val var = dest_comb concl |> snd |> dest_comb |> snd
    in
      Induction.induction_tac ctxt false [[SOME (NONE, (var, false))]] [] [] NONE []
      THEN_ALL_NEW (solve_tac ctxt)
    end
  in
    Class.prove_instantiation_instance (fn ctxt =>
      Class.intro_classes_tac ctxt []
      THEN HEADGOAL (TacUtil.FOCUS_PARAMS_CTXT' (TacUtil.SUBGOAL_STRIPPED (snd o snd) o tac) ctxt))
  end

fun mk_ctrl_Rel_thm ctr simps ctxt =
  let
    fun solve_Rel_nat_equiv ctxt = auto_tac (ctxt addsimps simps addDs fun_RelD)
    fun prove_goal t = Goal.prove ctxt [] [] (mk_Trueprop t) (#context #> solve_Rel_nat_equiv)
  in mk_ctr_Rel ctxt ctr |> prove_goal end

fun register_ctrl_Rel_thm ctr simps lthy =
  let
    val ctrl_Rel_thm = mk_ctrl_Rel_thm ctr simps lthy
    val binding = TranspUtil.add_suffix Rel_nat_binding (mk_ctr_binding ctr)
  in Local_Theory.note ((binding, @{attributes [transfer_rule]}), [ctrl_Rel_thm]) lthy end

fun register_ctrl_Rel_thms T ctrs simps =
  fold_map (fn ctr => register_ctrl_Rel_thm ctr simps #>> snd) ctrs
  #> (fn (thms, lthy) => Local_Theory.note ((mk_Rel_nat_type_binding T, []), flat thms) lthy)

fun datatype_compile_nat T ctrs casex thy =
  let
    val (T_name, T_typ_args) = dest_Type T
    val T_base_name = Long_Name.base_name (fst (dest_Type T));

    (* Add nat version of constructors and start instantiation of compile_nat class*)
    val (ctrs_nat_defs, lthy) =
      Class.instantiation ([T_name], map dest_TFree T_typ_args, compile_natS) thy
      |> Local_Theory.begin_nested
      |> snd
      |> register_ctrs ctrs
      ||> register_natify_fun T casex ctrs
      ||> register_denatify_fun T ctrs

    val (natify_simps, denatify_simps) = (mk_natify_binding, mk_denatify_binding)
      |> apply2 (fn f => f T |> const_from_binding lthy |> get_fun_simps lthy |> cat_options |> flat)
    (* Remove simps from simp set as they would make problems later *)
    val natify_denatify_simps = natify_simps @ denatify_simps
    val lthy = del_simps natify_denatify_simps lthy

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy
    val phi = Proof_Context.export_morphism old_lthy lthy
    val (ctrs_nat_defs, natify_denatify_simps) = (ctrs_nat_defs, natify_denatify_simps)
      |> apply2 (map (Morphism.thm phi))

    val simps =
      @{thms rel_fun_def Rel_nat_iff_eq_natify} @ natify_denatify_simps @ ctrs_nat_defs @ pair_defs

    fun solve_instantiation_tac ctxt =
      asm_full_simp_tac (ctxt addsimps ctrs_nat_defs @ natify_denatify_simps @ pair_defs)
    val lthy = prove_instantiation solve_instantiation_tac lthy
    val (_, lthy) = register_ctrl_Rel_thms T ctrs simps lthy

    (* transform case to if expression *)
    val (case_eq_if_thm, (lthy, old_lthy)) =
      Local_Theory.begin_nested lthy
      |> snd
      |> if_exp_of_case_exp T ctrs casex
      ||> `Local_Theory.end_nested
    val phi = Proof_Context.export_morphism old_lthy lthy
    val (_, lthy) = Rel_nat_case_nat_equiv (map (Morphism.thm phi) (case_eq_if_thm @ simps)) T lthy;
  in lthy end;

fun datatype_compile_nat_cmd T thy =
  let
    val ctxt = Proof_Context.init_global thy
    val Tname = T |> Syntax.parse_typ ctxt |> dest_Type |> fst
  in case Ctr_Sugar.ctr_sugar_of ctxt Tname of
      NONE => error ("Unknown datatype " ^ Tname)
    | SOME sugar =>
      let
        val T = #T sugar |> mk_tfrees_add_sort
        val ctrs = #ctrs sugar |> map mk_frees_add_sort
        val casex = #casex sugar
          |> (fn casex => subst_atomic_types [(body_type (fastype_of casex), natT)] casex)
          |> mk_frees_add_sort
      in datatype_compile_nat T ctrs casex thy end
  end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>datatype_compile_nat\<close>
    "Create datatype encoding of datatype"
    (Parse.typ >> datatype_compile_nat_cmd >> Toplevel.begin_main_target false)

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
        val t = Const (rel_const_name, Transport_Util.mk_hom_rel_type T)
      in fold_rev mk_Fun_Rel (map mk_rel Ts) t end
    val goal = mk_rel (fastype_of t) $ t $ t  |> mk_Trueprop

    val thm = Goal.prove lthy [] [] goal (fn {context=ctxt, ...} => asm_full_simp_tac ctxt 1);

    val name = Term.term_name t ^ "_related_self";
    val lthy = Local_Theory.note ((Binding.name name, @{attributes [trp_in_dom]}), [thm]) lthy |> snd

  in
    Local_Theory.end_nested lthy
  end;

fun wrapper_transport_api binding yT cx lthy =
  let
    val (_, lthy) = (Local_Theory.begin_nested lthy);
    val ctxt = Transport_Util.set_proof_mode_schematic lthy;

    val ([L, R, y], maxidx) =
      let
        val opts_constraints =
          [Transport_Util.mk_hom_rel_type (Thm.typ_of_cterm cx), Transport_Util.mk_hom_rel_type yT, yT]
          |> map Type.constraint;
        val params_maxidx = ~1;
        fun create_var n maxidx = Term_Util.fresh_var n dummyT params_maxidx ||> Integer.max maxidx;
        val (ts, maxidx) =
          fold_map create_var ["L", "R", "y"] params_maxidx
          |>> map2 I opts_constraints;
      in (ts, maxidx) end;

    val goals =
      Transport.setup_goals_blackbox ctxt (L, R, cx) maxidx
      |> map fst;

    val thms = Goal.prove_common ctxt NONE [] [] goals (fn {context=ctxt, ...} =>
      HEADGOAL Goal.conjunction_tac
      THEN HEADGOAL (Transport.transport_prover ctxt))

    val lthy = Transport.after_qed_blackbox (binding, NoSyn) [thms] lthy

  in Local_Theory.end_nested lthy end;

fun mk_natT T = let val (Ts, T) = strip_type T
  in (map mk_natT Ts) ---> pair_reprT end

fun mk_trp_term t ctxt =
  let
    val binding = Binding.name (Term.term_name t ^ "_nat");
    val yT = mk_natT (fastype_of t)
    val ct = Thm.cterm_of ctxt t;
  in wrapper_transport_api binding yT ct ctxt end;

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
      |>> (fn s => Var ((s, max_idx + 1), pair_reprT));

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
      |> \<^Const_fn>\<open>Pure.eq pair_reprT for A _ => A\<close>
      |> Thm.cterm_of lthy
    val ct' = lhs_synth_def |> Thm.cterm_of lthy
    val a : ctyp TVars.table * cterm Vars.table = Thm.match (ct, ct')

    val var_names = map (fst o dest_Free) (arg_ts @ arg_nat_ts);

    val synth_def_thm =
      Goal.prove lthy var_names assms_synth_thm goal (fn {prems=prems, context=ctxt, ...} =>
        (* print_tac ctxt "Start"
        THEN Classical.rule_tac ctxt [rule_thm] [] 1
        THEN print_tac ctxt "1"
        THEN Method.insert_tac ctxt (app_eq_thm @ prems) 1
        THEN print_tac ctxt "2"
        THEN REPEAT (fast_force_tac ctxt 1 THEN print_tac ctxt "applied fastforce")
        THEN print_tac ctxt "3"
        THEN ALLGOALS (Method.insert_tac ctxt (app_eq_thm @ prems))
        THEN print_tac ctxt "4"
        THEN auto_tac (ctxt addsimps @{thms Rel_nat_def} addsimps app_eq_thm)
        THEN print_tac ctxt "5" *)
        print_tac ctxt "Start"
        THEN Classical.rule_tac ctxt [rule_thm] [] 1
        THEN print_tac ctxt "1"
        THEN ALLGOALS (Method.insert_tac ctxt prems)
        THEN print_tac ctxt "2"
        THEN auto_tac (ctxt addsimps app_eq_thm addsimps @{thms rel_fun_def Rel_nat_def})
        THEN print_tac ctxt "3"
        );
    val binding_name = Binding.name (t_base_name ^ "_nat_synth_def");
    val (_, lthy) = Local_Theory.note ((binding_name, []), [synth_def_thm]) lthy;

    val lthy = Local_Theory.end_nested lthy;
  in lthy end;

fun function_compile_nat_cmd t lthy =
  let
    val t = Syntax.read_term lthy t |> mk_frees_add_sort
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