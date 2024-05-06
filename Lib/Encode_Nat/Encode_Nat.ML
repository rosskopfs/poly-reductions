(*  Title:      Encode_Nat.ML
    Author:     Johannes Neubrand, TU Muenchen
    Author:     Andreas Vollert, TU Muenchen
    Copyright   2022, 2023, 2024
*)


signature ENCODE_NAT =
sig
end

structure Encode_Nat : ENCODE_NAT =
struct

open BNF_Util
open HOLogic

val read_const' = Proof_Context.read_const {proper = false, strict = false};

val lhs_of_term = dest_Trueprop #> dest_eq #> fst;

val rhs_of_term = dest_Trueprop #> dest_eq #> snd;

val pair_defs = @{thms pair_def fstP_def sndP_def};

val subscript = implode o map (prefix "\<^sub>") o Symbol.explode;

fun argname i = "arg" ^ subscript (string_of_int (i + 1));

fun funname i = "f" ^ subscript (string_of_int (i + 1));

val argnames = map_range argname;

fun rep_nat T = \<^Const>\<open>Rep_nat T\<close>;

fun abs_nat T = \<^Const>\<open>Abs_nat T\<close>;

fun add_lift_nat_to_sort (Type (s, Ts)) = Type (s, map add_lift_nat_to_sort Ts)
  | add_lift_nat_to_sort T =
      dest_TFree_or_TVar T
      ||> (fn \<^sort>\<open>type\<close> => \<^sort>\<open>lift_nat\<close> | s => insert (op =) \<^class>\<open>lift_nat\<close> s)
      |> TFree;

val normalize_type_of_term =
  map_aterms (fn Var ((s, _), T) => Free (s, T) | x => x) #> map_types add_lift_nat_to_sort;

fun add_fun binding_name lhs rhs ctxt =
  let
    val fixes = [(binding_name, NONE, NoSyn)];
    val specs = [((Binding.empty_atts, mk_Trueprop_eq (lhs, rhs)), [], [])];
  in Function_Fun.add_fun fixes specs Function_Fun.fun_config ctxt end;

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
  | mk_unpairing t (FST x) = \<^Const>\<open>fstP for \<open>mk_unpairing t x\<close>\<close>
  | mk_unpairing t (SND x) = \<^Const>\<open>sndP for \<open>mk_unpairing t x\<close>\<close>;

fun mk_unpairing_from_idx t idx length =
  let
    val snd_t = fold_range (fn _ => fn t => \<^Const>\<open>sndP for t\<close>) (idx + 1) t;
  in if idx = length - 1 then snd_t else \<^Const>\<open>fstP for snd_t\<close> end;

fun mk_constructor_tag ctrs ctxt t =
  find_index (can (Ctr_Sugar_Util.fo_match ctxt t)) ctrs |> mk_number \<^typ>\<open>nat\<close>;

fun mk_constructor_pairing [] = error "Emtpy argument list"
  | mk_constructor_pairing [t] = \<^Const>\<open>pair for t \<^term>\<open>0::nat\<close>\<close>
  | mk_constructor_pairing [t, t'] = \<^Const>\<open>pair for t t'\<close>
  | mk_constructor_pairing (t::ts) = \<^Const>\<open>pair for t \<open>mk_constructor_pairing ts\<close>\<close>;

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

fun mk_cr_nat_equiv ctxt ctr_t =
  let
    fun mk_rel_funs (T as Type (\<^type_name>\<open>fun\<close>, _)) =
          dest_funT T |> apply2 mk_rel_funs |-> mk_rel_fun
      | mk_rel_funs T =  \<^Const>\<open>cr_nat T\<close>;
    val (ctr_nat_name, T) = dest_Const (head_of ctr_t) |>> suffix "_nat" o Long_Name.base_name;
  in list_comb (mk_rel_funs T, [read_const' ctxt ctr_nat_name, ctr_t]) end;

fun lift_ctr ctrs ctr_t ctxt =
  let
    val n = length (binder_types (type_of ctr_t));
    val ctr_nat_args = map (fn name => Free (name, \<^typ>\<open>pair_repr\<close>)) (mk_names n "v");
    val ctr_nat_rhs =
      mk_constructor_pairing ((mk_constructor_tag ctrs ctxt ctr_t) :: ctr_nat_args);
    val ctr_nat_t =
      Free (Term.term_name ctr_t ^ "_nat", (replicate n \<^typ>\<open>pair_repr\<close>) ---> \<^typ>\<open>pair_repr\<close>);
    val ctr_nat_equ = mk_Trueprop_eq (list_comb (ctr_nat_t, ctr_nat_args), ctr_nat_rhs);
  in
    Specification.definition NONE [] [] (Binding.empty_atts, ctr_nat_equ) ctxt |>> snd o snd
  end;

fun lift_ctrs ctrs ctxt =
  let
    val (ctrs_nat_defs, (phi, ctxt)) =
    snd (Local_Theory.begin_nested ctxt)
    |> fold_map (lift_ctr ctrs) ctrs
    ||> `Local_Theory.end_nested
    ||> (fn (ctxt, old_ctxt) => (Proof_Context.export_morphism old_ctxt ctxt, ctxt));
    val cr_nat_equiv_terms = map (mk_cr_nat_equiv ctxt) ctrs;
  in ((cr_nat_equiv_terms, map (Morphism.thm phi) ctrs_nat_defs), ctxt) end;

fun add_abs_rep_fun T casex ctrs ctxt =
  let
    val (T_name, _) = dest_Type T;
    val T_base_name = Long_Name.base_name T_name;
    val abs_nat_binding = Binding.name ("Abs_nat_" ^ T_base_name);
    val rep_nat_binding = Binding.name ("Rep_nat_" ^ T_base_name);

    fun mk_abs_case ctr_t =
      let
        val ctr_args_Ts = (binder_types o type_of) ctr_t;
        val ctr_nat_name = (Term.term_name ctr_t) ^ "_nat";
        val n = length ctr_args_Ts;
        val encoded_args = map2 (curry op $) (map abs_nat ctr_args_Ts) (rev (map_range Bound n));
      in
        fold (fn (s, T) => fn t => Abs (s, T, t))
          (rev ((mk_names n "v") ~~ ctr_args_Ts))
          (list_comb (read_const' ctxt ctr_nat_name, encoded_args))
      end;

    fun mk_rep_case ctr_t =
      let
        val ctr_args_Ts = (Term.binder_types o Term.type_of) ctr_t;
        val args_decoded =
          map_index (fn (i, e) =>
            rep_nat e $ mk_unpairing_from_idx \<^term>\<open>v::pair_repr\<close> i (length ctr_args_Ts))
          ctr_args_Ts;
      in list_comb (ctr_t, args_decoded) end;

    val abs_lhs = \<^Const>\<open>Abs_nat T\<close> $ Free ("v", T);
    val abs_cases = map mk_abs_case ctrs;
    val abs_rhs = list_comb (casex, abs_cases @ [Free ("v", T)]);

    val rep_lhs = \<^Const>\<open>Rep_nat T\<close> $ \<^term>\<open>v::pair_repr\<close>;
    val rep_conditions =
      map (mk_constructor_tag ctrs ctxt #> curry mk_eq (\<^term>\<open>fstP v::pair_repr\<close>)) ctrs;
    val rep_cases = map mk_rep_case ctrs;
    val rep_rhs = Ctr_Sugar_Util.mk_IfN T rep_conditions rep_cases;
  in
    add_fun abs_nat_binding abs_lhs abs_rhs ctxt |> add_fun rep_nat_binding rep_lhs rep_rhs
  end;

fun build_nat_condition ctrs ctxt t =
  let
    fun mk_condition arg (match, path) =
      mk_eq (mk_unpairing arg path, mk_constructor_tag ctrs ctxt match);
    fun mk_conditions (arg, paths) = map (mk_condition arg) paths;
    val args_t = Term.args_of (lhs_of_term t);
    val new_args_t = map (fn s => Free (s, \<^typ>\<open>pair_repr\<close>)) (argnames (length args_t));
  in
    map (mk_condition_paths o mk_patmatch_term) args_t
    |> (curry op ~~) new_args_t
    |> maps mk_conditions
    |> foldl1 mk_conj
  end;

fun if_exp_of_case_exp T ctrs casex ctxt =
  let
    val args =
      map (binder_types o fastype_of) ctrs
      |> map (map_index (fn (i, T) => Free (argname i,  T)));
    val end_T = body_type (fastype_of casex);
    val T_base_name = Long_Name.base_name (fst (dest_Type T));
    val case_nat_binding_name = Binding.name ("case_" ^ T_base_name ^ "_nat");

    val fun_ts =
      binder_types (fastype_of casex)
      |> fst o split_last
      |> map_index (fn (i, T) => Free (funname i, T));

    val fun_ts2 =
      binder_types (fastype_of casex)
      |> fst o split_last
      |> map (length o fst o strip_type)
      |> map (fn i => (replicate i \<^typ>\<open>pair_repr\<close>) ---> \<^typ>\<open>pair_repr\<close>)
      |> map_index (fn (i, T) => Free (funname i, T));

    fun arguments_and_paths t =
      Term.args_of (lhs_of_term t)
      |> map (mk_variable_paths o mk_patmatch_term)
      |> flat o map_index (fn (i, x) => map (pair (argname i)) x);

    fun nat_encode_term with_rep t =
      let
        fun maybe_abs t' = with_rep ? ((curry op $) (rep_nat (fastype_of t')));
        fun mk_arg name path = mk_unpairing (Free (name, \<^typ>\<open>pair_repr\<close>)) path;
        val wrappers =
          map (fn (name, (t', path)) => fn term =>
            term $ maybe_abs t' (mk_arg name path))
          (arguments_and_paths t);
      in fold (fn f => fn x => f x) wrappers (rhs_of_term t) end;

    val case_exp =
      (list_comb (casex, fun_ts)) $ (\<^Const>\<open>Rep_nat T\<close> $ Free (argname 0, \<^typ>\<open>pair_repr\<close>));

    val if_exp =
      map list_comb (ctrs ~~ args) ~~ fun_ts
      |> map (fn (t, rhs) => mk_Trueprop_eq (Term.dummy_pattern (fastype_of t --> end_T) $ t, rhs))
      |> (fn ts => (map (build_nat_condition ctrs ctxt) ts, map (nat_encode_term true) ts))
      |-> mk_IfN end_T;

    val if_exp_2 =
      map list_comb (ctrs ~~ args) ~~ fun_ts2
      |> map (fn (t, rhs) =>
        mk_Trueprop_eq (Term.dummy_pattern (fastype_of t --> \<^typ>\<open>pair_repr\<close>) $ t, rhs))
      |> (fn ts => (map (build_nat_condition ctrs ctxt) ts, map (nat_encode_term false) ts))
      |-> mk_IfN \<^typ>\<open>pair_repr\<close>
      |> fold lambda ((Free (argname 0, \<^typ>\<open>pair_repr\<close>))::(rev fun_ts2));

    val ((_, (_, case_nat_def_thm)), ctxt) =
      Local_Theory.define
        ((case_nat_binding_name, NoSyn),
          ((Binding.suffix_name "_def" case_nat_binding_name, []), if_exp_2))
        ctxt;

    val goal = mk_Trueprop_eq (case_exp, if_exp);

    val decoder_simps = Proof_Context.get_thms ctxt ("Rep_nat_" ^ T_base_name ^ ".simps");

    val schemvars = argname 0 :: map (fst o dest_Free) fun_ts;

    val thm =
      Goal.prove ctxt schemvars [] goal
        (fn {context=ctxt, ...} => asm_full_simp_tac (ctxt addsimps decoder_simps) 1);

    val name = "case_" ^ T_base_name ^ "_eq_if";
  in
    Local_Theory.note ((Binding.name name, []), [thm]) ctxt |>> snd |>> cons case_nat_def_thm
  end;

fun cr_nat_case_nat_equiv thms T ctxt =
  let
    fun mk_cr_nat_case_nat_equiv free_T (T as Type (\<^type_name>\<open>fun\<close>, _)) =
          dest_funT T |> apply2 (mk_cr_nat_case_nat_equiv free_T) |-> mk_rel_fun
      | mk_cr_nat_case_nat_equiv free_T T =
          if T = free_T then Free ("R", [\<^typ>\<open>nat\<close>, T] ---> \<^typ>\<open>bool\<close>) else \<^Const>\<open>cr_nat T\<close>;

    val T_base_name = Long_Name.base_name (fst (dest_Type T));
    val case_t = read_const' ctxt ("case_" ^ T_base_name) |> normalize_type_of_term;
    val case_t_T = fastype_of case_t;
    val case_nat_t = read_const' ctxt ("case_" ^ T_base_name ^ "_nat");
    val body_T = body_type case_t_T;

    val goal =
      list_comb (mk_cr_nat_case_nat_equiv body_T case_t_T, [case_nat_t, case_t]) |> mk_Trueprop;

    val simps = Proof_Context.get_thm ctxt (T_base_name ^ ".split") :: thms;
    val thm =
      Goal.prove ctxt ["R"] [] goal
        (fn {context=ctxt, ...} => asm_full_simp_tac (ctxt addsimps simps) 1);
    val name = "cr_nat_" ^ T_base_name ^ "_case_" ^ T_base_name;
  in Local_Theory.note ((Binding.name name, @{attributes [transfer_rule]}), [thm]) ctxt end;

fun datatype_lift_nat T ctrs casex (thy : theory) =
  let
    val (T_name, T_typ_args) = dest_Type T;
    val T_base_name = Long_Name.base_name T_name;

    (* Add nat version of constructors and start instantiation of lift_nat class*)
    val ((cr_nat_equiv_terms, ctrs_nat_defs), lthy) =
      Class.instantiation ([T_name], map dest_TFree T_typ_args, \<^sort>\<open>lift_nat\<close>) thy
      |> snd o Local_Theory.begin_nested
      |> lift_ctrs ctrs
      ||> add_abs_rep_fun T casex ctrs;
    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;
    val ctrs_nat_defs = map (Morphism.thm phi) ctrs_nat_defs;

    (* Remove abs/rep nat simps from simp set as they would make problems later *)
    val abs_rep_simps =
      [Proof_Context.get_thm lthy ("Rep_nat_" ^ T_base_name ^ ".simps"),
        Proof_Context.get_thm lthy ("Abs_nat_" ^ T_base_name ^ ".simps")];
    val (_, new_lthy) =
      Local_Theory.note ((Binding.empty, @{attributes [simp del]}), abs_rep_simps) lthy;

    val simps =
      @{thms rel_fun_def cr_nat_def} @ abs_rep_simps @ ctrs_nat_defs @ pair_defs;

    val lthy =
      Class.prove_instantiation_instance (fn ctxt =>
        Class.intro_classes_tac ctxt []
        THEN HEADGOAL (Subgoal.FOCUS_PARAMS_FIXED (fn {context = ctxt, ...} =>
          let
            val var = Free ("x", T);
            val inst =
              lambda var (mk_eq (\<^Const>\<open>Rep_nat T for \<^Const>\<open>Abs_nat T for var\<close>\<close>, var))
              |> Thm.cterm_of ctxt;
            val thm =
              Proof_Context.get_thm ctxt (T_base_name ^ ".induct")
              |> infer_instantiate' ctxt [SOME inst];
          in
            resolve_tac ctxt [thm] 1
            THEN REPEAT
              (asm_full_simp_tac (ctxt addsimps ctrs_nat_defs @ abs_rep_simps @ pair_defs) 1)
          end
          ) ctxt)
        ) new_lthy;

    val cr_nat_equiv_thms =
      map (fn t =>
        Goal.prove lthy [] [] (mk_Trueprop t)
          (fn {context=ctxt, ...} =>
            asm_full_simp_tac (ctxt addsimps (@{thm prod_encode_0}::simps)) 1)
        ) cr_nat_equiv_terms;

    val name = "cr_nat_" ^ T_base_name ^ "_equiv";
    val (_, lthy) =
      Local_Theory.note
        ((Binding.name name, @{attributes [transfer_rule]}), cr_nat_equiv_thms) lthy;

    (* transform case to if expression *)
    val (case_eq_if_thm, (lthy, old_lthy)) =
      snd (Local_Theory.begin_nested lthy)
      |> if_exp_of_case_exp T ctrs casex
      ||> `Local_Theory.end_nested
    val phi = Proof_Context.export_morphism old_lthy lthy;
    val (_, lthy) = cr_nat_case_nat_equiv (map (Morphism.thm phi) (case_eq_if_thm @ simps)) T lthy;
  in lthy end;

fun datatype_lift_nat_cmd T thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val sugar =
      fst (dest_Type (Syntax.parse_typ ctxt T))
      |> Ctr_Sugar.ctr_sugar_of ctxt
      |> the;
    val T = add_lift_nat_to_sort (#T sugar);
    val casex =
      subst_atomic_types [(body_type (type_of (#casex sugar)), \<^typ>\<open>pair_repr\<close>)] (#casex sugar)
      |> normalize_type_of_term;
    val ctrs = map normalize_type_of_term (#ctrs sugar);
  in datatype_lift_nat T ctrs casex thy end;

val _ =
  Outer_Syntax.command
    \<^command_keyword>\<open>datatype_lift_nat\<close>
    "Lift datatype to an encoding in natural numbers"
    (Parse.typ >> datatype_lift_nat_cmd >> (Toplevel.begin_main_target false));

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

    val rel_const_name = fst (dest_Const \<^term>\<open>lift_nat_type_def.R\<close>)
    val rels =
      strip_type (fastype_of t)
      |> (op @) o apsnd single
      |> map (fn T => Const (rel_const_name, T --> T --> HOLogic.boolT))

    val goal = (Library.foldr1 (uncurry mk_Fun_Rel) rels) $ t $ t  |> mk_Trueprop

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

    val thms =
      Goal.prove_common ctxt NONE [] [] goals
        (fn {context=ctxt, ...} =>
          HEADGOAL Goal.conjunction_tac
          THEN HEADGOAL (Transport.transport_prover ctxt));

    val lthy = Transport.after_qed_blackbox (binding, NoSyn) [thms] lthy

  in Local_Theory.end_nested lthy end;

fun mk_trp_term t ctxt =
  let
    val binding = Binding.name (Term.term_name t ^ "_nat");
    val yT = map (K \<^typ>\<open>pair_repr\<close>) (binder_types (fastype_of t)) ---> \<^typ>\<open>pair_repr\<close>;
    val ct = normalize_type_of_term t |> Thm.cterm_of ctxt;
  in wrapper_transport_api binding yT ct ctxt end;


fun mk_lifting_thm t lthy =
  let
    val (_, lthy) = (Local_Theory.begin_nested lthy);

    val T = fastype_of t;
    val (binderTs, bodyT) = strip_type T;
    val Ts = fold_atyps (insert (op =)) T [] |> rev;

    val t_nat_name = dest_Const t |> fst |> suffix "_nat";
    val nat_base_name = Long_Name.base_name t_nat_name;

    val t_nat =
      Const (t_nat_name,
             (map Term.itselfT Ts) @ (map (K \<^typ>\<open>pair_repr\<close>) binderTs) ---> \<^typ>\<open>pair_repr\<close>);
    val t_nat_app = list_comb (t_nat, map (fn T => \<^Const>\<open>Pure.type T\<close>) Ts);

    val cr_nat_rel_fun =
      fold_rev (mk_rel_fun o (fn T => \<^Const>\<open>cr_nat T\<close>)) binderTs \<^Const>\<open>cr_nat bodyT\<close>;

    val related_thm = Proof_Context.get_thm lthy (t_nat_name ^ "_related'");

    val goal = mk_Trueprop (cr_nat_rel_fun $ t_nat_app $ t);
    val thm =
      Goal.prove lthy [] [] goal (fn {context=ctxt, ...} =>
        Method.insert_tac ctxt [related_thm] 1
        THEN fast_tac ctxt 1
        );

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

fun function_lift_nat_cmd t lthy =
  let
    val t = Syntax.read_term lthy t |> normalize_type_of_term;

    val lthy =
      lthy
      |> mk_case_defs t
      |> mk_related_self_thm t
      |> mk_trp_term t
      |> mk_lifting_thm t
  in
    lthy
  end;

fun test_cmd t lthy =
  let
    val t = Syntax.read_term lthy t |> normalize_type_of_term;
  in lthy end;

val _ =
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>function_lift_nat\<close>
    "Test"
    (Parse.term >> function_lift_nat_cmd);

val _ =
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>test\<close>
    "Test"
    (Parse.term >> test_cmd);


end