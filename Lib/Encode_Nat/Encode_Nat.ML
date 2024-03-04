(*  Title:      Encode_Nat.ML
    Author:     Johannes Neubrand, TU Muenchen
    Author:     Andreas Vollert, TU Muenchen
    Copyright   2022, 2023, 2024
*)

infix 7 ***

signature ENCODE_NAT =
sig
end

structure Encode_Nat : ENCODE_NAT =
struct

open BNF_Util

val read_const' = Proof_Context.read_const {proper = false, strict = false};

fun lhs_of_term t = (HOLogic.dest_Trueprop #> HOLogic.dest_eq #> fst) t;

fun rhs_of_term t = (HOLogic.dest_Trueprop #> HOLogic.dest_eq #> snd) t;

val pair_defs = @{thms pair_def fstP_def sndP_def};

datatype pairing_path =
  DONE |
  FST of pairing_path |
  SND of pairing_path;

fun build_unpairing t DONE = t
  | build_unpairing t (FST x) = \<^Const>\<open>fstP for \<open>build_unpairing t x\<close>\<close>
  | build_unpairing t (SND x) = \<^Const>\<open>sndP for \<open>build_unpairing t x\<close>\<close>;

fun build_unpairing_from_idx t idx length =
  let
    fun repeat_snd 0 t = t
      | repeat_snd n t = \<^Const>\<open>sndP for \<open>repeat_snd (n - 1) t\<close>\<close>
  in
    if idx = length - 1
    then repeat_snd (idx + 1) t
    else \<^Const>\<open>fstP for \<open>repeat_snd (idx + 1) t\<close>\<close>
  end;

fun build_constructor_tag ctrs ctxt t =
  find_index (can (Ctr_Sugar_Util.fo_match ctxt t)) ctrs
  |> HOLogic.mk_number \<^typ>\<open>nat\<close>;

fun build_constructor_pairing ts c =
  let
    fun bcs c (t :: ts) = \<^Const>\<open>pair for c \<open>bcs t ts\<close>\<close>
      | bcs c [] = c;
  in
    bcs c (if ts = [] then [\<^term>\<open>0::nat\<close>] else ts)
  end;

fun rep_nat T = \<^Const>\<open>Rep_nat T\<close>;

fun abs_nat T = \<^Const>\<open>Abs_nat T\<close>;

fun mk_cr_type _ [] = error "Empty type list"
  | mk_cr_type T [T'] =
      [[\<^typ>\<open>nat\<close>, T'] ---> \<^typ>\<open>bool\<close>, [\<^typ>\<open>nat\<close>, T] ---> \<^typ>\<open>bool\<close>, \<^typ>\<open>nat\<close> --> \<^typ>\<open>nat\<close>,
        T' --> T]
      ---> \<^typ>\<open>bool\<close>
  | mk_cr_type T (T'::arg_Ts) =
      let
        val n = length arg_Ts + 1
        val snd_arg_T = (tl o tl) (binder_types (mk_cr_type T arg_Ts));
        val T1 = replicate n \<^typ>\<open>nat\<close> ---> \<^typ>\<open>nat\<close>
        val T2 = (T'::arg_Ts) ---> T
      in
          [[\<^typ>\<open>nat\<close>, T'] ---> \<^typ>\<open>bool\<close>, snd_arg_T ---> \<^typ>\<open>bool\<close>, T1, T2] ---> \<^typ>\<open>bool\<close>
      end;

fun mk_rel_funs _ [] = error "Empty type list"
  | mk_rel_funs T [T'] =
      list_comb
        (Const (\<^const_name>\<open>rel_fun\<close>, mk_cr_type T [T']), [\<^Const>\<open>cr_nat T'\<close>, \<^Const>\<open>cr_nat T\<close>])
  | mk_rel_funs T (T'::arg_Ts) =
      list_comb
        (Const (\<^const_name>\<open>rel_fun\<close>, mk_cr_type T (T'::arg_Ts)),
          [\<^Const>\<open>cr_nat T'\<close>, mk_rel_funs T arg_Ts]);

fun mk_cr_nat_equiv ctxt ctr_t =
  let
    val (ctr_nat_name, (ctr_Ts, T)) =
      dest_Const (head_of ctr_t)
      |>> suffix "_nat" o Long_Name.base_name
      ||> strip_type
    val args = [read_const' ctxt ctr_nat_name, ctr_t]
    val t = if null ctr_Ts then \<^Const>\<open>cr_nat T\<close> else mk_rel_funs T ctr_Ts
  in
    list_comb (t, args)
  end;

fun lift_ctr ctrs ctr_t ctxt =
  let
    val n = length (binder_types (type_of ctr_t));
    val ctr_nat_args = mk_names n "v" |> map (fn name => Free (name, \<^typ>\<open>pair_repr\<close>))
    val ctr_nat_rhs =
        build_constructor_tag ctrs ctxt ctr_t
        |> build_constructor_pairing ctr_nat_args;
    val ctr_nat_t =
      Free (Term.term_name ctr_t ^ "_nat", (replicate n \<^typ>\<open>pair_repr\<close>) ---> \<^typ>\<open>pair_repr\<close>);
    val ctr_nat_equ = mk_Trueprop_eq (list_comb (ctr_nat_t, ctr_nat_args), ctr_nat_rhs);
  in
    Specification.definition NONE [] [] (Binding.empty_atts, ctr_nat_equ) ctxt |>> snd o snd
  end;

fun lift_ctrs ctrs ctxt =
  let
    val (thms, (phi, ctxt)) =
    snd (Local_Theory.begin_nested ctxt)
    |> fold_map (lift_ctr ctrs) ctrs
    ||> `Local_Theory.end_nested
    ||> (fn (ctxt, old_ctxt) => (Proof_Context.export_morphism old_ctxt ctxt, ctxt))
    val cr_nat_equiv_terms = map (mk_cr_nat_equiv ctxt) ctrs
  in
    ((cr_nat_equiv_terms, map (Morphism.thm phi) thms), ctxt)
  end;

fun add_fun binding_name lhs rhs ctxt =
    let
      val fixes = [(binding_name, NONE, NoSyn)];
      val specs = [((Binding.empty_atts, BNF_Util.mk_Trueprop_eq (lhs, rhs)), [], [])];
    in
      Function_Fun.add_fun fixes specs Function_Fun.fun_config ctxt
    end;

fun add_abs_rep_fun T casex ctrs ctxt =
  let
    val (T_name, _) = dest_Type T;
    val T_base_name = Long_Name.base_name T_name;
    val abs_nat_binding = Binding.name ("Abs_nat_" ^ T_base_name);
    val rep_nat_binding = Binding.name ("Rep_nat_" ^ T_base_name);

    val abs_lhs = \<^Const>\<open>Abs_nat T\<close> $ Free ("v", T);
    val abs_cases =
      map (suffix "_nat" o Term.term_name) ctrs
      |> curry (op ~~) ctrs
      |> map (fn (ctr_t, ctr_nat_name) =>
          let
            val ctr_args_Ts = (binder_types o type_of) ctr_t;
            val n = length ctr_args_Ts;
            val encoded_args =
              map2 (curry op $) (map abs_nat ctr_args_Ts) (rev (map_range Bound n));
          in
            fold (fn (s, T) => fn t => Abs (s, T, t))
              (rev ((mk_names n "v") ~~ ctr_args_Ts))
              (list_comb (read_const' ctxt ctr_nat_name , encoded_args))
          end);

    val abs_rhs = list_comb (casex, abs_cases @ [Free ("v", T)]);

    val rep_lhs = \<^Const>\<open>Rep_nat T\<close> $ \<^term>\<open>v::pair_repr\<close>;
    val rep_conditions =
      map (build_constructor_tag ctrs ctxt #> curry HOLogic.mk_eq (\<^term>\<open>fstP v::pair_repr\<close>)) ctrs;
    val rep_cases =
      ctrs
      |> map (fn ctr_t =>
        let
          val ctr_args_Ts = (Term.binder_types o Term.type_of) ctr_t;
          val args_decoded =
            ctr_args_Ts
            |> map_index (fn (i, e) =>
              rep_nat e $ build_unpairing_from_idx \<^term>\<open>v::pair_repr\<close> i (length ctr_args_Ts));
        in
          Term.list_comb (ctr_t, args_decoded)
        end);

    val rep_rhs = Ctr_Sugar_Util.mk_IfN T rep_conditions rep_cases;
  in
    add_fun abs_nat_binding abs_lhs abs_rhs ctxt
    |> add_fun rep_nat_binding rep_lhs rep_rhs
  end;

fun datatype_lift_nat T ctrs casex (thy : theory) =
  let
    val (T_name, T_typ_args) = dest_Type T;
    val T_base_name = Long_Name.base_name T_name;
    val ((cr_nat_equiv_terms, new_ctrs), lthy) =
      Class.instantiation ([T_name], map dest_TFree T_typ_args, \<^sort>\<open>lift_nat\<close>) thy
      |> Local_Theory.begin_nested |> snd
      |> lift_ctrs ctrs
      ||> add_abs_rep_fun T casex ctrs;
    val new_lthy = Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism lthy new_lthy;

    val abs_rep_simps =
      [Proof_Context.get_thm new_lthy ("Rep_nat_" ^ T_base_name ^ ".simps"),
        Proof_Context.get_thm new_lthy ("Abs_nat_" ^ T_base_name ^ ".simps")];

    val (_, new_lthy) =
      Local_Theory.note ((Binding.empty, @{attributes [simp del]}), abs_rep_simps) new_lthy
    val new_ctrs = map (Morphism.thm phi) new_ctrs;

    val simps =
      @{thms rel_fun_def cr_nat_def prod_encode_0} @ abs_rep_simps @ new_ctrs @ pair_defs;

    val instantiated_lthy =
      Class.prove_instantiation_instance (fn ctxt =>
        Class.intro_classes_tac ctxt []
        THEN HEADGOAL (Subgoal.FOCUS_PARAMS_FIXED (fn {context = ctxt, ...} =>
          let
            val var = Free ("x", T)
            val inst =
              lambda var (HOLogic.mk_eq (\<^Const>\<open>Rep_nat T for \<^Const>\<open>Abs_nat T for var\<close>\<close>, var))
              |> Thm.cterm_of ctxt
            val thm =
              Proof_Context.get_thm ctxt (T_base_name ^ ".induct")
              |> infer_instantiate' ctxt [SOME inst]
          in
            resolve_tac ctxt [thm] 1
            THEN REPEAT (asm_full_simp_tac (ctxt addsimps new_ctrs @ abs_rep_simps @ pair_defs) 1)
          end
          ) ctxt)
        ) new_lthy;

    val cr_nat_equiv_thms =
      map (fn t =>
        Goal.prove instantiated_lthy [] [] (HOLogic.mk_Trueprop t)
          (fn {context=ctxt, ...} => asm_full_simp_tac (ctxt addsimps simps) 1)
        ) cr_nat_equiv_terms;

    val name = "cr_nat_" ^ T_base_name ^ "_equiv";
  in
    Local_Theory.note
      ((Binding.name name, @{attributes [transfer_rule]}), cr_nat_equiv_thms) instantiated_lthy
    |> snd
  end;

fun add_sort_lift_nat sort =
  if sort = \<^sort>\<open>type\<close> then \<^sort>\<open>lift_nat\<close> else insert (op =) \<^class>\<open>lift_nat\<close> sort;

fun normalize_type (Type (s, Ts)) = Type (s, map normalize_type Ts)
  | normalize_type T = TFree (apsnd add_sort_lift_nat (dest_TFree_or_TVar T));

val normalize_type_of_term =
  map_aterms (fn Var ((s, _), T) => Free (s, T) | x => x) #> map_types normalize_type;

fun datatype_lift_nat_cmd T thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val sugar =
      fst (dest_Type (Syntax.parse_typ ctxt T))
      |> Ctr_Sugar.ctr_sugar_of ctxt
      |> the;
    val T = normalize_type (#T sugar);
    val casex =
      subst_atomic_types [(body_type (type_of (#casex sugar)), \<^typ>\<open>pair_repr\<close>)] (#casex sugar)
      |> normalize_type_of_term;
    val ctrs = map normalize_type_of_term (#ctrs sugar);
  in
    datatype_lift_nat T ctrs casex thy
  end;

val _ =
  Outer_Syntax.command
    \<^command_keyword>\<open>datatype_lift_nat\<close>
    "Test"
    (Parse.typ >> datatype_lift_nat_cmd >> (Toplevel.begin_main_target false));

val _ =
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>test\<close>
    "Test"
    (Parse.typ >> K I);

datatype patmatch_term =
  CONSTRUCTOR of (string * typ) * (patmatch_term list) |
  VARIABLE of (indexname * typ);

datatype pairing_tree =
  LEAF |
  VAR of (indexname * typ) |
  NODE of (pairing_tree * pairing_tree);

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
  in
    mk_path DONE t
  end;

fun build_patmatch_term (Var v) = VARIABLE v
  | build_patmatch_term (Free (s, T)) = VARIABLE ((s, 0), T)
  | build_patmatch_term t =
      strip_comb t
      |>> dest_Const
      ||> map build_patmatch_term
      |> CONSTRUCTOR;

fun mk_variable_paths (VARIABLE n) = [(n, DONE)]
  | mk_variable_paths (CONSTRUCTOR (_, args)) = mk_path (NODE (LEAF, mk_pairing_tree args));

val subscript = implode o map (prefix "\<^sub>") o Symbol.explode;

fun argname i = "arg" ^ subscript (string_of_int (i + 1));

fun funname i = "f" ^ subscript (string_of_int (i + 1));

val argnames = map_range argname;

fun retag_list [] = []
  | retag_list [x] = x
  | retag_list (x :: xs) =
    (map (apsnd FST) x) @ (retag_list (map (map (apsnd SND)) xs));

(* TODO: Also replace with pairing_tree without retag? *)
fun extract_condition_paths (CONSTRUCTOR (c, args)) =
      retag_list ([(c, DONE)] ::
        (case args of [] => [[]] \<comment> \<open>dummy arg for 0-arity constructor\<close>
                    | args => map extract_condition_paths args))
  | extract_condition_paths (VARIABLE _) = [];

fun build_nat_condition ctrs ctxt t =
  let
    fun mk_condition (arg, x) =
      map (fn (match, path) =>
        build_constructor_tag ctrs ctxt (Const match)
        |> (pair (build_unpairing arg path) #> HOLogic.mk_eq)) x;
    val args_t = Term.args_of (lhs_of_term t);
    val new_args_t = map (fn s => Free (s, \<^typ>\<open>pair_repr\<close>)) (argnames (length args_t));
  in
    map (extract_condition_paths o build_patmatch_term) args_t
    |> (curry op ~~) new_args_t
    |> maps mk_condition
    |> foldl1 HOLogic.mk_conj
  end;

fun if_exp_of_case_exp_cmd T ctxt =
  let
    val {T, ctrs, casex, ...} =
      the (Ctr_Sugar.ctr_sugar_of ctxt (fst (dest_Type (Syntax.parse_typ ctxt T))));
    val args =
      map (binder_types o fastype_of) ctrs
      |> map (map_index (fn (i, T) => Free (argname i,  T)));
    val end_T =  (body_type (fastype_of casex));
    val T_base_name = Long_Name.base_name (fst (dest_Type T));
    val case_nat_binding_name = Binding.name ("case_" ^ T_base_name ^ "_nat");

    val fun_ts =
      binder_types (fastype_of casex)
      |> fst o split_last
      |> map_index (fn (i, T) => Free (funname i, T))

    val fun_ts2 =
      binder_types (fastype_of casex)
      |> fst o split_last
      |> map (length o fst o strip_type)
      |> map (fn i => (replicate i \<^typ>\<open>pair_repr\<close>) ---> \<^typ>\<open>pair_repr\<close>)
      |> map_index (fn (i, T) => Free (funname i, T));

    fun arguments_and_paths t =
      Term.args_of (lhs_of_term t)
      |> map (mk_variable_paths o build_patmatch_term)
      |> flat o map_index (fn (i, x) => map (pair (argname i)) x);

    fun nat_encode_term t =
      let
        val wrappers =
          map (fn (fun_arg_name, ((_, T), pattern_var_path)) => fn term =>
            term $ (rep_nat T $ build_unpairing (Free (fun_arg_name, \<^typ>\<open>pair_repr\<close>)) pattern_var_path))
          (arguments_and_paths t)
      in
        fold (fn f => fn x => f x) wrappers (rhs_of_term t)
      end;

    fun nat_encode_term2 t =
      let
        val wrappers =
          map (fn (fun_arg_name, ((_, _), pattern_var_path)) => fn term =>
            term $ (build_unpairing (Free (fun_arg_name, \<^typ>\<open>pair_repr\<close>)) pattern_var_path))
          (arguments_and_paths t)
      in
        fold (fn f => fn x => f x) wrappers (rhs_of_term t)
      end;

    val case_exp =
      (list_comb (casex, fun_ts)) $ (\<^Const>\<open>Rep_nat T\<close> $ Free (argname 0, \<^typ>\<open>pair_repr\<close>));

    val if_exp =
      map list_comb (ctrs ~~ args) ~~ fun_ts
      |> map (fn (t, rhs) => mk_Trueprop_eq (Term.dummy_pattern (fastype_of t --> end_T) $ t, rhs))
      |> (fn ts => (map (build_nat_condition ctrs ctxt) ts, map nat_encode_term ts))
      |-> mk_IfN end_T;

    val if_exp_2 =
      map list_comb (ctrs ~~ args) ~~ fun_ts2
      |> map (fn (t, rhs) =>
        mk_Trueprop_eq (Term.dummy_pattern (fastype_of t --> \<^typ>\<open>pair_repr\<close>) $ t, rhs))
      |> (fn ts => (map (build_nat_condition ctrs ctxt) ts, map nat_encode_term2 ts))
      |-> mk_IfN \<^typ>\<open>pair_repr\<close>
      |> fold lambda ((Free (argname 0, \<^typ>\<open>pair_repr\<close>))::(rev fun_ts2));

    val (_, ctxt) =
      Local_Theory.define
        ((case_nat_binding_name, NoSyn),
          ((Binding.suffix_name "_def" case_nat_binding_name, []), if_exp_2))
        ctxt;

    val goal = BNF_Util.mk_Trueprop_eq (case_exp, if_exp);

    val decoder_simps = Proof_Context.get_thms ctxt ("Rep_nat_" ^ T_base_name ^ ".simps");

    val schemvars = argname 0 :: map (fst o dest_Free) fun_ts;

    val thm =
      Goal.prove ctxt schemvars [] (normalize_type_of_term goal)
        (fn {context=ctxt, ...} => asm_full_simp_tac (ctxt addsimps decoder_simps) 1);

    val name = "case_" ^ T_base_name ^ "_eq_if";
  in
    Local_Theory.note ((Binding.name name, []), [thm]) ctxt |> snd
  end;

val _ =
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>test2\<close>
    "Test2"
    (Parse.typ >> if_exp_of_case_exp_cmd);


end