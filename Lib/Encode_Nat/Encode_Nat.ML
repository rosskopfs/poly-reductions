(*  Title:      Encode_Nat.ML
    Author:     Johannes Neubrand, TU Muenchen
    Author:     Andreas Vollert, TU Muenchen
    Copyright   2022, 2023
*)

infix 7 ***

signature ENCODE_NAT =
sig
end

structure Encode_Nat : ENCODE_NAT =
struct

fun map_prod f g (x, y) = (f x, g y);

fun f *** g = map_prod f g;

val tvar_to_tfree = Term.map_type_tvar (TFree o fst *** I);

val is_funtype = fn (Type ("fun", [_, _])) => true | _ => false;

\<comment> \<open>\<open>HOLogic.mk_conj\<close> is binary, so \<open>fold\<close>s would leave a stray \<open>True\<close>.\<close>
fun mk_conj' [] = @{term "True"}
  | mk_conj' [t] = t
  | mk_conj' (t :: ts) = HOLogic.mk_conj (t, mk_conj' ts);

val read_const' = Proof_Context.read_const {proper = false, strict = false};

fun lhs_of_term t = (HOLogic.dest_Trueprop #> HOLogic.dest_eq #> fst) t;

fun rhs_of_term t = (HOLogic.dest_Trueprop #> HOLogic.dest_eq #> snd) t;

fun collect_concrete_types (T as Type (_, Ts)) =
    fold (insert (op =)) (maps collect_concrete_types Ts) [T]
  | collect_concrete_types _ = [];

fun collect_types_of_term (Const (_, T)) = collect_concrete_types T
  | collect_types_of_term (Free (_, T)) = collect_concrete_types T
  | collect_types_of_term (Var (_, T)) = collect_concrete_types T
  | collect_types_of_term (Bound _) = []
  | collect_types_of_term (Abs (_, T, t)) = insert (op =) T (collect_types_of_term t)
  | collect_types_of_term (t1 $ t2) =
      union (op =) (collect_types_of_term t1) (collect_types_of_term t2);

datatype pairing_path =
  DONE |
  FST of pairing_path |
  SND of pairing_path;

fun build_unpairing t DONE = t
  | build_unpairing t (FST x) = @{term fstP} $ build_unpairing t x
  | build_unpairing t (SND x) = @{term sndP} $ build_unpairing t x;

fun build_unpairing_from_idx t idx length =
  let fun repeat_snd 0 t = t
        | repeat_snd n t = @{term sndP} $ repeat_snd (n - 1) t
  in
    if idx = length - 1
    then repeat_snd (idx + 1) t
    else @{term fstP} $ repeat_snd (idx + 1) t
  end;

fun pull_front i xs =
  (Library.nth xs i) :: (Library.nth_drop i xs);

fun get_ctrs_idx_bot ctxt T ctrs =
  let
    val T_base_name = Long_Name.base_name (fst (dest_Type T));
    val T_name = (fst (dest_Type T));
    val cond =
      fastype_of #> try dest_Type #> Option.map fst #> (curry (op =) (SOME T_name));
    (* TODO: find more efficient method. Can't use just the base name with find theorem as there
      might be several datatypes with the same base name *)
    val bot' =
      Find_Theorems.find_theorems ctxt NONE NONE false [(true, Find_Theorems.Name ("bot_" ^ T_base_name ^ "_def"))]
      |> snd
      |> map (snd #> Thm.prop_of #> rhs_of_term)
      |> Library.get_first (fn t => if cond t then SOME t else NONE)
      |> try (Option.map (fst o dest_Const))
      |> Option.join;
  in
    if is_none bot' then 0
    else Library.find_index ((curry (op =) (the bot')) o fst o dest_Const) ctrs
  end;

fun build_constructor_tag ctxt (t as (_, T)) =
  let
    val ctrs =
      Term.body_type T
      |> (map_type_tfree (fn (name, _) => TFree (name, ["Orderings.order_bot"])))
      |> try Term.dest_Type
      |> Option.map fst
      |> Option.map (Ctr_Sugar.ctr_sugar_of ctxt)
      |> Option.join
      |> Option.map #ctrs;
    val i = Option.getOpt (Option.map (get_ctrs_idx_bot ctxt (Term.body_type T)) ctrs, 0);
    val ctrs = Option.map (pull_front i) ctrs;
  in
    case Option.map (find_index (can (Ctr_Sugar_Util.fo_match ctxt (Const t)))) ctrs of
        SOME (~1) => NONE
      | SOME i => SOME (@{term atomic} $ HOLogic.mk_number @{typ nat} i)
      | NONE => NONE
  end;

fun build_constructor_pairing ts c =
  let
    fun bcs c (t :: ts) = @{term pair} $ c $ bcs t ts
      | bcs c [] = c;
  in
    bcs c (if ts = [] then [@{term "atomic 0"}] else ts)
  end;

fun encoder_name_of_type ctxt (Type (name, _)) =
      Name_Space.extern ctxt (Proof_Context.type_space ctxt) name
      |> Long_Name.base_name
      |> prefix "enc_"
  | encoder_name_of_type _ (TFree (name, _)) = prefix "enc_" name
  | encoder_name_of_type _ (TVar ((name, _), _)) = prefix "enc_" name;

fun encoder_args_of_type ctxt T =
  snd (dest_Type T)
  |> map (fn T => Free (encoder_name_of_type ctxt T, T --> @{typ "pair_repr"}))
  |> (fn x => x @ [Free ("v", T)])

fun encoder_type_of_type (T as Type (_, typargs)) =
      map (fn T => T --> @{typ "pair_repr"}) typargs
      |> (fn x => x @ [T])
      ---> @{typ "pair_repr"}
  | encoder_type_of_type (T as TFree _) = T --> @{typ "pair_repr"}
  | encoder_type_of_type (T as TVar _) = T --> @{typ "pair_repr"};

fun encoder_free_term_of_type ctxt T = Free (encoder_name_of_type ctxt T, encoder_type_of_type T);

fun encoder_const_term_of_type ctxt (T as Type _) =
      fst (dest_Const (read_const' ctxt (encoder_name_of_type ctxt T)))
      |> (fn name => Const (name, encoder_type_of_type T))
  | encoder_const_term_of_type _ _ = error "Can't build a const encoder for TVar or TFree";

fun encoder_term_of_type ctxt (T as Type _) = encoder_const_term_of_type ctxt T
  | encoder_term_of_type ctxt (T as TFree _) = encoder_free_term_of_type ctxt T
  | encoder_term_of_type ctxt (T as TVar ((_, i), _)) =
      Var ((encoder_name_of_type ctxt T, i), encoder_type_of_type T);

fun build_encoder_invocation ctxt freeT (T as Type (_, args)) =
  let
    val t = if freeT = SOME T
            then encoder_free_term_of_type ctxt T
            else encoder_const_term_of_type ctxt T;
  in
    Term.list_comb (t, map (build_encoder_invocation ctxt freeT) args)
  end
  | build_encoder_invocation ctxt _ (T as TFree _) = encoder_free_term_of_type ctxt T
  | build_encoder_invocation _ _ (TVar _) = error "Can't build an encoder for TVar";


fun mk_encoded_typ (Const (_, T)) =
  ((map (K @{typ "pair_repr"}) (binder_types T)) ---> @{typ "pair_repr"})
  | mk_encoded_typ _ = error "Can only make encoder of Const";

fun build_better_encoder ctxt T ctrs casex =
  let
    val lhs = Term.list_comb (encoder_free_term_of_type ctxt T, encoder_args_of_type ctxt T);
    val ctr_nat_ts =
      ctrs
      |> map (fn ctr_t =>
          let
            val ctr_nat_args =
              (binder_types o type_of) ctr_t
              |> map_index (fn (i, _) => Free ("v" ^ string_of_int i, @{typ "pair_repr"}));
            val ctr_nat_rhs =
              build_constructor_tag ctxt (dest_Const ctr_t)
              |> the
              |> build_constructor_pairing ctr_nat_args;
            val ctr_nat_name = Term.term_name ctr_t ^ "_nat";
            val ctr_nat_t = Free (ctr_nat_name, mk_encoded_typ ctr_t);
          in
            (ctr_nat_name, ctr_nat_t, ctr_nat_args, ctr_nat_rhs)
          end
        );
    val ctxt' =
      let
        fun f (_, ctr_nat_lhs, ctr_nat_args, ctr_nat_rhs) ctxt =
          let
            val _ = BNF_Util.mk_Trueprop_eq (Term.list_comb (ctr_nat_lhs, ctr_nat_args), ctr_nat_rhs)
              |> Thm.cterm_of ctxt;
            val ctr_nat_equ =
              BNF_Util.mk_Trueprop_eq (Term.list_comb (ctr_nat_lhs, ctr_nat_args), ctr_nat_rhs);
          in
            snd (Specification.definition NONE [] [] (Binding.empty_atts, ctr_nat_equ) ctxt)
          end;
      in
        fold f ctr_nat_ts ctxt
      end;
    val cases =
      ctrs ~~ ctr_nat_ts
      |> map (fn (ctr_t, (ctr_nat_name, _, _, _)) =>
          let
            val ctr_args_Ts = (binder_types o type_of) ctr_t;
            val encoded_args =
              (map (build_encoder_invocation ctxt (SOME T)) ctr_args_Ts, ctr_args_Ts)
              ||> (length #> (map_range Bound) #> rev)
              |-> map2 (curry op $);
            val res = (rev (map_index (fn (i, T) => ("v" ^ string_of_int i, T)) ctr_args_Ts),
                Term.list_comb (read_const' ctxt' ctr_nat_name , encoded_args))
              |->  fold (fn (s, T) => fn t => Abs (s, T, t));
          in
            res
          end
        ) |> map (Thm.cterm_of ctxt') |> map (Thm.term_of);
    val rhs = if T = @{typ "nat"} then Free ("v", T)
              else Term.list_comb (casex, cases @ [Free ("v", T)]);
  in
    (ctxt', BNF_Util.mk_Trueprop_eq (lhs, rhs))
  end;

fun normalize_type (Type (s, Ts)) = Type (s, map normalize_type Ts)
  | normalize_type (TFree (s, sort)) =
    let
      val new_sort = if sort = [@{class "HOL.type"}]
                     then [@{class "Orderings.order_bot"}]
                     else insert (op =) @{class "Orderings.order_bot"} sort;
    in TFree (s, new_sort) end
  | normalize_type (TVar (i, sort)) =
    let
      val new_sort = if sort = [@{class "HOL.type"}]
                     then [@{class "Orderings.order_bot"}]
                     else insert (op =) @{class "Orderings.order_bot"} sort;
    in TVar (i, new_sort) end;

val normalize_type_of_term =
      map_aterms (fn Var ((s, _), T) => Free (s, T) | x => x)
      #> map_types tvar_to_tfree
      #> map_types normalize_type;

fun datatype_nat_encode_cmd T ctxt =
  let
    val T_name = fst (dest_Type (Syntax.parse_typ ctxt T));
    val sugar = Ctr_Sugar.ctr_sugar_of ctxt T_name |> the;
    val T = tvar_to_tfree (#T sugar) |> normalize_type;
    val casex =
      subst_atomic_types [(body_type (type_of (#casex sugar)), @{typ "pair_repr"})] (#casex sugar)
      |> normalize_type_of_term;
    val ctrs = map (map_types tvar_to_tfree) (#ctrs sugar) |> map normalize_type_of_term;
    val (ctxt', eqns) = build_better_encoder ctxt T ctrs casex;
    val fixes = [(Binding.name (encoder_name_of_type ctxt T), NONE, NoSyn)];
    val specs = [((Binding.empty_atts, eqns), [], [])];
  in Function_Fun.add_fun fixes specs Function_Fun.fun_config ctxt'
  end;

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>datatype_nat_encode\<close>
    "Creates encoder for a data type"
    (Parse.typ >> datatype_nat_encode_cmd);

fun decoder_name_of_type ctxt (Type (name, _)) =
      Name_Space.extern ctxt (Proof_Context.type_space ctxt) name
      |> Long_Name.base_name
      |> prefix "dec_"
  | decoder_name_of_type _ (TFree (name, _)) =
      prefix "dec_" name
  | decoder_name_of_type _ (TVar _) = error "Can't build a decoder for TVar";

fun decoder_args_of_type ctxt T =
  snd (dest_Type T)
  |> map (fn T => Free (decoder_name_of_type ctxt T, @{typ "pair_repr"} --> T))
  |> (fn x => x @ [Free ("v", @{typ "pair_repr"})]);

fun decoder_type_of_type (T as Type (_, typargs)) =
      map (curry (op -->) @{typ "pair_repr"}) typargs
      |> (fn x => x @ [@{typ "pair_repr"}])
      ---> T
  | decoder_type_of_type (T as TFree _) = @{typ "pair_repr"} --> T
  | decoder_type_of_type (TVar _) = error "Can't build a decoder for TVar";

fun decoder_free_term_of_type ctxt T = Free (decoder_name_of_type ctxt T, decoder_type_of_type T);

fun decoder_const_term_of_type ctxt (T as Type _) =
      fst (dest_Const (read_const' ctxt (decoder_name_of_type ctxt T)))
      |> (fn name => Const (name, decoder_type_of_type T))
  | decoder_const_term_of_type _ _ = error "Can't build a Const decoder for a type variable";

fun build_decoder_invocation ctxt freeT (T as Type (_, args)) =
  let
    val t = if freeT = SOME T then decoder_free_term_of_type ctxt T
            else decoder_const_term_of_type ctxt T;
  in
    list_comb (t, map (build_decoder_invocation ctxt freeT) args)
  end
  | build_decoder_invocation ctxt _ (T as TFree _) = decoder_free_term_of_type ctxt T
  | build_decoder_invocation _ _ (TVar _) = error "Can't build a decoder for TVar";

fun build_decoder ctxt T ctrs =
  let
    val T = T |> map_type_tfree (fn (name, _) => TFree (name, ["Orderings.order_bot"]));
    val ctrs = map (map_types (map_type_tfree (fn (name, _) =>
                      TFree (name, ["Orderings.order_bot"])))) ctrs;
    val lhs = Term.list_comb (decoder_free_term_of_type ctxt T, decoder_args_of_type ctxt T);
    val free_var = Free ("v", @{typ "pair_repr"});
    val (conditions, cases) =
      ctrs
      |> map (fn ctr_t =>
        let
          val ctr_args_Ts = (Term.binder_types o Term.type_of) ctr_t;
          val args_decoded =
            ctr_args_Ts
            |> curry (op ~~) (map_range I (length ctr_args_Ts))
            |> map (fn (i, e) =>
                    build_decoder_invocation ctxt (SOME T) e
                    $ build_unpairing_from_idx free_var i (length ctr_args_Ts));
          val condition =
            build_constructor_tag ctxt (dest_Const ctr_t)
            |> the
            |> curry HOLogic.mk_eq (@{term "fstP"} $ free_var);
        in
          (condition, Term.list_comb (ctr_t, args_decoded))
        end)
     |> split_list;
    val rhs = if T = @{typ "nat"} then free_var
              else Ctr_Sugar_Util.mk_IfN T conditions cases;
  in
    BNF_Util.mk_Trueprop_eq (lhs, rhs)
  end;

fun datatype_nat_decode_cmd T ctxt =
  let
    val T_name = fst (dest_Type (Syntax.parse_typ ctxt T));
    val sugar = Ctr_Sugar.ctr_sugar_of ctxt T_name |> the;
    val T = tvar_to_tfree (#T sugar);
    val ctrs = map (map_types tvar_to_tfree) (#ctrs sugar);
    val eqns = build_decoder ctxt T ctrs;
    val fixes = [(Binding.name (decoder_name_of_type ctxt T), NONE, NoSyn)];
    val specs = [((Binding.empty_atts, eqns), [], [])];
    fun pat_completeness_auto ctxt =
            Pat_Completeness.pat_completeness_tac ctxt 1 THEN auto_tac ctxt;
  in
    snd (Function.add_function fixes specs Function_Fun.fun_config pat_completeness_auto ctxt)
  end;

val _ =
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>datatype_nat_decode\<close>
    "creates decoder for a datatype"
    (Parse.typ >> datatype_nat_decode_cmd);

fun mk_wellbehaved_thm_name ctxt (Type (name, _)) =
      Name_Space.extern ctxt (Proof_Context.type_space ctxt) name
      |> Long_Name.base_name
      |> prefix "encoding_"
      |> suffix "_wellbehaved"
  | mk_wellbehaved_thm_name _ _ = error "Can't generate wellbehaved theorem name for type variables";

fun mk_wellbehaved_thm enc dec =
  let
    val T = body_type (fastype_of dec)
  in
    BNF_Util.mk_Trueprop_eq(HOLogic.mk_comp (dec, enc), HOLogic.id_const T)
  end;

fun wellbehavedness_thm T int ctxt =
  let
    val T = map_type_tfree (fn (name, _) => TFree (name, ["Orderings.order_bot"])) T;
    val (encoder_args, decoder_args) =
      apply2 (fst o split_last) (encoder_args_of_type ctxt T, decoder_args_of_type ctxt T);
    val encoder = Term.list_comb (encoder_const_term_of_type ctxt T, encoder_args);
    val decoder = Term.list_comb (decoder_const_term_of_type ctxt T, decoder_args);
    val assms = map (uncurry mk_wellbehaved_thm) (encoder_args ~~ decoder_args);
    val goal = mk_wellbehaved_thm encoder decoder;
  in
    Specification.theorem
      true
      Thm.theoremK
      NONE
      (K I)
      (Binding.name (mk_wellbehaved_thm_name ctxt T), [])
      []
      [Element.Assumes [(Binding.empty_atts, map (rpair []) assms)]]
      (Element.Shows [(Binding.empty_atts, [(goal, [])])])
      int
      ctxt
  end;

fun datatype_nat_wellbehaved_cmd T int ctxt =
  let
    val {T, ...} = the (Ctr_Sugar.ctr_sugar_of ctxt (fst (dest_Type (Syntax.parse_typ ctxt T))));
  in
    wellbehavedness_thm (tvar_to_tfree T) int ctxt
  end;

val _ =
  Outer_Syntax.local_theory_to_proof'
    \<^command_keyword>\<open>datatype_nat_wellbehaved\<close>
    "generates proof obligations to relate encoders and decoders of a type"
    (Parse.typ >> datatype_nat_wellbehaved_cmd);

datatype patmatch_term =
  CONSTRUCTOR of (string * typ) * (patmatch_term list) |
  VARIABLE of (indexname * typ);

fun build_patmatch_term (Var v) = VARIABLE v
  | build_patmatch_term (Free (s, T)) = VARIABLE ((s, 0), T)
  | build_patmatch_term t =
      Term.strip_comb t
      |>> Term.dest_Const
      ||> map build_patmatch_term
      |> CONSTRUCTOR;

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

datatype pairing_tree =
  LEAF |
  VAR of (indexname * typ) |
  NODE of (pairing_tree * pairing_tree);

fun mk_pairing_tree [] = LEAF
  | mk_pairing_tree [(VARIABLE n)] = VAR n
  | mk_pairing_tree ((VARIABLE n) :: xs) = NODE (VAR n, mk_pairing_tree xs)
  | mk_pairing_tree ((CONSTRUCTOR (_, [])) :: xs) =
      NODE (NODE (LEAF, LEAF), mk_pairing_tree xs) |> @{print}
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

fun mk_variable_paths (VARIABLE n) = [(n, DONE)]
  | mk_variable_paths (CONSTRUCTOR (_, args)) = mk_path (NODE (LEAF, mk_pairing_tree args));

val subscript = implode o map (prefix "\<^sub>") o Symbol.explode;

fun argname i = "arg" ^ subscript (string_of_int (i + 1));

val argnames = map_range argname;

fun replace_constructors _ (Const (\<^const_name>\<open>undefined\<close>, _)) =
    error "Correctness will not work with undefined! Rewrite to function that uses bot!"
  | replace_constructors _ (t as (Const (\<^const_name>\<open>bot\<close>, _))) = t
  | replace_constructors ctxt t =
    Term.strip_comb t
    ||> map (replace_constructors ctxt)
    |> (fn (h, args') =>
       case h of
         Const (n, T) =>
            (case build_constructor_tag ctxt (n, T) of
              SOME cons_nat => build_constructor_pairing args' cons_nat
            | NONE => Term.list_comb (h, args'))
       | _ => Term.list_comb (h, args'));


fun change_if ctxt (t as ((c as Const ("HOL.If", _)) $ cond $ thn $ els)) =
  if fst (Term.dest_Const (Term.head_of cond)) = "HOL.eq" then t
  else c $ (decoder_const_term_of_type ctxt @{typ "bool"} $ cond) $ thn $ els
  | change_if ctxt (t $ u) = change_if ctxt t $ u
  | change_if _ x = x;

fun const_nat_unchanged s =
          s <> "HOL.True"
  andalso s <> "HOL.False"
  andalso exists (fn x => String.isPrefix x s)
           ["HOL.", \<comment> \<open>\<open>If\<close>, \<open>Let\<close>, and more\<close>
            "Nat.", "Num.", "Groups.", \<comment> \<open>Relating to (natural) numbers\<close>
            "enc"
           ]
  orelse exists (fn x => String.isPrefix x (Long_Name.base_name s)) \<comment> \<open>Very hacky\<close>
           [
            "dec"
           ]
  orelse exists (fn x => x = s)
          (List.map (fst o dest_Const) [@{term fstP}, @{term sndP}, @{term atomic}, @{term pair}]);

fun change_const_to_nat ctxt parent_fun_name (t as Const (c, _)) =
  if c = "Orderings.bot_class.bot" then Const (c, @{typ "pair_repr"})
  else if c = "HOL.If" then Const (c, @{typ "bool \<Rightarrow> pair_repr \<Rightarrow> pair_repr \<Rightarrow> pair_repr"})
  else if c = "HOL.eq" then Const (c, @{typ "pair_repr \<Rightarrow> pair_repr \<Rightarrow> bool"})
  else if const_nat_unchanged c then t
  else if c = parent_fun_name then Const (c ^ "_nat", mk_encoded_typ t)
  else read_const' ctxt (Long_Name.base_name c ^ "_nat")
 | change_const_to_nat _ _ x = x;

fun const_to_free (c, T) t =
  Term.subst_atomic [(Const (c, T), Free (Long_Name.base_name c, T))] t;

fun replace_suc t =
  let
    fun minus_one v =
          Const ("Groups.minus_class.minus", @{typ "nat \<Rightarrow> nat \<Rightarrow> nat"})
            $ v $ Const ("Groups.one_class.one", @{typ "nat"});
    fun substs_for_suc (t as (Const ("Nat.Suc", _) $ v)) = [(t, v), (v, minus_one v)]
      | substs_for_suc _ = [];
    val substs =
      Term.args_of (lhs_of_term t)
      |> maps substs_for_suc;
    val res =
      t
      |> Term.subst_free substs;
  in
    res
  end;

fun build_nat_condition ctxt t =
  let
    fun mk_condition (arg, x) =
      map (fn (match, path) =>
            if match = ("Groups.zero_class.zero", @{typ "nat"})
            then HOLogic.mk_eq (arg, HOLogic.mk_number @{typ nat} 0)
            else
              the (build_constructor_tag ctxt match)
              |> (pair (build_unpairing arg path) #> HOLogic.mk_eq)) x;
    val args_t = Term.args_of (lhs_of_term t);
    val new_args_t = map (fn s => Free (s, @{typ "pair_repr"})) (argnames (length args_t));
    val condition_paths =
      map build_patmatch_term args_t
      |> map extract_condition_paths;
    val ret =
      (new_args_t ~~ condition_paths)
      |> map mk_condition
      |> List.concat |> map (Thm.cterm_of ctxt)  |> map Thm.term_of
      |> mk_conj';
  in
    ret
  end;

fun nat_encode_term ctxt t =
  let
    val arguments_and_paths =
      lhs_of_term t
      |> map_types tvar_to_tfree
      |> Term.args_of
      |> map build_patmatch_term
      |> map mk_variable_paths
      |> flat o map_index (fn (i, x) => map (pair (argname i)) x);
    val wrappers =
      let
        fun f (fun_arg_name, (pattern_var_t as ((pattern_var_name, _), T), pattern_var_path)) term =
        let
        val _ = T |> @{print}
        in
          (Const (\<^const_name>\<open>HOL.Let\<close>, @{typ "pair_repr \<Rightarrow> (pair_repr \<Rightarrow> pair_repr) \<Rightarrow> pair_repr"}))
           $ build_unpairing (Free (fun_arg_name, @{typ "pair_repr"})) pattern_var_path
           $ Term.abs (pattern_var_name, @{typ "pair_repr"}) (abstract_over (Var pattern_var_t, term))
        end;
      in
        map f arguments_and_paths
      end;
  in
    t
    |> rhs_of_term
    |> map_types tvar_to_tfree
    |> change_if ctxt |> Thm.cterm_of ctxt |> @{print} |> Thm.term_of
    |> fold (fn f => fn x => f x) wrappers
  end;

fun function_nat_rewrite s ctxt =
  let
    val t = Syntax.read_term ctxt s
    val (fun_name, _) = Term.dest_Const t
    val newfun_name = (Long_Name.base_name fun_name) ^ "_nat"
    val arg_Ts = (binder_types (fastype_of t))
    val arg_ts =
      argnames (List.length arg_Ts)
      |> map (fn argname => Free (argname, @{typ "pair_repr"}))
    val newfun_T = mk_encoded_typ t
    val newfun_t = Free (newfun_name, newfun_T)
    val lhs = Term.list_comb (newfun_t, arg_ts)
    val (nat_cond, t_encoded) =
      Proof_Context.get_thms ctxt (fun_name ^ ".simps")
      |> map Thm.prop_of
      |> map replace_suc
      |> (fn t => (map (build_nat_condition ctxt) t, map (nat_encode_term ctxt) t))
    val ite =
      Ctr_Sugar_Util.mk_IfN (Term.body_type newfun_T) nat_cond t_encoded
      |> Term.map_aterms (change_const_to_nat ctxt fun_name)
      |> const_to_free (fun_name ^ "_nat", newfun_T)
    val (_, newfun_lthy) =
      Partial_Function.add_partial_function
        "tailrec"
        [(Binding.name newfun_name, NONE, NoSyn)]
        ((Binding.empty, []), BNF_Util.mk_Trueprop_eq (lhs, ite))
        ctxt;
  in
    newfun_lthy
  end;

val _ =
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>function_nat_rewrite\<close>
    "converts existing tail-recursive functions into nat encoded functions"
    (Parse.term >> function_nat_rewrite)

fun mk_dec_bot_eq_bot ctxt T =
  let
    val lhs = decoder_free_term_of_type ctxt T $ (Const (\<^const_name>\<open>bot\<close>, @{typ "pair_repr"}))
    val rhs = Const (\<^const_name>\<open>bot\<close>, T)
  in
    BNF_Util.mk_Trueprop_eq (lhs, rhs)
  end;

fun mk_enc_bot_eq_bot ctxt T =
  let
    val lhs = encoder_free_term_of_type ctxt T $ (Const (\<^const_name>\<open>bot\<close>, T))
    val rhs = Const (\<^const_name>\<open>bot\<close>, @{typ "pair_repr"})
  in
    BNF_Util.mk_Trueprop_eq (lhs, rhs)
  end;

fun function_nat_rewrite_correctness_cmd fn_str int ctxt  =
  let
    val (fn_name, (fn_T, fn_t)) =
      Syntax.read_term ctxt fn_str
      |> map_types (map_type_tfree (fn (name, _) => TFree (name, ["Orderings.order_bot"])))
      |> `Term.term_name
      ||> `fastype_of
    val fn_args =
      map_index (fn (i, T) =>
                 Free ("arg" ^ subscript (string_of_int (i + 1)), T)) (Term.binder_types fn_T)
    val rhs = Term.list_comb (fn_t, fn_args)
    val lhs =
      map (fn t => (build_encoder_invocation ctxt NONE (fastype_of t)) $ t) fn_args
      |> Term.list_comb o (pair (read_const' ctxt (fn_name ^ "_nat")))
      |> (curry op $) (build_decoder_invocation ctxt NONE (Term.body_type fn_T))
    val _ = fn_T
    val assms =
      fold_atyps (insert (op =)) fn_T []
      |> maps (fn T =>
                [mk_wellbehaved_thm (encoder_free_term_of_type ctxt T) (decoder_free_term_of_type ctxt T),
                 mk_dec_bot_eq_bot ctxt T])
    val goal =
      BNF_Util.mk_Trueprop_eq (lhs, rhs)
  in
    Specification.theorem
      true
      Thm.theoremK
      NONE
      (K I)
      (Binding.name (fn_name ^ "_nat_equiv"), [])
      []
      [Element.Assumes [(Binding.empty_atts, map (rpair []) assms)]]
      (Element.Shows [(Binding.empty_atts, [(goal, [])])])
      int
      ctxt
  end;



fun function_nat_rewrite_correctness_cmd2 fn_str ctxt =
  let
    val (fn_name, (fn_T, fn_t)) =
      Syntax.read_term ctxt fn_str
      |> map_types (map_type_tfree (fn (name, _) => TFree (name, ["Orderings.order_bot"])))
      |> `Term.term_name
      ||> `fastype_of
    val fn_args =
      map_index (fn (i, T) =>
                 Free ("arg" ^ subscript (string_of_int (i + 1)), T)) (Term.binder_types fn_T)
    val rhs = Term.list_comb (fn_t, fn_args)
      |> (curry op $) (build_encoder_invocation ctxt NONE (Term.body_type fn_T))
    val lhs =
      map (fn t => (build_encoder_invocation ctxt NONE (fastype_of t)) $ t) fn_args
      |> Term.list_comb o (pair (read_const' ctxt (fn_name ^ "_nat")))
    val _ = fn_T
    val assms =
      fold_atyps (insert (op =)) fn_T []
      |> maps (fn T =>
                [mk_wellbehaved_thm (encoder_free_term_of_type ctxt T) (decoder_free_term_of_type ctxt T),
                 mk_dec_bot_eq_bot ctxt T])
    val argnames =
      map_range (fn i => "arg" ^ subscript (string_of_int (i + 1))) (length (Term.binder_types fn_T))
    val schemvars =
      fold_atyps (insert (op =)) fn_T []
      |> maps (fn T => [encoder_name_of_type ctxt T, decoder_name_of_type ctxt T])
      |> (curry op @) argnames
    val goal =
      BNF_Util.mk_Trueprop_eq (lhs, rhs)
    val encoder_simps =
        Library.distinct (op =) ((body_type fn_T)::(binder_types fn_T))
        |> map (suffix ".simps" o encoder_name_of_type ctxt)
        |> maps (Proof_Context.get_thms ctxt)
    val other_simps =
        ["fstP.simps", "sndP.simps", "atomic.simps", "pair.simps"]
        |> maps (Proof_Context.get_thms ctxt)
    val induction_rule =
      Proof_Context.get_thms ctxt (fn_name ^ ".induct")
    val fn_nat_simps =
      Proof_Context.get_thms ctxt (fn_name ^ "_nat.simps")
    val fn_simps =
      Proof_Context.get_thms ctxt (fn_name ^ ".simps")
    val bla =
      Induct_Tacs.induct_tac ctxt [map SOME argnames] (SOME induction_rule) 1
      THEN ALLGOALS (EqSubst.eqsubst_tac ctxt [0] fn_nat_simps)
      THEN ALLGOALS (EqSubst.eqsubst_tac ctxt [0] fn_simps)
      THEN ALLGOALS (full_simp_tac (ctxt addsimps encoder_simps))
      THEN ALLGOALS (full_simp_tac (ctxt addsimps other_simps))
    val a =
      Goal.prove ctxt schemvars assms goal (fn {...} => bla)
  in
    Local_Theory.note ((Binding.name (fn_name ^ "_nat_equiv"), []), [a]) ctxt
    |> snd
  end;

fun get_conditions_of_ifs t =
  let
    fun f acc (Const ("HOL.If", _) $ cond $ u) = insert (op =) cond (f acc u)
      | f acc (t $ u) = union (op =) (f acc t) (f acc u)
      | f acc (Abs (_, _, t)) = f acc t
      | f acc _ = acc
  in
    f [] t
  end;

val _ =
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>test\<close>
    "Test"
    (Parse.term >> function_nat_rewrite_correctness_cmd2)

val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>function_nat_rewrite_correctness\<close>
    "converts existing functions into nat encoded functions"
    (Parse.term >> function_nat_rewrite_correctness_cmd)

fun construct_equiv_lemma ctxt uses_bot t =
  let
    val fun_base_name = Long_Name.base_name (fst (Term.dest_Const t))
    val fun_T = fastype_of t
    val (fun_arg_Ts, fun_body_T) = Term.strip_type fun_T
    val fun_arg_ts =
      map_index (fn (i, T) => Free ("arg" ^ subscript (string_of_int (i + 1)), T)) fun_arg_Ts

    val correctness_rhs =
      Term.list_comb (t, fun_arg_ts)
      |> (curry op $) (build_encoder_invocation ctxt NONE fun_body_T)

    val fun_nat_t =
      fun_base_name ^ "_nat"
      |> Proof_Context.read_const {proper = true, strict = false} ctxt

    val correctness_lhs =
      map (fn t => (build_encoder_invocation ctxt NONE (fastype_of t)) $ t) fun_arg_ts
      |> Term.list_comb o (pair fun_nat_t)

    val assms =
      fold_atyps (insert (op =)) fun_T []
      |> maps (fn T =>
          [mk_wellbehaved_thm (encoder_free_term_of_type ctxt T) (decoder_free_term_of_type ctxt T),
           mk_dec_bot_eq_bot ctxt T])

    (* Only add bot assumption if bot is used in function? *)
    val assms =
      fold_atyps (insert (op =)) fun_T []
      |> maps (fn T =>
          [mk_wellbehaved_thm (encoder_free_term_of_type ctxt T) (decoder_free_term_of_type ctxt T)]
          |> uses_bot ? ((curry op ::) (mk_enc_bot_eq_bot ctxt T)))

    val argnames =
      map_range (fn i => "arg" ^ subscript (string_of_int (i + 1))) (length (Term.binder_types fun_T))

    val schemvars =
      fold_atyps (insert (op =)) fun_T []
      |> maps (fn T => [encoder_name_of_type ctxt T, decoder_name_of_type ctxt T])
      |> (curry op @) argnames
    val goal =
      BNF_Util.mk_Trueprop_eq (correctness_lhs, correctness_rhs)
  in
    (schemvars, assms, goal)
  end

fun constructor_equiv_lemma ctxt t =
  let
    val (schemvars, assms, goal) = construct_equiv_lemma ctxt false t
    val _ = schemvars
    val _ = map (Thm.cterm_of ctxt) assms
    val _ = Thm.cterm_of ctxt goal

    val encoder_simp =
      encoder_name_of_type ctxt (Term.body_type (fastype_of t))
      |> suffix ".simps"
      |> Proof_Context.get_thms ctxt

    val const_def =
      Long_Name.base_name (fst (dest_Const t))
      |> suffix "_nat_def"
      |> Proof_Context.get_thms ctxt

    val thm =
      Goal.prove ctxt schemvars assms goal
        (fn {context=ctxt, ...} =>
           asm_full_simp_tac (ctxt addsimps encoder_simp addsimps const_def) 1)

  in
    thm
  end;

fun constructor_equiv_lemmas_cmd T ctxt =
  let
    val T_name = fst (dest_Type (Syntax.parse_typ ctxt T))
    val sugar = Ctr_Sugar.ctr_sugar_of ctxt T_name |> the
    val ctrs = map (map_types tvar_to_tfree) (#ctrs sugar) |> map normalize_type_of_term
    val goals = map (constructor_equiv_lemma ctxt) ctrs
    val names = map (suffix "_nat_equiv" o Term.term_name) ctrs
    fun add_thm (name, thm) ctxt =
      Local_Theory.note ((Binding.name name, []), [thm]) ctxt |> snd
  in
    fold add_thm (names ~~ goals) ctxt
  end;

val _ =
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>test2\<close>
    "Test2"
    (Parse.typ >> constructor_equiv_lemmas_cmd)

fun function_nat_rewrite_auto s ctxt =
  let

    (* Build nat encoded function*)

    val t = Syntax.read_term ctxt s |> normalize_type_of_term
    val (fun_name, _) = Term.dest_Const t
    val fun_T = fastype_of t
    val fun_arg_Ts = (binder_types (fastype_of t))

    val fun_simps =  Proof_Context.get_thms ctxt (fun_name ^ ".simps")

    val fun_nat_name = (Long_Name.base_name fun_name) ^ "_nat"
    val fun_nat_T = mk_encoded_typ t
    val fun_nat_arg_ts =
      argnames (List.length fun_arg_Ts)
      |> map (fn argname => Free (argname, @{typ "pair_repr"}))
    val fun_nat_t = Free (fun_nat_name, fun_nat_T)

    val fun_nat_lhs = Term.list_comb (fun_nat_t, fun_nat_arg_ts)
    val fun_nat_rhs =
      map Thm.prop_of fun_simps
      |> map replace_suc (* "morally" replace "f (Suc n) = g n" by "f n = g (n - 1)" *)
      |> (fn ts => (map (build_nat_condition ctxt) ts, map (nat_encode_term ctxt) ts))
      |-> Ctr_Sugar_Util.mk_IfN (Term.body_type fun_nat_T)
      |> Term.map_aterms (change_const_to_nat ctxt fun_name)
      |> const_to_free (fun_name ^ "_nat", fun_nat_T)
      |> normalize_type_of_term |> @{print} |> Thm.cterm_of ctxt |> @{print} |> Thm.term_of

    val (_, fun_nat_lthy) =
      Partial_Function.add_partial_function
        "tailrec"
        [(Binding.name fun_nat_name, NONE, NoSyn)]
        ((Binding.empty, []), BNF_Util.mk_Trueprop_eq (fun_nat_lhs, fun_nat_rhs))
        ctxt

    val ctxt' : Proof.context = fun_nat_lthy
    val fun_nat_simps = Proof_Context.get_thms ctxt' (fun_name ^ "_nat.simps") |> @{print}

    (* start constructing and proving correctness lemma *)

    val uses_bot =
      map Thm.prop_of fun_simps
      |> map (fn t => fold_aterms (fn Const ("Orderings.bot_class.bot", _) => K true | _ => I) t false)
      |> foldl1 (fn (a, b) => a orelse b) |> @{print}

    val fun_patmached_arg_ts =
      map Thm.prop_of fun_simps
      |> map lhs_of_term
      |> maps (snd o Term.strip_comb)

    fun mk_encoder_invocation ctxt (T as Type (_, typargs)) =
          Term.list_comb (encoder_const_term_of_type ctxt T, map (mk_encoder_invocation ctxt) typargs)
      | mk_encoder_invocation ctxt (T as TFree _) = encoder_free_term_of_type ctxt T
      | mk_encoder_invocation ctxt T = encoder_term_of_type ctxt T

    fun encode_term ctxt t =
      Term.list_comb (mk_encoder_invocation ctxt (type_of t), [t])

    val type_typ_in_fun =
      map (Thm.prop_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq) fun_simps
      |> (op @) o split_list
      |> maps collect_types_of_term
      |> map collect_concrete_types
      |> map (filter_out is_funtype)
      |> foldl1 (merge (op =))

    val encoder_simps =
      map (encoder_name_of_type ctxt') type_typ_in_fun
      |> distinct (op =)
      |> map (suffix ".simps")
      |> maps (Proof_Context.get_thms ctxt')

    val ctrs =
      map (fst o dest_Type) type_typ_in_fun
      |> distinct (op =)
      |> map (Ctr_Sugar.ctr_sugar_of ctxt')
      |> maps the_list
      |> maps #ctrs

    val ctr_simps =
      ctrs
      |> map ((suffix "_nat_def") o Long_Name.base_name o fst o dest_Const)
      |> maps (Proof_Context.get_thms ctxt')

    val let_simps_thms =
      fun_patmached_arg_ts
      |> map (Thm.cterm_of ctxt)
      |> map Thm.term_of
      |> filter (not o is_Var) (* don't need simplification for a variable itself *)
      |> maps (fn t =>
        let
          val _ = t |> Thm.cterm_of ctxt |> @{print}
        in
        build_patmatch_term t |> @{print}
        |> map (apfst Var) o mk_variable_paths |> @{print}
        |> map (pair (encode_term ctxt' t))
        end)
      (* now like: [(enc_list enc_'a (x # xs), (x, <pairing path to x>)), ...] *)
      |> map (fn (enc_t, (var, p)) =>
          (BNF_Util.mk_Trueprop_eq (build_unpairing enc_t p, encode_term ctxt' var)
           |> normalize_type_of_term,
           fold_aterms (fn Var ((s,_),_) => insert (op =) s | _ => I) enc_t []))
      (* now like: [(sndP (sndP (enc_list enc_'a (x # xs))) = enc_list enc_'a xs,
                     <list of free vars in this term>, ...] *)
      |> map (fn (t, vars) =>
          let
            val _ = t |> Thm.cterm_of ctxt
          in
          Goal.prove ctxt' vars [] t
            (fn {context=ctxt, ...} =>
               print_tac ctxt "start"
               THEN asm_full_simp_tac (ctxt addsimps encoder_simps addsimps ctr_simps) 1
               THEN print_tac ctxt "after"
             )
          end)|> @{print}

    fun collect_const_invocations t =
      let
        val (fn_t, args) = strip_comb t
        val acc = (if fst (dest_Const fn_t) <> fun_name then [t] else [])
        handle TERM _ => []
      in
        map collect_const_invocations args
        |> (fn x => fold (union (op =)) x acc)
      end;

    fun collect_const_nat_invocations t =
      let
        val (fn_t, args) = strip_comb t
      in
        maps collect_const_nat_invocations args
          @ (if is_Const fn_t andalso fst (dest_Const fn_t) <> fun_name
             then [(fn_t, args)] else [])
      end;

    val const_ts =
      map Thm.prop_of fun_simps
      |> map rhs_of_term
      |> map collect_const_invocations
      |> Library.foldl1 (merge (op =))

    val const_ts_alt =
      map Thm.prop_of fun_simps
      |> map rhs_of_term
      |> map (map_types normalize_type)
      |> maps collect_const_nat_invocations

    fun const_equiv_thms_of_thm thm =
      Thm.prop_of thm
      |> rhs_of_term
      |> map_types normalize_type
      |> collect_const_nat_invocations
      |> map (fn (t, args) =>
        let
          val (s, _) = dest_Const t

          val inv_fun_arg_Ts =
            binder_types (fastype_of (read_const' ctxt' s))
            |> map normalize_type

          val reg_invoc =
            (read_const' ctxt' s)
            |> map_types normalize_type

          val inv_fun_arg_ts =
            inv_fun_arg_Ts
            |> map_index (fn (i, T) => Var ((argname i, 0), T))

          val a =
            Term.list_comb (reg_invoc, inv_fun_arg_ts)
            |> Thm.cterm_of ctxt'

          val b =
            list_comb (t, args)
            |> Thm.cterm_of ctxt'

          val substs = Thm.first_order_match (a, b)

          val equiv_thm =
            if const_nat_unchanged (@{print} s)
            orelse s = "Orderings.bot_class.bot" |> @{print}
            then NONE |> @{print}
            else SOME (hd (Proof_Context.get_thms ctxt' (Long_Name.base_name s ^ "_nat_equiv"))) |> @{print}
        in
          Option.map (Thm.instantiate substs) equiv_thm
        end
        )
      |> map_filter I

    val const_equiv_thms =
      maps const_equiv_thms_of_thm fun_simps
      |> @{print}




    (* val equiv_thms_inst =
      map (equiv_thms_inst_prems ctxt) equiv_thms_inst_vars  *)

    fun if_exp_simp_tac ctxt i thm =
      let
        val if_simps =
          Thm.prems_of thm
          |> maps get_conditions_of_ifs
          |> maps (fn t => [BNF_Util.mk_Trueprop_eq (t, @{term "True"}),
                           BNF_Util.mk_Trueprop_eq (t, @{term "False"})])
          |> map_filter (try (fn t =>
               Goal.prove ctxt [] [] t (fn {context=ctxt, ...} =>
                full_simp_tac (ctxt addsimps encoder_simps addsimps ctr_simps) 1)))
      in
        (EqSubst.eqsubst_tac ctxt [0] if_simps i
        THEN (EqSubst.eqsubst_tac ctxt [0] @{thms HOL.if_False HOL.if_True} i)) thm
      end

    fun solve_subgoal_tac ctxt assms i =
      let
        val _ = assms |> @{print}
        fun instantiate_equiv thm =
          let
            val prem = Thm.major_prem_of thm
          in
            case rhs_of_term prem of
              Const ("Fun.id", id_T) =>
                (case body_type id_T of
                  Type (s, _) => Long_Name.base_name s
                    |> prefix "encoding_" o suffix "_wellbehaved"
                    |> hd o Proof_Context.get_thms ctxt
                    |> instantiate_equiv
                    |> Option.map (curry (op OF) thm o single)
                    |> the |> instantiate_equiv
                | TVar _ => get_first (try (curry (op OF) thm o single)) assms
                            |> the |> instantiate_equiv
                | _ => get_first (try (curry (op OF) thm o single)) assms
                            |> the |> instantiate_equiv )
            | Const ("Orderings.bot_class.bot", bot_T) =>
                (case body_type bot_T of
                  Type (s, _) => Long_Name.base_name s
                    |> prefix "dec_" o suffix "_bot"
                    |> hd o Proof_Context.get_thms ctxt
                    |> instantiate_equiv
                    |> Option.map (curry (op OF) thm o single)
                    |> the |> instantiate_equiv
                | TVar _ => get_first (try (curry (op OF) thm o single)) assms
                            |> the |> instantiate_equiv
                | _ => get_first (try (curry (op OF) thm o single)) assms
                            |> the |> instantiate_equiv )
            | _ => NONE
          end
          handle THM _ => SOME thm
          handle Option => NONE
        val const_equiv_thms_instantiated =
          const_equiv_thms
          |> map instantiate_equiv
          |> map_filter I |> @{print}
        fun subst_nat_invocation_tac j =
          nth fun_simps (i - 1)
          |> const_equiv_thms_of_thm
          |> map instantiate_equiv
          |> map_filter I |> @{print}
          |> map (simplify (clear_simpset ctxt addsimps (Proof_Context.get_thms ctxt "enc_nat.simps")))
          |> map (fn thm => (EqSubst.eqsubst_tac ctxt [1] [thm] j))
          |> foldl1 ((op THEN))
          handle Empty => all_tac

        val j = i
        val i = 1
      in
        Subgoal.FOCUS_PARAMS (fn {context = ctxt, ...} =>
        print_tac ctxt "start solve subgoal"
        THEN EqSubst.eqsubst_tac ctxt [0] fun_nat_simps i
        THEN print_tac ctxt "after subst nat fun"
        THEN EqSubst.eqsubst_tac ctxt [0] fun_simps i
        THEN print_tac ctxt "after subst fun"
        THEN REPEAT_DETERM (if_exp_simp_tac ctxt i)
        THEN (print_tac ctxt "after if")
        THEN (simp_tac (clear_simpset ctxt addsimps let_simps_thms addsimps @{thms HOL.Let_def}) i)
        THEN (print_tac ctxt "after let simps and let def")
        (* THEN TRY (simp_tac (clear_simpset ctxt addsimps ctr_simps) 1)
        THEN (print_tac ctxt "after constructor simps") *)
         (* THEN foo
        THEN print_tac ctxt "after foo" *)
(*         THEN TRY (simp_tac (clear_simpset ctxt addsimps const_equiv_thms_instantiated) i)
        THEN print_tac ctxt "after subst const equiv thms instantiated" *)
(*         THEN Method.insert_tac ctxt (assms @ wellbehaved_thms @ const_equiv_thms) 1
        THEN (print_tac ctxt "after insert prems and wellbehaved") *)
        THEN (subst_nat_invocation_tac i)
        (* THEN TRY (asm_full_simp_tac (clear_simpset ctxt addsimps (@{print} const_equiv_thms_instantiated)) i) *)
        THEN (print_tac ctxt "after subst nat invocations")
        (* THEN TRY (auto_tac (ctxt addsimps (encoder_simps @ ctr_simps @ const_equiv_thms_instantiated)) ) *)
        THEN (print_tac ctxt "after equiv simps")
        THEN TRY (asm_full_simp_tac (ctxt addsimps assms) i)
        THEN (print_tac ctxt "after almost last simps")
        THEN TRY (auto_tac (ctxt addsimps encoder_simps addsimps assms) )
        THEN (print_tac ctxt "after last simps")
        ) ctxt (@{print} j)
      end;

    val (schemvars, assms, goal) = construct_equiv_lemma ctxt' uses_bot t

    val induction_rule =
      Proof_Context.get_thms ctxt' (fun_name ^ ".induct")

    val argnames =
      map_range (fn i => "arg" ^ subscript (string_of_int (i + 1))) (length (Term.binder_types fun_T))

(*     val g =
      Thm.cterm_of ctxt' (Logic.list_implies (assms, goal))
      |> Goal.init |> @{print}
      |> (Induct_Tacs.induct_tac ctxt' [map SOME argnames] (SOME induction_rule) 1)
      |> Seq.hd |> @{print}
      |> ALLGOALS (EqSubst.eqsubst_tac ctxt' [0] fun_nat_simps)
      |> Seq.hd |> @{print}
      |> ALLGOALS (EqSubst.eqsubst_tac ctxt' [0] fun_simps)
      |> Seq.hd |> @{print}
      |> Method.insert_tac ctxt' (wellbehaved_thms @ const_equiv_thms) 1
      |> Seq.hd |> @{print}
      |> auto_tac (ctxt' addsimps (encoder_simps @ ctr_simps))
      |> Seq.hd |> @{print}
      |> Goal.finish ctxt'  *)


    val correctness_thm =
      Goal.prove ctxt' schemvars assms goal
        (fn {context=ctxt, prems = assms, ...} =>
           print_tac ctxt "Start"
           THEN Induct_Tacs.induct_tac ctxt [map SOME argnames] (SOME induction_rule) 1
           THEN (print_tac ctxt "after induction")
           THEN ALLGOALS (solve_subgoal_tac ctxt assms)
           (*  THEN ALLGOALS (Subgoal.FOCUS_PARAMS (fn {context = ctxt, ...} =>
             solve_subgoal_tac ctxt assms 1
             (* EqSubst.eqsubst_tac ctxt [0] fun_nat_simps 1
             THEN EqSubst.eqsubst_tac ctxt [0] fun_simps 1
             THEN Method.insert_tac ctxt (assms @ wellbehaved_thms @ const_equiv_thms) 1
             THEN auto_tac (ctxt addsimps (encoder_simps @ ctr_simps)) *)
             ) ctxt )  *)
      )


    val correctness_thm_name =
      Binding.name fun_nat_name
      |> Binding.suffix_name "_equiv"

    val (_, ctxt'') =
      Local_Theory.note ((correctness_thm_name, []), [correctness_thm]) ctxt'

  in
    ctxt''
  end;

val _ =
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>function_nat_rewrite_auto\<close>
    "converts existing tail-recursive functions into nat encoded functions"
    (Parse.term >> function_nat_rewrite_auto)



end