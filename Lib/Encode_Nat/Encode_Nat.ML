(*  Title:      Encode_Nat.ML
    Author:     , TU Muenchen
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

fun f *** g = map_prod f g

val tvar_to_tfree = Term.map_type_tvar (TFree o fst *** I)

\<comment> \<open>\<open>HOLogic.mk_conj\<close> is binary, so \<open>fold\<close>s would leave a stray \<open>True\<close>.\<close>
fun mk_conj' [] = @{term "True"}
  | mk_conj' [t] = t
  | mk_conj' (t :: ts) = HOLogic.mk_conj (t, mk_conj' ts)

val read_const' = Proof_Context.read_const {proper = false, strict = false}

fun lhs_of thm = (Thm.prop_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq #> fst) thm

fun rhs_of thm = (Thm.prop_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq #> snd) thm

datatype pairing_path =
  DONE |
  FST of pairing_path |
  SND of pairing_path

fun build_unpairing t DONE = t
  | build_unpairing t (FST x) = @{term fstP} $ build_unpairing t x
  | build_unpairing t (SND x) = @{term sndP} $ build_unpairing t x

fun build_unpairing_from_idx t idx length =
  let fun repeat_snd 0 t = t
        | repeat_snd n t = @{term sndP} $ repeat_snd (n - 1) t
  in
    if idx = length - 1
    then repeat_snd (idx + 1) t
    else @{term fstP} $ repeat_snd (idx + 1) t
  end

fun build_constructor_tag ctxt (t as (_, T)) =
  let
    val f = Const t
    val sugar =
      Term.body_type T
      |> try Term.dest_Type
      |> Option.map fst
      |> Option.map (Ctr_Sugar.ctr_sugar_of ctxt)
      |> Option.join
  in
    case sugar of
      SOME {ctrs, ...} =>
        (case find_index (can (Ctr_Sugar_Util.fo_match ctxt f)) ctrs of
          ~1 => NONE
        | i => SOME (@{term atomic} $ HOLogic.mk_number @{typ nat} i))
    | NONE => NONE
  end;

fun build_constructor_pairing ts c =
  let
    fun bcs c (t :: ts) = @{term pair} $ c $ bcs t ts
      | bcs c [] = c
  in
    bcs c (if ts = [] then [@{term "atomic 0"}] else ts)
  end

fun encoder_name_of_type (Type (name, _)) = "enc_" ^ (Long_Name.base_name name)
  | encoder_name_of_type (TFree (name, _)) = "enc_" ^ (Long_Name.base_name name)
  | encoder_name_of_type (TVar _) = error "Can't build an encoder for TVar"

fun encoder_args_of_type T =
  snd (dest_Type T)
  |> map (fn T => Free (encoder_name_of_type T, T --> @{typ "pair_repr"}))
  |> (fn x => x @ [Free ("v", T)])

fun encoder_type_of_type (T as Type (_, typargs)) =
      map (fn T => T --> @{typ "pair_repr"}) typargs
      |> (fn x => x @ [T])
      ---> @{typ "pair_repr"}
  | encoder_type_of_type (T as TFree _) = T --> @{typ "pair_repr"}
  | encoder_type_of_type (TVar _) = error "Can't build an encoder for TVar"

fun encoder_free_term_of_type T = Free (encoder_name_of_type T, encoder_type_of_type T)

fun encoder_const_term_of_type ctxt (T as Type _) =
      fst (dest_Const (read_const' ctxt (encoder_name_of_type T)))
      |> (fn name => Const (name, encoder_type_of_type T))
  | encoder_const_term_of_type _ _ = error "Can't build a const encoder for TVar or TFree"

fun build_encoder_invocation ctxt freeT (T as Type (_, args)) =
  let
    val t = if freeT = SOME T
            then encoder_free_term_of_type T
            else encoder_const_term_of_type ctxt T
  in
    Term.list_comb (t, map (build_encoder_invocation ctxt freeT) args)
  end
  | build_encoder_invocation _ _ (T as TFree _) = encoder_free_term_of_type T
  | build_encoder_invocation _ _ (TVar _) = error "Can't build an encoder for TVar"

fun pull_front i xs =
  (Library.nth xs i) :: (Library.nth_drop i xs)

fun get_ctrs_idx_bot ctxt T ctrs =
let
    val T_name = Long_Name.base_name (fst (dest_Type T))
    val bot' =
      (Proof_Context.get_thms ctxt) ("bot_" ^ T_name ^ "_def")
      |> hd
      |> rhs_of
      |> try (fst o dest_Const)
  in
    if is_none bot' then 0
    else Library.find_index ((curry (op =) (the bot')) o fst o dest_Const) ctrs
  end;

fun build_encoder ctxt T ctrs casex =
  let
    val T = T |> (map_type_tfree (fn (name, _) => TFree (name, ["Orderings.order_bot"])))
    val ctrs = map (map_types (map_type_tfree (fn (name, _) => TFree (name, ["Orderings.order_bot"])))) ctrs
    val casex = map_types (map_type_tfree (fn (name, _) => TFree (name, ["Orderings.order_bot"]))) casex
    val i = get_ctrs_idx_bot ctxt T ctrs
    val ctrs = pull_front i ctrs
    val lhs = Term.list_comb (encoder_free_term_of_type T, encoder_args_of_type T)
    val cases =
      ctrs
      |> map (fn ctr_t =>
          let
            val ctr_args_Ts = (binder_types o type_of) ctr_t
            val encoded_args =
              (map (build_encoder_invocation ctxt (SOME T)) ctr_args_Ts,
               ctr_args_Ts)
              ||> (length #> (map_range Bound) #> rev)
              |> (op ~~)
              |> map (op $)
            val res =
              (rev (map_index (fn (i, T) => ("v" ^ string_of_int i, T)) ctr_args_Ts),
              build_constructor_tag ctxt (dest_Const ctr_t))
              ||> the
              ||> build_constructor_pairing encoded_args
              |->  fold (fn (s, T) => fn t => Abs (s, T, t))
            val _ =
              binder_types (type_of ctr_t)
          in
            res
          end
        )
    val rhs = if T = @{typ "nat"} then Free ("v", T)
              else Term.list_comb (casex, cases @ [Free ("v", T)])
  in
    BNF_Util.mk_Trueprop_eq (lhs, rhs)
  end

fun datatype_nat_encode_cmd T ctxt =
  let
    val T_name = fst (dest_Type (Syntax.parse_typ ctxt T))
    val sugar = Ctr_Sugar.ctr_sugar_of ctxt T_name |> the
    val T = tvar_to_tfree (#T sugar)
    val casex =
      subst_atomic_types [(body_type (type_of (#casex sugar)), @{typ "pair_repr"})] (#casex sugar)
      |> map_types tvar_to_tfree
    val ctrs = map (map_types tvar_to_tfree) (#ctrs sugar)
    val eqns = build_encoder ctxt T ctrs casex
    val fixes = [(Binding.name (encoder_name_of_type T), NONE, NoSyn)]
    val specs = [((Binding.empty_atts, eqns), [], [])]
  in Function_Fun.add_fun fixes specs Function_Fun.fun_config ctxt
  end

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>datatype_nat_encode\<close>
    "Creates encoder for a data type"
    (Parse.typ >> datatype_nat_encode_cmd)

fun decoder_name_of_type (Type (name, _)) = "dec_" ^ (Long_Name.base_name name)
  | decoder_name_of_type (TFree (name, _)) = "dec_" ^ (Long_Name.base_name name)
  | decoder_name_of_type (TVar _) = error "Can't build a decoder for TVar"

fun decoder_args_of_type T =
  snd (dest_Type T)
  |> map (fn T => Free (decoder_name_of_type T, @{typ "pair_repr"} --> T))
  |> (fn x => x @ [Free ("v", @{typ "pair_repr"})])

fun decoder_type_of_type (T as Type (_, typargs)) =
      map (curry (op -->) @{typ "pair_repr"}) typargs
      |> (fn x => x @ [@{typ "pair_repr"}])
      ---> T
  | decoder_type_of_type (T as TFree _) = @{typ "pair_repr"} --> T
  | decoder_type_of_type (TVar _) = error "Can't build a decoder for TVar"

fun decoder_free_term_of_type T = Free (decoder_name_of_type T, decoder_type_of_type T)

fun decoder_const_term_of_type ctxt (T as Type _) =
      fst (dest_Const (read_const' ctxt (decoder_name_of_type T)))
      |> (fn name => Const (name, decoder_type_of_type T))
  | decoder_const_term_of_type _ _ = error "Can't build a Const decoder for a type variable"

fun build_decoder_invocation ctxt freeT (T as Type (_, args)) =
  let
    val t = if freeT = SOME T then decoder_free_term_of_type T
            else decoder_const_term_of_type ctxt T
  in
    list_comb (t, map (build_decoder_invocation ctxt freeT) args)
  end
  | build_decoder_invocation _ _ (T as TFree _) = decoder_free_term_of_type T
  | build_decoder_invocation _ _ (TVar _) = error "Can't build a decoder for TVar"

fun build_decoder ctxt T ctrs =
  let
    val T = T |> map_type_tfree (fn (name, _) => TFree (name, ["Orderings.order_bot"]))
    val ctrs = map (map_types (map_type_tfree (fn (name, _) => TFree (name, ["Orderings.order_bot"])))) ctrs
    val i = get_ctrs_idx_bot ctxt T ctrs
    val lhs = Term.list_comb (decoder_free_term_of_type T, decoder_args_of_type T)
    val free_var = Free ("v", @{typ "pair_repr"})
    val (conditions, cases) =
      ctrs
      |> map (fn ctr_t =>
        let
          val ctr_args_Ts = (Term.binder_types o Term.type_of) ctr_t
          val args_decoded =
            ctr_args_Ts
            |> curry (op ~~) (map_range I (length ctr_args_Ts))
            |> map (fn (i, e) =>
                    build_decoder_invocation ctxt (SOME T) e
                    $ build_unpairing_from_idx free_var i (length ctr_args_Ts))
          val condition =
            build_constructor_tag ctxt (dest_Const ctr_t)
            |> the
            |> curry HOLogic.mk_eq (@{term "fstP"} $ free_var)
        in
          (condition, Term.list_comb (ctr_t, args_decoded))
        end)
     |> split_list
     ||> pull_front i
    val rhs = if T = @{typ "nat"} then free_var
              else Ctr_Sugar_Util.mk_IfN T conditions cases
  in
    BNF_Util.mk_Trueprop_eq (lhs, rhs)
  end

fun datatype_nat_decode_cmd T ctxt =
  let
    val T_name = fst (dest_Type (Syntax.parse_typ ctxt T))
    val sugar = Ctr_Sugar.ctr_sugar_of ctxt T_name |> the
    val T = tvar_to_tfree (#T sugar)
    val ctrs = map (map_types tvar_to_tfree) (#ctrs sugar)
    val eqns = build_decoder ctxt T ctrs
    val fixes = [(Binding.name (decoder_name_of_type T), NONE, NoSyn)]
    val specs = [((Binding.empty_atts, eqns), [], [])]
    fun pat_completeness_auto ctxt =
            Pat_Completeness.pat_completeness_tac ctxt 1 THEN auto_tac ctxt
  in
    snd (Function.add_function fixes specs Function_Fun.fun_config pat_completeness_auto ctxt)
  end

val _ =
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>datatype_nat_decode\<close>
    "creates decoder for a datatype"
    (Parse.typ >> datatype_nat_decode_cmd)

fun mk_wellbehaved_thm_name (Type (name, _)) =
    "encoding_" ^ Long_Name.base_name name ^ "_wellbehaved"
  | mk_wellbehaved_thm_name _ = error "Can't generate wellbehaved theorem name for type variables"

fun mk_wellbehaved_thm enc dec =
  let
    val T = body_type (fastype_of dec)
  in
    BNF_Util.mk_Trueprop_eq(HOLogic.mk_comp (dec, enc), HOLogic.id_const T)
  end;

fun wellbehavedness_thm T int ctxt =
  let
    val T = map_type_tfree (fn (name, _) => TFree (name, ["Orderings.order_bot"])) T
    val (encoder_args, decoder_args) =
      apply2 (fst o split_last) (encoder_args_of_type T, decoder_args_of_type T)
    val encoder = Term.list_comb (encoder_const_term_of_type ctxt T, encoder_args)
    val decoder = Term.list_comb (decoder_const_term_of_type ctxt T, decoder_args)
    val assms = map (uncurry mk_wellbehaved_thm) (encoder_args ~~ decoder_args)
    val goal = mk_wellbehaved_thm encoder decoder
  in
    Specification.theorem
      true
      Thm.theoremK
      NONE
      (K I)
      (Binding.name (mk_wellbehaved_thm_name T), [])
      []
      [Element.Assumes [(Binding.empty_atts, map (rpair []) assms)]]
      (Element.Shows [(Binding.empty_atts, [(goal, [])])])
      int
      ctxt
  end

fun datatype_nat_wellbehaved_cmd T int ctxt =
  let
    val {T, ...} = the (Ctr_Sugar.ctr_sugar_of ctxt (fst (dest_Type (Syntax.parse_typ ctxt T))))
  in
    wellbehavedness_thm (tvar_to_tfree T) int ctxt
  end

val _ =
  Outer_Syntax.local_theory_to_proof'
    \<^command_keyword>\<open>datatype_nat_wellbehaved\<close>
    "generates proof obligations to relate encoders and decoders of a type"
    (Parse.typ >> datatype_nat_wellbehaved_cmd)

datatype patmatch_term =
  CONSTRUCTOR of (string * typ) * (patmatch_term list) |
  VARIABLE of (indexname * typ)

fun build_patmatch_term (Var v) = VARIABLE v
  | build_patmatch_term t =
      Term.strip_comb t
      |>> Term.dest_Const
      ||> map build_patmatch_term
      |> CONSTRUCTOR

fun retag_list [] = []
  | retag_list [x] = x
  | retag_list (x :: xs) =
  (map (apsnd FST) x) @ (retag_list (map (map (apsnd SND)) xs))

fun extract_condition_paths (CONSTRUCTOR (c, args)) =
      retag_list ([(c, DONE)] ::
        (case args of [] => [[]] \<comment> \<open>dummy arg for 0-arity constructor\<close>
                    | args => map extract_condition_paths args))
  | extract_condition_paths (VARIABLE _) = []

fun extract_variable_paths (CONSTRUCTOR (_, args)) =
      retag_list ([] :: map extract_variable_paths args)
  | extract_variable_paths (VARIABLE n) = [(n, DONE)]

val subscript =
  String.explode
  #> map (str #> prefix ("\\" ^ "<^sub>"))
  #> String.concat

val argnames = map_range (fn i => "arg" ^ subscript (string_of_int (i+1)))

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

fun build_nat_condition ctxt thm =
  let
    fun mk_condition (arg, x) =
      map (fn (match, path) =>
            the (build_constructor_tag ctxt match)
            |> (pair (build_unpairing arg path) #> HOLogic.mk_eq)) x
    val args_t = Term.args_of (lhs_of thm)
    val new_args_t = map (fn s => Free (s, @{typ "pair_repr"})) (argnames (length args_t))
    val condition_paths = map (extract_condition_paths o build_patmatch_term) args_t
  in
    map mk_condition (new_args_t ~~ condition_paths)
    |> List.concat
    |> mk_conj'
  end;

fun nat_encode_term ctxt thm =
  let
    fun absvar ((v, idx), typ) body = (v, typ, abstract_over (Var ((v, idx), typ), body))
    val arguments_and_paths =
      thm
      |> lhs_of
      |> map_types tvar_to_tfree
      |> Term.args_of
      |> map build_patmatch_term
      |> map extract_variable_paths
      |> (fn x =>
        argnames (length x) ~~ x
        |> map (fn (arg, paths_from_this_arg) => map (pair arg) paths_from_this_arg))
      |> List.concat
    val wrappers =
      arguments_and_paths
      |> map (fn (argname_new, ((var_indexname, vartyp_old), varpath)) => fn term =>
          let
            val (var_name, _, abs_body) = absvar (var_indexname, vartyp_old) term
          in
            (Const (\<^const_name>\<open>HOL.Let\<close>,
                    @{typ "pair_repr \<Rightarrow> (pair_repr \<Rightarrow> pair_repr) \<Rightarrow> pair_repr"}))
             $ build_unpairing (Free (argname_new, @{typ "pair_repr"})) varpath
             $ Abs (var_name, @{typ "pair_repr"}, abs_body)
          end)
  in
    thm
    |> rhs_of
    |> map_types tvar_to_tfree
    |> replace_constructors ctxt
    |> (fn t => fold (fn wf => fn t' => wf t') wrappers t)
  end

fun const_nat_unchanged s =
  if exists (fn x => String.isPrefix x s)
       ["HOL.", \<comment> \<open>\<open>If\<close>, \<open>Let\<close>, and more\<close>
        "Nat.", "Num.", "Groups." \<comment> \<open>Relating to (natural) numbers\<close>
       ]
  then true
  else exists (fn x => x = s)
        (List.map (fst o dest_Const) [@{term fstP}, @{term sndP}, @{term atomic}, @{term pair}])

fun mk_encoded_typ (Const (_, T)) =
  ((map (K @{typ "pair_repr"}) (binder_types T)) ---> @{typ "pair_repr"})
  | mk_encoded_typ _ = error "Can only make encoder of Const"

fun change_const_to_nat parent parent_nat (t as Const (cident, ctyp)) =
  if cident = parent then parent_nat
  else if cident = "Orderings.bot_class.bot" then Const (cident, @{typ "pair_repr"})
  else if cident = "HOL.If" then Const (cident, @{typ "bool \<Rightarrow> pair_repr \<Rightarrow> pair_repr \<Rightarrow> pair_repr"})
  else if cident = "HOL.eq" then Const (cident, @{typ "pair_repr \<Rightarrow> pair_repr \<Rightarrow> bool"})
  else if const_nat_unchanged cident then Const (cident, ctyp)
  else Const (cident ^ "_nat", mk_encoded_typ t)
 | change_const_to_nat _ _ x = x


fun function_nat_rewrite s ctxt =
  let
    val t = Syntax.read_term ctxt s;
    val (fun_name, _) = Term.dest_Const t;
    val newfun_name = (Long_Name.base_name fun_name) ^ "_nat";
    val arg_Ts = (binder_types (fastype_of t));
    val arg_ts =
      argnames (List.length arg_Ts)
      |> map (fn argname => Free (argname, @{typ "pair_repr"}));
    val newfun_T = mk_encoded_typ t;
    val newfun_t = Free (newfun_name, newfun_T);
    val lhs = Term.list_comb (newfun_t, arg_ts);
    val ite =
      Proof_Context.get_thms ctxt (fun_name ^ ".simps")
      |> (fn thms => (map (build_nat_condition ctxt) thms, map (nat_encode_term ctxt) thms))
      |-> Ctr_Sugar_Util.mk_IfN (Term.body_type newfun_T)
      |> Term.map_aterms (change_const_to_nat fun_name newfun_t)
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

val _ =
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>test2\<close>
    "Test2"
    (Parse.term >> function_nat_rewrite)

fun mk_dec_bot_eq_bot T =
  let
    val lhs = decoder_free_term_of_type T $ (Const (\<^const_name>\<open>bot\<close>, @{typ "pair_repr"}))
    val rhs = Const (\<^const_name>\<open>bot\<close>, T)
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
      |> map (fn T =>
                [mk_wellbehaved_thm (encoder_free_term_of_type T) (decoder_free_term_of_type T),
                 mk_dec_bot_eq_bot T])
      |> flat
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

val _ =
  Outer_Syntax.local_theory_to_proof'
    \<^command_keyword>\<open>test\<close>
    "Test"
    (Parse.term >> function_nat_rewrite_correctness_cmd)

val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>function_nat_rewrite_correctness\<close>
    "converts existing functions into nat encoded functions"
    (Parse.term >> function_nat_rewrite_correctness_cmd)
end