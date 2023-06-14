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

fun f *** g = fn (a, b) => (f a, g b)
fun both f = f *** f

fun bothM (SOME a, SOME b) = SOME (a, b)
  | bothM _ = NONE

fun allM (x :: xs) = Option.map (op ::) (bothM (x, allM xs))
  | allM [] = SOME []

fun zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys
  | zip _         _         = []

fun inferT (Const (x, _)) = Const (x, dummyT)
  | inferT _ = error "Refusing to infer type of a non-const."

\<comment> \<open>We can't always use \<open>HOLogic.mk_eq\<close>: it tries to run some basic type inference.\<close>
fun mk_eq_dummyT (l, r) = Const ("HOL.eq", dummyT) $ l $ r

val tvar_to_tfree = Term.map_type_tvar (TFree o fst *** I)

fun build_ite [] = inferT @{term "undefined"}
  | build_ite ((acond, aval) :: bs) = inferT @{term "If"} $ acond $ aval $ build_ite bs

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

fun collect_tvars (Type (_, typlist)) = map collect_tvars typlist |> List.concat
  | collect_tvars (TVar (indexname, sort)) = [(indexname, sort)]
  | collect_tvars (TFree _) = error "Found a TFree while collecting TVars."

fun collect_all_tvars t =
  Term.fold_term_types (K (Term.fold_atyps (fn t => fn a => collect_tvars t @ a))) t []

fun constructor_to_int ctxt (ctr_str, T) =
  let
    fun matches_ctr (Const (y, _)) = if y = ctr_str then SOME () else NONE
      | matches_ctr _ = NONE;
  in
    (case Term.body_type T of
      Type (name, _) =>
      name
      |> Ctr_Sugar.ctr_sugar_of ctxt
      |> Option.mapPartial (#ctrs #> get_index matches_ctr)
      |> Option.map (fn c => fst c)
    | _ => NONE)

  end

fun constructor_to_number ctxt c =
  Option.map (HOLogic.mk_number @{typ nat}) (constructor_to_int ctxt c)

fun build_constructor_tag c ctxt =
  Option.map (curry (op $) @{term atomic}) (constructor_to_number ctxt c)

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
    val t = if freeT = SOME T then encoder_free_term_of_type T
            else encoder_const_term_of_type ctxt T
  in
    list_comb (t, map (build_encoder_invocation ctxt freeT) args)
  end
  | build_encoder_invocation _ _ (T as TFree _) = encoder_free_term_of_type T
  | build_encoder_invocation _ _ (TVar _) = error "Can't build an encoder for TVar"

fun build_encoder ctxt T ctrs casex =
  let
    val lhs = Term.list_comb (encoder_free_term_of_type T, encoder_args_of_type T)
    val cases =
      ctrs
      |> map (fn ctr_t =>
          let
            val ctr_args_Ts = (binder_types o type_of) ctr_t
            val encoded_args =
              `(map (build_encoder_invocation ctxt (SOME T))) ctr_args_Ts
              ||> (length #> (map_range Bound) #> rev)
              |-> zip |> map (op $)
          in
            build_constructor_tag (dest_Const ctr_t) ctxt |> the
            |> build_constructor_pairing encoded_args
            |> (fn term =>
              List.foldr (fn ((T, i), t) => Abs ("v" ^ string_of_int i, T, t))
                         term
                         (zip ctr_args_Ts (map_range I (length encoded_args))))
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
      map (fn T => @{typ "pair_repr"} --> T) typargs
      |> (fn x => x @ [@{typ "pair_repr"}])
      ---> T
  | decoder_type_of_type (T as TFree _) = @{typ "pair_repr"} --> T
  | decoder_type_of_type (TVar _) = error "Can't build a decoder for TVar"

fun decoder_free_term_of_type T = Free (decoder_name_of_type T, decoder_type_of_type T)

fun decoder_const_term_of_type ctxt (T as Type _) =
      fst (dest_Const (read_const' ctxt (decoder_name_of_type T)))
      |> (fn name => Const (name, decoder_type_of_type T))
  | decoder_const_term_of_type _ _ = error "Can't build a decoder for TVar"

fun decoder_term_of_type (T as Type (_, typargs)) =
      map (curry (op -->) @{typ "pair_repr"}) typargs
      |> (fn x => x @ [@{typ "pair_repr"}])
      |> (fn Ts => Free (decoder_name_of_type T, Ts ---> T))
  | decoder_term_of_type T = Free (decoder_name_of_type T, @{typ "pair_repr"} --> T)

fun build_decoder_invocation ctxt freeT (T as Type (_, args)) =
  let
    val t = if freeT = SOME T then decoder_free_term_of_type T
            else decoder_const_term_of_type ctxt T
  in
    list_comb (t, map (build_decoder_invocation ctxt freeT) args)
  end
  | build_decoder_invocation _ _ (T as TFree _) = decoder_term_of_type T
  | build_decoder_invocation _ _ (TVar _) = error "Can't build a decoder for TVar"

fun build_decoder ctxt T ctrs =
  let
    val lhs = Term.list_comb (decoder_term_of_type T, decoder_args_of_type T)
    val free_var = Free ("v", @{typ "pair_repr"})
    val cases =
      ctrs
      |> map (fn ctr_t =>
        let
          val ctr_args_Ts = (Term.binder_types o Term.type_of) ctr_t
          val args_decoded =
            ctr_args_Ts
            |> zip (map_range I (length ctr_args_Ts))
            |> map (fn (i, e) =>
                    build_decoder_invocation ctxt (SOME T) e
                    $ build_unpairing_from_idx free_var i (length ctr_args_Ts))
          val condition =
            build_constructor_tag (dest_Const ctr_t) ctxt |> the
            |> curry HOLogic.mk_eq (@{term "fstP"} $ free_var)
        in
          (condition, Term.list_comb (ctr_t, args_decoded))
        end)
    val rhs = if T = @{typ "nat"} then free_var else build_ite cases
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

fun mk_wellbehaved enc dec =
  BNF_Util.mk_Trueprop_eq(HOLogic.mk_comp (dec, enc), HOLogic.id_const (body_type (fastype_of dec)))

fun wellbehavedness_thm T int ctxt =
  let
    val (encoder_args, decoder_args) =
    (encoder_args_of_type T, decoder_args_of_type T)
    |> apply2 (`(fn x => length x - 1))
    |> apply2 (uncurry take)
    val encoder = Term.list_comb (encoder_const_term_of_type ctxt T, encoder_args)
    val decoder = Term.list_comb (decoder_const_term_of_type ctxt T, decoder_args)
  in
    Specification.theorem
    true
    Thm.theoremK
    NONE
    (K I)
    (Binding.name (mk_wellbehaved_thm_name T), [])
    []
    [Element.Assumes [
        (Binding.empty_atts,
            zip encoder_args decoder_args
         |> map (fn (enc, dec) => (mk_wellbehaved enc dec, []))
        )
    ]]
    (Element.Shows [
        (Binding.empty_atts, [(
            mk_wellbehaved encoder decoder, []
        )])
    ])
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

fun build_patmatch_term (Var v) = SOME (VARIABLE v)
  | build_patmatch_term t =
      Term.strip_comb t
      |> Term.dest_Const *** I
      |> (fn (t', args) =>
            allM (map build_patmatch_term args)
            |> Option.map (fn args' => CONSTRUCTOR (t', args')))

fun retag_list [] = []
  | retag_list [x] = x
  | retag_list (x :: xs) =
    (x |> map (I *** FST)) @ (xs |> map (map (I *** SND)) |> retag_list)

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
  | replace_constructors ctxt t =
    t
    |> Term.strip_comb
    |> (fn (hd, args) =>
        map (replace_constructors ctxt) args
        |> allM
        |> Option.map (fn args' => (hd, args')))
    |> Option.map (fn (h, args') =>
       (case h of
         Const (n, t') =>
            (case (build_constructor_tag (n, t') ctxt) of
              SOME cons_nat => (if (Term.binder_types #> length) t' = length args'
                                then build_constructor_pairing args' cons_nat
                                else error "Constructor not fully applied!")
            | NONE => \<comment> \<open>non-constructor function, just keep it for now\<close>
              let val _ = ()
              in
                Term.list_comb (Const (n, t'), args')
              end)
       | _ => Term.list_comb (h, args')));

fun build_nat_condition ctxt thm =
  thm
  |> lhs_of
  |> Term.args_of
  |> (map build_patmatch_term #> allM)
  |> Option.map (map extract_condition_paths)
  |> Option.map (fn x => zip (argnames (length x)) x)
  |> Option.map
      (map (fn (arg', condition_paths) =>
        map (fn (match, path) =>
          build_constructor_tag match ctxt
          |> Option.map (fn tag =>
            HOLogic.mk_eq (build_unpairing (Free (arg', @{typ "pair_repr"})) path, tag)))
          condition_paths))
  |> Option.mapPartial (map allM #> allM)
  |> Option.map (List.concat #> mk_conj')

fun nat_encode_term ctxt thm =
  let
    fun absvar ((v, idx), typ) body = (v, typ, abstract_over (Var ((v, idx), typ), body))
    val arguments_and_paths : (string * ((indexname * typ) * pairing_path)) list =
      thm
      |> lhs_of
      |> Term.args_of
      |> map build_patmatch_term
      |> allM
      |> the
      |> map extract_variable_paths
      |> (fn x =>
        zip (argnames (length x)) x
        |> map (fn (arg, paths_from_this_arg) => map (pair arg) paths_from_this_arg))
      |> List.concat
    val wrappers =
      \<comment> \<open>A list of functions that’ll each wrap our result with a \<^term>\<open>Let\<close>,\<close>
      \<comment> \<open>reusing the name of a source-argument to hold the “unwrapped” value\<close>
      \<comment> \<open>from the \<^typ>\<open>nat\<close> argument it is encoded in.\<close>
      arguments_and_paths
      |> map (fn (argname_new,
        ((var_indexname, vartyp_old), varpath)) => fn term =>
          let
            val (var_name, _, abs_body) = absvar (var_indexname, vartyp_old) term
          in  \<comment> \<open>RHS within the \<^term>\<open>Let\<close>:\<close>
            inferT @{term "HOL.Let"}
                   $ build_unpairing (Free (argname_new, @{typ "pair_repr"})) varpath
                   $ Abs (var_name, dummyT, abs_body)
          end)
  in
    thm
    |> rhs_of
    |> replace_constructors ctxt
    |> Option.map (fn t => fold (fn wf => fn t' => wf t') wrappers t)
  end

fun const_nat_unchanged s =
  if exists (fn x => String.isPrefix x s)
       ["HOL.", \<comment> \<open>\<open>If\<close>, \<open>Let\<close>, and more\<close>
        "Nat.", "Num.", "Groups." \<comment> \<open>Relating to (natural) numbers\<close>
       ]
  then true
  else exists (fn x => x = s)
        (List.map (fst o dest_Const) [@{term fstP}, @{term sndP}, @{term atomic}, @{term pair}])

fun change_const_to_nat parent parent_nat (Const (cident, ctyp)) =
  if cident = parent then parent_nat
  else if cident = "Orderings.bot_class.bot" then Const (cident, @{typ "pair_repr"})
  else if const_nat_unchanged cident then Const (cident, ctyp)
       else Const (cident ^ "_nat", dummyT)
 | change_const_to_nat _ _ x = x \<comment> \<open>return \<open>Free\<close>, \<open>Var\<close>, \<open>Bound\<close> unchanged\<close>

fun function_nat_rewrite s ctxt =
  let
    val t = Syntax.read_term ctxt s;
    val (fun_name, _) = dest_Const t;
    val newfun_name = (Long_Name.base_name fun_name) ^ "_nat";
    val arg_Ts = (binder_types (fastype_of t));
    val arg_ts =
      List.length arg_Ts
      |> argnames
      |> (map (fn n => Free (n, @{typ "pair_repr"})));
    val newfun_T = ((map (K @{typ "pair_repr"}) arg_Ts) ---> @{typ "pair_repr"});
    val newfun_t = Free (newfun_name, newfun_T);
    val lhs = Term.list_comb (newfun_t, arg_ts);
    val ite =
      Proof_Context.get_thms ctxt (fun_name ^ ".simps")
      |> map (fn x => bothM (build_nat_condition ctxt x, nat_encode_term ctxt x))
      |> allM
      |> the |> @{print}
      |> build_ite |> @{print}
      |> Term.map_aterms (change_const_to_nat fun_name newfun_t) |> @{print};
    val (_, newfun_lthy) =
      Partial_Function.add_partial_function
        "tailrec"
        [(Binding.name newfun_name, NONE, NoSyn)]
        ((Binding.empty, []), BNF_Util.mk_Trueprop_eq (lhs, ite))
        ctxt;
  in
    newfun_lthy
  end

val _ =
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>function_nat_rewrite\<close>
    "converts existing tail-recursive functions into nat encoded functions"
    ((Parse.term ) >> function_nat_rewrite)


fun correctness_thm name (int : bool) ctxt : Proof.state =
  let
    val fn_eqns : thm list = Proof_Context.get_thms ctxt (name ^ ".simps")
    val (fn_head, fn_args_orig) =
      hd fn_eqns
      |> lhs_of
      |> Term.strip_comb
      |> dest_Const *** I
    val fn_arg_names : string list = argnames (length fn_args_orig)
    val fn_arg_types : typ list = Term.binder_types (snd fn_head)
    val fn_args : term list =
      zip fn_arg_names fn_arg_types
      |> map Free
    val fn_args_encoded : term list =
      zip (map (build_encoder_invocation ctxt NONE) fn_arg_types) fn_args
      |> map (op $)
    val run_nat = read_const' ctxt (name ^ "_nat")
    val run_nat_with_encoded_args = Term.list_comb (run_nat, fn_args_encoded)
    val decode_run_nat_with_encoded_args =
      build_decoder_invocation ctxt NONE (Term.body_type (snd fn_head)) $ run_nat_with_encoded_args
    val used_type_var_names : string list =
      fn_eqns
      |> map (Thm.prop_of #> HOLogic.dest_Trueprop #> collect_all_tvars)
      |> List.concat
      |> distinct (uncurry equal)
      |> List.map (fst o fst) \<comment> \<open>Get the name of a \<open>TVar\<close> description\<close>
  in
    Specification.theorem
    true
    Thm.theoremK
    NONE
    (K I)
    (Binding.name (name ^ "_nat_equiv"), [])
    []
    [Element.Assumes [
        \<comment> \<open>for every free type 'a in the function signature: @{term "wellbehaved enc_'a dec_'a"}.\<close>
        (Binding.empty_atts, List.map (fn tvn => (
              mk_wellbehaved (Free ("enc_" ^ tvn, dummyT))
                                                (Free ("dec_" ^ tvn, dummyT))
              , []))
              used_type_var_names)]
    ]
    (Element.Shows [
        \<comment> \<open>Theorem results. @{term "DECODER (fn_nat ENCODED_ARGS) = fn ARGS"}\<close>
        (Binding.empty_atts, [
              ((HOLogic.mk_Trueprop o mk_eq_dummyT
                o both (Term.map_types tvar_to_tfree))
                  (decode_run_nat_with_encoded_args,
                   (Term.list_comb (Const fn_head, fn_args)))
              , [])])
    ])
    int
    ctxt
  end

val _ =
  Outer_Syntax.local_theory_to_proof'
    \<^command_keyword>\<open>function_nat_rewrite_correctness\<close>
    "converts existing functions into nat encoded functions"
    (Parse.binding >> (fn bound => fn int => fn ctxt =>
        correctness_thm (Binding.name_of bound) int ctxt))
end