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

fun allM (x :: xs) = bothM (x, allM xs) |> Option.map (op ::)
  | allM [] = SOME []

fun all_values_same []        = NONE
  | all_values_same [x]       = SOME x
  | all_values_same (x :: xs) = if SOME x = all_values_same xs
                                then SOME x else NONE

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

val read_defaults = {proper = false, strict = false}
val read_const' = Proof_Context.read_const read_defaults
val read_type_name' = Proof_Context.read_type_name read_defaults

fun sanitize_sugar_name (s: Ctr_Sugar.ctr_sugar) =
  s
  |> #T
  |> Term.dest_Type
  |> fst
  |> String.translate (fn x => if x = #"." then "_" else Char.toString x)

datatype pairing_path =
  DONE |
  FST of pairing_path |
  SND of pairing_path

fun build_unpairing i DONE = i
  | build_unpairing i (FST x) = inferT @{term fstP} $ build_unpairing i x
  | build_unpairing i (SND x) = inferT @{term sndP} $ build_unpairing i x

fun build_unpairing_from_idx t idx length =
  let fun repeat_snd 0 t = t
        | repeat_snd n t = @{term sndP} $ repeat_snd (n - 1) t
  in
    if idx = length - 1
    then repeat_snd (idx + 1) t
    else @{term fstP} $ repeat_snd (idx + 1) t
  end

val CONSTRUCTOR_OFFSET = 1

fun collect_tvars typ : (indexname * sort) list =
  case typ of Type (_, typlist) => map collect_tvars typlist |> List.concat
            | TVar (indexname, sort) => [(indexname, sort)]
            | TFree (_, _) => error "Found a TFree while collecting TVars."

fun collect_all_tvars t =
  Term.fold_term_types (K (Term.fold_atyps (fn t => fn a => collect_tvars t @ a))) t []

fun constructor_to_int (ctr, typ) ctx =
  let
    fun matches_ctr (Const (y, _)) = if y = ctr then SOME () else NONE
      | matches_ctr _ = NONE;
  in
    typ
    |> Term.body_type
    |> Term.dest_Type
    |> fst
    |> Ctr_Sugar.ctr_sugar_of ctx
    |> Option.mapPartial (#ctrs #> get_index matches_ctr)
    (*|> Option.map (fn c => fst c + CONSTRUCTOR_OFFSET) *)
    |> Option.map (fn c => fst c)
  end

fun constructor_to_number c ctx =
  constructor_to_int c ctx
  |> Option.map (HOLogic.mk_number @{typ nat})

fun build_constructor_tag c ctx =
  constructor_to_number c ctx
  |> Option.map (fn n => @{term atomic} $ n)

fun build_constructor_pairing a b =
  let fun bcs a (b :: bs) = @{term pair} $ a $ bcs b bs
        | bcs a [] = a
  in
    bcs a (if b = []
           then [@{term "atomic 0"}] \<comment> \<open>dummy (0-arity constructor)\<close>
           else b)
  end

fun invocation_factory pfx defaultT ctx f typ =
  \<comment> \<open>Build, generally speaking, a function to destructure \<open>typ\<close> and use its arguments.\<close>
  \<comment> \<open>In practice, we'll specify \<open>f\<close> to generate an encoder or decoder.\<close>
  case typ of
    Type (name, args) =>
      Term.list_comb (f (name, typ), map (invocation_factory pfx defaultT ctx f) args)
  | TVar ((name, _), _) => Free (pfx ^ name, defaultT)
  | TFree _ => error "Found TFree running an invocation factory."

fun build_encoder_invocation ctx (freetyp : typ option) : typ -> term =
  invocation_factory "enc_" (dummyT --> @{typ "pair_repr"}) ctx
    (fn (name, typ) =>
        let val sugar = Ctr_Sugar.ctr_sugar_of ctx name |> the
        in
          if freetyp = SOME typ
              \<comment> \<open>We're want an encoder for \<open>freetyp\<close>, but we're actually trying to generate\<close>
              \<comment> \<open>that encoder. We need to recurse: \<open>enc_freetyp\<close> is not a constant!\<close>
          then Free ("enc_" ^ sanitize_sugar_name sugar, dummyT)
          else
            inferT (read_const' ctx ("enc_" ^ sanitize_sugar_name sugar))
        end)

fun build_encoder_invocation_example__ ctx : typ -> term =
  invocation_factory "enc_" (dummyT --> @{typ "pair_repr"}) ctx
    (fn (name, _) =>
      let val sugar = Ctr_Sugar.ctr_sugar_of ctx name |> the
      in Const ("enc_" ^ sanitize_sugar_name sugar, dummyT)
      end)

val tfree_to_tvar_example__ =
  Term.map_atyps (fn t => case t of TFree (str, srt) => TVar ((str, 0), srt) | t => t)

fun build_encoder ctx sugar =
  if #T sugar = @{typ "nat"}
  then (HOLogic.mk_Trueprop o mk_eq_dummyT) (
          Free ("enc_" ^ sanitize_sugar_name sugar, dummyT) $ Free ("v", dummyT),
          Free ("v", @{typ "nat"})
       )
  else
    let
      val typeargs =
        #ctrs sugar
        |> map (dest_Const #> snd #> collect_tvars)
        |> List.concat
        |> distinct (uncurry equal)
        |> map (fn ((name, _), sort) =>
                Free ("enc_" ^ name, TFree (name, sort) --> @{typ "pair_repr"}))
      val cases =
        #ctrs sugar
        |> map (fn ctr =>
            let val arg_types = (Term.binder_types o Term.type_of) ctr
                val encoded_args =
                  arg_types
                  |> map (build_encoder_invocation ctx (SOME (#T sugar)))
                  |> zip (rev (map_range I (length arg_types)))
                  |> List.map (fn (i, e) => e $ Bound i)
            in
              build_constructor_tag (dest_Const ctr) ctx
              |> the
              |> (fn tag => (build_constructor_pairing tag encoded_args))
              |> (fn term =>
                List.foldr (fn ((ty, i), t) => Abs ("v" ^ string_of_int i, tvar_to_tfree ty, t))
                           term
                           (zip arg_types (map_range I (length encoded_args))))
            end
          )
    in
      HOLogic.mk_Trueprop (mk_eq_dummyT (
           Term.list_comb (Free ("enc_" ^ sanitize_sugar_name sugar, dummyT),
                           typeargs @ [Free ("v", dummyT)]),
           Term.list_comb (inferT (#casex sugar),
                           cases @ [Free ("v", dummyT)])
       ))
    end

val _ =
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>datatype_nat_encode\<close>
    "creates encoder for a data type"
    (Parse.typ >> (fn typ => fn lthy =>
        let
          val typename = (fst o dest_Type) (read_type_name' lthy typ)
          val sugar = Ctr_Sugar.ctr_sugar_of lthy typename |> the
          val eqns = build_encoder lthy sugar
          val fixes = @{print}[(Binding.name ("enc_" ^ sanitize_sugar_name sugar), NONE, NoSyn)]
          val specs = [((Binding.empty_atts, eqns), [], [])]
        in lthy |> Function_Fun.add_fun fixes specs Function_Fun.fun_config
        end))

fun build_decoder_invocation ctx (freetyp : typ option) : typ -> term =
  invocation_factory "dec_" (@{typ "pair_repr"} --> dummyT) ctx
    (fn (name, typ) =>
        let val sugar = Ctr_Sugar.ctr_sugar_of ctx name |> the
        in if freetyp = SOME typ then Free ("dec_" ^ sanitize_sugar_name sugar, dummyT)
           else inferT (read_const' ctx ("dec_" ^ sanitize_sugar_name sugar))
        end)

fun build_decoder ctx sugar =
  if #T sugar = @{typ "nat"}
  then (HOLogic.mk_Trueprop o mk_eq_dummyT) (
          Free ("dec_" ^ sanitize_sugar_name sugar, dummyT)
          $ Free ("v", dummyT),
          Free ("v", @{typ "nat"})
       )
  else
    let
      val typeargs =
        #ctrs sugar
        |> map (dest_Const #> snd #> collect_tvars)
        |> List.concat
        |> distinct (uncurry equal)
        |> map (fn ((name, _), sort) =>
                Free ("dec_" ^ name, @{typ "pair_repr"} --> TFree (name, sort))
                )
      val cases =
        #ctrs sugar
        |> List.map (fn ctr =>
          let
            val arg_types = (Term.binder_types o Term.type_of) ctr
            val args_decoded =
              arg_types
              |> zip (map_range I (length arg_types))
              |> map (fn (i, e) =>
                      build_decoder_invocation ctx (SOME (#T sugar)) e
                      $ build_unpairing_from_idx (Free ("v", dummyT)) i (length arg_types))
            val condition =
              build_constructor_tag (dest_Const ctr) ctx |> the
              |> (fn tag => mk_eq_dummyT (inferT @{term "fstP"} $ Free ("v", dummyT), tag))
          in
            (condition, Term.list_comb (inferT ctr, args_decoded))
          end
          )
    in
      HOLogic.mk_Trueprop (mk_eq_dummyT (Term.list_comb
        (Free ("dec_" ^ sanitize_sugar_name sugar, dummyT), typeargs @ [Free ("v", dummyT)]),
         build_ite cases))
    end

val _ =
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>datatype_nat_decode\<close>
    "creates decoder for a datatype"
    (Parse.typ >> (fn typ => fn lthy =>
      let val typename = (fst o dest_Type) (read_type_name' lthy typ)
          val sugar = Ctr_Sugar.ctr_sugar_of lthy typename |> the
          val eqns = build_decoder lthy sugar
          val fixes = @{print} [(Binding.name ("dec_" ^ sanitize_sugar_name sugar), NONE, NoSyn)]
          val specs = [((Binding.empty_atts, eqns), [], [])]
          fun pat_completeness_auto ctxt =
            Pat_Completeness.pat_completeness_tac ctxt 1 THEN auto_tac ctxt
      in
        lthy
        |> Function.add_function fixes specs Function_Fun.fun_config pat_completeness_auto
        |> snd
      end)
    )

fun mk_wellbehaved enc dec =
  HOLogic.mk_Trueprop (
    inferT @{term "HOL.eq"}
    $ (inferT @{term "Fun.comp"} $ dec $ enc)
    $ inferT @{term "Fun.id"})


fun wellbehavedness_thm (sugar: Ctr_Sugar.ctr_sugar) int lthy =
  let
  val typeargs =
    dest_Type (#T sugar)
    |> snd
  fun typearg_terms_prefixed pfx =
    typeargs
    |> map (fn x => Free (pfx ^ (fst o fst) (dest_TVar x), dummyT))
  val encoder = read_const' lthy ("enc_" ^ sanitize_sugar_name sugar)
  val encoder_args = typearg_terms_prefixed "enc_"
  val decoder = read_const' lthy ("dec_" ^ sanitize_sugar_name sugar)
  val decoder_args = typearg_terms_prefixed "dec_"
  val _ = (@{print} encoder, @{print} decoder)
  val (encoder_instantiated, decoder_instantiated) =
          both (  Term.map_types tvar_to_tfree
                o Term.list_comb
                o (inferT *** I))
               ((inferT encoder, encoder_args),
                (inferT decoder, decoder_args))
  val _ = (@{print} encoder_instantiated, @{print} decoder_instantiated)
  in
    Specification.theorem
    true
    Thm.theoremK
    NONE
    (K I)
    (Binding.name (sanitize_sugar_name sugar ^ "_wellbehaved"), [])
    []
    [Element.Assumes [
        \<comment> \<open>For every type variable \<open>'a\<close> in the type signature, we need\<close>
        \<comment> \<open>@{term "wellbehaved enc_'a dec_'a"} as an assumption to our lemma.\<close>
        (Binding.empty_atts,
            zip encoder_args decoder_args
         |> map (fn (enc, dec) => (mk_wellbehaved enc dec, []))
        )
    ]]
    (Element.Shows [
        \<comment> \<open>Theorem results. @{term "wellbehaved enc dec"}\<close>
        (Binding.empty_atts, [(
            mk_wellbehaved encoder_instantiated decoder_instantiated, []
        )])
    ])
    int
    lthy
  end

val _ =
  Outer_Syntax.local_theory_to_proof'
    \<^command_keyword>\<open>datatype_nat_wellbehaved\<close>
    "generates proof obligations to relate encoders and decoders of a type"
    (Parse.typ >> (fn typ => fn int => fn lthy =>
        let val typename = (fst o dest_Type) (read_type_name' lthy typ)
            val sugar = Ctr_Sugar.ctr_sugar_of lthy typename |> the
        in wellbehavedness_thm sugar int lthy
        end))

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

val free_to_var_example__ =
  Term.map_aterms (fn t => case t of Free (str, typ) => Var ((str, 0), typ) | t => t)

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

fun replace_constructors ctx t =
  Term.strip_comb t
  |> (fn (hd, args) =>
    map (replace_constructors ctx) args
    |> allM
    |> Option.map (fn args' => (hd, args')))
  |> Option.map (fn (h, args') =>
    case h of
      Const nt => (
        case (build_constructor_tag nt ctx) of
          (SOME cons_nat) => (if (Term.binder_types #> length) (snd nt) = length args'
                              then build_constructor_pairing cons_nat args'
                              else error "Constructor not fully applied!")
        | NONE => \<comment> \<open>non-constructor function, just keep it for now\<close>
                     Term.list_comb (Const nt, args'))
    | _ => Term.list_comb (h, args'))

fun build_nat_condition ctx t =
  t
  |> (Thm.prop_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq #> fst)
  |> Term.args_of
  |> (map build_patmatch_term #> allM)
  |> Option.map (map extract_condition_paths)
  |> Option.map (fn x => zip (argnames (length x)) x)
  |> Option.map
      (map (fn (arg', condition_paths) =>
        map (fn (match, path) =>
          build_constructor_tag match ctx
          |> Option.map (fn tag =>
            mk_eq_dummyT (build_unpairing (Free (arg', @{typ "pair_repr"})) path, tag)))
          condition_paths))
  |> Option.mapPartial (map allM #> allM)
  |> Option.map (List.concat #> mk_conj')

fun nat_encode_term ctx t =
  let
    fun absvar ((v, idx), typ) body = (v, typ, abstract_over (Var ((v, idx), typ), body))
    val arguments_and_paths : (string * ((indexname * typ) * pairing_path)) list =
      t
      |> (Thm.prop_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq #> fst)
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
    t
    |> (Thm.prop_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq #> snd)
    |> replace_constructors ctx
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
  else if const_nat_unchanged cident then Const (cident, ctyp)
       else Const (cident ^ "_nat", dummyT)
 | change_const_to_nat _ _ x = x \<comment> \<open>return \<open>Free\<close>, \<open>Var\<close>, \<open>Bound\<close> unchanged\<close>

fun nat_encode_simp_rules ctx thms =
  let
    val argcount =
      map (Thm.prop_of #> HOLogic.dest_Trueprop)
      #> map (HOLogic.dest_eq #> fst #> Term.args_of #> List.length)
      \<comment> \<open>sanity check: all equations have the same argument count\<close>
      #> all_values_same
      #> the
    val args' =
      argcount thms
      |> argnames
      |> (map (fn n => Free (n, @{typ "pair_repr"})))
    val funcname =
      map (Thm.prop_of #> HOLogic.dest_Trueprop)
      #> map (HOLogic.dest_eq #> fst)
      #> map (Term.head_of #> Term.dest_Const #> fst)
      \<comment> \<open>sanity check: all equations have the same head\<close>
      #> all_values_same
      #> the
    val funcname' = Free (Long_Name.base_name (funcname thms) ^ "_nat", dummyT)
    val lhs' = Term.list_comb (funcname', args')
    val ite =
      thms
      |> map (fn x => bothM (build_nat_condition ctx x, nat_encode_term ctx x))
      |> allM
      |> the
      |> build_ite
      |> Term.map_aterms (change_const_to_nat (funcname thms) funcname')
  in
    (lhs', ite)
    |> HOLogic.mk_Trueprop o mk_eq_dummyT
    |> Term.map_types tvar_to_tfree
    |> singleton (Type_Infer_Context.infer_types ctx)
  end

fun function_nat_cmd f =
  (Parse.binding >> (fn bound => fn lthy =>
    let
      val name = Binding.name_of bound
      val simps = Proof_Context.get_thms lthy (name ^ ".simps")
      val eqns = nat_encode_simp_rules lthy simps
      val fixes = [(Binding.name (name ^ "_nat"), NONE, NoSyn)]
    in
      f eqns fixes lthy
    end))

val _ =
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>function_nat_rewrite\<close>
    "converts existing tail-recursive functions into nat encoded functions"
    (function_nat_cmd (fn eqns => fn fixes =>
        snd o Partial_Function.add_partial_function
                "tailrec" (@{print} fixes) ((Binding.empty, []), eqns)))

val _ =
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>function_nat_rewrite_manual\<close>
    "converts existing functions into nat encoded functions"
    (function_nat_cmd (fn eqns => fn fixes =>
        let
          fun pat_completeness_auto ctxt =
            Pat_Completeness.pat_completeness_tac ctxt 1 THEN auto_tac ctxt
        in
          snd o Function.add_function
                  fixes [((Binding.empty_atts, eqns), [], [])]
                  Function_Fun.fun_config
                  pat_completeness_auto
        end))

fun correctness_thm name (int : bool) lthy : Proof.state =
  let
    val fn_eqns : thm list = Proof_Context.get_thms lthy (name ^ ".simps")
    val (fn_head, fn_args_orig) =
      hd fn_eqns
      |> (Thm.prop_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq #> fst)
      |> Term.strip_comb
      |> dest_Const *** I
    val fn_arg_names : string list = argnames (length fn_args_orig)
    val fn_arg_types : typ list = Term.binder_types (snd fn_head)
    val fn_args : term list =
      zip fn_arg_names fn_arg_types
      |> map Free
    val fn_args_encoded : term list =
      zip (map (build_encoder_invocation lthy NONE) fn_arg_types) fn_args
      |> map (op $)
    val run_nat = read_const' lthy (name ^ "_nat")
    val run_nat_with_encoded_args = Term.list_comb (run_nat, fn_args_encoded)
    val decode_run_nat_with_encoded_args =
      build_decoder_invocation lthy NONE (Term.body_type (snd fn_head)) $ run_nat_with_encoded_args
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
    lthy
  end

val _ =
  Outer_Syntax.local_theory_to_proof'
    \<^command_keyword>\<open>function_nat_rewrite_correctness\<close>
    "converts existing functions into nat encoded functions"
    (Parse.binding >> (fn bound => fn int => fn lthy =>
        correctness_thm (Binding.name_of bound) int lthy))
end