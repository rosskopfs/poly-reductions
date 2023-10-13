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

fun f *** g = map_prod f g

val tvar_to_tfree = Term.map_type_tvar (TFree o fst *** I)

\<comment> \<open>\<open>HOLogic.mk_conj\<close> is binary, so \<open>fold\<close>s would leave a stray \<open>True\<close>.\<close>
fun mk_conj' [] = @{term "True"}
  | mk_conj' [t] = t
  | mk_conj' (t :: ts) = HOLogic.mk_conj (t, mk_conj' ts)

val read_const' = Proof_Context.read_const {proper = false, strict = false}

fun lhs_of_term t = (HOLogic.dest_Trueprop #> HOLogic.dest_eq #> fst) t

fun rhs_of_term t = (HOLogic.dest_Trueprop #> HOLogic.dest_eq #> snd) t

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
  end;

fun pull_front i xs =
  (Library.nth xs i) :: (Library.nth_drop i xs);

fun get_ctrs_idx_bot ctxt T ctrs =
let
    val T_base_name = Long_Name.base_name (fst (dest_Type T))
    val T_name = (fst (dest_Type T))
    val cond =
      fastype_of #> try dest_Type #> Option.map fst #> (curry (op =) (SOME T_name))
    (* TODO: find more efficient method. Can't use just the base name with find theorem as there
      might be several datatypes with the same base name *)
    val bot' =
      Find_Theorems.find_theorems ctxt NONE NONE false [(true, Find_Theorems.Name ("bot_" ^ T_base_name ^ "_def"))]
      |> snd
      |> map (snd #> Thm.prop_of #> rhs_of_term)
      |> Library.get_first (fn t => if cond t then SOME t else NONE)
      |> try (Option.map (fst o dest_Const))
      |> Option.join
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
      |> Option.map #ctrs
    val i = Option.getOpt (Option.map (get_ctrs_idx_bot ctxt (Term.body_type T)) ctrs, 0)
    val ctrs = Option.map (pull_front i) ctrs
  in
    case Option.map (find_index (can (Ctr_Sugar_Util.fo_match ctxt (Const t)))) ctrs of
        SOME (~1) => NONE
      | SOME i => SOME (@{term atomic} $ HOLogic.mk_number @{typ nat} i)
      | NONE => NONE
  end;

fun build_constructor_pairing ts c =
  let
    fun bcs c (t :: ts) = @{term pair} $ c $ bcs t ts
      | bcs c [] = c
  in
    bcs c (if ts = [] then [@{term "atomic 0"}] else ts)
  end

fun encoder_name_of_type ctxt (Type (name, _)) =
      Name_Space.extern ctxt (Proof_Context.type_space ctxt) name
      |> Long_Name.base_name
      |> prefix "enc_"
  | encoder_name_of_type _ (TFree (name, _)) = prefix "enc_" name
  | encoder_name_of_type _ (TVar ((name, _), _)) = prefix "enc_" name

fun encoder_args_of_type ctxt T =
  snd (dest_Type T)
  |> map (fn T => Free (encoder_name_of_type ctxt T, T --> @{typ "pair_repr"}))
  |> (fn x => x @ [Free ("v", T)])

fun encoder_type_of_type (T as Type (_, typargs)) =
      map (fn T => T --> @{typ "pair_repr"}) typargs
      |> (fn x => x @ [T])
      ---> @{typ "pair_repr"}
  | encoder_type_of_type (T as TFree _) = T --> @{typ "pair_repr"}
  | encoder_type_of_type (T as TVar _) = T --> @{typ "pair_repr"}

fun encoder_free_term_of_type ctxt T = Free (encoder_name_of_type ctxt T, encoder_type_of_type T)

fun encoder_const_term_of_type ctxt (T as Type _) =
      fst (dest_Const (read_const' ctxt (encoder_name_of_type ctxt T)))
      |> (fn name => Const (name, encoder_type_of_type T))
  | encoder_const_term_of_type _ _ = error "Can't build a const encoder for TVar or TFree"

fun encoder_term_of_type ctxt (T as Type _) = encoder_const_term_of_type ctxt T
  | encoder_term_of_type ctxt (T as TFree _) = encoder_free_term_of_type ctxt T
  | encoder_term_of_type ctxt (T as TVar ((_, i), s)) = Var ((encoder_name_of_type ctxt T, i), encoder_type_of_type T)

fun build_encoder_invocation ctxt freeT (T as Type (_, args)) =
  let
    val t = if freeT = SOME T
            then encoder_free_term_of_type ctxt T
            else encoder_const_term_of_type ctxt T
  in
    Term.list_comb (t, map (build_encoder_invocation ctxt freeT) args)
  end
  | build_encoder_invocation ctxt _ (T as TFree _) = encoder_free_term_of_type ctxt T
  | build_encoder_invocation _ _ (TVar _) = error "Can't build an encoder for TVar"

fun build_encoder ctxt T ctrs casex =
  let
    val T = T |> (map_type_tfree (fn (name, _) => TFree (name, ["Orderings.order_bot"])))
    val ctrs = map (map_types (map_type_tfree (fn (name, _) => TFree (name, ["Orderings.order_bot"])))) ctrs
    val casex = map_types (map_type_tfree (fn (name, _) => TFree (name, ["Orderings.order_bot"]))) casex
    val lhs = Term.list_comb (encoder_free_term_of_type ctxt T, encoder_args_of_type ctxt T)
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
    val fixes = [(Binding.name (encoder_name_of_type ctxt T), NONE, NoSyn)]
    val specs = [((Binding.empty_atts, eqns), [], [])]

  in Function_Fun.add_fun fixes specs Function_Fun.fun_config ctxt
  end

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>datatype_nat_encode\<close>
    "Creates encoder for a data type"
    (Parse.typ >> datatype_nat_encode_cmd)

fun decoder_name_of_type ctxt (Type (name, _)) =
      Name_Space.extern ctxt (Proof_Context.type_space ctxt) name
      |> Long_Name.base_name
      |> prefix "dec_"
  | decoder_name_of_type _ (TFree (name, _)) =
      prefix "dec_" name
  | decoder_name_of_type _ (TVar _) = error "Can't build a decoder for TVar"

fun decoder_args_of_type ctxt T =
  snd (dest_Type T)
  |> map (fn T => Free (decoder_name_of_type ctxt T, @{typ "pair_repr"} --> T))
  |> (fn x => x @ [Free ("v", @{typ "pair_repr"})])

fun decoder_type_of_type (T as Type (_, typargs)) =
      map (curry (op -->) @{typ "pair_repr"}) typargs
      |> (fn x => x @ [@{typ "pair_repr"}])
      ---> T
  | decoder_type_of_type (T as TFree _) = @{typ "pair_repr"} --> T
  | decoder_type_of_type (TVar _) = error "Can't build a decoder for TVar"

fun decoder_free_term_of_type ctxt T = Free (decoder_name_of_type ctxt T, decoder_type_of_type T)

fun decoder_const_term_of_type ctxt (T as Type _) =
      fst (dest_Const (read_const' ctxt (decoder_name_of_type ctxt T)))
      |> (fn name => Const (name, decoder_type_of_type T))
  | decoder_const_term_of_type _ _ = error "Can't build a Const decoder for a type variable"

fun build_decoder_invocation ctxt freeT (T as Type (_, args)) =
  let
    val t = if freeT = SOME T then decoder_free_term_of_type ctxt T
            else decoder_const_term_of_type ctxt T
  in
    list_comb (t, map (build_decoder_invocation ctxt freeT) args)
  end
  | build_decoder_invocation ctxt _ (T as TFree _) = decoder_free_term_of_type ctxt T
  | build_decoder_invocation _ _ (TVar _) = error "Can't build a decoder for TVar"

fun build_decoder ctxt T ctrs =
  let
    val T = T |> map_type_tfree (fn (name, _) => TFree (name, ["Orderings.order_bot"]))
    val ctrs = map (map_types (map_type_tfree (fn (name, _) => TFree (name, ["Orderings.order_bot"])))) ctrs
    val lhs = Term.list_comb (decoder_free_term_of_type ctxt T, decoder_args_of_type ctxt T)
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
    val fixes = [(Binding.name (decoder_name_of_type ctxt T), NONE, NoSyn)]
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

fun mk_wellbehaved_thm_name ctxt (Type (name, _)) =
      Name_Space.extern ctxt (Proof_Context.type_space ctxt) name
      |> Long_Name.base_name
      |> prefix "encoding_"
      |> suffix "_wellbehaved"
  | mk_wellbehaved_thm_name _ _ = error "Can't generate wellbehaved theorem name for type variables"

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
      apply2 (fst o split_last) (encoder_args_of_type ctxt T, decoder_args_of_type ctxt T)
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
      (Binding.name (mk_wellbehaved_thm_name ctxt T), [])
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

(* TODO: Also replace with pairing_tree without retag? *)
fun extract_condition_paths (CONSTRUCTOR (c, args)) =
      retag_list ([(c, DONE)] ::
        (case args of [] => [[]] \<comment> \<open>dummy arg for 0-arity constructor\<close>
                    | args => map extract_condition_paths args))
  | extract_condition_paths (VARIABLE _) = []

datatype pairing_tree =
  LEAF |
  VAR of (indexname * typ) |
  NODE of (pairing_tree * pairing_tree)

fun mk_pairing_tree [] = LEAF
  | mk_pairing_tree [(VARIABLE n)] = VAR n
  | mk_pairing_tree ((VARIABLE n) :: xs) = NODE (VAR n, mk_pairing_tree xs)
  | mk_pairing_tree ((CONSTRUCTOR (_, args)) :: xs) =
      NODE (NODE (LEAF, mk_pairing_tree args), mk_pairing_tree xs)

fun mk_path t =
  let
    fun mk_path p (VAR n) = [(n, p)]
      | mk_path _ LEAF = []
      | mk_path p (NODE (l, r)) = (mk_path (FST p) l) @ (mk_path (SND p) r)
  in
    mk_path DONE t
  end;

fun mk_variable_paths (VARIABLE n) = [(n, DONE)]
  | mk_variable_paths (CONSTRUCTOR (_, args)) = mk_path (NODE (LEAF, mk_pairing_tree args))

val subscript = implode o map (prefix "\<^sub>") o Symbol.explode

fun argname i = "arg" ^ subscript (string_of_int (i + 1))

val argnames = map_range argname

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

fun build_nat_condition ctxt t =
  let
    fun mk_condition (arg, x) =
      map (fn (match, path) =>
            if match = ("Groups.zero_class.zero", @{typ "nat"})
            then HOLogic.mk_eq (arg, HOLogic.mk_number @{typ nat} 0)
            else
              the (build_constructor_tag ctxt match)
              |> (pair (build_unpairing arg path) #> HOLogic.mk_eq)) x
    val args_t = Term.args_of (lhs_of_term t)
    val new_args_t = map (fn s => Free (s, @{typ "pair_repr"})) (argnames (length args_t))
    val condition_paths =
      map build_patmatch_term args_t
      |> map extract_condition_paths
  in
    (new_args_t ~~ condition_paths)
    |> map mk_condition
    |> List.concat
    |> mk_conj'
  end;

fun change_if ctxt (t as ((c as Const ("HOL.If", _)) $ cond $ thn $ els)) =
  if fst (Term.dest_Const (Term.head_of cond)) = "HOL.eq" then t
  else c $ (decoder_const_term_of_type ctxt @{typ "bool"} $ cond) $ thn $ els
  | change_if ctxt (t $ u) = change_if ctxt t $ u
  | change_if _ x = x



fun nat_encode_term ctxt t =
  let
    fun absvar ((v, idx), typ) body = (v, typ, abstract_over (Var ((v, idx), typ), body))
    val arguments_and_paths =
      t
      |> lhs_of_term
      |> map_types tvar_to_tfree
      |> Term.args_of |> @{print}
      |> map build_patmatch_term
      |> map mk_variable_paths
      |> (fn x =>
        argnames (length x) ~~ x
        |> map (fn (arg, paths_from_this_arg) => map (pair arg) paths_from_this_arg))
      |> List.concat |> @{print}
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
    t
    |> rhs_of_term
    |> map_types tvar_to_tfree
    |> change_if ctxt
    |> replace_constructors ctxt
    |> (fn t => fold (fn wf => fn t' => wf t') wrappers t)
  end


fun nat_encode_term ctxt t =
  let
    val arguments_and_paths =
      lhs_of_term t
      |> map_types tvar_to_tfree
      |> Term.args_of |> @{print}
      |> map build_patmatch_term
      |> map mk_variable_paths
      |> flat o map_index (fn (i, x) => map (pair (argname i)) x)
    val wrappers =
      let
        fun f (fun_arg_name, (pattern_var_t as ((pattern_var_name, _), _), pattern_var_path)) term =
          (Const (\<^const_name>\<open>HOL.Let\<close>, @{typ "pair_repr \<Rightarrow> (pair_repr \<Rightarrow> pair_repr) \<Rightarrow> pair_repr"}))
           $ build_unpairing (Free (fun_arg_name, @{typ "pair_repr"})) pattern_var_path
           $ Term.abs (pattern_var_name, @{typ "pair_repr"}) (abstract_over (Var pattern_var_t, term))
      in
        map f arguments_and_paths
      end
    val foo =
      rhs_of_term t
      |> map_types tvar_to_tfree
      |> change_if ctxt
      |> replace_constructors ctxt |> @{print}
    fun f (fun_arg_name, (pattern_var_t as ((pattern_var_name, _), _), pattern_var_path)) (acc, term) =
          (Var pattern_var_t :: acc,
           (Const (\<^const_name>\<open>HOL.Let\<close>, @{typ "pair_repr \<Rightarrow> (pair_repr \<Rightarrow> pair_repr) \<Rightarrow> pair_repr"}))
           $ @{print} (build_unpairing (Free (fun_arg_name, @{typ "pair_repr"})) pattern_var_path)
           $ @{print} (Term.abs (pattern_var_name, @{typ "pair_repr"}) (abstract_over (Var pattern_var_t, term))))
    val ret =
    t
    |> rhs_of_term
    |> map_types tvar_to_tfree
    |> change_if ctxt
    |> replace_constructors ctxt
    |> fold (fn f => fn x => f x) wrappers |> @{print}
    val ret' =
      lhs_of_term t
      |> map_types tvar_to_tfree
      |> Term.args_of |> @{print}
      |> map build_patmatch_term |> @{print}
      |> map mk_variable_paths |> @{print}
      |> flat o map_index (fn (i, x) => map (pair (argname i)) x)
      |> map f
      |> (fn x => fold (fn f => fn x => f x) x ([], foo)) |>> @{print}
  in
    ret
  end


fun const_nat_unchanged s =
  if exists (fn x => String.isPrefix x s)
       ["HOL.", \<comment> \<open>\<open>If\<close>, \<open>Let\<close>, and more\<close>
        "Nat.", "Num.", "Groups.", \<comment> \<open>Relating to (natural) numbers\<close>
        "enc"
       ]
  then true
  else if exists (fn x => String.isPrefix x (Long_Name.base_name s)) \<comment> \<open>Very hacky\<close>
       [
        "dec"
       ]
  then true
  else exists (fn x => x = s)
        (List.map (fst o dest_Const) [@{term fstP}, @{term sndP}, @{term atomic}, @{term pair}])

fun mk_encoded_typ (Const (_, T)) =
  ((map (K @{typ "pair_repr"}) (binder_types T)) ---> @{typ "pair_repr"})
  | mk_encoded_typ _ = error "Can only make encoder of Const"

fun change_const_to_nat (t as Const (c, _)) =
  if c = "Orderings.bot_class.bot" then Const (c, @{typ "pair_repr"})
  else if c = "HOL.If" then Const (c, @{typ "bool \<Rightarrow> pair_repr \<Rightarrow> pair_repr \<Rightarrow> pair_repr"})
  else if c = "HOL.eq" then Const (c, @{typ "pair_repr \<Rightarrow> pair_repr \<Rightarrow> bool"})
  else if const_nat_unchanged c then t
  else Const (c ^ "_nat", mk_encoded_typ t)
 | change_const_to_nat x = x;

fun const_to_free (c, T) t =
  Term.subst_atomic [(Const (c, T), Free (Long_Name.base_name c, T))] t;

fun replace_suc t =
  let
    fun minus_one v =
          Const ("Groups.minus_class.minus", @{typ "nat \<Rightarrow> nat \<Rightarrow> nat"})
            $ v $ Const ("Groups.one_class.one", @{typ "nat"})
    fun substs_for_suc (t as (Const ("Nat.Suc", _) $ v)) = [(t, v), (v, minus_one v)]
      | substs_for_suc _ = []
    val substs =
      Term.args_of (lhs_of_term t)
      |> map substs_for_suc
      |> Library.flat
    val res =
      t
      |> Term.subst_free substs
  in
    res
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
      |> Term.map_aterms change_const_to_nat
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

val _ =
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>test2\<close>
    "Test2"
    (Parse.term >> function_nat_rewrite)

fun mk_dec_bot_eq_bot ctxt T =
  let
    val lhs = decoder_free_term_of_type ctxt T $ (Const (\<^const_name>\<open>bot\<close>, @{typ "pair_repr"}))
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
                [mk_wellbehaved_thm (encoder_free_term_of_type ctxt T) (decoder_free_term_of_type ctxt T),
                 mk_dec_bot_eq_bot ctxt T])
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
      |> map (fn T =>
                [mk_wellbehaved_thm (encoder_free_term_of_type ctxt T) (decoder_free_term_of_type ctxt T),
                 mk_dec_bot_eq_bot ctxt T])
      |> flat
    val argnames =
      map_range (fn i => "arg" ^ subscript (string_of_int (i + 1))) (length (Term.binder_types fn_T))
    val schemvars =
      fold_atyps (insert (op =)) fn_T []
      |> map (fn T => [encoder_name_of_type ctxt T, decoder_name_of_type ctxt T])
      |> flat
      |> (curry op @) argnames
    val goal =
      BNF_Util.mk_Trueprop_eq (lhs, rhs) |> @{print}
    val encoder_simps =
        Library.distinct (op =) ((body_type fn_T)::(binder_types fn_T)) |> @{print}
        |> map (suffix ".simps" o encoder_name_of_type ctxt) |> @{print}
        |> map (Proof_Context.get_thms ctxt) |> @{print}
        |> flat
    val other_simps =
        ["fstP.simps", "sndP.simps", "atomic.simps", "pair.simps"]
        |> map (Proof_Context.get_thms ctxt)
        |> flat
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
    fun f acc (Const ("HOL.If", _) $ cond $ u) = insert (op =) cond (f acc u)
      | f acc (t $ u) = union (op =) (f acc t) (f acc u)
      | f acc (Abs (_, _, t)) = f acc t
      | f acc _ = acc
    val g =
      Thm.cterm_of ctxt goal |> @{print}
      |> Goal.init
      |> (Induct_Tacs.induct_tac ctxt [map SOME argnames] (SOME induction_rule) 1
      THEN ALLGOALS (EqSubst.eqsubst_tac ctxt [0] fn_nat_simps)
      THEN ALLGOALS (EqSubst.eqsubst_tac ctxt [0] fn_simps))
      |> Seq.hd |> @{print}
      |> (ALLGOALS (simp_tac (ctxt addsimps encoder_simps))) |> Seq.hd
      |> (ALLGOALS (simp_tac (ctxt addsimps other_simps)))
      |> Seq.hd |> @{print}
    val a =
      Goal.prove ctxt schemvars assms goal
      (fn {context=ctxt, prems, ...} =>
        bla)
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

fun function_nat_rewrite_correctness_cmd3 fn_str int ctxt =
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
      |> map (fn T =>
                [mk_wellbehaved_thm (encoder_free_term_of_type ctxt T) (decoder_free_term_of_type ctxt T),
                 mk_dec_bot_eq_bot ctxt T])
      |> flat
    val argnames =
      map_range (fn i => "arg" ^ subscript (string_of_int (i + 1))) (length (Term.binder_types fn_T))
    val schemvars =
      fold_atyps (insert (op =)) fn_T []
      |> map (fn T => [encoder_name_of_type ctxt T, decoder_name_of_type ctxt T])
      |> flat
      |> (curry op @) argnames
    val goal =
      BNF_Util.mk_Trueprop_eq (lhs, rhs) |> @{print}
    val encoder_simps =
        Library.distinct (op =) ((body_type fn_T)::(binder_types fn_T)) |> @{print}
        |> map (suffix ".simps" o encoder_name_of_type ctxt) |> @{print}
        |> map (Proof_Context.get_thms ctxt) |> @{print}
        |> flat
    val other_simps =
        ["fstP.simps", "sndP.simps", "atomic.simps", "pair.simps"]
        |> map (Proof_Context.get_thms ctxt)
        |> flat
    val other_other_simps =
        ["atomic.simps", "Nat.One_nat_def", "HOL.simp_thms", "HOL.if_True", "HOL.if_False"]
        |> map (Proof_Context.get_thms ctxt)
        |> flat
    val induction_rule =
      Proof_Context.get_thms ctxt (fn_name ^ ".induct")
    val fn_nat_simps =
      Proof_Context.get_thms ctxt (fn_name ^ "_nat.simps")
    val fn_simps =
      Proof_Context.get_thms ctxt (fn_name ^ ".simps")
    (*val bla =
      Induct_Tacs.induct_tac ctxt [map SOME argnames] (SOME induction_rule) 1
      THEN ALLGOALS (EqSubst.eqsubst_tac ctxt [0] fn_nat_simps)
      THEN ALLGOALS (EqSubst.eqsubst_tac ctxt [0] fn_simps)
      THEN ALLGOALS (full_simp_tac (ctxt addsimps encoder_simps))
      THEN ALLGOALS (full_simp_tac (ctxt addsimps other_simps))*)
    fun f acc (Const ("HOL.If", _) $ cond $ u) = insert (op =) cond (f acc u)
      | f acc (t $ u) = union (op =) (f acc t) (f acc u)
      | f acc (Abs (_, _, t)) = f acc t
      | f acc _ = acc
    val g =
      Thm.cterm_of ctxt goal |> @{print}
      |> Goal.init
      |> (Induct_Tacs.induct_tac ctxt [map SOME argnames] (SOME induction_rule) 1
      THEN ALLGOALS ((EqSubst.eqsubst_tac ctxt [0] fn_nat_simps)
                      THEN' (EqSubst.eqsubst_tac ctxt [0] fn_simps)))
      |> Seq.hd |> @{print}
      |> (ALLGOALS (Subgoal.FOCUS_PARAMS (fn {context = ctxt, ...} =>
          (let
            fun foo thm =
            let
              val if_subst_tac =
                thm
                |> Thm.prems_of
                |> map get_conditions_of_ifs
                |> flat
                |> map (fn t => [BNF_Util.mk_Trueprop_eq (t, @{term "True"}),
                                 BNF_Util.mk_Trueprop_eq (t, @{term "False"})])
                |> flat
                |> map (fn t =>
                    t
                    |> Thm.cterm_of ctxt
                    |> Goal.init
                    |> (full_simp_tac (ctxt addsimps encoder_simps addsimps other_simps) 1)
                    |> Seq.hd
                    |> try (Goal.finish ctxt))
                |> map Option.valOf o filter Option.isSome
                |> EqSubst.eqsubst_tac ctxt [0]
              val if_subst_tac' = if_subst_tac 1
            in
              if_subst_tac' thm
            end
          in
            foo
          end)
          )
        ctxt))
      |> Seq.hd |> @{print}
      |> ALLGOALS (EqSubst.eqsubst_tac ctxt [0] @{thms HOL.if_False HOL.if_True})
      |> Seq.hd |> @{print}
      |> (HEADGOAL (Subgoal.FOCUS_PARAMS (fn {context = ctxt, ...} =>
          (let
            fun foo thm =
            let
              fun f acc (Const ("HOL.Let", _) $ t $ u) = insert (op =) t (f acc u)
                | f acc (t $ u) = union (op =) (f acc t) (f acc u)
                | f acc (Abs (_, _, t)) = f acc t
                | f acc _ = acc
              val if_subst_tac =
                thm
                |> Thm.prems_of  |> @{print}
                |> map (f []) |> @{print}
                |> flat |> @{print}
              val _ : conv = undefined
            in
              Seq.single thm
            end
          in
            foo
          end)
          )
        ctxt))
      |> Seq.hd |> @{print}
    (*val a =
      Goal.prove ctxt schemvars assms goal
      (fn {context=ctxt, prems, ...} =>
        bla)*)
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
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>test\<close>
    "Test"
    (Parse.term >> function_nat_rewrite_correctness_cmd2)

val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>function_nat_rewrite_correctness\<close>
    "converts existing functions into nat encoded functions"
    (Parse.term >> function_nat_rewrite_correctness_cmd3)



fun function_nat_rewrite_auto s ctxt =
  let
    val normalize_type =
      map_aterms (fn Var ((s, _), T) => Free (s, T) | x => x)
      #> map_types tvar_to_tfree
      #> map_types (map_type_tfree (fn (name, _) => TFree (name, [@{class "Orderings.order_bot"}])))

    val t = Syntax.read_term ctxt s |> normalize_type
    val (fun_name, _) = Term.dest_Const t
    val fun_T = fastype_of t
    val fun_nat_name = (Long_Name.base_name fun_name) ^ "_nat"
    val fun_arg_Ts = (binder_types (fastype_of t))
    val fun_arg_ts =
      map_index (fn (i, T) => Free ("arg" ^ subscript (string_of_int (i + 1)), T)) fun_arg_Ts
    val fun_nat_arg_ts =
      argnames (List.length fun_arg_Ts)
      |> map (fn argname => Free (argname, @{typ "pair_repr"}))
    val fun_nat_T = mk_encoded_typ t
    val fun_nat_t = Free (fun_nat_name, fun_nat_T)
    val fun_simps =  Proof_Context.get_thms ctxt (fun_name ^ ".simps") |> @{print}
    val fun_nat_lhs = Term.list_comb (fun_nat_t, fun_nat_arg_ts)

    fun build_patmatch_term (Var v) = VARIABLE v
      | build_patmatch_term (Free (s,T)) = VARIABLE ((s, 0), T)
      | build_patmatch_term t =
          Term.strip_comb t
          |>> Term.dest_Const
          ||> map build_patmatch_term
          |> CONSTRUCTOR
    val fun_patmached_arg_ts =
      map Thm.prop_of fun_simps
      |> map lhs_of_term
      |> flat o map (snd o Term.strip_comb)
    fun mk_encoder_invocation ctxt (T as Type (_, typargs)) =
          Term.list_comb (encoder_const_term_of_type ctxt T, map (mk_encoder_invocation ctxt) typargs)
      | mk_encoder_invocation ctxt (T as TFree _) = encoder_free_term_of_type ctxt T
      | mk_encoder_invocation ctxt T = encoder_term_of_type ctxt T

    fun encode_term ctxt t =
      Term.list_comb (mk_encoder_invocation ctxt (type_of t), [t])


    (* (recursively) collect arguments of functions in term *)
    fun collect_args t =
      let
        (* add t itself if whole term is a constructor *)
        val term_if_ctr =
          t |> @{print}
          |> fst o strip_comb |> @{print}
          |> try dest_Const |> @{print}
          |> Option.map (build_constructor_tag ctxt) (* probably not the most performant way *)
          |> Option.join
          |> Option.map (K [t])
          |> (fn x => Option.getOpt (x, []))
        fun collect t =
          let
            val args = Term.args_of t
          in
            map collect args
            |> (fn x => fold (union (op =)) x args)
          end
      in
        collect t @ term_if_ctr
      end

    fun collect_encoders ctxt (T as Type (_, Ts)) =
        fold (insert (op =)) (flat (map (collect_encoders ctxt) Ts)) [encoder_name_of_type ctxt T]
      | collect_encoders _ _ = []

    val encoder_simps =
      fun_patmached_arg_ts (* we should probably go through all types in the whole function *)
      |> filter (not o is_Var)
      |> map (collect_encoders ctxt o type_of)
      |> (fn x => fold (union (op =)) x [])
      |> map (suffix ".simps")
      |> flat o map (Proof_Context.get_thms ctxt) |> @{print}

    val ctr_simps =
      map Thm.prop_of fun_simps
      |> map rhs_of_term |> @{print}
      |> map normalize_type
      |> map collect_args
      |> (fn x => fold (union (op =)) x [])
      |> filter (fn t => size_of_term t > 1) (* don't need simplification for a term itself *)
      |> (fn ts => (map (replace_constructors ctxt) ts, map (encode_term ctxt) ts))
      |> (fn (lhs, rhs) =>
             ((lhs, rhs),
              map (fn t => fold_aterms (fn Free (s, _) => insert (op =) s | _ => I) t []) rhs))
      |>> apfst (map (map_aterms (fn t as Free _ => encode_term ctxt t | x => x)))
      |>> op ~~
      |>> map BNF_Util.mk_Trueprop_eq
      |> op ~~
      |> map (fn (t, vars) =>
          Goal.prove ctxt vars [] t
            (fn {context=ctxt, prems, ...} =>
              asm_full_simp_tac (ctxt addsimps encoder_simps) 1
             )) |> @{print}

    val let_simps_thms =
      fun_patmached_arg_ts
      |> filter (not o is_Var) (* don't need simplification for a variable itself *)
      |> flat o map (fn t =>
        build_patmatch_term t
        |> map (apfst Var) o mk_variable_paths
        |> map (pair (encode_term ctxt t)))
      (* now like: [(enc_list enc_'a (x # xs), (x, <pairing path to x>)), ...] *)
      |> map (fn (enc_t, (var, p)) =>
          (BNF_Util.mk_Trueprop_eq (build_unpairing enc_t p, encode_term ctxt var)
           |> normalize_type,
           fold_aterms (fn Var ((s,_),_) => insert (op =) s | _ => I) enc_t []))
      (* now like: [(sndP (sndP (enc_list enc_'a (x # xs))) = enc_list enc_'a xs,
                     <list of free vars in this term>, ...] *)
      |> map (fn (t, vars) =>
          Goal.prove ctxt vars [] t
            (fn {context=ctxt, prems, ...} =>
               asm_full_simp_tac (ctxt addsimps encoder_simps) 1
             )) |> @{print}

    val fun_nat_rhs =
      map Thm.prop_of fun_simps
      |> map replace_suc (* morally replace "f (Suc n) = g n" by "f n = g (n - 1)" *)
      |> (fn ts => (map (build_nat_condition ctxt) ts, map (nat_encode_term ctxt) ts))
      |-> Ctr_Sugar_Util.mk_IfN (Term.body_type fun_nat_T) |> @{print}
      |> Term.map_aterms change_const_to_nat |> @{print}
      |> const_to_free (fun_name ^ "_nat", fun_nat_T)

    val (_, fun_nat_lthy) =
      Partial_Function.add_partial_function
        "tailrec"
        [(Binding.name fun_nat_name, NONE, NoSyn)]
        ((Binding.empty, []), BNF_Util.mk_Trueprop_eq (fun_nat_lhs, fun_nat_rhs))
        ctxt

    val ctxt' : Proof.context = fun_nat_lthy

    (* start constructing and proving correctness lemma *)
    val correctness_rhs =
      Term.list_comb (t, fun_arg_ts)
      |> (curry op $) (build_encoder_invocation ctxt' NONE (Term.body_type fun_T)) |> @{print}
    val correctness_lhs =
      map (fn t => (build_encoder_invocation ctxt' NONE (fastype_of t)) $ t) fun_arg_ts
      |> Term.list_comb o (pair (read_const' ctxt' (fun_name ^ "_nat"))) |> @{print}

    val assms =
      fold_atyps (insert (op =)) fun_T []
      |> flat o map (fn T =>
                [mk_wellbehaved_thm (encoder_free_term_of_type ctxt' T) (decoder_free_term_of_type ctxt' T),
                 mk_dec_bot_eq_bot ctxt' T])
      |> @{print}
    val argnames =
      map_range (fn i => "arg" ^ subscript (string_of_int (i + 1))) (length (Term.binder_types fun_T))

    val schemvars =
      fold_atyps (insert (op =)) fun_T []
      |> map (fn T => [encoder_name_of_type ctxt' T, decoder_name_of_type ctxt' T])
      |> flat
      |> (curry op @) argnames |> @{print}
    val goal =
      BNF_Util.mk_Trueprop_eq (correctness_lhs, correctness_rhs)

    val induction_rule =
      Proof_Context.get_thms ctxt' (fun_name ^ ".induct")
    val fun_nat_simps =
      Proof_Context.get_thms ctxt' (fun_name ^ "_nat.simps") |> @{print}

    fun collect_const_invocations t =
      let
        val (fn_t, args) = strip_comb t
        val v =
          dest_Const fn_t
          |> (fn (fn_name, fn_T) => (fn_name, build_constructor_tag ctxt (fn_name, fn_T)))
          ||> Option.map (K false)
          ||> (fn x => Option.getOpt (x, true))
          |> (fn (fn_name, b) => if fn_name <> fun_name andalso b then [(fn_name, args)] else [])
          handle TERM _ => []
      in
        map collect_const_invocations args
        |> (fn x => fold (union (op =)) x v)
      end

    fun collect_const_invocations2 t =
      let
        val (fn_t, args) = strip_comb t
        val v =
          dest_Const fn_t
          |> (fn (fn_name, fn_T) => (fn_name, build_constructor_tag ctxt (fn_name, fn_T)))
          ||> Option.map (K false)
          ||> (fn x => Option.getOpt (x, true))
          |> (fn (fn_name, b) => if fn_name <> fun_name andalso b then [t] else [])
          handle TERM _ => []
      in
        map collect_const_invocations2 args
        |> (fn x => fold (union (op =)) x v)
      end

    fun get_args thm =
      Thm.prop_of thm |> @{print}
      |> lhs_of_term
      |> snd o Term.strip_comb
      |> map (fn t => (Term.fastype_of t, t))


    val equiv_thms_inst_vars =
      map Thm.prop_of fun_simps
      |> map rhs_of_term |> @{print}
      
      |> map collect_const_invocations2
      |> (fn x => fold (union (op =)) x []) |> @{print}
      |> map (fn t => 
        let
        val ((s,_), args) =
            strip_comb t
            |>> dest_Const
        val add_sort_order_bot =
          Term.map_type_tvar (fn (n, s) => TVar (n, [@{class "Orderings.order_bot"}]))
        
        val reg_invoc =
          (read_const' ctxt' s)
          |> map_types add_sort_order_bot

        val inv_fun_arg_Ts =
          binder_types (fastype_of (read_const' ctxt' s))
          |> map add_sort_order_bot |> @{print}

        val inv_fun_arg_ts =
          inv_fun_arg_Ts
          |> map_index (fn (i, T) => Var ((argname i, 0), T)) |> @{print}
          
        val a =
          Term.list_comb (reg_invoc, inv_fun_arg_ts) |> @{print}
          |> Thm.cterm_of ctxt' |> @{print}

        val b =
          map_types add_sort_order_bot t
          |> Thm.cterm_of ctxt' |> @{print}
        val substs = Thm.first_order_match (a, b) |> @{print}

        val equiv_thm = hd (Proof_Context.get_thms ctxt (s ^ "_nat_equiv")) |> @{print}
        in
          Thm.instantiate substs equiv_thm
        end
        )
      |> @{print}


    val bla = 
      map Thm.prop_of fun_simps
      |> map rhs_of_term
      |> map normalize_type
      |> map collect_const_invocations
      |> (fn x => fold (union (op =)) x [])
      |> map (apfst (suffix "_nat.simps")) |> @{print}
      |> map (apfst (hd o Proof_Context.get_thms ctxt'))
      |> map (apfst (snd o Term.strip_comb o lhs_of_term o Thm.prop_of))
      |> map (fn (args, inst_args) => map dest_Var args ~~ map (Thm.cterm_of ctxt') inst_args)
      |> map Vars.make |> @{print}

    val const_invocations =
      map Thm.prop_of fun_simps
      |> map rhs_of_term
      |> map normalize_type
      |> map collect_const_invocations
      |> (fn x => fold (union (op =)) x [])
      |> map (apfst (suffix "_nat_equiv")) |> @{print}
      |> map (apfst (hd o Proof_Context.get_thms ctxt')) (* should always be only one thm *)
      |> map (fn (thm, args) => (thm, get_args thm, map (fn t => (Term.fastype_of t, t)) args))
      |> map (fn (thm, orig_args, new_args) => (thm, map snd orig_args, map snd new_args))
      |> map (fn (thm, a, b) => (thm, map dest_Var a, map (Thm.cterm_of ctxt') b))
      |> map (fn (thm, a, b) => (thm, (a ~~ b)))
      |> map (fn (thm, l) => ((TVars.empty, Vars.make l), thm))
      |> map (uncurry Thm.instantiate) |> @{print}
    
    fun if_exp_simp_tac ctxt thm =
      let
        val if_simps =
          Thm.prems_of thm
          |> flat o map get_conditions_of_ifs
          |> flat o map (fn t => [BNF_Util.mk_Trueprop_eq (t, @{term "True"}),
                           BNF_Util.mk_Trueprop_eq (t, @{term "False"})])
          |> map_filter (try (fn t =>
               Goal.prove ctxt [] [] t (fn {context=ctxt, prems, ...} =>
                full_simp_tac (ctxt addsimps encoder_simps) 1)))
      in
        EqSubst.eqsubst_tac ctxt [0] if_simps 1 thm
      end

    fun solve_subgoal_tac ctxt =
      print_tac ctxt "before if"
      THEN (if_exp_simp_tac ctxt)
      THEN (print_tac ctxt "after if")
      THEN (EqSubst.eqsubst_tac ctxt [0] @{thms HOL.if_False HOL.if_True} 1)
      THEN (print_tac ctxt "after sub if")
      THEN (simp_tac (clear_simpset ctxt addsimps let_simps_thms addsimps @{thms HOL.Let_def}) 1)
      THEN (print_tac ctxt "after let simps and let def")
      THEN TRY (simp_tac (clear_simpset ctxt addsimps ctr_simps) 1)
      THEN (print_tac ctxt "after constructor simps")
    

    val g =
      Thm.cterm_of ctxt' goal |> @{print}
      |> Goal.init |> @{print}
      |> (Induct_Tacs.induct_tac ctxt' [map SOME argnames] (SOME induction_rule) 1
          THEN ALLGOALS ((EqSubst.eqsubst_tac ctxt' [0] fun_simps)
                          THEN' (EqSubst.eqsubst_tac ctxt' [0] fun_nat_simps))) |> @{print}
      |> Seq.hd |> @{print}
      |> (ALLGOALS (Subgoal.FOCUS_PARAMS (fn {context = ctxt, ...} =>
          solve_subgoal_tac ctxt
          )
        ctxt'))
      |> Seq.hd |> @{print}
      |> Goal.finish ctxt' |> @{print}

    val correctness_thm =
      Goal.prove ctxt' schemvars assms goal
        (fn {context=ctxt, prems, ...} =>
           Induct_Tacs.induct_tac ctxt [map SOME argnames] (SOME induction_rule) 1
           THEN ALLGOALS ((EqSubst.eqsubst_tac ctxt [0] fun_simps)
                           THEN' (EqSubst.eqsubst_tac ctxt [0] fun_nat_simps))
           THEN ALLGOALS (Subgoal.FOCUS_PARAMS (fn {context = ctxt, ...} =>
             solve_subgoal_tac ctxt
             ) ctxt ))
      |> @{print}


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