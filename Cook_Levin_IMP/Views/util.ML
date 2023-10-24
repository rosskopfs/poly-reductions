signature VIEW_UTIL =
sig
  (* general *)
  val flip : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  val nth_replace : int -> 'a -> 'a list -> 'a list
  val find_first_index : ('a -> bool) -> 'a list -> (int * 'a) option
  (*returns false if function throws an exception*)
  val try_bool : ('a -> bool) -> 'a -> bool
  (*turns option into a sequence; calls given function if option is NONE*)
  val seq_of_opt : (unit -> unit) -> 'a option -> 'a Seq.seq

  exception EXTRACT_NONE of unit -> string
  val extract_opt : (unit -> string) -> 'a option -> 'a

  (* terms *)
  val strip_imp : term -> term list * term
  val strip_cimp : cterm -> cterm list * cterm

  val unprotect : cterm -> cterm

  (* HOL-specific *)
  val dest_Trueprop : term -> term
  val cdest_Trueprop : cterm -> cterm
  val dest_eq : term -> term * term
  val cdest_eq : cterm -> cterm * cterm

  (* conversions *)
  val move_prem_to_front_conv : int -> conv
  val move_prems_to_front_conv : int list -> conv

  (* tactic combinators*)
  val HEADGOAL : (int -> 'a) -> 'a

  val TRY' : ('a -> tactic) -> 'a -> tactic

  val EVERY_ARG : ('a -> tactic) -> 'a list -> tactic
  val EVERY_ARG' : ('a -> 'b -> tactic) -> 'a list -> 'b -> tactic

  val FOCUS_PARAMS' : (Subgoal.focus -> int -> tactic) -> Proof.context -> int -> tactic
  val FOCUS_PARAMS_CTXT : (Proof.context -> tactic) -> Proof.context -> int -> tactic
  val FOCUS_PARAMS_CTXT' : (Proof.context -> int -> tactic) -> Proof.context -> int -> tactic
  val FOCUS_PARAMS_FIXED' : (Subgoal.focus -> int -> tactic) -> Proof.context -> int -> tactic
  val FOCUS_PREMS' : (Subgoal.focus -> int -> tactic) -> Proof.context -> int -> tactic
  val FOCUS' : (Subgoal.focus -> int -> tactic) -> Proof.context -> int -> tactic
  val SUBPROOF' : (Subgoal.focus -> int -> tactic) -> Proof.context -> int -> tactic

  val CSUBGOAL_DATA : (cterm -> 'a) -> ('a -> int -> tactic) -> int -> tactic
  val CSUBGOAL_PREMS_CONCL : (cterm list * cterm -> 'a) -> ('a -> int -> tactic) -> int -> tactic
  val SUBGOAL_DATA : (term -> 'a) -> ('a -> int -> tactic) -> int -> tactic
  val SUBGOAL_PREMS_CONCL : (term list * term -> 'a) -> ('a -> int -> tactic) -> int -> tactic

  (* tactics *)
  val insert_tac : thm -> int -> tactic
  (*thin_tac n i deletes nth premise of the ith subgoal*)
  val thin_tac : int -> int -> tactic
  val thin_tacs : int list -> int -> tactic

  (*solve subgoal by assumption, preferring premise n*)
  val nth_assume_tac : int -> Proof.context -> int -> tactic

  val resolve_all_tac : Proof.context -> thm list -> int -> tactic

  val subst_first_tac : Proof.context -> thm -> int -> tactic
  val subst_first_asm_tac : Proof.context -> thm -> int -> tactic

  (*protect premises starting from the given index in the specified subgoal*)
  val protect_tac : int -> Proof.context -> int -> tactic
  (*unprotect the subgoal*)
  val unprotect_tac : int -> tactic
  (*protect premises starting from the given index in the specified subgoal,
    then apply tactic, then unprotect*)
  val protected_tac : int -> (int -> tactic) -> Proof.context -> int -> tactic

  (*focus on the specified subgoal, introducing only the specified list of premises
    as theorems in the focus*)
  val focus_prems_tac : int list -> (Subgoal.focus -> int -> tactic) ->
    Proof.context -> int -> tactic
  (*calls focus_prems_tac tac and then deletes all focused premises*)
  val focus_delete_prems_tac : int list -> (Subgoal.focus -> int -> tactic) ->
    Proof.context -> int -> tactic

  (*apply tactic to the specified goal (given as a cterm)*)
  val apply_tac : (int -> tactic) -> int -> cterm -> thm Seq.seq

  (* simplifier *)
  val set_simps : Proof.context -> thm list -> Proof.context

end

structure View_Util : VIEW_UTIL =
struct

(* general *)
fun flip f x y = f y x
fun nth_replace n x = nth_map n (K x)

fun find_first_index p = get_index (Option.filter p)

fun try_bool f = try f #> (Option.getOpt o rpair false)

fun seq_of_opt _ (SOME x) = Seq.single x
  | seq_of_opt f_none NONE = (f_none (); Seq.empty)

exception EXTRACT_NONE of unit -> string
fun extract_opt error_msg opt =
  if is_none opt
  then raise EXTRACT_NONE error_msg
  else the opt

(* terms *)
fun strip_imp t =
  (let
    val (prem, t) = Logic.dest_implies t
    val (prems, concl) = strip_imp t
  in (prem :: prems, concl) end)
  handle TERM _ => ([], t)

fun strip_cimp ct =
  (let
    val (cprem, ct) = Thm.dest_implies ct
    val (cprems, cconcl) = strip_cimp ct
  in (cprem :: cprems, cconcl) end)
  handle TERM _ => ([], ct)

val unprotect = Thm.dest_arg

(* HOL-specific *)
val dest_Trueprop = HOLogic.dest_Trueprop
val cdest_Trueprop = Thm.dest_arg

val dest_eq = HOLogic.dest_eq
val cdest_eq = Thm.dest_binop

(* conversions *)
fun move_prem_to_front_conv 0 = Conv.all_conv
  | move_prem_to_front_conv i = Conv.implies_concl_conv (move_prem_to_front_conv (i - 1))
    then_conv Conv.rewr_conv Drule.swap_prems_eq

val move_prems_to_front_conv = sort (rev_order o int_ord)
  #> map_index (op +)
  #> map move_prem_to_front_conv
  #> Conv.every_conv

(* tactic combinators *)
fun HEADGOAL f = f 1

fun TRY' tac = tac ORELSE' K all_tac
fun EVERY_ARG tac = EVERY o map tac
fun EVERY_ARG' tac = EVERY' o map tac

fun FOCUS_PARAMS' tac = Subgoal.FOCUS_PARAMS (HEADGOAL o tac)
fun FOCUS_PARAMS_FIXED' tac = Subgoal.FOCUS_PARAMS_FIXED (HEADGOAL o tac)
fun FOCUS_PREMS' tac = Subgoal.FOCUS_PREMS (HEADGOAL o tac)
fun FOCUS' tac = Subgoal.FOCUS (HEADGOAL o tac)
fun SUBPROOF' tac = Subgoal.SUBPROOF (HEADGOAL o tac)

fun FOCUS_PARAMS_CTXT tac = Subgoal.FOCUS_PARAMS (#context #> tac)
fun FOCUS_PARAMS_CTXT' tac = FOCUS_PARAMS' (#context #> tac)

fun CSUBGOAL_DATA f tac = CSUBGOAL (uncurry tac o apfst f)
fun CSUBGOAL_PREMS_CONCL f = CSUBGOAL_DATA (f o strip_cimp)
fun SUBGOAL_DATA f tac = SUBGOAL (uncurry tac o apfst f)
fun SUBGOAL_PREMS_CONCL f = SUBGOAL_DATA (f o strip_imp)

(* tactics *)
fun insert_tac thm = resolve0_tac [thm COMP revcut_rl]

fun thin_tac n = rotate_tac n THEN' (DETERM o eresolve0_tac [thin_rl]) THEN' rotate_tac (~n)
fun thin_tacs delete_is = EVERY_ARG' thin_tac (sort int_ord delete_is |> map_index ((op -) o swap))

fun nth_assume_tac n ctxt = rotate_tac n THEN' assume_tac ctxt

fun resolve_all_tac ctxt = EVERY_ARG' (resolve_tac ctxt o single)

fun subst_first_tac ctxt = DETERM oo EqSubst.eqsubst_tac ctxt [0] o single
fun subst_first_asm_tac ctxt = DETERM oo EqSubst.eqsubst_asm_tac ctxt [0] o single

fun apply_tac tac i = Goal.init #> tac i #> Seq.map Goal.conclude

fun protect_tac n ctxt =
  let fun protect ct i =
    let val nprems = Logic.count_prems (Thm.term_of ct)
    in
      if nprems < n then no_tac
      else
        let
          val ctrimmed = funpow n (Thm.dest_implies #> snd) ct
          val protect_thm = Drule.protectD
            |> Thm.instantiate (TVars.empty, Vars.make [((("A", 0), propT), ctrimmed)])
        in
        resolve_tac ctxt [protect_thm] i
        THEN REPEAT_DETERM_N (nprems - n) (thin_tac n i)
        THEN EVERY_ARG (fn n => nth_assume_tac n ctxt (i + 1)) (n upto nprems - 1)
      end
    end
  in if n < 0 then K no_tac else CSUBGOAL (uncurry protect) end

val unprotect_tac = resolve0_tac [Drule.protectI]

fun protected_tac n tac ctxt =
  protect_tac n ctxt
  THEN' tac
  THEN_ALL_NEW unprotect_tac

fun focus_prems_tac is tac ctxt =
  CONVERSION (move_prems_to_front_conv is)
  THEN' protect_tac (length is) ctxt
  THEN' FOCUS' (fn {context=ctxt, params=params, prems=prems,
    asms=asms, concl=concl, schematics=schematics} =>
    let val concl = unprotect concl
    in
      unprotect_tac
      THEN' tac {context=ctxt, params=params, prems=prems, asms=asms, concl=concl, schematics=schematics}
    end
  ) ctxt

fun focus_delete_prems_tac is tac ctxt =
  focus_prems_tac is tac ctxt
  THEN' thin_tacs (0 upto length is - 1)

(* simplifier *)
fun set_simps ctxt thms = (clear_simpset ctxt) addsimps thms


end