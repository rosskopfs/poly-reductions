signature VIEW_UTIL =
sig
  (* general *)
  val nth_replace : int -> 'a -> 'a list -> 'a list
  (*returns false if function throws an exception*)
  val try_bool : ('a -> bool) -> 'a -> bool
  (*turns option into a sequence; calls given function if option is NONE*)
  val seq_of_opt : (unit -> unit) -> 'a option -> 'a Seq.seq

  exception EXTRACT_NONE of unit -> string
  val extract_opt : (unit -> string) -> 'a option -> 'a

  (* HOL-specific *)
  val dest_Trueprop : term -> term
  val cdest_Trueprop : cterm -> cterm
  val dest_eq : term -> term * term
  val cdest_eq : cterm -> cterm * cterm

  (* simplifier *)
  val set_simps : Proof.context -> thm list -> Proof.context

  (* tactics *)
  val subst_first_tac : Proof.context -> thm list -> int -> tactic
  val subst_first_asm_tac : Proof.context -> thm list -> int -> tactic
  val resolve_all_tac : Proof.context -> thm list -> int -> tactic
end

structure View_Util : VIEW_UTIL =
struct

(* general *)
fun nth_replace n x = nth_map n (K x)

fun try_bool f = try f #> (Option.getOpt o rpair false)

fun seq_of_opt _ (SOME x) = Seq.single x
  | seq_of_opt f_none NONE = (f_none (); Seq.empty)

exception EXTRACT_NONE of unit -> string
fun extract_opt error_msg opt =
  if is_none opt
  then raise EXTRACT_NONE error_msg
  else the opt

(* HOL-specific *)
val dest_Trueprop = HOLogic.dest_Trueprop
val cdest_Trueprop = Thm.dest_arg

val dest_eq = HOLogic.dest_eq
val cdest_eq = Thm.dest_binop

(* simplifier *)
fun set_simps ctxt thms = (clear_simpset ctxt) addsimps thms

(* tactics *)

fun subst_first_tac ctxt = EqSubst.eqsubst_tac ctxt [1]
fun subst_first_asm_tac ctxt = EqSubst.eqsubst_asm_tac ctxt [1]

fun resolve_all_tac ctxt = Tactic_Util.EVERY_ARG' (resolve_tac ctxt o single)

end