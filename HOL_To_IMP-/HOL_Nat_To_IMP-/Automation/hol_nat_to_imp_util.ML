(*  Title:  Automation/hol_nat_to_imp_util.ML
    Author: Kevin Kappelmann

More utilities when refining HOL to IMP programs.
*)
infix 1 LET

signature HOL_NAT_TO_IMP_UTIL =
sig
  include HOL_NAT_TO_IMP_UTIL

  val mk_register : string -> term
  val mk_state_register_retrieval : term -> string -> term

  val flip_eq_thm : Proof.context -> thm -> thm

  val with_dest_concl_tac : (unit -> string) -> (term -> 'a) -> Proof.context ->
    ('a -> int -> tactic) -> int -> tactic

  val seq_peek : ('a option -> 'b) -> 'a Seq.seq -> 'a Seq.seq
  val seq_peek_empty : (unit -> unit) -> 'a Seq.seq -> 'a Seq.seq

  structure Let : sig val LET : ('a * ('a -> 'b)) -> 'b end
end

structure HOL_Nat_To_IMP_Util : HOL_NAT_TO_IMP_UTIL =
struct

open HOL_Nat_To_IMP_Util
structure SUT = State_Update_Tracking

val mk_register = HOLogic.mk_string
fun mk_state_register_retrieval state = SUT.mk_state_retrieval state o mk_register

fun flip_eq_thm ctxt thm = Thm.proof_attributes [Calculation.symmetric] thm ctxt |> fst

fun with_dest_concl_tac msg dest_concl ctxt tac =
  let fun wrap_tac concl = case try dest_concl concl of
      NONE => (@{log Logger.WARN} ctxt msg; K no_tac)
    | SOME x => tac x
  in Tactic_Util.SUBGOAL_STRIPPED (snd o snd) wrap_tac end

(*evaluates the first element, offers it (or NONE) to f, then returns a new sequence where the
evaluation of the first element has been memoized*)
fun seq_peek f s =
  case Seq.pull s of
    SOME (x, xs) => (f (SOME x); Seq.cons x xs)
  | NONE => (f NONE; Seq.empty)

fun seq_peek_empty f = seq_peek (fn NONE => f () | SOME _ => ())

structure Let = struct
  fun x LET f = f x
end

end