(*  Title: Refinements/hol_to_imp_util.ML
    Author: Kevin Kappelmann

More utilities when refining HOL to IMP programs.
*)

infix 1 LET

signature HOL_TO_IMP_UTIL =
sig
include HOL_TO_IMP_UTIL

val dest_IMP_Minus_big_step : term -> (term * term) * term * term
val mk_IMP_Minus_big_step : typ -> term -> term -> term -> term -> term

val mk_register : string -> term
val mk_state_register_retrieval : term -> string -> term

val refl_tac : Proof.context -> int -> tactic
val uresolve_tac : Proof.context -> thm list -> int -> tactic

val seq_peek : ('a option -> 'b) -> 'a Seq.seq -> 'a Seq.seq
val seq_peek_empty : (unit -> unit) -> 'a Seq.seq -> 'a Seq.seq

structure Let : sig val LET : ('a * ('a -> 'b)) -> 'b end

val time_tac : (Pretty.T -> unit) -> string -> ('a -> 'b Seq.seq) -> 'a -> 'b Seq.seq

end

structure HOL_To_IMP_Util : HOL_TO_IMP_UTIL =
struct

open HOL_To_IMP_Util
structure SUT = State_Update_Tracking

val dest_IMP_Minus_big_step =
  \<^Const_fn>\<open>big_step_t for \<^Const>\<open>Pair _ _ for c s\<close> t s' => \<open>((c, s), t, s')\<close>\<close>

fun mk_IMP_Minus_big_step state IMP_program s t s'=
  \<^Const>\<open>Pair \<^typ>\<open>com\<close> state for \<open>IMP_program\<close> s\<close>
  |> (fn cs => \<^Const>\<open>big_step_t for cs t s'\<close>)

val mk_register = HOLogic.mk_string
fun mk_state_register_retrieval state = SUT.mk_state_retrieval state o mk_register

fun refl_tac ctxt = resolve_tac ctxt [@{thm refl}]

fun uresolve_tac ctxt thms =
  Standard_Unify_Resolve.unify_resolve_tac (Unify_Resolve_Args.PRM.r ()) thms [] ctxt

(* evaluates the first element, offers it (or NONE) to f, then returns a new sequence where the
    evaluation of the first element has been memoized *)
fun seq_peek f s =
  case Seq.pull s of
    SOME (x, xs) => (f (SOME x); Seq.cons x xs)
  | NONE => (f NONE; Seq.empty)

fun seq_peek_empty f = seq_peek (fn NONE => f () | SOME _ => ())

structure Let = struct
  fun x LET f = f x
end


val bblock = Pretty.block o Pretty.breaks

fun pretty_timing { elapsed, cpu, gc } =
  let fun item l t = bblock [Pretty.str l, Value.print_time t |> Pretty.str]
  in bblock [item "elapsed:" elapsed, item "cpu:" cpu, item "gc:" gc] end

fun time_tac printer label tac st =
  let
    fun log t s : unit =
      bblock [
        Pretty.str label,
        Pretty.str ("[" ^ s ^ "]"),
        pretty_timing t]
      |> printer
    
    fun time_seq0 i s =
      Seq.make (fn () =>
        let
          val (t, cell) = Timing.timing Seq.pull s
          val _ = log t (Int.toString i)
        in
      case cell of
          NONE => NONE
        | SOME (x, s') => SOME (x, time_seq0 (i + 1) s')
    end)
    val (t, seq) = Timing.timing tac st
    val _ = log t "init"
  in time_seq0 0 seq end

(* fun lbld lbl p = Pretty.writeln (bblock [Pretty.str lbl, p]) *)

end

