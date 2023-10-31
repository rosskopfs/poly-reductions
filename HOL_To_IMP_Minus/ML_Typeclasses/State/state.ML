(*  Title: state.ML
    Author: Kevin Kappelmann

Indexed state monad, inspired by the Haskell Prelude
and "Kleisli arrows of outrageous fortune" by Conor McBride.
*)
signature STATE =
sig

structure M : MONAD_BASE
structure SR : STATE_RESULT_BASE

type ('si, 'so, 'a) state
val interp : ('si, 'so, 'a) state -> 'si -> ('so, 'a) SR.result M.t
val State : ('si -> ('so, 'a) SR.result M.t) -> ('si, 'so, 'a) state
val state : ('si -> ('so, 'a) SR.result) -> ('si, 'so, 'a) state

val eval : ('si, 'so, 'a) state -> 'si -> 'a M.t
val exec : ('si, 'so, 'a) state -> 'si -> 'so M.t
val get : unit -> ('s, 's, 's) state
val put : 'so -> ('si, 'so, unit) state

(*states are indexed monads*)
include IMONAD_BASE
sharing type state = t

val kleisli : ('a -> 'b) -> 'a -> ('s, 's, 'b) state
val kleisli_state : ('a -> 's -> 'b) -> 'a -> ('s, 's, 'b) state
val kleisli_state_monad : ('a -> 's -> 'b M.t) -> 'a -> ('s, 's, 'b) state

val lift_state_single : ('a -> 'b -> 'c) -> 'a -> 'b -> ('b, 'c) SR.result M.t
val lift_state_monad : ('a -> 'b -> 'c M.t) -> 'a -> 'b -> ('b, 'c) SR.result M.t

end

functor State(structure M : MONAD_BASE; structure S : STATE_RESULT_BASE) : STATE =
struct

structure M = M
structure SR = State_Result(S)

datatype ('si, 'so, 'a) state = State of 'si -> ('so, 'a) S.result M.t
fun interp (State fs) = fs
fun state fs = State (M.pure o fs)

fun eval st s = interp st s |> M.map S.value
fun exec st s = interp st s |> M.map S.state
fun get () = state (fn s => S.result s s)
fun put s = state (fn _ => S.result s ())

(*IMONAD_BASE instance*)
structure IM : IMONAD_BASE =
struct
type ('i, 'j, 'a) t = ('i, 'j, 'a) state

fun map f st = State (M.map (SR.map_value f) o interp st)
fun pure x = state (fn s => S.result s x)
fun <*> stf stx = State (fn s => M.bind (interp stf s)
  (fn r => M.bind (interp stx (S.state r))
  (fn r' => S.result (S.state r') (S.value r (S.value r')) |> M.pure)))
fun bind st f_st = State (fn s => M.bind (interp st s)
  (fn r => interp (f_st (S.value r)) (S.state r)))
end
open IM

structure IK = IKleisli(IM)
fun kleisli f = IK.arr f |> IK.interp

fun kleisli_state f x = get () |> map (f x)
fun kleisli_state_monad f x = State (fn s => M.map (S.result s) (f x s))

fun lift_state_single f = interp o kleisli_state f
fun lift_state_monad fsq = interp o kleisli_state_monad fsq

end

signature STATE_STACK =
sig

structure S : STATE
structure SRS : STATE_RESULT_STACK

val push_state_monad : ('a -> 'b) ->
  ('a -> 'c -> (('d, 'e) SRS.entry, 'f) S.SR.result S.M.t) ->
  'a -> 'c -> (('d, ('e, 'b) SRS.entry) SRS.entry, 'f) S.SR.result S.M.t
val lift_push_state_monad : ('a -> 'b) ->
  ('a -> ('c, 'd) SRS.entry -> 'e S.M.t) ->
  'a -> ('c, 'd) SRS.entry -> (('c, ('d, 'b) SRS.entry) SRS.entry, 'e) S.SR.result S.M.t

end

functor State_Stack(S : STATE) : STATE_STACK =
struct

structure S = S
structure SR = State_Result(S.SR)
structure SRS = State_Result_Stack(S.SR)

fun push_state_monad lense f x = S.M.map (SR.map_state (SRS.push (lense x))) o f x
fun lift_push_state_monad lense = push_state_monad lense o S.lift_state_monad

end