(*  Title:  state.ML
    Author: Kevin Kappelmann

Indexed state monads adapted from Haskell's mtl package.
*)
signature IMONAD_STATE_BASE =
sig
  structure SR : STATE_RESULT_BASE
  include IMONAD_BASE
  val state : ('si -> ('so, 'a) SR.result) -> ('p1, 'si, 'so, 'a) t
  val get : unit -> ('p1, 's, 's, 's) t
  val put : 'so -> ('p1, 'si, 'so, unit) t
end

signature IMONAD_STATE =
sig
  include IMONAD_STATE_BASE
  val map_state : ('sj -> 'so) -> ('p1, 'si, 'sj, 'a) t -> ('p1, 'si, 'so, 'a) t
  val map_result : ('a -> 'sj -> ('so, 'b) SR.result) -> ('p1, 'si, 'sj, 'a) t -> ('p1, 'si, 'so, 'b) t
end

functor IMonad_State(M : IMONAD_STATE_BASE) : IMONAD_STATE =
struct
open M
structure SR = State_Result(SR)
fun map_base f st = M.bind st (M.state o f)
fun map_state f = map_base (fn x => fn s => SR.result (f s) x)
fun map_result f = map_base f
end

signature STATE_TRANS =
sig
  structure SR : STATE_RESULT_BASE

  type ('p1, 'a) mt
  type ('p1, 'si, 'so, 'a) state = 'si -> ('p1, ('so, 'a) SR.result) mt

  include IMONAD_TRANS
  where type ('p1, 'si, 'so, 'a) t = ('p1, 'si, 'so, 'a) state
  sharing type M.t = mt

  (*IMONAD_STATE_BASE*)
  val state : ('si -> ('so, 'a) SR.result) -> ('p1, 'si, 'so, 'a) state
  val get : unit -> ('p1, 's, 's, 's) state
  val put : 'so -> ('p1, 'si, 'so, unit) state

  val eval : 'si -> ('p1, 'si, 'so, 'a) state -> ('p1, 'a) M.t
  val exec : 'si -> ('p1, 'si, 'so, 'a) state -> ('p1, 'so) M.t
end

functor State_Trans(structure M : MONAD_BASE; structure SR : STATE_RESULT_BASE) : STATE_TRANS =
struct

type ('p1, 'a) mt = ('p1, 'a) M.t
type ('p1, 'si, 'so, 'a) state = 'si -> ('p1, ('so, 'a) SR.result) mt

structure MT : IMONAD_TRANS =
struct
structure M = Monad(M) open M
type ('p1, 'si, 'so, 'a) t = ('p1, 'si, 'so, 'a) state

fun lift x s = x >>= (SR.result s #> M.pure)

structure SR = State_Result(SR)
fun map f st = M.map (SR.map_value f) o st
fun pure x = M.pure o (fn s => SR.result s x)
fun stf <*> stx = (fn s => stf s
  >>= (fn r => stx (SR.state r)
  >>= (fn r' => SR.result (SR.state r') (SR.value r (SR.value r')) |> M.pure)))
fun bind st f_st = (fn s => st s >>= (fn r => (f_st (SR.value r)) (SR.state r)))
end
open MT

structure MS : IMONAD_STATE_BASE =
struct
open MT
structure SR = SR
fun state fs = M.pure o fs
fun get () = state (fn s => SR.result s s)
fun put s = state (fn _ => SR.result s ())
end
open MS

fun eval s st = st s |> M.map SR.value
fun exec s st = st s |> M.map SR.state

end

functor IMonad_Zero_State_Trans(
    structure M : MONAD_ZERO_BASE
    structure S : STATE_TRANS
    sharing type S.M.t = M.t
  ) : IMONAD_ZERO_BASE where type ('p1, 'i, 'j, 'a) t = ('p1, 'i, 'j, 'a) S.t
  =
struct
fun zero _ = S.lift (M.zero ())
open S
end

functor IMonad_Exception_State_Trans(
    structure M : MONAD_EXCEPTION_BASE
    structure S : STATE_TRANS
    sharing type S.M.t = M.t
  ) : IMONAD_EXCEPTION_BASE where type ('p1, 'i, 'j, 'a) t = ('p1, 'i, 'j, 'a) S.t
  =
struct

open M
fun throw e = S.lift (M.throw e)
fun catch m f s = M.catch (m s) (fn e => f e s)
open S

end

signature IARROW_STATE_BASE =
sig
  include IARROW_BASE
  val get : unit -> ('p1, 's, 's, 'a, 's) cat
  val put : unit -> ('p1, 'si, 'so, 'so, unit) cat
end

signature IARROW_STATE =
sig
  include IARROW_STATE_BASE
  val change : ('p1, 'si, 'sm, 'a * 'si, 'so) cat -> ('p1, 'si, 'so, 'a, 'a) cat
  val access : ('p1, 'si, 'so, 'a * 'si, 'b) cat -> ('p1, 'si, 'so, 'a, 'b) cat
end

functor IArrow_State(
    structure AS : IARROW_STATE_BASE
    structure A : IARROW
    sharing type A.cat = AS.cat
  ) : IARROW_STATE =
struct
open AS
open A

local structure SC = ISemi_Category(A) open SC
in
fun get_state _ = id () &&& get ()
fun change f = get_state () &&& id ()
  >>> first (f >>> put ())
  >>> arr snd
fun access f = get_state () >>> f
end

end

signature IKLEISLI_ARROW_STATE_BASE =
sig
  structure K : IKLEISLI
  include IARROW_STATE_BASE
  where type ('p1, 'i, 'j, 'a, 'b) cat = ('p1, 'i, 'j, 'a, 'b) K.kleisli
end

functor IKleisli_Arrow_State_Base(MS : IMONAD_STATE_BASE) : IKLEISLI_ARROW_STATE_BASE =
struct
structure KA = IKleisli_Arrow_Apply_Base(MS)
open KA
fun get _ _ = MS.get ()
fun put _ x = MS.put x
end
