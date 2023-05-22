(*  Title: state_result.ML
    Author: Kevin Kappelmann

Types that contain a state and a result value.
*)
signature STATE_RESULT_BASE =
sig

type ('s, 'a) result
val interp : ('s, 'a) result -> ('a * 's)
val result : 's -> 'a -> ('s, 'a) result

val state : ('s, 'a) result -> 's
val value : ('s, 'a) result -> 'a

end

signature STATE_RESULT =
sig

include STATE_RESULT_BASE
val map : ('a -> 's -> 'b * 't) -> ('s, 'a) result -> ('t, 'b) result
val map_state : ('s -> 't) -> ('s, 'a) result -> ('t, 'a) result
val map_value : ('a -> 'b) -> ('s, 'a) result -> ('s, 'b) result
val empty_state_result : 'a -> (unit, 'a) result
val empty_value_result : 's -> ('s, unit) result

end

functor State_Result(S : STATE_RESULT_BASE) : STATE_RESULT =
struct

open S
fun map f = uncurry result o swap o uncurry f o interp
fun map_state f = uncurry result o swap o apsnd f o interp
fun map_value f = uncurry result o swap o apfst f o interp
fun empty_value_result s = result s ()
fun empty_state_result x = result () x

end

(*From a given STATE_RESULT structure, we can build a new structure
that contains a state and a non-empty result values stack. Such a structure is
useful for sequential, stateful tactic compositions: result values can be
pushed to the result values stack to be available for later tactics while the
position of the (permanent) state stays fixed.*)

signature STATE_RESULT_STACK =
sig

type ('s, 'a) entry

structure SR : STATE_RESULT_BASE
sharing type entry = SR.result

val empty : 's -> ('s, unit) entry
val init : 's  -> 'a -> ('s, 'a) entry
val push : 'a -> ('s, 'b) entry -> ('s, ('b, 'a) entry) entry
val pop : ('s, ('a, 'b) entry) entry -> ('b * ('s, 'a) entry)
val pop' : ('s, ('a, 'b) entry) entry -> ('s, 'a) entry

end

functor State_Result_Stack(SR : STATE_RESULT_BASE) : STATE_RESULT_STACK =
struct

structure SR = State_Result(SR)
type ('s, 'a) entry = ('s, 'a) SR.result
val empty = SR.empty_value_result
fun init x = SR.result x
fun push x = SR.map_value (fn x' => SR.result x' x)
fun pop r = SR.interp r |> (fn (r', s) => (SR.value r', SR.result s (SR.state r')))
fun pop' r = SR.map_value SR.state r

end

(*instances*)

structure Pair_State_Result_Base : STATE_RESULT_BASE =
struct

type ('s, 'a) result = ('a * 's)
val interp = I
val result = rpair
val state = snd
val value = fst

end
