(*  Title:  category_util.ML
    Author: Kevin Kappelmann

Utilities on categories
*)
signature ARROW_EXCEPTION_REC =
sig
  include ARROW_EXCEPTION
  val repeat : ('p1, 'a, 'a) cat -> ('p1, 'a, 'a) cat
  val try_step : ('p1, 'a, 'b) cat -> ('p1, 'a, 'a) cat -> ('p1, 'a, 'b) cat
end

signature KLEISLI_ARROW_EXCEPTION_REC =
sig
  structure K : KLEISLI
  include ARROW_EXCEPTION_REC
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) K.kleisli
end

functor Kleisli_Arrow_Exception_Rec(AE : KLEISLI_ARROW_EXCEPTION) : KLEISLI_ARROW_EXCEPTION_REC =
struct
open AE
fun repeat move x = x |> try (comp (repeat move) move)
fun try_step f step x = x |> catch' f (comp (try_step f step) step)
end

signature ARROW_FOLD =
sig
  include ARROW_BASE

  type 'a res
  val stop : 'a -> 'a res
  val continue : 'a -> 'a res
  val dest_res : 'a res -> 'a

  val fold : ('p1, 'a, 'a) cat -> ('p1, 'a * 'b, 'b res) cat ->
    ('p1, 'a * 'b, 'b res) cat

  val fold_init : ('p1, 'a, 'a) cat -> ('p1, 'a * 'b, 'b res) cat ->
    ('p1, 'a, 'b res) cat -> ('p1, 'a, 'b res) cat
end

signature KLEISLI_ARROW_FOLD =
sig
  structure K : KLEISLI
  include ARROW_FOLD
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) K.kleisli
end

functor Kleisli_Arrow_Fold_Exception_Rec(AE : KLEISLI_ARROW_EXCEPTION_REC) : KLEISLI_ARROW_FOLD =
struct

open AE

datatype 'a res = Stop of 'a | Continue of 'a

val stop = Stop
val continue = Continue
fun dest_res (Stop x) = x
  | dest_res (Continue x) = x

local structure SC = Semi_Category(AE) structure A = Kleisli_Arrow(K.M) open SC A
in

fun fold_step _ _ (_, res as Stop _) = res |> id ()
  | fold_step next cont x = x |> (AE.catch' ((next *** arr dest_res) >>> cont) (arr snd))

fun fold next update x = x |> (arr fst &&& update >>> fold_step next (fold next update))

fun fold_init next update init = AE.try_step (id () &&& init) next
  >>> fold_step next (fold next update)

end

end
