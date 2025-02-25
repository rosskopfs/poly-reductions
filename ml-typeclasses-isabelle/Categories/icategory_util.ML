(*  Title:  icategory_util.ML
    Author: Kevin Kappelmann

Utilities on indexed categories
*)
signature IARROW_EXCEPTION_REC =
sig
  include IARROW_EXCEPTION
  val repeat : ('p1, 'i, 'i, 'a, 'a) cat -> ('p1, 'i, 'i, 'a, 'a) cat
  val try_step : ('p1, 'i, 'j, 'a, 'b) cat -> ('p1, 'i, 'i, 'a, 'a) cat -> ('p1, 'i, 'j, 'a, 'b) cat
end

signature IKLEISLI_ARROW_EXCEPTION_REC =
sig
  structure K : IKLEISLI
  include IARROW_EXCEPTION_REC
  where type ('p1, 'i, 'j, 'a, 'b) cat = ('p1, 'i, 'j, 'a, 'b) K.kleisli
end

functor IKleisli_Arrow_Exception_Rec(AE : IKLEISLI_ARROW_EXCEPTION) : IKLEISLI_ARROW_EXCEPTION_REC =
struct
open AE
fun repeat move x = x |> try (comp (repeat move) move)
fun try_step f step x = x |> catch' f (comp (try_step f step) step)
end

signature IARROW_FOLD =
sig
  include IARROW_BASE

  type 'a res
  val stop : 'a -> 'a res
  val continue : 'a -> 'a res
  val dest_res : 'a res -> 'a

  val fold : ('p1, 'j, 'i, 'a, 'a) cat -> ('p1, 'i, 'j, 'a * 'b, 'b res) cat ->
    ('p1, 'i, 'j, 'a * 'b, 'b res) cat

  val fold_init : ('p1, 'i, 'i, 'a, 'a) cat -> ('p1, 'i, 'i, 'a * 'b, 'b res) cat ->
    ('p1, 'i, 'i, 'a, 'b res) cat -> ('p1, 'i, 'i, 'a, 'b res) cat
end

signature IKLEISLI_ARROW_FOLD =
sig
  structure K : IKLEISLI
  include IARROW_FOLD
  where type ('p1, 'i, 'j, 'a, 'b) cat = ('p1, 'i, 'j, 'a, 'b) K.kleisli
end

functor IKleisli_Arrow_Fold_Exception_Rec(AE : IKLEISLI_ARROW_EXCEPTION_REC) : IKLEISLI_ARROW_FOLD =
struct

open AE

datatype 'a res = Stop of 'a | Continue of 'a

val stop = Stop
val continue = Continue
fun dest_res (Stop x) = x
  | dest_res (Continue x) = x

local structure SC = ISemi_Category(AE) structure A = IKleisli_Arrow(K.M) open SC A
in

fun fold_step _ _ (_, res as Stop _) = res |> id ()
  | fold_step next cont x = x |> (AE.catch' ((next *** arr dest_res) >>> cont) (arr snd))

fun fold next update x = x |> (arr fst &&& update >>> fold_step next (fold next update))

fun fold_init next update init = AE.try_step (id () &&& init) next
  >>> fold_step next (fold next update)

end

end

