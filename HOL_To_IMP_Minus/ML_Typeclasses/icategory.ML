(*  Title: icategory.ML
    Author: Kevin Kappelmann

Basic indexed typeclasses related to category theory,
inspired by the Haskell base package and
"Kleisli arrows of outrageous fortune" by Conor McBride.
*)
signature ICATEGORY_BASE =
sig

type ('i, 'o, 'a, 'b) cat
val id : ('i, 'i, 'a, 'a) cat
val comp : ('j, 'k, 'b, 'c) cat -> ('i, 'j, 'a, 'b) cat -> ('i, 'k, 'a, 'c) cat

end

functor Category_Base_ICategory_Base
  (structure IC : ICATEGORY_BASE; structure T : GROUND_TYPE) : CATEGORY_BASE =
struct

type ('a, 'b) cat = (T.t, T.t, 'a, 'b) IC.cat
val id = IC.id
val comp = IC.comp

end

signature IARROW_BASE =
sig

include ICATEGORY_BASE
val arr : ('a -> 'b) -> ('i, 'i, 'a, 'b) cat
val *** : ('i, 'j, 'a, 'b) cat -> ('j, 'k, 'c, 'd) cat -> ('i, 'k, ('a * 'c), ('b * 'd)) cat

end

signature IARROW =
sig

include IARROW_BASE

val first : ('i, 'o, 'a, 'b) cat -> ('i, 'o, ('a * 'c), ('b * 'c)) cat
val second : ('i, 'o, 'a, 'b) cat -> ('i, 'o, ('c * 'a), ('c * 'b)) cat

end

functor Arrow_Base_IArrow_Base
  (structure IA : IARROW_BASE; structure T : GROUND_TYPE) : ARROW_BASE =
struct

structure C = Category_Base_ICategory_Base(structure IC = IA; structure T = T)
open C
val arr = IA.arr
val *** = IA.***

end

functor IArrow(IA : IARROW_BASE) : IARROW =
struct

open IA
fun first f = *** f id
fun second f = *** id f

end

signature IKLEISLI =
sig

structure IM : IMONAD_BASE

type ('i, 'o, 'a, 'b) kleisli
val interp : ('i, 'o, 'a, 'b) kleisli -> 'a -> ('i, 'o, 'b) IM.t

(*Indexed Kleisli category*)
include IARROW_BASE
sharing type cat = kleisli

end

functor Kleisli_IKleisli
  (structure IK : IKLEISLI; structure T : GROUND_TYPE) : KLEISLI =
struct

structure M = Monad_Base_IMonad_Base(structure IM = IK.IM; structure T = T)

type ('a, 'b) kleisli = (T.t, T.t, 'a, 'b) IK.kleisli
val interp = IK.interp
structure A = Arrow_Base_IArrow_Base(structure IA = IK; structure T = T)
open A

end

functor IKleisli(IM : IMONAD_BASE) : IKLEISLI =
struct

structure IM = IM

datatype ('i, 'o, 'a, 'b) kleisli = Kleisli of 'a -> ('i, 'o, 'b) IM.t
fun interp (Kleisli f) = f

(*IARROW_BASE instance*)
type ('i, 'o, 'a, 'b) cat = ('i, 'o, 'a, 'b) kleisli
val id = Kleisli IM.pure
fun comp k1 k2 = Kleisli (fn x => IM.bind (interp k2 x) (interp k1))
fun arr f = Kleisli (IM.pure o f)
fun *** k1 k2 = Kleisli (fn (x, y) => IM.bind (interp k1 x)
  (fn x' => IM.bind (interp k2 y)
  (fn y' => IM.pure (x', y'))))

end