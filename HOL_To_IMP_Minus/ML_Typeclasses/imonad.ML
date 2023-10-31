(*  Title: imonad.ML
    Author: Kevin Kappelmann

Basic indexed typeclasses up to monads, inspired by the Haskell Prelude
and "Kleisli arrows of outrageous fortune" by Conor McBride.
*)
signature IFUNCTOR_BASE =
sig

type ('i, 'o, 'a) t
val map : ('a -> 'b) -> ('i, 'o, 'a) t -> ('i, 'o, 'b) t

end

(*In general, we would like to get a Functor from an IFunctor for arbitrary index
types; however, SML cannot express polymorphic functors. The best we can do is hence to
create an instance for an arbitrary but fixed ground index type.*)
signature GROUND_TYPE = sig type t end

functor Functor_Base_IFunctor_Base
  (structure IF : IFUNCTOR_BASE; structure T : GROUND_TYPE) : FUNCTOR_BASE =
struct

type 'a t = (T.t, T.t, 'a) IF.t
val map = IF.map

end

signature IAPPLICATIVE_BASE =
sig

include IFUNCTOR_BASE
val pure : 'a -> ('i, 'i, 'a) t
val <*> : ('i, 'j, 'a -> 'b) t -> ('j, 'k, 'a) t -> ('i, 'k, 'b) t

end

functor Applicative_Base_IApplicative_Base
  (structure IA : IAPPLICATIVE_BASE; structure T : GROUND_TYPE) : APPLICATIVE_BASE =
struct

structure F = Functor_Base_IFunctor_Base(structure IF = IA; structure T = T)
open F
val pure = IA.pure
val <*> = IA.<*>

end

signature IMONAD_BASE =
sig

include IAPPLICATIVE_BASE
val bind : ('i, 'j, 'a) t -> ('a -> ('j, 'k, 'b) t) -> ('i, 'k, 'b) t

end

functor Monad_Base_IMonad_Base
  (structure IM : IMONAD_BASE; structure T : GROUND_TYPE) : MONAD_BASE =
struct

structure A = Applicative_Base_IApplicative_Base(structure IA = IM; structure T = T)
open A
val bind = IM.bind

end

signature IMONAD =
sig

include IMONAD_BASE
val >=> : ('a -> ('i, 'j, 'b) t) -> ('b -> ('j, 'k, 'c) t) -> 'a -> ('i, 'k, 'c) t

end

functor IMonad(M : IMONAD_BASE) : IMONAD =
struct

open M
fun >=> fm gm x = bind (fm x) gm 

end
