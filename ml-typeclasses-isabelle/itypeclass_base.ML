(*  Title:  itypeclass_base.ML
    Author: Kevin Kappelmann

Basic indexed typeclasses (in Atkey-style),
inspired by the Haskell Prelude and "Parameterised Notions of Computation" by Robert Atkey.

See typeclass_base.ML for an explanation of the 'pi type variables.
*)
signature IFUNCTOR_BASE =
sig
  type ('p1, 'i, 'o, 'a) t
  (*TODO: should we also require contravariance in first and covariance in second parameter?
  cf. paper by Atkey*)
  val map : ('a -> 'b) -> ('p1, 'i, 'o, 'a) t -> ('p1, 'i, 'o, 'b) t
end

signature IFUNCTOR =
sig
  include IFUNCTOR_BASE
  val <&> : ('p1, 'i, 'o, 'a) t * ('a -> 'b) -> ('p1, 'i, 'o, 'b) t
end

functor IFunctor(F : IFUNCTOR_BASE) : IFUNCTOR =
struct
open F
fun x <&> f = map f x
end

signature IFUNCTOR_TRANS =
sig
  (*the base functor to transform*)
  structure F : FUNCTOR_BASE
  include IFUNCTOR_BASE
  val lift : ('p1, 'a) F.t -> ('p1, 'i, 'i, 'a) t
end

signature IAPPLICATIVE_BASE =
sig
  include IFUNCTOR_BASE
  val pure : 'a -> ('p1, 'i, 'i, 'a) t
  val <*> : ('p1, 'i, 'j, 'a -> 'b) t * ('p1, 'j, 'k, 'a) t -> ('p1, 'i, 'k, 'b) t
end

signature IMONAD_BASE =
sig
  include IAPPLICATIVE_BASE
  val bind : ('p1, 'i, 'j, 'a) t -> ('a -> ('p1, 'j, 'k, 'b) t) -> ('p1, 'i, 'k, 'b) t
end

signature IMONAD =
sig
include IMONAD_BASE
  val >>= : ('p1, 'i, 'j, 'a) t * ('a -> ('p1, 'j, 'k, 'b) t) -> ('p1, 'i, 'k, 'b) t
  val join : ('p1, 'i, 'j, ('p1, 'j, 'k, 'a) t) t -> ('p1, 'i, 'k, 'a) t
end

functor IMonad(M : IMONAD_BASE) : IMONAD =
struct
open M
fun m >>= f = bind m f
fun join x = bind x I
end

signature IMONAD_TRANS =
sig
  (*the base monad to transform*)
  structure M : MONAD_BASE
  include IMONAD_BASE

  val lift : ('p1, 'a) M.t -> ('p1, 'i, 'i, 'a) t
end

signature IMONAD_ZERO_BASE =
sig
include IMONAD_BASE
val zero : unit -> ('p1, 'i, 'i, 'a) t
end

signature IMONAD_PLUS_BASE =
sig
  include IMONAD_ZERO_BASE
  (*satisfies left distribution law: "plus x y >>= f = plus (x >>= f) (y >>= f)"*)
  val plus_lazy : ('p1, 'i, 'j, 'a) t -> (unit -> ('p1, 'i, 'j, 'a) t) -> ('p1, 'i, 'j, 'a) t
end

signature IMONAD_OR_BASE =
sig
  include IMONAD_ZERO_BASE
  (*satisfies left catch law: "or (pure x) y = pure x"*)
  val or_lazy : ('p1, 'i, 'j, 'a) t -> (unit -> ('p1, 'i, 'j, 'a) t) -> ('p1, 'i, 'j, 'a) t
end

signature IMONAD_EXCEPTION_BASE =
sig
  include IMONAD_BASE
  type 'p1 exn
  val throw : 'p1 exn -> ('p1, 'i, 'i, 'a) t
  val catch : ('p1, 'i, 'j, 'a) t -> ('p1 exn -> ('p1, 'i, 'j, 'a) t) -> ('p1, 'i, 'j, 'a) t
end
