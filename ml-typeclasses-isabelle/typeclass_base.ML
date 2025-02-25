(*  Title:  typeclass_base.ML
    Author: Kevin Kappelmann

Basic typeclasses inspired by the Haskell Prelude, monad-transformers, and the mtl package.

You might wonder: what are those 'pi type variables?
They are here because many types ('a1,...,'a{n+1}) t satisfy below laws for
all 'a1,...,'an. For example, ('a, 'b) either is a functor for all 'a. However, we cannot express
this in the SML type system. We can only say (t, 'b) either is a functor for each and every ground
type g. We hence use additional 'pi type variables to allow such instances.

Unfortunately, we cannot do this for an arbitrary number of 'pi type variables. As of now, we only
support the case for i=1.
*)
infix 1 <*>
infix 1 >>=
infix 1 <&>

signature FUNCTOR_BASE =
sig
  type ('p1, 'a) t
  val map : ('a -> 'b) -> ('p1, 'a) t -> ('p1, 'b) t
end

signature FUNCTOR =
sig
  include FUNCTOR_BASE
  val <&> : ('p1, 'a) t * ('a -> 'b) -> ('p1, 'b) t
end

functor Functor(F : FUNCTOR_BASE) : FUNCTOR =
struct

open F
fun x <&> f = map f x

end

signature FUNCTOR_TRANS =
sig
  (*the base functor to transform*)
  structure F : FUNCTOR_BASE
  include FUNCTOR_BASE
  val lift : ('p1, 'a) F.t -> ('p1, 'a) t
end

signature APPLICATIVE_BASE =
sig
  include FUNCTOR_BASE
  val pure : 'a -> ('p1, 'a) t
  val <*> : ('p1, 'a -> 'b) t * ('p1, 'a) t -> ('p1, 'b) t
end

signature APPLICATIVE =
sig
  include APPLICATIVE_BASE
  val liftA2 : ('a -> 'b -> 'c) -> ('p1, 'a) t -> ('p1, 'b) t -> ('p1, 'c) t
end

functor Applicative(A : APPLICATIVE_BASE) : APPLICATIVE =
struct

open A
fun liftA2 f x = curry (op <*>) (A.map f x)

end

signature APPLICATIVE_TRANS =
sig
  (*the base applicative to transform*)
  structure A : APPLICATIVE_BASE
  include APPLICATIVE_BASE
  val lift : ('p1, 'a) A.t -> ('p1, 'a) t
end

signature MONAD_BASE =
sig
  include APPLICATIVE_BASE
  val bind : ('p1, 'a) t -> ('a -> ('p1, 'b) t) -> ('p1, 'b) t
end

signature MONAD =
sig
  include MONAD_BASE
  val >>= : ('p1, 'a) t * ('a -> ('p1, 'b) t) -> ('p1, 'b) t
  val join : ('p1, ('p1, 'a) t) t -> ('p1, 'a) t
  val flat1 : ('p1, 'a -> ('p1, 'b) t) t -> 'a -> ('p1, 'b) t
  val flat2 : ('p1, 'a -> 'b -> ('p1, 'c) t) t -> 'a -> 'b -> ('p1, 'c) t
end

functor Monad(M : MONAD_BASE) : MONAD =
struct

open M
fun x >>= f = bind x f
fun join x = x >>= I
fun flat1 fm x = fm >>= (fn f => f x)
fun flat2 fm x = M.map (fn f => f x) fm |> flat1

end

signature MONAD_TRANS =
sig
  (*the base monad to transform*)
  structure M : MONAD_BASE
  include MONAD_BASE

  val lift : ('p1, 'a) M.t -> ('p1, 'a) t
end

signature ALTERNATIVE_BASE =
sig
  include APPLICATIVE_BASE
  (*laws: (empty, <|>) forms a monoid on ('p1, 'a) t*)
  val empty : unit -> ('p1, 'a) t
  val <|> : ('p1, 'a) t -> ('p1, 'a) t -> ('p1, 'a) t
end

signature ALTERNATIVE =
sig
  include ALTERNATIVE_BASE
  val optional : ('p1, 'a) t -> ('p1, 'a option) t
end

functor Alternative(A : ALTERNATIVE_BASE) : ALTERNATIVE =
struct

open A
fun optional x = A.<|> (A.map SOME x) (A.pure NONE)

end

signature MONAD_ZERO_BASE =
sig
  include MONAD_BASE
  val zero : unit -> ('p1, 'a) t
end

signature MONAD_PLUS_BASE =
sig
  include MONAD_ZERO_BASE
  (*satisfies left distribution law: "plus x y >>= f = plus (x >>= f) (y >>= f)"*)
  val plus_lazy : ('p1, 'a) t -> (unit -> ('p1, 'a) t) -> ('p1, 'a) t
end

signature MONAD_PLUS =
sig
  include MONAD_PLUS_BASE
  val plus : ('p1, 'a) t -> ('p1, 'a) t -> ('p1, 'a) t
end

functor Monad_Plus(M : MONAD_PLUS_BASE) : MONAD_PLUS =
struct
  open M
  fun plus x y = M.plus_lazy x (K y)
end

signature MONAD_OR_BASE =
sig
  include MONAD_ZERO_BASE
  (*satisfies left catch law: "or (pure x) y = pure x"*)
  val or_lazy : ('p1, 'a) t -> (unit -> ('p1, 'a) t) -> ('p1, 'a) t
end

signature MONAD_OR =
sig
  include MONAD_OR_BASE
  val or : ('p1, 'a) t -> ('p1, 'a) t -> ('p1, 'a) t
end

functor Monad_Or(M : MONAD_OR_BASE) : MONAD_OR =
struct
  open M
  fun or x y = M.or_lazy x (K y)
end

signature MONAD_EXCEPTION_BASE =
sig
  include MONAD_BASE
  type 'p1 exn
  val throw : 'p1 exn -> ('p1, 'a) t
  val catch : ('p1, 'a) t -> ('p1 exn -> ('p1, 'a) t) -> ('p1, 'a) t
end

signature FOLDABLE_BASE =
sig
  type ('p1, 'a) f
  val foldl : ('a -> 'b -> 'b) -> ('p1, 'a) f -> 'b -> 'b
  val foldr : ('a -> 'b -> 'b) -> ('p1, 'a) f -> 'b -> 'b
end

signature FOLDABLE_MONAD =
sig
  include FOLDABLE_BASE
  structure M : MONAD_BASE

  val foldlM : ('a -> 'b -> ('q1, 'b) M.t) -> ('p1, 'a) f -> 'b -> ('q1, 'b) M.t
  val foldrM : ('a -> 'b -> ('q1, 'b) M.t) -> ('p1, 'a) f -> 'b -> ('q1, 'b) M.t
end

functor Foldable_Monad(structure F : FOLDABLE_BASE; structure M : MONAD_BASE) : FOLDABLE_MONAD =
struct

open F
structure M = M

fun foldlM f xs acc = let fun c x k acc = M.bind (f x acc) k
  in foldr c xs M.pure acc end

fun foldrM f xs acc = let fun c x k acc = M.bind (f x acc) k
  in foldl c xs M.pure acc end

end

signature TRAVERSABLE_BASE =
sig
  include FUNCTOR_BASE
  include FOLDABLE_BASE
  sharing type t = f

  structure A : APPLICATIVE_BASE

  val traverse : ('a -> ('p1, 'b) A.t) -> ('p2, 'a) t -> ('p1, ('p2, 'b) t) A.t
end

signature TRAVERSABLE =
sig
  include TRAVERSABLE_BASE
  val sequence : ('p1, ('p2, 'a) A.t) t -> ('p2, ('p1, 'a) t) A.t
end

functor Traversable(T : TRAVERSABLE_BASE) : TRAVERSABLE =
struct

open T
fun sequence x = traverse I x

end

signature TRAVERSABLE_TRANS =
sig
  (*the base traversable to transform*)
  structure T : TRAVERSABLE_BASE
  include TRAVERSABLE_BASE
  val lift : ('p1, 'a) T.t -> ('p1, 'a) t
end



