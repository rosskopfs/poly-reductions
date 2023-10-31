(*  Title: monad.ML
    Author: Kevin Kappelmann

Basic typeclasses up to monads, inspired by the Haskell Prelude.
*)
signature FUNCTOR_BASE =
sig

type 'a t
val map : ('a -> 'b) -> 'a t -> 'b t

end

signature APPLICATIVE_BASE =
sig

include FUNCTOR_BASE
val pure : 'a -> 'a t
val <*> : ('a -> 'b) t -> 'a t -> 'b t

end

signature MONAD_BASE =
sig

include APPLICATIVE_BASE
val bind : 'a t -> ('a -> 'b t) -> 'b t

end

signature MONAD =
sig

include MONAD_BASE
val >=> : ('a -> 'b t) -> ('b -> 'c t) -> 'a -> 'c t
val flat1 : ('a -> 'b t) t -> 'a -> 'b t
val flat2 : ('a -> 'b -> 'c t) t -> 'a -> 'b -> 'c t

end

functor Monad(M : MONAD_BASE) : MONAD =
struct

open M
fun >=> fm gm x = bind (fm x) gm
fun flat1 fm x = M.bind fm (fn f => f x)
fun flat2 fm x = M.map (fn f => f x) fm |> flat1

end