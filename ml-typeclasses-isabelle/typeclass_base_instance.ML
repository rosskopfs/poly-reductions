(*  Title:  typeclass_base_instance.ML
    Author: Kevin Kappelmann

Instances of basic typeclasses.
*)
structure Identity_Monad : MONAD_BASE =
struct

type ('p1, 'a) t = 'a
fun map f x = f x
fun pure x = x
fun f <*> x = f x
fun bind x f = f x

end

structure Identity_Foldable : FOLDABLE_BASE =
struct

type ('p1, 'a) f = 'a
fun foldl f x acc = f x acc
fun foldr f x acc = f x acc

end

functor Identity_Traversable(A : APPLICATIVE_BASE) : TRAVERSABLE_BASE =
struct

open Identity_Monad
open Identity_Foldable

structure A = A
fun traverse f x = f x

end

functor Seq_Functor_Trans(F : FUNCTOR_BASE) : FUNCTOR_TRANS =
struct

structure F = F

type ('p1, 'a) t = ('p1, 'a Seq.seq) F.t
fun lift x = F.map Seq.single x
fun map f = F.map (Seq.map f)

end

functor Seq_Foldable_Trans(F : FOLDABLE_BASE) : FOLDABLE_BASE =
struct

type ('p1, 'a) f = ('p1, 'a Seq.seq) F.f

fun fold_base step sq acc = case Seq.pull sq of
    SOME (x, sq) => step (fold_base step sq) x acc
  | NONE => acc

fun foldl f = F.foldl (fold_base (fn frec => frec oo f))
fun foldr f = F.foldr (fold_base (fn frec => fn x => f x o frec))

end

functor Seq_Traversable_Trans(T : TRAVERSABLE_BASE) : TRAVERSABLE_TRANS =
struct

structure T = T
structure F = Seq_Functor_Trans(T)
open F
structure F = Seq_Foldable_Trans(T)
open F
structure F = Seq_Foldable_Trans(Identity_Foldable)

structure A = Applicative(T.A)
fun traverse f = T.traverse (fn sq => F.foldr (A.liftA2 Seq.cons o f) sq (A.pure Seq.empty))

end

functor Seq_Monad_Trans(M : MONAD_BASE) : MONAD_TRANS =
struct

structure M = M
structure F = Seq_Functor_Trans(M)
open F

structure F = Seq_Functor_Trans(Identity_Monad)
structure T = Seq_Traversable_Trans(Identity_Traversable(M))

fun pure x = M.pure (Seq.single x)

local structure M = Monad(M) open M
in
fun f <*> x = x >>= (fn x => f >>= (Seq.maps (fn f => F.map f x) #> M.pure))

fun bind x f = x >>= T.traverse f >>= (Seq.flat #> M.pure)
end

end

functor List_Functor_Trans(F : FUNCTOR_BASE) : FUNCTOR_TRANS =
struct

structure F = F

type ('p1, 'a) t = ('p1, 'a list) F.t
fun lift x = F.map single x
fun map f = F.map (List.map f)

end

functor List_Foldable_Trans(F : FOLDABLE_BASE) : FOLDABLE_BASE =
struct

type ('p1, 'a) f = ('p1, 'a list) F.f

fun fold_base _ [] = I
  | fold_base step (x :: xs) = step (fold_base step xs) x

fun foldl f = F.foldl (fold_base (fn frec => frec oo f))
fun foldr f = F.foldr (fold_base (fn frec => fn x => f x o frec))

end

functor List_Traversable_Trans(T : TRAVERSABLE_BASE) : TRAVERSABLE_TRANS =
struct

structure T = T
structure F = List_Functor_Trans(T)
open F
structure F = List_Foldable_Trans(T)
open F
structure F = List_Foldable_Trans(Identity_Foldable)

structure A = Applicative(T.A)
fun traverse f = T.traverse (fn sq => F.foldr (A.liftA2 cons o f) sq (A.pure []))

end

functor List_Monad_Trans(M : MONAD_BASE) : MONAD_TRANS =
struct

structure M = M
structure F = List_Functor_Trans(M)
open F

structure F = List_Functor_Trans(Identity_Monad)
structure T = List_Traversable_Trans(Identity_Traversable(M))

fun pure x = M.pure (single x)

local structure M = Monad(M) open M
in
fun f <*> x = x >>= (fn x => f >>= (maps (fn f => F.map f x) #> M.pure))

fun bind x f = x >>= (fn x => T.traverse f x >>= (flat #> M.pure))
end
end

functor Option_Functor_Trans(F : FUNCTOR_BASE) : FUNCTOR_TRANS =
struct

structure F = F

type ('p1, 'a) t = ('p1, 'a option) F.t
fun lift x = F.map SOME x
fun map f = F.map (Option.map f)

end

functor Option_Monad_Trans(M : MONAD_BASE) : MONAD_TRANS =
struct

structure M = M
structure F = Option_Functor_Trans(M)
open F

fun pure x = M.pure (SOME x)
fun f <*> x = M.bind f (fn NONE => M.pure NONE | SOME f => map f x)
fun bind x f = M.bind x (fn NONE => M.pure NONE | SOME x => f x)

end

functor Option_Monad_Or_Trans(M : MONAD_BASE) : MONAD_OR_BASE =
struct

structure OM = Option_Monad_Trans(M)
open OM

fun zero _ = M.pure NONE
fun or_lazy x fy = OM.M.bind x (fn NONE => fy () | _ => x)

end

functor Option_Monad_Exception_Trans_Exception(M : MONAD_EXCEPTION_BASE)
  : MONAD_EXCEPTION_BASE where type 'p1 exn = 'p1 M.exn =
struct

structure OM = Option_Monad_Trans(M)
type 'p1 exn = 'p1 M.exn

fun throw e = e |> OM.lift o M.throw
fun catch m f = M.catch m f
open OM

end

functor Option_Foldable_Trans(F : FOLDABLE_BASE) : FOLDABLE_BASE =
struct

type ('p1, 'a) f = ('p1, 'a option) F.f

fun fold_base _ NONE = I
  | fold_base f (SOME x) = f x
fun foldl f = F.foldl (fold_base f)
fun foldr f = F.foldr (fold_base f)

end

functor Option_Traversable_Trans(T : TRAVERSABLE_BASE) : TRAVERSABLE_TRANS =
struct

structure T = T
structure F = Option_Functor_Trans(T)
open F
structure F = Option_Foldable_Trans(T)
open F

structure A = Applicative(T.A)
fun traverse f = T.traverse (fn NONE => A.pure NONE | SOME x => A.map SOME (f x))

end

functor Monad_Exception_Monad_Or(M : MONAD_OR_BASE) : MONAD_EXCEPTION_BASE where type 'p1 exn = unit =
struct

open M
type 'p1 exn = unit

val throw = zero
val catch = or_lazy

end

(* adapted from Haskell's free package https://hackage.haskell.org/package/free *)
functor Free_Monad_Trans(structure F : FUNCTOR_BASE; structure M : MONAD_BASE) : MONAD_TRANS =
struct

structure M = M

datatype ('p1, 'a, 'b) freef = Pure of 'a | Free of ('p1, 'b) F.t
datatype ('p1, 'a) freet = FreeT of ('p1, ('p1, 'a, ('p1, 'a) freet) freef) M.t

fun runFreeT (FreeT m) = m

type ('p1, 'a) t = ('p1, 'a) freet

fun lift x = FreeT (M.map Pure x)

fun map f (FreeT m) =
  let fun f' (Pure x) = Pure (f x)
        | f' (Free xs) = Free (F.map (map f) xs)
  in FreeT (M.map f' m) end

fun pure a = FreeT (M.pure (Pure a))

fun bind (FreeT m) f = FreeT (M.bind m (fn Pure a => runFreeT (f a)
  | Free ms => M.pure (Free (F.map (fn m => bind m f) ms))))
fun m1 <*> m2 = bind m1 (fn f => bind m2 (fn x => pure (f x)))

end

