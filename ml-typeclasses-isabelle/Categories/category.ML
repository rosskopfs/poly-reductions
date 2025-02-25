(*  Title:  category.ML
    Author: Kevin Kappelmann

Basic typeclasses related to category theory, inspired by the Haskell base package.

See typeclass_base.ML for an explanation of the 'pi type variables.
*)
infix 1 >>>
infix 1 ***
infix 1 &&&

signature SEMI_CATEGORY_BASE =
sig
  type ('p1, 'a, 'b) cat
  val comp : ('p1, 'b, 'c) cat -> ('p1, 'a, 'b) cat -> ('p1, 'a, 'c) cat
end

signature SEMI_CATEGORY =
sig
  include SEMI_CATEGORY_BASE
  val >>> : ('p1, 'a, 'b) cat * ('p1, 'b, 'c) cat -> ('p1, 'a, 'c) cat
  val o : ('p1, 'b, 'c) cat * ('p1, 'a, 'b) cat -> ('p1, 'a, 'c) cat
end

functor Semi_Category(SC : SEMI_CATEGORY_BASE) : SEMI_CATEGORY =
struct

open SC
fun f >>> g = comp g f
fun f o g = comp f g

end

signature CATEGORY_BASE =
sig
  include SEMI_CATEGORY_BASE

  (*unit argument to fight ML's value restriction*)
  val id : unit -> ('p1, 'a, 'a) cat
end

signature CATEGORY =
sig
  include CATEGORY_BASE
  val repeatn : int -> ('p1, 'a, 'a) cat -> ('p1, 'a, 'a) cat
end

functor Category(C : CATEGORY_BASE) : CATEGORY =
struct
open C
fun repeatn n f = if n <= 0 then id () else comp (repeatn (n - 1) f) f
end

signature ARROW_BASE =
sig
  include CATEGORY_BASE
  val arr : ('a -> 'b) -> ('p1, 'a, 'b) cat
  val *** : ('p1, 'a, 'b) cat * ('p1, 'c, 'd) cat -> ('p1, ('a * 'c), ('b * 'd)) cat
end

signature ARROW =
sig
  include ARROW_BASE

  val first : ('p1, 'a, 'b) cat -> ('p1, ('a * 'c), ('b * 'c)) cat
  val second : ('p1, 'a, 'b) cat -> ('p1, ('c * 'a), ('c * 'b)) cat

  val &&& : ('p1, 'a, 'b) cat * ('p1, 'a, 'c) cat -> ('p1, 'a, ('b * 'c)) cat

  val K : 'a -> ('p1, 'b, 'a) cat
  val curry : ('p1, ('a * 'b), 'c) cat -> 'a -> ('p1, 'b, 'c) cat
end

functor Arrow(A : ARROW_BASE) : ARROW =
struct

open A
fun first f = f *** id ()
fun second f = id () *** f

fun f &&& g = comp (f *** g) (arr (fn b => (b, b)))

fun K x = arr (fn _ => x)
fun curry f i = comp f (K i &&& id ())

end

signature ARROW_APPLY_BASE =
sig
  include ARROW_BASE
  val app : ('p1, ('p1, 'a, 'b) cat * 'a, 'b) cat
end

signature ARROW_APPLY =
sig
  include ARROW_APPLY_BASE
  val uncurry : ('a -> ('p1, 'b, 'c) cat) -> ('p1, ('a * 'b), 'c) cat
  val app' : 'a -> ('p1, ('p1, 'a, 'b) cat, 'b) cat
end

functor Arrow_Apply(A : ARROW_APPLY_BASE) : ARROW_APPLY =
struct

open A
local structure SC = Semi_Category(A) open SC
in
fun uncurry f = arr (apfst f) >>> app
fun app' x = arr (rpair x) >>> app
end

end

signature ARROW_ARROW_APPLY =
sig
  structure A : ARROW
  structure AA : ARROW_APPLY
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) A.cat
end

signature ARROW_ZERO_BASE =
sig
  include ARROW_BASE
  val zero : unit -> ('p1, 'a, 'b) cat
end

signature ARROW_PLUS_BASE =
sig
  include ARROW_ZERO_BASE
  val plus : ('p1, 'a, 'b) cat -> ('p1, 'a, 'b) cat -> ('p1, 'a, 'b) cat
end

signature ARROW_OR_BASE =
sig
  include ARROW_ZERO_BASE
  val or : ('p1, 'a, 'b) cat -> ('p1, 'a, 'b) cat -> ('p1, 'a, 'b) cat
end

signature ARROW_EXCEPTION_BASE =
sig
  include ARROW_BASE
  type 'p1 exn

  val throw : ('p1, 'p1 exn, 'a) cat
  val catch : ('p1, 'a, 'b) cat -> ('p1, 'a * 'p1 exn, 'b) cat -> ('p1, 'a, 'b) cat
end

signature ARROW_EXCEPTION =
sig
  include ARROW_EXCEPTION_BASE

  val throw' : 'p1 exn -> ('p1, 'a, 'b) cat
  val catch' : ('p1, 'a, 'b) cat -> ('p1, 'a, 'b) cat -> ('p1, 'a, 'b) cat
  val try : ('p1, 'a, 'a) cat -> ('p1, 'a, 'a) cat
end

functor Arrow_Exception(A : ARROW_EXCEPTION_BASE) : ARROW_EXCEPTION =
struct

open A

fun throw' x = comp throw (arr (K x))
fun catch' f g = catch f (comp g (arr fst))
fun try f = catch' f (id ())

end

signature ARROW_CHOICE_BASE =
sig
  include ARROW_BASE
  val cases : ('p1, 'a, 'c) cat -> ('p1, 'b, 'd) cat ->
    ('p1, ('a, 'b) Either.either, ('c, 'd) Either.either) cat
  val merge : ('p1, 'a, 'c) cat -> ('p1, 'b, 'c) cat ->
    ('p1, ('a, 'b) Either.either, 'c) cat
end

signature ARROW_CHOICE =
sig
  include ARROW_CHOICE_BASE
  val opt : ('p1, unit, 'b) cat -> ('p1, 'a, 'b) cat -> ('p1, 'a option, 'b) cat
end

functor Arrow_Choice(A : ARROW_CHOICE_BASE) : ARROW_CHOICE =
struct
open A
fun opt fnone fsome = comp (merge fnone fsome) (arr Either.of_opt)
end
