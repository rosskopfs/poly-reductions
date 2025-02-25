(*  Title:  icategory.ML
    Author: Kevin Kappelmann

Basic indexed typeclasses related to category theory,
inspired by the Haskell Prelude and "Parameterised Notions of Computation" by Robert Atkey.
*)
signature ISEMI_CATEGORY_BASE =
sig
  type ('p1, 'i, 'o, 'a, 'b) cat
  val comp : ('p1, 'j, 'k, 'b, 'c) cat -> ('p1, 'i, 'j, 'a, 'b) cat -> ('p1, 'i, 'k, 'a, 'c) cat
end

signature ISEMI_CATEGORY =
sig
  include ISEMI_CATEGORY_BASE
  val >>> : ('p1, 'i, 'j, 'a, 'b) cat * ('p1, 'j, 'k, 'b, 'c) cat -> ('p1, 'i, 'k, 'a, 'c) cat
  val o : ('p1, 'j, 'k, 'b, 'c) cat * ('p1, 'i, 'j, 'a, 'b) cat -> ('p1, 'i, 'k, 'a, 'c) cat
end

functor ISemi_Category(C : ISEMI_CATEGORY_BASE) : ISEMI_CATEGORY =
struct
open C
fun f >>> g = comp g f
fun f o g = comp f g
end

signature ICATEGORY_BASE =
sig
  include ISEMI_CATEGORY_BASE
  (*unit argument to fight ML's value restriction*)
  val id : unit -> ('p1, 'i, 'i, 'a, 'a) cat
end

signature ICATEGORY =
sig
  include ICATEGORY_BASE
  val repeatn : int -> ('p1, 'i, 'i, 'a, 'a) cat -> ('p1, 'i, 'i, 'a, 'a) cat
end

functor ICategory(C : ICATEGORY_BASE) : ICATEGORY =
struct
open C
fun repeatn n f = if n <= 0 then id () else comp (repeatn (n - 1) f) f
end

signature IARROW_BASE =
sig
  include ICATEGORY_BASE
  val arr : ('a -> 'b) -> ('p1, 'i, 'i, 'a, 'b) cat
  val *** : ('p1, 'i, 'j, 'a, 'b) cat * ('p1, 'j, 'k, 'c, 'd) cat ->
    ('p1, 'i, 'k, ('a * 'c), ('b * 'd)) cat
end

signature IARROW =
sig
include IARROW_BASE

val first : ('p1, 'i, 'o, 'a, 'b) cat -> ('p1, 'i, 'o, ('a * 'c), ('b * 'c)) cat
val second : ('p1, 'i, 'o, 'a, 'b) cat -> ('p1, 'i, 'o, ('c * 'a), ('c * 'b)) cat

val &&& : ('p1, 'i, 'j, 'a, 'b) cat * ('p1, 'j, 'k, 'a, 'c) cat -> ('p1, 'i, 'k, 'a, 'b * 'c) cat

val K : 'a -> ('p1, 'i, 'i, 'b, 'a) cat
val curry : ('p1, 'i, 'o, 'a * 'b, 'c) cat -> 'a -> ('p1, 'i, 'o, 'b, 'c) cat
end

functor IArrow(A : IARROW_BASE) : IARROW =
struct

open A
fun first f = f *** id ()
fun second f = id () *** f

fun f &&& g = comp (f *** g) (arr (fn b => (b, b)))

fun K x = arr (fn _ => x)
fun curry m i = comp m (K i &&& id ())

end

signature IARROW_APPLY_BASE =
sig
  include IARROW_BASE
  val app : ('p1, 'i, 'j, ('p1, 'i, 'j, 'a, 'b) cat * 'a, 'b) cat
end

signature IARROW_APPLY =
sig
  include IARROW_APPLY_BASE
  val uncurry : ('a -> ('p1, 'i, 'j, 'b, 'c) cat) -> ('p1, 'i, 'j, 'a * 'b, 'c) cat
  val app' : 'a -> ('p1, 'i, 'j, ('p1, 'i, 'j, 'a, 'b) cat, 'b) cat
end

functor IArrow_Apply(A : IARROW_APPLY_BASE) : IARROW_APPLY =
struct
open A
local structure SC = ISemi_Category(A) open SC
in
fun uncurry f = arr (apfst f) >>> app
fun app' x = arr (rpair x) >>> app
end
end

signature IARROW_ZERO_BASE =
sig
  include IARROW_BASE
  val zero : unit -> ('p1, 'i, 'i, 'a, 'b) cat
end

signature IARROW_PLUS_BASE =
sig
  include IARROW_ZERO_BASE
  val plus : ('p1, 'i, 'j, 'a, 'b) cat -> ('p1, 'i, 'j, 'a, 'b) cat -> ('p1, 'i, 'j, 'a, 'b) cat
end

signature IARROW_OR_BASE =
sig
  include IARROW_ZERO_BASE
  val or : ('p1, 'i, 'j, 'a, 'b) cat -> ('p1, 'i, 'j, 'a, 'b) cat -> ('p1, 'i, 'j, 'a, 'b) cat
end

signature IARROW_EXCEPTION_BASE =
sig
  include IARROW_BASE
  type 'p1 exn

  val throw : ('p1, 'i, 'i, 'p1 exn, 'a) cat
  val catch : ('p1, 'i, 'j, 'a, 'b) cat -> ('p1, 'i, 'j, 'a * 'p1 exn, 'b) cat ->
    ('p1, 'i, 'j, 'a, 'b) cat
end

signature IARROW_EXCEPTION =
sig
  include IARROW_EXCEPTION_BASE
  val throw' : 'p1 exn -> ('p1, 'i, 'i, 'a, 'b) cat
  val catch' : ('p1, 'i, 'j, 'a, 'b) cat -> ('p1, 'i, 'j, 'a, 'b) cat -> ('p1, 'i, 'j, 'a, 'b) cat
  val try : ('p1, 'i, 'i, 'a, 'a) cat -> ('p1, 'i, 'i, 'a, 'a) cat
end

functor IArrow_Exception(A : IARROW_EXCEPTION_BASE) : IARROW_EXCEPTION =
struct
open A

fun throw' x = comp throw (arr (K x))
fun catch' f g = catch f (comp g (arr fst))
fun try f = catch' f (id ())
end

signature IARROW_CHOICE_BASE =
sig
  include IARROW_BASE
  val cases : ('p1, 'i, 'j, 'a, 'c) cat -> ('p1, 'i, 'j, 'b, 'd) cat ->
    ('p1, 'i, 'j, ('a, 'b) Either.either, ('c, 'd) Either.either) cat
  val merge : ('p1, 'i, 'j, 'a, 'c) cat -> ('p1, 'i, 'j, 'b, 'c) cat ->
    ('p1, 'i, 'j, ('a, 'b) Either.either, 'c) cat
end

signature IARROW_CHOICE =
sig
  include IARROW_CHOICE_BASE
  val opt : ('p1, 'i, 'j, unit, 'b) cat -> ('p1, 'i, 'j, 'a, 'b) cat -> ('p1, 'i, 'j, 'a option, 'b) cat
end

functor IArrow_Choice(A : IARROW_CHOICE_BASE) : IARROW_CHOICE =
struct
open A
fun opt fnone fsome = comp (merge fnone fsome) (arr Either.of_opt)
end
