(*  Title:  bi_typeclass.ML
    Author: Kevin Kappelmann
*)
signature BI_FUNCTOR_FIRST =
sig
  type ('p1, 'a, 'b) t
  val first : ('a -> 'c) -> ('p1, 'a, 'b) t -> ('p1, 'c, 'b) t
end

signature BI_FUNCTOR_SECOND =
sig
  type ('p1, 'a, 'b) t
  val second : ('b -> 'c) -> ('p1, 'a, 'b) t -> ('p1, 'a, 'c) t
end

signature BI_FUNCTOR_BASE =
sig
  type ('p1, 'a, 'b) t
  val bimap : ('a -> 'c) -> ('b -> 'd) -> ('p1, 'a, 'b) t -> ('p1, 'c, 'd) t
end

signature BI_FUNCTOR =
sig
  include BI_FUNCTOR_BASE
  val first : ('a -> 'c) -> ('p1, 'a, 'b) t -> ('p1, 'c, 'b) t
  val second : ('b -> 'd) -> ('p1, 'a, 'b) t -> ('p1, 'a, 'd) t
end

functor Bi_Functor(B : BI_FUNCTOR_BASE) : BI_FUNCTOR =
struct
open B
fun first f = B.bimap f I
fun second f = B.bimap I f
end