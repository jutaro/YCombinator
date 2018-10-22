= Relation : Relations with Multi Pathes

> module Relation

> %access public export
> %default total

A _binary relation_ on a set [X] is a family of propositions
parameterized by two elements of [X] -- i.e., a proposition about
pairs of elements of [X].  *)

> Relation : Type -> Type
> Relation t = t -> t -> Type

> deterministic : {xt: Type} -> (r: Relation xt) -> Type
> deterministic {xt} r = (x, y1, y2: xt) -> r x y1 -> r x y2 -> y1 = y2

> data Multi: {X: Type} -> Relation X -> Relation X where
>   MultiRefl  : {X: Type} -> {R: Relation X} -> {x : X} ->  Multi R x x
>   MultiStep  : {X: Type} -> {R: Relation X} -> {x, y, z : X} -> R x y -> Multi R y z -> Multi R x z

> multiR : {X: Type} -> {R: Relation X} -> (x,y: X) -> R x y -> (Multi R) x y
> multiR x y h = MultiStep h (MultiRefl)

> multiTrans: {X:Type} -> {R: Relation X} -> {x, y, z : X} ->
>   Multi R x y  -> Multi R y z -> Multi R x z
> multiTrans m1 m2 =
>    case m1 of
>      MultiRefl => m2
>      MultiStep r mx =>
>         let indHyp = multiTrans mx m2
>         in MultiStep r indHyp
