= Lib : Additions for base library

> module Lib

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
>   Multi_refl  : {X: Type} -> {R: Relation X} -> {x : X} ->  Multi R x x
>   Multi_step  : {X: Type} -> {R: Relation X} -> {x, y, z : X} -> R x y -> Multi R y z -> Multi R x z

> multi_R : {X: Type} -> {R: Relation X} -> (x,y: X) -> R x y -> (Multi R) x y
> multi_R x y h = Multi_step h (Multi_refl)

> multi_trans: {X:Type} -> {R: Relation X} -> {x, y, z : X} ->
>   Multi R x y  -> Multi R y z -> Multi R x z
> multi_trans m1 m2 =
>    case m1 of
>      Multi_refl => m2
>      Multi_step r mx =>
>         let indHyp = multi_trans mx m2
>         in Multi_step r indHyp
