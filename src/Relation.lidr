= Relation : Relations with Multi Pathes

> module Relation

> %access public export
> %default total

A _binary relation_ on a set [X] is a family of propositions
parameterized by two elements of [X] -- i.e., a proposition about
pairs of elements of [X].  *)

> Relation : Type -> Type
> Relation t = t -> t -> Type

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

== Properties of relations

> deterministic : {xt: Type} -> (r: Relation xt) -> Type
> deterministic {xt} r = (x, y1, y2: xt) -> r x y1 -> r x y2 -> y1 = y2

> normalForm : {xt:Type} -> Relation xt -> xt -> Type
> normalForm r t = Not (t' ** r t t')

> symmetric : {xt:Type} -> Relation xt -> Type
> symmetric {xt} r = {x,y : xt} -> r x y -> r y x

> reflexive : {xt:Type} -> Relation xt -> Type
> reflexive {xt} r = {x : xt} -> r x x

> confluent : {xt: Type} -> (r: Relation xt) -> Type
> confluent {xt} r = (x, y1, y2: xt) -> r x y1 -> r x y2 -> (z: xt ** (r y1 z, r y2 z))

> symmetricIsConfluent : {xt: Type} -> (rt : Relation xt) -> symmetric rt -> confluent rt
> symmetricIsConfluent r sym = \ x, y1, y2, r1, r2 => (x ** (sym r1, sym r2))

> confluenceToMulti : {xt: Type} -> {r: Relation xt} -> confluent r -> confluent (Multi r)
> confluenceToMulti {r} hyp x y1 y2 m1 m2 =
>   case m1 of
>     MultiRefl =>
>       case m2 of
>         MultiRefl => (x ** (MultiRefl, MultiRefl))
>         MultiStep st ms => (y2 ** (m2,MultiRefl))
>     MultiStep st1 {y=y1'} ms1 =>
>       case m2 of
>         MultiRefl => (y1 ** (MultiRefl,m1))

-- >           -- case is redundant
-- >         MultiStep st2 MultiRefl =>
-- >           let (z1 ** (hl1,hr1)) = hyp x y1' y2 st1 st2
-- >               (zo ** (hlo,hro)) = confluenceToMulti {r} hyp y1' y1 z1
-- >                   ms1 (assert_smaller m2 (MultiStep hl1 MultiRefl))
-- >           in (zo ** (hlo,multiTrans (MultiStep hr1 MultiRefl) hro))

>         MultiStep st2 {y=y2'} ms2 =>
>           let (z1 ** (hl1,hr1)) = hyp x y1' y2' st1 st2
>               (zo ** (hlo,hro)) = confluenceToMulti {r} hyp y1' y1 z1
>                   ms1 (assert_smaller m2 (MultiStep hl1 MultiRefl))
>               (zu ** (hlu,hru)) = confluenceToMulti {r} hyp y2' y2 z1
>                   ms2 (assert_smaller m2 (MultiStep hr1 MultiRefl))
>               (z **  (hlf,hrf)) = confluenceToMulti {r} hyp z1 zo zu
>                   hro (assert_smaller m2 hru) -- how to justify this assert_smaller?
>           in (z ** (multiTrans hlo hlf,multiTrans hlu hrf))

> -- Doesn't really belong here

> forallToExistence : {X: Type} -> {P: X -> Type} -> ((b : X) -> Not (P b)) -> Not (b : X ** P b)
> forallToExistence hyp (b ** p2) = hyp b p2
