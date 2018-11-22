= Lib.Other : Collection of code which don't belong anywhere else

> module Lib.Other

> %access public export
> %default total

> infixl 7 .&.
> (.&.) : Int -> Int -> Int
> (.&.) = prim__andInt

> infixl 5 .|.
> (.|.) : Int -> Int -> Int
> (.|.) = prim__orInt

> forallToExistence : {xty: Type} -> {pty: xty -> Type} -> ((b : xty) -> Not (pty b)) -> Not (b : xty ** pty b)
> forallToExistence hyp (b ** p2) = hyp b p2

> iff : (p, q : Type) -> Type
> iff p q = (p -> q, q -> p)
>
> infixl 9 <->
> (<->) : (p : Type) -> (q : Type) -> Type
> (<->) = iff

> absurdEqSym : Uninhabited (a = b) => Not (b = a)
> absurdEqSym = uninhabited . sym

> not_true_is_false : (b : Bool) -> Not (b = True) -> b = False
> not_true_is_false False h = Refl
> not_true_is_false True h = absurd $ h Refl

> not_true_iff_false : (Not (b = True)) <-> (b = False)
> not_true_iff_false {b} = (not_true_is_false b, not_true_and_false b)
>   where
>     not_true_and_false : (b : Bool) -> (b = False) -> Not (b = True)
>     not_true_and_false False _ Refl impossible
>     not_true_and_false True Refl _ impossible
