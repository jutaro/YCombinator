= BaseKSDiamond : Proof diamond property of KS

> module BaseKSDiamond

> import Decidable.Equality
> import Control.Isomorphism
> import Combinator
> import Reduction
> import BaseKS

> %access public export
> %default total

> data NotNormalForm : Comb KS -> Type where
>   NotNormal : (a : Comb KS) -> (b : Comb KS ** Step' a b) -> NotNormalForm a

> data NormalForm : Comb KS -> Type where
>   Normal : (a : Comb KS) -> Not (b : Comb KS ** Step' a b) -> NormalForm a

> forallToExistence : {X : Type} -> {P: X -> X -> Type} -> (a : X) -> ((b : X) -> Not (P a b)) -> Not (b : X ** P a b)
> forallToExistence a hyp (b ** p2) = hyp b p2

> normalKSPrf: (b : Comb KS) -> Step' (:K # :S) b -> Void
> normalKSPrf (:K) step =
>   case step of
>     Prim' _ impossible
>     AppL' _ impossible
>     AppR' _ impossible
> normalKSPrf (:S) step =
>   case step of
>     Prim' _ impossible
>     AppL' _ impossible
>     AppR' _ impossible
> normalKSPrf (App l r) step =
>   case step of
>     Prim' _ impossible
>     AppL' s2 => case s2 of
>       Prim' _ impossible
>       AppL' _ impossible
>       AppR' _ impossible
>     AppR' s2 => case s2 of
>       Prim' _ impossible
>       AppL' _ impossible
>       AppR' _ impossible

> normalKS : NormalForm (:K # :S)
> normalKS = Normal (:K # :S) (forallToExistence (:K # :S) normalKSPrf)

> notNormalKSS : NotNormalForm (:K # :S # :S)
> notNormalKSS = NotNormal (:K # :S # :S) (:S ** Prim' StepK)



> {-
> isoLemma : (P: Type -> Type) -> Iso (Not (b : Type ** P b)) ({b : Type} -> Not (P b))
> isoLemma P = MkIso from to toFrom fromTo
>   where from : (Not (b : Type ** P b)) -> (b : Type) -> Not (P b)
>         from h1 b h3 = h1 (b ** h3)
>         to : ((b : Type) -> Not (P b)) -> (Not (b : Type ** P b))
>         to h1 (b ** p) = h1 b p
>         toFrom : (y: (b : Type) -> Not (P b)) -> from (to y) = y
>         toFrom y = ?h3
>         fromTo : (x : Not (b : Type ** P b)) -> to (from x) = x
>         fromTo x = ?h4
> -}

> isNormalTest1 : isNormalForm (:K # :S) = True
> isNormalTest1 = Refl

> isNormalTest2 : isNormalForm (:K # :S # :S) = False
> isNormalTest2 = Refl
