= BaseMB : A base with combinators M and B

> module BaseMB

> import Combinator
> import Reduction
> import Decidable.Equality
> import Other

> %access public export
> %default total

A base with M and B

> data MB : Type where
>   M : MB
>   B : MB

> syntax ":M" = PrimComb M 1;
> syntax ":B" = PrimComb B 3;

> data PrimStep : Comb MB -> Comb MB -> Type where
>   StepM   : {x: Comb MB} -> Reduce MB => PrimStep (:M # x) (x # x)
>   StepB   : {x, y: Comb MB} -> Reduce MB => PrimStep (:B # x # y # z) (x # (y # z))

> implementation Eq MB where
>   M == M = True
>   B == B = True
>   _ == _ = False

> Uninhabited (B = M) where
>   uninhabited Refl impossible

> implementation DecEq MB where
>   decEq M M = Yes Refl
>   decEq B B = Yes Refl
>   decEq B M = No absurd
>   decEq M B = No absurdEqSym

> implementation Show MB where
>   show M = ":M"
>   show B = ":B"

> implementation Reduce MB where
>   reduceStep (App (PrimComb M _) x) = Just (x # x)
>   reduceStep (App (App (App (PrimComb B _) x) y) z) = Just (x # (y # z))
>   reduceStep _ = Nothing
>   PrimRed = PrimStep

> stepM : {x : Comb MB} -> Step (:M # x) (x # x)
> stepM = Prim StepM

> stepB : {x, y, z: Comb MB} -> Step (:B # x # y # z) (x # (y # z))
> stepB = Prim StepB
