= Base : Combinator Bases

> module BaseMB

> import Combinator
> import Reduction
> import Decidable.Equality

> %access public export
> %default total

A base with M and B

> data MB : Type where
>   M : MB
>   B : MB

> syntax ":M" = PrimComb M;
> syntax ":B" = PrimComb B;

> implementation Reduce MB where
>   reduceStep (App (PrimComb M) x) = Just (x # x)
>   reduceStep (App (App (App (PrimComb B) x) y) z) = Just (x # (y # z))
>   reduceStep _ = Nothing

> data Step : Comb MB -> Comb MB -> Type where
>   StepM   : Step (:M # x) (x # x)
>   StepB   : Step (:B # x # y # z) (x # (y # z))
>   AppL    : Step l res -> Step (l # r) (res # r)
>   AppR    : Step r res -> Step (l # r) (l # res)
>   Steps   : Step c1 c2 -> Step c2 c3 -> Step c1 c3
>   StepEq  : Step x x

> infixl 10 >-
> (>-) : Step c1 c2 -> Step c2 c3 -> Step c1 c3
> (>-) a b = Steps a b

> eqStep : {a,b : Comb MB} -> Step a b -> a = b
> eqStep step = believe_me step

> implementation Eq MB where
>   M == M = True
>   B == B = True
>   _ == _ = False

> bNotM : B = M -> Void
> bNotM Refl impossible

> implementation DecEq MB where
>   decEq M M = Yes Refl
>   decEq B B = Yes Refl
>   decEq B M = No bNotM
>   decEq M B = No (negEqSym bNotM)

> implementation Show MB where
>   show M = ":M"
>   show B = ":B"
