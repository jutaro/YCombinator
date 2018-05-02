= Base : Combinator Bases

> module BaseMB

> import Combinator
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

> data StepMB : Comb MB -> Comb MB -> Type where
>   MBStepM   : StepMB (:M # x) (x # x)
>   MBStepB   : StepMB (:B # x # y # z) (x # (y # z))
>   MBAppL    : StepMB l res -> StepMB (l # r) (res # r)
>   MBAppR    : StepMB r res -> StepMB (l # r) (l # res)
>   MBSteps   : StepMB c1 c2 -> StepMB c2 c3 -> StepMB c1 c3
>   MBStepEq  : StepMB x x

> infixl 10 >-
> (>-) : StepMB c1 c2 -> StepMB c2 c3 -> StepMB c1 c3
> (>-) a b = MBSteps a b

> eqStepMB : {a,b : Comb MB} -> StepMB a b -> a = b
> eqStepMB step = believe_me step

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
