= Base : Combinator Bases

> module BaseMBK

> import Combinator
> import Decidable.Equality

> %access public export
> %default total

A base with M and B

> data MBK : Type where
>   M : MBK
>   B : MBK
>   K : MBK

> syntax ":M" = PrimComb M;
> syntax ":B" = PrimComb B;
> syntax ":K" = PrimComb B;

> implementation Reduce MBK where
>   reduceStep (App (PrimComb M) x) = Just (x # x)
>   reduceStep (App (App (App (PrimComb B) x) y) z) = Just (x # (y # z))
>   reduceStep (App (App (PrimComb K) x) y) = Just x
>   reduceStep _ = Nothing

> data StepMBK : Comb MBK -> Comb MBK -> Type where
>   MBKStepM   : StepMBK (:M # x) (x # x)
>   MBKStepB   : StepMBK (:B # x # y # z) (x # (y # z))
>   MBKStepK   : StepMBK (:K # x # y) x
>   MBKAppL    : StepMBK l res -> StepMBK (l # r) (res # r)
>   MBKAppR    : StepMBK r res -> StepMBK (l # r) (l # res)
>   MBKSteps   : StepMBK c1 c2 -> StepMBK c2 c3 -> StepMBK c1 c3
>   MBKStepEq  : StepMBK x x

> infixl 10 >-
> (>-) : StepMBK c1 c2 -> StepMBK c2 c3 -> StepMBK c1 c3
> (>-) a b = MBKSteps a b

> eqStepMBK : {a,b : Comb MBK} -> StepMBK a b -> a = b
> eqStepMBK step = believe_me step

> implementation Eq MBK where
>   M == M = True
>   B == B = True
>   K == K = True
>   _ == _ = False

> bNotM : B = M -> Void
> bNotM Refl impossible

> kNotM : K = M -> Void
> kNotM Refl impossible

> kNotB : K = B -> Void
> kNotB Refl impossible

> implementation DecEq MBK where
>   decEq M M = Yes Refl
>   decEq B B = Yes Refl
>   decEq K K = Yes Refl
>   decEq B M = No bNotM
>   decEq B K = No (negEqSym kNotB)
>   decEq M B = No (negEqSym bNotM)
>   decEq M K = No (negEqSym kNotM)
>   decEq K M = No kNotM
>   decEq K B = No kNotB

> implementation Show MBK where
>   show M = ":M"
>   show B = ":B"
>   show K = ":K"
