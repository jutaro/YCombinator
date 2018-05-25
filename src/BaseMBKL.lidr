= Base : Combinator Bases

> module BaseMBKL

> import Combinator
> import Reduction
> import Decidable.Equality

> %access public export
> %default total

A base with M, B, K and L

> data MBKL : Type where
>   M : MBKL
>   B : MBKL
>   K : MBKL
>   L : MBKL

> syntax ":M" = PrimComb M;
> syntax ":B" = PrimComb B;
> syntax ":K" = PrimComb K;
> syntax ":L" = PrimComb L;

> implementation Reduce MBKL where
>   reduceStep (App (PrimComb M) x) = Just (x # x)
>   reduceStep (App (App (App (PrimComb B) x) y) z) = Just (x # (y # z))
>   reduceStep (App (App (PrimComb K) x) y) = Just x
>   reduceStep (App (App (PrimComb L) x) y) = Just (x # (y # y))
>   reduceStep _ = Nothing

> data StepMBKL : Comb MBKL -> Comb MBKL -> Type where
>   MBKLStepM   : StepMBKL (:M # x) (x # x)
>   MBKLStepB   : StepMBKL (:B # x # y # z) (x # (y # z))
>   MBKLStepK   : StepMBKL (:K # x # y) x
>   MBKLStepL   : StepMBKL (:L # x # y) (x # (y # y))
>   MBKLAppL    : StepMBKL l res -> StepMBKL (l # r) (res # r)
>   MBKLAppR    : StepMBKL r res -> StepMBKL (l # r) (l # res)
>   MBKLSteps   : StepMBKL c1 c2 -> StepMBKL c2 c3 -> StepMBKL c1 c3
>   MBKLRev     : StepMBKL c1 c2 -> StepMBKL c2 c1
>   MBKLStepsR  : StepMBKL c1 c2 -> StepMBKL c3 c2 -> StepMBKL c1 c3
>   MBKLStepEq  : StepMBKL x x

> infixl 10 >-
> (>-) : StepMBKL c1 c2 -> StepMBKL c2 c3 -> StepMBKL c1 c3
> (>-) a b = MBKLSteps a b

> infixl 10 -<
> (-<) : StepMBKL c1 c2 -> StepMBKL c3 c2 -> StepMBKL c1 c3
> (-<) a b = MBKLStepsR a b

> eqStepMBKL : {a,b : Comb MBKL} -> StepMBKL a b -> a = b
> eqStepMBKL step = believe_me step

> combinatorExtensionality : {a, b : Comb MBKL} -> (x : Comb MBKL) -> a # x = b # x -> a = b
> combinatorExtensionality {a} {b} x = really_believe_me

> implementation Eq MBKL where
>   M == M = True
>   B == B = True
>   K == K = True
>   L == L = True
>   _ == _ = False

> bNotM : B = M -> Void
> bNotM Refl impossible

> bNotL : B = L -> Void
> bNotL Refl impossible

> kNotM : K = M -> Void
> kNotM Refl impossible

> kNotB : K = B -> Void
> kNotB Refl impossible

> kNotL : K = L -> Void
> kNotL Refl impossible

> lNotM : L = M -> Void
> lNotM Refl impossible

> implementation DecEq MBKL where
>   decEq M M = Yes Refl
>   decEq B B = Yes Refl
>   decEq K K = Yes Refl
>   decEq L L = Yes Refl
>   decEq B M = No bNotM
>   decEq B K = No (negEqSym kNotB)
>   decEq B L = No bNotL
>   decEq M B = No (negEqSym bNotM)
>   decEq M K = No (negEqSym kNotM)
>   decEq M L = No (negEqSym lNotM)
>   decEq K M = No kNotM
>   decEq K B = No kNotB
>   decEq K L = No kNotL
>   decEq L M = No lNotM
>   decEq L B = No (negEqSym bNotL)
>   decEq L K = No (negEqSym kNotL)

> implementation Show MBKL where
>   show M = ":M"
>   show B = ":B"
>   show K = ":K"
>   show L = ":L"
