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

> data Step : Comb MBKL -> Comb MBKL -> Type where
>   StepM   : Step (:M # x) (x # x)
>   StepB   : Step (:B # x # y # z) (x # (y # z))
>   StepK   : Step (:K # x # y) x
>   StepL   : Step (:L # x # y) (x # (y # y))
>   AppL    : Step l res -> Step (l # r) (res # r)
>   AppR    : Step r res -> Step (l # r) (l # res)
>   Steps   : Step c1 c2 -> Step c2 c3 -> Step c1 c3
>   Rev     : Step c1 c2 -> Step c2 c1
>   StepEq  : Step x x

> infixl 10 >-
> (>-) : Step c1 c2 -> Step c2 c3 -> Step c1 c3
> (>-) a b = Steps a b

> eqStep : {a,b : Comb MBKL} -> Step a b -> a = b
> eqStep step = believe_me step

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
