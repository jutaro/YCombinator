= BaseMBKL : A base with combinators M, B, K and L

> module BaseMBKL

> import Combinator
> import Reduction
> import RevReduction
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

> data PrimStep : Comb MBKL -> Comb MBKL -> Type where
>   StepM   : {x : Comb MBKL} -> Reduce MBKL => PrimStep (:M # x) (x # x)
>   StepB   : {x, y, z : Comb MBKL} -> Reduce MBKL => PrimStep (:B # x # y # z) (x # (y # z))
>   StepK   : {x, y : Comb MBKL} -> Reduce MBKL => PrimStep (:K # x # y) x
>   StepL   : {x, y : Comb MBKL} -> Reduce MBKL => PrimStep (:L # x # y) (x # (y # y))

> implementation Reduce MBKL where
>   reduceStep (App (PrimComb M) x) = Just (x # x)
>   reduceStep (App (App (App (PrimComb B) x) y) z) = Just (x # (y # z))
>   reduceStep (App (App (PrimComb K) x) y) = Just x
>   reduceStep (App (App (PrimComb L) x) y) = Just (x # (y # y))
>   reduceStep _ = Nothing
>   PrimRed = PrimStep

> stepM : {x : Comb MBKL} -> Step (:M # x) (x # x)
> stepM = Prim StepM

> stepB : {x, y, z: Comb MBKL} -> Step (:B # x # y # z) (x # (y # z))
> stepB = Prim StepB

> stepK : {x, y : Comb MBKL} -> Step (:K # x # y) x
> stepK = Prim StepK

> stepL : {x, y : Comb MBKL} -> Step (:L # x # y) (x # (y # y))
> stepL = Prim StepL

> stepM' : {x : Comb MBKL} -> Step' (:M # x) (x # x)
> stepM' = Prim' StepM

> stepB' : {x, y, z: Comb MBKL} -> Step' (:B # x # y # z) (x # (y # z))
> stepB' = Prim' StepB

> stepK' : {x, y : Comb MBKL} -> Step' (:K # x # y) x
> stepK' = Prim' StepK

> stepL' : {x, y : Comb MBKL} -> Step' (:L # x # y) (x # (y # y))
> stepL' = Prim' StepL

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
