= BaseMBKL : A base with combinators M, B, K and L

> module BaseMBKL

> import Combinator
> import Reduction
> import RevReduction
> import Decidable.Equality
> import Other

> %access public export
> %default total

A base with M, B, K and L

> data MBKL : Type where
>   M : MBKL
>   B : MBKL
>   K : MBKL
>   L : MBKL

> syntax ":M" = PrimComb M 1;
> syntax ":B" = PrimComb B 3;
> syntax ":K" = PrimComb K 2;
> syntax ":L" = PrimComb L 2;

> data PrimStep : Comb MBKL -> Comb MBKL -> Type where
>   StepM   : {x : Comb MBKL} -> Reduce MBKL => PrimStep (:M # x) (x # x)
>   StepB   : {x, y, z : Comb MBKL} -> Reduce MBKL => PrimStep (:B # x # y # z) (x # (y # z))
>   StepK   : {x, y : Comb MBKL} -> Reduce MBKL => PrimStep (:K # x # y) x
>   StepL   : {x, y : Comb MBKL} -> Reduce MBKL => PrimStep (:L # x # y) (x # (y # y))

> implementation Eq MBKL where
>   M == M = True
>   B == B = True
>   K == K = True
>   L == L = True
>   _ == _ = False

> Uninhabited (B = M) where
>   uninhabited Refl impossible

> Uninhabited (B = L) where
>   uninhabited Refl impossible

> Uninhabited (K = M) where
>   uninhabited Refl impossible

> Uninhabited (K = B) where
>   uninhabited Refl impossible

> Uninhabited (K = L) where
>   uninhabited Refl impossible

> Uninhabited (L = M) where
>   uninhabited Refl impossible

> implementation DecEq MBKL where
>   decEq M M = Yes Refl
>   decEq B B = Yes Refl
>   decEq K K = Yes Refl
>   decEq L L = Yes Refl
>   decEq B M = No absurd
>   decEq B K = No absurdEqSym
>   decEq B L = No absurd
>   decEq M B = No absurdEqSym
>   decEq M K = No absurdEqSym
>   decEq M L = No absurdEqSym
>   decEq K M = No absurd
>   decEq K B = No absurd
>   decEq K L = No absurd
>   decEq L M = No absurd
>   decEq L B = No absurdEqSym
>   decEq L K = No absurdEqSym

> implementation Show MBKL where
>   show M = ":M"
>   show B = ":B"
>   show K = ":K"
>   show L = ":L"

> implementation Reduce MBKL where
>   reduceStep (App (PrimComb M _) x) = Just (x # x)
>   reduceStep (App (App (App (PrimComb B _) x) y) z) = Just (x # (y # z))
>   reduceStep (App (App (PrimComb K _) x) y) = Just x
>   reduceStep (App (App (PrimComb L _) x) y) = Just (x # (y # y))
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
