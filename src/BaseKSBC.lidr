= Base KSBC : A base with combinators K, S, I, B, W

> module BaseKSBC

> import Combinator
> import Reduction
> import RevReduction
> import Decidable.Equality
> import Other

> %access public export
> %default total

A base with combinators K, S, B and C

> data KSBC : Type where
>   K : KSBC
>   S : KSBC
>   B : KSBC
>   C : KSBC

> syntax ":K" = PrimComb K 2;
> syntax ":S" = PrimComb S 3;
> syntax ":B" = PrimComb B 3;
> syntax ":C" = PrimComb C 2;

> data PrimStep : Comb KSBC -> Comb KSBC -> Type where
>   StepK   : {x, y: Comb KSBC} -> Reduce KSBC => PrimStep (:K # x # y) x
>   StepS   : {x, y, z: Comb KSBC} -> Reduce KSBC => PrimStep (:S # x # y # z) ((x # z) # (y # z))
>   StepB   : {x, y, z: Comb KSBC} -> Reduce KSBC => PrimStep (:B # x # y # z) (x # (y # z))
>   StepC   : {x, y, z: Comb KSBC} -> Reduce KSBC => PrimStep (:C # x # y # z) (x # z # y)

> implementation Eq KSBC where
>   K == K = True
>   S == S = True
>   B == B = True
>   C == C = True
>   _ == _ = False

> Uninhabited (K = BaseKSBC.S) where
>   uninhabited Refl impossible

> Uninhabited (K = B) where
>   uninhabited Refl impossible

> Uninhabited (K = C) where
>   uninhabited Refl impossible

> Uninhabited (BaseKSBC.S = B) where
>   uninhabited Refl impossible

> Uninhabited (BaseKSBC.S = C) where
>   uninhabited Refl impossible

> Uninhabited (B = C) where
>   uninhabited Refl impossible

> implementation DecEq KSBC where
>   decEq K K = Yes Refl
>   decEq S S = Yes Refl
>   decEq B B = Yes Refl
>   decEq C C = Yes Refl

>   decEq K S = No absurd
>   decEq K B = No absurd
>   decEq K C = No absurd
>   decEq S B = No absurd
>   decEq S C = No absurd
>   decEq B C = No absurd

>   decEq S K = No absurdEqSym
>   decEq B K = No absurdEqSym
>   decEq C K = No absurdEqSym
>   decEq B S = No absurdEqSym
>   decEq C S = No absurdEqSym
>   decEq C B = No absurdEqSym

> implementation Show KSBC where
>   show K = ":K"
>   show S = ":S"
>   show B = ":B"
>   show C = ":C"

> implementation Reduce KSBC where
>   reduceStep (App (App (PrimComb K _) x) y) = Just x
>   reduceStep (App (App (App (PrimComb S _) x) y) z) = Just ((x # z) # (y # z))
>   reduceStep (App (App (App (PrimComb B _) x) y) z) = Just (x # (y # z))
>   reduceStep (App (App (App (PrimComb C _) x) y) z) = Just (x # z # y)
>   reduceStep _ = Nothing
>   PrimRed = PrimStep

> stepK : {x, y: Comb KSBC} -> Step (:K # x # y) x
> stepK = Prim StepK

> stepS : {x, y, z: Comb KSBC} -> Step (:S # x # y # z) ((x # z) # (y # z))
> stepS = Prim StepS

> stepB : {x, y, z: Comb KSBC} -> Step (:B # x # y # z) (x # (y # z))
> stepB = Prim StepB

> stepC : {x, y: Comb KSBC} -> Step (:C # x # y # z) (x # z # y)
> stepC = Prim StepC
