= Base KSIBC : A base with combinators K, S, I, B, W

> module BaseKSIBC

> import Combinator
> import Reduction
> import RevReduction
> import Decidable.Equality
> import Other

> %access public export
> %default total

A base with combinators K, S, I, B and C

> data KSIBC : Type where
>   K : KSIBC
>   S : KSIBC
>   I : KSIBC
>   B : KSIBC
>   C : KSIBC

> syntax ":K" = PrimComb K 2;
> syntax ":S" = PrimComb S 3;
> syntax ":I" = PrimComb I 1;
> syntax ":B" = PrimComb B 3;
> syntax ":C" = PrimComb C 2;

> data PrimStep : Comb KSIBC -> Comb KSIBC -> Type where
>   StepK   : {x, y: Comb KSIBC} -> Reduce KSIBC => PrimStep (:K # x # y) x
>   StepS   : {x, y, z: Comb KSIBC} -> Reduce KSIBC => PrimStep (:S # x # y # z) ((x # z) # (y # z))
>   StepI   : {x: Comb KSIBC} -> Reduce KSIBC => PrimStep (:I # x) x
>   StepB   : {x, y, z: Comb KSIBC} -> Reduce KSIBC => PrimStep (:B # x # y # z) (x # (y # z))
>   StepC   : {x, y, z: Comb KSIBC} -> Reduce KSIBC => PrimStep (:C # x # y # z) (x # z # y)

> implementation Eq KSIBC where
>   K == K = True
>   S == S = True
>   I == I = True
>   B == B = True
>   C == C = True
>   _ == _ = False

> Uninhabited (K = BaseKSIBC.S) where
>   uninhabited Refl impossible

> Uninhabited (K = I) where
>   uninhabited Refl impossible

> Uninhabited (K = B) where
>   uninhabited Refl impossible

> Uninhabited (K = C) where
>   uninhabited Refl impossible

> Uninhabited (BaseKSIBC.S = I) where
>   uninhabited Refl impossible

> Uninhabited (BaseKSIBC.S = B) where
>   uninhabited Refl impossible

> Uninhabited (BaseKSIBC.S = C) where
>   uninhabited Refl impossible

> Uninhabited (I = B) where
>   uninhabited Refl impossible

> Uninhabited (I = C) where
>   uninhabited Refl impossible

> Uninhabited (B = C) where
>   uninhabited Refl impossible

> implementation DecEq KSIBC where
>   decEq K K = Yes Refl
>   decEq S S = Yes Refl
>   decEq I I = Yes Refl
>   decEq B B = Yes Refl
>   decEq C C = Yes Refl

>   decEq K S = No absurd
>   decEq K I = No absurd
>   decEq K B = No absurd
>   decEq K C = No absurd

>   decEq S I = No absurd
>   decEq S B = No absurd
>   decEq S C = No absurd

>   decEq I B = No absurd
>   decEq I C = No absurd

>   decEq B C = No absurd

>   decEq S K = No absurdEqSym
>   decEq I K = No absurdEqSym
>   decEq B K = No absurdEqSym
>   decEq C K = No absurdEqSym

>   decEq I S = No absurdEqSym
>   decEq B S = No absurdEqSym
>   decEq C S = No absurdEqSym

>   decEq B I = No absurdEqSym
>   decEq C I = No absurdEqSym

>   decEq C B = No absurdEqSym

> implementation Show KSIBC where
>   show K = ":K"
>   show S = ":S"
>   show I = ":I"
>   show B = ":B"
>   show C = ":C"

> implementation Reduce KSIBC where
>   reduceStep (App (App (PrimComb K _) x) y) = Just x
>   reduceStep (App (App (App (PrimComb S _) x) y) z) = Just ((x # z) # (y # z))
>   reduceStep (App (PrimComb I _) x) = Just x
>   reduceStep (App (App (App (PrimComb B _) x) y) z) = Just (x # (y # z))
>   reduceStep (App (App (App (PrimComb C _) x) y) z) = Just (x # z # y)
>   reduceStep _ = Nothing
>   PrimRed = PrimStep

> stepK : {x, y: Comb KSIBC} -> Step (:K # x # y) x
> stepK = Prim StepK

> stepS : {x, y, z: Comb KSIBC} -> Step (:S # x # y # z) ((x # z) # (y # z))
> stepS = Prim StepS

> stepI : {x, y, z: Comb KSIBC} -> Step (:I # x) x
> stepI = Prim StepI

> stepB : {x, y, z: Comb KSIBC} -> Step (:B # x # y # z) (x # (y # z))
> stepB = Prim StepB

> stepC : {x, y: Comb KSIBC} -> Step (:C # x # y # z) (x # z # y)
> stepC = Prim StepC
