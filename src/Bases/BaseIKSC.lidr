= Base IKCS : A base with combinators I, K, S , C

> module Bases.BaseIKSC

> import Combinator
> import Reduction
> import RevReduction
> import Decidable.Equality
> import Lib.Other

> %access public export
> %default total

A base with combinators K, S, I, B and C

> data IKSC : Type where
>   I : IKSC
>   K : IKSC
>   S : IKSC
>   C : IKSC

> syntax ":I" = PrimComb I 1;
> syntax ":K" = PrimComb K 2;
> syntax ":S" = PrimComb S 3;
> syntax ":C" = PrimComb C 2;

> data PrimStep : Comb IKSC -> Comb IKSC -> Type where
>   StepI   : {x: Comb IKSC} -> Reduce IKSC => PrimStep (:I # x) x
>   StepK   : {x, y: Comb IKSC} -> Reduce IKSC => PrimStep (:K # x # y) x
>   StepS   : {x, y, z: Comb IKSC} -> Reduce IKSC => PrimStep (:S # x # y # z) ((x # z) # (y # z))
>   StepC   : {x, y, z: Comb IKSC} -> Reduce IKSC => PrimStep (:C # x # y # z) (x # z # y)

> implementation Eq IKSC where
>   I == I = True
>   K == K = True
>   S == S = True
>   C == C = True
>   _ == _ = False

> Uninhabited (K = BaseIKSC.S) where
>   uninhabited Refl impossible

> Uninhabited (K = I) where
>   uninhabited Refl impossible

> Uninhabited (K = C) where
>   uninhabited Refl impossible

> Uninhabited (BaseIKSC.S = I) where
>   uninhabited Refl impossible

> Uninhabited (BaseIKSC.S = C) where
>   uninhabited Refl impossible

> Uninhabited (I = C) where
>   uninhabited Refl impossible

> implementation DecEq IKSC where
>   decEq K K = Yes Refl
>   decEq S S = Yes Refl
>   decEq I I = Yes Refl
>   decEq C C = Yes Refl

>   decEq K S = No absurd
>   decEq K I = No absurd
>   decEq K C = No absurd
>   decEq S I = No absurd
>   decEq S C = No absurd
>   decEq I C = No absurd

>   decEq S K = No absurdEqSym
>   decEq I K = No absurdEqSym
>   decEq C K = No absurdEqSym
>   decEq I S = No absurdEqSym
>   decEq C S = No absurdEqSym
>   decEq C I = No absurdEqSym

> implementation Show IKSC where
>   show I = ":I"
>   show K = ":K"
>   show S = ":S"
>   show C = ":C"

> implementation Reduce IKSC where
>   reduceStep (App (PrimComb I _) x) = Just x
>   reduceStep (App (App (PrimComb K _) x) y) = Just x
>   reduceStep (App (App (App (PrimComb S _) x) y) z) = Just ((x # z) # (y # z))
>   reduceStep (App (App (App (PrimComb C _) x) y) z) = Just (x # z # y)
>   reduceStep _ = Nothing
>   PrimRed = PrimStep

> stepI : {x, y, z: Comb IKSC} -> Step (:I # x) x
> stepI = Prim StepI

> stepK : {x, y: Comb IKSC} -> Step (:K # x # y) x
> stepK = Prim StepK

> stepS : {x, y, z: Comb IKSC} -> Step (:S # x # y # z) ((x # z) # (y # z))
> stepS = Prim StepS

> stepC : {x, y: Comb IKSC} -> Step (:C # x # y # z) (x # z # y)
> stepC = Prim StepC
