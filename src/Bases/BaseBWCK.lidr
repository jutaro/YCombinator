= BaseBWCK : A base with combinators B, W, C and K

> module Bases.BaseBWCK

> import Combinator
> import Reduction
> import RevReduction
> import Decidable.Equality
> import Lib.Other

> %access public export
> %default total

A base with combinators B, W, C and K

> data BWCK : Type where
>   B : BWCK
>   W : BWCK
>   C : BWCK
>   K : BWCK

> syntax ":B" = PrimComb B 3;
> syntax ":W" = PrimComb W 2;
> syntax ":C" = PrimComb C 3;
> syntax ":K" = PrimComb K 2;

> data PrimStep : Comb BWCK -> Comb BWCK -> Type where
>   StepB   : {x, y, z: Comb BWCK} -> Reduce BWCK => PrimStep (:B # x # y # z) (x # (y # z))
>   StepW   : {x, y: Comb BWCK} -> Reduce BWCK => PrimStep (:W # x # y) (x # y # y)
>   StepC   : {x, y, z: Comb BWCK} -> Reduce BWCK => PrimStep (:C # x # y # z) (x # z # y)
>   StepK   : {x, y: Comb BWCK} -> Reduce BWCK => PrimStep (:K # x # y) x

> implementation Eq BWCK where
>   B == B = True
>   W == W = True
>   C == C = True
>   K == K = True
>   _ == _ = False

> Uninhabited (B = W) where
>   uninhabited Refl impossible

> Uninhabited (B = C) where
>   uninhabited Refl impossible

> Uninhabited (B = K) where
>   uninhabited Refl impossible

> Uninhabited (W = C) where
>   uninhabited Refl impossible

> Uninhabited (W = K) where
>   uninhabited Refl impossible

> Uninhabited (C = K) where
>   uninhabited Refl impossible

> implementation DecEq BWCK where
>   decEq B B = Yes Refl
>   decEq W W = Yes Refl
>   decEq C C = Yes Refl
>   decEq K K = Yes Refl

>   decEq B W = No absurd
>   decEq B C = No absurd
>   decEq B K = No absurd

>   decEq W B = No absurdEqSym
>   decEq W C = No absurd
>   decEq W K = No absurd

>   decEq C B = No absurdEqSym
>   decEq C W = No absurdEqSym
>   decEq C K = No absurd

>   decEq K B = No absurdEqSym
>   decEq K W = No absurdEqSym
>   decEq K C = No absurdEqSym

> implementation Show BWCK where
>   show B = ":B"
>   show W = ":W"
>   show C = ":C"
>   show K = ":K"

> implementation Reduce BWCK where
>   reduceStep (App (App (App (PrimComb B _) x) y) z) = Just (x # (y # z))
>   reduceStep (App (App (PrimComb W _) x) y) = Just (x # y # y)
>   reduceStep (App (App (App (PrimComb C _) x) y) z) = Just (x # z # y)
>   reduceStep (App (App (PrimComb K _) x) y) = Just x
>   reduceStep _ = Nothing
>   PrimRed = PrimStep

> stepK : {x, y: Comb BWCK} -> Step (:K # x # y) x
> stepK = Prim StepK

> stepB : {x, y, z: Comb BWCK} -> Step (:B # x # y # z) (x # (y # z))
> stepB = Prim StepB

> stepW : {x, y: Comb BWCK} -> Step (:W # x # y) (x # y # y)
> stepW = Prim StepW

> stepC : {x, y: Comb BWCK} -> Step (:C # x # y # z) (x # z # y)
> stepC = Prim StepC

> stepK' : {x, y: Comb BWCK} -> Step' (:K # x # y) x
> stepK' = Prim' StepK

> stepB' : {x, y, z: Comb BWCK} -> Step' (:B # x # y # z) (x # (y # z))
> stepB' = Prim' StepB

> stepW' : {x, y: Comb BWCK} -> Step' (:W # x # y) (x # y # y)
> stepW' = Prim' StepW

> stepC' : {x, y: Comb BWCK} -> Step' (:C # x # y # z) (x # z # y)
> stepC' = Prim' StepC
