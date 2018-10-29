= BaseBWCK : A base with combinators B, W, C and K

> module BaseBWCK

> import Combinator
> import Reduction
> import RevReduction
> import Decidable.Equality

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

> bNotW : B = W -> Void
> bNotW Refl impossible

> bNotC : B = C -> Void
> bNotC Refl impossible

> bNotK : B = K -> Void
> bNotK Refl impossible

> wNotC : W = C -> Void
> wNotC Refl impossible

> wNotK : W = K -> Void
> wNotK Refl impossible

> cNotK : C = K -> Void
> cNotK Refl impossible

> implementation DecEq BWCK where
>   decEq B B = Yes Refl
>   decEq W W = Yes Refl
>   decEq C C = Yes Refl
>   decEq K K = Yes Refl

>   decEq B W = No bNotW
>   decEq B C = No bNotC
>   decEq B K = No bNotK

>   decEq W B = No (negEqSym bNotW)
>   decEq W C = No wNotC
>   decEq W K = No wNotK

>   decEq C B = No (negEqSym bNotC)
>   decEq C W = No (negEqSym wNotC)
>   decEq C K = No cNotK

>   decEq K B = No (negEqSym bNotK)
>   decEq K W = No (negEqSym wNotK)
>   decEq K C = No (negEqSym cNotK)

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
