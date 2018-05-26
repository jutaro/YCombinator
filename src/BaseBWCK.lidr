= Base : Combinator Bases

> module BaseBWCK

> import Combinator
> import Reduction
> import Decidable.Equality

> %access public export
> %default total

A base with B, W, C, K

> data BWCK : Type where
>   B : BWCK
>   W : BWCK
>   C : BWCK
>   K : BWCK

> syntax ":B" = PrimComb B;
> syntax ":W" = PrimComb W;
> syntax ":C" = PrimComb C;
> syntax ":K" = PrimComb K;

> implementation Reduce BWCK where
>   reduceStep (App (App (App (PrimComb B) x) y) z) = Just (x # (y # z))
>   reduceStep (App (App (PrimComb W) x) y) = Just (x # y # y)
>   reduceStep (App (App (App (PrimComb C) x) y) z) = Just (x # z # y)
>   reduceStep (App (App (PrimComb K) x) y) = Just x
>   reduceStep _ = Nothing

> data Step : Comb BWCK -> Comb BWCK -> Type where
>   StepB   : Step (:B # x # y # z) (x # (y # z))
>   StepW   : Step (:W # x # y) (x # y # y)
>   StepC   : Step (:C # x # y # z) (x # z # y)
>   StepK   : Step (:K # x # y) x
>   AppL    : Step l res -> Step (l # r) (res # r)
>   AppR    : Step r res -> Step (l # r) (l # res)
>   Steps   : Step c1 c2 -> Step c2 c3 -> Step c1 c3
>   Rev     : Step c1 c2 -> Step c2 c1
>   StepEq  : Step x x

> infixl 10 >-
> (>-) : Step c1 c2 -> Step c2 c3 -> Step c1 c3
> (>-) a b = Steps a b

> eqStep : {a,b : Comb BWCK} -> Step a b -> a = b
> eqStep step = believe_me step

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
