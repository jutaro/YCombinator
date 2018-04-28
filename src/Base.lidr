= Base : Combinator Bases

> module Base

> import Combinator
> import Decidable.Equality

> %hide Language.Reflection.I
> %hide Language.Reflection.Var

> %access public export
> %default total

> -- A basic combinator base
> data IKS : Type where
>   I : IKS
>   K : IKS
>   S : IKS

> syntax ":I" = PrimComb I;
> syntax ":K" = PrimComb K;
> syntax ":S" = PrimComb S;

> implementation Reduce IKS where
>   reduceStep (App (PrimComb I) x) = Just x
>   reduceStep (App (App (PrimComb K) x) y) = Just x
>   reduceStep (App (App (App (PrimComb S) x) y) z) = Just ((x # z) # (y # z))
>   reduceStep _ = Nothing

> data StepIKS : Comb IKS -> Comb IKS -> Type where
>   IStep   : {x: Comb IKS} -> StepIKS (:I # x) x
>   KStep   : {x, y: Comb IKS} -> StepIKS (:K # x # y) x
>   SStep   : {x, y, z: Comb IKS} -> StepIKS (:S # x # y # z) ((x # z) # (y # z))
>   RecStep : StepIKS l res -> StepIKS (l # r) (res # r)

> implementation Eq IKS where
>   I == I = True
>   K == K = True
>   S == S = True
>   _ == _ = False

> iNotK : I = K -> Void
> iNotK Refl impossible

> iNotS : I = S -> Void
> iNotS Refl impossible

> kNotS : K = S -> Void
> kNotS Refl impossible

> implementation DecEq IKS where
>   decEq I I = Yes Refl
>   decEq I K = No iNotK
>   decEq I S = No iNotS
>   decEq K I = No (negEqSym iNotK)
>   decEq K K = Yes Refl
>   decEq K S = No kNotS
>   decEq S I = No (negEqSym iNotS)
>   decEq S K = No (negEqSym kNotS)
>   decEq S S = Yes Refl

> implementation Show IKS where
>   show I = ":I"
>   show K = ":K"
>   show S = ":S"

A base with M and B

> data MT : Type where
>   M : MT
>   B : MT

> syntax ":M" = PrimComb M;
> syntax ":B" = PrimComb B;

> implementation Reduce MT where
>   reduceStep (App (PrimComb M) x) = Just (x # x)
>   reduceStep (App (App (App (PrimComb b) x) y) z) = Just (x # (y # z))
>   reduceStep _ = Nothing

> data StepMT : Comb MT -> Comb MT -> Type where
>   MStep   : StepMT (:M # x) (x # x)
>   BStep   : StepMT (:B # x # y # z) (x # (y # z))
>   MTRecStep : StepMT l res -> StepMT (l # r) (res # r)

> implementation Eq MT where
>   M == M = True
>   B == B = True
>   _ == _ = False

> bNotM : B = M -> Void
> bNotM Refl impossible

> implementation DecEq MT where
>   decEq M M = Yes Refl
>   decEq B B = Yes Refl
>   decEq B M = No bNotM
>   decEq M B = No (negEqSym bNotM)

> implementation Show MT where
>   show M = ":M"
>   show B = ":B"

Test code

>
> stepTest1 : whr (:K # :S # :I) = :S
> stepTest1 = Refl

> stepPrf1 : StepIKS (:K # :S # :I) :S
> stepPrf1 = KStep

> stepTest2 : step (:S # (:K # §"x") # :I # :S # (:I # :K)) = Just (((:K # §"x") #  :S) # (:I # :S) # (:I # :K))
> stepTest2 = Refl

> stepPrf2 : StepIKS (:S # (:K # §"x") # :I # :S # (:I # :K)) (((:K # §"x") # :S) # (:I # :S) # (:I # :K))
> stepPrf2 = RecStep SStep


> subtermTest1 : Subterm (:K # :S) ((:K # :S) # :I)
> subtermTest1 = SubtermAppL $ SubtermEq

> subtermTest1' : subterm (:K # :S) ((:K # :S) # :I) = True
> subtermTest1' = Refl
