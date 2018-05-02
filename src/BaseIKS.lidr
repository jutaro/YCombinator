= Base : Combinator Bases

> module BaseIKS

> import Combinator
> import Decidable.Equality

> %hide Language.Reflection.I
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
>   IKSStepI   :  {x: Comb IKS} -> StepIKS (:I # x) x
>   IKSStepK   :  {x, y: Comb IKS} -> StepIKS (:K # x # y) x
>   IKSStepS   :  {x, y, z: Comb IKS} -> StepIKS (:S # x # y # z) ((x # z) # (y # z))
>   IKSAppL    :  StepIKS l res -> StepIKS (l # r) (res # r)
>   IKSAppR    :  StepIKS r res -> StepIKS (l # r) (l # res)
>   IKSSteps   :  StepIKS c1 c2 -> StepIKS c2 c3 -> StepIKS c1 c3
>   IKSStepEq  :  StepIKS x x

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


Test code

>
> stepTest1 : whr (:K # :S # :I) = :S
> stepTest1 = Refl

> stepPrf1 : StepIKS (:K # :S # :I) :S
> stepPrf1 = IKSStepK

> stepTest2 : {x: Comb IKS} -> step (:S # (:K # x) # :I # :S # (:I # :K)) = Just (((:K # x) #  :S) # (:I # :S) # (:I # :K))
> stepTest2 = Refl

> stepPrf2 : {x: Comb IKS} -> StepIKS (:S # (:K # x) # :I # :S # (:I # :K)) (((:K # x) # :S) # (:I # :S) # (:I # :K))
> stepPrf2 = IKSAppL IKSStepS

> subtermTest1 : Subterm (:K # :S) ((:K # :S) # :I)
> subtermTest1 = SubtermAppL $ SubtermEq

> subtermTest1' : subterm (:K # :S) ((:K # :S) # :I) = True
> subtermTest1' = Refl
