= Base : Combinator Bases

> module BaseKS

> import Combinator
> import Reduction
> import Decidable.Equality

> %hide Language.Reflection.I
> %access public export
> %default total

> -- A basic combinator base
> data KS : Type where
>   K : KS
>   S : KS

> syntax ":K" = PrimComb K;
> syntax ":S" = PrimComb S;

> implementation Reduce KS where
>   reduceStep (App (App (PrimComb K) x) y) = Just x
>   reduceStep (App (App (App (PrimComb S) x) y) z) = Just ((x # z) # (y # z))
>   reduceStep _ = Nothing

> data Step : Comb KS -> Comb KS -> Type where
>   StepK   :  {x, y: Comb KS} -> Step (:K # x # y) x
>   StepS   :  {x, y, z: Comb KS} -> Step (:S # x # y # z) ((x # z) # (y # z))
>   AppL    : Step l res -> Step (l # r) (res # r)
>   AppR    : Step r res -> Step (l # r) (l # res)
>   Steps   : Step c1 c2 -> Step c2 c3 -> Step c1 c3
>   Rev     : Step c1 c2 -> Step c2 c1
>   StepRep : c1 = c2 -> Step c1 c2
>   StepEq  : Step x x

> infixl 10 >-
> (>-) : Step c1 c2 -> Step c2 c3 -> Step c1 c3
> (>-) a b = Steps a b

> eqStep : {a,b : Comb KS} -> Step a b -> a = b
> eqStep step = believe_me step

> implementation Eq KS where
>   K == K = True
>   S == S = True
>   _ == _ = False

> kNotS : K = S -> Void
> kNotS Refl impossible

> implementation DecEq KS where
>   decEq K K = Yes Refl
>   decEq K S = No kNotS
>   decEq S K = No (negEqSym kNotS)
>   decEq S S = Yes Refl

> implementation Show KS where
>   show K = ":K"
>   show S = ":S"


Test code

>
> stepTest1 : whr (:K # :S # :K) = :S
> stepTest1 = Refl

> stepPrf1 : Step (:K # :S # :K) :S
> stepPrf1 = StepK

> {-
> stepTest2 : {x: Comb KS} -> step (:S # (:K # x) # :I # :S # (:I # :K)) = Just (((:K # x) #  :S) # (:I # :S) # (:I # :K))
> stepTest2 = Refl

> stepPrf2 : {x: Comb KS} -> Step (:S # (:K # x) # :I # :S # (:I # :K)) (((:K # x) # :S) # (:I # :S) # (:I # :K))
> stepPrf2 = KSAppL KSStepS
> -}

> subtermTest1 : Subterm (:K # :S) ((:K # :S) # :K)
> subtermTest1 = SubtermAppL $ SubtermEq

> subtermTest1' : subterm (:K # :S) ((:K # :S) # :K) = True
> subtermTest1' = Refl
