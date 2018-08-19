= BaseKS : A base with combinators K and S

> module BaseKS

> import Combinator
> import Reduction
> import Decidable.Equality

> %access public export
> %default total

A basic combinator base

> data KS : Type where
>   K : KS
>   S : KS

> syntax ":K" = PrimComb K;
> syntax ":S" = PrimComb S;

> data PrimStep : Comb KS -> Comb KS -> Type where
>   StepK   :  {x, y: Comb KS} -> Reduce KS => PrimStep (:K # x # y) x
>   StepS   :  {x, y, z: Comb KS} -> Reduce KS => PrimStep (:S # x # y # z) ((x # z) # (y # z))

> implementation Reduce KS where
>   reduceStep (App (App (PrimComb K) x) y) = Just x
>   reduceStep (App (App (App (PrimComb S) x) y) z) = Just ((x # z) # (y # z))
>   reduceStep _ = Nothing
>   PrimRed = PrimStep

> stepK : {x, y: Comb KS} -> Step (:K # x # y) x
> stepK = Prim StepK

> stepS : {x, y, z: Comb KS} -> Step (:S # x # y # z) ((x # z) # (y # z))
> stepS = Prim StepS

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
> stepPrf1 = stepK

> subtermTest1 : Subterm (:K # :S) ((:K # :S) # :K)
> subtermTest1 = SubtermAppL $ SubtermEq

> subtermTest1' : subterm (:K # :S) ((:K # :S) # :K) = True
> subtermTest1' = Refl
