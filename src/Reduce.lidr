= Reduce : Reduction for Combinators

> module Reduce

> import Base
> import Comb

> %access public export
> %default total

> interface Reduce a where
>   reduceStep : Comb a -> Maybe (Comb a)

> implementation Reduce IKS where
>   reduceStep (App (PrimComb I) x) = Just x
>   reduceStep (App (App (PrimComb K) x) y) = Just x
>   reduceStep (App (App (App (PrimComb S) x) y) z) = Just ((x # z) # (y # z))
>   reduceStep _ = Nothing

> step : Reduce b => Comb b -> Maybe (Comb b)
> step (Var a)            = Nothing
> step (PrimComb i)           = Nothing
> step a@(App head redex) = case reduceStep a of
>                             Nothing =>  case step head of
>                                           Nothing => Nothing
>                                           Just t => Just (App t redex)
>                             Just t => Just t

> stepTest1 : step (App (App :K :S) :I) = Just :S
> stepTest1 = Refl

> data StepIKS : Comb IKS -> Comb IKS -> Type where
>   IStep   : StepIKS (:I # x) x
>   KStep   : StepIKS (:K # x # y) x
>   SStep   : StepIKS (:S # x # y # z) ((x # z) # (y # z))
>   RecStep : StepIKS l res -> StepIKS (l # r) (res # r)

> stepPrf1 : StepIKS (:K # :S # :I) :S
> stepPrf1 = KStep

> stepTest2 : step (:S # (:K # $"x") # :I # :S # (:I # :K)) = Just (((:K # $"x") #  :S) # (:I # :S) # (:I # :K))
> stepTest2 = Refl

> stepPrf2 : StepIKS (:S # (:K # $"x") # :I # :S # (:I # :K)) (((:K # $"x") # :S) # (:I # :S) # (:I # :K))
> stepPrf2 = RecStep SStep

-- Reduction strategies

> partial weakHeadReduction : Reduce b => Comb b -> Comb b
> weakHeadReduction term =
>   case step term of
>     Nothing => term
>     Just newComb => weakHeadReduction newComb


-- Monomorphic variant

> {-
> reduceStep' : Comb IKS -> Maybe (Comb IKS)
> reduceStep' (App (Comb I) x) = Just x
> reduceStep' (App (App (Comb K) x) y) = Just x
> reduceStep' (App (App (App (Comb S) x) y) z) = Just (App (App x z) (App y z))
> reduceStep' _ = Nothing

> step' : Comb IKS -> Maybe (Comb IKS)
> step' (Var a)            = Nothing
> step' (Comb i)           = Nothing
> step' a@(App head redex) = case reduceStep' a of
>                             Nothing =>  case step' head of
>                                           Nothing => Nothing
>                                           Just t => Just (App t redex)
>                             Just t => Just t
> -}
