= Reduce : Reduction for Combinators

> module Reduce

> import Base
> import Term

> %access public export
> %default total

> interface Reduce a where
>   reduceStep : Term a -> Maybe (Term a)

> implementation Reduce IKS where
>   reduceStep (App (Comb I) x) = Just x
>   reduceStep (App (App (Comb K) x) y) = Just x
>   reduceStep (App (App (App (Comb S) x) y) z) = Just (App (App x z) (App y z))
>   reduceStep _ = Nothing

> step : Reduce b => Term b -> Maybe (Term b)
> step (Var a)            = Nothing
> step (Comb i)           = Nothing
> step a@(App head redex) = case reduceStep a of
>                             Nothing =>  case step head of
>                                           Nothing => Nothing
>                                           Just t => Just (App t redex)
>                             Just t => Just t

> stepTest1 : step (App (App :K :S) :I) = Just :S
> stepTest1 = Refl

> data Step : Term IKS -> Term IKS -> Type where
>   IStep   : Step (App (Comb I) x) x
>   KStep   : Step (App (App (Comb K) x) y) x
>   SStep   : Step (App (App (App (Comb S) x) y) z) (App (App x z) (App y z))
>   RecStep : Step l res -> Step (App l r) (App res r)

> stepPrf1 : Step (:K # :S # :I) :S
> stepPrf1 = KStep

> stepTest2 : step (:S # (:K # (Var "x")) # :I # :S # (:I # :K)) = Just (((:K # (Var "x")) #  :S) # (:I # :S) # (:I # :K))
> stepTest2 = Refl

> stepPrf2 : Step (:S # (:K # (Var "x")) # :I # :S # (:I # :K)) (((:K # (Var "x")) #  :S) # (:I # :S) # (:I # :K))
> stepPrf2 = RecStep SStep


-- Monomorphic variant

> {-
> reduceStep' : Term IKS -> Maybe (Term IKS)
> reduceStep' (App (Comb I) x) = Just x
> reduceStep' (App (App (Comb K) x) y) = Just x
> reduceStep' (App (App (App (Comb S) x) y) z) = Just (App (App x z) (App y z))
> reduceStep' _ = Nothing

> step' : Term IKS -> Maybe (Term IKS)
> step' (Var a)            = Nothing
> step' (Comb i)           = Nothing
> step' a@(App head redex) = case reduceStep' a of
>                             Nothing =>  case step' head of
>                                           Nothing => Nothing
>                                           Just t => Just (App t redex)
>                             Just t => Just t
> -}
