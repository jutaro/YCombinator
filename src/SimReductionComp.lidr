= Simultaneously Reduction : Computation for simultaneously reduction

> module SimReductionComp

> import Combinator
> import Reduction
> import Path
> import BaseKS
> import Id


> %access public export
> %default total

> ||| Take a step in computational reduction on the first possible redex starting from the head.
> ||| Return just the new combinator if possible, or Nothing if the head is not a redex
> ||| which is the same as to say the term is in weak normal form
> stepSim : {b: Type} -> Reduce b => {default Z n: Nat} -> Comb b -> (Nat, Comb b)
> stepSim {n} i@(PrimComb _ _)   = (n,i)
> stepSim {n} i@(Var _)          = (n,i)
> stepSim {n} i@(App left right) =
>   let (n',r) = stepSim {n} right
>       (n'', l) = stepSim {n=n'} left
>   in case reduceStep (App l r) of
>     Just t => (S n'', t)
>     Nothing => (n'',App l r)

> ||| Applies multiple head steps, until a normal form is reached,
> ||| or calculates forever, if no weak head normal form exists
> partial simReduction : {b: Type} -> Reduce b => Comb b -> Comb b
> simReduction term =
>   case stepSim term of
>     (Z, _) => term
>     (_, t) => simReduction t

> ||| Applies multiple head steps, until a normal form is reached,
> ||| or the maximum number of steps has been taken
> simReductionCut : {b: Type} -> Reduce b => Nat -> Comb b -> Maybe (Comb b)
> simReductionCut (S x) term =
>   case stepSim term of
>     (Z, _) => Just term
>     (_, t) => simReductionCut x t
> simReductionCut Z term = Nothing

> ||| Short name for convenience
> sr : {b: Type} -> Reduce b => Comb b -> Maybe (Comb b)
> sr = simReductionCut 300

> test1 : sr Path.excomb = Just Path.rcomb
> test1 = Refl
