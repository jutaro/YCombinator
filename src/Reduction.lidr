= Reduction : Terms for Combinators

> module Reduction

> import Decidable.Equality
> import Lib.Relation
> import Combinator
> import Data.List.Quantifiers
> import Lib.Id


> %access public export
> %default total
> %hide Prelude.Stream.(::)

> ||| Single step reduction or One-step reduction
> data Step : {b: Type} -> Comb b -> Comb b -> Type where
>   Prim    : {l, r: Comb b} -> Reduce b => PrimRed {base=b} l r -> Step {b} l r
>   AppL    : Step l res -> Step (l # r) (res # r)
>   AppR    : Step r res -> Step (l # r) (l # res)

Weak reduction is the transitive closure of One-step reduction.
We use the Multi Relation to define it as Multi Step

> infixr 6 ->+
> (->+) : {c1,c2: Comb b} -> Step c1 c2 -> Multi Step c2 c3 -> Multi Step c1 c3
> (->+) a b = MultiStep a b

> infixr 6 ->-
> (->-) : {c1,c2,c3: Comb b} -> Step c1 c2 -> Step c2 c3 -> Multi Step c1 c3
> (->-) {c3} a b = MultiStep {z=c3} a (MultiStep b MultiRefl)

> infixr 6 +>+
> (+>+) : {c1,c2,c3: Comb b} -> Multi Step c1 c2 -> Multi Step c2 c3 -> Multi Step c1 c3
> (+>+) a MultiRefl = a
> (+>+) MultiRefl b = b
> (+>+) (MultiStep a MultiRefl) msr = (MultiStep a msr)
> (+>+) (MultiStep a msl) msr = MultiStep a (msl +>+ msr)

> infixr 6+>-
> (+>-) : {c1,c2: Comb b} -> Multi Step c1 c2 -> Step c2 c3 -> Multi Step c1 c3
> (+>-) a b = a +>+ MultiStep b MultiRefl

> ||| Lift Appl to multiple Steps
> appL : Multi Step a b -> Multi Step (a # r) (b # r)
> appL MultiRefl = MultiRefl
> appL (MultiStep step multi) = MultiStep (AppL step) (appL multi )

> ||| Lift AppR to multiple Steps
> appR : Multi Step a b -> Multi Step (l # a) (l # b)
> appR MultiRefl = MultiRefl
> appR (MultiStep step multi) = MultiStep (AppR step) (appR multi)

> ||| Terms are defined as equal if they are in a step relation
> ||| We should only need this one believe me!
> eqStep : {b: Type} -> {a,b : Comb b} -> Step a b -> a = b
> eqStep step = believe_me step

> ||| Defining this equality transitiv for mutiple steps gives weak equality
> eqSteps : {b: Type} -> {a,b : Comb b} -> Multi Step a b -> a = b
> eqSteps MultiRefl = Refl
> eqSteps (MultiStep s m) =
>   let indHyp = eqSteps m
>   in trans (eqStep s) indHyp


== Computational reduction

> ||| Take a step in computational reduction on the head redex.
> ||| Return Just the new combinator if possible, or Nothing if the head is not a redex,
> ||| which is the same as to say the term is in weak head normal form
> stepHead : Reduce b => Comb b -> Maybe (Comb b)
> stepHead (PrimComb i n)     = Nothing
> stepHead (Var n)            = Nothing
> stepHead a@(App head redex) =
>   case reduceStep a of
>     Nothing =>
>       case stepHead head of
>         Nothing => Nothing
>         Just t => Just (App t redex)
>     Just t => Just t


> ||| Take a step in computational reduction on the first possible redex starting from the head.
> ||| Return just the new combinator if possible, or Nothing if the head is not a redex
> ||| which is the same as to say the term is in weak normal form
> step : Reduce b => Comb b -> Maybe (Comb b)
> step (PrimComb i n)     = Nothing
> step (Var n)            = Nothing
> step a@(App head redex) =
>   case reduceStep a of
>     Just t => Just t
>     Nothing =>
>       case step head of
>         Just h => Just (App h redex)
>         Nothing =>
>           case step redex of
>             Nothing => Nothing
>             Just r => Just (App head r)

-- Reduction strategies

> ||| Applies multiple head steps, until a normal form is reached,
> ||| or calculates forever, if no weak head normal form exists
> partial weakHeadReduction : Reduce b => Comb b -> Comb b
> weakHeadReduction term =
>   case stepHead term of
>     Nothing => term
>     Just newComb => weakHeadReduction newComb

> ||| Applies multiple head steps, until a normal form is reached,
> ||| or the maximum number of steps has been taken
> weakHeadReductionCut : Reduce b => Nat -> Comb b -> Maybe (Comb b)
> weakHeadReductionCut (S x) term =
>   case stepHead term of
>     Nothing => Just term
>     Just newComb => weakHeadReductionCut x newComb
> weakHeadReductionCut Z term = Nothing

> ||| Short name for convenience
> whr : Reduce b => Comb b -> Maybe (Comb b)
> whr = weakHeadReductionCut 300

> ||| Computes if a term is in weak head normal form
> isWeakHeadNormalForm : Reduce b => Comb b -> Bool
> isWeakHeadNormalForm c = case stepHead c of
>                      Nothing => True
>                      Just _ => False

> ||| Computes if a term is in weak normal form
> isWeakNormalForm : Reduce b => Comb b -> Bool
> isWeakNormalForm c = case step c of
>                      Nothing => True
>                      Just _ => False

> ||| Applies multiple steps, until a normal form is reached,
> ||| or calculates forever, if no weak normal form exists
> partial weakReduction : Reduce b => Comb b -> Comb b
> weakReduction term =
>   case step term of
>     Nothing => term
>     Just newComb => weakReduction newComb

> ||| Applies multiple steps, until a normal form is reached,
> ||| or the maximum number of steps has been taken
> weakReductionCut : Reduce b => Nat -> Comb b -> Maybe (Comb b)
> weakReductionCut (S x) term =
>   case step term of
>     Nothing => Just term
>     Just newComb => weakReductionCut x newComb
> weakReductionCut Z term = Nothing

> ||| Short name for convenience
> wr : Reduce b => Comb b -> Maybe (Comb b)
> wr = weakReductionCut 300
