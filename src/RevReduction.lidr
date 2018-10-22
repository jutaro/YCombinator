= RevReduction : Add reverse reduction

> module RevReduction

> import Decidable.Equality
> import Relation
> import Combinator
> import Reduction

> %access public export
> %default total

-- ||| Two way transformation (reduction plus reverse)

> data Step' : Comb b -> Comb b -> Type where
>   Prim'    : {l, r: Comb b} -> Reduce b => PrimRed l r -> Step' l r
>   AppL'    : Step' l res -> Step' (l # r) (res # r)
>   AppR'    : Step' r res -> Step' (l # r) (l # res)
>   Rev      : Step' a b -> Step' b a

> -- ||| Transform step to reversable step
> asReversable : Step a b -> Step' a b
> asReversable (Prim prim) = Prim' prim
> asReversable (AppL red)  = AppL' (asReversable red)
> asReversable (AppR red)  = AppR' (asReversable red)

> -- ||| Transform mutiple steps to reversable steps
> asReversableM : Multi Step a b -> Multi Step' a b
> asReversableM MultiRefl = MultiRefl
> asReversableM (MultiStep step multi) = MultiStep (asReversable step) (asReversableM multi)

> -- ||| Reverse mutiple Steps
> reverseM : Multi Step' a b -> Multi Step' b a
> reverseM MultiRefl = MultiRefl
> reverseM (MultiStep step multi) = reverseM' (MultiStep (Rev step) MultiRefl) multi
>   where reverseM' : Multi Step' y x -> Multi Step' y z -> Multi Step' z x
>         reverseM' aggr MultiRefl = aggr
>         reverseM' aggr (MultiStep step' multi') = reverseM' (MultiStep (Rev step') aggr) multi'

> infixr 6 +>>+
> (+>>+) : {c1,c2,c3: Comb base} -> Multi Step' c1 c2 -> Multi Step' c2 c3 -> Multi Step' c1 c3
> (+>>+) a MultiRefl = a
> (+>>+) MultiRefl b = b
> (+>>+) (MultiStep a MultiRefl) msr = (MultiStep a msr)
> (+>>+) (MultiStep a msl) msr = MultiStep a (msl +>>+ msr)

> infixr 6 ->>+
> (->>+) : {c1,c2: Comb b} -> Step' c1 c2 -> Multi Step' c2 c3 -> Multi Step' c1 c3
> (->>+) a b = MultiStep a b

> infixr 6 ->>-
> (->>-) : {c1,c2,c3: Comb b} -> Step' c1 c2 -> Step' c2 c3 -> Multi Step' c1 c3
> (->>-) {c3} a b = MultiStep {z=c3} a (MultiStep b MultiRefl)

> infixr 6 +>>-
> (+>>-) : {c1,c2: Comb b} -> Multi Step' c1 c2 -> Step' c2 c3 -> Multi Step' c1 c3
> (+>>-) a b = a +>>+ MultiStep b MultiRefl

> -- ||| Lift Appl to multiple Steps
> appL' : Multi Step' a b -> Multi Step' (a # r) (b # r)
> appL' MultiRefl = MultiRefl
> appL' (MultiStep step multi) = MultiStep (AppL' step) (appL' multi )

> -- ||| Lift AppR to multiple Steps
> appR' : Multi Step' a b -> Multi Step' (l # a) (l # b)
> appR' MultiRefl = MultiRefl
> appR' (MultiStep step multi) = MultiStep (AppR' step) (appR' multi)

> eqStep' : {a,b : Comb base} -> Multi Step' a b -> a = b
> eqStep' step = believe_me step
