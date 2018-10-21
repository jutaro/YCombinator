= Reduction : Terms for Combinators

> module Reduction

> import Decidable.Equality
> import Lib
> import Combinator

> %access public export
> %default total

-- Single step reduction

> data Step : Comb b -> Comb b -> Type where
>   Prim    : {l, r: Comb b} -> Reduce b => PrimRed l r -> Step l r
>   AppL    : Step l res -> Step (l # r) (res # r)
>   AppR    : Step r res -> Step (l # r) (l # res)

> step_not_deterministic : Not (deterministic Step)
> step_not_deterministic = ?step_not_deterministic_rhs

> (++) : {c1,c2,c3: Comb base} -> Multi Step c1 c2 -> Multi Step c2 c3 -> Multi Step c1 c3
> (++) a Multi_refl = a
> (++) Multi_refl b = b
> (++) (Multi_step a Multi_refl) msr = (Multi_step a msr)
> (++) (Multi_step a msl) msr = Multi_step a (msl ++ msr)

> infixr 9 >-
> (>-) : {c1,c2: Comb b} -> Step c1 c2 -> Multi Step c2 c3 -> Multi Step c1 c3
> (>-) a b = Multi_step a b

> infixr 10 >>-
> (>>-) : {c1,c2,c3: Comb b} -> Step c1 c2 -> Step c2 c3 -> Multi Step c1 c3
> (>>-) {c3} a b = Multi_step {z=c3} a (Multi_step b Multi_refl)

-- ||| Two way transformation (reduction plus reverse)

> data Step' : Comb b -> Comb b -> Type where
>   Prim'    : {l, r: Comb b} -> Reduce b => PrimRed l r -> Step' l r
>   AppL'    : Step' l res -> Step' (l # r) (res # r)
>   AppR'    : Step' r res -> Step' (l # r) (l # res)
>   Rev      : Step' a b -> Step' b a

> infixr 9 <>-
> (<>-) : {c1,c2: Comb b} -> Step' c1 c2 -> Multi Step' c2 c3 -> Multi Step' c1 c3
> (<>-) a b = Multi_step a b

> infixr 10 <>>-
> (<>>-) : {c1,c2,c3: Comb b} -> Step' c1 c2 -> Step' c2 c3 -> Multi Step' c1 c3
> (<>>-) {c3} a b = Multi_step {z=c3} a (Multi_step b Multi_refl)

-- >   StepRefl: c1 = c2 -> Step c1 c2

> -- ||| Transform step to reversable step
> asReversable : Step a b -> Step' a b
> asReversable (Prim prim) = Prim' prim
> asReversable (AppL red)  = AppL' (asReversable red)
> asReversable (AppR red)  = AppR' (asReversable red)

> -- ||| Transform mutiple steps to reversable steps
> asReversableM : Multi Step a b -> Multi Step' a b
> asReversableM Multi_refl = Multi_refl
> asReversableM (Multi_step step multi) = Multi_step (asReversable step) (asReversableM multi)

> -- ||| Reverse mutiple Steps
> reverseM : Multi Step' a b -> Multi Step' b a
> reverseM Multi_refl = Multi_refl
> reverseM (Multi_step step multi) = reverseM' (Multi_step (Rev step) Multi_refl) multi
>   where reverseM' : Multi Step' y x -> Multi Step' y z -> Multi Step' z x
>         reverseM' aggr Multi_refl = aggr
>         reverseM' aggr (Multi_step step multi) = reverseM' (Multi_step (Rev step) aggr) multi

> -- ||| Apply Appl to multiple Steps
> appL : Multi Step a b -> Multi Step (a # r) (b # r)
> appL Multi_refl = Multi_refl
> appL (Multi_step {x}{y}{z} step multi) = Multi_step (AppL step) (appL {a=y} {b=z} multi )

> -- ||| Apply AppR to multiple Steps
> appR : Multi Step a b -> Multi Step (l # a) (l # b)
> appR Multi_refl = Multi_refl
> appR (Multi_step step multi) = Multi_step (AppR step) (appR multi)

> eqStep : {a,b : Comb base} -> Multi Step a b -> a = b
> eqStep step = believe_me step

> eqStep' : {a,b : Comb base} -> Multi Step' a b -> a = b
> eqStep' step = believe_me step

> stepHead : Reduce b => Comb b -> Maybe (Comb b)
> stepHead (PrimComb i)       = Nothing
> stepHead a@(App head redex) = case reduceStep a of
>                                 Nothing =>  case stepHead head of
>                                               Nothing => Nothing
>                                               Just t => Just (App t redex)
>                                 Just t => Just t

> step : Reduce b => Comb b -> Maybe (Comb b)
> step (PrimComb i)       = Nothing
> step a@(App head redex) = case reduceStep a of
>                             Nothing =>  case step head of
>                                           Nothing => case step redex of
>                                                           Nothing => Nothing
>                                                           Just r => Just (App head r)
>                                           Just h => Just (App h redex)
>                             Just t => Just t

-- Reduction strategies

> partial weakHeadReduction : Reduce b => Comb b -> Comb b
> weakHeadReduction term =
>   case stepHead term of
>     Nothing => term
>     Just newComb => weakHeadReduction newComb

> weakHeadReductionCut : Reduce b => Nat -> Comb b -> Maybe (Comb b)
> weakHeadReductionCut (S x) term =
>   case stepHead term of
>     Nothing => Just term
>     Just newComb => weakHeadReductionCut x newComb
> weakHeadReductionCut Z term = Nothing

> whr : Reduce b => Comb b -> Comb b
> whr c =
>   case weakHeadReductionCut 1000 c of
>       Nothing => c
>       Just t => t

> partial reduction : Reduce b => Comb b -> Comb b
> reduction term =
>   case step term of
>     Nothing => term
>     Just newComb => reduction newComb

> reductionCut : Reduce b => Nat -> Comb b -> Maybe (Comb b)
> reductionCut (S x) term =
>   case step term of
>     Nothing => Just term
>     Just newComb => reductionCut x newComb
> reductionCut Z term = Nothing

> reduct : Reduce b => Comb b -> Comb b
> reduct c =
>   case reductionCut 100 c of
>       Nothing => c
>       Just t => t

> implementation (StructEq (Comb b), Reduce b) => DecEq (Comb b) where
>   decEq l r =
>     case structEq l r of
>       Yes p =>  Yes $ p
>       No p  =>  let l' = reduct l
>                     r' = reduct r
>                 in case structEq l' r' of
>                   Yes p1 => let hyp : (l = r) = believe_me p1
>                             in Yes $ hyp
>                   No p1 =>  let hyp : ((l = r) -> Void) = believe_me p1
>                             in No $ (\ h : l = r => hyp h)

> isNormalForm : Reduce b => Comb b -> Bool
> isNormalForm c = case step c of
>                      Nothing => True
>                      Just _ => False

>{-

Proof that subterm implement Subterm? How to do this?

>

-- > subtermLemma : {t : Type} -> DecEq t =>(a : Comb t) ->  {prf : Dec (a = a)} ->subterm' a a prf = True
-- > subtermLemma  x {prf = Yes eqPrf} = Refl
-- > subtermLemma  x {prf = No contra} = void (contra (Refl))

We have the problem that Subterm may point to a right subterm, while the algorithm always detects the leftmost subterm.
So they give the result, but we can't proof them equal

> subtermCorrect : {t : Type} -> (DecEq t, Reduce t) => {a, b: Comb t} -> (prf: Dec (a = b)) -> Subterm a b -> subterm' a b prf = True
> subtermCorrect {a=term} {b=term} (Yes p) SubtermEq = Refl
> subtermCorrect {a=term} {b=term} (No contra) SubtermEq = void (contra Refl)
> subtermCorrect {a=term} {b=App l r} (No contra) (SubtermAppL lp) =
>   let indHyp = subtermCorrect {a=term} {b=l} (decEq term l) lp
>   in rewrite indHyp
>   in Refl
> subtermCorrect {a=term} {b=App l r} (No contra) (SubtermAppR rp) =
>   let indHypAbsurd = subtermCorrect {a=term} {b=l} (decEq term l) ?subtermCorrect0
>       indHyp = subtermCorrect {a=term} {b=r} (decEq term r) rp
>   in rewrite indHyp
>   in rewrite indHypAbsurd
>   in ?subtermCorrect1

> lemma : a || b = True -> Either (a = True) (b = True)
> lemma {a = True} {b = True} prf = Left prf
> lemma {a = True} {b = False} prf = Left prf
> lemma {a = False} {b = True} prf = Right prf
> lemma {a = False} {b = False} Refl impossible

> subtermComplete : {t : Type} -> (DecEq t, Reduce t) => {a, b: Comb t} -> (prf : Dec (a = b))
>                                                 -> (hyp : subterm' a b prf = True) -> Subterm a b
> subtermComplete {a} {b} (Yes p) hyp = rewrite p in SubtermEq
> subtermComplete {a} {b=App l r} (No p) hyp =
>   let indHyp1 = subtermComplete {a} {b=l} (decEq a l) ?hole0
>       indHyp2 = subtermComplete {a} {b=r} (decEq a r) ?hole1
>   in ?subtermComplete
> subtermComplete {a} {b=Var _} (No p) hyp = absurd hyp
> subtermComplete {a} {b=PrimComb _} (No p) hyp = absurd hyp
> -}
