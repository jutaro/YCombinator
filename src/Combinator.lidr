= Reduce : Reduction for Combinators

> module Combinator

> import Term

> %access public export
> %default total

> interface Reduce b where
>   reduceStep : Term b -> Maybe (Term b)

> data Comb : (b : Type) -> Type where
>   MkComb : Term b -> Comb b

> combInjective : (Comb a = Comb b) -> a = b
> combInjective Refl = Refl

> mkCombInjective : MkComb l = MkComb r -> l = r
> mkCombInjective Refl = Refl

> infixl 10 #

> (#) : Reduce b => Comb b -> Comb b -> Comb b
> (MkComb a) # (MkComb b) = (MkComb (a ## b))

> syntax "?"[var] = Comb (Var var);

> step : Reduce b => Term b -> Maybe (Term b)
> step (Var a)            = Nothing
> step (PrimComb i)       = Nothing
> step a@(App head redex) = case reduceStep a of
>                             Nothing =>  case step head of
>                                           Nothing => Nothing
>                                           Just t => Just (App t redex)
>                             Just t => Just t


-- Reduction strategies

> partial weakHeadReduction : Reduce b => Term b -> Term b
> weakHeadReduction term =
>   case step term of
>     Nothing => term
>     Just newTerm => weakHeadReduction newTerm

> weakHeadReductionCut : Reduce b => Nat -> Term b -> Maybe (Term b)
> weakHeadReductionCut (S x) term =
>   case step term of
>     Nothing => Just term
>     Just newTerm => weakHeadReductionCut x newTerm
> weakHeadReductionCut Z term = Nothing

> whr : Reduce b => Comb b -> Comb b
> whr (MkComb c) =
>   case weakHeadReductionCut 1000 c of
>       Nothing => (MkComb c)
>       Just t => (MkComb t)

> reduxEquals : (Reduce b) => (a : Comb b) -> whr a = a
> reduxEquals a = believe_me (whr a = a)

> implementation (DecEq (Term b), Reduce b) => DecEq (Comb b) where
>   decEq (MkComb l) (MkComb r) =
>     case decEq l r of
>       Yes p =>  Yes $ cong p
>       No p  =>  let (MkComb l') = whr (MkComb l)
>                     (MkComb r') = whr (MkComb r)
>                 in case decEq l' r' of
>                   Yes p1 => let hyp : (l = r) = believe_me p1
>                             in Yes $ cong hyp
>                   No p1 =>  let hyp : ((l = r) -> Void) = believe_me p1
>                             in No $ (\ h : MkComb l = MkComb r => hyp (mkCombInjective h))
