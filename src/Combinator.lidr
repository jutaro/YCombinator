= Combinator : Combs for Combinators

> module Combinator

> import Decidable.Equality

> %access public export
> %default total


> -- ||| a term can be a a primitive combinator or an application
> -- ||| Vars are in the meta language (Idris)
> data Comb : (base: Type) -> Type where
>   PrimComb : base -> Comb base
>   App : Comb base -> Comb base -> Comb base

> infixl 9 #
> (#) : Comb base -> Comb base -> Comb base
> (#) l r = App l r

> implementation (Eq t) => Eq (Comb t) where
>   (PrimComb a)  == (PrimComb b)  = a == b
>   (App a b) == (App c d) = a == c && b == d
>   _         == _         = False

> implementation (Show t) => Show (Comb t) where
>   showPrec d (PrimComb c) = show c
>   showPrec d (App a b) = showParens (d > Open) (showPrec Open a ++ " # " ++ showPrec App b)

> baseInjective : {a, b : t} -> PrimComb a = PrimComb b -> a = b
> baseInjective Refl = Refl

> appCongruent : {a, b, c, d : Comb t} -> a = c -> b = d -> App a b = App c d
> appCongruent Refl Refl = Refl

> appInjective : {a, b, c, d : Comb t}  -> App a b = App c d -> (a = c, b = d)
> appInjective Refl = (Refl,Refl)

> baseNotApp : PrimComb t = App l r -> Void
> baseNotApp Refl impossible

> interface StructEq t where
>   ||| Decide whether two elements of `t` are propositionally equal
>   total structEq : (x1 : t) -> (x2 : t) -> Dec (x1 = x2)

> implementation (DecEq t) => StructEq (Comb t) where
>   structEq (PrimComb a) (PrimComb b) with (decEq a b)
>     | Yes p = Yes $ cong p
>     | No p  = No $ \h : PrimComb a = PrimComb b => p (baseInjective h)

>   structEq (App a b) (App c d) with (structEq a c)
>     structEq (App a b) (App c d) | Yes p with (structEq b d)
>       structEq (App a b) (App c d) | Yes p | Yes p' = Yes $ appCongruent p p'
>       structEq (App a b) (App c d) | Yes p | No p' =  No $ \h : App a b = App c d => p' (snd (appInjective h))
>     structEq (App a b) (App c d) | No p = No $ \h : App a b = App c d => p (fst (appInjective h))

>   structEq (PrimComb t) (App l r) = No (baseNotApp)
>   structEq (App l r) (PrimComb t) = No (negEqSym baseNotApp)

> subterm' : {t : Type} -> DecEq t => (t1 : Comb t) -> (t2 : Comb t) -> Dec (t1 = t2) -> Bool
> subterm' a b (Yes _) = True
> subterm' a b (No  _) = case b of
>                 (App l r) => subterm' a l (structEq a l) || subterm' a r (structEq a r)
>                 _ => False

> subterm : {t : Type} -> (StructEq (Comb t), DecEq t) => (t1 : Comb t) -> (t2 : Comb t) -> Bool
> subterm a b = subterm' a b (structEq a b)

> data Subterm : Comb b -> Comb b -> Type where
>   SubtermEq : Subterm x x
>   SubtermAppL : Subterm x l -> Subterm x (l # r)
>   SubtermAppR : Subterm x r -> Subterm x (l # r)

> subtermInAppL : Subterm (l # r) b -> Subterm l b
> subtermInAppL SubtermEq = SubtermAppL $ SubtermEq
> subtermInAppL (SubtermAppL pl) =
>   let indHyp = subtermInAppL pl
>   in SubtermAppL indHyp
> subtermInAppL (SubtermAppR pl) =
>   let indHyp = subtermInAppL pl
>   in SubtermAppR indHyp

> subtermInAppR : Subterm (l # r) b -> Subterm r b
> subtermInAppR SubtermEq = SubtermAppR $ SubtermEq
> subtermInAppR (SubtermAppR pl) =
>   let indHyp = subtermInAppR pl
>   in SubtermAppR indHyp
> subtermInAppR (SubtermAppL pl) =
>   let indHyp = subtermInAppR pl
>   in SubtermAppL indHyp

> subtermTransitive : {t: Type} -> {a, b, c : Comb t} -> Subterm a b -> Subterm b c -> Subterm a c
> subtermTransitive SubtermEq SubtermEq = SubtermEq
> subtermTransitive SubtermEq r = r
> subtermTransitive l SubtermEq = l
> subtermTransitive {a} {b = App bl br} {c = App cl cr} (SubtermAppL pl) (SubtermAppL pr) =
>   let pr' = subtermInAppL pr
>       indHyp = subtermTransitive {a=a} {b=bl} {c=cl} pl pr'
>   in SubtermAppL indHyp
> subtermTransitive {a} {b = App bl br} {c = App cl cr} (SubtermAppR pl) (SubtermAppR pr) =
>   let pr' = subtermInAppR pr
>       indHyp = subtermTransitive {a=a} {b=br} {c=cr} pl pr'
>   in SubtermAppR indHyp
> subtermTransitive {a} {b = App bl br} {c = App cl cr} (SubtermAppR pl) (SubtermAppL pr) =
>   let pr' = subtermInAppR pr
>       indHyp = subtermTransitive {a=a} {b=br} {c=cl} pl pr'
>   in SubtermAppL indHyp
> subtermTransitive {a} {b = App bl br} {c = App cl cr} (SubtermAppL pl) (SubtermAppR pr) =
>   let pr' = subtermInAppL pr
>       indHyp = subtermTransitive {a=a} {b=bl} {c=cr} pl pr'
>   in SubtermAppR indHyp

> subtermReflexive : {t: Type} -> {a : Comb t} -> Subterm a a
> subtermReflexive = SubtermEq

> {-}
> subtermAnitsymmetric : {t: Type} -> {n, m : Comb t} -> Subterm m n -> Subterm n m -> n = m
> subtermAnitsymmetric SubtermEq _ = Refl
> subtermAnitsymmetric _ SubtermEq = Refl
> subtermAnitsymmetric {n = App l r} {m = App l' r'} (SubtermAppL p1) (SubtermAppL p2) =
>   let indHyp = subtermAnitsymmetric {n=l} {m=l'} (subtermInAppL p1) (subtermInAppL p2)
>   -- in rewrite indHyp
>   in ?subtermAnitsymmetric1
> subtermAnitsymmetric {n = App l r} {m = App l' r'}(SubtermAppR p1) (SubtermAppR p2) =
>   let indHyp = subtermAnitsymmetric {n=r} {m=r'} (subtermInAppR p1) (subtermInAppR p2)
>   -- in rewrite indHyp
>   in ?subtermAnitsymmetric2
> subtermAnitsymmetric {n = App l r} {m = App l' r'} (SubtermAppR p1) (SubtermAppL p2) =
>   let indHyp = subtermAnitsymmetric {n=r} {m= l'} (subtermInAppL p1) (subtermInAppR p2)
>   -- in rewrite indHyp
>   in ?subtermAnitsymmetric3
> subtermAnitsymmetric {n = App l r} {m = App l' r'} (SubtermAppL p1) (SubtermAppR p2) =
>   let indHyp = subtermAnitsymmetric {n=l} {m= r'} (subtermInAppR p1) (subtermInAppL p2)
>   --in rewrite indHyp
>   in ?subtermAnitsymmetric4
> -}


= Reduce : Reduction for Combinators

> interface Reduce b where
>   reduceStep : Comb b -> Maybe (Comb b)

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


Proof that subterm implement Subterm? How to do this?

> {-

-- > subtermLemma : {t : Type} -> DecEq t =>(a : Comb t) ->  {prf : Dec (a = a)} ->subterm' a a prf = True
-- > subtermLemma  x {prf = Yes eqPrf} = Refl
-- > subtermLemma  x {prf = No contra} = void (contra (Refl))

We have the problem that Subterm may point to a right subterm, while the algorithm always detects the leftmost subterm.
So they give the result, but we can't proof them equal

> subtermCorrect : {t : Type} -> (DecEq t) => {a, b: Comb t} -> (prf: Dec (a = b)) -> Subterm a b -> subterm' a b prf = True
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

> subtermComplete : {t : Type} -> (DecEq t) => {a, b: Comb t} -> (prf : Dec (a = b))
>                                                 -> (hyp : subterm' a b prf = True) -> Subterm a b
> subtermComplete {a} {b} (Yes p) hyp = rewrite p in SubtermEq
> subtermComplete {a} {b=App l r} (No p) hyp =
>   let indHyp1 = subtermComplete {a} {b=l} (decEq a l) ?hole0
>       indHyp2 = subtermComplete {a} {b=r} (decEq a r) ?hole1
>   in ?subtermComplete
> subtermComplete {a} {b=Var _} (No p) hyp = absurd hyp
> subtermComplete {a} {b=PrimComb _} (No p) hyp = absurd hyp

> -}
