= Combinator : Terms for Combinators

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
> -- ||| Application operator
> (#) : Comb base -> Comb base -> Comb base
> (#) l r = App l r

> combinatorExtensionality : {base: Type} -> {a, b : Comb base} -> (x : Comb base) -> a # x = b # x -> a = b
> combinatorExtensionality {a} {b} x = really_believe_me

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

Using here a new interface to use DecEq for "reductional" equality

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

Subterms

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
> termImpossible : {t: Type} -> {a, b : Comb t} ->  Not (App a b = a)
> termImpossible Refl impossible

> subtermImpossible : {t: Type} -> {a, b : Comb t} ->  Not (Subterm (App a b) a)
> subtermImpossible SubtermEq impossible
> subtermImpossible (SubtermAppL p1) = ?hole

> subtermAnitsymmetric : {t: Type} -> {n, m : Comb t} -> Subterm m n -> Subterm n m -> n = m
> subtermAnitsymmetric SubtermEq _ = Refl
> subtermAnitsymmetric _ SubtermEq = Refl
> subtermAnitsymmetric {n = App l r} {m} (SubtermAppL p1) p2 =
>   let indHyp = subtermAnitsymmetric {n=l} {m} p1 (subtermInAppL p2)
>       rule = subtermImpossible {a=m} {b=r}
>       p2' = replace (sym indHyp) p2
>   in rewrite indHyp
>   in ?hole
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
