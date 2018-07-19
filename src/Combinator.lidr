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

> combinatorExtensionality : {a, b : Comb base} -> (x : Comb base) -> a # x = b # x -> a = b
> combinatorExtensionality _ Refl = Refl

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

> Uninhabited (PrimComb _ = App _ _) where
>   uninhabited Refl impossible

> Uninhabited (App _ _ = PrimComb _) where
>   uninhabited Refl impossible

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

>   structEq (PrimComb t) (App l r) = No absurd
>   structEq (App l r) (PrimComb t) = No absurd

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
>       indHyp = subtermTransitive {a} {b=bl} {c=cl} pl pr'
>   in SubtermAppL indHyp
> subtermTransitive {a} {b = App bl br} {c = App cl cr} (SubtermAppR pl) (SubtermAppR pr) =
>   let pr' = subtermInAppR pr
>       indHyp = subtermTransitive {a} {b=br} {c=cr} pl pr'
>   in SubtermAppR indHyp
> subtermTransitive {a} {b = App bl br} {c = App cl cr} (SubtermAppR pl) (SubtermAppL pr) =
>   let pr' = subtermInAppR pr
>       indHyp = subtermTransitive {a} {b=br} {c=cl} pl pr'
>   in SubtermAppL indHyp
> subtermTransitive {a} {b = App bl br} {c = App cl cr} (SubtermAppL pl) (SubtermAppR pr) =
>   let pr' = subtermInAppL pr
>       indHyp = subtermTransitive {a} {b=bl} {c=cr} pl pr'
>   in SubtermAppR indHyp

> subtermReflexive : {t: Type} -> {a : Comb t} -> Subterm a a
> subtermReflexive = SubtermEq

> termImpossible : {t: Type} -> {a, b : Comb t} ->  Not (App a b = a)
> termImpossible Refl impossible

> mutual
>   subtermImpossibleR : Not (Subterm (App a b) b)
>   subtermImpossibleR SubtermEq impossible
>   subtermImpossibleR {b=PrimComb _} (SubtermAppL _) impossible
>   subtermImpossibleR {b=PrimComb _} (SubtermAppR _) impossible
>   subtermImpossibleR {b=App _ _} (SubtermAppL s) = subtermImpossibleL $ subtermInAppR s
>   subtermImpossibleR {b=App _ _} (SubtermAppR s) = subtermImpossibleR $ subtermInAppR s

>   subtermImpossibleL : Not (Subterm (App a b) a)
>   subtermImpossibleL SubtermEq impossible
>   subtermImpossibleL {a=PrimComb _} (SubtermAppL _) impossible
>   subtermImpossibleL {a=PrimComb _} (SubtermAppR _) impossible
>   subtermImpossibleL {a=App _ _} (SubtermAppL s) = subtermImpossibleL $ subtermInAppL s
>   subtermImpossibleL {a=App _ _} (SubtermAppR s) = subtermImpossibleR $ subtermInAppL s

> subtermAntisymmetric : {n, m : Comb t} -> Subterm m n -> Subterm n m -> n = m
> subtermAntisymmetric SubtermEq _ = Refl
> subtermAntisymmetric _ SubtermEq = Refl
> subtermAntisymmetric {n=l1 # r1} {m=l2 # r2} (SubtermAppL s1) (SubtermAppL s2) = 
>   let ih = subtermAntisymmetric {n=l1} {m=l2} (subtermInAppL s1) (subtermInAppL s2) in
>   absurd $ subtermImpossibleL $ replace ih s1
> subtermAntisymmetric {n=l1 # r1} {m=l2 # r2} (SubtermAppL s1) (SubtermAppR s2) = 
>   let ih = subtermAntisymmetric {n=l1} {m=r2} (subtermInAppR s1) (subtermInAppL s2) in  
>   absurd $ subtermImpossibleR $ replace ih s1
> subtermAntisymmetric {n=l1 # r1} {m=l2 # r2} (SubtermAppR s1) (SubtermAppL s2) = 
>   let ih = subtermAntisymmetric {n=r1} {m=l2} (subtermInAppL s1) (subtermInAppR s2) in
>   absurd $ subtermImpossibleL $ replace ih s1
> subtermAntisymmetric {n=l1 # r1} {m=l2 # r2} (SubtermAppR s1) (SubtermAppR s2) = 
>   let ih = subtermAntisymmetric {n=r1} {m=r2} (subtermInAppR s1) (subtermInAppR s2) in
>   absurd $ subtermImpossibleR $ replace ih s1
