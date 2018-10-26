= Combinator : Terms for Combinators

> module Combinator

> import Decidable.Equality

> %access public export
> %default total
> %hide Language.Reflection.Var

> mutual
>
> -- ||| a term can be a a primitive combinator or an application
> -- ||| Vars are in the meta language (Idris)
>   data Comb : (base: Type) -> Type where
>     PrimComb : Reduce base => base -> Comb base
>     App : Comb base -> Comb base -> Comb base
>     Var : String -> Comb base
>
> -- Combinatory bases are implemented with this type
>   interface Reduce base where
>     reduceStep : Comb base -> Maybe (Comb base)
>     PrimRed    : Comb base -> Comb base -> Type

> infixl 9 #
> -- ||| Application operator
> (#) : Comb base -> Comb base -> Comb base
> (#) = App

> -- this is a specialized version of `appInjective` below
> combinatorExtensionality : {a, b : Comb base} -> (x : Comb base) -> a # x = b # x -> a = b
> combinatorExtensionality _ Refl = Refl

> implementation (Eq t) => Eq (Comb t) where
>   (PrimComb a) == (PrimComb b) = a == b
>   (App a b)    == (App c d)    = a == c && b == d
>   (Var n1)     == (Var n2)     = n1 == n2
>   _            == _            = False

> implementation (Show t) => Show (Comb t) where
>   showPrec d (PrimComb c) = show c
>   showPrec d (Var n)   = show n
>   showPrec d (App a b) = showParens (d > Open) (showPrec Open a ++ " # " ++ showPrec App b)

> combInjective : {a, b : base} -> Reduce base => PrimComb a = PrimComb b -> a = b
> combInjective Refl = Refl

> varInjective : Var a = Var b -> a = b
> varInjective Refl = Refl

> appCongruent : {a, b, c, d : Comb t} -> a = c -> b = d -> App a b = App c d
> appCongruent Refl Refl = Refl

> appInjective : {a, b, c, d : Comb t}  -> App a b = App c d -> (a = c, b = d)
> appInjective Refl = (Refl,Refl)

> primNotApp : {a : base} -> (Reduce base) => PrimComb a = App _ _ -> Void
> primNotApp Refl impossible

> varNotPrim : {a : base} -> (Reduce base) => Var n = PrimComb a -> Void
> varNotPrim Refl impossible

> varNotApp : Var n = App _ _ -> Void
> varNotApp Refl impossible

Using here a new interface to use DecEq for "reductional" equality


> -- Correct is structEq l r -> l = r, but Not (structEq) -> Not (l = r) is not true
> -- as we will define '=' as weak equality
> interface StructEq t where
>   ||| Decide whether two elements of `t` are propositionally equal
>   total structEq : (x1, x2 : Comb t) -> Maybe (x1 = x2)

> implementation (DecEq base, Reduce base, DecEq (Comb base)) => StructEq (Comb base) where
>   structEq (PrimComb a) (PrimComb b) with (decEq a b)
>     | Yes prf  = Just $ cong prf
>     | No contra  = Nothing
>   structEq (App a b) (App c d) with (structEq a c)
>     structEq (App a b) (App c d) | Just p with (structEq b d)
>       structEq (App a b) (App c d) | Just p | Just p' = Just $ appCongruent p p'
>       structEq (App a b) (App c d) | Just p | Nothing =  Nothing
>     structEq (App a b) (App c d) | Nothing = Nothing
>   structEq (Var n1) (Var n2) with (decEq n1 n2)
>     | Yes p = Just $ cong p
>     | No contra = Nothing
>   structEq (PrimComb t) (App l r) = Nothing
>   structEq (App l r) (PrimComb t) = Nothing
>   structEq (Var n) (PrimComb t)   = Nothing
>   structEq (PrimComb t) (Var n)   = Nothing
>   structEq (Var n) (App l r)      = Nothing
>   structEq (App l r) (Var n)      = Nothing

Subterms

> subterm' : (StructEq t, Reduce t) => (t1, t2 : Comb t) -> Maybe (t1 = t2) -> Bool
> subterm' a b         (Just _) = True
> subterm' a (App l r) Nothing  = subterm' a l (structEq a l) || subterm' a r (structEq a r)
> subterm' a _         Nothing  = False

> subterm : (StructEq (Comb t), StructEq t, Reduce t) => (t1, t2 : Comb t) -> Bool
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
> subtermTransitive {b = App bl br} {c = App cl cr} (SubtermAppL pl) (SubtermAppL pr) =
>   let pr' = subtermInAppL pr
>       indHyp = subtermTransitive {b=bl} {c=cl} pl pr'
>   in SubtermAppL indHyp
> subtermTransitive {b = App bl br} {c = App cl cr} (SubtermAppR pl) (SubtermAppR pr) =
>   let pr' = subtermInAppR pr
>       indHyp = subtermTransitive {b=br} {c=cr} pl pr'
>   in SubtermAppR indHyp
> subtermTransitive {b = App bl br} {c = App cl cr} (SubtermAppR pl) (SubtermAppL pr) =
>   let pr' = subtermInAppR pr
>       indHyp = subtermTransitive {b=br} {c=cl} pl pr'
>   in SubtermAppL indHyp
> subtermTransitive {b = App bl br} {c = App cl cr} (SubtermAppL pl) (SubtermAppR pr) =
>   let pr' = subtermInAppL pr
>       indHyp = subtermTransitive {b=bl} {c=cr} pl pr'
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
> subtermAntisymmetric                        SubtermEq        _               = Refl
> subtermAntisymmetric                        _                SubtermEq       = Refl
> subtermAntisymmetric {n=l1 # _} {m=l2 # _} (SubtermAppL s1) (SubtermAppL s2) =
>   let ih = subtermAntisymmetric {n=l1} {m=l2} (subtermInAppL s1) (subtermInAppL s2) in
>   absurd $ subtermImpossibleL $ replace ih s1
> subtermAntisymmetric {n=l1 # _} {m=_ # r2} (SubtermAppL s1) (SubtermAppR s2) =
>   let ih = subtermAntisymmetric {n=l1} {m=r2} (subtermInAppR s1) (subtermInAppL s2) in
>   absurd $ subtermImpossibleR $ replace ih s1
> subtermAntisymmetric {n=_ # r1} {m=l2 # _} (SubtermAppR s1) (SubtermAppL s2) =
>   let ih = subtermAntisymmetric {n=r1} {m=l2} (subtermInAppL s1) (subtermInAppR s2) in
>   absurd $ subtermImpossibleL $ replace ih s1
> subtermAntisymmetric {n=_ # r1} {m=_ # r2} (SubtermAppR s1) (SubtermAppR s2) =
>   let ih = subtermAntisymmetric {n=r1} {m=r2} (subtermInAppR s1) (subtermInAppR s2) in
>   absurd $ subtermImpossibleR $ replace ih s1
