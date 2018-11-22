= Combinator : Terms for Combinators

> module Combinator

> import Decidable.Equality
> import Lib.Id

> %access public export
> %default total
> %hide Language.Reflection.Var
> %hide Prelude.Show.Eq

> mutual
>
> -- ||| a term can be a a primitive combinator or an application
> -- ||| or a variable. Variables are just placeholders and no substitution will be defined
>   data Comb : (base: Type) -> Type where
>     PrimComb : Reduce base => base -> Nat -> Comb base
>     App : {base: Type} -> Comb base -> Comb base -> Comb base
>     Var : Id -> Comb base
>

> -- Combinatory bases are implemented with this interface
>   interface DecEq base => Reduce base where
>     ||| computational reduction
>     reduceStep : Comb base -> Maybe (Comb base)
>     ||| type level reduction
>     PrimRed    : {base : Type} -> Comb base -> Comb base -> Type

> infixl 9 #
> -- ||| Application operator
> (#) : {base:Type} -> Comb base -> Comb base -> Comb base
> (#) = App

> implementation Eq base => Eq (Comb base) where
>   (PrimComb a _) == (PrimComb b _) = a == b
>   (App a b)    == (App c d)    = a == c && b == d
>   (Var n1)     == (Var n2)     = n1 == n2
>   _            == _            = False

> implementation Show base => Show (Comb base) where
>   showPrec d (PrimComb c _) = show c
>   showPrec d (Var n)   = show n
>   showPrec d (App a b) = showParens (d > Open) (showPrec Open a ++ " # " ++ showPrec App b)

> -- Counts the nodes of a combinator
> combSize : Comb base -> Int
> combSize (App l r) = 1 + combSize l + combSize r
> combSize _ = 0

> ||| Number of binary trees with n internal nodes is:
> catalan : Integer -> Integer
> catalan 0 = 0
> catalan 1 = 1
> catalan n = assert_total ((2 * (2 * n - 1) * catalan (n - 1)) `div` (n + 1))

> -- this is a specialized version of `appInjective` below
> combinatorExtensionality : {a, b : Comb base} -> (x : Comb base) -> Reduce base => a # x = b # x -> a = b
> combinatorExtensionality _ Refl = Refl

> combInjective : {a, b : base} -> Reduce base => PrimComb a = PrimComb b -> a = b
> combInjective Refl = Refl

> varInjective : Var a = Var b -> a = b
> varInjective Refl = Refl

> varCongruent : a = b -> Var {base} a = Var {base} b
> varCongruent Refl = Refl

> appCongruent : {a, b, c, d : Comb base} -> a = c -> b = d -> App a b = App c d
> appCongruent Refl Refl = Refl

> primCongruent : {a, b: base} -> Reduce base => {n, m: Nat} -> a = b -> n = m -> PrimComb a n = PrimComb b m
> primCongruent Refl Refl = Refl

> appInjective : {a, b, c, d : Comb base}  -> App a b = App c d -> (a = c, b = d)
> appInjective Refl = (Refl,Refl)

> primNotApp : {a : base} -> (Reduce base) => PrimComb a _ = Combinator.App _ _ -> Void
> primNotApp Refl impossible

> varNotPrim : {a : base} -> (Reduce base) => Var n = PrimComb a _ -> Void
> varNotPrim Refl impossible

> varNotApp : Var n = App _ _ -> Void
> varNotApp Refl impossible

Using here a new interface to use DecEq for "reductional" equality


> -- Correct is structEq l r -> l = r, but Not (structEq) -> Not (l = r) is not true
> -- as we will define '=' as weak equality
> interface StructEq t where
>   ||| Decide whether two elements of `base` are propositionally equal
>   total structEq : (x1, x2 : t) -> Maybe (x1 = x2)

> implementation (DecEq base) => StructEq (Comb base) where
>   structEq (PrimComb a n) (PrimComb b m) with (decEq a b,decEq n m)
>     | (Yes prf1,Yes prf2)  = Just $ rewrite prf1 in cong prf2
>     | _  = Nothing
>   structEq (App a b) (App c d) with (structEq a c)
>     structEq (App a b) (App c d) | Just p with (structEq b d)
>       structEq (App a b) (App c d) | Just p | Just p' = Just $ appCongruent p p'
>       structEq (App a b) (App c d) | Just p | Nothing =  Nothing
>     structEq (App a b) (App c d) | Nothing = Nothing
>   structEq (Var n1) (Var n2) with (decEq n1 n2)
>     | Yes p = Just $ cong p
>     | No contra = Nothing
>   structEq (PrimComb c _) (App l r) = Nothing
>   structEq (App l r) (PrimComb c _) = Nothing
>   structEq (Var n) (PrimComb c _)   = Nothing
>   structEq (PrimComb c _) (Var n)   = Nothing
>   structEq (Var n) (App l r)        = Nothing
>   structEq (App l r) (Var n)        = Nothing

Subterms

> subterm' : StructEq (Comb base) => (t1, t2 : Comb base) -> Maybe (t1 = t2) -> Bool
> subterm' t1 t2            (Just _)  = True
> subterm' t1 (App t2l t2r) Nothing   = subterm' t1 t2l (structEq t1 t2l) || subterm' t1 t2r (structEq t1 t2r)
> subterm' t1 _             Nothing   = False

> subterm : StructEq (Comb base) => (t1, t2 : Comb base) -> Bool
> subterm t1 t2 = subterm' t1 t2 (structEq t1 t2)

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

> subtermTransitive : {base: Type} -> {a, b, c : Comb base} -> Subterm a b -> Subterm b c -> Subterm a c
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

> subtermReflexive : {base: Type} -> {a : Comb base} -> Subterm a a
> subtermReflexive = SubtermEq

> termImpossible : {base: Type} -> {a, b : Comb base} ->  Not (App a b = a)
> termImpossible Refl impossible

> mutual
>   subtermImpossibleR : Not (Subterm (App a b) b)
>   subtermImpossibleR SubtermEq impossible
>   subtermImpossibleR {b=PrimComb _ _} (SubtermAppL _) impossible
>   subtermImpossibleR {b=PrimComb _ _} (SubtermAppR _) impossible
>   subtermImpossibleR {b=App _ _} (SubtermAppL s) = subtermImpossibleL $ subtermInAppR s
>   subtermImpossibleR {b=App _ _} (SubtermAppR s) = subtermImpossibleR $ subtermInAppR s

>   subtermImpossibleL : Not (Subterm (App a b) a)
>   subtermImpossibleL SubtermEq impossible
>   subtermImpossibleL {a=PrimComb _ _} (SubtermAppL _) impossible
>   subtermImpossibleL {a=PrimComb _ _} (SubtermAppR _) impossible
>   subtermImpossibleL {a=App _ _} (SubtermAppL s) = subtermImpossibleL $ subtermInAppL s
>   subtermImpossibleL {a=App _ _} (SubtermAppR s) = subtermImpossibleR $ subtermInAppL s

> subtermAntisymmetric : {n, m : Comb base} -> Subterm m n -> Subterm n m -> n = m
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
