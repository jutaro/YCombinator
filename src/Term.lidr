= Term : Terms for Combinators

> import Decidable.Equality

> %hide Language.Reflection.I
> %hide Language.Reflection.Var

> %access public export
> %default total


> -- ||| a term can be a variable, a primitive combinator or an application
> data Term : (base: Type) -> Type where
>   PrimComb : base -> Term base
>   Var : String -> Term base
>   App : Term base -> Term base -> Term base

> infixl 9 ##

> (##) : Term base -> Term base -> Term base
> (##) l r = App l r

> implementation (Eq t) => Eq (Term t) where
>   (PrimComb a)  == (PrimComb b)  = a == b
>   (Var a)   == (Var b)   = a == b
>   (App a b) == (App c d) = a == c && b == d
>   _         == _         = False

> implementation (Show t) => Show (Term t) where
>   show (PrimComb c) = ":" ++ show c
>   show (Var a) = "(Var " ++ a ++ ")"
>   show (App a b) = "(" ++ show a ++ " ## " ++ show b ++ ")"


> varInjective : {a, b : String} -> Var a = Var b -> a = b
> varInjective Refl = Refl

> baseInjective : {a, b : t} -> PrimComb a = PrimComb b -> a = b
> baseInjective Refl = Refl

> appCongruent : {a, b, c, d : Term t} -> a = c -> b = d -> App a b = App c d
> appCongruent Refl Refl = Refl

> appInjective : {a, b, c, d : Term t}  -> App a b = App c d -> (a = c, b = d)
> appInjective Refl = (Refl,Refl)

> varNotPrimComb : {a : String} -> Var a = PrimComb t -> Void
> varNotPrimComb Refl impossible

> varNotApp : {a : String} -> {l, r : Term t} -> Var a = App l r -> Void
> varNotApp Refl impossible

> baseNotApp : PrimComb t = App l r -> Void
> baseNotApp Refl impossible

> implementation (DecEq t) => DecEq (Term t) where
>   decEq (Var a) (Var b) with (decEq a b)
>     | Yes p = Yes $ cong p
>     | No p  = No $ \h : Var a = Var b => p (varInjective h)
>   decEq (PrimComb a) (PrimComb b) with (decEq a b)
>     | Yes p = Yes $ cong p
>     | No p  = No $ \h : PrimComb a = PrimComb b => p (baseInjective h)

>   decEq (App a b) (App c d) with (decEq a c)
>     decEq (App a b) (App c d) | Yes p with (decEq b d)
>       decEq (App a b) (App c d) | Yes p | Yes p' = Yes $ appCongruent p p'
>       decEq (App a b) (App c d) | Yes p | No p' =  No $ \h : App a b = App c d => p' (snd (appInjective h))
>     decEq (App a b) (App c d) | No p = No $ \h : App a b = App c d => p (fst (appInjective h))

>   decEq (Var a) (PrimComb t) = No varNotPrimComb
>   decEq (Var a) (App l r) = No varNotApp
>   decEq (PrimComb t) (Var b) = No (negEqSym varNotPrimComb)
>   decEq (PrimComb t) (App l r) = No (baseNotApp)
>   decEq (App l r) (Var a) = No (negEqSym varNotApp)
>   decEq (App l r) (PrimComb t) = No (negEqSym baseNotApp)

> subterm' : {t : Type} -> DecEq t => (t1 : Term t) -> (t2 : Term t) -> Dec (t1 = t2) -> Bool
> subterm' a b (Yes _) = True
> subterm' a b (No  _) = case b of
>                 (App l r) => subterm' a l (decEq a l) || subterm' a r (decEq a r)
>                 _ => False

> subterm : {t : Type} -> DecEq t => (t1 : Term t) -> (t2 : Term t) -> Bool
> subterm a b = subterm' a b (decEq a b)

> data Subterm : Term b -> Term b -> Type where
>   SubtermEq : Subterm x x
>   SubtermAppL : Subterm x l -> Subterm x (l ## r)
>   SubtermAppR : Subterm x r -> Subterm x (l ## r)

> subtermInAppL : Subterm (l ## r) b -> Subterm l b
> subtermInAppL SubtermEq = SubtermAppL $ SubtermEq
> subtermInAppL (SubtermAppL pl) =
>   let indHyp = subtermInAppL pl
>   in SubtermAppL indHyp
> subtermInAppL (SubtermAppR pl) =
>   let indHyp = subtermInAppL pl
>   in SubtermAppR indHyp

> subtermInAppR : Subterm (l ## r) b -> Subterm r b
> subtermInAppR SubtermEq = SubtermAppR $ SubtermEq
> subtermInAppR (SubtermAppR pl) =
>   let indHyp = subtermInAppR pl
>   in SubtermAppR indHyp
> subtermInAppR (SubtermAppL pl) =
>   let indHyp = subtermInAppR pl
>   in SubtermAppL indHyp

> subtermTransitive : {t: Type} -> {a, b, c : Term t} -> Subterm a b -> Subterm b c -> Subterm a c
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

> subtermReflexive : {t: Type} -> {a : Term t} -> Subterm a a
> subtermReflexive = SubtermEq

> subtermAnitsymmetric : {t: Type} -> {n, m : Term t} -> Subterm m n -> Subterm n m -> n = m
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


Proof that subterm implement Subterm? How to do this?

> {-

-- > subtermLemma : {t : Type} -> DecEq t =>(a : Term t) ->  {prf : Dec (a = a)} ->subterm' a a prf = True
-- > subtermLemma  x {prf = Yes eqPrf} = Refl
-- > subtermLemma  x {prf = No contra} = void (contra (Refl))

We have the problem that Subterm may point to a right subterm, while the algorithm always detects the leftmost subterm.
So they give the result, but we can't proof them equal

> subtermCorrect : {t : Type} -> (DecEq t) => {a, b: Term t} -> (prf: Dec (a = b)) -> Subterm a b -> subterm' a b prf = True
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

> subtermComplete : {t : Type} -> (DecEq t) => {a, b: Term t} -> (prf : Dec (a = b))
>                                                 -> (hyp : subterm' a b prf = True) -> Subterm a b
> subtermComplete {a} {b} (Yes p) hyp = rewrite p in SubtermEq
> subtermComplete {a} {b=App l r} (No p) hyp =
>   let indHyp1 = subtermComplete {a} {b=l} (decEq a l) ?hole0
>       indHyp2 = subtermComplete {a} {b=r} (decEq a r) ?hole1
>   in ?subtermComplete
> subtermComplete {a} {b=Var _} (No p) hyp = absurd hyp
> subtermComplete {a} {b=PrimComb _} (No p) hyp = absurd hyp

> -}
