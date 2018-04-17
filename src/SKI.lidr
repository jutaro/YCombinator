= SKI : Combinator reduction

> module SKI
> import Debug.Trace

> %access public export
> %default total

> data Term : Type where
>   I : Term
>   K : Term
>   S : Term
>   Var : String -> Term
>   App : Term -> Term -> Term

> implementation Eq Term where
>   I == I = True
>   K == K = True
>   S == S = True
>   (Var a) == (Var b) = a == b
>   (App a b) == (App c d) = a == c && b == d
>   _ == _ = False

> implementation Show Term where
>   show I = "I"
>   show K = "K"
>   show S = "S"
>   show (Var a) = a
>   show (App a b) = "(" ++ show a ++ " @ " ++ show b ++ ")"

> syntax [app] "@" [applied]   = App app applied;
> syntax ":" [var]    = Var var;

> subterm : Term -> Term -> Bool
> subterm x (App l r) with (x == (App l r))
>   | True  = True
>   | False = if subterm x l
>             then True
>             else subterm x r
> subterm x y = x == y

> data Subterm : Term -> Term -> Type where
>   SubtermEq : Subterm x x
>   SubtermAppL : Subterm x l -> Subterm x (l @ r)
>   SubtermAppR : Subterm x r -> Subterm x (l @ r)

> subtermTest1 : Subterm (K @ S) ((K @ S) @ I)
> subtermTest1 = SubtermAppL $ SubtermEq

> subtermTest1' : subterm (K @ S) ((K @ S) @ I) = True
> subtermTest1' = Refl

> subtermLemmaL : Subterm (l @ r) b -> Subterm l b
> subtermLemmaL SubtermEq = SubtermAppL $ SubtermEq
> subtermLemmaL (SubtermAppL pl) =
>   let indHyp = subtermLemmaL pl
>   in SubtermAppL indHyp
> subtermLemmaL (SubtermAppR pl) =
>   let indHyp = subtermLemmaL pl
>   in SubtermAppR indHyp

> subtermLemmaR : Subterm (l @ r) b -> Subterm r b
> subtermLemmaR SubtermEq = SubtermAppR $ SubtermEq
> subtermLemmaR (SubtermAppL pl) =
>   let indHyp = subtermLemmaL pl
>   in SubtermAppL indHyp
> subtermLemmaR (SubtermAppR pl) =
>   let indHyp = subtermLemmaL pl
>   in SubtermAppR indHyp

> subtermTransitive : {a, b, c : Term} -> Subterm a b -> Subterm b c -> Subterm a c
> subtermTransitive SubtermEq SubtermEq = SubtermEq
> subtermTransitive SubtermEq r = r
> subtermTransitive l SubtermEq = l
> subtermTransitive {a} {b = App bl br} {c = App cl cr} (SubtermAppL pl) (SubtermAppL pr) =
>   let pr' = subtermLemmaL pr
>       indHyp = subtermTransitive {a=a} {b=bl} {c=cl} pl pr'
>   in SubtermAppL indHyp
> subtermTransitive {a} {b} {c} _ _  = ?holen
