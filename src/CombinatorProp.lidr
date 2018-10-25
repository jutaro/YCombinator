= CombinatorProp : Properties of Combinators

> module CombinatorProp

> import Decidable.Equality
> import Control.Isomorphism
> import Combinator
> import Relation
> import Reduction
> import BaseKS

> %access public export
> %default total
> %hide Prelude.Nat.S

> ||| We give a counterexample to prove this
> step_not_deterministic : Not (deterministic (Step {b= KS}))
> step_not_deterministic hyp =
>   case hyp (:K # (:K # Var "x" # Var "y") # Var "z")
>             (:K # Var "x" # Var "y")
>             (:K # Var "x" # Var "z")
>             (Prim StepK)
>             (AppL (AppR (Prim StepK))) of
>     Refl impossible


> ||| Show that (K S) is in normal form
> normalKS : normalForm (Step {b = KS}) (:K # :S)
> normalKS = forallToExistence (\t, h => case eqStep h of
>                                           hyp => normalKS' t h hyp)
>   where normalKS': (b : Comb KS) -> Step (:K # :S) b -> (:K # :S) = b -> Void
>         normalKS' (:K) step Refl impossible
>         normalKS' (:S) step Refl impossible
>         normalKS' (Var _) step Refl impossible
>         normalKS' (App l r) step hyp =
>           case step of
>             Prim _ impossible
>             AppL s2 => case s2 of
>               Prim _ impossible
>               AppL _ impossible
>               AppR _ impossible
>             AppR s2 => case s2 of
>               Prim _ impossible
>               AppL _ impossible
>               AppR _ impossible




> {-}
> normalKS : NormalForm (:K # :S)
> normalKS = Normal (:K # :S) (forallToExistence (:K # :S) normalKSPrf)

> notNormalKSS : NotNormalForm (:K # :S # :S)
> notNormalKSS = NotNormal (:K # :S # :S) (:S ** Prim' StepK)


> isoLemma : (P: Type -> Type) -> Iso (Not (b : Type ** P b)) ({b : Type} -> Not (P b))
> isoLemma P = MkIso from to toFrom fromTo
>   where from : (Not (b : Type ** P b)) -> (b : Type) -> Not (P b)
>         from h1 b h3 = h1 (b ** h3)
>         to : ((b : Type) -> Not (P b)) -> (Not (b : Type ** P b))
>         to h1 (b ** p) = h1 b p
>         toFrom : (y: (b : Type) -> Not (P b)) -> from (to y) = y
>         toFrom y = ?h3
>         fromTo : (x : Not (b : Type ** P b)) -> to (from x) = x
>         fromTo x = ?h4

> isNormalTest1 : isNormalForm (:K # :S) = True
> isNormalTest1 = Refl

> isNormalTest2 : isNormalForm (:K # :S # :S) = False
> isNormalTest2 = Refl

> -}
