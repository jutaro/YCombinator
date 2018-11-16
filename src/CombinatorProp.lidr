= CombinatorProp : Properties of Combinators

> module CombinatorProp

> import Decidable.Equality
> import Control.Isomorphism
> import Combinator
> import Relation
> import Reduction
> import BaseKS
> import Other

> %access public export
> %default total

=== Equality
TODO: Change to maybe, no algorithm to decide equality

> -- Weak equal is a Maybe type and not decidable as:
> --
> --  - we have no algorithm to decide weak equality for all cases
> --  - even stronger: weak equality is general undecidable
>
> -- Correct is weakEq l r -> l = r, but Not (weakEq) -> Not (l = r) is not true
> interface WeakEq t where
>   ||| Decide whether two terms of `base` are weak equal
>   total weakEq : (x1, x2 : t) -> Maybe (x1 = x2)

> ||| WeakEq instance
> ||| TODO: Base this on eqStep, when similarity of whr and Steps is established
> ||| so that we can live with one beleive_me
> implementation (DecEq b, StructEq (Comb b), Reduce b) => WeakEq (Comb b) where
>   weakEq l r =
>     case structEq l r of
>       Just p =>  Just p
>       Nothing =>
>         let ln = whr l
>             rn = whr r
>         in  case (ln, rn) of
>               (Just ln', Just rn') =>
>                 case structEq ln' rn' of
>                   Just p =>   Just $ believe_me p
>                   Nothing =>  Nothing
>               _ =>  Nothing

=== Normal form

> ||| Show that (K S S) is not in normal form
> notNormalKSS : Not (normalForm (Step {b = KS}) (:K # :S # :S))
> notNormalKSS hyp = hyp (:S ** Prim StepK)

> ||| Show that (K S) is in normal form
> normalKS : normalForm (Step {b = KS}) (:K # :S)
> normalKS = forallToExistence (\t, h => case eqStep h of
>                                           hyp => normalKS' t h hyp)
>   where normalKS': (b : Comb KS) -> Step (:K # :S) b -> (:K # :S) = b -> Void
>         normalKS' (PrimComb K _) step Refl impossible
>         normalKS' (PrimComb BaseKS.S _) step Refl impossible
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

=== Deterministic

> ||| We give a counterexample to prove this
> step_not_deterministic : Not (deterministic (Step {b= KS}))
> step_not_deterministic hyp =
>   case hyp (:K # (:K # Var "x" # Var "y") # Var "z")
>             (:K # Var "x" # Var "y")
>             (:K # Var "x" # Var "z")
>             (Prim StepK)
>             (AppL (AppR (Prim StepK))) of
>     Refl impossible

=== Confluence

> stepNotConfluent : Not (confluent (Step {b = KS}))
> stepNotConfluent hyp =
>   let (z ** (lh,rh)) = hyp (:K # :S # (:K # :S # :K)) (:S) (:K # :S # :S) stepK (AppR stepK)
>   in  lemma1 z lh
>     where
>       lemma1 : (z: Comb KS) -> Not (Step :S z)
>       lemma1 z hyp =
>         case hyp of
>           Prim StepS impossible
>           Prim StepK impossible
>           AppL s impossible
>           AppR s impossible

> ||| Weak reduction confluent
> whr_confluent : confluent (Multi Step)
> whr_confluent x y1 y2 step1 step2 = ?whr_confluent_rhs
