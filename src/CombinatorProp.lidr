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

=== Equality
TODO: Change to maybe, no algorithm to decide equality

> ||| DecEq instance for weak equality
> ||| Base this on eqStep, when similarity of whr and Steps is established
> implementation (StructEq b, StructEq (Comb b), Reduce b) => DecEq (Comb b) where
>   decEq l r =
>     case structEq l r of
>       Just p =>  Yes $ p
>       Nothing =>
>         let ln = whr l
>             rn = whr r
>         in  case (ln, rn) of
>               (Just ln', Just rn') =>
>                 case structEq ln' rn' of
>                   Just p =>   Yes $ believe_me p
>                   Nothing =>  No $ believe_me ()
>               _ =>  No $ believe_me ()

=== Normal form

> ||| Show that (K S S) is not in normal form
> notNormalKSS : Not (normalForm (Step {b = KS}) (:K # :S # :S))
> notNormalKSS hyp = hyp (:S ** (Prim StepK))

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
>       lemma1 : (z: Comb KS) -> Not (Step (PrimComb S) z)
>       lemma1 z hyp =
>         case hyp of
>           Prim StepS impossible
>           Prim StepK impossible
>           AppL s impossible
>           AppR s impossible


> ||| Weak reduction confluent
> whr_confluent : confluent (Multi Step)
> whr_confluent x y1 y2 step1 step2 = ?whr_confluent_rhs
