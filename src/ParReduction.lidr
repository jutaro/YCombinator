= Parallel Reduction : Simultaneously one step reduction

> module ParReduction

> import Decidable.Equality
> import Relation
> import Combinator
> import Reduction
> import BaseKS
> import Data.List.Quantifiers


> %access public export
> %default total

== Parallel reduction

> ||| Type gives top and target of combinator
> data Path : Comb b -> Comb b -> Type where
>   LP  : Reduce b  => {t,l,r: Comb b} -> Path t l -> Path t (App l r)
>   RP  : Reduce b  => {t,l,r: Comb b} -> Path t r -> Path t (App l r)
>   Here : Reduce b => {h : Comb b} -> Path h h

> ||| Untyped version of path
> data PathU : Type where
>   LP'  : PathU -> PathU
>   RP'  : PathU -> PathU
>   Here' : PathU

> implementation Eq PathU where
>   (LP' r) == (LP' r2) = r == r2
>   (RP' m) == (RP' m2) = m == m2
>   Here'   == Here'    = True
>   _       == _        = False

> ||| Pre-order traversal ordering for path
> implementation Ord PathU where
>   compare (LP' _) (RP' _) = LT
>   compare (LP' l1) (LP' l2) = compare l1 l2
>   compare (LP' _) Here' = GT
>   compare (RP' _) (LP' _) = GT
>   compare (RP' r1) (RP' r2) = compare r1 r2
>   compare (RP' _) Here' = GT
>   compare Here' Here' = EQ
>   compare Here' _ = LT

> ||| Return local spine length above target
> arity : Reduce b  => {from, to: Comb b} -> Nat -> Path from to -> Nat
> arity n (LP next) = arity (S n) next
> arity n (RP next) = arity 0 next
> arity n Here = n

> data Redex : Comb b -> Type where
>   RPath : {b: Type} -> Reduce b => {bb : b} -> {t: Comb b} -> (p : Path (PrimComb bb n) t) -> {-- {auto prf: LTE n (arity 0 p)} -> --} Redex t

> excomb : Comb KS
> excomb = :S # (:S # Var "x" # Var "y" # Var "z") # (:S # Var "x" # Var "y" # Var "z") # Var "z"

> path1 : Path  :S ParReduction.excomb
> path1 = LP (LP (LP Here))

> redex1 : Redex ParReduction.excomb
> redex1 = RPath path1

> path2 : Path  :S ParReduction.excomb
> path2 = LP (LP (RP (LP (LP (LP Here)))))

> redex2 : Redex ParReduction.excomb
> redex2 = RPath path2

> asUntypedPath : Path c1 c2 -> PathU
> asUntypedPath (LP c) = LP' (asUntypedPath c)
> asUntypedPath (RP c) = RP' (asUntypedPath c)
> asUntypedPath Here   = Here'

> applyRedex : (co: Comb KS) -> (co2: Comb KS) -> Redex co -> Step {b = KS} co co2
> applyRedex (App (App :K a) b) a (RPath (LP (LP Here))) = stepK {x=a} {y=b}
> applyRedex (App (App (App :S a) b) c) (App (App a c) (App b c)) (RPath (LP (LP (LP Here)))) = stepS {x=a} {y=b} {z=c}
> applyRedex (App l1 r) (App l2 r) (RPath (LP p)) = AppL (applyRedex l1 l2 (RPath p))
> applyRedex (App l r1) (App l r2) (RPath (RP p)) = AppR (applyRedex r1 r2 (RPath p))



> -- applyRedex (Here (LP _)) = AppL applyRedex ps s)
> -- applyRedex (Here (RP _)) = applyRedex (AppR ps s)

> {--
> -- ||| Apply redexes consecutively in reverse pre order
> -- TODO: What does non overlapping mean?
> parStep : Reduce b => (t: Comb b) -> List (Redex t) -> Muti Step t tr
> parStep t redexes =
>   let redexesSorted = sort redexes
>   in foldr (\ multiStep, redex => MultiStep (applyRedex redex) multiStep) MultiRefl redexesSorted
>     where

> ||| --- Test code ---


> --}
