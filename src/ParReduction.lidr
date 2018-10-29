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
> %hide Prelude.Stream.(::)

== Parallel reduction

-- Non overlapping

-- Change to type level function


> mutual
>

> data Path : Comb b -> Comb b -> Nat -> Type where
>   LP  : Reduce b => {t,l,r: Comb b} -> Path t (App l r) n -> Path t l (S n)
>   RP  : Reduce b => {t,l,r: Comb b} -> Path t (App l r) n -> Path t r 0
>   Top : Reduce b => {t: Comb b} -> Path t t 0

> data Redex : Reduce b => Comb b -> Type where
>   Here : Reduce b => {t: Comb b} -> Path t (PrimComb c m) n -> {auto prf: LT m n} -> Redex t

> excomb : Comb KS
> excomb = :S # (:S # Var "x" # Var "y" # Var "z") # (:S # Var "x" # Var "y" # Var "z") # Var "z"

> path1 : Path ParReduction.excomb :S 3
> path1 = LP (LP (LP Top))

> NonOverlapping : Reduce b => (t: Comb b) -> List (Redex t) -> Type

> ParStep : Reduce b => Comb b -> Comb b -> Type
> ParStep f t = (r: List (Redex t)) -> NonOverlapping t r
