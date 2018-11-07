= Simultaneously Reduction : Simultaneously reduction

> module Path

> import Decidable.Equality
> import Relation
> import Combinator
> import CombinatorCompProp
> import Reduction
> import BaseKS
> import Data.List.Quantifiers

> %access public export
> %default total

=== Path

> ||| Path is typed with the combinator, so it can't go wrong
> data Path : {b: Type} -> Comb b -> Type where
>   LP  : Reduce b  => {l,r: Comb b} -> Path l -> Path (App l r)
>   RP  : Reduce b  => {l,r: Comb b} -> Path r -> Path (App l r)
>   Here : Reduce b => {h : Comb b}  -> Path h

> implementation Eq (Path t) where
>   (LP r) == (LP r2) = r == r2
>   (RP m) == (RP m2) = m == m2
>   Here   == Here    = True
>   _       == _        = False

> ||| Pre-order traversal ordering for path
> implementation Ord (Path t) where
>   compare (LP _) (RP _) = LT
>   compare (LP l1) (LP l2) = compare l1 l2
>   compare (LP _) Here = GT
>   compare (RP _) (LP _) = GT
>   compare (RP r1) (RP r2) = compare r1 r2
>   compare (RP _) Here = GT
>   compare Here Here = EQ
>   compare Here _ = LT

> ||| Find Combinator at path
> combAtPath : Reduce b => {combType : Comb b} -> Path combType -> Comb b
> combAtPath (LP p) = combAtPath p
> combAtPath (RP p) = combAtPath p
> combAtPath {combType} Here = combType

> ||| Shorten a path at the end
> shortenPath : Reduce b => {combType : Comb b} -> Path combType -> Path combType
> shortenPath Here = Here
> shortenPath (LP Here) = Here
> shortenPath (LP other) = LP (shortenPath other)
> shortenPath (RP Here) = Here
> shortenPath (RP other) = RP (shortenPath other)

> ||| Shorten a path for n elements at the end
> shortenN: Reduce b => {combType : Comb b} -> Nat -> Path combType -> Path combType
> shortenN Z p = p
> shortenN (S n) p = shortenN n (shortenPath p)

> ||| Return local spine length above path
> arity : Reduce b  => {combType: Comb b} -> {default 0 nn : Nat} -> Path combType -> Nat
> arity {nn} (LP next) = arity {nn=(S nn)} next
> arity {nn} (RP next) = arity {nn=0} next
> arity {nn} Here = nn

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

> asUntypedPath : Path c1 -> PathU
> asUntypedPath (LP c) = LP' (asUntypedPath c)
> asUntypedPath (RP c) = RP' (asUntypedPath c)
> asUntypedPath Here   = Here'

> excomb : Comb KS
> excomb = :S # (:S # Var "x" # Var "y" # Var "z") # (:S # Var "x" # Var "y" # Var "z") # Var "z"

> rcomb : Comb KS
> rcomb = Var "x" # Var "z" # (Var "y" # Var "z") # Var "z" # (Var "x" # Var "z" # (Var "y" # Var "z") # Var "z")

> path1 : Path Path.excomb
> path1 = LP (LP (LP Here))

> path2 : Path  Path.excomb
> path2 = LP (LP (RP (LP (LP (LP Here)))))

> path3 : Path  Path.excomb
> path3 = LP (RP (LP (LP (LP Here))))

> test1 : combAtPath Path.path1 = PrimComb BaseKS.S 3
> test1 = Refl

> test2 : combAtPath (shortenPath Path.path1) = :S # (:S # Var "x" # Var "y" # Var "z")
> test2 = Refl

> test3 : combAtPath (shortenPath (shortenPath Path.path1)) =
>                         :S # (:S # Var "x" # Var "y" # Var "z") # (:S # Var "x" # Var "y" # Var "z")
> test3 = Refl

> test4 : combAtPath (shortenN 2 Path.path1) =
>                         :S # (:S # Var "x" # Var "y" # Var "z") # (:S # Var "x" # Var "y" # Var "z")
> test4 = Refl

> test5 : combAtPath Path.path2 = PrimComb BaseKS.S 3
> test5 = Refl

> test6 : combAtPath Path.path3 = PrimComb BaseKS.S 3
> test6 = Refl
