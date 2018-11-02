= Simultaneously Reduction : Simultaneously reduction

> module ParReduction

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

> ||| Type gives type of combinator
> data Path : Comb b -> Type where
>   LP  : Reduce b  => {l,r: Comb b} -> Path l -> Path (App l r)
>   RP  : Reduce b  => {l,r: Comb b} -> Path r -> Path (App l r)
>   Here : Reduce b => {h : Comb b}  -> Path h

> ||| Find Combinator at path
> combAtPath : {b: Type} -> Reduce b => {combType : Comb b} -> Path combType -> Comb b
> combAtPath (LP p) = combAtPath p
> combAtPath (RP p) = combAtPath p
> combAtPath {combType} Here = combType

> ||| Shorten a path
> shortenPath : {b: Type} -> Reduce b => {combType : Comb b} -> Path combType -> Path combType
> shortenPath Here = Here
> shortenPath (LP Here) = Here
> shortenPath (LP other) = LP (shortenPath other)
> shortenPath (RP Here) = Here
> shortenPath (RP other) = RP (shortenPath other)

> shortenN: {b: Type} -> Reduce b => {combType : Comb b} -> Nat -> Path combType -> Path combType
> shortenN Z p = p
> shortenN (S n) p = shortenN n (shortenPath p)

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


=== Redex

> ||| Return local spine length above path
> arity : Reduce b  => {combType: Comb b} -> {default 0 nn : Nat} -> Path combType -> Nat
> arity {nn} (LP next) = arity {nn=(S nn)} next
> arity {nn} (RP next) = arity {nn=0} next
> arity {nn} Here = nn

> data Redex : Comb b -> Type where
>    RPath :  Reduce b =>
>               {t, t1,t2: Comb b} ->
>               PrimRed t1 t2 ->
>               (p : Path t) ->
>               {auto prf1: LTE n (arity p)} ->
>               {auto prf2: combAtPath (shortenN (arity p) p) = t1} ->
>               Redex t

> implementation Eq (Redex t) where
>   (RPath pr1 p1) == (RPath pr2 p2) = asUntypedPath p1 == asUntypedPath p2

> implementation Ord (Redex t) where
>   compare (RPath pr1 p1) (RPath pr2 p2) = compare (asUntypedPath p1) (asUntypedPath p2)

> {--
> applyRedex : Reduce b => Redex t -> Step t1 t2
> applyRedex redex = ?applyRedex_rhs


> ||| A function which performs a simultaneous reduction
> simStep : Reduce b => (t: Comb b) -> List (Redex t) -> Multi Step t tr
> simStep comb redexList =
>   let redexesSorted = sort redexList
>       res = foldr (\ redex , (c,multiStep) => (c,MultiStep (applyRedex redex) multiStep))
>               (comb,MultiRefl) redexesSorted
>   in believe_me $ snd res

>   RPath : Reduce base => {t: Comb base} -> (p : Path (PrimComb base n) t) -> {auto prf: LTE n (arity 0 p)} -> Redex t


> transformType : {t,t2,t3: Comb base} -> (p : Path (PrimComb base n) t) -> (t2->t3)





> applyRedex : (co: Comb KS) -> Redex (co -> co2) -> Step co co2


> applyRedex : (co: Comb KS) -> (co2: Comb KS) -> Redex co -> Step {b = KS} co co2
> applyRedex (App (App :K a) b) a (RPath (LP (LP Here))) = stepK {x=a} {y=b}
> applyRedex (App (App (App :S a) b) c) (App (App a c) (App b c)) (RPath (LP (LP (LP Here)))) = stepS {x=a} {y=b} {z=c}
> applyRedex (App l1 r) (App l2 r) (RPath (LP p)) = AppL (applyRedex l1 l2 (RPath p))
> applyRedex (App l r1) (App l r2) (RPath (RP p)) = AppR (applyRedex r1 r2 (RPath p))



> -- applyRedex (Here (LP _)) = AppL applyRedex ps s)
> -- applyRedex (Here (RP _)) = applyRedex (AppR ps s)


> -- ||| Apply redexes consecutively in reverse pre order
> -- TODO: What does non overlapping mean?
> parStep : Reduce b => {t,tr: Comb b} -> List (Redex t) -> Muti Step t tr
> parStep t redexes =
>   let redexesSorted = sort redexes
>   in foldr (\ multiStep, redex => MultiStep (applyRedex redex) multiStep) MultiRefl redexesSorted
>     where

> ||| --- Test code ---


> --}

==== Test cases

> excomb : Comb KS
> excomb = :S # (:S # Var "x" # Var "y" # Var "z") # (:S # Var "x" # Var "y" # Var "z") # Var "z"

> rcomb : Comb KS
> rcomb = :S # (:S # Var "x" # Var "y" # Var "z") # (:S # Var "x" # Var "y" # Var "z") # Var "z"

> path1 : Path ParReduction.excomb
> path1 = LP (LP (LP Here))

> redex1 : Redex ParReduction.excomb
> redex1 = RPath StepS path1

> path2 : Path  ParReduction.excomb
> path2 = LP (LP (RP (LP (LP (LP Here)))))

> redex2 : Redex ParReduction.excomb
> redex2 = RPath StepS path2

> path3 : Path  ParReduction.excomb
> path3 = LP (RP (LP (LP (LP Here))))

> redex3 : Redex ParReduction.excomb
> redex3 = RPath StepS path3

> test1 : combAtPath ParReduction.path1 = PrimComb BaseKS.S 3
> test1 = Refl

> test2 : combAtPath (shortenPath ParReduction.path1) = :S # (:S # Var "x" # Var "y" # Var "z")
> test2 = Refl

> test3 : combAtPath (shortenPath (shortenPath ParReduction.path1)) =
>                         :S # (:S # Var "x" # Var "y" # Var "z") # (:S # Var "x" # Var "y" # Var "z")
> test3 = Refl

> test4 : combAtPath (shortenN 2 ParReduction.path1) =
>                         :S # (:S # Var "x" # Var "y" # Var "z") # (:S # Var "x" # Var "y" # Var "z")
> test4 = Refl

> test5 : combAtPath ParReduction.path2 = PrimComb BaseKS.S 3
> test5 = Refl

> test6 : combAtPath ParReduction.path3 = PrimComb BaseKS.S 3
> test6 = Refl

simStep {t=ParReduction.excomb} {tr=ParReduction.rescomb} [redex1, redex2,redex3]
