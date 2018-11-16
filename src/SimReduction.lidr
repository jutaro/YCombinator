= Simultaneously Reduction : Simultaneously reduction

> module SimReduction

> import Decidable.Equality
> import Relation
> import Combinator
> import CombinatorCompProp
> import Reduction
> import BaseKS
> import Path
> import Data.List.Quantifiers

> %access public export
> %default total

=== Redex

> {-}
> ||| A redex for simultaneus reduction
> ||| Variant1, which duplicates a term and adds a path
> data Redex : {b: Type} -> (from: Comb b) -> Path from -> (to: Comb b) -> Type where
>   RPrim    : {l, r: Comb b} -> Reduce b => PrimRed {base=b} l r -> Redex l Here r
>   RAppL    : Reduce b => Redex {b} l path res -> Redex {b} (l # r) (LP path) (res # r)
>   RAppR    : Reduce b => Redex {b} r path res -> Redex {b} (l # r) (RP path) (l # res)

> ||| Variant2
> ||| A Redex is a primitive reduction and a path, on which it is applied.
> ||| It contains the proofs, that
> ||| * A primitive combinator is at the path
> ||| * The left spine before this prim is at least as long as the arity
> ||| * The combinator at the path fits the PrimComb given
> data Redex : Comb b -> Type where
>    RPath :  Reduce b =>
>               {t, t1,t2: Comb b} ->
>               {n: Nat} ->
>               PrimRed t1 t2 ->
>               (p : Path t) ->
>               {auto prf: combAtPath p = PrimComb _ n} ->
>               {auto prf1: LTE n (arity p)} ->
>               {auto prf2: combAtPath (shortenN (arity p) p) = t1} ->
>               Redex t


> ||| Change type of (redex) path p from in to out type of a redex
> pathToType : {b: Type} -> (u : Comb b) -> {w : Comb b} -> Redex u p w -> Path w
> pathToType _ (RPrim p) = Here
> pathToType {b} (App l r) (RAppL rl)  = LP (pathToType {b} l rl)
> pathToType {b} (App l r) (RAppR rr)  = RP (pathToType {b} r rr)

> ||| Redexes can be combined
> simRedex   : {b: Type} -> {u,v,w: Comb b} -> {p1, p2: Path u} ->
>                 Redex {b} u p1 v -> Redex {b} u p2 w -> p1 < p2 = True -> Redex v p' b'
> simRedex {b} {u} redex1 redex2 lt =
>   let p' = pathToType {b} u redex1
>   in ?hole




--
-- > implementation Eq (Redex t) where
-- >   (RPath pr1 p1) == (RPath pr2 p2) = asUntypedPath p1 == asUntypedPath p2
--
-- > ||| This instance makes it possible to sort redexes in pre-order traversal ordering
-- > implementation Ord (Redex t) where
-- >   compare (RPath pr1 p1) (RPath pr2 p2) = compare (asUntypedPath p1) (asUntypedPath p2)
--
-- > applyRedex : Reduce b  => (t: Comb b) -> (v: Comb b) -> Redex t -> Step t v
-- > applyRedex c v (RPath prim path {prf2}) =
-- >   let applyPath = shortenN (arity path) path
-- >   in applyRedex' prim c v applyPath
-- >     where
-- >       applyRedex : Reduce b  => PrimRed {base=b} t1 t2 -> (t' : Comb b) -> (v': Comb b) -> Path t' -> Step t' v'
-- >       applyRedex' p (App l r) (App l' r) (LP np)  = AppL (applyRedex' p l l' np)
-- >       applyRedex' p (App l r) (App l r') (RP np)  = AppR (applyRedex' p r r' np)
-- >       applyRedex' p from to SimReduction.Here     =
-- >         let temp = replace (sym prf2) p
-- >         in  Prim ?hole
--

-- > transformType : Reduce b => {t : Comb b} -> Redex t -> Comb b -> Comb b
-- > transformType (RPath pr (LP np)) t =
-- >   case t of
-- >     App l r => ?hole0 -- App (transformType (RPath pr np) l) r
-- > transformType (RPath pr (RP np)) t =
-- >   case t of
-- >     App l r => ?hole1 -- App l (transformType (RPath pr np) r)
-- > transformType (RPath (Prim p (S(Z))) Here) (App prc r) =
-- >   case p {x=r} of
-- >     Step l r => r
-- > transformType (RPath (PrimComb p 2) Here) (App (App prc r) r1) = p {x=r} {y=r1}
-- > transformType (RPath (PrimComb p 3) Here) (App (App (App prc r) r1) r2) = p {x=r} {y=r1} {z=r2}


simStep {t=SimReduction.excomb} {tr=SimReduction.rescomb} [redex1, redex2,redex3]

applyRedex


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

-- > redex1 : Redex SimReduction.excomb
-- > redex1 = RPath StepS path1
--
-- > redex2 : Redex SimReduction.excomb
-- > redex2 = RPath StepS path2
--
-- > redex3 : Redex SimReduction.excomb
-- > redex3 = RPath StepS path3
