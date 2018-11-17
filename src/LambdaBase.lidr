LambdaBase.lidr -- Simple untyped lambda calculus, which can be compiled to combinators

> module LambdaBase

> import Id
> import Data.List
> import BaseKS
> import BaseKSIBC
> import Combinator
> import CombinatorCompProp
> import SimReductionComp
> import Reduction
> import GenComb

> %access public export
> %default total

Simple untyped lambda calculus without free variables

> data LBTm : List Id -> Type where
>   TApp    : LBTm ids -> LBTm ids -> LBTm ids
>   TVar    : (id : Id) -> {auto p : Elem id ids} -> LBTm ids
>   TAbs    : (id : Id) -> LBTm (id :: ids) -> LBTm ids

> infixl 9 &
> (&) : LBTm ids -> LBTm ids -> LBTm ids
> (&) = TApp

> syntax "(" "\\" [p] "." [r] ")" = TAbs p r

> xi : Id
> xi = MkId "x"

> yi : Id
> yi = MkId "y"

> zi : Id
> zi = MkId "z"

> ui : Id
> ui = MkId "u"

> ni : Id
> ni = MkId "n"

> fi : Id
> fi = MkId "f"

> gi : Id
> gi = MkId "g"

> hi : Id
> hi = MkId "h"


> termI : LBTm xs
> termI = (\ xi . TVar xi)

> termK : LBTm xs
> termK = (\ xi . (\ yi . TVar xi))

> termS : LBTm xs
> termS = (\ xi . (\ yi . (\ zi . TVar xi & TVar zi & (TVar yi & TVar zi))))

> occursInL : (id : Id) -> LBTm ids -> {auto p : Elem id ids} -> Bool
> occursInL id (TVar id2) = id == id2
> occursInL id (TAbs id2 t) = if id == id2 then False else occursInL id t
> occursInL id (TApp l r) = occursInL id l || occursInL id r

> bracketAbstractKS' : Id -> Comb KS -> Comb KS
> bracketAbstractKS' id v@(Var id2) =
>   if id == id2
>     then :S # :K # :K
>     else :K # v
> bracketAbstractKS' id p@(PrimComb _ _) = :K # p
> bracketAbstractKS' id t@(App l r) =
>   if r == Var id && not (occursInC id l)
>     then l
>     else if not (occursInC id t)
>       then :K # t
>       else :S # bracketAbstractKS' id l # bracketAbstractKS' id r

> bracketAbstractKS : LBTm vars -> Comb KS
> bracketAbstractKS (TAbs id t) =
>   if not (occursInL id t)
>       -- K
>     then :K # (bracketAbstractKS (assert_smaller (TAbs id t) t))
>     else case t of
>       -- I
>       (TVar _) => :S # :K # :K
>       (TApp tl (TVar id2)) =>
>         if id == id2
>           then if not (occursInL id tl)
>       --Eta
>                   then assert_total (bracketAbstractKS tl)
>                   else :S # bracketAbstractKS (assert_smaller (TAbs id t) (TAbs id tl)) # (:S # :K # :K)
>           else :S # bracketAbstractKS (assert_smaller (TAbs id t) (TAbs id tl)) # (:K # Var id2)
>       (TApp tl tr) =>
>       -- S
>           :S # bracketAbstractKS (assert_smaller (TAbs id t) (TAbs id tl)) #
>                bracketAbstractKS (assert_smaller (TAbs id t) (TAbs id tr))
>       -- Nested Abstracts
>       (TAbs id2 rt) =>  bracketAbstractKS' id (bracketAbstractKS (assert_smaller (TAbs id t) t))
> bracketAbstractKS (TApp l r) = bracketAbstractKS (assert_smaller (TApp l r) l) #
>                                bracketAbstractKS (assert_smaller (TApp l r) r)
> bracketAbstractKS (TVar id) = Var id

> bracketAbstractKSIBC' : Id -> Comb KSIBC -> Comb KSIBC
> bracketAbstractKSIBC' id v@(Var id2) =
>   if id == id2
>     then :I
>     else :K # v
> bracketAbstractKSIBC' id p@(PrimComb _ _) = :K # p
> bracketAbstractKSIBC' id t@(App l r) =
>   if r == Var id && not (occursInC id l)
>     then l
>     else if not (occursInC id t)
>       then :K # t
>       else if not (occursInC id l)
>         then :B # l # bracketAbstractKSIBC' id r
>         else if not (occursInC id r)
>           then :C # bracketAbstractKSIBC' id l # r
>           else :S # bracketAbstractKSIBC' id l # bracketAbstractKSIBC' id r

> bracketAbstractKSIBC : LBTm vars -> Comb KSIBC
> bracketAbstractKSIBC (TAbs id t) =
>   if not (occursInL id t)
>       -- K
>     then :K # (bracketAbstractKSIBC (assert_smaller (TAbs id t) t))
>     else case t of
>       -- I
>       (TVar _) => :I
>       (TApp tl (TVar id2)) =>
>         if id == id2
>           then if not (occursInL id tl)
>       --Eta
>                   then assert_total (bracketAbstractKSIBC (assert_smaller (TAbs id t) tl))
>                   else :C # bracketAbstractKSIBC (assert_smaller (TAbs id t) (TAbs id tl)) # :I
>           else :C # bracketAbstractKSIBC (assert_smaller (TAbs id t) (TAbs id tl)) # (:K # Var id2)
>       (TApp tl tr) =>
>       -- S
>         if not (occursInL id tl)
>           then :B # bracketAbstractKSIBC (assert_smaller (TAbs id t) tl)
>                   # bracketAbstractKSIBC (assert_smaller (TAbs id t) (TAbs id tr))
>           else if not (occursInL id tr)
>             then :C # bracketAbstractKSIBC  (assert_smaller (TAbs id t) (TAbs id tl)) #
>                       bracketAbstractKSIBC (assert_smaller (TAbs id t) tr)
>           else :S # bracketAbstractKSIBC (assert_smaller (TAbs id t) (TAbs id tl)) #
>                     bracketAbstractKSIBC (assert_smaller (TAbs id t) (TAbs id tr))
>       -- Nested Abstracts
>       (TAbs id2 rt) =>  bracketAbstractKSIBC' id (bracketAbstractKSIBC (assert_smaller (TAbs id t) t))
> bracketAbstractKSIBC (TApp l r) = bracketAbstractKSIBC (assert_smaller (TApp l r) l) #
>                                   bracketAbstractKSIBC (assert_smaller (TApp l r) r)
> bracketAbstractKSIBC (TVar id) = Var id

-- Tests

> exB : LBTm [LambdaBase.xi,LambdaBase.yi,LambdaBase.zi]
> exB =  (\ xi . (\ yi . (\ zi . TVar xi & (TVar yi & TVar zi))))

> exC : LBTm [LambdaBase.xi,LambdaBase.yi,LambdaBase.zi]
> exC =  (\ xi . (\ yi . (\ zi . TVar xi & TVar zi & TVar yi)))

> exW : LBTm [LambdaBase.xi,LambdaBase.yi,LambdaBase.zi]
> exW =  (\ xi . (\ yi . TVar xi & TVar yi & TVar yi))

> exPred : LBTm [LambdaBase.ni, LambdaBase.fi,LambdaBase.xi]
> exPred = (\ ni . (\ fi . (\ xi . TVar ni & (\ gi . (\ hi . TVar gi & TVar fi)) & (\ ui . TVar xi) & (\ ui . TVar ui))))


> bt2 : Comb KS -> Comb KS
> bt2 c = c # Var xi # Var yi

> bt3 : Comb KS -> Comb KS
> bt3 c = c # Var xi # Var yi # Var zi

> r1_b : Comb KS
> r1_b = bracketAbstractKS LambdaBase.exB

> t1_b : LambdaBase.r1_b = :S # (:K # :S) # :K
> t1_b = Refl

> tc1_b : sr (LambdaBase.bt3 LambdaBase.r1_b) = Just (Var LambdaBase.xi # (Var LambdaBase.yi # Var LambdaBase.zi))
> tc1_b = Refl

> r1_c : Comb KS
> r1_c = bracketAbstractKS LambdaBase.exC

> t1_c : LambdaBase.r1_c = :S # (:S # (:K # :S) # (:S # (:K # :K) # :S)) # (:K # :K)
> t1_c = Refl

> tc1_c : sr (LambdaBase.bt3 LambdaBase.r1_c) = Just (Var LambdaBase.xi # Var LambdaBase.zi # Var LambdaBase.yi)
> tc1_c = Refl

> r1_w : Comb KS
> r1_w = bracketAbstractKS LambdaBase.exW

> t1_w : LambdaBase.r1_w = :S # :S # (:K # (:S # :K # :K))
> t1_w = Refl

> tc1_w : sr (LambdaBase.bt2 LambdaBase.r1_w) = Just (Var LambdaBase.xi # Var LambdaBase.yi # Var LambdaBase.yi)
> tc1_w = Refl

> r1_pred : Comb KS
> r1_pred = bracketAbstractKS LambdaBase.exPred

> t1_pred : LambdaBase.r1_pred = :S # (:S # (:K # :S) # (:S # (:K # (:S # (:K # :S))) # (:S # (:S # (:K # :S) # (:S # (:K # (:S # (:K # :S)))
>                             # (:S # (:K # (:S # (:K # :K))) # (:S # (:S # (:K # :S) # :K) # (:K # (:S # (:K # (:S # (:K # :K))) # (:S # (:K #
>                                (:S # (:S # :K # :K))) # :K))))))) # (:K # (:K # :K))))) # (:K # (:K # (:K # (:S # :K # :K))))

> t1_pred = Refl
