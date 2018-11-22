LambdaBase.lidr -- Simple untyped lambda calculus, which can be compiled to combinators

> module LambdaBase

> import Lib.Id
> import Data.List
> import Bases.BaseKS
> import Bases.BaseKSIBC
> import Bases.BaseKSBC
> import Combinator
> import CombinatorCompProp
> import SimReductionComp
> import Reduction
> import RankComb

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
>         :S # bracketAbstractKS (assert_smaller (TAbs id t) (TAbs id tl)) #
>              bracketAbstractKS (assert_smaller (TAbs id t) (TAbs id tr))
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
>       (TVar _) => :I -- since id occurs here it must be identity
>       (TApp tl (TVar id2)) =>
>         if id == id2
>           then if not (occursInL id tl)
>       --Eta
>                   then assert_total (bracketAbstractKSIBC (assert_smaller (TAbs id t) tl))
>                   else :S # bracketAbstractKSIBC (assert_smaller (TAbs id t) (TAbs id tl)) # :I
>           else :S # bracketAbstractKSIBC (assert_smaller (TAbs id t) (TAbs id tl)) # (:K # Var id2)
>       (TApp tl tr) =>
>       -- S
>         if not (occursInL id tl)
>           then :B # bracketAbstractKSIBC (assert_smaller (TAbs id t) tl)
>                   # bracketAbstractKSIBC (assert_smaller (TAbs id t) (TAbs id tr))
>           else if not (occursInL id tr)
>             then :C # bracketAbstractKSIBC  (assert_smaller (TAbs id t) (TAbs id tl)) #
>                       bracketAbstractKSIBC (assert_smaller (TAbs id t) tr)
>             else :S # bracketAbstractKSIBC (assert_smaller (TAbs id t) (TAbs id tl)) #
>                       bracketAbstractKSIBC (assert_smaller (TAbs id t) (TAbs id tr))
>       -- Nested Abstracts
>       (TAbs id2 rt) =>  bracketAbstractKSIBC' id (bracketAbstractKSIBC (assert_smaller (TAbs id t) t))
> bracketAbstractKSIBC (TApp l r) = bracketAbstractKSIBC (assert_smaller (TApp l r) l) #
>                                   bracketAbstractKSIBC (assert_smaller (TApp l r) r)
> bracketAbstractKSIBC (TVar id) = Var id



> bracketAbstractKSBC' : Id -> Comb KSBC -> Comb KSBC
> bracketAbstractKSBC' id v@(Var id2) =
>   if id == id2
>     then :S # :K # :K
>     else :K # v
> bracketAbstractKSBC' id p@(PrimComb _ _) = :K # p
> bracketAbstractKSBC' id t@(App l r) =
>   if r == Var id && not (occursInC id l)
>     then l
>     else if not (occursInC id t)
>       then :K # t
>       else if not (occursInC id l)
>         then :B # l # bracketAbstractKSBC' id r
>         else if not (occursInC id r)
>           then :C # bracketAbstractKSBC' id l # r
>           else :S # bracketAbstractKSBC' id l # bracketAbstractKSBC' id r

> bracketAbstractKSBC : LBTm vars -> Comb KSBC
> bracketAbstractKSBC (TAbs id t) =
>   if not (occursInL id t)
>       -- K
>     then :K # (bracketAbstractKSBC (assert_smaller (TAbs id t) t))
>     else case t of
>       -- I
>       (TVar _) => :S # :K # :K -- since id occurs here it must be identity
>       (TApp tl (TVar id2)) =>
>         if id == id2
>           then if not (occursInL id tl)
>       --Eta
>                   then assert_total (bracketAbstractKSBC (assert_smaller (TAbs id t) tl))
>                   else :S # bracketAbstractKSBC (assert_smaller (TAbs id t) (TAbs id tl)) # (:S # :K # :K)
>           else :S # bracketAbstractKSBC (assert_smaller (TAbs id t) (TAbs id tl)) # (:K # Var id2)
>       (TApp tl tr) =>
>       -- S
>         if not (occursInL id tl)
>           then :B # bracketAbstractKSBC (assert_smaller (TAbs id t) tl)
>                   # bracketAbstractKSBC (assert_smaller (TAbs id t) (TAbs id tr))
>           else if not (occursInL id tr)
>             then :C # bracketAbstractKSBC  (assert_smaller (TAbs id t) (TAbs id tl)) #
>                       bracketAbstractKSBC (assert_smaller (TAbs id t) tr)
>             else :S # bracketAbstractKSBC (assert_smaller (TAbs id t) (TAbs id tl)) #
>                       bracketAbstractKSBC (assert_smaller (TAbs id t) (TAbs id tr))
>       -- Nested Abstracts
>       (TAbs id2 rt) =>  bracketAbstractKSBC' id (bracketAbstractKSBC (assert_smaller (TAbs id t) t))
> bracketAbstractKSBC (TApp l r) = bracketAbstractKSBC (assert_smaller (TApp l r) l) #
>                                   bracketAbstractKSBC (assert_smaller (TApp l r) r)
> bracketAbstractKSBC (TVar id) = Var id

-- Tests

> exB : LBTm []
> exB =  (\ xi . (\ yi . (\ zi . TVar xi & (TVar yi & TVar zi))))

> exC : LBTm []
> exC =  (\ xi . (\ yi . (\ zi . TVar xi & TVar zi & TVar yi)))

> exW : LBTm []
> exW =  (\ xi . (\ yi . TVar xi & TVar yi & TVar yi))

> exPred : LBTm []
> exPred = (\ ni . (\ fi . (\ xi . TVar ni & (\ gi . (\ hi . TVar gi & TVar fi)) & (\ ui . TVar xi) & (\ ui . TVar ui))))

> exY : LBTm []
> exY = (\ xi . (\yi . TVar xi & TVar yi & TVar xi)) & (\yi . (\xi . TVar yi & (TVar xi & TVar yi & TVar xi)))

> bt2 : Reduce a => Comb a -> Comb a
> bt2 c = c # Var xi # Var yi

> bt3 : Reduce a => Comb a -> Comb a
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
> r1_w = bracketAbstractKS exW

> t1_w : LambdaBase.r1_w = :S # :S # (:K # (:S # :K # :K))
> t1_w = Refl

> tc1_w : sr (LambdaBase.bt2 LambdaBase.r1_w) = Just (Var LambdaBase.xi # Var LambdaBase.yi # Var LambdaBase.yi)
> tc1_w = Refl

> r1_pred : Comb KS
> r1_pred = bracketAbstractKS exPred

> t1_pred : LambdaBase.r1_pred = :S # (:S # (:K # :S) # (:S # (:K # (:S # (:K # :S))) # (:S # (:S # (:K # :S) # (:S # (:K # (:S # (:K # :S)))
>                             # (:S # (:K # (:S # (:K # :K))) # (:S # (:S # (:K # :S) # :K) # (:K # (:S # (:K # (:S # (:K # :K))) # (:S # (:K #
>                                (:S # (:S # :K # :K))) # :K))))))) # (:K # (:K # :K))))) # (:K # (:K # (:K # (:S # :K # :K))))
> t1_pred = Refl

> r2_b : Comb KSIBC
> r2_b = bracketAbstractKSIBC exB

> t2_b : LambdaBase.r2_b = :B
> t2_b = Refl

> tc2_b : sr (LambdaBase.bt3 LambdaBase.r2_b) = Just (Var LambdaBase.xi # (Var LambdaBase.yi # Var LambdaBase.zi))
> tc2_b = Refl

> r2_c : Comb KSIBC
> r2_c = bracketAbstractKSIBC LambdaBase.exC

> t2_c : LambdaBase.r2_c = :C # (:B # :B # :S) # :K
> t2_c = Refl

> tc2_c : sr (LambdaBase.bt3 LambdaBase.r2_c) = Just (Var LambdaBase.xi # Var LambdaBase.zi # Var LambdaBase.yi)
> tc2_c = Refl

> r2_w : Comb KSIBC
> r2_w = bracketAbstractKSIBC LambdaBase.exW

> t2_w : LambdaBase.r2_w = :C # :S # :I
> t2_w = Refl

> tc2_w : sr (LambdaBase.bt2 LambdaBase.r2_w) = Just (Var LambdaBase.xi # Var LambdaBase.yi # Var LambdaBase.yi)
> tc2_w = Refl

> r2_pred : Comb KSIBC
> r2_pred = bracketAbstractKSIBC LambdaBase.exPred

> t2_pred : LambdaBase.r2_pred = :C # (:B # :C # (:B # (:B # :C) # (:C # (:B # :C # (:B # (:B # :B) #
>             (:C # :B # (:B # (:B # :K) # (:C # :I))))) # :K))) # :I
> t2_pred = Refl


> r3_b : Comb KSBC
> r3_b = bracketAbstractKSBC exB

> t3_b : LambdaBase.r3_b = :B
> t3_b = Refl

> tc3_b : sr (LambdaBase.bt3 LambdaBase.r3_b) = Just (Var LambdaBase.xi # (Var LambdaBase.yi # Var LambdaBase.zi))
> tc3_b = Refl

> r3_c : Comb KSBC
> r3_c = bracketAbstractKSBC LambdaBase.exC

> t3_c : LambdaBase.r3_c = :C # (:B # :B # :S) # :K
> t3_c = Refl

> tc3_c : sr (LambdaBase.bt3 LambdaBase.r3_c) = Just (Var LambdaBase.xi # Var LambdaBase.zi # Var LambdaBase.yi)
> tc3_c = Refl

> r3_w : Comb KSBC
> r3_w = bracketAbstractKSBC LambdaBase.exW

> t3_w : LambdaBase.r3_w = :C # :S # (:S # :K # :K)
> t3_w = Refl

> tc3_w : sr (LambdaBase.bt2 LambdaBase.r3_w) = Just (Var LambdaBase.xi # Var LambdaBase.yi # Var LambdaBase.yi)
> tc3_w = Refl

> r3_pred : Comb KSBC
> r3_pred = bracketAbstractKSBC LambdaBase.exPred

> -- size 24
> t3_pred : LambdaBase.r3_pred = :C # (:B # :C # (:B # (:B # :C) # (:C # (:B # :C # (:B # (:B # :B) # (:C # :B # (:B # (:B # :K) # (:C # (:S # :K # :K)))))) # :K))) # (:S # :K # :K)

> t3_pred = Refl
