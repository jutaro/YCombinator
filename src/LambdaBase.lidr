LambdaBase.lidr -- Simple untyped lambda calculus, which can be compiled to combinators

> module LambdaBase

> import Id
> import Data.List
> import BaseKS
> import Combinator
> import CombinatorCompProp

> %access public export
> %default total

Simple untyped lambda calculus without free variables

> data LBTm : List Id -> Type where
>   TApp    : LBTm ids -> LBTm ids -> LBTm ids
>   TVar    : (id : Id) -> {auto p : Elem id ids} -> LBTm ids
>   TAbs    : (id : Id) -> LBTm (id :: ids) -> LBTm ids

> infixr 7 &
> (&) : LBTm ids -> LBTm ids -> LBTm ids
> (&) = TApp

> syntax "(" "\\" [p] "." [r] ")" = TAbs p r

> xi : Id
> xi = MkId "x"

> yi : Id
> yi = MkId "y"

> zi : Id
> zi = MkId "z"

> termI : LBTm xs
> termI = (\ xi . TVar xi)

> termK : LBTm xs
> termK = (\ xi . (\ yi . TVar xi))

> termS : LBTm xs
> termS = (\ xi . (\ yi . (\ zi . (TVar xi & TVar zi) & (TVar yi & TVar zi))))

> occursInL : (id : Id) -> LBTm ids -> {auto p : Elem id ids} -> Bool
> occursInL id (TVar id2) = id == id2
> occursInL id (TAbs id2 t) = if id == id2 then False else occursInL id t
> occursInL id (TApp l r) = occursInL id l || occursInL id r

> bracketAbstract' : Id -> Comb KS -> Comb KS
> bracketAbstract' id (Var id2) = :S # :K # :K
> bracketAbstract' id p@(PrimComb _ _) = p
> bracketAbstract' id t@(App l r) =
>   if not (occursInC id t)
>     then :K # t
>     else :S # bracketAbstract' id l # bracketAbstract' id r

> bracketAbstract : LBTm vars -> Comb KS
> bracketAbstract (TAbs id (TVar id2)) =
>   if id == id2
>     then :S # :K # :K
>     else Var id2
> bracketAbstract (TAbs id t@(TApp l r)) =
>   if not (occursInL id t)
>     then :K # (bracketAbstract t)
>     else :S # bracketAbstract (assert_smaller (TAbs id t) (TAbs id l)) #
>               bracketAbstract (assert_smaller (TAbs id t) (TAbs id r))
> bracketAbstract (TAbs id t@(TAbs id2 rt)) =
>   if not (occursInL id t)
>     then :K # (bracketAbstract t)
>     else bracketAbstract' id (bracketAbstract (assert_smaller (TAbs id t) t))
> bracketAbstract (TApp l r) = bracketAbstract (assert_smaller (TApp l r) l) #
>                              bracketAbstract (assert_smaller (TApp l r) r)
> bracketAbstract (TVar id) = Var id


    bracketAbstract (LAbst v _ty :@: (LAbst v2 ty2 :@: r)) =
        bracketAbstract' v  (bracketAbstract (LAbst v2 ty2 :@: r))
    bracketAbstract (LVar v) = Var v
    -- identity case
    bracketAbstract (LAbst v _ :@: LVar r) | v == r = Const i
    -- eta shortcut
    bracketAbstract ((LAbst v _ty :@: l) :@: _r) | not (occurs v l) = bracketAbstract l
    -- constant case
    bracketAbstract (LAbst v _ :@: r) | not (occurs v r) = Const k :@ bracketAbstract r
    -- application case
    bracketAbstract (LAbst v ty :@: (l :@: r))   = Const s :@  bracketAbstract (LAbst v ty :@: l)
                                                    :@ bracketAbstract (LAbst v ty :@: r)
    bracketAbstract (l :@: r) = bracketAbstract l :@ bracketAbstract r
    bracketAbstract (LAbst v _) = error $ "CombLambda>>bracketAbstract: Lonely Abstraction " ++ show v

    -- identity case
    bracketAbstract' v (Var n) | v == n     = Const i
    -- constant case
                               | otherwise = Const k :@ Var n
    bracketAbstract' _v (Const c)          = Const k :@ Const c
    bracketAbstract' v r | not (occurs v r) = Const k :@ r
    -- application case
    bracketAbstract' v (l :@ r)            = Const s :@ bracketAbstract' v l :@ bracketAbstract' v r



> -- bracketAbstractKSIBC :
