LambdaBase.lidr -- Simple untyped lambda calculus, which can be compiled to combinators

> module LambdaBase

> import Id
  > import Data.List
> import BaseKS
> import Combinator

> %access public export
> %default total

Simple untyped lambda calculus without free variables

> data LBTm : List Id -> Type where
>   TApp    : LBTm ids -> LBTm ids -> LBTm ids
>   TVar    : (id : Id) -> {auto p : Elem id ids} -> LBTm ids
>   TAbs    : (id : Id) -> LBTm (id :: ids) -> LBTm ids

> infixr 7 ##
> (##) : LBTm ids -> LBTm ids -> LBTm ids
> (##) = TApp

> syntax "(" "\\" [p] "." [r] ")" = TAbs p r

> x : Id
> x = MkId "x"

> y : Id
> y = MkId "y"

> z : Id
> z = MkId "z"

> termI : LBTm xs
> termI = (\ x . TVar x)

> termK : LBTm xs
> termK = (\ x . (\ y . TVar x))

> termS : LBTm xs
> termS = (\ x . (\ y . (\ z . (TVar x ## TVar z) ## (TVar y ## TVar z))))

> occursIn : (id : Id) -> LBTm ids -> {auto p : Elem id ids} -> Bool
> occursIn id (TVar id2) = id == id2
> occursIn id (TAbs id2 t) = if id == id2 then False else occursIn id t
> occursIn id (TApp l r) = occursIn id l || occursIn id r

class Basis b => BracketAbstract b where
    bracketAbstract :: LTerm VarString t -> CTerm b
    -- ^ Implement / Call this to convert a combinatory term to a lambda term
    bracketAbstract' :: VarString -> CTerm b -> CTerm b
    -- ^ Implement this as a helper for nested abstrations

instance BracketAbstract KS where
    -- nested abstractions are passed to the helper function
    bracketAbstract (LAbst v _ty :@: (LAbst v2 ty2 :@: r)) =
        bracketAbstract' v  (bracketAbstract (LAbst v2 ty2 :@: r))
    bracketAbstract (LVar v) = Var v
    -- identity case
    bracketAbstract (LAbst v _ :@: LVar r) | v == r = Const s :@ Const k :@ Const k
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
    bracketAbstract' v (Var n) | v == n     = Const s :@ Const k :@ Const k
    -- constant case
                               | otherwise = Const k :@ Var n
    bracketAbstract' _v (Const c)          = Const k :@ Const c
    bracketAbstract' v r | not (occurs v r) = Const k :@ r
    -- application case
    bracketAbstract' v (l :@ r)            = Const s :@ bracketAbstract' v l :@ bracketAbstract' v r



> mutual
>   bracketAbstractKS : (id: Id) -> LBTm [id] -> Comb KS
>     -- id1 needs to be equal to id2 for the term to be well formed
>   bracketAbstractKS _ t@(TVar _) = :S # :K # :K
>   bracketAbstractKS id t@(TAbs id2 t) =
>     if id == id2
>       then bracketAbstractKS id2 t
>       else bracketAbstractKS id (bracketAbstractKS id2 t)

-- >   bracketAbstractKS id t@(TApp l r) =
-- >     if occursIn id t
-- >       then bracketAbstractKS id l # bracketAbstractKS id r
-- >       else :K # compileToCombKS t

>   compileToCombKS : LBTm [] -> Comb KS
>   compileToCombKS (TAbs id term) = bracketAbstractKS id term
>   compileToCombKS (TApp lterm rterm) = compileToCombKS lterm # compileToCombKS rterm
>   compileToCombKS (TVar _) = ?hole

[x](abf).x = I
[x](abf).t = Kt if x /∈ FV(t)
[x](abf).st = S([x](abf).s)([x](abf).t)




-- > bracketAbstractKS (TApp l r) = bracketAbstractKS l # bracketAbstractKS r



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
