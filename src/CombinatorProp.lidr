= CombinatorProp : Properties of Combinators

> module CombinatorProp

> import Combinator
> import Reduction
> import Relation
> import BaseBWCK

> %access public export
> %default total

Program:
Define arity and Classification of combinators:

  - Identity

  - Associator

  - Cancellator

  - Permutator

  - Duplicator

  - RegularCombinator

  - ProperCombinator

The arity is the minimum number of args on which a reduction happens

> ||| Spine of a combinator as list
> spine : Reduce b => Comb b -> List (Comb b)
> spine (App l r) = r :: spine l
> spine other = [other]

> ||| Generator of var names (step1)
> primVarNames : List String
> primVarNames = ["x", "y", "z", "u", "v", "w"]

> ||| Generator of var names (step2)
> varNames : List String
> varNames = primVarNames ++ concat (map (\i => map (\n => show i ++ n) primVarNames) [1..6])

> ||| Generator of Vars
> varCombs : Reduce base => List (Comb base)
> varCombs = map Var varNames

> ||| Returns arity of combinator
> arity : Reduce base => Comb base -> Maybe Nat
> arity comb = case step comb of
>                 Just _ => Just 0
>                 Nothing => arity' 1 comb varCombs
>   where arity' : Reduce base => Nat -> Comb base -> List (Comb base) -> Maybe Nat
>         arity' n acc (hd :: tail) =
>           let combi = acc # hd
>           in  case step combi of
>                 Just _ => Just n
>                 Nothing => arity' (S n) combi tail
>         arity' n acc [] = Nothing

Identity Combinators have the property Z x1 .. xn -> x1 .. xn


> {-}
> isIdentity : Comb base -> Type
> isIdentity c = ?holei -- Multi Step c
> -}
