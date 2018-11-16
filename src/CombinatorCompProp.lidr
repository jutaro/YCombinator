= CombinatorCompProp : Computational Properties of Combinators

> module CombinatorCompProp

> import Combinator
> import Reduction
> import Relation
> import BaseBWCK
> import Id
> import Data.List

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
> spine : Reduce b => Comb b {ids} -> List (Comb b {ids})
> spine (App l r) = r :: spine l
> spine other = [other]

> ||| Generator of var names (step1)
> primVarNames : List String
> primVarNames = ["x", "y", "z", "u", "v", "w"]

> ||| Generator of var names (step2)
> varIds : List Id
> varIds = map MkId $ primVarNames ++ concat (map (\i => map (\n => show i ++ n) primVarNames) [1..2])

> ||| Generator of Vars
> varCombs : {ids: List Id} -> Reduce base => List (Comb base {ids})
> varCombs {ids=varIds} = map (\ n => Var n {p=?varCombs_prf}) varIds

> x : Reduce base => Comb base {ids=CombinatorCompProp.varIds}
> x = head varCombs

> y : Reduce base => Comb base {ids=CombinatorCompProp.varIds}
> y = head (tail varCombs)

> z : Reduce base => Comb base {ids=CombinatorCompProp.varIds}
> z = head (tail (tail varCombs))

> ||| Returns arity of combinator
> arity : Reduce base => Comb base -> Maybe Nat
> arity comb = case step comb of
>                 Just _ => Just 0
>                 Nothing => arity' 1 comb varCombs
>   where arity' : Reduce base => Nat -> Comb base {ids} -> List (Comb base {ids}) -> Maybe Nat
>         arity' n acc (hd :: tail) =
>           let combi = acc # hd
>           in  case step combi of
>                 Just _ => Just n
>                 Nothing => arity' (S n) combi tail
>         arity' n acc [] = Nothing

> asApplications :  Reduce base => (l : List (Comb base {ids})) -> {auto ok: NonEmpty l} -> Comb base {ids}
> asApplications (hd :: tl) = foldl (\accu, ele => accu # ele) hd tl

> prepare : Reduce base => Comb base {ids} -> Maybe (List (Comb base {ids}), Comb base {ids})
> prepare c = do
>   i <- arity c
>   if i == 0
>     then Nothing
>     else let args = take i varCombs
>              app  = asApplications (c :: args)
>          in do
>             res <- weakHeadReductionCut 100 app
>             pure (args,res)

> ||| Identity Combinators have the property Z x1 .. xn -> x1 .. xn
> isIdentity : Eq (Comb base {ids}) => Reduce base => Comb base {ids} -> Maybe Bool
> isIdentity comb = do
>   (args,res) <- prepare comb
>   case args of
>     (hd :: tail) => pure (res == asApplications (hd :: tail))
>     [] => Nothing

> leftAssociated : Reduce base => Comb base -> Bool
> leftAssociated (App l r) =
>   case r of
>     App _ _ => False
>     _ => leftAssociated l
> leftAssociated _ = True

> ||| Associators have the property Z x1 .. xn -> M, M not purely left associated
> isAssociator : Eq (Comb base {ids}) => Reduce base => Comb base {ids} -> Maybe Bool
> isAssociator comb = do
>   (args,res) <- prepare comb
>   case args of
>     (hd :: tail) => pure $ not (leftAssociated res)
>     [] => Nothing

> contains: Eq (Comb base {ids}) => Comb base {ids} -> Comb base {ids} -> Bool
> contains this that =
>   if this == that
>     then True
>     else case this of
>       App l r => contains l that || contains r that
>       _ => False

> containsAll: Eq (Comb base {ids}) => Comb base {ids} -> List (Comb base {ids}) -> Bool
> containsAll this allThat =
>   case find (\e => not (contains this e)) allThat of
>     Nothing => True
>     Just _ => False

> ||| Cancellators have the property Z x1 .. xn -> M, with at least one of x1 .. xn having no occurence in M
> isCancellator : Eq (Comb base {ids}) => Reduce base => Comb base {ids} -> Maybe Bool
> isCancellator comb = do
>   (args,res) <- prepare comb
>   case args of
>     (hd :: tail) => pure $ not (containsAll res args)
>     [] => Nothing

> flattenComb : Comb base {ids} -> List (Comb base {ids})
> flattenComb (App l r) = flattenComb l ++ flattenComb r
> flattenComb other = [other]

> ||| Is thisVar preceded by any of laterVars in flattened
> preceding : Eq a => a -> List a -> List a -> Maybe Bool
> preceding thisVar laterVars flattened = do
>   i <- elemIndex thisVar flattened
>   let preFlattened = take i flattened
>   pure (and (map (\i => elem i preFlattened) laterVars))

> ||| Is any var in the list preceded by any later var of the same list in flattened
> precedingAny : Eq a => List a -> List a -> Bool
> precedingAny (hd::tl) flattened =
>   case foldl foldFunc (Just tl) (hd::tl) of
>     Nothing => False
>     Just _  => True
>   where foldFunc Nothing ele = Nothing
>         foldFunc (Just []) ele = Just []
>         foldFunc (Just (hd::tl)) ele =
>           case preceding ele (hd::tl) flattened of
>                 Just True => Nothing
>                 _         => Just tl
> precedingAny [] flattened = False

> ||| Permutators have the property Z x1 .. xn -> M, with M containing an xj preceding an xi (1 <= i < j <= n)
> isPermutator : Eq (Comb base {ids}) => Reduce base => Comb base {ids} -> Maybe Bool
> isPermutator comb = do
>   (args,res) <- prepare comb
>   case args of
>     (hd :: tail) => pure $ not (precedingAny args (flattenComb res))
>     [] => Nothing

> moreThenOne : Eq a => a -> List a -> Bool
> moreThenOne e l = length (elemIndices e l) > 1

> moreThenOneAny : Eq a => List a -> List a -> Bool
> moreThenOneAny search l = or (map (\e => moreThenOne e l) search)

> ||| Duplicators have the property Z x1 .. xn -> M, with M containing more than one occurance of an xi (1 <= i <= n)
> isDuplicator : Eq (Comb base {ids}) => Reduce base => Comb base {ids} -> Maybe Bool
> isDuplicator comb = do
>   (args,res) <- prepare comb
>   case args of
>     (hd :: tail) => pure $ (moreThenOneAny args (flattenComb res))
>     [] => Nothing

> ||| Regular combinators have the property Z x1 .. xn -> x1 M
> isRegular : Eq (Comb base {ids}) => Reduce base => Comb base {ids} -> Maybe Bool
> isRegular comb = do
>   (args,res) <- prepare comb
>   case args of
>     (hd :: tail) => case flattenComb res of
>                       (hd'::_) => pure $ hd == hd'
>                       _ => Nothing
>     [] => Nothing

> ||| Proper combinators have the property Z x1 .. xn -> x1 M and M contains no ther variables then x1, .. , xn
> isProper : Eq (Comb base) => Reduce base => Comb base -> Maybe Bool
> isProper comb = ?isProper_rhs
