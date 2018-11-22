= CombinatorCompProp : Computational Properties of Combinators

> module CombinatorCompProp

> import Combinator
> import Reduction
> import Lib.Relation
> import Bases.BaseBWCK
> import Lib.Id
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
> spine : Reduce b => Comb b -> List (Comb b)
> spine (App l r) = r :: spine l
> spine other = [other]

> occursInC : (id : Id) -> Comb b -> Bool
> occursInC id (PrimComb _ _) = False
> occursInC id (App l r) = occursInC id l || occursInC id r
> occursInC id (Var id2) = id == id2

> ||| Generator of var names (step1)
> primVarNames : List String
> primVarNames = ["x", "y", "z", "u", "v", "w"]

> ||| Generator of var names (step2)
> varIds : List Id
> varIds = map MkId $ primVarNames ++ concat (map (\i => map (\n => show i ++ n) primVarNames) [1..2])

> ||| Generator of Vars
> varCombs : Reduce base => List (Comb base)
> varCombs = map Var varIds

> xv : Reduce base => Comb base
> xv = head varCombs

> yv : Reduce base => Comb base
> yv = head (tail varCombs)

> zv : Reduce base => Comb base
> zv = head (tail (tail varCombs))

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

> asApplications :  Reduce base => (l : List (Comb base)) -> {auto ok: NonEmpty l} -> Comb base
> asApplications (hd :: tl) = foldl (\accu, ele => accu # ele) hd tl

> prepare : Reduce base => Comb base -> Maybe (List (Comb base), Comb base)
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
> isIdentity : Eq (Comb base) => Reduce base => Comb base -> Maybe Bool
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
> isAssociator : Eq (Comb base) => Reduce base => Comb base -> Maybe Bool
> isAssociator comb = do
>   (args,res) <- prepare comb
>   case args of
>     (hd :: tail) => pure $ not (leftAssociated res)
>     [] => Nothing

> contains: Eq (Comb base) => Comb base -> Comb base -> Bool
> contains this that =
>   if this == that
>     then True
>     else case this of
>       App l r => contains l that || contains r that
>       _ => False

> containsAll: Eq (Comb base) => Comb base -> List (Comb base) -> Bool
> containsAll this allThat =
>   case find (\e => not (contains this e)) allThat of
>     Nothing => True
>     Just _ => False

> ||| Cancellators have the property Z x1 .. xn -> M, with at least one of x1 .. xn having no occurence in M
> isCancellator : Eq (Comb base) => Reduce base => Comb base -> Maybe Bool
> isCancellator comb = do
>   (args,res) <- prepare comb
>   case args of
>     (hd :: tail) => pure $ not (containsAll res args)
>     [] => Nothing

> flattenComb : Comb base -> List (Comb base)
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
> isPermutator : Eq (Comb base) => Reduce base => Comb base -> Maybe Bool
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
> isDuplicator : Eq (Comb base) => Reduce base => Comb base -> Maybe Bool
> isDuplicator comb = do
>   (args,res) <- prepare comb
>   case args of
>     (hd :: tail) => pure $ (moreThenOneAny args (flattenComb res))
>     [] => Nothing

> ||| Regular combinators have the property Z x1 .. xn -> x1 M
> isRegular : Eq (Comb base) => Reduce base => Comb base -> Maybe Bool
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
