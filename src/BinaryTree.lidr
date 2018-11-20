= BinaryTree : Representation and generation of binary trees

> module BinaryTree

> import Other
> import Functions
> import Decidable.Equality

> %access public export
> %default total

> data BinaryTree : a -> Type where
>   BNode: (Show a, Eq a)  => BinaryTree a -> BinaryTree a -> BinaryTree a
>   BLeaf : (Show a, Eq a) => a -> BinaryTree a

> Eq a => Eq (BinaryTree a) where
>   (BNode l r) == (BNode l2 r2) = l == l2 && r == r2
>   (BLeaf e) == (BLeaf e2)      = e == e2
>   _ == _                       = False

> nodeInjectiveLeft : (Eq a, Show a) => {l1,r1,l2,r1 : BinaryTree a} -> (BNode l1 r1 = BNode l2 r2) -> l1 = l2
> nodeInjectiveLeft Refl = Refl

> nodeInjectiveRight : (Eq a, Show a) => {l1,r1,l2,r1 : BinaryTree a} -> (BNode l1 r1 = BNode l2 r2) -> r1 = r2
> nodeInjectiveRight Refl = Refl

> leafInjective : (Eq a, Show a) => {l,r : a} -> (BLeaf l = BLeaf r) -> l = r
> leafInjective Refl = Refl

> implementation (Eq a, Show a) => Uninhabited ((the (BinaryTree a) (BLeaf _)) = BNode _ _) where
>   uninhabited Refl impossible

> implementation (Eq a, Show a) => Uninhabited ((the (BinaryTree a) (BNode _ _)) = BLeaf _) where
>   uninhabited Refl impossible

> DecEq a => DecEq (BinaryTree a) where
>   decEq (BLeaf e) (BLeaf f) with (decEq e f)
>     | (Yes prf)   = Yes $ cong prf
>     | (No contra) = No (\h => contra (leafInjective h))
>   decEq (BNode l1 r1) (BNode l2 r2) with (decEq l1 l2, decEq r1 r2)
>     | (Yes prfL,Yes prfR)   = Yes $ rewrite prfL in cong prfR
>     | (No contraL,_) = No (\h => contraL (nodeInjectiveLeft {r1} h))
>     | (_ ,No contraR) = No (\h => contraR (nodeInjectiveRight {r1} h))
>   decEq (BNode _ _) (BLeaf _) = No $ absurd
>   decEq (BLeaf _) (BNode _ _) = No $ absurd

> ||| Parenthesis are omiited left associated as in combinator terms
> Show a => Show (BinaryTree a) where
>   showPrec p (BNode l r) = showParens (p >= App) (showPrec Open l ++ "->" ++ showPrec App r)
>   showPrec _ (BLeaf e)   = show e

> ||| The number of nodes of the tree
> nodeSize : BinaryTree a -> Nat
> nodeSize (BLeaf _) = 0
> nodeSize (BNode l r) = 1 + nodeSize l + nodeSize r

> ||| The number of leafs of the tree
> leafSize : BinaryTree a -> Nat
> leafSize (BLeaf _) = 1
> leafSize (BNode l r) = leafSize l + leafSize r

> ||| The number of leafs is one greater then the number of nodes
> treeSizes : (t: BinaryTree a) -> leafSize t = nodeSize t + 1
> treeSizes (BLeaf _) = Refl
> treeSizes (BNode l r) =
>   let indHypL = treeSizes l
>       indHypR = treeSizes r
>   in rewrite indHypL
>   in rewrite indHypR
>   in rewrite plusCommutative (nodeSize l) 1
>   in rewrite plusAssociative (nodeSize l) (nodeSize r) 1
>   in Refl

=== Ranking and unranking

We map binary trees to non-neg­a­tive inte­gers.
right are the even bits, left the uneven bits

> splitnum : {default 0 left : Int} -> {default 0 right : Int} -> {default 1 spot : Int} -> Int -> (Int,Int)
> splitnum {left} {right} 0 = (left, right)
> splitnum {left} {right} {spot} num =
>   let left'  = if num .&. 1 == 1 then left .|. spot else left
>       right' = if num .&. 2 == 2 then right .|. spot else right
>   in splitnum {left = left'} {right = right'} {spot = shiftL spot 1} (assert_smaller num (shiftR num 2))

> combnum : {default 0 acc : Int} -> {default 1 spot : Int} -> Int -> Int -> Int
> combnum {acc} 0 0 = acc
> combnum {acc} {spot} l r =
>   let a'  = if l .&. 1 == 1 then acc .|. spot else acc
>       a'' = if r .&. 1 == 1 then a' .|. (shiftL spot 1) else a'
>   in combnum {acc = a''} {spot = shiftL spot 2} (assert_smaller l (shiftR l 1)) (assert_smaller r (shiftR r 1))


> generateAll: (Eq a, Show a) => a -> Nat -> List (BinaryTree a)
> generateAll ele Z = [BLeaf ele]
> generateAll ele (S n) =
>   concatMap (\ i => [(BNode left right) | right  <- generateAll ele (assert_smaller (S n) i),
>                                           left   <- generateAll ele (assert_smaller (S n) (minus n i))])
>             [Z .. n]

> unrank : (Show a, Eq a) => a -> Int -> BinaryTree a
> unrank a 0 = BLeaf a
> unrank a n =
>   let (ln,rn) = splitnum (n - 1)
>   in  BNode (unrank a (assert_smaller n ln)) (unrank a (assert_smaller n rn))

> rank : (Show a, Eq a) => BinaryTree a -> Int
> rank (BLeaf a) = 0
> rank (BNode l r) = 1 + combnum (rank l) (rank r)

-- > splitReverseComb : {l,r,n: Int} -> (combnum l r = n) <-> ((l,r) = splitnum n)
-- > splitReverseComb = (believe_me, believe_me)

==== Properties of rank and unrank

> evenNat : (n:Nat) -> Bool
> evenNat Z     = True
> evenNat (S Z) = False
> evenNat (S (S k)) = evenNat k

> splitnumNat : Nat -> (Nat,Nat)
> splitnumNat Z = (Z, Z)
> splitnumNat (S n) =
>   let (left',right') = splitnumNat (assert_smaller (S n) (divNatNZ (S n) 4 SIsNotZ))
>       left'' = if evenNat (divNatNZ (S n) 2 SIsNotZ)
>                   then left' * 2
>                   else S (left' * 2)
>       right'' = if evenNat (S n)
>                   then right' * 2
>                   else S (right' * 2)
>   in (left'', right'')

> splitnumNatLeft : Nat -> Nat
> splitnumNatLeft Z = Z
> splitnumNatLeft (S n) =
>   let left' = splitnumNatLeft (assert_smaller (S n) (divNatNZ (S n) 4 SIsNotZ))
>       left'' = if evenNat (divNatNZ (S n) 2 SIsNotZ)
>                   then left' * 2
>                   else S (left' * 2)
>   in left''

> splitnumNatRight : Nat -> Nat
> splitnumNatRight Z = Z
> splitnumNatRight (S n) =
>   let right' = splitnumNatRight (assert_smaller (S n) (divNatNZ (S n) 4 SIsNotZ))
>       right'' = if evenNat (S n)
>                   then right' * 2
>                   else S (right' * 2)
>   in right''

> combnumNat : Nat -> Nat -> Nat
> combnumNat Z Z = Z
> combnumNat Z (S r) =
>   let res = combnumNat Z (assert_smaller (S r) (divNatNZ (S r) 2 SIsNotZ))
>       res2 = if evenNat (S r)
>                 then 4 * res
>                 else (S (2 *res))
>   in res2
> combnumNat (S l) Z =
>   let res = combnumNat (assert_smaller (S l) (divNatNZ (S l) 2 SIsNotZ)) Z
>       res2 = if evenNat (S l)
>                 then 2 * res
>                 else (S (4 *res))
>   in 2 * res2
> combnumNat (S l) (S r) =
>   let res = combnumNat
>                 (assert_smaller (S l) (divNatNZ (S l) 2 SIsNotZ))
>                 (assert_smaller (S r) (divNatNZ (S r) 2 SIsNotZ))
>       res2 = if evenNat (S l)
>                 then 2 * res
>                 else (S (2 *res))
>       res3 = if evenNat (S r)
>                 then 2 * res2
>                 else (S (2 *res2))
>   in res3

> unrankNat : (Show a, Eq a) => a -> Nat -> BinaryTree a
> unrankNat a Z = BLeaf a
> unrankNat a (S n) =
>   BNode (unrankNat a (assert_smaller (S n) (splitnumNatLeft n)))
>         (unrankNat a (assert_smaller (S n) (splitnumNatRight n)))

> rankNat : (Show a, Eq a) => BinaryTree a -> Nat
> rankNat (BLeaf a) = Z
> rankNat (BNode l r) = S (combnumNat (rankNat l) (rankNat r))

> lemmaCombnumInjectiveL : {a,b,c,d : Nat} -> combnumNat a b = combnumNat c d -> a = c
> lemmaCombnumInjectiveL = believe_me

> lemmaCombnumInjectiveR : {a,b,c,d : Nat} -> combnumNat a b = combnumNat c d -> b = d
> lemmaCombnumInjectiveR = believe_me

> lemmaBijective : Bijective BinaryTree.splitnumNat {dty=Nat} {cty=(Nat,Nat)} {x} {y}
> lemmaBijective = ((\ p => BinaryTree.combnumNat (fst p) (snd p)) ** ?lemmaBijective_rhs)

==== Basic theorems

> rankInjective : Injective {dty=BinaryTree Unit} BinaryTree.rankNat {x1} {x2}
> rankInjective {x1 = BLeaf ()} {x2 = BLeaf ()} Refl = Refl
> rankInjective {x1 = BLeaf ()} {x2 = BNode l r} Refl impossible
> rankInjective {x1 = BNode l r} {x2 = BLeaf ()} Refl impossible
> rankInjective {x1 = BNode l1 r1} {x2 = BNode l2 r2} hyp =
>   let h1 = lemmaCombnumInjectiveL {b=rankNat r1} {d=rankNat r2} (succInjective _ _ hyp)
>       h2 = lemmaCombnumInjectiveR {a=rankNat l1} {c=rankNat l2} (succInjective _ _ hyp)
>       indHypL = rankInjective {x1=l1} {x2=l2} h1
>       indHypR = rankInjective {x1=r1} {x2=r2} h2
>   in rewrite indHypL in rewrite indHypR in Refl

> rankSurjective : Surjective {dty = BinaryTree Unit} BinaryTree.rankNat {x}
> rankSurjective {x=BLeaf ()} = (Z ** Refl)
> rankSurjective {x=BNode l r} =
>   let (nl ** hypl) = rankSurjective {x=l}
>       (nr ** hypr) = rankSurjective {x=r}
>   in (S (combnumNat nl nr) ** rewrite hypl in rewrite hypr in Refl)

> lemmaUnrankInjective : (n,n' : Nat) ->
>   (unrankNat () (splitnumNatLeft n) = unrankNat () (splitnumNatLeft n'),
>    unrankNat () (splitnumNatRight n) = unrankNat () (splitnumNatRight n')) ->
>       unrankNat () n = unrankNat () n'
> lemmaUnrankInjective Z Z (hypL,hypR) = Refl
> lemmaUnrankInjective _ _ (hypL,hypR) = ?lemmaUnrankInjective_rhs

> unrankInjective : Injective (unrankNat ()) {x1} {x2}
> unrankInjective {x1 = Z} {x2 = Z} Refl = Refl
> unrankInjective {x1 = Z} {x2 = S n} hyp = absurd hyp
> unrankInjective {x1 = S n} {x2 = Z} hyp = absurd hyp
>    -- TODO Report: negEqSym don't typecheck because of constraint problem
> unrankInjective {x1 = S n} {x2 = S n'} hyp =
>   let h = ?unrankInjective_rhs
>       indHyp = unrankInjective {x1=n} {x2=n'} h
>   in  eqSucc n n' indHyp

-- > unrankSurjective : (n : Nat) -> (b : BinaryTree Unit ** b = unrankNat () n)
-- > unrankSurjective Z = (BLeaf () ** Refl)
-- > unrankSurjective n =
-- >   let (ln,rn) = splitnum n
-- >       (tl ** hypl)    = unrankSurjective (assert_smaller n ln)
-- >       (tr ** hypr)    = unrankSurjective (assert_smaller n rn)
-- >   in (BNode tl tr ** rewrite hypl in rewrite hypr in ?unrankSurjective)


--
-- > ||| Produces a list of catalan numbers
-- > catalans : Stream Integer
-- > catalans = 1 :: map (\n => sum (zipWith (*) (reverse (take' n catalans)) (take' n catalans))) [1..]




-- > combReversSplit : {n,l,r: Nat} -> l = splitnumNatLeft n -> r = splitnumNatRight n -> combnumNat l r = n
-- > combReversSplit {n=Z} Refl Refl = Refl
-- > combReversSplit {r} {n= S n'} hyp1 hyp2 =
-- >   let l' = splitnumNatLeft n'
-- >       r' = splitnumNatRight n'
-- >       indHyp = combReversSplit {n=n'} {l=l'} {r=r'} Refl Refl
-- >   in rewrite sym indHyp in rewrite hyp1 in rewrite hyp2 in ?hole

-- > lemma : {r,n : Nat} -> (0, r) = splitnumNat n -> (0,S r) = splitnumNat (S n)
-- > lemma {n=Z} Refl = Refl
-- > lemma {r=Z}{n=S Z} Refl impossible
-- > lemma {r=S r'}{n=S n'} hyp =
-- >   let indHyp = lemma {r=r'} {n=n'} _
-- >   in ?holeL
--
-- > splitReversComb : {l,r,n: Nat} -> combnumNat l r = n -> (l,r) = splitnumNat n
-- > splitReversComb {l=Z} {r=Z} Refl = Refl
-- > splitReversComb {l=Z} {r=S r'} hyp =
-- >   let n' = combnumNat Z r'
-- >       indHyp = splitReversComb {l=Z} {r=r'} {n=n'} Refl
-- >   in ?hole
-- > splitReversComb {l=S l'} {r=Z} hyp = ?hole1
-- > splitReversComb {l=S l'} {r=S r'} hyp = ?hole2


-- > ||| To complicated for me to prove, invented Nat variant to (maybe) make proves possible
-- > lemmaSplitnum: {n: Nat} ->  (l,r) = splitnum (cast n) -> (l2, r2) = splitnumNat n -> (cast l, cast r) = (l2, r2)
-- > lemmaCombnum: {l,r: Nat} ->  n = combnum (cast l) (cast r) -> n2 = combnumNat l r -> cast n = n2

==== Tests

> testRank : and (map (\ i => rank (unrank 0 i) == i) [100 .. 130]) = True
> testRank = Refl

> exTree : BinaryTree Int
> exTree = BNode (BNode (BLeaf 1) (BLeaf 2))(BNode (BLeaf 3) (BLeaf 4))

> test1 : show BinaryTree.exTree = "1->2->(3->4)"
> test1 = Refl
