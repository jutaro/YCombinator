= BinaryTree : Representation and generation of binary trees

> module BinaryTree

> import Other
> import Functions

> %access public export
> %default total

> data BinaryTree : a -> Type where
>   BNode: (Show a, Eq a)  => BinaryTree a -> BinaryTree a -> BinaryTree a
>   BLeaf : (Show a, Eq a) => a -> BinaryTree a

> Eq a => Eq (BinaryTree a) where
>   (BNode l r) == (BNode l2 r2) = l == l2 && r == r2
>   (BLeaf e) == (BLeaf e2)      = e == e2
>   _ == _                       = False

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

We map binary trees to non-neg­a­tive inte­ger following an idea from Luther Tychonievich.

Zero is a Leaf and 1 a node. To represent another number write it binary and cre­ate two numbers from it, one using the odd bits and the other the even bits. For exam­ple, to de-interleave 71 I’d write it in binary as 1000111 then I’d take the odd bits 1000111 to make 1011, which is 11, and the even bits 1000111 to make 001, which is 1; thus 71 becomes (11, 1).

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

> unrank : (Show a, Eq a) => a -> Int -> BinaryTree a
> unrank a 0 = BLeaf a
> unrank a n =
>   let (ln,rn) = splitnum (n - 1)
>   in  BNode (unrank a (assert_smaller n ln)) (unrank a (assert_smaller n rn))

> rank : (Show a, Eq a) => BinaryTree a -> Int
> rank (BLeaf a) = 0
> rank (BNode l r) = 1 + combnum (rank l) (rank r)

==== Properties of rank and unrank

> rankInjective : {b1, b2 : BinaryTree Unit} -> rank b1 = rank b2 -> b1 = b2
> rankInjective {b1 = BLeaf ()} {b2 = BLeaf ()} Refl = Refl
> rankInjective {b1 = BLeaf ()} {b2 = BNode l r} Refl impossible
> rankInjective {b1 = BNode l r} {b2 = BLeaf ()} Refl impossible
> rankInjective {b1 = BNode l1 r1} {b2 = BNode l2 r2} hyp = ?hole

> unrankInjective : {n1, n2 : Int} -> unrank () n1 = unrank () n2 -> n1 = n2
> unrankInjective {n1 = 0} {n2 = 0} Refl = Refl
> unrankInjective hyp = ?unrankInjective

> rankSurjective : (b : BinaryTree Unit) -> (n ** rank b = n)
> rankSurjective (BLeaf ()) = (0 ** Refl)
> rankSurjective (BNode l r) =
>   let (nl ** hypl) = rankSurjective l
>       (nr ** hypr) = rankSurjective r
>   in (1 + combnum nl nr ** rewrite hypl in rewrite hypr in Refl)

> unrankSurjective : (n : Int) -> (b : BinaryTree Unit ** b = unrank () n)
> unrankSurjective 0 = (BLeaf () ** Refl)
> unrankSurjective n =
>   let (ln,rn) = splitnum n
>       (tl ** hypl)    = unrankSurjective (assert_smaller n ln)
>       (tr ** hypr)    = unrankSurjective (assert_smaller n rn)
>   in (BNode tl tr ** rewrite hypl in rewrite hypr in ?unrankSurjective)


--
-- > ||| Produces a list of catalan numbers
-- > catalans : Stream Integer
-- > catalans = 1 :: map (\n => sum (zipWith (*) (reverse (take' n catalans)) (take' n catalans))) [1..]

> evenNat : (n:Nat) -> Bool
> evenNat Z     = True
> evenNat (S Z) = False
> evenNat (S (S k)) = evenNat k

> splitnumNat : {default 0 left : Nat} -> {default 0 right : Nat} -> Nat -> (Nat,Nat)
> splitnumNat {left} {right} Z = (left, right)
> splitnumNat {left} {right} (S n) =
>   let (left',right') = splitnumNat (assert_smaller (S n) (divNatNZ (S n) 4 SIsNotZ))
>       right'' = if evenNat (divNatNZ (S n) 2 SIsNotZ)
>                   then right' * 2
>                   else S (right' * 2)
>       left'' = if evenNat (S n)
>                   then left' * 2
>                   else S (left' * 2)
>   in (left'', right'')

-- > combnumNat : {default 0 acc : Nat} -> {default 1 spot : Nat} -> Nat -> Nat -> Nat
-- > combnumNat {acc} Z Z = acc
-- > combnumNat {acc} {spot} (S l) (S r) =
-- >   let a'  = if l .&. 1 == 1 then acc .|. spot else acc
-- >       a'' = if r .&. 1 == 1 then a' .|. (shiftL spot 1) else a'
-- >   in combnum {acc = a''} {spot = shiftL spot 2} (assert_smaller l (shiftR l 1)) (assert_smaller r (shiftR r 1))


> ||| To complicated for me to prove, invented Nat variant to (maybe) make proves possible
> lemmaSplitnum: {n: Nat} ->  (l,r) = splitnum (cast n) -> (l2, r2) = splitnumNat n -> (cast l, cast r) = (l2, r2)

==== Tests

> testRank : rank (unrank 0 300) = 300
> testRank = Refl

> exTree : BinaryTree Int
> exTree = BNode (BNode (BLeaf 1) (BLeaf 2))(BNode (BLeaf 3) (BLeaf 4))

> test1 : show BinaryTree.exTree = "1->2->(3->4)"
> test1 = Refl
