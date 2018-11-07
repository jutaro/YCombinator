= BinaryTree : Representation and generation of binary trees

> module BinaryTree

> import Data.Bits
> import Debug.Trace

> %access public export
> %default total

> data BinaryTree : a -> Type where
>   BNode: (Show a, Eq a) => BinaryTree a -> BinaryTree a -> BinaryTree a
>   BLeaf : (Show a, Eq a) => a -> BinaryTree a

> Eq a => Eq (BinaryTree a) where
>   (BNode l r) == (BNode l2 r2) = l == l2 && r == r2
>   (BLeaf e) == (BLeaf e2)      = e == e2
>   _ == _                       = False

> ||| Parenthesis are omiited left associated as in combinator terms
> Show a => Show (BinaryTree a) where
>   showPrec p (BNode l r) = showParens (p >= App) (showPrec Open l ++ "->" ++ showPrec App r)
>   showPrec _ (BLeaf e) = show e


=== Generation

We map binary tree2 to numbers following an idea from Luther Tychonievich.
A binary tree is either empty, or it has two binary trees as chil­dren. Fol­low­ing is a technique for mapping non-neg­a­tive inte­gers to binary trees in an efficient mann­er.

To de-interleave a number I write it in binary and cre­ate two numbers from it, one using the odd bits and the other the even bits. For exam­ple, to de-interleave 71 I’d write it in binary as 1000111 then I’d take the odd bits 1000111 to make 1011, which is 11, and the even bits 1000111 to make 001, which is 1; thus 71 becomes (11, 1).

> infixl 7 .&.
> (.&.) : Int -> Int -> Int
> (.&.) = prim__andInt

> infixl 5 .|.
> (.|.) : Int -> Int -> Int
> (.|.) = prim__orInt

> splitnum : Int -> (Int,Int)
> splitnum num = splitnum' 0 0 1 num
>   where
>     splitnum' : Int -> Int -> Int -> Int -> (Int,Int)
>     splitnum' left right spot 0 = (left, right)
>     splitnum' left right spot num =
>       let left' = if num .&. 1 == 1 then left .|. spot else left
>           right' = if num .&. 2 == 2 then right .|. spot else right
>       in splitnum' left' right' (shiftL spot 1) (assert_smaller num (shiftR num 2))

> combnum : Int -> Int -> Int
> combnum l r = combnum' 0 1 l r
>   where
>     combnum' : Int -> Int -> Int -> Int -> Int
>     combnum' acc spot 0 0 = acc
>     combnum' acc spot l r =
>       let a' = if l .&. 1 == 1 then acc .|. spot else acc
>           a'' = if r .&. 1 == 1 then a' .|. (shiftL spot 1) else a'
>       in combnum' a'' (shiftL spot 2) (assert_smaller l (shiftR l 1)) (assert_smaller r (shiftR r 1))

> unrank : (Show a, Eq a) => a -> Int -> BinaryTree a
> unrank a 0 = BLeaf a
> unrank a n =
>   let (ln,rn) = splitnum (n - 1)
>   in  BNode (unrank a (assert_smaller n ln)) (unrank a (assert_smaller n rn))

> rank : (Show a, Eq a) => BinaryTree a -> Int
> rank (BLeaf a) = 0
> rank (BNode l r) = 1 + combnum (rank l) (rank r)




-- > ||| Take precisely n elements from the stream
-- > ||| @ n how many elements to take
-- > ||| @ xs the stream
-- > take' : (n : Nat) -> (xs : Stream a) -> List a
-- > take' Z _ = []
-- > take' (S n) (x :: xs) = Force x :: take' n xs
--
-- > ||| Produces a list of catalan numbers
-- > catalans : Stream Integer
-- > catalans = 1 :: map (\n => sum (zipWith (*) (reverse (take' n catalans)) (take' n catalans))) [1..]


> t1 : splitnum 6 = (0,0)
> t1 = ?hole



> exTree : BinaryTree Int
> exTree = BNode (BNode (BLeaf 1) (BLeaf 2))(BNode (BLeaf 3) (BLeaf 4))

> test1 : show BinaryTree.exTree = "1->2->(3->4)"
> test1 = Refl
