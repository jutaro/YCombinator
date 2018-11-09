= GenComb : Generation of binary trees

> module GenComb

> import BinaryTree
> import Combinator
> import BaseKS

> %access public export
> %default total


=== Ranking and unranking

> unrank : Int -> Comb KS
> unrank 0 = :K
> unrank 1 = :S
> unrank n =
>   let (ln,rn) = splitnum (n - 1)
>   in  App (unrank (assert_smaller n ln)) (unrank (assert_smaller n rn))

-- > rank : (Show a, Eq a) => BinaryTree a -> Int
-- > rank (BLeaf a) = 0
-- > rank (BNode l r) = 1 + combnum (rank l) (rank r)




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

==== Tests

> testRank : rank (unrank 0 300) = 300
> testRank = Refl

> exTree : BinaryTree Int
> exTree = BNode (BNode (BLeaf 1) (BLeaf 2))(BNode (BLeaf 3) (BLeaf 4))

> test1 : show BinaryTree.exTree = "1->2->(3->4)"
> test1 = Refl
