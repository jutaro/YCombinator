= GenComb : Generation of binary trees

> module GenComb

> import BinaryTree
> import Combinator
> import BaseKS
> import BaseKSIBC
> import BaseBWCK
> import Id

> %access public export
> %default total

=== Ranking and unranking

> unrankKS : Int -> Comb KS
> unrankKS 0 = PrimComb K 2
> unrankKS 1 = PrimComb S 3
> unrankKS n =
>   let (ln,rn) = splitnum (n - 1)
>   in  App (unrankKS (assert_smaller n ln)) (unrankKS (assert_smaller n rn))

> rankKS : Comb KS -> Int
> rankKS (Var _) = -1
> rankKS (PrimComb K _) = 0
> rankKS (PrimComb S _) = 1
> rankKS (App l r) = 1 + combnum (rankKS l) (rankKS r)

> unrankBWCK : Int -> Comb BWCK
> unrankBWCK 0 = :B
> unrankBWCK 1 = :W
> unrankBWCK 2 = :C
> unrankBWCK 3 = :K
> unrankBWCK n =
>   let (ln,rn) = splitnum (n - 1)
>   in  App (unrankBWCK (assert_smaller n ln)) (unrankBWCK (assert_smaller n rn))

> rankBWCK : Comb BWCK -> Int
> rankBWCK (Var _) = -1
> rankBWCK (PrimComb B _) = 0
> rankBWCK (PrimComb W _) = 1
> rankBWCK (PrimComb C _) = 2
> rankBWCK (PrimComb K _) = 3
> rankBWCK a@(App l r) = 1 + combnum (rankBWCK (assert_smaller a l)) (rankBWCK (assert_smaller a r))

> unrankKSIBC : Int -> Comb KSIBC
> unrankKSIBC 0 = :K
> unrankKSIBC 1 = :S
> unrankKSIBC 2 = :I
> unrankKSIBC 3 = :B
> unrankKSIBC 4 = :C
> unrankKSIBC n =
>   let (ln,rn) = splitnum (n - 1)
>   in  App (unrankKSIBC (assert_smaller n ln)) (unrankKSIBC (assert_smaller n rn))

> rankKSIBC : Comb KSIBC -> Int
> rankKSIBC (Var _) = -1
> rankKSIBC (PrimComb K _) = 0
> rankKSIBC (PrimComb S _) = 1
> rankKSIBC (PrimComb I _) = 2
> rankKSIBC (PrimComb B _) = 3
> rankKSIBC (PrimComb C _) = 4
> rankKSIBC a@(App l r) = 1 + combnum (rankKSIBC (assert_smaller a l)) (rankKSIBC (assert_smaller a r))

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

> testRankBWCK : map GenComb.rankBWCK (map GenComb.unrankBWCK [295..300]) = [295..300]
> testRankBWCK = Refl

> testRankKS : map GenComb.rankKS (map GenComb.unrankKS [295..300]) = [295..300]
> testRankKS = Refl

> testRankKSIBC : map GenComb.rankKSIBC (map GenComb.unrankKSIBC [295..300]) = [295..300]
> testRankKSIBC = Refl

> lemmaRank1 : {n:Int} -> (c : Comb BWCK ** c = (unrankBWCK n) -> n = rankBWCK c)
> lemmaRank1 {n} = (unrankBWCK n ** (\ Refl => ?hole))
