= RankComb : Generation of binary trees

> module RankComb

> import BinaryTree
> import Combinator
> import BaseKS
> import BaseKSBC
> import BaseBWCK
> import Id
> import Data.Fin

> %access public export
> %default total

=== Ranking and unranking

> unrankKSBC : Int -> Comb KSBC
> unrankKSBC 0 = :K
> unrankKSBC 1 = :S
> unrankKSBC 2 = :B
> unrankKSBC 3 = :C
> unrankKSBC n =
>   let (ln,rn) = if n < 20 then splitnum (n - 4) else splitnum n
>   in App (unrankKSBC (assert_smaller n ln)) (unrankKSBC (assert_smaller n rn))

> rankKSBC : Comb KSBC -> Int
> rankKSBC (Var _) = 0 -- should never happen
> rankKSBC (PrimComb K _) = 0
> rankKSBC (PrimComb S _) = 1
> rankKSBC (PrimComb B _) = 2
> rankKSBC (PrimComb C _) = 3
> rankKSBC a@(App l@(PrimComb _ _) r@(PrimComb _ _)) =
>   4 + assert_total (combnum (rankKSBC l) (rankKSBC r))
> rankKSBC a@(App l r) =
>   combnum (rankKSBC (assert_smaller a l)) (rankKSBC (assert_smaller a r))

==== Tests

> testRankKSBC : map RankComb.rankKSBC (map RankComb.unrankKSBC [295..300]) = [295..300]
> testRankKSBC = Refl

> -- lemmaRank1 : {n:Int} -> (c : Comb BWCK ** c = (unrankBWCK n) -> n = rankBWCK c)
> -- lemmaRank1 {n} = (unrankBWCK n ** (\ Refl => ?hole))
