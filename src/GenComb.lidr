= GenComb : Generation of binary trees

> module GenComb

> import BinaryTree
> import Combinator
> import BaseKS
> import BaseKSIBC
> import BaseBWCK
> import Functions

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

// Number of binary trees with n internal nodes is:
> catalan : Integer -> Integer
> catalan 0 = 0
> catalan 1 = 1
> catalan n = assert_total ((2 * (2 * n - 1) * catalan (n - 1)) `div` (n + 1))

catalan 19 = 1767263190

bei 2 basis Kombinatoren ergibt sich ein Baum mit 17 Knoten
Die Tabelle hätte eine Größe von 1767263190 * 4 Byte = ~ 7 Gigabyte

catalan 18 = 477638700

bei 2 basis Kombinatoren ergibt sich ein Baum mit 16 Knoten
Die Tabelle hätte eine Größe von 477638700 * 4 Byte = 1910554800 Byte = ~ 1,9 Gigabyte

catalan 17 = 129644790 Maybe choose this for more realistic simulation

bei 2 basis Kombinatoren ergibt sich ein Baum mit 15 Knoten
bei 4 basis Kombinatoren ergibt sich ein Baum mit 13 Knoten

Die Tabelle hätte eine Größe von 129644790 * 4 Byte = 518579160 Byte = ~ 0,5 Gigabyte ~ 500 MB

catalan 16 = 35357670

bei 2 basis Kombinatoren ergibt sich ein Baum mit 14 Knoten
Die Tabelle hätte eine Größe von 35357670 * 4 Byte = 141430680 Byte = ~ 0,141 Gigabyte ~ 140 MB

catalan 15 = 9694845

bei 2 basis Kombinatoren ergibt sich ein Baum mit 13 Knoten
Die Tabelle hätte eine Größe von 9694845 * 4 Byte = 38779380 Byte = ~ 0,03 Gigabyte ~ 38 MB

catalan 11 = 58786

bei 2 basis Kombinatoren ergibt sich ein Baum mit 9 Knoten
Die Tabelle hätte eine Größe von 58786 * 2 Byte = 117572 Byte = ~ 0.11 MB = 117 Kilobyte



==== Tests

> testRankBWCK : map GenComb.rankBWCK (map GenComb.unrankBWCK [295..300]) = [295..300]
> testRankBWCK = Refl

> testRankKS : map GenComb.rankKS (map GenComb.unrankKS [295..300]) = [295..300]
> testRankKS = Refl

> testRankKSIBC : map GenComb.rankKSIBC (map GenComb.unrankKSIBC [295..300]) = [295..300]
> testRankKSIBC = Refl

> lemmaRank1 : {n:Int} -> (c : Comb BWCK ** c = (unrankBWCK n) -> n = rankBWCK c)
> lemmaRank1 {n} = (unrankBWCK n ** (\ Refl => ?hole))
