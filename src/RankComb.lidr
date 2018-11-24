ex= RankComb : Generation of binary trees

> module RankComb

> import BinaryTree
> import Combinator
> import Bases.BaseIKSC
> import Lib.Id
> import Lib.Other

> %access public export
> %default total

=== Ranking and unranking

We map combinators to natural numbers in a Quaternary number system.
Left branches are the even numbers, right starting the rightmost
e.g 01|11|10|01 |ll|rr|ll|rr split to
left  = 0110
right = 1101

> splitnum4 : {default 0 left : Integer} -> {default 0 right : Integer} -> {default 1 spot : Integer} -> Integer -> (Integer,Integer)
> splitnum4 {left} {right} 0 = (left, right)
> splitnum4 {left} {right} {spot} num =
>   let r1 = num .&&. 3
>       right'  = if r1 /= 0 then right .||. (r1 .<<<. (spot - 1)) else right
>       num' = num .>>>. 2
>       l1 = num' .&&. 3
>       left' = if l1 /= 0 then left .||. (l1 .<<<. (spot - 1)) else left
>   in splitnum4 {left = left'} {right = right'} {spot = spot + 2} (assert_smaller num (num' .>>>. 2))

> combnum4 : {default 0 acc : Integer} -> {default 1 spot : Integer} -> Integer -> Integer -> Integer
> combnum4 {acc} 0 0 = acc
> combnum4 {acc} {spot} l r =
>   let rc = r .&&. 3
>       a1  = if rc /= 0 then acc .||. (rc .<<<. (spot - 1)) else acc
>       lc = l .&&. 3
>       a2 = if lc /= 0 then a1 .||. (lc .<<<. (spot + 1)) else a1
>   in combnum4 {acc = a2} {spot = spot + 4} (assert_smaller l (l .>>>. 2)) (assert_smaller r (r .>>>. 2))

Take I for 0, and left I's dissapear, as a zero on the left dissapears

> unrankIKSC : Integer -> Comb IKSC
> unrankIKSC 0 = :I
> unrankIKSC 1 = :K
> unrankIKSC 2 = :S
> unrankIKSC 3 = :C
> unrankIKSC n =  let (ln,rn) = splitnum4 n
>                 in App (unrankIKSC (assert_smaller n ln)) (unrankIKSC (assert_smaller n rn))

> rankIKSC : Comb IKSC -> Integer
> rankIKSC (Var _) = 0 -- should never happen
> rankIKSC (PrimComb I _) = 0
> rankIKSC (PrimComb K _) = 1
> rankIKSC (PrimComb S _) = 2
> rankIKSC (PrimComb C _) = 3
> rankIKSC a@(App l r)    = combnum4 (rankIKSC (assert_smaller a l)) (rankIKSC (assert_smaller a r))

==== Tests

> testRankIKSC : map RankComb.rankIKSC (map RankComb.unrankIKSC [295..300]) = [295..300]
> testRankIKSC = Refl

-- > testRankIKSCNub : length (nub (map RankComb.unrankIKSC [295..394])) = 100
-- > testRankIKSCNub = Refl

-- > length $ filter (\ c => combSize c == 1) (map RankComb.unrankIKSC [0..100])

-- > length $ filter (\ c => combSize c == 1) (map RankComb.unrankIKSC [0..100])
