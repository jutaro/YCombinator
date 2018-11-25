ex= RankComb : Generation of binary trees

> module RankComb

> import BinaryTree
> import Combinator
> import Bases.BaseIKSC
> import Bases.BaseTurner
> import Lib.Id
> import Lib.Other

> %access public export
> %default total

=== Ranking and unranking


We map combinators to natural numbers in a Quaternary (4 Combinators) or Octal (8 Combinators) number system.

Left branches are the even numbers, right starting the rightmost
Quaternary:
e.g 01|11|10|01 |ll|rr|ll|rr split to
left  = 0110
right = 1101

== Quaternary / Turner IKSC

> splitnumQuater : {default 0 left : Integer} -> {default 0 right : Integer} -> {default 1 spot : Integer} -> Integer -> (Integer,Integer)
> splitnumQuater {left} {right} 0 = (left, right)
> splitnumQuater {left} {right} {spot} num =
>   let r1 = num .&&. 3
>       right'  = if r1 /= 0 then right .||. (r1 .<<<. (spot - 1)) else right
>       num' = num .>>>. 2
>       l1 = num' .&&. 3
>       left' = if l1 /= 0 then left .||. (l1 .<<<. (spot - 1)) else left
>   in splitnumQuater {left = left'} {right = right'} {spot = spot + 2} (assert_smaller num (num' .>>>. 2))

> combnumQuater : {default 0 acc : Integer} -> {default 1 spot : Integer} -> Integer -> Integer -> Integer
> combnumQuater {acc} 0 0 = acc
> combnumQuater {acc} {spot} l r =
>   let rc = r .&&. 3
>       a1  = if rc /= 0 then acc .||. (rc .<<<. (spot - 1)) else acc
>       lc = l .&&. 3
>       a2 = if lc /= 0 then a1 .||. (lc .<<<. (spot + 1)) else a1
>   in combnumQuater {acc = a2} {spot = spot + 4} (assert_smaller l (l .>>>. 2)) (assert_smaller r (r .>>>. 2))

Take I for 0, and left I's dissapear, as a zero on the left dissapears

> unrankIKSC : Integer -> Comb IKSC
> unrankIKSC 0 = :I
> unrankIKSC 1 = :K
> unrankIKSC 2 = :S
> unrankIKSC 3 = :C
> unrankIKSC n =  let (ln,rn) = splitnumQuater n
>                 in App (unrankIKSC (assert_smaller n ln)) (unrankIKSC (assert_smaller n rn))

> rankIKSC : Comb IKSC -> Integer
> rankIKSC (Var _) = 0 -- should never happen
> rankIKSC (PrimComb I _) = 0
> rankIKSC (PrimComb K _) = 1
> rankIKSC (PrimComb S _) = 2
> rankIKSC (PrimComb C _) = 3
> rankIKSC a@(App l r)    = combnumQuater (rankIKSC (assert_smaller a l)) (rankIKSC (assert_smaller a r))

== Octal / Turner

> splitnumOctal : {default 0 left : Integer} -> {default 0 right : Integer} -> {default 1 spot : Integer} -> Integer -> (Integer,Integer)
> splitnumOctal {left} {right} 0 = (left, right)
> splitnumOctal {left} {right} {spot} num =
>   let r1 = num .&&. 7
>       right'  = if r1 /= 0 then right .||. (r1 .<<<. (spot - 1)) else right
>       num' = num .>>>. 3
>       l1 = num' .&&. 7
>       left' = if l1 /= 0 then left .||. (l1 .<<<. (spot - 1)) else left
>   in splitnumOctal {left = left'} {right = right'} {spot = spot + 3} (assert_smaller num (num' .>>>. 3))

> combnumOctal : {default 0 acc : Integer} -> {default 1 spot : Integer} -> Integer -> Integer -> Integer
> combnumOctal {acc} 0 0 = acc
> combnumOctal {acc} {spot} l r =
>   let rc = r .&&. 7
>       a1  = if rc /= 0 then acc .||. (rc .<<<. (spot - 1)) else acc
>       lc = l .&&. 7
>       a2 = if lc /= 0 then a1 .||. (lc .<<<. (spot + 2)) else a1
>   in combnumOctal {acc = a2} {spot = spot + 6} (assert_smaller l (l .>>>. 3)) (assert_smaller r (r .>>>. 3))

> unrankTurner : Integer -> Comb Turner
> unrankTurner 0 = I'
> unrankTurner 1 = K'
> unrankTurner 2 = S'
> unrankTurner 3 = B'
> unrankTurner 4 = C'
> unrankTurner 5 = S2'
> unrankTurner 6 = B2'
> unrankTurner 7 = C2'
> unrankTurner n =  let (ln,rn) = splitnumOctal n
>                 in App (unrankTurner (assert_smaller n ln)) (unrankTurner (assert_smaller n rn))

> rankTurner : Comb Turner -> Integer
> rankTurner (Var _) = 0 -- should never happen
> rankTurner (PrimComb I _) = 0
> rankTurner (PrimComb K _) = 1
> rankTurner (PrimComb S _) = 2
> rankTurner (PrimComb B _) = 3
> rankTurner (PrimComb C _) = 4
> rankTurner (PrimComb S2 _) = 5
> rankTurner (PrimComb B2 _) = 6
> rankTurner (PrimComb C2 _) = 7
> rankTurner a@(App l r)    = combnumOctal (rankTurner (assert_smaller a l)) (rankTurner (assert_smaller a r))


==== Tests

> testRankIKSC : map RankComb.rankIKSC (map RankComb.unrankIKSC [295..300]) = [295..300]
> testRankIKSC = Refl

> testRankTurner : map RankComb.rankTurner (map RankComb.unrankTurner [295..300]) = [295..300]
> testRankTurner = Refl

-- > testRankIKSCNub : length (nub (map RankComb.unrankIKSC [295..394])) = 100
-- > testRankIKSCNub = Refl

-- > length $ filter (\ c => combSize c == 1) (map RankComb.unrankIKSC [0..100])

-- > length $ filter (\ c => combSize c == 1) (map RankComb.unrankIKSC [0..100])
