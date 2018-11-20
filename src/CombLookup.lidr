= CombLookup : Lookup table for combinator reduction

> module CombLookup

> import Combinator
> import BaseKSIBC
> import RankComb
> import SimReductionComp
> import System

> %access public export
> %default total

Here we assume to work with integers, which shall not be bigger then 2 ^ 31 = 2147483648

> ||| Number of binary trees with n internal nodes is:
> catalan : Integer -> Integer
> catalan 0 = 0
> catalan 1 = 1
> catalan n = assert_total ((2 * (2 * n - 1) * catalan (n - 1)) `div` (n + 1))

catalan 19 = 1767263190
Die Tabelle hätte eine Größe von 1767263190 * 4 Byte = ~ 7 Gigabyte

catalan 18 = 477638700
Die Tabelle hätte eine Größe von 477638700 * 4 Byte = 1910554800 Byte = ~ 1,9 Gigabyte

catalan 17 = 129644790 Maybe choose this for more realistic simulation
Die Tabelle hätte eine Größe von 129644790 * 4 Byte = 518579160 Byte = ~ 0,5 Gigabyte ~ 500 MB

catalan 16 = 35357670
Die Tabelle hätte eine Größe von 35357670 * 4 Byte = 141430680 Byte = ~ 0,141 Gigabyte ~ 140 MB

catalan 15 = 9694845
Die Tabelle hätte eine Größe von 9694845 * 4 Byte = 38779380 Byte = ~ 0,03 Gigabyte ~ 38 MB

catalan 11 = 58786
Die Tabelle hätte eine Größe von 58786 * 2 Byte = 117572 Byte = ~ 0.11 MB = 117 Kilobyte
2 Kominatoren = 58786 * (2 ^ 11) = 120393728 
Die Tabelle hätte eine Größe von 120393728 * 4 Byte = 481574912 Byte = *** Prod ~ 481 MB


catalan 10 = 16796
Die Tabelle hätte eine Größe von 16796 * 4 Byte = 67184 Byte = ~ 67 Kb
2 Kominatoren = 16796 * (2 ^ 10) = 17199104
Die Tabelle hätte eine Größe von 17199104 * 4 Byte = 68796416 Byte = *** Test ~ 68 MB
5 Kominatoren = 16796 * (5 ^ 10) = 164023437500
Die Tabelle hätte eine Größe von 164023437500 * 4 Byte =  656 GByte

catalan 8 = 1034
Die Tabelle hätte eine Größe von 1034 * 2 Byte = 2068 Byte
2 Kominatoren = 1034 * (2 ^ 8) = 264704
Die Tabelle hätte eine Größe von 264704 * 4 Byte = 1058816 Byte = ~ 1 MB
5 Kominatoren = 1034 * (5 ^ 8) = 403906250
Die Tabelle hätte eine Größe von 1615625000 * 4 Byte =  6462500000 = *** Prod 6,4 GB

catalan 7 = 429
Die Tabelle hätte eine Größe von 429 * 2 Byte = 858 Byte
2 Kominatoren = 429 * (2 ^ 7) = 54912
Die Tabelle hätte eine Größe von 54912 * 2 Byte = 109824 Byte = ~ 100 KBye
7 * 3 = 21 bit +
5 Kominatoren = 429 * (5 ^ 7) = 33515625
Die Tabelle hätte eine Größe von 33515625 * 4 Byte = *** Test 33 MB


> getLineFor : Int -> (Int, Int, String, String)
> getLineFor n =
>   let comb = unrankKSIBC n
>       condNewComb = sr comb
>       newNum =  case condNewComb of
>                   Nothing => -2 -- loop or unfinished
>                   Just c  =>
>                     let ranked = rankKSIBC c
>                     in  if ranked == n
>                           then -1 -- normal form
>                           else ranked
>       newCombString =
>         if newNum < 0
>           then ""
>           else case condNewComb of
>                   Just nc => show nc
>                   Nothing => "impossible"
>       res = (n, newNum, show comb, newCombString)
>   in (n, newNum, show comb, newCombString)

> mkTable : {default [] acc: List (Int, Int, String, String)} -> Int -> List (Int, Int, String, String)
> mkTable {acc} (-1) = acc
> mkTable {acc} n =
>   let res = getLineFor n
>   in mkTable {acc = res :: acc} (assert_smaller n (n - 1))

> lineAsString : (Int, Int, String, String) -> String
> lineAsString (from,to,fromComb,toComb) = show from ++ ";" ++ show to ++ ";" ++ fromComb ++ ";" ++ toComb

> partial writeTable : Int -> Int -> String -> IO ()
> writeTable from to fileName = (do
>   when (from >= to) $ do
>     putStrLn "to needs to be bigger then from"
>     exitFailure
>   fc <- openFile fileName WriteTruncate
>   case fc of
>     Left error => do
>       putStrLn ("Can't open file " ++ fileName)
>       exitFailure
>     Right file => do
>       writeIt file from
>       closeFile file
>       exitSuccess)
>     where
>       partial writeIt : File -> Int -> IO ()
>       writeIt file n =
>         if n == to
>           then pure ()
>           else do
>             fPutStrLn file (lineAsString (getLineFor n))
>             when (mod n 10 == 0) (putStrLn (show n))
>             writeIt file (n + 1)
