= CombLookup : Lookup table for combinator reduction

> module CombLookup

> import Combinator
> import BaseKSIBC
> import RankComb
> import SimReductionComp
> import System

> %access public export
> %default total

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
