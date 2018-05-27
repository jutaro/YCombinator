Smullyan4 : Mockingbirds, Warblers and Starlings : Exercises from Mock a Mockingbird (Chapter 12)

> module Smullyan4

> import Combinator
> import Reduction
> import BaseBWCK
> import Smullyan3

> %access public export
> %default total

2) Lark from B, C M


> larkFromCBM : (x, y : Comb BWCK) -> (l : Comb BWCK ** l # x # y = x # (y # y))
> larkFromCBM x y =
>   let l = :C # :B # :M
>       stepPrf = AppL StepC >- StepB >- AppR StepW >- AppR (AppL StepW) >- AppR (AppL StepK)
>   in (l ** eqStep stepPrf)

> Lark : Comb BWCK
> Lark = :B # :W # :B

> syntax ":L" = Lark;

> larkFromBWB : (x, y : Comb BWCK) -> (:L # x # y = x # (y # y))
> larkFromBWB x y =
>   let stepPrf = AppL StepB >- StepW >- StepB
>   in (eqStep stepPrf)

10) Warblers and Hummingbirds

> Hummingbird : Comb BWCK
> Hummingbird = :B # :C # (:B # (:B # :W) # :C)

> syntax ":H" = Hummingbird;

> hummingbird : (x, y, z : Comb BWCK) -> (:H # x # y # z = x # y # z # y)
> hummingbird x y z =
>   let stepPrf = AppL (AppL StepB) >- StepC >- AppL (AppL StepB) >- AppL StepB >- StepW >- AppL StepC
>   in (eqStep stepPrf)

12 Starlings

> Starling : Comb BWCK
> Starling = :B # (:B # :W) # :G

> syntax ":S" = Starling;

> starling : (x, y, z : Comb BWCK) -> :S # x # y # z  = x # z # (y # z)
> starling x y z =
>   let stepPrf = AppL (AppL StepB) >- AppL StepB >- StepW >- AppL (AppL (AppL StepB)) >- AppL StepB >- StepC
>   in eqStep stepPrf
