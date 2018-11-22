Smullyan4 : Mockingbirds, Warblers and Starlings : Exercises from Mock a Mockingbird (Chapter 12)

> module Smullyan.Smullyan4

> import Lib.Relation
> import Combinator
> import Reduction
> import Bases.BaseBWCK
> import Smullyan.Smullyan3

> %access public export
> %default total

2) Lark from B, C M

> larkFromCBM : (x, y : Comb BWCK) -> (l : Comb BWCK ** l # x # y = x # (y # y))
> larkFromCBM x y =
>   let l = :C # :B # :M
>       stepPrf = AppL stepC ->+ stepB ->+ appR mockingBirdSteps
>   in (l ** eqSteps stepPrf)

> Lark : Comb BWCK
> Lark = :B # :W # :B

> syntax ":L" = Lark;

> larkSteps : Multi Step (:L # x # y) (x # (y # y))
> larkSteps = AppL stepB ->+ stepW ->- stepB

> larkFromBWB : (x, y : Comb BWCK) -> (:L # x # y = x # (y # y))
> larkFromBWB x y = eqSteps larkSteps

10) Warblers and Hummingbirds

> Hummingbird : Comb BWCK
> Hummingbird = :B # :C # (:B # (:B # :W) # :C)

> syntax ":H" = Hummingbird;

> hummingbirdSteps : Multi Step (:H # x # y # z) (x # y # z # y)
> hummingbirdSteps = AppL (AppL stepB) ->+ stepC ->+ AppL (AppL stepB) ->+ AppL stepB ->+ stepW ->- AppL stepC

> hummingbird : (x, y, z : Comb BWCK) -> (:H # x # y # z = x # y # z # y)
> hummingbird x y z = eqSteps hummingbirdSteps

12 Starlings

> Starling : Comb BWCK
> Starling = :B # (:B # :W) # :G

> syntax ":S" = Starling;

> starlingSteps : Multi Step (:S # x # y # z) (x # z # (y # z))
> starlingSteps = AppL (AppL stepB) ->+ AppL stepB ->+ stepW ->+ goldfinchSteps

> starling : (x, y, z : Comb BWCK) -> :S # x # y # z  = x # z # (y # z)
> starling x y z = eqSteps starlingSteps
