Smullyan3 : Birds Galore: Exercises from Mock a Mockingbird (Chapter 11)

> module Smullyan3

> import Combinator
> import Reduction
> import BaseMBKL
> import BaseBWCK

> %access public export
> %default total

5) Doves

> Dove : Comb BWCK
> Dove = :B # :B

> syntax ":D" = Dove;

> dove : (x, y, z, w: Comb BWCK) -> :D # x # y # z # w = x # y # (z # w)
> dove x y z w =
>   let stepPrf = AppL (AppL StepB) >- StepB
>   in eqStep stepPrf

6) Blackbirds

> Blackbird : Comb BWCK
> Blackbird = :B # :B # :B


7) Eagle

> Eagle : Comb BWCK
> Eagle = :B # (:B # :B # :B)

> syntax ":E" = Eagle;

> eagle : (x, y, z, w, v: Comb BWCK) -> Eagle # x # y # z # w # v = x # y # (z # w # v)
> eagle x y z w v =
>   let stepPrf = AppL (AppL (AppL StepB))
>                 >- AppL (AppL (AppL StepB))
>                 >- AppL StepB
>                 >- StepB
>   in eqStep stepPrf

13) Warbler

> Mockingbird : Comb BWCK
> Mockingbird = :W # (:W # :K)

> syntax ":M" = Mockingbird;

> mockingbirdFromWarbler : (x : Comb BWCK) -> (:M # x = x # x)
> mockingbirdFromWarbler x =
>   let stepPrf = StepW >- AppL StepW >- AppL StepK
>   in (eqStep stepPrf)

15) Identity

> I : Comb BWCK
> I = :W # :K

> syntax ":I" = I;

> identity : (x : Comb BWCK) -> :I # x = x
> identity x =
>   let stepPrf = StepW >- StepK
>   in eqStep stepPrf

16) Cardinal and Identity

> identityCK : (x : Comb BWCK) -> (i: Comb BWCK ** i # x = x)
> identityCK x =
>   let i = :C # :K # :K
>       stepPrf = StepC >- StepK
>   in (i ** eqStep stepPrf)

17) Thrushes

> T : Comb BWCK
> T = :C # :I

> syntax ":T" = T;

> trush : (x, y : Comb BWCK) -> :T # x # y = y # x
> trush x y =
>   let stepPrf = StepC >- AppL StepW >- AppL StepK
>   in eqStep stepPrf

20) Robins

> R : Comb BWCK
> R = :B # :B # :T

> syntax ":R" = R;

> robin : (x, y, z : Comb BWCK) -> :R # x # y # z = y # z # x
> robin x y z =
>   let stepPrf = AppL (AppL StepB) >- StepB >- StepC >- AppL StepW >- AppL StepK
>   in eqStep stepPrf

21) Robins and Cardinals

> cardinalFromRobin :  (x, y, z : Comb BWCK) -> (c : Comb BWCK ** c # x # y # z = x # z # y)
> cardinalFromRobin x y z =
>   let c = R # R # R
>       stepPrf = AppL (AppL (AppL (AppL StepB))) >- AppL (AppL StepB) >- AppL (AppL StepC)
>                     >- AppL (AppL (AppL StepW)) >- AppL (AppL (AppL StepK))
>                 >- AppL (AppL (AppL StepB)) >- AppL StepB >- AppL StepC >- AppL (AppL StepW) >- AppL (AppL StepK)
>                 >- AppL (AppL StepB) >- StepB >- StepC >- AppL StepW >- AppL StepK
>   in (c ** eqStep stepPrf)

> {-}
> cardinalFromRobin2 :  (x, y, z : Comb BWCK) -> (c : Comb BWCK ** c # x # y # z = x # z # y)
> cardinalFromRobin2 x y z =
>   let c = R # R # R
>       seq = AppL (AppL StepB) >- StepB >- StepC >- AppL StepW >- AppL StepK
>       seq' = (map (AppL . AppL) seq >- map AppL seq >- seq)
>       stepPrf = seq'
>   in (c ** eqStep stepPrf)
> -}

37) Queer Bird

> Q : Comb BWCK
> Q = :C # :B

> syntax ":Q" = Q;

> queer : (x, y, z : Comb BWCK) -> :Q # x # y # z = y # (x # z)
> queer x y z =
>   let stepPrf = AppL StepC >- StepB
>   in eqStep stepPrf

47) Goldfinches

> Goldfinch : Comb BWCK
> Goldfinch = :B # :B # :C

> syntax ":G" = Goldfinch;

> goldfinch : (x, y, z, w : Comb BWCK) -> :G # x # y # z # w = x # w # (y # z)
> goldfinch x y z w =
>   let stepPrf = AppL (AppL (AppL StepB)) >- AppL StepB >- StepC
>   in eqStep stepPrf
