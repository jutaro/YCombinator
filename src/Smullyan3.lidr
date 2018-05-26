Smullyan3 : Birds Galore: Exercises from Mock a Mockingbird (Chapter 11)

> module Smullyan3

> import Combinator
> import Reduction
> import BaseMBKL
> import BaseBWCK

> %access public export
> %default total

5) Doves

> Dove : Comb MBKL
> Dove = :B # :B

> syntax ":D" = Dove;

> dove : (x, y, z, w: Comb MBKL) -> :D # x # y # z # w = x # y # (z # w)
> dove x y z w =
>   let
>     stepPrf = AppL (AppL StepB) >- StepB
>   in eqStep stepPrf

6) Blackbirds

> Blackbird : Comb MBKL
> Blackbird = :B # :B # :B


7) Eagle

> Eagle : Comb MBKL
> Eagle = :B # (:B # :B # :B)

> syntax ":E" = Eagle;

> eagle : (x, y, z, w, v: Comb MBKL) -> Eagle # x # y # z # w # v = x # y # (z # w # v)
> eagle x y z w v =
>   let
>     stepPrf = AppL (AppL (AppL StepB))
>                 >- AppL (AppL (AppL StepB))
>                 >- AppL StepB
>                 >- StepB
>   in eqStep stepPrf

13) Warbler

> mockingbirdFromWarbler : (x : Comb BWCK) -> (m : Comb BWCK ** m # x = x # x)
> mockingbirdFromWarbler x =
>   let m = :W # (:W # :K)
>       stepPrf = StepW >- AppL StepW >- AppL StepK
>   in (m ** eqStep stepPrf)
