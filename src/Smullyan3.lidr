Smullyan3 : Birds Galore: Exercises from Mock a Mockingbird (Chapter 11)

> module Smullyan3

> import Combinator
> import Reduction
> import BaseMBKL

> %access public export
> %default total

5) Doves

> Dove : Comb MBKL
> Dove = :B # :B

> syntax ":D" = Dove;

> dove : (x, y, z, w: Comb MBKL) -> :D # x # y # z # w = x # y # (z # w)
> dove x y z w =
>   let
>     stepPrf = MBKLAppL (MBKLAppL MBKLStepB) >- MBKLStepB
>   in eqStepMBKL stepPrf

6) Blackbirds

> Blackbird : Comb MBKL
> Blackbird = :B # (:B # :B # :B)

> blackbird : (x, y, z, w, v: Comb MBKL) -> Blackbird # x # y # z # w # v = x # y # (z # w # v)
> blackbird x y z w v =
>   let
>     stepPrf = MBKLAppL (MBKLAppL (MBKLAppL MBKLStepB))
>                 >- MBKLAppL (MBKLAppL (MBKLAppL MBKLStepB))
>                 >- MBKLAppL MBKLStepB
>                 >- MBKLStepB
>   in eqStepMBKL stepPrf
