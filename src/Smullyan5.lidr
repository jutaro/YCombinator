Smullyan5 : A Galery of Sage Birds? : Exercises from Mock a Mockingbird (Chapter 13)

> module Smullyan5

> import Combinator
> import Reduction
> import BaseBWCK
> import Smullyan3
> import Smullyan4

> %access public export
> %default total

Sage bird Y
x(Yx) = Yx or: x # (Y # x) == Y # x

1) From M, B,R

> sageFromMBR : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromMBR x =
>   let phi = :B # :M # (:R # :M # :B)
>       stepPrf = StepB
>                   >- StepW
>                   >- AppL StepW
>                   >- AppL StepK
>                   >- AppL (AppL (AppL StepB))
>                   >- AppL StepB
>                   >- AppL StepC
>                   >- AppL (AppL StepW)
>                   >- AppL (AppL StepK)
>                   >- StepB
>                   >- AppR (Rev StepB)
>   in (phi ** eqStep stepPrf)

2) From M, B, C

> sageFromMBC : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromMBC x =
>   let phi = :B # :M # (:C # :B # :M)
>       stepPrf = StepB
>                   >- StepW
>                   >- AppL StepW
>                   >- AppL StepK
>                   >- AppL StepC
>                   >- StepB
>                   >- AppR (Rev StepB)
>   in (phi ** eqStep stepPrf)

2) From M, B, L

> sageFromMBL : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromMBL x =
>   let phi = :B # :M # :L
>       stepPrf = StepB
>                   >- StepW
>                   >- AppL StepW
>                   >- AppL StepK
>                   >- AppL StepB
>                   >- StepW
>                   >- StepB
>                   >- Rev (AppR (StepW >- AppL StepW >- AppL StepK))
>                   >- Rev (AppR StepB)
>   in (phi ** eqStep stepPrf)

> -- lemma1 (x: Comb BWCK) -> (x # x = (:W # :W # :K) # x)
