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
>                   >- mockingBirdSteps
>                   >- AppL robinSteps
>                   >- StepB
>                   >- AppR (Rev StepB)
>   in (phi ** eqStep stepPrf)

2) From M, B, C

> sageFromMBC : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromMBC x =
>   let phi = :B # :M # (:C # :B # :M)
>       stepPrf = StepB
>                   >- mockingBirdSteps
>                   >- AppL StepC
>                   >- StepB
>                   >- AppR (Rev StepB)
>   in (phi ** eqStep stepPrf)


3) From M, B, L

> sageFromMBL : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromMBL x =
>   let phi = :B # :M # :L
>       stepPrf = StepB
>                   >- mockingBirdSteps
>                   >- larkSteps
>                   >- Rev (AppR mockingBirdSteps)
>                   >- Rev (AppR StepB)
>   in (phi ** eqStep stepPrf)

4) From M, B, W

The same as before, as L = B W B

> sageFromMBW : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromMBW x =
>   let phi = :B # :M # (:B # :W # :B)
>       stepPrf = StepB
>                   >- mockingBirdSteps
>                   >- AppL StepB
>                   >- StepW
>                   >- StepB
>                   >- Rev (AppR mockingBirdSteps)
>                   >- Rev (AppR StepB)
>   in (phi ** eqStep stepPrf)

6) From Q, M, L

> sageFromQML : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromQML x =
>   let phi = :Q # :L # (:L # :I)
>       stepPrf = queerSteps
>                 >- larkSteps
>                 >- StepW
>                 >- StepK
>                 >- larkSteps
>                 >- ?hole
>   in (phi ** eqStep stepPrf)
