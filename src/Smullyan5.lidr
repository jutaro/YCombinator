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

6) From Q, L, W

> sageFromQLW : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromQLW x =
>   let phi = :W # (:Q # :L # (:Q # :L))
>       stepPrf = StepW
>                   >- AppL queerSteps
>                   >- queerSteps
>                   >- larkSteps
>                   >- Rev (AppR queerSteps)
>                   >- Rev (AppR (AppL queerSteps))
>                   >- Rev (AppR StepW)
>   in (phi ** eqStep stepPrf)

6) From Q, L, I

> sageFromQLI : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromQLI x =
>   let phi = :Q # :L # (:L # :I)
>       stepPrf = queerSteps
>                 >- larkSteps
>                 >- identitySteps
>                 >- larkSteps
>                 >- Rev (AppR identitySteps)
>                 >- Rev (AppR larkSteps)
>                 >- Rev (AppR queerSteps)
>   in (phi ** eqStep stepPrf)

7) From B, W, C

Q = C B
L = B W B

> sageFromBWC : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromBWC x =
>   let phi = :W # (:B # (:C # :B # (:B # :W # :B)) # (:B # :W # :B))
>       stepPrf = StepW
>                 >- AppL StepB
>                 >- AppL StepC
>                 >- StepB
>                 >- AppL StepB
>                 >- StepW
>                 >- StepB
>                 >- Rev (AppR StepB)
>                 >- Rev (AppR (AppL StepC))
>                 >- Rev (AppR (AppL StepB))
>                 >- Rev (AppR StepW)
>   in (phi ** eqStep stepPrf)

7) From Q M

> sageFromQM : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromQM x =
>   let phi = :Q # (:Q # :M) # :M
>       stepPrf = queerSteps
>                   >- mockingBirdSteps
>                   >- queerSteps
>                   >- Rev (AppR queerSteps)
>   in (phi ** eqStep stepPrf)

8) From S L

> sageFromSL : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromSL x =
>   let phi = :S # :L # :L
>       stepPrf = starlingSteps
>                   >- larkSteps
>                   >- Rev (AppR starlingSteps)
>   in (phi ** eqStep stepPrf)

8) From B W S

> sageFromBWS : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromBWS x =
>   let phi = :W # :S # (:B # :W # :B)
>       stepPrf = AppL StepW
>                   >- starlingSteps
>                   >- larkSteps
>                   >- Rev (AppR starlingSteps)
>                   >- Rev (AppR (AppL StepW))
>   in (phi ** eqStep stepPrf)
