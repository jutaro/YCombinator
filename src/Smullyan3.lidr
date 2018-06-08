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

> doveSteps : Step (:D # x # y # z # w)  (x # y # (z # w))
> doveSteps = AppL (AppL StepB) >- StepB

> dove : (x, y, z, w: Comb BWCK) -> :D # x # y # z # w = x # y # (z # w)
> dove x y z w =
>   let stepPrf = doveSteps
>   in eqStep stepPrf

6) Blackbirds

> Blackbird : Comb BWCK
> Blackbird = :B # :B # :B

> blackbirdSteps : Step (Blackbird # x # y # z # w) (x # (y # z # w))
> blackbirdSteps = AppL (AppL (AppL StepB)) >- AppL StepB >- StepB

> blackbird : (x, y, z, w: Comb BWCK) -> Blackbird # x # y # z # w = x # (y # z # w)
> blackbird x y z w =
>   let stepPrf = blackbirdSteps
>   in eqStep stepPrf

7) Eagle

> Eagle : Comb BWCK
> Eagle = :B # (:B # :B # :B)

> syntax ":E" = Eagle;

> eagleSteps : Step (:E # x # y # z # w # v) (x # y # (z # w # v))
> eagleSteps = AppL (AppL (AppL StepB)) >- blackbirdSteps

> eagle : (x, y, z, w, v: Comb BWCK) -> :E # x # y # z # w # v = x # y # (z # w # v)
> eagle x y z w v =
>   let stepPrf = eagleSteps
>   in eqStep stepPrf

13) Mockingbird

> Mockingbird : Comb BWCK
> Mockingbird = :W # (:W # :K)

> syntax ":M" = Mockingbird;

> mockingBirdSteps : Step (:M # x) (x # x)
> mockingBirdSteps = StepW >- AppL StepW >- AppL StepK

> mockingbirdFromWarbler : (x : Comb BWCK) -> (:M # x = x # x)
> mockingbirdFromWarbler x =
>   let stepPrf = mockingBirdSteps
>   in (eqStep stepPrf)

Just to test how to prove the reverse with steps

> revMockingbirdFromWarbler : (x : Comb BWCK) -> (x # x = :M # x)
> revMockingbirdFromWarbler x =
>   let stepPrf = Rev mockingBirdSteps
>   in (eqStep stepPrf)


15) Identity

> I : Comb BWCK
> I = :W # :K

> syntax ":I" = I;

> identitySteps : Step (:I # x) x
> identitySteps = StepW >- StepK

> identity : (x : Comb BWCK) -> :I # x = x
> identity x =
>   let stepPrf = identitySteps
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

> trushSteps : Step (:T # x # y) (y # x)
> trushSteps = StepC >- AppL StepW >- AppL StepK

> trush : (x, y : Comb BWCK) -> :T # x # y = y # x
> trush x y =
>   let stepPrf = trushSteps
>   in eqStep stepPrf

20) Robins

> R : Comb BWCK
> R = :B # :B # :T

> syntax ":R" = R;

> robinSteps : Step (:R # x # y # z) (y # z # x)
> robinSteps = AppL (AppL StepB) >- StepB >- StepC >- AppL StepW >- AppL StepK

> robin : (x, y, z : Comb BWCK) -> :R # x # y # z = y # z # x
> robin x y z =
>   let stepPrf = robinSteps
>   in eqStep stepPrf

21) Robins and Cardinals

> cardinalFromRobin :  (x, y, z : Comb BWCK) -> (c : Comb BWCK ** c # x # y # z = x # z # y)
> cardinalFromRobin x y z =
>   let c = R # R # R
>       stepPrf = AppL (AppL robinSteps) >- AppL robinSteps >- robinSteps
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

> queerSteps : Step (:Q # x # y # z) (y # (x # z))
> queerSteps = AppL StepC >- StepB

> queer : (x, y, z : Comb BWCK) -> :Q # x # y # z = y # (x # z)
> queer x y z =
>   let stepPrf = queerSteps
>   in eqStep stepPrf

47) Goldfinches

> Goldfinch : Comb BWCK
> Goldfinch = :B # :B # :C

> syntax ":G" = Goldfinch;

> goldfinchSteps : Step (:G # x # y # z # w) (x # w # (y # z))
> goldfinchSteps = AppL (AppL (AppL StepB)) >- AppL StepB >- StepC

> goldfinch : (x, y, z, w : Comb BWCK) -> :G # x # y # z # w = x # w # (y # z)
> goldfinch x y z w =
>   let stepPrf = goldfinchSteps
>   in eqStep stepPrf
