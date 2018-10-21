Smullyan3 : Birds Galore: Exercises from Mock a Mockingbird (Chapter 11)

> module Smullyan3

> import Lib
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

> doveSteps : Multi Step (:D # x # y # z # w)  (x # y # (z # w))
> doveSteps = AppL (AppL stepB) >>- stepB

> dove : (x, y, z, w: Comb BWCK) -> :D # x # y # z # w = x # y # (z # w)
> dove x y z w = eqStep doveSteps

6) Blackbirds

> Blackbird : Comb BWCK
> Blackbird = :B # :B # :B

> blackbirdSteps : Multi Step (Blackbird # x # y # z # w) (x # (y # z # w))
> blackbirdSteps = AppL (AppL (AppL stepB)) >- AppL stepB >>- stepB

> blackbird : (x, y, z, w: Comb BWCK) -> Blackbird # x # y # z # w = x # (y # z # w)
> blackbird x y z w = eqStep blackbirdSteps

7) Eagle

> Eagle : Comb BWCK
> Eagle = :B # (:B # :B # :B)

> syntax ":E" = Eagle;

> eagleSteps : Multi Step (:E # x # y # z # w # v) (x # y # (z # w # v))
> eagleSteps = AppL (AppL (AppL stepB)) >- blackbirdSteps

> eagle : (x, y, z, w, v: Comb BWCK) -> :E # x # y # z # w # v = x # y # (z # w # v)
> eagle x y z w v = eqStep eagleSteps

13) Mockingbird

> Mockingbird : Comb BWCK
> Mockingbird = :W # (:W # :K)

> syntax ":M" = Mockingbird;

> mockingBirdSteps : Multi Step (:M # x) (x # x)
> mockingBirdSteps = stepW >- AppL stepW >>- AppL stepK

> mockingbirdFromWarbler : (x : Comb BWCK) -> (:M # x = x # x)
> mockingbirdFromWarbler x = eqStep mockingBirdSteps

Just to test how to prove the reverse with steps

> revMockingbirdFromWarbler : (x : Comb BWCK) -> (x # x = :M # x)
> revMockingbirdFromWarbler x =
>   let stepPrf = reverseM (asReversableM mockingBirdSteps)
>   in (eqStep' stepPrf)


15) Identity

> I : Comb BWCK
> I = :W # :K

> syntax ":I" = I;

> identitySteps : Multi Step (:I # x) x
> identitySteps = stepW >>- stepK

> identity : (x : Comb BWCK) -> :I # x = x
> identity x = eqStep identitySteps

16) Cardinal and Identity

> identityCK : (x : Comb BWCK) -> (i: Comb BWCK ** i # x = x)
> identityCK x =
>   let i = :C # :K # :K
>       stepPrf = stepC >>- stepK
>   in (i ** eqStep stepPrf)

17) Thrushes

> T : Comb BWCK
> T = :C # :I

> syntax ":T" = T;

> trushSteps : Multi Step (:T # x # y) (y # x)
> trushSteps = stepC >- AppL stepW >>- AppL stepK

> trush : (x, y : Comb BWCK) -> :T # x # y = y # x
> trush x y = eqStep trushSteps

20) Robins

> R : Comb BWCK
> R = :B # :B # :T

> syntax ":R" = R;

> robinSteps : Multi Step (:R # x # y # z) (y # z # x)
> robinSteps = AppL (AppL stepB) >- stepB >- stepC >- AppL stepW >>- AppL stepK

> robin : (x, y, z : Comb BWCK) -> :R # x # y # z = y # z # x
> robin x y z = eqStep robinSteps

21) Robins and Cardinals

> cardinalFromRobin :  (x, y, z : Comb BWCK) -> (c : Comb BWCK ** c # x # y # z = x # z # y)
> cardinalFromRobin x y z =
>   let c = :R # :R # :R
>       stepPrf = appL (appL robinSteps) ++ appL robinSteps ++ robinSteps
>   in (c ** eqStep stepPrf)

37) Queer Bird

> Q : Comb BWCK
> Q = :C # :B

> syntax ":Q" = Q;

> queerSteps : Multi Step (:Q # x # y # z) (y # (x # z))
> queerSteps = AppL stepC >>- stepB

> queer : (x, y, z : Comb BWCK) -> :Q # x # y # z = y # (x # z)
> queer x y z = eqStep queerSteps

47) Goldfinches

> Goldfinch : Comb BWCK
> Goldfinch = :B # :B # :C

> syntax ":G" = Goldfinch;

> goldfinchSteps : Multi Step (:G # x # y # z # w) (x # w # (y # z))
> goldfinchSteps = AppL (AppL (AppL stepB)) >- AppL stepB >>- stepC

> goldfinch : (x, y, z, w : Comb BWCK) -> :G # x # y # z # w = x # w # (y # z)
> goldfinch x y z w = eqStep goldfinchSteps
