Smullyan2 : Is there a sage bird? : Exercises from Mock a Mockingbird (Chapter 10)

> module Smullyan2

> import Relation
> import Combinator
> import Reduction
> import RevReduction
> import BaseMBKL

> %access public export
> %default total

Sage bird Y
x(Yx) = Yx or: x # (Y # x) == Y # x

Vorstufe:
A x = x M

> composeWithM : (x: Comb MBKL) -> (a : Comb MBKL ** a # x = :B # x # :M)
> composeWithM x =
>   let a = :L
>       stepPrf = stepL' ->>+ AppR' (Rev stepM') ->>- Rev stepB'
>   in (a ** combinatorExtensionality x (eqSteps' stepPrf))

And the sage is B M L

> sageExist : (x: Comb MBKL) -> (Y : Comb MBKL ** Y # x = x # (Y # x))
> sageExist x =
>   let Y = :B # :M # :L
>       stepPrf = stepB' ->>+ stepM' ->>+ stepL' ->>+ AppR' (Rev stepM') ->>- AppR' (Rev stepB')
>   in (Y ** eqSteps' stepPrf)
