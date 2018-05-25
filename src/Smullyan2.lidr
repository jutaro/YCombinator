Smullyan2 : Exercises from Mock a Mockingbird (Chapter 9)

> module Smullyan2

> import Combinator
> import Reduction
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
>       stepPrf = MBKLStepL >- MBKLAppR (MBKLRev MBKLStepM) >- MBKLRev MBKLStepB
>   in (a ** combinatorExtensionality x (eqStepMBKL stepPrf))

> sageExist : (x: Comb MBKL) -> (Y : Comb MBKL ** x # (Y # x)= Y # x)
> sageExist x = ?hole2
