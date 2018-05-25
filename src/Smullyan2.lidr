Smullyan2 : Is there a sage bird? : Exercises from Mock a Mockingbird (Chapter 10)

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

And the sage is B M L

> sageExist : (x: Comb MBKL) -> (Y : Comb MBKL ** Y # x = x # (Y # x))
> sageExist x =
>   let Y = :B # :M # :L
>       stepPrf = MBKLStepB >- MBKLStepM >- MBKLStepL >- MBKLAppR (MBKLRev MBKLStepM) >- MBKLAppR (MBKLRev MBKLStepB)
>   in (Y ** eqStepMBKL stepPrf)
