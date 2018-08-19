= BaseKSDiamond : Proof diamond property of KS

> module BaseKSDiamond

> import Combinator
> import Reduction
> import BaseKS
> import Decidable.Equality

> %access public export
> %default total

> normalForm : (a: Comb KS) -> Dec (Not (b : Comb KS ** Not (a = b) -> Step' a b))
> normalForm a = ?hole1
> -- normalForm a b unEqPrf (AppL' prf prf2) = ?hole11

> -- normalFormTest1' : (:K # :S) -> Yes
> -- normalFormTest1' = ?hole


> isNormalTest1 : isNormalForm (:K # :S) = True
> isNormalTest1 = Refl

> isNormalTest2 : isNormalForm (:K # :S # :S) = False
> isNormalTest2 = Refl
