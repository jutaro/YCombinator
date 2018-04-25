Smullyan : Exercises from Mock a Mockingbird

> module Reduce

> import Base
> import Comb
> import Reduce

> %access public export
> %default total
> %hide Prelude.Show.Eq

> implementation Reduce MT where
>   reduceStep (App (PrimComb M) x) = Just (x # x)
>   reduceStep _ = Nothing

> data StepM : Comb MT -> Comb MT -> Type where
>   MStep   : StepM (:M # x) (x # x)
>   MRecStep : StepM l res -> StepM (l # r) (res # r)

> isFondOf : {t : Type} -> Eq t => (a: Comb t) -> (b : Comb t) -> Bool
> isFondOf a b = (App a b) == b

> data FondOf : {t : Type} -> (a : Comb t) -> (b : Comb t) -> (prf: b = a # b) -> Type where
>   Fond : FondOf a b prf

> rumor1 : (a: Comb MT) -> (b : Comb MT ** Dec (a # b = b))
> rumor1 a =
>   let c = :B # a # :M
>       cc = c # c
>   in (cc ** decEq (a # cc) cc)

> -- rumor1 (PrimComb pc) = \ b => ?hole
> -- rumor1 (Var vn) = ?hole1
> -- rumor1 (App l r) = ?hole2

> rumor2 : (a : Comb MT ** (b : Comb MT) -> Not ((a # b) = b))
