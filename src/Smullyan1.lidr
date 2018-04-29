Smullyan : Exercises from Mock a Mockingbird

> module Reduce

> import Combinator
> import Base

> %access public export
> %default total
> %hide Prelude.Show.Eq

> isFondOf : {t : Type} -> (Reduce t, Eq t, Eq (Comb t)) => (a: Comb t) -> (b : Comb t) -> Bool
> isFondOf a b = (a # b) == b

> data FondOf : (t : Type) -> Reduce t => (a : Comb t) -> (b : Comb t) -> (prf: b = a # b) -> Type where
>   Fond : Reduce t => FondOf t a b prf

> rumor : (a: Comb MB) -> (b : Comb MB ** b = a # b)
> rumor a =
>   let c   = :B # a # :M
>       cc  = c # c
>       eqPrf : StepMB ((:B # a # :M) # (:B # a # :M)) (a # ((:B # a # :M) # (:B # a # :M)))
>           = MBSteps MBStepB (MBAppR MBStepM)
>   in (cc ** eqStepMB eqPrf)
