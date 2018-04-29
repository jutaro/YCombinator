Smullyan : Exercises from Mock a Mockingbird

> module Smullyan

> import Combinator
> import Base

> %access public export
> %default total
> %hide Prelude.Show.Eq

> isFondOf : {base : Type} -> (Reduce base, Eq (Comb base)) => (a: Comb base) -> (b : Comb base) -> Bool
> isFondOf a b = (a # b) == b

> data FondOf : (base : Type) -> (a : Comb base) -> (b : Comb base) -> (prf: b = a # b) -> Type where
>   Fond : Reduce t => FondOf t a b prf

> anyFondOfSome : (a: Comb MB) -> (b : Comb MB ** b = a # b)
> anyFondOfSome a =
>   let c   = :B # a # :M
>       cc  = c # c
>       stepPrf : StepMB cc (a # cc) = MBStepB >- MBAppR MBStepM
>   in (cc ** eqStepMB stepPrf)

> egocentric : {base : Type} -> (Reduce base, Eq (Comb base)) => (a: Comb base) -> Bool
> egocentric a = (a # a) == a

> data Egocentric : (t : Type) -> Reduce t => (a : Comb t) -> (prf: a = a # a) -> Type where
>   MkEgo : Reduce t => Egocentric t a prf

> existEgocentric : (a: Comb MB ** a = a # a)
> existEgocentric =
>   let d = c
>       c = :B # :M # d # x
>       stepPrf :  StepMB c (c # c) = MBStepB >- MBStepM
>   in (c ** eqStepMB stepPrf)
