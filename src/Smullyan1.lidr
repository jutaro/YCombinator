Smullyan : Exercises from Mock a Mockingbird (Chapter 9)

> module Smullyan1

> import Combinator
> import Reduction
> import BaseMB
> import BaseMBKL

> %access public export
> %default total

> isFondOf : {base : Type} -> (Reduce base, Eq (Comb base)) => (a: Comb base) -> (b : Comb base) -> Bool
> isFondOf a b = (a # b) == b

> data FondOf : {base : Type} -> (a : Comb base) -> (b : Comb base) -> (prf: b = a # b) -> Type where
>   Fond : FondOf a b prf

1 Significance of the M

> ||| For any Combinator 'a' in MB exist a combinator 'b', so that 'a # b = b'
> ||| This Combinator 'b' is 'B a M (B a M)'
> anyFondOfSome : (a: Comb MB) -> (b : Comb MB ** b = a # b)
> anyFondOfSome a =
>   let c   = :B # a # :M
>       cc  = c # c
>       stepPrf : StepMB cc (a # cc) = MBStepB >- MBAppR MBStepM
>   in (cc ** eqStepMB stepPrf)

2 Egocentric

> egocentric : {base : Type} -> (Reduce base, Eq (Comb base)) => (a: Comb base) -> Bool
> egocentric a = (a # a) == a

> data Egocentric : {base : Type} -> (a : Comb base) -> (prf: a = a # a) -> Type where
>   MkEgo : Egocentric a prf

> ||| It exist a Combinator 'a' in MB, so that 'a # a = a'
> ||| This Combinator is 'B M M (B M M)'
> existEgocentric : (a: Comb MB ** a = a # a)
> existEgocentric =
>   let e   = :B # :M # :M
>       ee  = e # e
>       stepPrf : StepMB ee (ee # ee) = MBStepB >- MBStepM >- MBAppL MBStepM >- MBAppR MBStepM
>   in (ee ** eqStepMB stepPrf)

5 An exercise in Composition

> composition : (a, b, c, x : Comb MB) -> (d: Comb MB ** d # a # b # c # x = a # (b # (c # x)))
> composition a b c x =
>   let d  = :B # (:B # :B) # :B
>       stepPrf : StepMB (d # a # b # c # x) (a # (b # (c # x))) = MBAppL (MBAppL (MBAppL MBStepB)) >-
>         MBAppL (MBAppL MBStepB) >- MBStepB >- MBStepB
>   in (d ** eqStepMB stepPrf)

6 Compatible

> compatible : (a, b : Comb MB) -> (x : Comb MB ** (y: Comb MB ** (y = a # x, x = b # y)))
> compatible a b =
>   let c = :B # a # b
>       y' = :B # c # :M
>       y  = y' # y'
>       x  = b # y
>       stepPrf1 : StepMB y (a # x) = MBStepB >- MBStepB >- MBAppR (MBAppR MBStepM)
>       stepPrf2 : StepMB x (b # y) = MBStepEq
>   in  (x ** (y ** (eqStepMB stepPrf1, eqStepMB stepPrf2)))

7 Happy

> happy : (a : Comb MB) -> (x : Comb MB ** (y: Comb MB ** (y = a # x, x = a # y)))
> happy a =
>   let c = :B # a # a
>       y' = :B # c # :M
>       y  = y' # y'
>       x  = a # y
>       stepPrf1 : StepMB y (a # x) = MBStepB >- MBStepB >- MBAppR (MBAppR MBStepM)
>       stepPrf2 : StepMB x (a # y) = MBStepEq
>   in  (x ** (y ** (eqStepMB stepPrf1, eqStepMB stepPrf2)))

9 Hopelessly Egocentric

> hopelesslyEgocentric : (x : Comb MBKL) -> (b: Comb MBKL ** b # x = b)
> hopelesslyEgocentric x =
>   let b' = :B # :K # :M
>       b  = b' # b'
>       stepPrf : StepMBKL (b # x) b = MBKLAppL MBKLStepB >- MBKLStepK >- MBKLStepM
>   in (b ** eqStepMBKL stepPrf)

10 Fixation

> fixation : (x, z : Comb MBKL) -> (y : Comb MBKL ** x # z = y -> x # y = y)
> fixation x z = (z ** id)

11 A fact about K

> KEgocentricHopeless : (x : Comb MBKL) -> :K # :K = :K -> :K # x = :K
> KEgocentricHopeless x hyp =
>   let stepPrf : StepMBKL (:K # :K # x) :K = MBKLStepK
>   in rewrite sym hyp
>   in rewrite eqStepMBKL stepPrf
>   in rewrite hyp
>   in Refl

15

> contagiousLemma : (a, x : Comb MBKL) -> (a # x = a) -> (y : Comb MBKL) -> (a # y = a)
> contagiousLemma a x hyp y = ?h1


> egocentricContagious : (a, x , y : Comb MBKL) -> (a # x = a) -> (a # x) # y = a # x
> egocentricContagious a x y hyp =
>   rewrite hyp
>   in ?hole
