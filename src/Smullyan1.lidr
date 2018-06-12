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
>       stepPrf = StepB >- AppR StepM
>   in (cc ** eqStep stepPrf)

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
>       stepPrf = StepB >- StepM >- AppL StepM >- AppR StepM
>   in (ee ** eqStep stepPrf)

5 An exercise in Composition

> composition : (a, b, c, x : Comb MB) -> (d: Comb MB ** d # a # b # c # x = a # (b # (c # x)))
> composition a b c x =
>   let d  = :B # (:B # :B) # :B
>       stepPrf = AppL (AppL (AppL StepB)) >-
>         AppL (AppL StepB) >- StepB >- StepB
>   in (d ** eqStep stepPrf)

6 Compatible

> compatible : (a, b : Comb MB) -> (x : Comb MB ** (y: Comb MB ** (y = a # x, x = b # y)))
> compatible a b =
>   let c = :B # a # b
>       y' = :B # c # :M
>       y  = y' # y'
>       x  = b # y
>       stepPrf1 = StepB >- StepB >- AppR (AppR StepM)
>       stepPrf2 = StepEq
>   in  (x ** (y ** (eqStep stepPrf1, eqStep stepPrf2)))

7 Happy

> happy : (a : Comb MB) -> (x : Comb MB ** (y: Comb MB ** (y = a # x, x = a # y)))
> happy a =
>   let c = :B # a # a
>       y' = :B # c # :M
>       y  = y' # y'
>       x  = a # y
>       stepPrf1 = StepB >- StepB >- AppR (AppR StepM)
>       stepPrf2 = StepEq
>   in  (x ** (y ** (eqStep stepPrf1, eqStep stepPrf2)))

9 Hopelessly Egocentric

> hopelesslyEgocentric : (x : Comb MBKL) -> (b: Comb MBKL ** b # x = b)
> hopelesslyEgocentric x =
>   let b' = :B # :K # :M
>       b  = b' # b'
>       stepPrf = AppL StepB >- StepK >- StepM
>   in (b ** eqStep stepPrf)

10 Fixation

> fixation : (x, z : Comb MBKL) -> (y : Comb MBKL ** x # z = y -> x # y = y)
> fixation x z = (z ** id)

11 A fact about K

> KEgocentricHopeless : (x : Comb MBKL) -> :K # :K = :K -> :K # x = :K
> KEgocentricHopeless x hyp =
>   let stepPrf : Step (:K # :K # x) :K = StepK
>   in rewrite sym hyp
>   in rewrite eqStep stepPrf
>   in rewrite hyp
>   in Refl

15

> {-
> contagiousLemma : (a, x : Comb MBKL) -> (a # x = a) -> (y : Comb MBKL) -> (a # y = a)
> contagiousLemma a x hyp y = ?h1


> egocentricContagious : (a, x , y : Comb MBKL) -> (a # x = a) -> (a # x) # y = a # x
> egocentricContagious a x y hyp =
>   rewrite hyp
>   in ?hole
> -}
