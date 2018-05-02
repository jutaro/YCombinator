Smullyan : Exercises from Mock a Mockingbird

> module Smullyan1

> import Combinator
> import BaseMB
> import BaseMBK

> %access public export
> %default total

> isFondOf : {base : Type} -> (Reduce base, Eq (Comb base)) => (a: Comb base) -> (b : Comb base) -> Bool
> isFondOf a b = (a # b) == b

> data FondOf : {base : Type} -> (a : Comb base) -> (b : Comb base) -> (prf: b = a # b) -> Type where
>   Fond : FondOf a b prf

> ||| For any Combinator 'a' in MB exist a combinator 'b', so that 'a # b = b'
> ||| This Combinator 'b' is 'B a M (B a M)'
> anyFondOfSome : (a: Comb MB) -> (b : Comb MB ** b = a # b)
> anyFondOfSome a =
>   let c   = :B # a # :M
>       cc  = c # c
>       stepPrf : StepMB cc (a # cc) = MBStepB >- MBAppR MBStepM
>   in (cc ** eqStepMB stepPrf)

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

> composition : (a, b, c, x : Comb MB) -> (d: Comb MB ** d # a # b # c # x = a # (b # (c # x)))
> composition a b c x =
>   let d  = :B # (:B # :B) # :B
>       stepPrf : StepMB (d # a # b # c # x) (a # (b # (c # x))) = MBAppL (MBAppL (MBAppL MBStepB)) >-
>         MBAppL (MBAppL MBStepB) >- MBStepB >- MBStepB
>   in (d ** eqStepMB stepPrf)

> compatible : (a, b : Comb MB) -> (x : Comb MB ** (y: Comb MB ** (y = a # x, x = b # y)))
> compatible a b =
>   let c = :B # a # b
>       y' = :B # c # :M
>       y  = y' # y'
>       x  = b # y
>       stepPrf1 : StepMB y (a # x) = MBStepB >- MBStepB >- MBAppR (MBAppR MBStepM)
>       stepPrf2 : StepMB x (b # y) = MBStepEq
>   in  (x ** (y ** (eqStepMB stepPrf1, eqStepMB stepPrf2)))

> happy : (a : Comb MB) -> (x : Comb MB ** (y: Comb MB ** (y = a # x, x = a # y)))
> happy a =
>   let c = :B # a # a
>       y' = :B # c # :M
>       y  = y' # y'
>       x  = a # y
>       stepPrf1 : StepMB y (a # x) = MBStepB >- MBStepB >- MBAppR (MBAppR MBStepM)
>       stepPrf2 : StepMB x (a # y) = MBStepEq
>   in  (x ** (y ** (eqStepMB stepPrf1, eqStepMB stepPrf2)))

> hopelesslyEgocentric : (x : Comb MBK) -> (b: Comb MBK ** b # x = b)

-- > hopelesslyEgocentric x =
-- >   let b = B # M # K
-- >   stepPrf1 : StepMB b (b # x) = MBStepB >- MBStepB >- MBAppR (MBAppR MBStepM)
