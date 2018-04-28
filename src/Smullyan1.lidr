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

> rumor1 : DecEq (Comb MT) => (a: Comb MT) -> (b : Comb MT ** a # b = b)
> rumor1 a =
>   let c  = :B # a # :M
>       cc = c # c
>   in (cc ** case decEq (a # cc) cc of
>               _ => ?hole1 )

> lemma1 : (a : Comb MT) -> reduct ((:B # a # :M) # (:B # a # :M)) = ?h0
> lemma1 a = ?h

> -- rumor1 (PrimComb pc) = \ b => ?hole
> -- rumor1 (Var vn) = ?hole1
> -- rumor1 (App l r) = ?hole2

> -- rumor2 : (a : Comb MT ** (b : Comb MT) -> Not ((a # b) = b))
