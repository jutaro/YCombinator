= Base : Combinator Bases

> module SKI
> import Debug.Trace
> import Decidable.Equality

> %hide Language.Reflection.I
> %hide Language.Reflection.Var

> %access public export
> %default total

> -- A basic combinator base
> data IKS : Type where
>   I : IKS
>   K : IKS
>   S : IKS

> implementation Eq IKS where
>   I == I = True
>   K == K = True
>   S == S = True
>   _ == _ = False

> iNotK : I = K -> Void
> iNotK Refl impossible

> iNotS : I = S -> Void
> iNotS Refl impossible

> kNotS : K = S -> Void
> kNotS Refl impossible

> implementation DecEq IKS where
>   decEq I I = Yes Refl
>   decEq I K = No iNotK
>   decEq I S = No iNotS
>   decEq K I = No (negEqSym iNotK)
>   decEq K K = Yes Refl
>   decEq K S = No kNotS
>   decEq S I = No (negEqSym iNotS)
>   decEq S K = No (negEqSym kNotS)
>   decEq S S = Yes Refl

> implementation Show IKS where
>   show I = ":I"
>   show K = ":K"
>   show S = ":S"
