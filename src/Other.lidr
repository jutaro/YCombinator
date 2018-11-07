= Other : Collection of code which don't belong anywhere else

> module Other

> %access public export
> %default total

> infixl 7 .&.
> (.&.) : Int -> Int -> Int
> (.&.) = prim__andInt

> infixl 5 .|.
> (.|.) : Int -> Int -> Int
> (.|.) = prim__orInt

> forallToExistence : {X: Type} -> {P: X -> Type} -> ((b : X) -> Not (P b)) -> Not (b : X ** P b)
> forallToExistence hyp (b ** p2) = hyp b p2
