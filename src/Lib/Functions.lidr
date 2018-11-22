= Functions : Relations with Multi Pathes

> module Lib.Functions

> %access public export
> %default total

=== General definitions

> Injective : {dty, cty : Type} -> (f: dty -> cty) -> {x1, x2 : dty} -> Type
> Injective {dty} {cty} f {x1} {x2} = f x1 = f x2 -> x1 = x2

> Surjective : {dty, cty : Type} -> (f: dty -> cty) -> {x : dty} -> Type
> Surjective {dty} {cty} f {x} = (y : cty ** f x = y)

> Bijective : {dty, cty : Type} -> (f: dty -> cty) -> {x : dty} -> {y : cty} -> Type
> Bijective {dty} {cty} f {x} {y} = (g : (cty -> dty) ** (g (f x) = x , f (g y) = y))
