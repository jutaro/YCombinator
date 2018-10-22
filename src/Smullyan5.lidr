Smullyan5 : A Galery of Sage Birds? : Exercises from Mock a Mockingbird (Chapter 13)

> module Smullyan5

> import Relation
> import Combinator
> import Reduction
> import RevReduction
> import BaseBWCK
> import Smullyan3
> import Smullyan4

> %access public export
> %default total

Sage bird Y
x(Yx) = Yx or: x # (Y # x) == Y # x

1) From M, B,R

1) From M, B,R

> sageFromMBR : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromMBR x =
>   let phi = :B # :M # (:R # :M # :B)
>       stepPrf = stepB'
>                 ->>+ asReversableM mockingBirdSteps
>                 +>>+ appL' (asReversableM robinSteps)
>                 +>>+ stepB'
>                 ->>- AppR' (Rev stepB')
>   in (phi ** eqStep' stepPrf)


2) From M, B, C

> sageFromMBC : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromMBC x =
>   let phi = :B # :M # (:C # :B # :M)
>       stepPrf = stepB'
>                   ->>+ asReversableM mockingBirdSteps
>                   +>>+ AppL' stepC'
>                   ->>+ stepB'
>                   ->>- AppR' (Rev stepB')
>   in (phi ** eqStep' stepPrf)


3) From M, B, L

> sageFromMBL : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromMBL x =
>   let phi = :B # :M # :L
>       stepPrf = stepB'
>                   ->>+ asReversableM mockingBirdSteps
>                   +>>+ asReversableM larkSteps
>                   +>>+ reverseM (appR' (asReversableM mockingBirdSteps))
>                   +>>- Rev (AppR' stepB')
>   in (phi ** eqStep' stepPrf)

4) From M, B, W

The same as before, as L = B W B

> sageFromMBW : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromMBW x =
>   let phi = :B # :M # (:B # :W # :B)
>       stepPrf = stepB'
>                   ->>+ asReversableM mockingBirdSteps
>                   +>>+ AppL' stepB'
>                   ->>+ stepW'
>                   ->>+ stepB'
>                   ->>+ reverseM (appR' (asReversableM mockingBirdSteps))
>                   +>>- Rev (AppR' stepB')
>   in (phi ** eqStep' stepPrf)

6) From Q, L, W

> sageFromQLW : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromQLW x =
>   let phi = :W # (:Q # :L # (:Q # :L))
>       stepPrf = stepW'
>                   ->>+ appL' (asReversableM queerSteps)
>                   +>>+ asReversableM queerSteps
>                   +>>+ asReversableM larkSteps
>                   +>>+ reverseM (appR' (asReversableM queerSteps))
>                   +>>+ reverseM (appR' (appL' (asReversableM queerSteps)))
>                   +>>- Rev (AppR' stepW')
>   in (phi ** eqStep' stepPrf)

6) From Q, L, I

> sageFromQLI : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromQLI x =
>   let phi = :Q # :L # (:L # :I)
>       stepPrf = asReversableM queerSteps
>                 +>>+ asReversableM larkSteps
>                 +>>+ asReversableM identitySteps
>                 +>>+ asReversableM larkSteps
>                 +>>+ reverseM (appR' (asReversableM identitySteps))
>                 +>>+ reverseM (appR' (asReversableM larkSteps))
>                 +>>+ reverseM (appR' (asReversableM queerSteps))
>   in (phi ** eqStep' stepPrf)

7) From B, W, C

Q = C B
L = B W B

> sageFromBWC : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromBWC x =
>   let phi = :W # (:B # (:C # :B # (:B # :W # :B)) # (:B # :W # :B))
>       stepPrf = stepW'
>                 ->>+ AppL' stepB'
>                 ->>+ AppL' stepC'
>                 ->>+ stepB'
>                 ->>+ AppL' stepB'
>                 ->>+ stepW'
>                 ->>+ stepB'
>                 ->>+ Rev (AppR' stepB')
>                 ->>+ Rev (AppR' (AppL' stepC'))
>                 ->>+ Rev (AppR' (AppL' stepB'))
>                 ->>- Rev (AppR' stepW')
>   in (phi ** eqStep' stepPrf)

8) From Q M

> sageFromQM : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromQM x =
>   let phi = :Q # (:Q # :M) # :M
>       stepPrf = asReversableM queerSteps
>                   +>>+ asReversableM mockingBirdSteps
>                   +>>+ asReversableM queerSteps
>                   +>>+ reverseM (appR' (asReversableM queerSteps))
>   in (phi ** eqStep' stepPrf)

9) From S L

> sageFromSL : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromSL x =
>   let phi = :S # :L # :L
>       stepPrf = asReversableM starlingSteps
>                   +>>+ asReversableM larkSteps
>                   +>>+ reverseM (appR' (asReversableM starlingSteps))
>   in (phi ** eqStep' stepPrf)

10) From B W S

> sageFromBWS : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromBWS x =
>   let phi = :W # :S # (:B # :W # :B)
>       stepPrf = AppL' stepW'
>                   ->>+ asReversableM starlingSteps
>                   +>>+ asReversableM larkSteps
>                   +>>+ reverseM (appR' (asReversableM starlingSteps))
>                   +>>- Rev (AppR' (AppL' stepW'))
>   in (phi ** eqStep' stepPrf)

11) TuringBird

> Turing : Comb BWCK
> Turing = :B # :W # (:L # :Q)

> syntax ":U" = Turing;

> turingSteps : Multi Step (:U # x # y) (y # (x # x # y))
> turingSteps = AppL stepB ->+ stepW ->+ appL (appL larkSteps) +>+ queerSteps

> turing : (x, y : Comb BWCK) -> :U # x # y = y # (x # x # y)
> turing x y = eqStep turingSteps

12) From U

> sageFromU : (x : Comb BWCK) -> (phi: Comb BWCK ** phi # x = x # (phi # x))
> sageFromU x =
>   let phi = :U # :U
>       stepPrf = turingSteps
>   in (phi ** eqStep stepPrf)

13) Owls

> Owl : Comb BWCK
> Owl = :B # :W # (:C # :B)

> syntax ":O" = Owl;

> owlSteps : Multi Step (:O # x # y) (y # (x # y))
> owlSteps = AppL stepB ->+ stepW ->+ AppL stepC ->- stepB

> owl : (x, y : Comb BWCK) -> :O # x # y = y # (x # y)
> owl x y = eqStep owlSteps

14) Turing from O and L

> turingFromOL : (x, y : Comb BWCK) -> (t : Comb BWCK ** t # x # y = y # (x # x # y))
> turingFromOL x y =
>   let t = :L # :O
>       stepPrf = appL larkSteps +>+ owlSteps
>   in (t ** eqStep stepPrf)

15) Mockingbird from O I

> mockingbirdFromOI : (x : Comb BWCK) -> (m : Comb BWCK ** m # x = x # x)
> mockingbirdFromOI x =
>   let m = :O # :I
>       stepPrf = owlSteps +>+ appR identitySteps
>   in (m ** eqStep stepPrf)

16) Owl from S I

> owlFromSI : (x, y : Comb BWCK) -> (o : Comb BWCK ** o # x # y = y # (x # y))
> owlFromSI x y =
>   let o = :S # :I
>       stepPrf = starlingSteps +>+ appL identitySteps
>   in (o ** eqStep stepPrf)

17) x y = y -> x (x y) = x y

> lemmaPre : (x, y : Comb BWCK) -> x # y = y -> x # (x # y) = x # y
> lemmaPre x y hyp = rewrite hyp in hyp

18)

> owlSage : (x :Comb BWCK) -> (y : Comb BWCK) -> y # x = x # (y # x) -> x # (:O # y # x) = :O # y # x
> owlSage x y hyp =
>   let hyp1 = cong {f=App x} hyp
>       stepPrf = appR' (asReversableM owlSteps) +>>+ StepEq (sym hyp1) ->>+ reverseM (asReversableM owlSteps)
>   in (eqStep' stepPrf)

19)

> owlSage2 : (y : Comb BWCK) -> ((x :Comb BWCK) -> y # x = x # (y # x)) -> :O # (y # :O) = y # :O
> owlSage2 y hyp =
>   let stepPrf = MultiStep (Rev (StepEq (hyp :O))) MultiRefl
>   in (eqStep' stepPrf)

20)

> owlSage3 : (y : Comb BWCK) -> (x :Comb BWCK) -> :O # y = y ->  y # x = x # (y # x)
> owlSage3 y x hyp =
>   let hyp1 = cong {f= \ arg => App arg x} hyp
>       stepPrf = StepEq (sym hyp1) ->>+ asReversableM owlSteps
>   in (eqStep' stepPrf)

22)

> owlSage5 : (x :Comb BWCK) -> (y : Comb BWCK) -> y # x = x # (y # x) -> :O # y = y
> owlSage5 x y hyp =
>   let hyp1 : Multi Step' (:O # y # x) (y # x) = asReversableM owlSteps +>>- StepEq (sym hyp)
>       stepPrf = MultiStep (StepEq (combinatorExtensionality x (eqStep' hyp1))) MultiRefl
>   in (eqStep' stepPrf)
