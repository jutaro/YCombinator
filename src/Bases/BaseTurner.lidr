= Base IKCS : A base with combinators I, K, S , B, C, S2, B2, C2

> module Bases.BaseTurner

> import Combinator
> import Reduction
> import RevReduction
> import Decidable.Equality
> import Lib.Other

> %access public export
> %default total

A base with combinators K, S, I, B and C

> data Turner : Type where
>   I : Turner
>   K : Turner
>   S : Turner
>   B : Turner
>   C : Turner
>   S2 : Turner
>   B2 : Turner
>   C2 : Turner

> implementation Eq Turner where
>   I == I = True
>   K == K = True
>   B == B = True
>   S == S = True
>   C == C = True
>   B2 == B2 = True
>   S2 == S2 = True
>   C2 == C2 = True
>   _ == _ = False

> Uninhabited (I = K) where
>   uninhabited Refl impossible
> Uninhabited (I = BaseTurner.S) where
>   uninhabited Refl impossible
> Uninhabited (I = B) where
>   uninhabited Refl impossible
> Uninhabited (I = C) where
>   uninhabited Refl impossible
> Uninhabited (I = S2) where
>   uninhabited Refl impossible
> Uninhabited (I = B2) where
>   uninhabited Refl impossible
> Uninhabited (I = C2) where
>   uninhabited Refl impossible

> Uninhabited (K = I) where
>   uninhabited Refl impossible
> Uninhabited (K = BaseTurner.S) where
>   uninhabited Refl impossible
> Uninhabited (K = B) where
>   uninhabited Refl impossible
> Uninhabited (K = C) where
>   uninhabited Refl impossible
> Uninhabited (K = S2) where
>   uninhabited Refl impossible
> Uninhabited (K = B2) where
>   uninhabited Refl impossible
> Uninhabited (K = C2) where
>   uninhabited Refl impossible

> Uninhabited (BaseTurner.S = I) where
>   uninhabited Refl impossible
> Uninhabited (BaseTurner.S = K) where
>   uninhabited Refl impossible
> Uninhabited (BaseTurner.S = B) where
>   uninhabited Refl impossible
> Uninhabited (BaseTurner.S = C) where
>   uninhabited Refl impossible
> Uninhabited (BaseTurner.S = S2) where
>   uninhabited Refl impossible
> Uninhabited (BaseTurner.S = B2) where
>   uninhabited Refl impossible
> Uninhabited (BaseTurner.S = C2) where
>   uninhabited Refl impossible


> Uninhabited (B = I) where
>   uninhabited Refl impossible
> Uninhabited (B = K) where
>   uninhabited Refl impossible
> Uninhabited (B = BaseTurner.S) where
>   uninhabited Refl impossible
> Uninhabited (B = C) where
>   uninhabited Refl impossible
> Uninhabited (B = S2) where
>   uninhabited Refl impossible
> Uninhabited (B = B2) where
>   uninhabited Refl impossible
> Uninhabited (B = C2) where
>   uninhabited Refl impossible

> Uninhabited (C = I) where
>   uninhabited Refl impossible
> Uninhabited (C = K) where
>   uninhabited Refl impossible
> Uninhabited (C = BaseTurner.S) where
>   uninhabited Refl impossible
> Uninhabited (C = B) where
>   uninhabited Refl impossible
> Uninhabited (C = S2) where
>   uninhabited Refl impossible
> Uninhabited (C = B2) where
>   uninhabited Refl impossible
> Uninhabited (C = C2) where
>   uninhabited Refl impossible

> Uninhabited (S2 = I) where
>   uninhabited Refl impossible
> Uninhabited (S2 = K) where
>   uninhabited Refl impossible
> Uninhabited (S2 = S) where
>   uninhabited Refl impossible
> Uninhabited (S2 = B) where
>   uninhabited Refl impossible
> Uninhabited (S2 = C) where
>   uninhabited Refl impossible
> Uninhabited (S2 = B2) where
>   uninhabited Refl impossible
> Uninhabited (S2 = C2) where
>   uninhabited Refl impossible

> Uninhabited (B2 = I) where
>   uninhabited Refl impossible
> Uninhabited (B2 = K) where
>   uninhabited Refl impossible
> Uninhabited (B2 = BaseTurner.S) where
>   uninhabited Refl impossible
> Uninhabited (B2 = B) where
>   uninhabited Refl impossible
> Uninhabited (B2 = C) where
>   uninhabited Refl impossible
> Uninhabited (B2 = S2) where
>   uninhabited Refl impossible
> Uninhabited (B2 = C2) where
>   uninhabited Refl impossible

> Uninhabited (C2 = I) where
>   uninhabited Refl impossible
> Uninhabited (C2 = K) where
>   uninhabited Refl impossible
> Uninhabited (C2 = BaseTurner.S) where
>   uninhabited Refl impossible
> Uninhabited (C2 = B) where
>   uninhabited Refl impossible
> Uninhabited (C2 = C) where
>   uninhabited Refl impossible
> Uninhabited (C2 = S2) where
>   uninhabited Refl impossible
> Uninhabited (C2 = B2) where
>   uninhabited Refl impossible

> implementation DecEq Turner where
>   decEq I I = Yes Refl
>   decEq K K = Yes Refl
>   decEq S S = Yes Refl
>   decEq B B = Yes Refl
>   decEq C C = Yes Refl
>   decEq S2 S2 = Yes Refl
>   decEq B2 B2 = Yes Refl
>   decEq C2 C2 = Yes Refl

>   decEq I K = No absurd
>   decEq I S = No absurd
>   decEq I B = No absurd
>   decEq I C = No absurd
>   decEq I S2 = No absurd
>   decEq I B2 = No absurd
>   decEq I C2 = No absurd

>   decEq K I = No absurd
>   decEq K S = No absurd
>   decEq K B = No absurd
>   decEq K C = No absurd
>   decEq K S2 = No absurd
>   decEq K B2 = No absurd
>   decEq K C2 = No absurd

>   decEq S I = No absurd
>   decEq S K = No absurd
>   decEq S B = No absurd
>   decEq S C = No absurd
>   decEq S S2 = No absurd
>   decEq S B2 = No absurd
>   decEq S C2 = No absurd

>   decEq B I = No absurd
>   decEq B K = No absurd
>   decEq B S = No absurd
>   decEq B C = No absurd
>   decEq B S2 = No absurd
>   decEq B B2 = No absurd
>   decEq B C2 = No absurd

>   decEq C I = No absurd
>   decEq C K = No absurd
>   decEq C S = No absurd
>   decEq C B = No absurd
>   decEq C S2 = No absurd
>   decEq C B2 = No absurd
>   decEq C C2 = No absurd

>   decEq S2 I = No absurd
>   decEq S2 K = No absurd
>   decEq S2 S = No absurd
>   decEq S2 B = No absurd
>   decEq S2 C = No absurd
>   decEq S2 B2 = No absurd
>   decEq S2 C2 = No absurd

>   decEq B2 I = No absurd
>   decEq B2 K = No absurd
>   decEq B2 S = No absurd
>   decEq B2 B = No absurd
>   decEq B2 C = No absurd
>   decEq B2 S2 = No absurd
>   decEq B2 C2 = No absurd

>   decEq C2 I = No absurd
>   decEq C2 K = No absurd
>   decEq C2 S = No absurd
>   decEq C2 B = No absurd
>   decEq C2 C = No absurd
>   decEq C2 S2 = No absurd
>   decEq C2 B2 = No absurd

> implementation Show Turner where
>   show I = "I'"
>   show K = "K'"
>   show S = "S'"
>   show B = "B'"
>   show C = "C'"
>   show S2 = "S2'"
>   show B2 = "B2'"
>   show C2 = "C2'"


> data PrimStep : Comb Turner -> Comb Turner -> Type where
>   StepI   : {x: Comb Turner} -> Reduce Turner => PrimStep ((PrimComb I 1) # x) x
>   StepK   : {x, y: Comb Turner} -> Reduce Turner => PrimStep ((PrimComb K 2) # x # y) x
>   StepS   : {x, y, z: Comb Turner} -> Reduce Turner => PrimStep ((PrimComb S 3) # x # y # z) ((x # z) # (y # z))
>   StepB   : {x, y: Comb Turner} -> Reduce Turner => PrimStep ((PrimComb B 3) # x # y # z) (x # (y # z))
>   StepC   : {x, y, z: Comb Turner} -> Reduce Turner => PrimStep ((PrimComb C 2) # x # y # z) (x # z # y)
>   StepS2   : {k, x, y, z: Comb Turner} -> Reduce Turner => PrimStep ((PrimComb S2 4) # k # x # y # z) (k # (x # z) # (y # z))
>   StepB2   : {k, x, y: Comb Turner} -> Reduce Turner => PrimStep ((PrimComb B2 4) # k # x # y # z) (k # x # (y # z))
>   StepC2   : {k, x, y, z: Comb Turner} -> Reduce Turner => PrimStep ((PrimComb C2 3) # k # x # y # z) (k # (x # z) # y)

> implementation Reduce Turner where
>   reduceStep (App (PrimComb I _) x) = Just x
>   reduceStep (App (App (PrimComb K _) x) y) = Just x
>   reduceStep (App (App (App (PrimComb S _) x) y) z) = Just ((x # z) # (y # z))
>   reduceStep (App (App (App (PrimComb B _) x) y) z) = Just (x # (y # z))
>   reduceStep (App (App (App (PrimComb C _) x) y) z) = Just (x # z # y)
>   reduceStep (App (App (App (App (PrimComb S2 _) k) x) y) z) = Just (k # (x # z) # (y # z))
>   reduceStep (App (App (App (App (PrimComb B2 _) k) x) y) z) = Just (k # x # (y # z))
>   reduceStep (App (App (App (App (PrimComb C2 _) k) x) y) z) = Just (k # (x # z) # y)
>   reduceStep _ = Nothing
>   PrimRed = PrimStep

> I' : Comb Turner
> I' = PrimComb I 1

> K' : Comb Turner
> K' = PrimComb K 2

> S' : Comb Turner
> S' = PrimComb S 3

> B' : Comb Turner
> B' = PrimComb B 3

> C' : Comb Turner
> C' =  PrimComb C 2

> S2' : Comb Turner
> S2' = PrimComb S2 4

> B2' : Comb Turner
> B2' = PrimComb B2 4

> C2' : Comb Turner
> C2' = PrimComb C2 3

S′ = λkxyz.k(xz)(yz)
B′ = λkxyz.kx(yz)
C′ = λkxyz.k(xz)y

> stepI : {x, y, z: Comb Turner} -> Step (I' # x) x
> stepI = Prim StepI

> stepK : {x, y: Comb Turner} -> Step (K' # x # y) x
> stepK = Prim StepK

> stepS : {x, y, z: Comb Turner} -> Step (S' # x # y # z) ((x # z) # (y # z))
> stepS = Prim StepS

> stepB : {x, y, z: Comb Turner} -> Step (B' # x # y # z) (x # (y # z))
> stepB = Prim StepB

> stepC : {x, y: Comb Turner} -> Step (C' # x # y # z) (x # z # y)
> stepC = Prim StepC

> stepS2 : {k, x, y, z: Comb Turner} -> Step (S2' # k # x # y # z) (k # (x # z) # (y # z))
> stepS2 = Prim StepS2

> stepB2 : {k, x, y, z: Comb Turner} -> Step (B2' # k # x # y # z) (k # x # (y # z))
> stepB2 = Prim StepB2

> stepC2 : {k, x, y: Comb Turner} -> Step (C2' # k # x # y # z) (k # (x # z) # y)
> stepC2 = Prim StepC2
