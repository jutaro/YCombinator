= Id : Identifiers or Symbols

> module Id

> import Other

> %access public export
> %default total


> data Id : Type where
>   MkId : String -> Id
>
> beq_id : (x1, x2 : Id) -> Bool
> beq_id (MkId n1) (MkId n2) = decAsBool $ decEq n1 n2

> idInjective : {x,y : String} -> (MkId x = MkId y) -> x = y
> idInjective Refl = Refl

> implementation Eq Id where
>   (MkId s1) == (MkId s2) = s1 == s2

> implementation Show Id where
>   show (MkId s1) = s1

> implementation DecEq Id where
>   decEq (MkId s1) (MkId s2) with (decEq s1 s2)
>     | Yes prf = Yes (cong prf)
>     | No contra = No (\h : MkId s1 = MkId s2 => contra (idInjective h))


(The function \idr{decEq} comes from Idris's string library. If you check its
result type, you'll see that it does not actually return a \idr{Bool}, but
rather a type that looks like \idr{Either (x = y) (Not (x = y))}, called a
{Dec}, which can be thought of as an "evidence-carrying boolean." Formally, an
element of \idr{Dec (x=y)} is either a proof that two things are equal or a
proof that they are unequal, together with a tag indicating which. But for
present purposes you can think of it as just a fancy \idr{Bool}.)

> beq_id_refl : (x : Id) -> True = beq_id x x
> beq_id_refl (MkId n) with (decEq n n)
>   beq_id_refl _ | Yes _     = Refl
>   beq_id_refl _ | No contra = absurd $ contra Refl
>

The following useful property of  \idr{beq_id} follows from an analogous lemma
about strings:

> beq_id_true_iff : (beq_id x y = True) <-> (x = y)
> beq_id_true_iff = (bto, bfro)
>   where
>     bto : (beq_id x y = True) -> x = y
>     bto {x=MkId n1} {y=MkId n2} prf with (decEq n1 n2)
>       bto Refl | Yes eq = cong {f=MkId} eq
>       bto Refl | No _ impossible
>
>     idInj : MkId x = MkId y -> x = y
>     idInj Refl = Refl
>
>     bfro : (x = y) -> beq_id x y = True
>     bfro {x=MkId n1} {y=MkId n2} prf with (decEq n1 n2)
>       bfro _   | Yes _     = Refl
>       bfro prf | No contra = absurd $ contra $ idInj prf
>

Similarly:

> beq_id_false_iff : (beq_id x y = False) <-> Not (x = y)
> beq_id_false_iff = (to, fro)
>   where
>     to : (beq_id x y = False) -> Not (x = y)
>     to beqf = (Prelude.Basics.snd not_true_iff_false) beqf . (Prelude.Basics.snd beq_id_true_iff)
>
>     fro : (Not (x = y)) -> beq_id x y = False
>     fro noteq = (Prelude.Basics.fst not_true_iff_false) $ noteq . (Prelude.Basics.fst beq_id_true_iff)
>
