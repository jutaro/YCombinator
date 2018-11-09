= Functions : Relations with Multi Pathes

> module Functions


> %access public export
> %default total

Main result : for functions f:A->A with finite A, f injective <-> f bijective <-> f surjective.

Require Import List Compare_dec EqNat Decidable ListDec. Require Fin.

Set Implicit Arguments.

=== General definitions

> Injective : (f: Type -> Type) -> Type
> Injective f = {x1,x2 : Type} -> f x1 = f x2 -> x1 = x2

Definition Surjective {A B} (f : A->B) :=
 forall y, exists x, f x = y.

Definition Bijective {A B} (f : A->B) :=
 exists g:B->A, (forall x, g (f x) = x) /\ (forall y, f (g y) = y).

Finiteness is defined here via exhaustive list enumeration

Definition Full {A:Type} (l:list A) := forall a:A, In a l.
Definition Finite (A:Type) := exists (l:list A), Full l.

In many following proofs, it will be convenient to have list enumerations without duplicates. As soon as we have decidability of equality (in Prop), this is equivalent to the previous notion.

Definition Listing {A:Type} (l:list A) := NoDup l /\ Full l.
Definition Finite' (A:Type) := exists (l:list A), Listing l.

Lemma Finite_alt A (d:decidable_eq A) : Finite A <-> Finite' A.

Injections characterized in term of lists

Lemma Injective_map_NoDup A B (f:A->B) (l:list A) :
 Injective f -> NoDup l -> NoDup (map f l).

Lemma Injective_list_carac A B (d:decidable_eq A)(f:A->B) :
  Injective f <-> (forall l, NoDup l -> NoDup (map f l)).

Lemma Injective_carac A B (l:list A) : Listing l ->
   forall (f:A->B), Injective f <-> NoDup (map f l).

Surjection characterized in term of lists

Lemma Surjective_list_carac A B (f:A->B):
  Surjective f <-> (forall lB, exists lA, incl lB (map f lA)).

Lemma Surjective_carac A B : Finite B -> decidable_eq B ->
  forall f:A->B, Surjective f <-> (exists lA, Listing (map f lA)).

Main result :

Lemma Endo_Injective_Surjective :
 forall A, Finite A -> decidable_eq A ->
  forall f:A->A, Injective f <-> Surjective f.

An injective and surjective function is bijective. We need here stronger hypothesis : decidability of equality in Type.

Definition EqDec (A:Type) := forall x y:A, {x=y}+{x<>y}.

First, we show that a surjective f has an inverse function g such that f.g = id.


Lemma Finite_Empty_or_not A :
  Finite A -> (A->False) \/ exists a:A,True.

Lemma Surjective_inverse :
  forall A B, Finite A -> EqDec B ->
   forall f:A->B, Surjective f ->
    exists g:B->A, forall x, f (g x) = x.

Same, with more knowledge on the inverse function: g.f = f.g = id

Lemma Injective_Surjective_Bijective :
 forall A B, Finite A -> EqDec B ->
  forall f:A->B, Injective f -> Surjective f -> Bijective f.

An example of finite type : Fin.t

Lemma Fin_Finite n : Finite (Fin.t n).

Instead of working on a finite subset of nat, another solution is to use restricted nat->nat functions, and to consider them only below a certain bound n.

Definition bFun n (f:nat->nat) := forall x, x < n -> f x < n.

Definition bInjective n (f:nat->nat) :=
 forall x y, x < n -> y < n -> f x = f y -> x = y.

Definition bSurjective n (f:nat->nat) :=
 forall y, y < n -> exists x, x < n /\ f x = y.

We show that this is equivalent to the use of Fin.t n.

Module Fin2Restrict.

Notation n2f := Fin.of_nat_lt.
Definition f2n {n} (x:Fin.t n) := proj1_sig (Fin.to_nat x).
Definition f2n_ok n (x:Fin.t n) : f2n x < n := proj2_sig (Fin.to_nat x).
Definition n2f_f2n : forall n x, n2f (f2n_ok x) = x := @Fin.of_nat_to_nat_inv.
Definition f2n_n2f x n h : f2n (n2f h) = x := f_equal (@proj1_sig _ _) (@Fin.to_nat_of_nat x n h).
Definition n2f_ext : forall x n h h', n2f h = n2f h' := @Fin.of_nat_ext.
Definition f2n_inj : forall n x y, f2n x = f2n y -> x = y := @Fin.to_nat_inj.

Definition extend n (f:Fin.t n -> Fin.t n) : (nat->nat) :=
 fun x =>
   match le_lt_dec n x with
     | left _ => 0
     | right h => f2n (f (n2f h))
   end.

Definition restrict n (f:nat->nat)(hf : bFun n f) : (Fin.t n -> Fin.t n) :=
 fun x => let (x',h) := Fin.to_nat x in n2f (hf _ h).

Ltac break_dec H :=
 let H' := fresh "H" in
 destruct le_lt_dec as [H'|H'];
  [elim (Lt.le_not_lt _ _ H' H)
  |try rewrite (n2f_ext H' H) in *; try clear H'].

Lemma extend_ok n f : bFun n (@extend n f).

Lemma extend_f2n n f (x:Fin.t n) : extend f (f2n x) = f2n (f x).

Lemma extend_n2f n f x (h:x<n) : n2f (extend_ok f h) = f (n2f h).

Lemma restrict_f2n n f hf (x:Fin.t n) :
 f2n (@restrict n f hf x) = f (f2n x).

Lemma restrict_n2f n f hf x (h:x<n) :
 @restrict n f hf (n2f h) = n2f (hf _ h).

Lemma extend_surjective n f :
  bSurjective n (@extend n f) <-> Surjective f.

Lemma extend_injective n f :
  bInjective n (@extend n f) <-> Injective f.

Lemma restrict_surjective n f h :
  Surjective (@restrict n f h) <-> bSurjective n f.

Lemma restrict_injective n f h :
  Injective (@restrict n f h) <-> bInjective n f.

End Fin2Restrict.
Import Fin2Restrict.

We can now use Proof via the equivalence ...

Lemma bInjective_bSurjective n (f:nat->nat) :
 bFun n f -> (bInjective n f <-> bSurjective n f).

Lemma bSurjective_bBijective n (f:nat->nat) :
 bFun n f -> bSurjective n f ->
 exists g, bFun n g /\ forall x, x < n -> g (f x) = x /\ f (g x) = x.
