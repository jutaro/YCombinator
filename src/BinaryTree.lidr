= BinaryTree : Representation and generation of binary trees

> module BinaryTree

> import Other
> import Functions
> import Decidable.Equality

> %access public export
> %default total

> data BinaryTree : a -> Type where
>   BNode: (Show a, Eq a)  => BinaryTree a -> BinaryTree a -> BinaryTree a
>   BLeaf : (Show a, Eq a) => a -> BinaryTree a

> Eq a => Eq (BinaryTree a) where
>   (BNode l r) == (BNode l2 r2) = l == l2 && r == r2
>   (BLeaf e) == (BLeaf e2)      = e == e2
>   _ == _                       = False

> nodeInjectiveLeft : (Eq a, Show a) => {l1,r1,l2,r1 : BinaryTree a} -> (BNode l1 r1 = BNode l2 r2) -> l1 = l2
> nodeInjectiveLeft Refl = Refl

> nodeInjectiveRight : (Eq a, Show a) => {l1,r1,l2,r1 : BinaryTree a} -> (BNode l1 r1 = BNode l2 r2) -> r1 = r2
> nodeInjectiveRight Refl = Refl

> leafInjective : (Eq a, Show a) => {l,r : a} -> (BLeaf l = BLeaf r) -> l = r
> leafInjective Refl = Refl

> implementation (Eq a, Show a) => Uninhabited ((the (BinaryTree a) (BLeaf _)) = BNode _ _) where
>   uninhabited Refl impossible

> implementation (Eq a, Show a) => Uninhabited ((the (BinaryTree a) (BNode _ _)) = BLeaf _) where
>   uninhabited Refl impossible

> DecEq a => DecEq (BinaryTree a) where
>   decEq (BLeaf e) (BLeaf f) with (decEq e f)
>     | (Yes prf)   = Yes $ cong prf
>     | (No contra) = No (\h => contra (leafInjective h))
>   decEq (BNode l1 r1) (BNode l2 r2) with (decEq l1 l2, decEq r1 r2)
>     | (Yes prfL,Yes prfR)   = Yes $ rewrite prfL in cong prfR
>     | (No contraL,_) = No (\h => contraL (nodeInjectiveLeft {r1} h))
>     | (_ ,No contraR) = No (\h => contraR (nodeInjectiveRight {r1} h))
>   decEq (BNode _ _) (BLeaf _) = No $ absurd
>   decEq (BLeaf _) (BNode _ _) = No $ absurd

> ||| Parenthesis are omiited left associated as in combinator terms
> Show a => Show (BinaryTree a) where
>   showPrec p (BNode l r) = showParens (p >= App) (showPrec Open l ++ "->" ++ showPrec App r)
>   showPrec _ (BLeaf e)   = show e

> ||| The number of nodes of the tree
> nodeSize : BinaryTree a -> Nat
> nodeSize (BLeaf _) = 0
> nodeSize (BNode l r) = 1 + nodeSize l + nodeSize r

> ||| The number of leafs of the tree
> leafSize : BinaryTree a -> Nat
> leafSize (BLeaf _) = 1
> leafSize (BNode l r) = leafSize l + leafSize r

> ||| The number of leafs is one greater then the number of nodes
> treeSizes : (t: BinaryTree a) -> leafSize t = nodeSize t + 1
> treeSizes (BLeaf _) = Refl
> treeSizes (BNode l r) =
>   let indHypL = treeSizes l
>       indHypR = treeSizes r
>   in rewrite indHypL
>   in rewrite indHypR
>   in rewrite plusCommutative (nodeSize l) 1
>   in rewrite plusAssociative (nodeSize l) (nodeSize r) 1
>   in Refl

=== Ranking and unranking

We map binary trees to non-neg­a­tive inte­gers.

> splitnum : {default 0 left : Int} -> {default 0 right : Int} -> {default 1 spot : Int} -> Int -> (Int,Int)
> splitnum {left} {right} 0 = (left, right)
> splitnum {left} {right} {spot} num =
>   let left'  = if num .&. 2 == 2 then left .|. spot else left
>       right' = if num .&. 1 == 1 then right .|. spot else right
>   in splitnum {left = left'} {right = right'} {spot = shiftL spot 1} (assert_smaller num (shiftR num 2))

Given that you know that every other bit is 0 in your application, you can do it like this:

x = (x | (x >> 1)) & 0x33333333;
x = (x | (x >> 2)) & 0x0f0f0f0f;
x = (x | (x >> 4)) & 0x00ff00ff;
x = (x | (x >> 8)) & 0x0000ffff;
The first step looks like this:

  0a0b0c0d0e0f0g0h0i0j0k0l0m0n0o0p   x
| 00a0b0c0d0e0f0g0h0i0j0k0l0m0n0o0   x >> 1
  --------------------------------
= 0aabbccddeeffgghhiijjkkllmmnnoop   x | (x >> 1)
& 00110011001100110011001100110011   0x33333333
  --------------------------------
= 00ab00cd00ef00gh00ij00kl00mn00op   (x | (x >> 1)) & 0x33333333
Then the second step works with two bits at a time, and so on.

shareeditflag
answered Jul 12 '10 at 23:54

…and if you don't know that the odd bits are zero, do x &= 0x55555555 in before – Bergi Jun 19 '15 at 5:43

> combnum : {default 0 acc : Int} -> {default 1 spot : Int} -> Int -> Int -> Int
> combnum {acc} 0 0 = acc
> combnum {acc} {spot} l r =
>   let a'  = if r .&. 1 == 1 then acc .|. spot else acc
>       a'' = if l .&. 1 == 1 then a' .|. (shiftL spot 1) else a'
>   in combnum {acc = a''} {spot = shiftL spot 2} (assert_smaller l (shiftR l 1)) (assert_smaller r (shiftR r 1))

Interleave bits the obvious way
unsigned short x;   // Interleave bits of x and y, so that all of the
unsigned short y;   // bits of x are in the even positions and y in the odd;
unsigned int z = 0; // z gets the resulting Morton Number.

for (int i = 0; i < sizeof(x) * CHAR_BIT; i++) // unroll for more speed...
{
  z |= (x & 1U << i) << i | (y & 1U << i) << (i + 1);
}
Interleaved bits (aka Morton numbers) are useful for linearizing 2D integer coordinates, so x and y are combined into a single number that can be compared easily and has the property that a number is usually close to another if their x and y values are close.
Interleave bits by table lookup
static const unsigned short MortonTable256[256] =
{
  0x0000, 0x0001, 0x0004, 0x0005, 0x0010, 0x0011, 0x0014, 0x0015,
  0x0040, 0x0041, 0x0044, 0x0045, 0x0050, 0x0051, 0x0054, 0x0055,
  0x0100, 0x0101, 0x0104, 0x0105, 0x0110, 0x0111, 0x0114, 0x0115,
  0x0140, 0x0141, 0x0144, 0x0145, 0x0150, 0x0151, 0x0154, 0x0155,
  0x0400, 0x0401, 0x0404, 0x0405, 0x0410, 0x0411, 0x0414, 0x0415,
  0x0440, 0x0441, 0x0444, 0x0445, 0x0450, 0x0451, 0x0454, 0x0455,
  0x0500, 0x0501, 0x0504, 0x0505, 0x0510, 0x0511, 0x0514, 0x0515,
  0x0540, 0x0541, 0x0544, 0x0545, 0x0550, 0x0551, 0x0554, 0x0555,
  0x1000, 0x1001, 0x1004, 0x1005, 0x1010, 0x1011, 0x1014, 0x1015,
  0x1040, 0x1041, 0x1044, 0x1045, 0x1050, 0x1051, 0x1054, 0x1055,
  0x1100, 0x1101, 0x1104, 0x1105, 0x1110, 0x1111, 0x1114, 0x1115,
  0x1140, 0x1141, 0x1144, 0x1145, 0x1150, 0x1151, 0x1154, 0x1155,
  0x1400, 0x1401, 0x1404, 0x1405, 0x1410, 0x1411, 0x1414, 0x1415,
  0x1440, 0x1441, 0x1444, 0x1445, 0x1450, 0x1451, 0x1454, 0x1455,
  0x1500, 0x1501, 0x1504, 0x1505, 0x1510, 0x1511, 0x1514, 0x1515,
  0x1540, 0x1541, 0x1544, 0x1545, 0x1550, 0x1551, 0x1554, 0x1555,
  0x4000, 0x4001, 0x4004, 0x4005, 0x4010, 0x4011, 0x4014, 0x4015,
  0x4040, 0x4041, 0x4044, 0x4045, 0x4050, 0x4051, 0x4054, 0x4055,
  0x4100, 0x4101, 0x4104, 0x4105, 0x4110, 0x4111, 0x4114, 0x4115,
  0x4140, 0x4141, 0x4144, 0x4145, 0x4150, 0x4151, 0x4154, 0x4155,
  0x4400, 0x4401, 0x4404, 0x4405, 0x4410, 0x4411, 0x4414, 0x4415,
  0x4440, 0x4441, 0x4444, 0x4445, 0x4450, 0x4451, 0x4454, 0x4455,
  0x4500, 0x4501, 0x4504, 0x4505, 0x4510, 0x4511, 0x4514, 0x4515,
  0x4540, 0x4541, 0x4544, 0x4545, 0x4550, 0x4551, 0x4554, 0x4555,
  0x5000, 0x5001, 0x5004, 0x5005, 0x5010, 0x5011, 0x5014, 0x5015,
  0x5040, 0x5041, 0x5044, 0x5045, 0x5050, 0x5051, 0x5054, 0x5055,
  0x5100, 0x5101, 0x5104, 0x5105, 0x5110, 0x5111, 0x5114, 0x5115,
  0x5140, 0x5141, 0x5144, 0x5145, 0x5150, 0x5151, 0x5154, 0x5155,
  0x5400, 0x5401, 0x5404, 0x5405, 0x5410, 0x5411, 0x5414, 0x5415,
  0x5440, 0x5441, 0x5444, 0x5445, 0x5450, 0x5451, 0x5454, 0x5455,
  0x5500, 0x5501, 0x5504, 0x5505, 0x5510, 0x5511, 0x5514, 0x5515,
  0x5540, 0x5541, 0x5544, 0x5545, 0x5550, 0x5551, 0x5554, 0x5555
};

unsigned short x; // Interleave bits of x and y, so that all of the
unsigned short y; // bits of x are in the even positions and y in the odd;
unsigned int z;   // z gets the resulting 32-bit Morton Number.

z = MortonTable256[y >> 8]   << 17 |
    MortonTable256[x >> 8]   << 16 |
    MortonTable256[y & 0xFF] <<  1 |
    MortonTable256[x & 0xFF];

For more speed, use an additional table with values that are MortonTable256 pre-shifted one bit to the left. This second table could then be used for the y lookups, thus reducing the operations by two, but almost doubling the memory required. Extending this same idea, four tables could be used, with two of them pre-shifted by 16 to the left of the previous two, so that we would only need 11 operations total.
Interleave bits with 64-bit multiply
In 11 operations, this version interleaves bits of two bytes (rather than shorts, as in the other versions), but many of the operations are 64-bit multiplies so it isn't appropriate for all machines. The input parameters, x and y, should be less than 256.
unsigned char x;  // Interleave bits of (8-bit) x and y, so that all of the
unsigned char y;  // bits of x are in the even positions and y in the odd;
unsigned short z; // z gets the resulting 16-bit Morton Number.

z = ((x * 0x0101010101010101ULL & 0x8040201008040201ULL) *
     0x0102040810204081ULL >> 49) & 0x5555 |
    ((y * 0x0101010101010101ULL & 0x8040201008040201ULL) *
     0x0102040810204081ULL >> 48) & 0xAAAA;
Holger Bettag was inspired to suggest this technique on October 10, 2004 after reading the multiply-based bit reversals here.
Interleave bits by Binary Magic Numbers
static const unsigned int B[] = {0x55555555, 0x33333333, 0x0F0F0F0F, 0x00FF00FF};
static const unsigned int S[] = {1, 2, 4, 8};

unsigned int x; // Interleave lower 16 bits of x and y, so the bits of x
unsigned int y; // are in the even positions and bits from y in the odd;
unsigned int z; // z gets the resulting 32-bit Morton Number.
                // x and y must initially be less than 65536.

x = (x | (x << S[3])) & B[3];
x = (x | (x << S[2])) & B[2];
x = (x | (x << S[1])) & B[1];
x = (x | (x << S[0])) & B[0];

y = (y | (y << S[3])) & B[3];
y = (y | (y << S[2])) & B[2];
y = (y | (y << S[1])) & B[1];
y = (y | (y << S[0])) & B[0];

z = x | (y << 1);

> unrank : (Show a, Eq a) => a -> Int -> BinaryTree a
> unrank a 0 = BLeaf a
> unrank a n =
>   let (ln,rn) = splitnum (n - 1)
>   in  BNode (unrank a (assert_smaller n ln)) (unrank a (assert_smaller n rn))

> rank : (Show a, Eq a) => BinaryTree a -> Int
> rank (BLeaf a) = 0
> rank (BNode l r) = 1 + combnum (rank l) (rank r)

-- > splitReverseComb : {l,r,n: Int} -> (combnum l r = n) <-> ((l,r) = splitnum n)
-- > splitReverseComb = (believe_me, believe_me)

==== Rank and unrank version with Nat for proofs

> evenNat : (n:Nat) -> Bool
> evenNat Z     = True
> evenNat (S Z) = False
> evenNat (S (S k)) = evenNat k

> splitnumNat : Nat -> (Nat,Nat)
> splitnumNat Z = (Z, Z)
> splitnumNat (S n) =
>   let (left',right') = splitnumNat (assert_smaller (S n) (divNatNZ (S n) 4 SIsNotZ))
>       left'' = if evenNat (divNatNZ (S n) 2 SIsNotZ)
>                   then left' * 2
>                   else S (left' * 2)
>       right'' = if evenNat (S n)
>                   then right' * 2
>                   else S (right' * 2)
>   in (left'', right'')

> splitnumNatLeft : Nat -> Nat
> splitnumNatLeft Z = Z
> splitnumNatLeft (S n) =
>   let left' = splitnumNatLeft (assert_smaller (S n) (divNatNZ (S n) 4 SIsNotZ))
>       left'' = if evenNat (divNatNZ (S n) 2 SIsNotZ)
>                   then left' * 2
>                   else S (left' * 2)
>   in left''

> splitnumNatRight : Nat -> Nat
> splitnumNatRight Z = Z
> splitnumNatRight (S n) =
>   let right' = splitnumNatRight (assert_smaller (S n) (divNatNZ (S n) 4 SIsNotZ))
>       right'' = if evenNat (S n)
>                   then right' * 2
>                   else S (right' * 2)
>   in right''

> combnumNat : Nat -> Nat -> Nat
> combnumNat Z Z = Z
> combnumNat Z (S r) =
>   let res = combnumNat Z (assert_smaller (S r) (divNatNZ (S r) 2 SIsNotZ))
>       res2 = if evenNat (S r)
>                 then 4 * res
>                 else (S (2 *res))
>   in res2
> combnumNat (S l) Z =
>   let res = combnumNat (assert_smaller (S l) (divNatNZ (S l) 2 SIsNotZ)) Z
>       res2 = if evenNat (S l)
>                 then 2 * res
>                 else (S (4 *res))
>   in 2 * res2
> combnumNat (S l) (S r) =
>   let res = combnumNat
>                 (assert_smaller (S l) (divNatNZ (S l) 2 SIsNotZ))
>                 (assert_smaller (S r) (divNatNZ (S r) 2 SIsNotZ))
>       res2 = if evenNat (S l)
>                 then 2 * res
>                 else (S (2 *res))
>       res3 = if evenNat (S r)
>                 then 2 * res2
>                 else (S (2 *res2))
>   in res3

> unrankNat : (Show a, Eq a) => a -> Nat -> BinaryTree a
> unrankNat a Z = BLeaf a
> unrankNat a (S n) =
>   BNode (unrankNat a (assert_smaller (S n) (splitnumNatLeft n)))
>         (unrankNat a (assert_smaller (S n) (splitnumNatRight n)))

> rankNat : (Show a, Eq a) => BinaryTree a -> Nat
> rankNat (BLeaf a) = Z
> rankNat (BNode l r) = S (combnumNat (rankNat l) (rankNat r))

==== Properties and proofs

> lemmaCombnumInjectiveL : {a,b,c,d : Nat} -> combnumNat a b = combnumNat c d -> a = c
> lemmaCombnumInjectiveL = believe_me

> lemmaCombnumInjectiveR : {a,b,c,d : Nat} -> combnumNat a b = combnumNat c d -> b = d
> lemmaCombnumInjectiveR = believe_me

-- > lemmaBijective : Bijective BinaryTree.splitnumNat {dty=Nat} {cty=(Nat,Nat)} {x} {y}
-- > lemmaBijective = ((\ p => BinaryTree.combnumNat (fst p) (snd p)) ** ?lemmaBijective_rhs)

==== Basic theorems

> rankInjective : Injective {dty=BinaryTree Unit} BinaryTree.rankNat {x1} {x2}
> rankInjective {x1 = BLeaf ()} {x2 = BLeaf ()} Refl = Refl
> rankInjective {x1 = BLeaf ()} {x2 = BNode l r} Refl impossible
> rankInjective {x1 = BNode l r} {x2 = BLeaf ()} Refl impossible
> rankInjective {x1 = BNode l1 r1} {x2 = BNode l2 r2} hyp =
>   let h1 = lemmaCombnumInjectiveL {b=rankNat r1} {d=rankNat r2} (succInjective _ _ hyp)
>       h2 = lemmaCombnumInjectiveR {a=rankNat l1} {c=rankNat l2} (succInjective _ _ hyp)
>       indHypL = rankInjective {x1=l1} {x2=l2} h1
>       indHypR = rankInjective {x1=r1} {x2=r2} h2
>   in rewrite indHypL in rewrite indHypR in Refl

> rankSurjective : Surjective {dty = BinaryTree Unit} BinaryTree.rankNat {x}
> rankSurjective {x=BLeaf ()} = (Z ** Refl)
> rankSurjective {x=BNode l r} =
>   let (nl ** hypl) = rankSurjective {x=l}
>       (nr ** hypr) = rankSurjective {x=r}
>   in (S (combnumNat nl nr) ** rewrite hypl in rewrite hypr in Refl)

-- > lemmaUnrankInjective : (n,n' : Nat) ->
-- >   (unrankNat () (splitnumNatLeft n) = unrankNat () (splitnumNatLeft n'),
-- >    unrankNat () (splitnumNatRight n) = unrankNat () (splitnumNatRight n')) ->
-- >       unrankNat () n = unrankNat () n'
-- > lemmaUnrankInjective Z Z (hypL,hypR) = Refl
-- > lemmaUnrankInjective _ _ (hypL,hypR) = ?lemmaUnrankInjective_rhs
--
-- > unrankInjective : Injective (unrankNat ()) {x1} {x2}
-- > unrankInjective {x1 = Z} {x2 = Z} Refl = Refl
-- > unrankInjective {x1 = Z} {x2 = S n} hyp = absurd hyp
-- > unrankInjective {x1 = S n} {x2 = Z} hyp = absurd hyp
-- >    -- TODO Report: negEqSym don't typecheck because of constraint problem
-- > unrankInjective {x1 = S n} {x2 = S n'} hyp =
-- >   let h = ?unrankInjective_rhs
-- >       indHyp = unrankInjective {x1=n} {x2=n'} h
-- >   in  eqSucc n n' indHyp

-- > unrankSurjective : (n : Nat) -> (b : BinaryTree Unit ** b = unrankNat () n)
-- > unrankSurjective Z = (BLeaf () ** Refl)
-- > unrankSurjective n =
-- >   let (ln,rn) = splitnum n
-- >       (tl ** hypl)    = unrankSurjective (assert_smaller n ln)
-- >       (tr ** hypr)    = unrankSurjective (assert_smaller n rn)
-- >   in (BNode tl tr ** rewrite hypl in rewrite hypr in ?unrankSurjective)


-- > combReversSplit : {n,l,r: Nat} -> l = splitnumNatLeft n -> r = splitnumNatRight n -> combnumNat l r = n
-- > combReversSplit {n=Z} Refl Refl = Refl
-- > combReversSplit {r} {n= S n'} hyp1 hyp2 =
-- >   let l' = splitnumNatLeft n'
-- >       r' = splitnumNatRight n'
-- >       indHyp = combReversSplit {n=n'} {l=l'} {r=r'} Refl Refl
-- >   in rewrite sym indHyp in rewrite hyp1 in rewrite hyp2 in ?hole

-- > lemma : {r,n : Nat} -> (0, r) = splitnumNat n -> (0,S r) = splitnumNat (S n)
-- > lemma {n=Z} Refl = Refl
-- > lemma {r=Z}{n=S Z} Refl impossible
-- > lemma {r=S r'}{n=S n'} hyp =
-- >   let indHyp = lemma {r=r'} {n=n'} _
-- >   in ?holeL
--
-- > splitReversComb : {l,r,n: Nat} -> combnumNat l r = n -> (l,r) = splitnumNat n
-- > splitReversComb {l=Z} {r=Z} Refl = Refl
-- > splitReversComb {l=Z} {r=S r'} hyp =
-- >   let n' = combnumNat Z r'
-- >       indHyp = splitReversComb {l=Z} {r=r'} {n=n'} Refl
-- >   in ?hole
-- > splitReversComb {l=S l'} {r=Z} hyp = ?hole1
-- > splitReversComb {l=S l'} {r=S r'} hyp = ?hole2


-- > ||| To complicated for me to prove, invented Nat variant to (maybe) make proves possible
-- > lemmaSplitnum: {n: Nat} ->  (l,r) = splitnum (cast n) -> (l2, r2) = splitnumNat n -> (cast l, cast r) = (l2, r2)
-- > lemmaCombnum: {l,r: Nat} ->  n = combnum (cast l) (cast r) -> n2 = combnumNat l r -> cast n = n2

==== Tests

> testRank : rank (unrank 0 300) = 300
> testRank = Refl

> exTree : BinaryTree Int
> exTree = BNode (BNode (BLeaf 1) (BLeaf 2))(BNode (BLeaf 3) (BLeaf 4))

> test1 : show BinaryTree.exTree = "1->2->(3->4)"
> test1 = Refl
