module IdrisUtils.Data.Integer.SInt.Prop

import public IdrisUtils.Data.Integer.Sign
import public IdrisUtils.Data.Integer.SInt.Base
import public IdrisUtils.Data.Integer.SInt.TotalOrdering
import public IdrisUtils.Algebra.Structures

%default total

---------------------------------------------------------------------------------------------------
-- [Positive Decidability] ------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
implementation DecPLT SInt where
  lt_sound {x = Pos x} (PosLTPos p) IsEq = asymLTNat x x p p
  lt_sound {x = Pos x} {y = Pos y} (PosLTPos p) (IsLT (PosLTPos q)) = asymLTNat x y p q
  lt_sound NegLTPos (Ord.IsLT _) impossible
  lt_sound {x = Neg x} (NegLTNeg p) IsEq = asymLTNat x x p p
  lt_sound {x = Neg x} {y = Neg y} (NegLTNeg p) (IsLT (NegLTNeg q)) = asymLTNat y x p q

  gte_sound {x = x} IsEq q = asymLTSInt x x q q
  gte_sound {x = x} {y = y} (IsLT p) q = asymLTSInt y x p q


---------------------------------------------------------------------------------------------------
-- [Properties of subNat] -------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
subNatSameArgsEqZero : (n : Nat) -> subNat n n = Pos Z
subNatSameArgsEqZero Z = Refl
subNatSameArgsEqZero (S n) = subNatSameArgsEqZero n

---------------------------------------------------------------------------------------------------
-- [Properties of plus] ---------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
plusCommutative : (x,y : SInt) -> x + y = y + x
plusCommutative (Neg x) (Neg y) = rewrite plusCommutative x y in Refl
plusCommutative (Pos x) (Pos y) = rewrite plusCommutative x y in Refl
plusCommutative (Neg x) (Pos y) = Refl
plusCommutative (Pos x) (Neg y) = Refl

export
plusLeftIdentity : (right : SInt) -> Pos Z + right = right
plusLeftIdentity (Pos n) = Refl
plusLeftIdentity (Neg n) = Refl

export
plusRightIdentity : (left : SInt) -> left + (Pos Z) = left
plusRightIdentity (Pos n) = plusRightIdentityPos n where
  plusRightIdentityPos : (left : Nat) -> (Pos left) + (Pos Z) = (Pos left)
  plusRightIdentityPos n = rewrite plusZeroRightNeutral n in Refl
plusRightIdentity (Neg n) = Refl

export
subNatLeftDistribOverPos : (x,y,z : Nat) -> (subNat y z) + (Pos x) = subNat (y + x) z
subNatLeftDistribOverPos _ Z Z = Refl
subNatLeftDistribOverPos _ Z (S _) = Refl
subNatLeftDistribOverPos _ (S _) Z = Refl
subNatLeftDistribOverPos x (S y) (S z) = subNatLeftDistribOverPos x y z

export
subNatLeftDistribOverNeg : (x,y,z : Nat) -> subNat y z + (Neg x) = subNat y (S z + x)
subNatLeftDistribOverNeg _ Z Z = Refl
subNatLeftDistribOverNeg _ Z (S z) = Refl
subNatLeftDistribOverNeg _ (S y) Z = Refl
subNatLeftDistribOverNeg x (S y) (S z) = subNatLeftDistribOverNeg x y z

export
subNatRightDistribOverPos : (x,y,z : Nat) -> (Pos x) + (subNat y z) = subNat (x + y) z
subNatRightDistribOverPos x y z =
  rewrite plusCommutative (Pos x) (subNat y z) in
    rewrite subNatLeftDistribOverPos x y z in
      rewrite plusCommutative y x in Refl

export
subNatRightDistribOverNeg : (x,y,z : Nat) -> (Neg x) + (subNat y z) = subNat y (S x + z)
subNatRightDistribOverNeg x y z =
  rewrite plusCommutative (Neg x) (subNat y z) in
    rewrite subNatLeftDistribOverNeg x y z in
      rewrite plusCommutative z x in Refl

export
plusAssociative : (x,y,z : SInt) -> (x + y) + z = x + (y + z)
plusAssociative (Pos Z) y z =
  rewrite plusLeftIdentity (y + z) in rewrite plusLeftIdentity y in Refl
plusAssociative x (Pos Z) z =
  rewrite plusLeftIdentity z in rewrite plusRightIdentity x in Refl
plusAssociative x y (Pos Z) =
  rewrite plusRightIdentity y in rewrite plusRightIdentity (x + y) in Refl
plusAssociative (Neg x) (Neg y) (Pos (S z)) = sym (subNatRightDistribOverNeg x z y)
plusAssociative (Neg x) (Pos (S y)) (Pos (S z)) = subNatLeftDistribOverPos (S z) y x
plusAssociative (Pos (S x)) (Neg y) (Neg z) = subNatLeftDistribOverNeg z x y
plusAssociative (Pos (S x)) (Neg y) (Pos (S z)) =
  rewrite subNatLeftDistribOverPos (S z) x y in
    rewrite subNatRightDistribOverPos (S x) z y in
      rewrite plusAssociative x (S Z) z in
        rewrite plusCommutative x (S Z) in
          Refl
plusAssociative (Pos (S x)) (Pos (S y)) (Neg z) =
  rewrite subNatRightDistribOverPos (S x) y z in
    rewrite plusAssociative x (S Z) y in
      rewrite plusCommutative x (S Z) in
        Refl
plusAssociative (Neg x) (Neg y) (Neg z) =
  rewrite plusAssociative x (S Z) (y + z) in
    rewrite plusCommutative x (S Z) in
      rewrite sym (plusAssociative x y z) in
        Refl
plusAssociative (Neg x) (Pos (S y)) (Neg z) = 
  rewrite subNatRightDistribOverNeg x y z in
    rewrite subNatLeftDistribOverNeg z y x in
      Refl
plusAssociative (Pos (S x)) (Pos (S y)) (Pos (S z)) =
  rewrite sym (plusAssociative (S x) (S y) (S z)) in Refl

export
plusLeftInverse : (x : SInt) -> x + (negate x) = (Pos Z)
plusLeftInverse (Neg n) = subNatSameArgsEqZero n
plusLeftInverse (Pos Z) = Refl
plusLeftInverse (Pos (S n)) = subNatSameArgsEqZero n

export
plusRightInverse : (x : SInt) -> (negate x) + x = (Pos Z)
plusRightInverse x = rewrite plusCommutative (negate x) x in plusLeftInverse x

-- [Algebraic Structures] -------------------------------------------------------------------------

plusMagma : Magma SInt Base.plus
plusMagma = MkMagma plus

plusSemigroup : Semigroup SInt Base.plus
plusSemigroup = MkSemigroup plusMagma plusAssociative

plusZeroMonoid : Monoid SInt Base.plus (Pos Z)
plusZeroMonoid = MkMonoid plusSemigroup plusLeftIdentity plusRightIdentity

plusZeroGroup : Group SInt Base.plus (Pos Z) Base.negate
plusZeroGroup = MkGroup plusZeroMonoid plusLeftInverse plusRightInverse

plusZeroCommGroup : CommGroup SInt Base.plus (Pos Z) Base.negate
plusZeroCommGroup = MkCommGroup plusZeroGroup plusCommutative

---------------------------------------------------------------------------------------------------
-- [Properties of mult] ---------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
multCommutative : (x,y : SInt) -> x * y = y * x
multCommutative (Neg x) (Neg y) = rewrite multCommutative (S x) (S y) in Refl
multCommutative (Neg x) (Pos y) = rewrite multCommutative (S x) y in Refl
multCommutative (Pos x) (Neg y) = rewrite multCommutative x (S y) in Refl
multCommutative (Pos x) (Pos y) = rewrite multCommutative x y in Refl

export
multLeftIdentity : (x : SInt) -> (Pos (S Z)) * x = x
multLeftIdentity (Neg n) = rewrite plusZeroRightNeutral n in Refl
multLeftIdentity (Pos Z) = Refl
multLeftIdentity (Pos (S n)) = rewrite plusZeroRightNeutral n in Refl

export
multRightIdentity : (x : SInt) -> x * (Pos (S Z)) = x
multRightIdentity x = rewrite multCommutative x (Pos (S Z)) in multLeftIdentity x

export
multLeftZero : (x : SInt) -> (Pos Z) * x = (Pos Z)
multLeftZero n = Refl

export
multRightZero : (x : SInt) -> x * (Pos Z) = (Pos Z)
multRightZero n = rewrite multCommutative n (Pos Z) in multLeftZero n

{-
signPosMult : (x,y : Nat) -> sign (ctrSInt Positive (mult x y)) = Positive
signPosMult Z y = Refl
signPosMult (S x) Z = rewrite multZeroRightZero x in Refl
signPosMult (S x) (S y) = Refl

-- sign y = Positive non-zero
signSameMult : (y : Nat) -> (z : SInt) -> sign (ctrSInt (sign z) (mult (S y) (absSIntNat z))) = sign z
signSameMult y (Pos z) = rewrite signPosMult (S y) z in Refl
signSameMult y (Neg z) = Refl

export
signDistributes : (x,y,z : SInt)
               -> (sign (ctrSInt (sign x * sign y) (mult (absSIntNat x) (absSIntNat y))) * sign z) = (sign x * sign (ctrSInt (sign y * sign z) (mult (absSIntNat y) (absSIntNat z))))
signDistributes (Pos x) (Pos Z) (Pos z) = rewrite signPosMult x Z in Refl
signDistributes (Pos x) (Pos Z) (Neg z) = rewrite signPosMult x Z in ?holeHere5 -- impossible
signDistributes (Pos x) (Pos (S y)) z =
  rewrite signPosMult x (S y) in rewrite signSameMult y z in Refl
signDistributes (Pos x) (Neg y) z = ?holeHere3
signDistributes (Neg x) y z = ?holeHere2
-}

||| Not (yet) implemented because Agda uses a ring solver (+-*-solver) which Idris doesn't have.
|||
||| NB this currently uses a `believe_me`.
export
multAssociative : (x,y,z : SInt) -> (x * y) * z = x * (y * z)
multAssociative x y z = believe_me (Refl {x = x * y * z})

||| Not (yet) implemented because Agda uses a ring solver (+-*-solver) which Idris doesn't have.
|||
||| NB this currently uses a `believe_me`.
export
multRightDistribOverPlus : (x,y,z : SInt) -> (x + y) * z = (x * z) + (y * z)
multRightDistribOverPlus x y z = believe_me (Refl {x = (x + y) * z})

export
multLeftDistribOverPlus : (x,y,z : SInt) -> x * (y + z) = (x * y) + (x * z)
multLeftDistribOverPlus x y z =
  rewrite multCommutative x y in
    rewrite multCommutative x z in
      rewrite multCommutative x (y + z) in
        multRightDistribOverPlus y z x

export
multZeroLeftAbsorb : (x : SInt) -> (Pos Z) * x = (Pos Z)
multZeroLeftAbsorb x = Refl

export
multZeroRightAbsorb : (x : SInt) -> x * (Pos Z) = (Pos Z)
multZeroRightAbsorb x = rewrite multCommutative x (Pos Z) in Refl

-- [Algebraic Structures] -------------------------------------------------------------------------

multMagma : Magma SInt Base.mult
multMagma = MkMagma mult

multSemigroup : Semigroup SInt Base.mult
multSemigroup = MkSemigroup multMagma multAssociative

multOneMonoid : Monoid SInt Base.mult (Pos (S Z))
multOneMonoid = MkMonoid multSemigroup multLeftIdentity multRightIdentity

addMultSemiring : Semiring SInt Base.plus Base.mult (Pos Z) (Pos (S Z))
addMultSemiring =
  MkSemiring plusZeroMonoid plusCommutative multOneMonoid multLeftDistribOverPlus multRightDistribOverPlus multZeroLeftAbsorb multZeroRightAbsorb

addMultRing : Ring SInt Base.plus Base.mult (Pos Z) (Pos (S Z)) Base.negate
addMultRing =
  MkRing plusZeroCommGroup multOneMonoid multLeftDistribOverPlus multRightDistribOverPlus

addMultCommRing : CommRing SInt Base.plus Base.mult (Pos Z) (Pos (S Z)) Base.negate
addMultCommRing = MkCommRing addMultRing multCommutative



