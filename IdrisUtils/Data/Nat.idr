module IdrisUtils.Data.Nat

import public Data.Nat
import public IdrisUtils.Equality

%default total

---------------------------------------------------------------------------------------------------
-- [(Strict) Total Ordering] ----------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Definition] -----------------------------------------------------------------------------------

public export
data LTNat : Nat -> Nat -> Type where
  LTZero : LTNat Z (S k)
  LTSucc : LTNat n m -> LTNat (S n) (S m)

public export
LTNat' : (x,y : Nat) -> Type
LTNat' x y = LTNat x y

public export
GTNat : Nat -> Nat -> Type
GTNat x y = LTNat y x

-- [Uninhabited] ----------------------------------------------------------------------------------

export
implementation Uninhabited (LTNat x Z) where
  uninhabited _ impossible

-- [Asymmetry, Transitivity, and Trichotomy] ------------------------------------------------------

export
asymLTNat : (x,y : Nat) -> LTNat x y -> Not (LTNat y x)
asymLTNat Z (S k) LTZero _ impossible
asymLTNat (S n) (S k) (LTSucc p) (LTSucc q) = asymLTNat n k p q

export
irrLTNat : (x : Nat) -> Not (LTNat x x)
irrLTNat x p = asymLTNat x x p p

export
transLTNat : (x,y,z : Nat) -> LTNat x y -> LTNat y z -> LTNat x z
transLTNat Z (S y) (S z) LTZero (LTSucc q) = LTZero
transLTNat (S x) (S y) (S z) (LTSucc p) (LTSucc q) = LTSucc (transLTNat x y z p q)

||| < on naturals is a congruence
export
congLTNat : LTNat n m -> LTNat (S n) (S m)
congLTNat LTZero = LTSucc LTZero
congLTNat (LTSucc lt) = LTSucc (LTSucc lt)

export
trichoLTNat : (x,y : Nat)
           -> Trichotomy (PropEqSetoid Nat Decidable.Equality.decEq) LTNat' Nat.asymLTNat x y
trichoLTNat Z Z = IsEq Refl
trichoLTNat Z (S y) = IsBinR_xRy LTZero
trichoLTNat (S x) Z = IsBinR_yRx LTZero
trichoLTNat (S x) (S y) with (trichoLTNat x y)
  trichoLTNat (S x) (S x) | IsEq Refl = IsEq Refl
  trichoLTNat (S x) (S y) | IsBinR_xRy lt = IsBinR_xRy (LTSucc lt)
  trichoLTNat (S x) (S y) | IsBinR_yRx gt = IsBinR_yRx (LTSucc gt)

-- [Decision Procedure] ---------------------------------------------------------------------------

export
decLTNat : (x,y : Nat) -> Dec (LTNat x y)
decLTNat Z Z = No absurd
decLTNat Z (S y) = Yes LTZero
decLTNat (S x) Z = No absurd
decLTNat (S x) (S y) with (decLTNat x y)
  decLTNat (S x) (S y) | Yes lt = Yes (LTSucc lt)
  decLTNat (S x) (S y) | No gte = No (\(LTSucc lt) => gte lt)
  
-- [Total Ordering (General Setoid)] --------------------------------------------------------------

public export
StrictTotalOrderingTNat : StrictTotalOrderingT Nat (PropEqSetoid Nat Decidable.Equality.decEq)
StrictTotalOrderingTNat = MkSTOrderingT LTNat' asymLTNat transLTNat trichoLTNat decLTNat

-- [Singleton] ------------------------------------------------------------------------------------

export
singLTNat : (x,y : Nat) -> (p,q : LTNat x y) -> p = q
singLTNat Z (S y) LTZero LTZero = Refl
singLTNat (S x) (S y) (LTSucc p) (LTSucc q) = rewrite (singLTNat x y p q) in Refl

-- [Total Ordering with Singleton] ----------------------------------------------------------------

public export
StrictTotalOrderingSNat : StrictTotalOrderingS Nat (PropEqSetoid Nat Decidable.Equality.decEq)
StrictTotalOrderingSNat = MkSTOrderingS StrictTotalOrderingTNat singLTNat

-- [Total Ordering] -------------------------------------------------------------------------------

public export
StrictTotalOrderingNat : StrictTotalOrdering Nat
StrictTotalOrderingNat = MkSTOrdering Decidable.Equality.decEq StrictTotalOrderingSNat

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data IsZero : Nat -> Type where
  ItIsZero : IsZero Z

export
implementation Uninhabited (IsZero (S k)) where
  uninhabited ItIsZero impossible

export
decIsZero : (k : Nat) -> Dec (IsZero k)
decIsZero Z     = Yes ItIsZero
decIsZero (S k) = No absurd

public export
data IsOne : Nat -> Type where
  ItIsOne : IsOne (S Z)

export
implementation Uninhabited (IsOne Z) where
  uninhabited _ impossible
export
implementation Uninhabited (IsOne (S (S k))) where
  uninhabited _ impossible

export
decIsOne : (k : Nat) -> Dec (IsOne k)
decIsOne Z         = No absurd
decIsOne (S Z)     = Yes ItIsOne
decIsOne (S (S k)) = No absurd

export
fromIntegerNat : Integer -> Nat
fromIntegerNat x = ifThenElse (intToBool (prim__eq_Integer x 0))
                              Z (S (fromInteger (prim__sub_Integer x 1)))

-- [Decidability (Prelude.Nat.LTE)] ---------------------------------------------------------------

export
soundLTNat : (x, y : Nat) -> (LTNat x y) -> Not (LTE y x)
soundLTNat Z (S y) LTZero p = absurd p
soundLTNat (S x) (S y) (LTSucc lt) (LTESucc lte) = soundLTNat x y lt lte

export
soundLTE : (x,y : Nat) -> (LTE y x) -> Not (LTNat x y)
soundLTE x Z LTEZero p = absurd p
soundLTE (S x) (S y) (LTESucc lte) (LTSucc lt) = soundLTE x y lte lt

public export
PropNat : (x,y : Nat) -> Prop
PropNat x y = MkProp (LTNat x y) (LTE y x)
                     (decLTNat x y) (isLTE y x)
                     (soundLTNat x y) (soundLTE x y)

export
decPLTNat : (x,y : Nat) -> PDec (PropNat x y)
decPLTNat Z Z = No LTEZero
decPLTNat (S x) Z = No LTEZero
decPLTNat Z (S y) = Yes LTZero
decPLTNat (S x) (S y) with (decPLTNat x y)
  decPLTNat (S x) (S y) | Yes p = Yes (LTSucc p)
  decPLTNat (S x) (S y) | No  q = No (LTESucc q)

public export
DecidableNat : (x,y : Nat) -> Decidable (PropNat x y)
DecidableNat x y = IsDecidable (decPLTNat x y)

-- [Decidability (StrictTotalOrder)] --------------------------------------------------------------

export
implementation StrictTotalOrder Nat where
  theOrder = StrictTotalOrderingNat

export
implementation DecPLT Nat where
  lt_sound LTZero (Ord.IsLT _) impossible
  lt_sound {x = S x} (LTSucc p) IsEq = asymLTNat x x p p
  lt_sound {x = S x} {y = S y} (LTSucc p) (IsLT (LTSucc q)) = asymLTNat x y p q

  gte_sound {x = x} IsEq q = asymLTNat x x q q
  gte_sound {x = x} {y = y} (IsLT p) q = asymLTNat x y q p
