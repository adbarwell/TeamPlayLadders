module IdrisUtils.Data.Integer.SInt.Base

import public Decidable.Equality

import public IdrisUtils.Data.Nat
import public IdrisUtils.Data.Integer.Sign

%default total

---------------------------------------------------------------------------------------------------
-- [Definition] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Agda-style integers.
public export
data SInt : Type where
  ||| +n
  Pos : (n : Nat) -> SInt
  ||| -(1+n)
  Neg : (n : Nat)-> SInt

---------------------------------------------------------------------------------------------------
-- [Injectiveness] --------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
posInjective : {0 left, right : Nat} -> (0 p : Pos left = Pos right) -> left = right
posInjective Refl = Refl

export
negInjective : {0 left, right : Nat} -> (0 p : Neg left = Neg right) -> left = right
negInjective Refl = Refl

---------------------------------------------------------------------------------------------------
-- [DecEq] ----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
implementation Uninhabited (Pos x = Neg y) where
  uninhabited Refl impossible

export
decEqSInt : (x,y : SInt) -> Dec (x = y)
decEqSInt (Pos x) (Pos y) with (decEq x y)
  decEqSInt (Pos x) (Pos x) | Yes Refl = Yes Refl
  decEqSInt (Pos x) (Pos y) | No neq = No (\eq => neq (posInjective eq))
decEqSInt (Pos x) (Neg y) = No absurd
decEqSInt (Neg x) (Pos y) = No (\eq => absurd (sym eq))
decEqSInt (Neg x) (Neg y) with (decEq x y)
  decEqSInt (Neg x) (Neg x) | Yes Refl = Yes Refl
  decEqSInt (Neg x) (Neg y) | No neq = No (\eq => neq (negInjective eq))

export
implementation DecEq SInt where
  decEq = decEqSInt

---------------------------------------------------------------------------------------------------
-- [Conversions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
absSInt : SInt -> SInt
absSInt (Pos n) = Pos n
absSInt (Neg n) = (Pos (S n))

public export
absSIntNat : SInt -> Nat
absSIntNat (Pos n) = n
absSIntNat (Neg n) = (S n)

||| Convert an Integer to a SInt.
export
fromIntegerSInt : Integer -> SInt
fromIntegerSInt 0 = Pos Z
fromIntegerSInt n =
  if (n > 0)
    then
      Pos (S (fromIntegerNat (assert_smaller n (n - 1))))
    else
      Neg (fromIntegerNat (assert_smaller n (abs n - 1)))

||| Convert a SInt to an Integer.
public export
toIntegerSInt : SInt -> Integer
toIntegerSInt (Pos n) = natToInteger n
toIntegerSInt (Neg n) = -(natToInteger (S n))

---------------------------------------------------------------------------------------------------
-- [Sign] -----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
sign : SInt -> Sign
sign (Pos n) = Positive
sign (Neg n) = Negative

public export
ctrSInt : Sign -> Nat -> SInt
ctrSInt _ Z = Pos Z
ctrSInt Positive (S n) = Pos (S n)
ctrSInt Negative (S n) = Neg n

public export
ctrSIntLeftInverse : (i : SInt) -> ctrSInt (sign i) (absSIntNat i) = i
ctrSIntLeftInverse (Neg n) = Refl
ctrSIntLeftInverse (Pos Z) = Refl
ctrSIntLeftInverse (Pos (S n)) = Refl

public export
data SignAbs : SInt -> Type where
  MkSignAbs : (s : Sign) -> (n : Nat) -> SignAbs (ctrSInt s n)

public export
signAbs : (i : SInt) -> SignAbs i
signAbs i = rewrite sym (ctrSIntLeftInverse i) in MkSignAbs (sign i) (absSIntNat i)

---------------------------------------------------------------------------------------------------
-- [Basic Arithmetic Operations] ------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Negates an integer.
public export
negate : SInt -> SInt
negate (Pos Z) = Pos Z
negate (Pos (S n)) = Neg n
negate (Neg n) = Pos (S n)

public export
subNat : (x,y : Nat) -> SInt
subNat m Z = Pos m
subNat Z (S m) = Neg m
subNat (S n) (S m) = subNat n m

||| Add two integers.
public export
plus : SInt -> SInt -> SInt
plus (Neg x) (Neg y) = Neg (S (x + y))
plus (Neg x) (Pos y) = subNat y (S x)
plus (Pos x) (Neg y) = subNat x (S y)
plus (Pos x) (Pos y) = Pos (x + y) 

||| Subtract integers. Uses `negate`.
public export
minus : SInt -> SInt -> SInt
minus x y = plus x (negate y)

public export
succ : SInt -> SInt
succ i = plus (Pos (S Z)) i

public export
pred : SInt -> SInt
pred i = plus (Neg Z) i

||| Multiply integers.
public export
mult : SInt -> SInt -> SInt
mult i j = ctrSInt (sign i * sign j) (absSIntNat i * absSIntNat j)

public export
power : SInt -> Nat -> SInt
power base Z = Pos (S Z)
power base (S exp) = mult base (power base exp)

---------------------------------------------------------------------------------------------------
-- [Interface implementations] --------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
implementation Eq SInt where
  (Pos n) == (Pos m) = n == m
  (Neg n) == (Neg m) = n == m
  _ == _ = False

export
implementation Cast SInt Integer where
  cast = toIntegerSInt

export
implementation Cast Integer SInt where
  cast = fromIntegerSInt

export
implementation Cast String SInt where
  cast orig = fromIntegerSInt (cast orig)

export
implementation Ord SInt where
  compare (Pos Z) (Pos Z) = EQ
  compare (Pos Z) (Pos (S m)) = LT
  compare (Pos (S n)) (Pos Z) = GT
  compare (Pos (S n)) (Pos (S m)) = compare n m
  compare (Pos n) (Neg m) = GT
  compare (Neg n) (Pos m) = LT
  compare (Neg n) (Neg m) = compare m n

export
implementation Num SInt where
  (+) = plus
  (*) = mult

  fromInteger = fromIntegerSInt

export
implementation Abs SInt where
  abs = absSInt

export
implementation Neg SInt where
  negate = Base.negate
  (-) = minus

export
implementation Show SInt where
  show (Pos n) = show n
  show (Neg n) = "-" ++ show (S n)

