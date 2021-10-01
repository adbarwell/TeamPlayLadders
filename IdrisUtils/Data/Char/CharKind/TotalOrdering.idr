module IdrisUtils.Data.Char.CharKind.TotalOrdering

import public IdrisUtils.Data.Nat
import public IdrisUtils.Data.Char.CharKind.Base
-- import public IdrisUtils.Ord

%default total

---------------------------------------------------------------------------------------------------
-- [Total Orders] ---------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Definition] -----------------------------------------------------------------------------------

public export
data LTCharKind : (x : CharKind) -> (y : CharKind) -> Type where
  LTSymNum : LTCharKind Sym Num
  LTSymMin : LTCharKind Sym (Min _)
  LTSymMaj : LTCharKind Sym (Maj _)
  LTNumMin : LTCharKind Num (Min _)
  LTNumMaj : LTCharKind Num (Maj _)
  LTMinMin : LTNat n m -> LTCharKind (Min n) (Min m)
  LTMinMaj : LTCharKind (Min _) (Maj _)
  LTMajMaj : LTNat n m -> LTCharKind (Maj n) (Maj m)

public export
LTCharKind' : (x,y : CharKind) -> Type
LTCharKind' x y = LTCharKind x y

-- [Uninhabited] ----------------------------------------------------------------------------------

export
implementation Uninhabited (LTCharKind Num Sym) where
  uninhabited _ impossible
export
implementation Uninhabited (LTCharKind (Min _) Sym) where
  uninhabited _ impossible
export
implementation Uninhabited (LTCharKind (Maj _) Sym) where
  uninhabited _ impossible
export
implementation Uninhabited (LTCharKind (Min _) Num) where
  uninhabited _ impossible
export
implementation Uninhabited (LTCharKind (Maj _) Num) where
  uninhabited _ impossible
export
implementation Uninhabited (LTCharKind (Maj _) (Min _)) where
  uninhabited _ impossible

-- [Asymmetry, Transitivity, and Trichotomy] -------------------------------------------------------

export
asymLTCharKind : (x,y : CharKind) -> LTCharKind x y -> Not (LTCharKind y x)
asymLTCharKind Sym Num LTSymNum q = absurd q
asymLTCharKind Sym (Min y) LTSymMin q = absurd q
asymLTCharKind Sym (Maj y) LTSymMaj q = absurd q
asymLTCharKind Num (Min y) LTNumMin q = absurd q
asymLTCharKind Num (Maj y) LTNumMaj q = absurd q
asymLTCharKind (Min x) (Min y) (LTMinMin p) (LTMinMin q) = asymLTNat x y p q
asymLTCharKind (Min x) (Maj y) LTMinMaj q = absurd q
asymLTCharKind (Maj x) (Maj y) (LTMajMaj p) (LTMajMaj q) = asymLTNat x y p q

export
irrLTCharKind : (x : CharKind) -> Not (LTCharKind x x)
irrLTCharKind x p = asymLTCharKind x x p p

export
transLTCharKind : (x,y,z : CharKind)
               -> LTCharKind x y -> LTCharKind y z -> LTCharKind x z
transLTCharKind Sym Num (Min z) LTSymNum LTNumMin = LTSymMin
transLTCharKind Sym Num (Maj z) LTSymNum LTNumMaj = LTSymMaj
transLTCharKind Sym (Min y) (Min z) LTSymMin (LTMinMin q) = LTSymMin
transLTCharKind Sym (Min y) (Maj z) LTSymMin LTMinMaj = LTSymMaj
transLTCharKind Sym (Maj y) (Maj z) LTSymMaj (LTMajMaj _) = LTSymMaj
transLTCharKind Num (Min y) (Min z) LTNumMin (LTMinMin q) = LTNumMin
transLTCharKind Num (Min y) (Maj z) LTNumMin LTMinMaj = LTNumMaj
transLTCharKind Num (Maj y) (Maj z) LTNumMaj (LTMajMaj q) = LTNumMaj
transLTCharKind (Min x) (Min y) (Min z) (LTMinMin p) (LTMinMin q) =
  LTMinMin (transLTNat x y z p q)
transLTCharKind (Min x) (Min y) (Maj z) (LTMinMin p) LTMinMaj = LTMinMaj
transLTCharKind (Min x) (Maj y) (Maj z) LTMinMaj (LTMajMaj q) = LTMinMaj
transLTCharKind (Maj x) (Maj y) (Maj z) (LTMajMaj p) (LTMajMaj q) =
  LTMajMaj (transLTNat x y z p q)

export
trichoLTCharKind : (x,y : CharKind)
                -> Trichotomy (PropEqSetoid CharKind Base.decEqCharKind)
                              LTCharKind' TotalOrdering.asymLTCharKind x y
trichoLTCharKind Sym Sym = IsEq Refl
trichoLTCharKind Sym Num = IsBinR_xRy LTSymNum
trichoLTCharKind Sym (Min y) = IsBinR_xRy LTSymMin
trichoLTCharKind Sym (Maj y) = IsBinR_xRy LTSymMaj
trichoLTCharKind Num Sym = IsBinR_yRx LTSymNum
trichoLTCharKind Num Num = IsEq Refl
trichoLTCharKind Num (Min y) = IsBinR_xRy LTNumMin
trichoLTCharKind Num (Maj y) = IsBinR_xRy LTNumMaj
trichoLTCharKind (Min x) Sym = IsBinR_yRx LTSymMin
trichoLTCharKind (Min x) Num = IsBinR_yRx LTNumMin
trichoLTCharKind (Min x) (Min y) with (trichoLTNat x y)
  trichoLTCharKind (Min x) (Min x) | IsEq Refl = IsEq Refl
  trichoLTCharKind (Min x) (Min y) | IsBinR_xRy p = IsBinR_xRy (LTMinMin p)
  trichoLTCharKind (Min x) (Min y) | IsBinR_yRx q = IsBinR_yRx (LTMinMin q)
trichoLTCharKind (Min x) (Maj y) = IsBinR_xRy LTMinMaj
trichoLTCharKind (Maj x) Sym = IsBinR_yRx LTSymMaj
trichoLTCharKind (Maj x) Num = IsBinR_yRx LTNumMaj
trichoLTCharKind (Maj x) (Min y) = IsBinR_yRx LTMinMaj
trichoLTCharKind (Maj x) (Maj y) with (trichoLTNat x y)
  trichoLTCharKind (Maj x) (Maj x) | IsEq Refl = IsEq Refl
  trichoLTCharKind (Maj x) (Maj y) | IsBinR_xRy p = IsBinR_xRy (LTMajMaj p)
  trichoLTCharKind (Maj x) (Maj y) | IsBinR_yRx q = IsBinR_yRx (LTMajMaj q)

-- [Decision Procedure] ---------------------------------------------------------------------------

export
decLTCharKind : (x,y : CharKind) -> Dec (LTCharKind x y)
decLTCharKind x y with (trichoLTCharKind x y)
  decLTCharKind x x | IsEq Refl = No (irrLTCharKind x)
  decLTCharKind x y | IsBinR_xRy p = Yes p
  decLTCharKind x y | IsBinR_yRx q = No (asymLTCharKind y x q)

-- [Total Ordering (General Setoid)] --------------------------------------------------------------

public export
StrictTotalOrderingTCharKind : StrictTotalOrderingT CharKind
                                                    (PropEqSetoid CharKind Base.decEqCharKind)
StrictTotalOrderingTCharKind =
  MkSTOrderingT LTCharKind' asymLTCharKind transLTCharKind trichoLTCharKind decLTCharKind

-- [Singleton] ------------------------------------------------------------------------------------

export
singLTCharKind : (x,y : CharKind) -> (p,q : LTCharKind x y) -> p = q
singLTCharKind Sym Num LTSymNum LTSymNum = Refl
singLTCharKind Sym (Min y) LTSymMin LTSymMin = Refl
singLTCharKind Sym (Maj y) LTSymMaj LTSymMaj = Refl
singLTCharKind Num (Min y) LTNumMin LTNumMin = Refl
singLTCharKind Num (Maj y) LTNumMaj LTNumMaj = Refl
singLTCharKind (Min x) (Min y) (LTMinMin p) (LTMinMin q) = rewrite (singLTNat x y p q) in Refl
singLTCharKind (Min x) (Maj y) LTMinMaj LTMinMaj = Refl
singLTCharKind (Maj x) (Maj y) (LTMajMaj p) (LTMajMaj q) = rewrite (singLTNat x y p q) in Refl

-- [Total Ordering with Singleton] ----------------------------------------------------------------

public export
StrictTotalOrderingSCharKind : StrictTotalOrderingS CharKind
                                                      (PropEqSetoid CharKind Base.decEqCharKind)
StrictTotalOrderingSCharKind = MkSTOrderingS StrictTotalOrderingTCharKind singLTCharKind

-- [Total Ordering] -------------------------------------------------------------------------------

public export
StrictTotalOrderingCharKind : StrictTotalOrdering CharKind
StrictTotalOrderingCharKind = MkSTOrdering Base.decEqCharKind StrictTotalOrderingSCharKind
