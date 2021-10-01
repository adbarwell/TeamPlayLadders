module IdrisUtils.Data.Integer.SInt.TotalOrdering

import public IdrisUtils.Data.Integer.SInt.Base
import public IdrisUtils.Data.Nat

%default total

---------------------------------------------------------------------------------------------------
-- [(Strict) Total Ordering] ----------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Definition] -----------------------------------------------------------------------------------

public export
data LTSInt : (x,y : SInt) -> Type where
  PosLTPos : (lt : LTNat x y) -> LTSInt (Pos x) (Pos y)
  NegLTNeg : (lt : LTNat y x) -> LTSInt (Neg x) (Neg y)
  NegLTPos : LTSInt (Neg x) (Pos y)

public export
LTSInt' : (x,y : SInt) -> Type
LTSInt' x y = LTSInt x y

-- [Uninhabited] ----------------------------------------------------------------------------------

export
implementation Uninhabited (LTSInt (Pos x) (Neg y)) where
  uninhabited _ impossible

-- [Asymmetry, Transitivity, and Trichotomy] ------------------------------------------------------

export
asymLTSInt : (x,y : SInt) -> LTSInt x y -> Not (LTSInt y x)
asymLTSInt (Pos x) (Pos y) (PosLTPos p) (PosLTPos q) = asymLTNat x y p q
asymLTSInt (Neg x) (Neg y) (NegLTNeg p) (NegLTNeg q) = asymLTNat x y q p

export
irrLTSInt : (x : SInt) -> Not (LTSInt x x)
irrLTSInt x p = asymLTSInt x x p p

export
transLTSInt : (x,y,z : SInt) -> LTSInt x y -> LTSInt y z -> LTSInt x z
transLTSInt (Pos x) (Pos y) (Pos z) (PosLTPos p) (PosLTPos q) =
  PosLTPos (transLTNat x y z p q)
transLTSInt (Neg x) (Pos y) (Pos z) NegLTPos (PosLTPos q) = NegLTPos
transLTSInt (Neg x) (Neg y) (Neg z) (NegLTNeg p) (NegLTNeg q) =
  NegLTNeg (transLTNat z y x q p)
transLTSInt (Neg x) (Neg y) (Pos z) (NegLTNeg p) NegLTPos = NegLTPos

export
trichoLTSInt : (x,y : SInt)
            -> Trichotomy (PropEqSetoid SInt Base.decEqSInt)
                          LTSInt' TotalOrdering.asymLTSInt x y
trichoLTSInt (Pos x) (Pos y) with (trichoLTNat x y)
  trichoLTSInt (Pos x) (Pos x) | IsEq Refl = IsEq Refl
  trichoLTSInt (Pos x) (Pos y) | IsBinR_xRy lt = IsBinR_xRy (PosLTPos lt)
  trichoLTSInt (Pos x) (Pos y) | IsBinR_yRx gt = IsBinR_yRx (PosLTPos gt)
trichoLTSInt (Pos x) (Neg y) = IsBinR_yRx NegLTPos
trichoLTSInt (Neg x) (Pos y) = IsBinR_xRy NegLTPos
trichoLTSInt (Neg x) (Neg y) with (trichoLTNat x y)
  trichoLTSInt (Neg x) (Neg x) | IsEq Refl = IsEq Refl
  trichoLTSInt (Neg x) (Neg y) | IsBinR_xRy lt = IsBinR_yRx (NegLTNeg lt)
  trichoLTSInt (Neg x) (Neg y) | IsBinR_yRx gt = IsBinR_xRy (NegLTNeg gt)

-- [Decision Procedure] ---------------------------------------------------------------------------

export
decLTSInt : (x,y : SInt) -> Dec (LTSInt x y)
decLTSInt (Pos x) (Pos y) with (decLTNat x y)
  decLTSInt (Pos x) (Pos y) | Yes lt = Yes (PosLTPos lt)
  decLTSInt (Pos x) (Pos y) | No gte = No (\(PosLTPos lt) => gte lt)
decLTSInt (Pos x) (Neg y) = No absurd
decLTSInt (Neg x) (Pos y) = Yes NegLTPos
decLTSInt (Neg x) (Neg y) with (decLTNat y x)
  decLTSInt (Neg x) (Neg y) | Yes lt = Yes (NegLTNeg lt)
  decLTSInt (Neg x) (Neg y) | No gte = No (\(NegLTNeg lt) => gte lt)

-- [Total Ordering (General Setoid)] --------------------------------------------------------------

public export
StrictTotalOrderingTSInt : StrictTotalOrderingT SInt (PropEqSetoid SInt Base.decEqSInt)
StrictTotalOrderingTSInt = MkSTOrderingT LTSInt' asymLTSInt transLTSInt trichoLTSInt decLTSInt

-- [Singleton] ------------------------------------------------------------------------------------

export
singLTSInt : (x,y : SInt) -> (p,q : LTSInt x y) -> p = q
singLTSInt (Pos x) (Pos y) (PosLTPos p) (PosLTPos q) = rewrite (singLTNat x y p q) in Refl
singLTSInt (Neg x) (Pos y) NegLTPos NegLTPos = Refl
singLTSInt (Neg x) (Neg y) (NegLTNeg p) (NegLTNeg q) = rewrite (singLTNat y x p q) in Refl

-- [Total Ordering with Singleton] ----------------------------------------------------------------

public export
StrictTotalOrderingSSInt : StrictTotalOrderingS SInt (PropEqSetoid SInt Base.decEqSInt)
StrictTotalOrderingSSInt = MkSTOrderingS StrictTotalOrderingTSInt singLTSInt

-- [Total Ordering] -------------------------------------------------------------------------------

public export
StrictTotalOrderingSInt : StrictTotalOrdering SInt
StrictTotalOrderingSInt = MkSTOrdering decEqSInt StrictTotalOrderingSSInt

export
implementation StrictTotalOrder SInt where
  theOrder = StrictTotalOrderingSInt

