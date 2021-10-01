module Lang.UnaryOperations

import public IdrisUtils.Ord

%default total

---------------------------------------------------------------------------------------------------
-- [Syntax] ---------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data UOp : Type where
  Neg    : UOp
  Square : UOp

---------------------------------------------------------------------------------------------------
-- [DecEq Implementations] ------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
implementation Uninhabited (Neg = Square) where
  uninhabited Refl impossible

export
decEqUOp : (x,y : UOp) -> Dec (x = y)
decEqUOp Neg    Neg    = Yes Refl
decEqUOp Square Square = Yes Refl
decEqUOp Neg    Square = No absurd
decEqUOp Square Neg    = No (\eq => absurd (sym eq))

export
implementation Equality.DecEq UOp where
  decEq = decEqUOp

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------------------
-- [Total Ordering] -------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data LTUOp : (x,y : UOp) -> Type where
  NegLTSquare : LTUOp Neg Square

-- [Decision Procedure] ---------------------------------------------------------------------------

export
implementation Uninhabited (LTUOp x x) where
  uninhabited NegLTSquare impossible
export
implementation Uninhabited (LTUOp Square Neg) where
  uninhabited NegLTSquare impossible

export
decLTUOp : (x,y : UOp) -> Dec (LTUOp x y)
decLTUOp Neg    Neg    = No absurd
decLTUOp Neg    Square = Yes NegLTSquare
decLTUOp Square Neg    = No absurd
decLTUOp Square Square = No absurd

-- [Singleton] ------------------------------------------------------------------------------------

export
singLTUOp : (x,y : UOp) -> (p,q : LTUOp x y) -> p = q
singLTUOp Neg Square NegLTSquare NegLTSquare = Refl

-- [Asymmetry] ------------------------------------------------------------------------------------

export
asymLTUOp : (x,y : UOp) -> (p : LTUOp x y) -> Not (LTUOp y x)
asymLTUOp Neg Square NegLTSquare q = absurd q

export
irrLTUOp : (x : UOp) -> Not (LTUOp x x)
irrLTUOp x p = asymLTUOp x x p p

-- [Transitivity] ---------------------------------------------------------------------------------

export
transLTUOp : (x,y,z : UOp) -> (p : LTUOp x y) -> (q : LTUOp y z) -> LTUOp x z
transLTUOp UnaryOperations.Neg Square Square NegLTSquare _ impossible

-- [Trichotomy] -----------------------------------------------------------------------------------

export
trichoLTUOp : (x,y : UOp)
           -> Trichotomy (PropEqSetoid UOp UnaryOperations.decEqUOp)
                         LTUOp UnaryOperations.asymLTUOp x y
trichoLTUOp Neg Neg = IsEq Refl 
trichoLTUOp Neg Square = IsBinR_xRy NegLTSquare
trichoLTUOp Square Neg = IsBinR_yRx NegLTSquare
trichoLTUOp Square Square = IsEq Refl

-- [TotalOrdering] --------------------------------------------------------------------------------

public export
StrictTotalOrderingUOp : StrictTotalOrdering UOp
StrictTotalOrderingUOp =
  MkSTOrdering decEqUOp (MkSTOrderingS (MkSTOrderingT LTUOp asymLTUOp transLTUOp trichoLTUOp 
                                                      decLTUOp)
                                       singLTUOp)

export
implementation StrictTotalOrder UOp where
  theOrder = StrictTotalOrderingUOp

---------------------------------------------------------------------------------------------------
-- [Implementations] ------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
implementation Eq UOp where
  e == f with (decEqUOp e f)
    e == e | Yes Refl = True
    e == f | No _ = False

export
implementation Show UOp where
  show Neg = "-"
  show Square = "square"
