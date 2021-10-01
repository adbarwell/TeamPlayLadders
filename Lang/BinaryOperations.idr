module Lang.BinaryOperations

import public IdrisUtils.Ord

%default total

---------------------------------------------------------------------------------------------------
-- [Syntax] ---------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data BOp : Type where
  Plus  : BOp
  Mult  : BOp

---------------------------------------------------------------------------------------------------
-- [DecEq Implementations] ------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
implementation Uninhabited (Plus = Mult) where
  uninhabited Refl impossible

export
decEqBOp : (x,y : BOp) -> Dec (x = y)
decEqBOp Plus Plus   = Yes Refl
decEqBOp Mult Mult   = Yes Refl
decEqBOp Plus Mult   = No absurd
decEqBOp Mult Plus   = No (\eq => absurd (sym eq))

export
implementation Equality.DecEq BOp where
  decEq = decEqBOp

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data IsCommutative : (op : BOp) -> Type where
  PlusIsComm : IsCommutative Plus
  MultIsComm : IsCommutative Mult

export
decIsCommutative : (op : BOp) -> Dec (IsCommutative op)
decIsCommutative Plus = Yes PlusIsComm
decIsCommutative Mult = Yes MultIsComm

public export
data IsAssociative : (op : BOp) -> Type where
  PlusIsAssoc : IsAssociative Plus
  MultIsAssoc : IsAssociative Mult

export
decIsAssociative : (op : BOp) -> Dec (IsAssociative op)
decIsAssociative Plus = Yes PlusIsAssoc
decIsAssociative Mult = Yes MultIsAssoc

||| f distributes over g
public export
data IsDistributive : (f : BOp) -> (g : BOp) -> Type where
  MultDistOverPlus : IsDistributive Mult Plus

export
implementation Uninhabited (IsDistributive op op) where
  uninhabited MultDistOverPlus impossible
export
implementation Uninhabited (IsDistributive Plus Mult) where
  uninhabited MultDistOverPlus impossible

export
decIsDistributive : (f : BOp) -> (g : BOp) -> Dec (IsDistributive f g)
decIsDistributive Plus Plus = No absurd
decIsDistributive Plus Mult = No absurd
decIsDistributive Mult Plus = Yes MultDistOverPlus
decIsDistributive Mult Mult = No absurd

---------------------------------------------------------------------------------------------------
-- [Total Ordering] -------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data LTBOp : (x,y : BOp) -> Type where
  PlusLTMult  : LTBOp Plus Mult

-- [Decision Procedure] ---------------------------------------------------------------------------

export
implementation Uninhabited (LTBOp x x) where
  uninhabited PlusLTMult  impossible
export
implementation Uninhabited (LTBOp Mult Plus) where
  uninhabited PlusLTMult  impossible

export
decLTBOp : (x,y : BOp) -> Dec (LTBOp x y)
decLTBOp Plus  Plus  = No absurd
decLTBOp Plus  Mult  = Yes PlusLTMult
decLTBOp Mult  Plus  = No absurd
decLTBOp Mult  Mult  = No absurd

-- [Singleton] ------------------------------------------------------------------------------------

export
singLTBOp : (x,y : BOp) -> (p,q : LTBOp x y) -> p = q
singLTBOp Plus Mult PlusLTMult PlusLTMult = Refl

-- [Asymmetry] ------------------------------------------------------------------------------------

export
asymLTBOp : (x,y : BOp) -> (p : LTBOp x y) -> Not (LTBOp y x)
asymLTBOp Plus Mult PlusLTMult q = absurd q

export
irrLTBOp : (x : BOp) -> Not (LTBOp x x)
irrLTBOp x p = asymLTBOp x x p p

-- [Transitivity] ---------------------------------------------------------------------------------

export
transLTBOp : (x,y,z : BOp) -> (p : LTBOp x y) -> (q : LTBOp y z) -> LTBOp x z
transLTBOp Plus Mult Mult PlusLTMult _ impossible

-- [Trichotomy] -----------------------------------------------------------------------------------

trichoLTBOp : (x,y : BOp)
          -> Trichotomy (PropEqSetoid BOp BinaryOperations.decEqBOp) LTBOp
                        BinaryOperations.asymLTBOp x y
trichoLTBOp Plus Plus = IsEq Refl
trichoLTBOp Plus Mult = IsBinR_xRy PlusLTMult
trichoLTBOp Mult Plus = IsBinR_yRx PlusLTMult
trichoLTBOp Mult Mult = IsEq Refl

-- [TotalOrdering] --------------------------------------------------------------------------------

export
StrictTotalOrderingBOp : StrictTotalOrdering BOp
StrictTotalOrderingBOp =
  MkSTOrdering decEqBOp
               (MkSTOrderingS (MkSTOrderingT LTBOp asymLTBOp transLTBOp trichoLTBOp decLTBOp)    
                              singLTBOp)

export
implementation StrictTotalOrder BOp where
  theOrder = StrictTotalOrderingBOp

---------------------------------------------------------------------------------------------------
-- [Implementations] ------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
implementation Eq BOp where
  e == f with (decEqBOp e f)
    e == e | Yes Refl = True
    e == f | No _ = False

export
implementation Show BOp where
  show Plus = "+"
  show Mult = "*"
