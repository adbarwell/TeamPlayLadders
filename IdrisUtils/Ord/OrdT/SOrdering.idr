module IdrisUtils.Ord.OrdT.SOrdering

import public Decidable.Equality

%default total

---------------------------------------------------------------------------------------------------
-- [Definition] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Prelude.Interfaces.Ordering sans EQ.
public export
data SOrdering : Type where
  LT : SOrdering
  GT : SOrdering

---------------------------------------------------------------------------------------------------
-- [Implementations] ------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
implementation Uninhabited (SOrdering.LT = SOrdering.GT) where
  uninhabited Refl impossible

export
implementation DecEq SOrdering where
  decEq LT LT = Yes Refl
  decEq GT GT = Yes Refl
  decEq LT GT = No absurd
  decEq GT LT = No (\x => absurd (sym x))
