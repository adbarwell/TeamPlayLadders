module Lang.Prop

import public Lang.Prop.DecEq
-- import public Lang.Prop.TotalOrdering -- why do we need this again...?

%default total

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data IsMult : AExp c nvars -> Type where
  ItIsMult : IsMult (BinOp Mult e f)

