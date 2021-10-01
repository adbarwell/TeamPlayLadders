module Rewrite.Show

import public Rewrite.Base

%default total

---------------------------------------------------------------------------------------------------
-- [Show] -----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
implementation Show (ARewrite e f) where
  show SqIsMult = "SqIsMult"
  show (Commutative {op} ok) = "Comm(" ++ show op ++ ")"
  show (Associative {op} ok) = "Asso(" ++ show op ++ ")"

export
implementation Show (Rewrite e f) where
  show Refl = "Refl"
  show (Fun r) = show r
  show (Sym r) = "(Sym (" ++ show r ++ "))"
  show (Trans r s) = show s ++ " . " ++ show r
  show (CongU r) = "CongU( " ++ show r ++ " )"
  show (CongB1 r) = "CongB1( " ++ show r ++ " )"
  show (CongB2 r) = "CongB2( " ++ show r ++ " )"