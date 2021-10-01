module Lang.Base

import public IdrisUtils.Data.String.PString

import public Lang.BinaryOperations
import public Lang.UnaryOperations


%default total

---------------------------------------------------------------------------------------------------
-- [Syntax] ---------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data AExp : (c : Type) -> (nvars : Nat) -> Type where
  Lit : (n : c) -> AExp c nvars
  Var : (x : Fin nvars) -> AExp c nvars
  BinOp : (op : BOp) -> (e1,e2 : AExp c nvars) -> AExp c nvars
  UniOp : (op : UOp) -> (e1 : AExp c nvars) -> AExp c nvars


--------------------------------------------------------------------------------------------------
-- [Implementations] ------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
implementation Show c => Show (AExp c nvars) where
  show (Lit n) = show n
  show (Var x) = "a" ++ show (finToNat x)
  show (BinOp op x y) = "(" ++ show x ++ " " ++ show op ++ " " ++ show y ++ ")"
  show (UniOp op x) = show op ++ "(" ++ show x ++ ")"

export
getVars : AExp c nvars -> List String -> List String 
getVars (Lit n) l = l
getVars (Var x) l = ("a" ++ show (finToNat x)) :: l
getVars (BinOp op x y) l = 
  case getVars x l of
    l' => getVars y l'
getVars (UniOp op x) l = getVars x l