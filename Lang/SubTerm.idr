module Lang.SubTerm

import public Lang.Base
import public Lang.Prop.DecEq

%default total

---------------------------------------------------------------------------------------------------
-- [SubTerm] --------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| e is a subterm of f.
public export
data SubTerm : (e,f : AExp c nvars) -> Type where
  Refl : SubTerm e e
  BinOpLeft : SubTerm e f -> SubTerm e (BinOp op f g)
  BinOpRight : SubTerm e g -> SubTerm e (BinOp op f g)
  UniOpThere : SubTerm e f -> SubTerm e (UniOp op f)

---------------------------------------------------------------------------------------------------
-- [Implementations] ------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
implementation Show (SubTerm e f) where
  show Refl = "Refl"
  show (BinOpLeft p) = "BinOpLeft(" ++ show p ++ ")"
  show (BinOpRight p) = "BinOpRight(" ++ show p ++ ")"
  show (UniOpThere p) = "UniOpThere(" ++ show p ++ ")"

export
implementation Uninhabited (SubTerm (Lit n) (Var i)) where
  uninhabited _ impossible
export
implementation Uninhabited (SubTerm (Var i) (Lit n)) where
  uninhabited _ impossible
export
implementation Uninhabited (SubTerm (UniOp _ e) (Lit n)) where
  uninhabited _ impossible
export
implementation Uninhabited (SubTerm (UniOp _ e) (Var i)) where
  uninhabited _ impossible
export
implementation Uninhabited (SubTerm (BinOp _ e f) (Lit n)) where
  uninhabited _ impossible
export
implementation Uninhabited (SubTerm (BinOp _ e f) (Var i)) where
  uninhabited _ impossible

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
reflImpliesEqLit : (p : SubTerm (Lit n) (Lit m)) -> n = m
reflImpliesEqLit Refl = Refl

export
reflImpliesEqVar : (p : SubTerm (Var i) (Var j)) -> i = j
reflImpliesEqVar Refl = Refl

export
decSubTerm : (DecEq c) => (e,f : AExp c nvars) -> Dec (SubTerm e f)
decSubTerm (Lit n) (Lit m) with (decEq n m)
  decSubTerm (Lit n) (Lit m) | No neq = No (\p => neq (reflImpliesEqLit p))
  decSubTerm (Lit n) (Lit n) | Yes Refl = Yes Refl
decSubTerm (Lit n) (Var i) = No absurd
decSubTerm (Var m) (Lit n) = No absurd
decSubTerm (Var m) (Var n) with (decEq m n)
  decSubTerm (Var n) (Var n) | Yes Refl = Yes Refl
  decSubTerm (Var m) (Var n) | No neq = No (\p => neq (reflImpliesEqVar p))
decSubTerm (UniOp op e) (Lit n) = No absurd
decSubTerm (UniOp op e) (Var n) = No absurd
decSubTerm (BinOp _ _ _) (Lit _) = No absurd
decSubTerm (BinOp _ _ _) (Var n) = No absurd
decSubTerm e (UniOp op f) with (decEqAExp decEq e (UniOp op f))
  decSubTerm e (UniOp op f) | Yes eq = Yes (rewrite eq in Refl)
  decSubTerm e (UniOp op f) | No neq with (decSubTerm e f)
    decSubTerm e (UniOp op f) | No neq | Yes p = Yes (UniOpThere p)
    decSubTerm e (UniOp op f) | No neq | No np = No (absurd neq np) where
      absurd : (c1 : Not (e' = (UniOp op' f')))
            -> (c2 : Not (SubTerm e' f'))
            -> Not (SubTerm e' (UniOp op' f'))
      absurd c1 c2 Refl = c1 Refl
      absurd c1 c2 (UniOpThere p) = c2 p
decSubTerm e (BinOp op f g) with (decEqAExp decEq e (BinOp op f g))
  decSubTerm e (BinOp op f g) | Yes eq = Yes (rewrite eq in Refl)
  decSubTerm e (BinOp op f g) | No neq with (decSubTerm e f)
    decSubTerm e (BinOp op f g) | No neq | Yes p = Yes (BinOpLeft p)
    decSubTerm e (BinOp op f g) | No neq | No np with (decSubTerm e g)
      decSubTerm e (BinOp op f g) | No neq | No np | Yes q = Yes (BinOpRight q)
      decSubTerm e (BinOp op f g) | No neq | No np | No nq = No (absurd neq np nq) where
        absurd : (c1 : Not (e' = BinOp op' f' g'))
              -> (c2 : Not (SubTerm e' f'))
              -> (c3 : Not (SubTerm e' g'))
              -> Not (SubTerm e' (BinOp op' f' g'))
        absurd c1 c2 c3 Refl = c1 Refl
        absurd c1 c2 c3 (BinOpLeft p) = c2 p
        absurd c1 c2 c3 (BinOpRight q) = c3 q
