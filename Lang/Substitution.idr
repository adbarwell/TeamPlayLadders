module Lang.Substitution

import public Lang.SubTerm

%default total

---------------------------------------------------------------------------------------------------
-- [Substitution of SubTerm] ----------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| g is the result of substituting subterm st in f for e.
public export
data SubstituteOne : {st : AExp c nvars}
                  -> (e,f,g : AExp c nvars) -> (ptr : SubTerm st f) -> Type where
  MkStRefl : SubstituteOne e e e Refl
  MkStBOLt : (q : SubstituteOne e f1 g p)
          -> SubstituteOne e (BinOp op f1 f2) (BinOp op g f2) (BinOpLeft p)
  MkStBORt : (q : SubstituteOne e f2 g p)
          -> SubstituteOne e (BinOp op f1 f2) (BinOp op f1 g) (BinOpRight p)
  MkStUOTh : (q : SubstituteOne e f g p) -> SubstituteOne e (UniOp op f) (UniOp op g) (UniOpThere p)

||| st is a subterm in e
public export
data SubTermAll : (st,e : AExp c nvars) -> Type where

||| g is the result of substituting all occurrences of subterm st in f for e
public export
data SubstituteAll : {st : AExp c nvars}
                  -> (e,f,g : AExp c nvars) -> (ptr : SubTermAll st f) -> Type where

