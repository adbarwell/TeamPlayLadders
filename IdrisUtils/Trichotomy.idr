module IdrisUtils.Trichotomy

import public IdrisUtils.Setoid

%default total

---------------------------------------------------------------------------------------------------
-- [Definition] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| 'A binary relation R on a set X is trichotomous if for all x and y in X, exactly one of
||| xRy, yRx, and x = y holds.'
|||
public export
data Trichotomy : (setoid : SetoidT c)
               -> (binR : c -> c -> Type)
               -> (asym : (x,y : c) -> binR x y -> Not (binR y x))
               -> (x, y : c)
               -> Type where
  IsEq       : (eq : eqR set x y) -> Trichotomy set binR asym x y
  IsBinR_xRy : {binR : c -> c -> Type} -> {asym : (x,y : c) -> binR x y -> Not (binR y x)}
            -> (prf : binR x y)
            -> Trichotomy set binR asym x y
  IsBinR_yRx : {binR : c -> c -> Type} -> {asym : (x,y : c) -> binR x y -> Not (binR y x)}
            -> (prf : binR y x)
            -> Trichotomy set binR asym x y

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
