module IdrisUtils.Maybe

%default total

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data Certainly : (m : Maybe a) -> (x : a) -> Type where
  MkCertainly : Certainly (Just x) x

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

injectiveCertainly : (m : Maybe a) -> (x,y : a)
                         -> (p : Certainly m x) -> (q : Certainly m y)
                         -> x = y
injectiveCertainly (Just z) z z MkCertainly MkCertainly = Refl

singletonCertainly : (m : Maybe a) -> (x : a)
                  -> (p : Certainly m x) -> (q : Certainly m x) -> p = q
singletonCertainly (Just x) x MkCertainly MkCertainly = Refl
