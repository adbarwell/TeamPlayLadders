module IdrisUtils.All

import public IdrisUtils.Data
import public IdrisUtils.Decidability
import public IdrisUtils.Equality
import public IdrisUtils.Error
import public IdrisUtils.Fin
import public IdrisUtils.Maybe
import public IdrisUtils.Setoid
import public IdrisUtils.Ord
import public IdrisUtils.Trichotomy

%default total

{-
-- [DecEq] ----------------------------------------------------------------------------------------

implementation Uninhabited (Vect.Here = Vect.There later) where
  uninhabited Refl impossible

implementation Equality.DecEq (Elem x xs) where
  decEq Here Here = Yes Refl
  decEq Here (There later) = No absurd
  decEq (There later) Here = No (absurd . sym)
  decEq (There later) (There x) with (decEq later x)
    decEq (There x) (There x) | Yes Refl = Yes Refl
    decEq (There later) (There x) | No c = No (\Refl => c Refl)
-}
