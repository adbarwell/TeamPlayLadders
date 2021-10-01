module IdrisUtils.Data.Vect

import public Decidable.Equality
import public Data.Vect

import public IdrisUtils.Data.Vect.IsSet

%default total

---------------------------------------------------------------------------------------------------
-- [decEq] --------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
decEqVect : DecEq a => {n,m : Nat} -> (xs : Vect n a) -> (ys : Vect m a) -> Dec (xs = ys)
decEqVect {n} {m} xs ys with (decEq n m)
  decEqVect {n} {m} xs ys | No neq = No (contra neq) where
    contra : {xs' : Vect n' a}
          -> {ys' : Vect m' a}
          -> (neq' : Not (n' = m'))
          -> Not (xs' = ys')
    contra neq' Refl = neq' Refl
  decEqVect {n} {m = n} xs ys | Yes Refl with (decEq xs ys)
    decEqVect {n} {m = n} xs ys | Yes Refl | No neq = No (\Refl => neq Refl)
    decEqVect {n} {m = n} xs xs | Yes Refl | Yes Refl = Yes Refl
