module IdrisUtils.Data.Vect.IsSet

import public Data.Vect
import public IdrisUtils.Data.Vect.Elem

%default total

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Proof that a given vector has no duplicate (totally ordered) elements.
public export
data IsSet : {ord : StrictTotalOrdering c} -> (xs : Vect n c) -> Type where
  Nil  : IsSet []
  (::) : (here : NotElem {ord} x xs) -> (there : IsSet {ord} xs) -> IsSet {ord} (x :: xs)

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
decIsSet : {ord : StrictTotalOrdering c} -> (xs : Vect n c) -> Dec (IsSet {ord} xs)
decIsSet [] = Yes []
decIsSet {ord} (x :: xs) with (decNotElem {ord=ord} x xs)
  decIsSet (x :: xs) | No later = No (\(nlater :: _) => later nlater)
  decIsSet (x :: xs) | Yes nLater with (decIsSet {ord} xs)
    decIsSet (x :: xs) | Yes nLater | No nset = No (\(_ :: set) => nset set)
    decIsSet (x :: xs) | Yes nLater | Yes set = Yes (nLater :: set)

export
singIsSet : {xs : Vect n c} -> (p,q : IsSet xs) -> p = q
singIsSet [] [] = Refl
singIsSet {xs=(x :: xs)} (p :: ps) (q :: qs) =
  rewrite singIsSet ps qs in replace {p=(\x => p :: qs = x :: qs)} (singNotElem x xs p q) Refl
