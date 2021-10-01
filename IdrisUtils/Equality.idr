module IdrisUtils.Equality

import public IdrisUtils.Ord
import public IdrisUtils.Decidability

%default total

---------------------------------------------------------------------------------------------------
-- [Propositional Inequality] ---------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Proof that two values of the same type are not (propositionally) equal.
|||
||| Takes advantage of the fact that the given type is totally ordered to avoid equality proofs;
||| specifically, x ≠ y iff (x > y) \/ (x < y).
public export
data NotEq : {ord : StrictTotalOrdering c} -> (x : c) -> (y : c) -> Type where
  IsLT : {ord : StrictTotalOrdering c} -> (lt : proj_LT ord x y) -> NotEq {ord} x y
  IsGT : {ord : StrictTotalOrdering c} -> (gt : proj_LT ord y x) -> NotEq {ord} x y

export
decNotEq_xEQy : (nlt : Not (proj_LT ord x y))
             -> (ngt : Not (proj_LT ord y x))
             -> Not (NotEq {ord} x y)
decNotEq_xEQy nlt ngt (IsLT lt) = nlt lt
decNotEq_xEQy nlt ngt (IsGT gt) = ngt gt

export
decNotEq : (ord : StrictTotalOrdering c) -> (x,y : c) -> Dec (NotEq {ord = ord} x y)
decNotEq ord x y with (proj_decLT ord x y)
  decNotEq ord x y | Yes lt = Yes (IsLT lt)
  decNotEq ord x y | No nlt with (proj_decLT ord y x)
    decNotEq ord x y | No nlt | Yes gt = Yes (IsGT gt)
    decNotEq ord x y | No nlt | No ngt = No (decNotEq_xEQy nlt ngt)
---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
soundNotEq : {x : c} -> {ord : StrictTotalOrdering c} -> (p : NotEq {ord=ord} x y) -> Not (x = y)
soundNotEq {x} (IsLT {ord} lt) Refl = proj_Asym ord x x lt lt
soundNotEq {x} (IsGT {ord} gt) Refl = proj_Asym ord x x gt gt

export
singNotEq : (ord : StrictTotalOrdering c) -> (x : c) -> (y : c)
         -> (p : NotEq {ord = ord} x y) -> (q : NotEq {ord = ord} x y) -> p = q
singNotEq ord x y (IsLT p) (IsLT q) with (singLT (ordS ord) x y p q)
  singNotEq ord x y (IsLT p) (IsLT p) | Refl = Refl
singNotEq ord x y (IsLT p) (IsGT q) with (proj_Asym ord x y p q)
  singNotEq ord x y (IsLT p) (IsGT q) | _ impossible
singNotEq ord x y (IsGT p) (IsGT q) with (singLT (ordS ord) y x p q)
  singNotEq ord x y (IsGT p) (IsGT p) | Refl = Refl
singNotEq ord x y (IsGT p) (IsLT q) with (proj_Asym ord y x p q)
  singNotEq ord x y (IsGT p) (IsLT q) | _ impossible

export
irrNotEq : {x : c} -> {ord : StrictTotalOrdering c} -> Not (NotEq {ord=ord} x x)
irrNotEq {x} (IsLT {ord} lt) = proj_Asym ord x x lt lt
irrNotEq {x} (IsGT {ord} gt) = proj_Asym ord x x gt gt

---------------------------------------------------------------------------------------------------
-- [Decidability] ---------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
record HasDecEq (c : Type) where
  constructor ItHasDecEq
  theFun : (x,y : c) -> Dec (x = y)

export
soundPropEq : {x : c} -> {ord : StrictTotalOrdering c} -> (x = y) -> Not (NotEq {ord} x y)
soundPropEq {x} Refl (IsLT {ord} p) = proj_Asym ord x x p p
soundPropEq {x} Refl (IsGT {ord} p) = proj_Asym ord x x p p

public export
PropDecEqT : (ord : StrictTotalOrdering c) -> (x, y : c) -> Prop
PropDecEqT ord x y =
  MkProp (x = y) (NotEq {ord=ord} x y)
         (decEq ord x y) (decNotEq ord x y)
         soundPropEq soundNotEq

export
decPEq : DecPLT c => (x, y : c) -> PDec (PropDecEqT (Ord.theOrder {c = c}) x y)
decPEq x y with (decPLT x y)
  decPEq x y | Yes lt = No (IsLT lt)
  decPEq x x | No IsEq = Yes Refl
  decPEq x y | No (IsLT gt) = No (IsGT gt)
