module IdrisUtils.Data.Vect.Elem

import public Data.Vect
import public Data.Vect.Elem
import public IdrisUtils.Equality

%default total

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A proof that some element is not in a vector.
public export
data NotElem : {0 c : Type} -> {ord : StrictTotalOrdering c} -> {n : Nat}
            -> (x : c) -> (ys : Vect n c) -> Type where
  Nil  : NotElem x []
  (::) : {ord : StrictTotalOrdering c}
      -> (notHere : NotEq {ord} x y)
      -> (notLater : NotElem {ord} x ys)
      -> NotElem {ord} x (y :: ys)

public export
data ElemS : {0 c : Type} -> {ord : StrictTotalOrdering c} -> {n : Nat}
          -> (x : c) -> (ys : Vect n c) -> Type where
  JustHere : {ord : StrictTotalOrdering c}
          -> (notLater : NotElem {ord} x ys)
          -> ElemS {ord} x (x :: ys)
  JustThere : {ord : StrictTotalOrdering c}
           -> (notHere : NotEq {ord} x y)
           -> (later : ElemS {ord} x ys)
           -> ElemS {ord} x (y :: ys)
  HereAndThere : {ord : StrictTotalOrdering c}
              -> (later : ElemS {ord} x ys)
              -> ElemS {ord} x (x :: ys)

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [NotElem] --------------------------------------------------------------------------------------

export
decNotElem : {ord : StrictTotalOrdering c}
          -> (x : c) -> (ys : Vect n c) -> Dec (NotElem {ord=ord} x ys)
decNotElem x [] = Yes []
decNotElem {ord} x (y :: ys) with (decNotEq ord x y)
  decNotElem {ord} x (y :: ys) | No eq = No (\(neq :: _) => eq neq)
  decNotElem {ord} x (y :: ys) | Yes neq with (decNotElem {ord=ord} x ys)
    decNotElem {ord} x (y :: ys) | Yes neq | No elem = No (\(_ :: nelem) => elem nelem)
    decNotElem {ord} x (y :: ys) | Yes neq | Yes nelem = Yes (neq :: nelem)

export
soundNotElem : {x : c} -> (p : NotElem x ys) -> Not (Elem x ys)
soundNotElem [] q = absurd q
soundNotElem (p :: ps) Here = irrNotEq p
soundNotElem (p :: ps) (There q) = soundNotElem ps q

export
singNotElem : {ord : StrictTotalOrdering c}
           -> (x : c) -> (ys : Vect n c) -> (p,q : NotElem {ord=ord} x ys) -> p = q
singNotElem x [] [] [] = Refl
singNotElem {ord} x (y :: ys) (p :: ps) (q :: qs) =
  rewrite singNotEq ord x y p q in
    replace {p=(\x => q :: ps = q :: x)} (singNotElem x ys ps qs) Refl

-- [ElemS] ----------------------------------------------------------------------------------------

export
implementation Uninhabited (ElemS {ord} x []) where
  uninhabited _ impossible

export
decElemS : {ord : StrictTotalOrdering c} -> (x : c) -> (ys : Vect n c) -> Dec (ElemS {ord} x ys)
decElemS x [] = No absurd
decElemS {ord} x (y :: ys) with (proj_Tricho ord x y)
  decElemS {ord} x (x :: ys) | IsEq Refl with (decElemS {ord=ord} x ys)
    decElemS {ord} x (x :: ys) | IsEq Refl | Yes later = Yes (HereAndThere later)
    decElemS {ord} x (x :: ys) | IsEq Refl | No nlater with (decNotElem x ys)
      decElemS {ord} x (x :: ys) | IsEq Refl | No nlater | Yes notLater = Yes (JustHere notLater)
      decElemS {ord} x (x :: ys) | IsEq Refl | No nlater | No nnotLater =
        No (contra nlater nnotLater) where
          contra : {x' : c}
                -> {0 ys' : Vect n' c}
                -> (c1 : Not (ElemS {ord} x' ys'))
                -> (c2 : Not (NotElem {ord} x' ys'))
                -> Not (ElemS {ord} x' (x' :: ys'))
          contra c1 c2 (JustHere p) = c2 p
          contra c1 c2 (JustThere p q) = irrNotEq p
          contra c1 c2 (HereAndThere p) = c1 p
  decElemS {ord} x (y :: ys) | IsBinR_xRy lt with (decElemS {ord=ord} x ys)
    decElemS {ord} x (y :: ys) | IsBinR_xRy lt | Yes later = Yes (JustThere (IsLT lt) later)
    decElemS {ord} x (y :: ys) | IsBinR_xRy lt | No nlater = No (contra lt nlater) where
      contra : {x' : c}
            -> (c1 : ltR (ordT (ordS ord)) x' y')
            -> (c2 : Not (ElemS {ord} x' ys'))
            -> Not (ElemS {ord} x' (y' :: ys'))
      contra {x'} c1 c2 (JustHere p) = proj_Asym ord x' x' c1 c1
      contra c1 c2 (JustThere p q) = c2 q
      contra {x'} c1 c2 (HereAndThere p) = proj_Asym ord x' x' c1 c1
  decElemS {ord} x (y :: ys) | IsBinR_yRx gt with (decElemS {ord=ord} x ys)
    decElemS {ord} x (y :: ys) | IsBinR_yRx gt | Yes later = Yes (JustThere (IsGT gt) later)
    decElemS {ord} x (y :: ys) | IsBinR_yRx gt | No nlater = No (contra gt nlater) where
      contra : {x' : c}
            -> (c1 : ltR (ordT (ordS ord)) y' x')
            -> (c2 : Not (ElemS {ord} x' ys'))
            -> Not (ElemS {ord} x' (y' :: ys'))
      contra {x'} c1 c2 (JustHere p) = proj_Asym ord x' x' c1 c1
      contra c1 c2 (JustThere p q) = c2 q
      contra {x'} c1 c2 (HereAndThere p) = proj_Asym ord x' x' c1 c1

export
soundElemS : {x : c} -> (p : ElemS {ord} x ys) -> Not (NotElem {ord} x ys)
soundElemS (JustHere p) (q :: qs) = irrNotEq q
soundElemS (JustThere p1 p2) (q :: qs) = soundElemS p2 qs
soundElemS (HereAndThere p) (q :: qs) = irrNotEq q

export
singElemS : {ord : StrictTotalOrdering c}
         -> (x : c)
         -> (ys : Vect n c)
         -> (p,q : ElemS {ord} x ys)
         -> p = q
singElemS x (x :: ys) (JustHere p) (JustHere q) =
  replace {p = (\x => JustHere p = JustHere x)} (singNotElem x ys p q) Refl
singElemS x (x :: ys) (JustHere p) (JustThere q1 q2) with (irrNotEq q1)
  singElemS x (x :: ys) (JustHere p) (JustThere q1 q2) | _ impossible
singElemS x (x :: ys) (JustHere p) (HereAndThere q) with (soundElemS q p)
  singElemS x (x :: ys) (JustHere p) (HereAndThere q) | _ impossible
singElemS x (x :: ys) (JustThere p1 p2) (JustHere q) with (irrNotEq p1)
  singElemS x (x :: ys) (JustThere p1 p2) (JustHere q) | _ impossible
singElemS {ord} x (y :: ys) (JustThere p1 p2) (JustThere q1 q2) =
  rewrite singNotEq ord x y p1 q1 in
    replace {p=(\x =>JustThere q1 p2 = JustThere q1 x)} (singElemS x ys p2 q2) Refl
singElemS x (x :: ys) (JustThere p1 p2) (HereAndThere q) with (irrNotEq p1)
  singElemS x (x :: ys) (JustThere p1 p2) (HereAndThere q) | _ impossible
singElemS x (x :: ys) (HereAndThere p) (JustHere q) with (soundElemS p q)
  singElemS x (x :: ys) (HereAndThere p) (JustHere q) | _ impossible
singElemS x (x :: ys) (HereAndThere p) (JustThere q1 q2) with (irrNotEq q1)
  singElemS x (x :: ys) (HereAndThere p) (JustThere q1 q2) | _ impossible
singElemS x (x :: ys) (HereAndThere p) (HereAndThere q) =
  replace {p=(\x => HereAndThere p = HereAndThere x)} (singElemS x ys p q) Refl
