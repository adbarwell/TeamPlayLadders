module IdrisUtils.Ord.OrdT

import public IdrisUtils.Setoid
import public IdrisUtils.Trichotomy

import public IdrisUtils.Ord.OrdT.SOrdering

%default total

---------------------------------------------------------------------------------------------------
-- [Definition] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A strict total ordering for a given carrier type that has an equivalence relation.
public export
record StrictTotalOrderingT (c : Type) (setoid : SetoidT c) where
  constructor MkSTOrderingT
  ||| The relation (strictly less-than).
  ltR      : c -> c -> Type
  ||| A proof that the relation is asymmetric; implies irreflexivity.
  asymLT   : (x,y : c) -> ltR x y -> Not (ltR y x)
  ||| A proof that the relation is transitive.
  transLT  : (x,y,z : c) -> ltR x y -> ltR y z -> ltR x z
  ||| A proof that the relation is trichotomous.
  trichoLT : (x,y : c) -> Trichotomy setoid ltR asymLT x y

  ||| A proof that the relation is decidable.
  decLT : (x,y : c) -> Dec (ltR x y)

---------------------------------------------------------------------------------------------------
-- [Interface] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
interface Setoid c => StrictTotalOrderT c where
  order : StrictTotalOrderingT c (Setoid.setoid {c = c})

---------------------------------------------------------------------------------------------------
-- [Projections] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
setoid : {1 set : SetoidT c} -> (0 _ : StrictTotalOrderingT c set) -> SetoidT c
setoid {set} _ = set
