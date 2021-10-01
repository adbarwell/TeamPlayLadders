module IdrisUtils.Ord.OrdS

import public IdrisUtils.Ord.OrdT

%default total

---------------------------------------------------------------------------------------------------
-- [Definition] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A strict total ordering over a given carrier type that has an equivalence relation s.t.
||| for all elements, `x` and `y`, and all proofs, `p` and `q`, of `x < y`, `p = q`.
|||
||| This 'singularity' proof (in the sense that only a single value may be constructed for the type)
||| is useful for proofs of contradiction.
|||
public export
record StrictTotalOrderingS (c : Type) (setoid : SetoidT c) where
  constructor MkSTOrderingS
  ordT   : StrictTotalOrderingT c setoid
  ||| `∀ x,y : c . ∀ p,q : LT x y . p = q`
  singLT : (x,y : c) -> (p,q : ltR ordT x y) -> p = q

---------------------------------------------------------------------------------------------------
-- [Projections] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
proj_LT : StrictTotalOrderingS c setoid -> (c -> c -> Type)
proj_LT ordS = ltR (ordT ordS)

public export
proj_Asym : (ordS : StrictTotalOrderingS c setoid)
         -> ((x,y : c) -> proj_LT ordS x y -> Not (proj_LT ordS y x))
proj_Asym ordS = asymLT (ordT ordS)

public export
proj_Trans : (ordS : StrictTotalOrderingS c setoid)
          -> ((x,y,z : c) -> proj_LT ordS x y -> proj_LT ordS y z -> proj_LT ordS x z)
proj_Trans ordS = transLT (ordT ordS)

public export
proj_Tricho : (ordS : StrictTotalOrderingS c setoid)
           -> ((x,y : c) -> Trichotomy setoid (proj_LT ordS) (proj_Asym ordS) x y)
proj_Tricho ordS = trichoLT (ordT ordS)

public export
proj_decLT : (ordS : StrictTotalOrderingS c setoid) -> ((x,y : c) -> Dec (proj_LT ordS x y))
proj_decLT ordS = decLT (ordT ordS)

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
