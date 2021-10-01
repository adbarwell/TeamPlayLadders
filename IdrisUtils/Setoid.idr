module IdrisUtils.Setoid

%default total

---------------------------------------------------------------------------------------------------
-- [Definition] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| An equivalence relation on a carrier type.
public export
record SetoidT (c : Type) where
  constructor MkSetoid
  ||| The equivalence relation itself.
  eqR    : c -> c -> Type
  ||| A proof that the equivalence relation is symmetric; implies reflexivity.
  symEq  : (x,y : c) -> eqR x y -> eqR y x
  ||| A proof that the equivalence relation is transitive.
  trnsEq : (x,y,z : c) -> eqR x y -> eqR y z -> eqR x z

  ||| A proof that the equivalence relation is decidable.
  decEq  : (x,y : c) -> Dec (eqR x y)

---------------------------------------------------------------------------------------------------
-- [Interface] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
interface Setoid c where
  setoid : SetoidT c

---------------------------------------------------------------------------------------------------
-- [Projections] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
