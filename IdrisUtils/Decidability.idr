module IdrisUtils.Decidability

%default total

---------------------------------------------------------------------------------------------------
-- [Proposition] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
record Prop where
  constructor MkProp
  p       : Type
  q       : Type
  isP     : Dec p
  isQ     : Dec q
  p_sound : p -> Not q
  q_sound : q -> Not p

---------------------------------------------------------------------------------------------------
-- [Decidability] ---------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A decidable property `p` either holds or its inverse property `q` holds.
public export
data PDec : (pred : Prop) -> Type where
  Yes : (prf : p pred) -> PDec pred
  No  : (contra : q pred) -> PDec pred

||| A property is decidable and has a decision procedure.
public export
record Decidable (pred : Prop) where
  constructor IsDecidable
  decP : PDec pred

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

soundDecidable : {pred : Prop} -> PDec pred -> Dec (p pred)
soundDecidable (Yes prf) = Yes prf
soundDecidable {pred} (No contra) = No (\prf => q_sound pred contra prf)
