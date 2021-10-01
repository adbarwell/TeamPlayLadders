module IdrisUtils.Fin

import public Data.Fin

%default total

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data IsZero : Fin n -> Type where
  MkIsZero : IsZero FZ

public export
data IsOne : Fin n -> Type where
  MkIsOne : IsOne (FS FZ)

public export
data FinToNat : (fin : Fin ub) -> (nat : Nat) -> Type where
  MkFinToNat : FinToNat fin (finToNat fin)

export
finToNat : (fin : Fin ub) -> (nat : Nat ** (FinToNat fin nat))
finToNat fin = (finToNat fin ** MkFinToNat)

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

injectiveFinToNat : (fin : Fin ub)
                 -> (n,m : Nat)
                 -> (p : FinToNat fin n)
                 -> (q : FinToNat fin m)
                 -> n = m
injectiveFinToNat fin (finToNat fin) (finToNat fin) MkFinToNat MkFinToNat = Refl

singletonFinToNat : (fin : Fin ub) -> (nat : Nat) -> (p,q : FinToNat fin nat) -> p = q
singletonFinToNat fin (finToNat fin) MkFinToNat MkFinToNat = Refl