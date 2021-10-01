module IdrisUtils.Data.Char.CharKind.Base

import public Decidable.Equality
-- import public IdrisUtils.Ord

%default total

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data CharKind : Type where
  ||| Symbols.
  Sym : CharKind
  ||| Numbers.
  Num : CharKind
  ||| Minuscule characters.
  Min : (lvl : Nat) -> CharKind
  ||| Majuscule characters.
  Maj : (lvl : Nat) -> CharKind

---------------------------------------------------------------------------------------------------
-- [Relations] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data CharKindAsNat : CharKind -> Nat -> Type where
  SymAsNat : CharKindAsNat Sym Z
  NumAsNat : CharKindAsNat Num 10
  MinAsNat : CharKindAsNat (Min n) (20 + (10 * n))
  MajAsNat : CharKindAsNat (Maj n) (50 + (10 * n))

export
charKindAsNat : (k : CharKind) -> (n : Nat ** CharKindAsNat k n)
charKindAsNat Sym     = (Z  ** SymAsNat)
charKindAsNat Num     = (10 ** NumAsNat)
charKindAsNat (Min n) = (20 + (10 * n) ** MinAsNat)
charKindAsNat (Maj n) = (50 + (10 * n) ** MajAsNat)

export
injectionCharKindAsNat : (p : CharKindAsNat k n) -> (q : CharKindAsNat k m) -> n = m
injectionCharKindAsNat SymAsNat    SymAsNat    = Refl
injectionCharKindAsNat NumAsNat    NumAsNat    = Refl
injectionCharKindAsNat MinAsNat MinAsNat = Refl
injectionCharKindAsNat MajAsNat MajAsNat = Refl

export
singletonCharKindAsNat : (p : CharKindAsNat k n) -> (q : CharKindAsNat k n) -> p = q
singletonCharKindAsNat SymAsNat SymAsNat = Refl
singletonCharKindAsNat NumAsNat NumAsNat = Refl
singletonCharKindAsNat MinAsNat MinAsNat = Refl
singletonCharKindAsNat MajAsNat MajAsNat = Refl

---------------------------------------------------------------------------------------------------
-- [DecEq] ----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
minInjective : {0 n, m : Nat} -> (0 _ : Min n = Min m) -> n = m
minInjective Refl = Refl

export
majInjective : {0 n, m : Nat} -> (0 _ : Maj n = Maj m) -> n = m
majInjective Refl = Refl

export
implementation Uninhabited (Sym = Num) where
  uninhabited Refl impossible
export
implementation Uninhabited (Sym = Min _) where
  uninhabited Refl impossible
export
implementation Uninhabited (Sym = Maj _) where
  uninhabited Refl impossible
export
implementation Uninhabited (Num = Min _) where
  uninhabited Refl impossible
export
implementation Uninhabited (Num = Maj _) where
  uninhabited Refl impossible
export
implementation Uninhabited (Min _ = Maj _) where
  uninhabited Refl impossible

export
decEqCharKind : (x,y : CharKind) -> Dec (x = y)
decEqCharKind Sym Sym = Yes Refl
decEqCharKind Num Num = Yes Refl
decEqCharKind (Min n) (Min m) with (decEq n m)
  decEqCharKind (Min n) (Min m) | No neq = No (\eq => neq (minInjective eq))
  decEqCharKind (Min n) (Min n) | Yes Refl = Yes Refl
decEqCharKind (Maj n) (Maj m) with (decEq n m)
  decEqCharKind (Maj n) (Maj m) | No neq = No (\eq => neq (majInjective eq))
  decEqCharKind (Maj n) (Maj n) | Yes Refl = Yes Refl
decEqCharKind Sym Num = No absurd
decEqCharKind Sym (Min _) = No absurd
decEqCharKind Sym (Maj _) = No absurd
decEqCharKind Num Sym = No (\p => absurd (sym p))
decEqCharKind Num (Min _) = No absurd
decEqCharKind Num (Maj _) = No absurd
decEqCharKind (Min _) Sym = No (\p => absurd (sym p))
decEqCharKind (Min _) Num = No (\p => absurd (sym p))
decEqCharKind (Min _) (Maj _) = No absurd
decEqCharKind (Maj _) Sym = No (\p => absurd (sym p))
decEqCharKind (Maj _) Num = No (\p => absurd (sym p))
decEqCharKind (Maj _) (Min _) = No (\p => absurd (sym p))

export
implementation DecEq CharKind where
  decEq = decEqCharKind
