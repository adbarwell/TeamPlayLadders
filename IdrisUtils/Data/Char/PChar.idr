module IdrisUtils.Data.Char.PChar

import public Data.Vect

import public IdrisUtils.Data.Char.QChar
import public IdrisUtils.Ord

%default total

---------------------------------------------------------------------------------------------------
-- [Char] -----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data PChar : Type where
  MkChar : {v : Char} -> {k : CharKind} -> {n : Nat} -> (c : QChar v (k,n)) -> PChar

---------------------------------------------------------------------------------------------------
-- [DecEq] ----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
decEqPChar : (x,y : PChar) -> Dec (x = y)
decEqPChar (MkChar {v} {k=ki} {n=ni} x) (MkChar {v=w} {k=kj} {n=nj} y) with (decEqQChar x y)
  decEqPChar (MkChar {v} {k=ki} {n=ni} x) (MkChar {v=v} {k=ki} {n=ni} x) | Yes Refl = Yes Refl
  decEqPChar (MkChar {v} {k=ki} {n=ni} x) (MkChar {v=w} {k=kj} {n=nj} y) | No neq =
    No (contra neq) where
      contra : {x' : QChar v' (ki',ni')} -> {y' : QChar w' (kj',nj')}
            -> (neq' : Not (x' = y')) -> Not (MkChar x' = MkChar y')
      contra neq' Refl = neq' Refl

export
implementation DecEq PChar where
  decEq = decEqPChar

---------------------------------------------------------------------------------------------------
-- [Total Ordering] -------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Definition] -----------------------------------------------------------------------------------

public export
data LTPChar : (x,y : PChar) -> Type where
  IsLTPChar : (lt : LTQChar x y) -> LTPChar (MkChar x) (MkChar y)

public export
LTPChar' : (x, y : PChar) -> Type
LTPChar' x y = LTPChar x y

-- [Asymmetry, Transitivity, and Trichotomy] ------------------------------------------------------

export
asymLTPChar : (x,y : PChar) -> (p : LTPChar x y) -> (q : LTPChar y x) -> Void
asymLTPChar (MkChar x) (MkChar y) (IsLTPChar p) (IsLTPChar q) = asymLTQChar x y p q

export
irrLTPChar : (x : PChar) -> (p : LTPChar x x) -> Void
irrLTPChar x p = asymLTPChar x x p p

export
transLTPChar : (x,y,z : PChar) -> LTPChar x y -> LTPChar y z -> LTPChar x z
transLTPChar (MkChar {v = xv} {k = xk} {n = xi} x)
             (MkChar {v = yv} {k = xk} {n = yi} y)
             (MkChar {v = zv} {k = xk} {n = zi} z)
             (IsLTPChar (IsLTNat p)) (IsLTPChar (IsLTNat q)) =
  IsLTPChar (IsLTNat (transLTNat xi yi zi p q))
transLTPChar (MkChar {v = xv} {k = xk} {n = xi} x)
             (MkChar {v = yv} {k = xk} {n = yi} y)
             (MkChar {v = zv} {k = zk} {n = zi} z)
             (IsLTPChar (IsLTNat p)) (IsLTPChar (IsLTCharKind q)) =
  IsLTPChar (IsLTCharKind q)
transLTPChar (MkChar {v = xv} {k = xk} {n = xi} x)
             (MkChar {v = yv} {k = yk} {n = yi} y)
             (MkChar {v = zv} {k = yk} {n = zi} z)
             (IsLTPChar (IsLTCharKind p)) (IsLTPChar (IsLTNat q)) =
  IsLTPChar (IsLTCharKind p)
transLTPChar (MkChar {v = xv} {k = xk} {n = xi} x)
             (MkChar {v = yv} {k = yk} {n = yi} y)
             (MkChar {v = zv} {k = zk} {n = zi} z)
             (IsLTPChar (IsLTCharKind p)) (IsLTPChar (IsLTCharKind q)) =
  IsLTPChar (IsLTCharKind (transLTCharKind xk yk zk p q))

export
trichoLTPChar : (x,y : PChar)
             -> Trichotomy (PropEqSetoid PChar PChar.decEqPChar) LTPChar' PChar.asymLTPChar x y
trichoLTPChar (MkChar {v} {k = ki} {n = ni} x) (MkChar {v = w} {k = kj} {n = nj} y) with (trichoLTCharKind ki kj)
  trichoLTPChar (MkChar {v} {k = ki} {n = ni} x) (MkChar {v = w} {k = ki} {n = nj} y) | IsEq Refl with (trichoLTNat ni nj)
    trichoLTPChar (MkChar {v} {k = ki} {n = ni} x) (MkChar {v = w} {k = ki} {n = ni} y) | IsEq Refl | IsEq Refl with (injectiveQChar'' x y)
      trichoLTPChar (MkChar {v} {k = ki} {n = ni} x) (MkChar {v = v} {k = ki} {n = ni} y) | IsEq Refl | IsEq Refl | Refl = rewrite (singletonQChar x y) in IsEq Refl
    trichoLTPChar (MkChar {v} {k = ki} {n = ni} x) (MkChar {v = w} {k = ki} {n = nj} y) | IsEq Refl | IsBinR_xRy nq = IsBinR_xRy (IsLTPChar (IsLTNat nq))
    trichoLTPChar (MkChar {v} {k = ki} {n = ni} x) (MkChar {v = w} {k = ki} {n = nj} y) | IsEq Refl | IsBinR_yRx nq = IsBinR_yRx (IsLTPChar (IsLTNat nq))
  trichoLTPChar (MkChar {v} {k = ki} {n = ni} x) (MkChar {v = w} {k = kj} {n = nj} y) | IsBinR_xRy kp = IsBinR_xRy (IsLTPChar (IsLTCharKind kp))
  trichoLTPChar (MkChar {v} {k = ki} {n = ni} x) (MkChar {v = w} {k = kj} {n = nj} y) | IsBinR_yRx kp = IsBinR_yRx (IsLTPChar (IsLTCharKind kp))

-- [Decision Procedure] ---------------------------------------------------------------------------

export
decLTPChar : (x,y : PChar) -> Dec (LTPChar x y)
decLTPChar (MkChar x) (MkChar y) with (decLTQChar x y)
  decLTPChar (MkChar x) (MkChar y) | No gte = No (\(IsLTPChar lt) => gte lt)
  decLTPChar (MkChar x) (MkChar y) | Yes lt = Yes (IsLTPChar lt)

-- [Total Ordering (General Setoid)] --------------------------------------------------------------

export
StrictTotalOrderingTPChar : StrictTotalOrderingT PChar (PropEqSetoid PChar PChar.decEqPChar)
StrictTotalOrderingTPChar = MkSTOrderingT LTPChar' asymLTPChar transLTPChar trichoLTPChar decLTPChar

-- [Singleton] ------------------------------------------------------------------------------------

export
singLTPChar : (x,y : PChar) -> (p,q : LTPChar x y) -> p = q
singLTPChar (MkChar x) (MkChar y) (IsLTPChar p) (IsLTPChar q) = rewrite singLTQChar x y p q in Refl

-- [Total Ordering with Singleton] ----------------------------------------------------------------

export
StrictTotalOrderingSPChar : StrictTotalOrderingS PChar (PropEqSetoid PChar PChar.decEqPChar)
StrictTotalOrderingSPChar = MkSTOrderingS StrictTotalOrderingTPChar singLTPChar

-- [Total Ordering] -------------------------------------------------------------------------------

export
StrictTotalOrderingPChar : StrictTotalOrdering PChar
StrictTotalOrderingPChar = MkSTOrdering PChar.decEqPChar StrictTotalOrderingSPChar

---------------------------------------------------------------------------------------------------
-- [CharAsNat] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data PCharAsNat : PChar -> Nat -> Type where
  MkPCharAsNat : CharKindAsNat k m -> PCharAsNat (MkChar {k} {n} x) (n + m)

---------------------------------------------------------------------------------------------------
-- [Char Kinds] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data Minuscule : PChar -> Type where
  IsUndscr : Minuscule (MkChar C_)
  IsMin : Minuscule (MkChar {k = Min _} x)

public export
data Majuscule : PChar -> Type where
  IsMaj : Majuscule (MkChar {k = Maj _} x)

public export
data Numeral : PChar -> Type where
  IsNum : Numeral (MkChar {k = Num} x)

public export
data Prime : PChar -> Type where
  IsPri : Prime (MkChar C')
