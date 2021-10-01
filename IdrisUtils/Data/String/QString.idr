module IdrisUtils.Data.String.QString

import public Data.List
import public IdrisUtils.Data.Char.PChar
import public IdrisUtils.Data.Vect

-- import public IdrisUtils.Data.Vect.Equality
-- import public IdrisUtils.Data.Vect.Sum

%default total

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data QString : (str : Vect len Char) -> Type where
  Nil  : QString []
  (::) : {k : CharKind} -> {n : Nat} -> QChar c (k,n) -> QString cs -> QString (c :: cs)

---------------------------------------------------------------------------------------------------
-- [Singleton] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| If two strings are indexed by the same character list, then those two strings are the same.
|||
||| I.e. (str1 = str2 -> QString str1 = QString str2)
export
congruentQString : (x,y : QString str) -> x = y
congruentQString Nil Nil = Refl
congruentQString ((::) x xs) ((::) y ys) with (injectiveQChar x y)
  congruentQString ((::) x xs) ((::) y ys) | Refl with (singletonQChar x y)
    congruentQString ((::) x xs) ((::) x ys) | Refl | Refl
      with (congruentQString xs ys)
        congruentQString ((::) x xs) ((::) x xs) | Refl | Refl | Refl = Refl

---------------------------------------------------------------------------------------------------
-- [DecEq] ----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
decEqQString0 : (x,y : QString str) -> Dec (x = y)
decEqQString0 x y = Yes (congruentQString x y)

export
implementation DecEq (QString str) where
  decEq = decEqQString0

export
decEqQString : {n,m : Nat} -> {v : Vect n Char} -> {w : Vect m Char}
            -> (x : QString v) -> (y : QString w) -> Dec (x = y)
decEqQString {n} {m} {v} {w} x y with (decEqVect v w)
  decEqQString {n} {m=n} {v} {w=v} x y | Yes Refl = rewrite congruentQString x y in Yes Refl
  decEqQString {n} {m} {v} {w} x y | No neq = No (contra neq) where
    contra : {v' : Vect n' Char}
          -> {w' : Vect m' Char}
          -> {x' : QString v'}
          -> {y' : QString w'}
          -> (neq' : Not (v' = w'))
          -> Not (x' = y')
    contra neq' Refl = neq' Refl

---------------------------------------------------------------------------------------------------
-- [Cast] -----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
toStringQString : {str : Vect n Char} -> (x : QString str) -> String
toStringQString {str} x = pack (toList str)

export
fromStringQString : (str : String) -> Maybe (QString (fromList (unpack str)))
fromStringQString str = fromString' (fromList (unpack str)) where
  fromString' : (cs : Vect len Char) -> Maybe (QString cs)
  fromString' [] = Just Nil
  fromString' (c :: cs) = do
    ((k,i) ** x) <- fromCharQChar c
    xs <- fromString' cs
    pure ((::) x xs)

---------------------------------------------------------------------------------------------------
-- [Total Ordering] -------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Definition] -----------------------------------------------------------------------------------

public export
data LTQString : (x : QString v) -> (y : QString w) -> Type where
  IsLTQStringNil : LTQString Nil (y :: ys)
  IsLTQStringChar : {xs : QString xs'} -> {ys : QString ys'}
                 -> (lt : LTQChar x y) -> LTQString (x :: xs) (y :: ys)
  IsLTQStringRest : (lt : LTQString xs ys) -> LTQString (x :: xs) (x :: ys)

-- [Uninhabited] ----------------------------------------------------------------------------------

export
implementation Uninhabited (LTQString (x :: xs) Nil) where
  uninhabited _ impossible

-- [Asymmetry, Transitivity, and Trichotomy] ------------------------------------------------------

export
asymLTQString : {v : Vect n Char} -> {w : Vect m Char}
             -> (x : QString v) -> (y : QString w) -> LTQString x y -> Not (LTQString y x)
asymLTQString Nil ((::) y ys) IsLTQStringNil q = absurd q
asymLTQString ((::) x xs) ((::) y ys) (IsLTQStringChar p) (IsLTQStringChar q) =
  asymLTQChar x y p q
asymLTQString ((::) x xs) ((::) x ys) (IsLTQStringChar p) (IsLTQStringRest q) =
  irrLTQChar x p
asymLTQString ((::) x xs) ((::) x ys) (IsLTQStringRest p) (IsLTQStringChar q) =
  irrLTQChar x q
asymLTQString ((::) x xs) ((::) x ys) (IsLTQStringRest p) (IsLTQStringRest q) =
  asymLTQString xs ys p q

export
irrLTQString : {v : Vect n Char} -> (x : QString v) -> Not (LTQString x x)
irrLTQString x p = asymLTQString x x p p

export
transLTQString : (x : QString v)
              -> (y : QString w)
              -> (z : QString u)
              -> LTQString x y
              -> LTQString y z
              -> LTQString x z
transLTQString Nil ((::) y ys) ((::) z zs) IsLTQStringNil (IsLTQStringChar q) =
  IsLTQStringNil
transLTQString Nil ((::) y ys) ((::) y zs) IsLTQStringNil (IsLTQStringRest q) =
  IsLTQStringNil
transLTQString ((::) x xs) ((::) y ys) ((::) z zs) (IsLTQStringChar p) (IsLTQStringChar q) =
  IsLTQStringChar (transLTQChar x y z p q)
transLTQString ((::) x xs) ((::) y ys) ((::) y zs) (IsLTQStringChar p) (IsLTQStringRest q) = IsLTQStringChar p
transLTQString ((::) x xs) ((::) x ys) ((::) z zs) (IsLTQStringRest p) (IsLTQStringChar q) = IsLTQStringChar q
transLTQString ((::) x xs) ((::) x ys) ((::) x zs) (IsLTQStringRest p) (IsLTQStringRest q) = IsLTQStringRest (transLTQString xs ys zs p q)

-- [Decision Procedure] ---------------------------------------------------------------------------

export
decLTQString : {n,m : Nat} -> {v : Vect n Char} -> {w : Vect m Char}
            -> (x : QString v) -> (y : QString w) -> Dec (LTQString x y)
decLTQString Nil Nil = No (irrLTQString Nil)
decLTQString Nil ((::) y ys) = Yes IsLTQStringNil
decLTQString ((::) x xs) Nil = No (asymLTQString Nil ((::) x xs) IsLTQStringNil)
decLTQString ((::) x xs) ((::) y ys) with (trichoLTPChar (MkChar x) (MkChar y))
  decLTQString ((::) x xs) ((::) x ys) | IsEq Refl with (decLTQString xs ys)
    decLTQString ((::) x xs) ((::) x ys) | IsEq Refl | Yes p =
      Yes (IsLTQStringRest p)
    decLTQString ((::) x xs) ((::) x ys) | IsEq Refl | No np =
      No (\prf => case prf of
                    IsLTQStringChar p => irrLTQChar x p
                    IsLTQStringRest p => np p)
  decLTQString ((::) x xs) ((::) y ys) | IsBinR_xRy (IsLTPChar p) =
    Yes (IsLTQStringChar p)
  decLTQString ((::) x xs) ((::) y ys) | IsBinR_yRx (IsLTPChar q) =
    No (\prf => case prf of
                  IsLTQStringChar p => asymLTQChar x y p q
                  IsLTQStringRest p => irrLTQChar x q)

-- [Singleton] ------------------------------------------------------------------------------------

export
singLTQString : (x : QString v)
             -> (y : QString w)
             -> (p,q : LTQString x y)
             -> p = q
singLTQString Nil ((::) y ys) IsLTQStringNil IsLTQStringNil = Refl
singLTQString ((::) x xs) ((::) y ys) (IsLTQStringChar p) (IsLTQStringChar q) =
  case (singLTQChar x y p q) of Refl => Refl
singLTQString ((::) x xs) ((::) x ys) (IsLTQStringChar p) (IsLTQStringRest q)
  with (irrLTQChar x p)
    singLTQString ((::) x xs) ((::) x ys) (IsLTQStringChar p) (IsLTQStringRest q) | _
      impossible
singLTQString ((::) x xs) ((::) x ys) (IsLTQStringRest p) (IsLTQStringChar q)
  with (irrLTQChar x q)
    singLTQString ((::) x xs) ((::) x ys) (IsLTQStringRest p) (IsLTQStringChar q) | _
      impossible
singLTQString ((::) x xs) ((::) x ys) (IsLTQStringRest p) (IsLTQStringRest q) =
  case (singLTQString xs ys p q) of Refl => Refl

