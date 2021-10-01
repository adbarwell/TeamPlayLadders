module IdrisUtils.Data.String.PString

import public IdrisUtils.Data.String.QString

%default total

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data PString : Type where
  MkString : {len : Nat} -> {str : Vect len Char} -> QString str -> PString

---------------------------------------------------------------------------------------------------
-- [DecEq] ----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
decEqPString : (x,y : PString) -> Dec (x = y)
decEqPString (MkString x) (MkString y) with (decEqQString x y)
  decEqPString (MkString x) (MkString x) | Yes Refl = Yes Refl
  decEqPString (MkString x) (MkString y) | No neq = No (contra neq) where
    contra : {x' : QString v}
          -> {y' : QString w}
          -> (neq' : Not (x' = y'))
          -> Not (MkString x' = MkString y')
    contra neq' Refl = neq' Refl

export
implementation DecEq PString where
  decEq = decEqPString

---------------------------------------------------------------------------------------------------
-- [Cast] -----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
toString : PString -> String
toString (MkString {str} _) = pack (toList str)

export
implementation Cast PString String where
  cast = toString

export
fromStringPString : (str : String) -> Maybe PString
fromStringPString str = do
  qstr <- fromStringQString str
  pure (MkString qstr)

export 
implementation Cast String PString where
  cast str = case fromStringPString str of
    Nothing => MkString Nil
    Just pstr => pstr

---------------------------------------------------------------------------------------------------
-- [Show] -----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
implementation Show PString where
  show = toString

---------------------------------------------------------------------------------------------------
-- [Total Ordering] -------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Definition] -----------------------------------------------------------------------------------

public export
data LTPString : (x,y : PString) -> Type where
  IsLTPString : (p : LTQString x y) -> LTPString (MkString x) (MkString y)

public export
LTPString' : (x,y : PString) -> Type
LTPString' x y = LTPString x y

-- [Uninhabited] ----------------------------------------------------------------------------------

implementation Uninhabited (MkString Nil = MkString ((::) y ys)) where
  uninhabited Refl impossible

-- [Asymmetry, Transitivity, and Trichotomy] ------------------------------------------------------

export
asymLTPString : (x,y : PString) -> LTPString x y -> Not (LTPString y x)
asymLTPString (MkString x) (MkString y) (IsLTPString p) (IsLTPString q) = asymLTQString x y p q

export
irrLTPString : (x : PString) -> Not (LTPString x x)
irrLTPString x p = asymLTPString x x p p

export
transLTPString : (x,y,z : PString)
              -> LTPString x y
              -> LTPString y z
              -> LTPString x z
transLTPString (MkString x) (MkString y) (MkString z) (IsLTPString p) (IsLTPString q) =
  IsLTPString (transLTQString x y z p q)


export
trichoLTPString' : {v : Vect n Char}
                -> {w : Vect m Char}
                -> (x : QString v)
                -> (y : QString w)
                -> Trichotomy (PropEqSetoid PString PString.decEqPString)
                              LTPString' PString.asymLTPString (MkString x) (MkString y)
trichoLTPString' [] [] = IsEq Refl
trichoLTPString' [] (y :: ys) = IsBinR_xRy (IsLTPString IsLTQStringNil)
trichoLTPString' (x :: xs) [] = IsBinR_yRx (IsLTPString IsLTQStringNil)
trichoLTPString' (x :: xs) (y :: ys) with (trichoLTPChar (MkChar x) (MkChar y))
  trichoLTPString' (x :: xs) (x :: ys) | IsEq Refl with (trichoLTPString' xs ys)
    trichoLTPString' (x :: xs) (x :: xs) | IsEq Refl | IsEq Refl = IsEq Refl
    trichoLTPString' (x :: xs) (x :: ys) | IsEq Refl | IsBinR_xRy (IsLTPString p) =
      IsBinR_xRy (IsLTPString (IsLTQStringRest p))
    trichoLTPString' (x :: xs) (x :: ys) | IsEq Refl | IsBinR_yRx (IsLTPString p) =
      IsBinR_yRx (IsLTPString (IsLTQStringRest p))
  trichoLTPString' (x :: xs) (y :: ys) | IsBinR_xRy (IsLTPChar p) =
    IsBinR_xRy (IsLTPString (IsLTQStringChar p))
  trichoLTPString' (x :: xs) (y :: ys) | IsBinR_yRx (IsLTPChar p) =
    IsBinR_yRx (IsLTPString (IsLTQStringChar p))

export 
trichoLTPString : (x, y : PString)
               -> Trichotomy (PropEqSetoid PString PString.decEqPString)
                             LTPString' PString.asymLTPString x y
trichoLTPString (MkString {str=v} x) (MkString {str=w} y) = trichoLTPString' x y

-- [Decision Procedure] ---------------------------------------------------------------------------

export
decLTPString : (x,y : PString) -> Dec (LTPString x y)
decLTPString x y with (trichoLTPString x y)
  decLTPString x x | IsEq Refl = No (irrLTPString x)
  decLTPString x y | IsBinR_xRy p = Yes p
  decLTPString x y | IsBinR_yRx q = No (asymLTPString y x q)


-- [Total Ordering (General Setoid)] --------------------------------------------------------------

export
StrictTotalOrderingTPString : StrictTotalOrderingT PString
                                                   (PropEqSetoid PString PString.decEqPString)
StrictTotalOrderingTPString =
  MkSTOrderingT LTPString' asymLTPString transLTPString trichoLTPString decLTPString

-- [Singleton] ------------------------------------------------------------------------------------

export
singLTPString : (x,y : PString) -> (p,q : LTPString x y) -> p = q
singLTPString (MkString x) (MkString y) (IsLTPString p) (IsLTPString q) with (singLTQString x y p q)
  singLTPString (MkString x) (MkString y) (IsLTPString p) (IsLTPString p) | Refl = Refl


-- [Total Ordering with Singleton] ----------------------------------------------------------------

export
StrictTotalOrderingSPString : StrictTotalOrderingS PString
                                                   (PropEqSetoid PString PString.decEqPString)
StrictTotalOrderingSPString = MkSTOrderingS StrictTotalOrderingTPString singLTPString

-- [Total Ordering] -------------------------------------------------------------------------------

export
StrictTotalOrderingPString : StrictTotalOrdering PString
StrictTotalOrderingPString = MkSTOrdering PString.decEqPString StrictTotalOrderingSPString

export
implementation StrictTotalOrder PString where
  theOrder = StrictTotalOrderingPString

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Decidability] ---------------------------------------------------------------------------------

export
implementation DecPLT PString where
  lt_sound {y = MkString y} (IsLTPString p) IsEq = irrLTQString y p
  lt_sound {x = MkString x} {y = MkString y} (IsLTPString p) (IsLT (IsLTPString q)) =
    asymLTQString x y p q

  gte_sound {y} IsEq q = irrLTPString y q
  gte_sound {x = MkString x} {y = MkString y} (IsLT (IsLTPString p)) (IsLTPString q) =
    asymLTQString y x p q
