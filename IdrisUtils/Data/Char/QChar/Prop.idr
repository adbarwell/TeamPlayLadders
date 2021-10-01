module IdrisUtils.Data.Char.QChar.Prop

import public IdrisUtils.Data.Char.QChar.Base
import public IdrisUtils.Data.Nat
import public IdrisUtils.Ord

%default total

--------------------------------------------------------------------------------------------------- 
-- [Injectiveness] --------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
injectiveQChar : (x : QChar v i) -> (y : QChar v j) -> i = j
injectiveQChar C_ C_ = Refl
injectiveQChar C' C' = Refl
injectiveQChar Cstop Cstop = Refl
injectiveQChar C0 C0 = Refl
injectiveQChar C1 C1 = Refl
injectiveQChar C2 C2 = Refl
injectiveQChar C3 C3 = Refl
injectiveQChar C4 C4 = Refl
injectiveQChar C5 C5 = Refl
injectiveQChar C6 C6 = Refl
injectiveQChar C7 C7 = Refl
injectiveQChar C8 C8 = Refl
injectiveQChar C9 C9 = Refl
injectiveQChar Ca Ca = Refl
injectiveQChar Cb Cb = Refl
injectiveQChar Cc Cc = Refl
injectiveQChar Cd Cd = Refl
injectiveQChar Ce Ce = Refl
injectiveQChar Cf Cf = Refl
injectiveQChar Cg Cg = Refl
injectiveQChar Ch Ch = Refl
injectiveQChar Ci Ci = Refl
injectiveQChar Cj Cj = Refl
injectiveQChar Ck Ck = Refl
injectiveQChar Cl Cl = Refl
injectiveQChar Cm Cm = Refl
injectiveQChar Cn Cn = Refl
injectiveQChar Co Co = Refl
injectiveQChar Cp Cp = Refl
injectiveQChar Cq Cq = Refl
injectiveQChar Cr Cr = Refl
injectiveQChar Cs Cs = Refl
injectiveQChar Ct Ct = Refl
injectiveQChar Cu Cu = Refl
injectiveQChar Cv Cv = Refl
injectiveQChar Cw Cw = Refl
injectiveQChar Cx Cx = Refl
injectiveQChar Cy Cy = Refl
injectiveQChar Cz Cz = Refl
injectiveQChar CA CA = Refl
injectiveQChar CB CB = Refl
injectiveQChar CC CC = Refl
injectiveQChar CD CD = Refl
injectiveQChar CE CE = Refl
injectiveQChar CF CF = Refl
injectiveQChar CG CG = Refl
injectiveQChar CH CH = Refl
injectiveQChar CI CI = Refl
injectiveQChar CJ CJ = Refl
injectiveQChar CK CK = Refl
injectiveQChar CL CL = Refl
injectiveQChar CM CM = Refl
injectiveQChar CN CN = Refl
injectiveQChar CO CO = Refl
injectiveQChar CP CP = Refl
injectiveQChar CQ CQ = Refl
injectiveQChar CR CR = Refl
injectiveQChar CS CS = Refl
injectiveQChar CT CT = Refl
injectiveQChar CU CU = Refl
injectiveQChar CV CV = Refl
injectiveQChar CW CW = Refl
injectiveQChar CX CX = Refl
injectiveQChar CY CY = Refl
injectiveQChar CZ CZ = Refl

public export
injectiveQChar' : (x : QChar v i) -> (y : QChar w i) -> v = w
injectiveQChar' C_ C_ = Refl
injectiveQChar' C' C' = Refl
injectiveQChar' Cstop Cstop = Refl
injectiveQChar' C0 C0 = Refl
injectiveQChar' C1 C1 = Refl
injectiveQChar' C2 C2 = Refl
injectiveQChar' C3 C3 = Refl
injectiveQChar' C4 C4 = Refl
injectiveQChar' C5 C5 = Refl
injectiveQChar' C6 C6 = Refl
injectiveQChar' C7 C7 = Refl
injectiveQChar' C8 C8 = Refl
injectiveQChar' C9 C9 = Refl
injectiveQChar' Ca Ca = Refl
injectiveQChar' Cb Cb = Refl
injectiveQChar' Cc Cc = Refl
injectiveQChar' Cd Cd = Refl
injectiveQChar' Ce Ce = Refl
injectiveQChar' Cf Cf = Refl
injectiveQChar' Cg Cg = Refl
injectiveQChar' Ch Ch = Refl
injectiveQChar' Ci Ci = Refl
injectiveQChar' Cj Cj = Refl
injectiveQChar' Ck Ck = Refl
injectiveQChar' Cl Cl = Refl
injectiveQChar' Cm Cm = Refl
injectiveQChar' Cn Cn = Refl
injectiveQChar' Co Co = Refl
injectiveQChar' Cp Cp = Refl
injectiveQChar' Cq Cq = Refl
injectiveQChar' Cr Cr = Refl
injectiveQChar' Cs Cs = Refl
injectiveQChar' Ct Ct = Refl
injectiveQChar' Cu Cu = Refl
injectiveQChar' Cv Cv = Refl
injectiveQChar' Cw Cw = Refl
injectiveQChar' Cx Cx = Refl
injectiveQChar' Cy Cy = Refl
injectiveQChar' Cz Cz = Refl
injectiveQChar' CA CA = Refl
injectiveQChar' CB CB = Refl
injectiveQChar' CC CC = Refl
injectiveQChar' CD CD = Refl
injectiveQChar' CE CE = Refl
injectiveQChar' CF CF = Refl
injectiveQChar' CG CG = Refl
injectiveQChar' CH CH = Refl
injectiveQChar' CI CI = Refl
injectiveQChar' CJ CJ = Refl
injectiveQChar' CK CK = Refl
injectiveQChar' CL CL = Refl
injectiveQChar' CM CM = Refl
injectiveQChar' CN CN = Refl
injectiveQChar' CO CO = Refl
injectiveQChar' CP CP = Refl
injectiveQChar' CQ CQ = Refl
injectiveQChar' CR CR = Refl
injectiveQChar' CS CS = Refl
injectiveQChar' CT CT = Refl
injectiveQChar' CU CU = Refl
injectiveQChar' CV CV = Refl
injectiveQChar' CW CW = Refl
injectiveQChar' CX CX = Refl
injectiveQChar' CY CY = Refl
injectiveQChar' CZ CZ = Refl

public export
injectiveQChar'' : (x : QChar v i) -> (y : QChar w i) -> v = w
injectiveQChar'' C_ C_ = Refl
injectiveQChar'' C' C' = Refl
injectiveQChar'' Cstop Cstop = Refl
injectiveQChar'' C0 C0 = Refl
injectiveQChar'' C1 C1 = Refl
injectiveQChar'' C2 C2 = Refl
injectiveQChar'' C3 C3 = Refl
injectiveQChar'' C4 C4 = Refl
injectiveQChar'' C5 C5 = Refl
injectiveQChar'' C6 C6 = Refl
injectiveQChar'' C7 C7 = Refl
injectiveQChar'' C8 C8 = Refl
injectiveQChar'' C9 C9 = Refl
injectiveQChar'' Ca Ca = Refl
injectiveQChar'' Cb Cb = Refl
injectiveQChar'' Cc Cc = Refl
injectiveQChar'' Cd Cd = Refl
injectiveQChar'' Ce Ce = Refl
injectiveQChar'' Cf Cf = Refl
injectiveQChar'' Cg Cg = Refl
injectiveQChar'' Ch Ch = Refl
injectiveQChar'' Ci Ci = Refl
injectiveQChar'' Cj Cj = Refl
injectiveQChar'' Ck Ck = Refl
injectiveQChar'' Cl Cl = Refl
injectiveQChar'' Cm Cm = Refl
injectiveQChar'' Cn Cn = Refl
injectiveQChar'' Co Co = Refl
injectiveQChar'' Cp Cp = Refl
injectiveQChar'' Cq Cq = Refl
injectiveQChar'' Cr Cr = Refl
injectiveQChar'' Cs Cs = Refl
injectiveQChar'' Ct Ct = Refl
injectiveQChar'' Cu Cu = Refl
injectiveQChar'' Cv Cv = Refl
injectiveQChar'' Cw Cw = Refl
injectiveQChar'' Cx Cx = Refl
injectiveQChar'' Cy Cy = Refl
injectiveQChar'' Cz Cz = Refl
injectiveQChar'' CA CA = Refl
injectiveQChar'' CB CB = Refl
injectiveQChar'' CC CC = Refl
injectiveQChar'' CD CD = Refl
injectiveQChar'' CE CE = Refl
injectiveQChar'' CF CF = Refl
injectiveQChar'' CG CG = Refl
injectiveQChar'' CH CH = Refl
injectiveQChar'' CI CI = Refl
injectiveQChar'' CJ CJ = Refl
injectiveQChar'' CK CK = Refl
injectiveQChar'' CL CL = Refl
injectiveQChar'' CM CM = Refl
injectiveQChar'' CN CN = Refl
injectiveQChar'' CO CO = Refl
injectiveQChar'' CP CP = Refl
injectiveQChar'' CQ CQ = Refl
injectiveQChar'' CR CR = Refl
injectiveQChar'' CS CS = Refl
injectiveQChar'' CT CT = Refl
injectiveQChar'' CU CU = Refl
injectiveQChar'' CV CV = Refl
injectiveQChar'' CW CW = Refl
injectiveQChar'' CX CX = Refl
injectiveQChar'' CY CY = Refl
injectiveQChar'' CZ CZ = Refl

--------------------------------------------------------------------------------------------------- 
-- [Singleton] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
singletonQChar : (x : QChar v i) -> (y : QChar v i) -> x = y
singletonQChar C_ C_ = Refl
singletonQChar C' C' = Refl
singletonQChar Cstop Cstop = Refl
singletonQChar C0 C0 = Refl
singletonQChar C1 C1 = Refl
singletonQChar C2 C2 = Refl
singletonQChar C3 C3 = Refl
singletonQChar C4 C4 = Refl
singletonQChar C5 C5 = Refl
singletonQChar C6 C6 = Refl
singletonQChar C7 C7 = Refl
singletonQChar C8 C8 = Refl
singletonQChar C9 C9 = Refl
singletonQChar Ca Ca = Refl
singletonQChar Cb Cb = Refl
singletonQChar Cc Cc = Refl
singletonQChar Cd Cd = Refl
singletonQChar Ce Ce = Refl
singletonQChar Cf Cf = Refl
singletonQChar Cg Cg = Refl
singletonQChar Ch Ch = Refl
singletonQChar Ci Ci = Refl
singletonQChar Cj Cj = Refl
singletonQChar Ck Ck = Refl
singletonQChar Cl Cl = Refl
singletonQChar Cm Cm = Refl
singletonQChar Cn Cn = Refl
singletonQChar Co Co = Refl
singletonQChar Cp Cp = Refl
singletonQChar Cq Cq = Refl
singletonQChar Cr Cr = Refl
singletonQChar Cs Cs = Refl
singletonQChar Ct Ct = Refl
singletonQChar Cu Cu = Refl
singletonQChar Cv Cv = Refl
singletonQChar Cw Cw = Refl
singletonQChar Cx Cx = Refl
singletonQChar Cy Cy = Refl
singletonQChar Cz Cz = Refl
singletonQChar CA CA = Refl
singletonQChar CB CB = Refl
singletonQChar CC CC = Refl
singletonQChar CD CD = Refl
singletonQChar CE CE = Refl
singletonQChar CF CF = Refl
singletonQChar CG CG = Refl
singletonQChar CH CH = Refl
singletonQChar CI CI = Refl
singletonQChar CJ CJ = Refl
singletonQChar CK CK = Refl
singletonQChar CL CL = Refl
singletonQChar CM CM = Refl
singletonQChar CN CN = Refl
singletonQChar CO CO = Refl
singletonQChar CP CP = Refl
singletonQChar CQ CQ = Refl
singletonQChar CR CR = Refl
singletonQChar CS CS = Refl
singletonQChar CT CT = Refl
singletonQChar CU CU = Refl
singletonQChar CV CV = Refl
singletonQChar CW CW = Refl
singletonQChar CX CX = Refl
singletonQChar CY CY = Refl
singletonQChar CZ CZ = Refl

---------------------------------------------------------------------------------------------------
-- [(Strict) Total Ordering] ----------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Definition] -----------------------------------------------------------------------------------

||| x < y
public export
data LTQChar : (x : QChar v i) -> (y : QChar w j) -> Type where
  IsLTNat : {x  : QChar v (k,i)}
         -> {y  : QChar w (k,j)}
         -> (lt : LTNat i j)
         -> LTQChar x y
  IsLTCharKind : {x  : QChar v (kv,i)}
              -> {y  : QChar w (kw,j)}
              -> (lt : LTCharKind kv kw)
              -> LTQChar x y

public export
LTQChar' : (x : QChar v i) -> (y : QChar w j) -> Type
LTQChar' x y = LTQChar x y

-- [Asymmetry, Transitivity, and Trichotomy] ------------------------------------------------------


public export
asymLTQChar : {i,j : (CharKind, Nat)}
           -> (x : QChar v i)
           -> (y : QChar w j)
           -> (p : LTQChar x y)
           -> (q : LTQChar y x)
           -> Void
asymLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTNat q) = asymLTNat i j p q
asymLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind q) = irrLTCharKind k q
asymLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTCharKind p) (IsLTNat q) = irrLTCharKind k p
asymLTQChar {i = (kv,i)} {j = (kw,j)} x y (IsLTCharKind p) (IsLTCharKind q) =
  asymLTCharKind kv kw p q

public export
irrLTQChar : {i : (CharKind, Nat)} -> (x : QChar v i) -> Not (LTQChar x x)
irrLTQChar x p = asymLTQChar x x p p

public export
transLTQChar : {i,j,k : (CharKind, Nat)}
            -> (x : QChar v i)
            -> (y : QChar w j)
            -> (z : QChar u k)
            -> LTQChar x y
            -> LTQChar y z
            -> LTQChar x z
transLTQChar {i = (xk, xi)} {j = (xk, yi)} {k = (xk, zi)} x y z (IsLTNat p) (IsLTNat q) =
  IsLTNat (transLTNat xi yi zi p q)
transLTQChar {i = (xk, xi)} {j = (xk, yi)} {k = (zk, zi)} x y z (IsLTNat p) (IsLTCharKind q) =
  IsLTCharKind q
transLTQChar {i = (xk, xi)} {j = (yk, yi)} {k = (yk, zi)} x y z (IsLTCharKind p) (IsLTNat q) =
  IsLTCharKind p
transLTQChar {i = (xk, xi)} {j = (yk, yi)} {k = (zk, zi)} x y z (IsLTCharKind p) (IsLTCharKind q) =
  IsLTCharKind (transLTCharKind xk yk zk p q)

-- [Decision Procedure] ---------------------------------------------------------------------------

export
decLTQChar : {i,j : (CharKind, Nat)}
          -> (x : QChar v i)
          -> (y : QChar w j)
          -> Dec (LTQChar x y)
decLTQChar {i = (ki,ni)} {j = (kj,nj)} x y with (trichoLTCharKind ki kj)
  decLTQChar {i = (ki,ni)} {j = (ki,nj)} x y | IsEq Refl with (decLTNat ni nj)
    decLTQChar {i = (ki,ni)} {j = (ki,nj)} x y | IsEq Refl | Yes lt = Yes (IsLTNat lt)
    decLTQChar {i = (ki,ni)} {j = (ki,nj)} x y | IsEq Refl | No gte = No (contra gte) where
      contra : {ki' : CharKind}
            -> {x' : QChar v' (ki', ni')}
            -> {y' : QChar w' (ki', nj')}
            -> (c0 : Not (LTNat ni' nj'))
            -> Not (LTQChar x' y')
      contra c0 (IsLTNat p) = c0 p
      contra {ki'} c0 (IsLTCharKind q) = irrLTCharKind ki' q
  decLTQChar {i = (ki,ni)} {j = (kj,nj)} x y | IsBinR_xRy p = Yes (IsLTCharKind p)
  decLTQChar {i = (ki,ni)} {j = (kj,nj)} x y | IsBinR_yRx q = No (contra q) where
    contra : {ki',kj' : CharKind}
          -> {x' : QChar v' (ki', ni')}
          -> {y' : QChar w' (kj', nj')}
          -> (q' : LTCharKind kj' ki')
          -> Not (LTQChar x' y')
    contra {ki'} {kj'=ki'} q' (IsLTNat p') = irrLTCharKind ki' q'
    contra {ki'} {kj'} q' (IsLTCharKind p') = asymLTCharKind ki' kj' p' q'

-- [Singleton] ------------------------------------------------------------------------------------

export
singLTQChar : {i,j : (CharKind, Nat)}
           -> (x : QChar v i) -> (y : QChar w j) -> (p,q : LTQChar x y) -> p = q
singLTQChar {i = (ki, ni)} {j = (ki, nj)} x y (IsLTNat p) (IsLTNat q) =
  rewrite singLTNat ni nj p q in Refl
singLTQChar {i = (ki, ni)} {j = (ki, nj)} x y (IsLTNat p) (IsLTCharKind q) with (irrLTCharKind ki q)
  singLTQChar {i = (ki, ni)} {j = (ki, nj)} x y (IsLTNat p) (IsLTCharKind q) | _ impossible
singLTQChar {i = (ki, ni)} {j = (ki, nj)} x y (IsLTCharKind p) (IsLTNat q) with (irrLTCharKind ki p)
  singLTQChar {i = (ki, ni)} {j = (ki, nj)} x y (IsLTCharKind p) (IsLTNat q) | _ impossible
singLTQChar {i = (ki, ni)} {j = (kj, nj)} x y (IsLTCharKind p) (IsLTCharKind q) =
  rewrite singLTCharKind ki kj p q in Refl
