module IdrisUtils.Data.Char.QChar.Base

import public IdrisUtils.Data.Char.CharKind

%default total

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------


||| Idris uses ASCII and that makes the natural numbers too large if you just `toNat` them.
|||
||| Let's try to be a bit more clever...
|||
||| The alternative is defining LT over Char pairwise which is going to be painful...
public export
data QChar : Char -> (CharKind, Nat) -> Type where
  C_ : QChar '_' (Sym, 0)
  C' : QChar '\'' (Sym, 1)
  Cstop : QChar '.' (Sym, 2)

  C0 : QChar '0' (Num, 0)
  C1 : QChar '1' (Num, 1)
  C2 : QChar '2' (Num, 2)
  C3 : QChar '3' (Num, 3)
  C4 : QChar '4' (Num, 4)
  C5 : QChar '5' (Num, 5)
  C6 : QChar '6' (Num, 6)
  C7 : QChar '7' (Num, 7)
  C8 : QChar '8' (Num, 8)
  C9 : QChar '9' (Num, 9)

  Ca : QChar 'a' (Min 1, 0)
  Cb : QChar 'b' (Min 1, 1)
  Cc : QChar 'c' (Min 1, 2)
  Cd : QChar 'd' (Min 1, 3)
  Ce : QChar 'e' (Min 1, 4)
  Cf : QChar 'f' (Min 1, 5)
  Cg : QChar 'g' (Min 1, 6)
  Ch : QChar 'h' (Min 1, 7)
  Ci : QChar 'i' (Min 1, 8)
  Cj : QChar 'j' (Min 1, 9)
  Ck : QChar 'k' (Min 2, 0)
  Cl : QChar 'l' (Min 2, 1)
  Cm : QChar 'm' (Min 2, 2)
  Cn : QChar 'n' (Min 2, 3)
  Co : QChar 'o' (Min 2, 4)
  Cp : QChar 'p' (Min 2, 5)
  Cq : QChar 'q' (Min 2, 6)
  Cr : QChar 'r' (Min 2, 7)
  Cs : QChar 's' (Min 2, 8)
  Ct : QChar 't' (Min 2, 9)
  Cu : QChar 'u' (Min 3, 0)
  Cv : QChar 'v' (Min 3, 1)
  Cw : QChar 'w' (Min 3, 2)
  Cx : QChar 'x' (Min 3, 3)
  Cy : QChar 'y' (Min 3, 4)
  Cz : QChar 'z' (Min 3, 5)

  CA : QChar 'A' (Maj 1, 0)
  CB : QChar 'B' (Maj 1, 1)
  CC : QChar 'C' (Maj 1, 2)
  CD : QChar 'D' (Maj 1, 3)
  CE : QChar 'E' (Maj 1, 4)
  CF : QChar 'F' (Maj 1, 5)
  CG : QChar 'G' (Maj 1, 6)
  CH : QChar 'H' (Maj 1, 7)
  CI : QChar 'I' (Maj 1, 8)
  CJ : QChar 'J' (Maj 1, 9)
  CK : QChar 'K' (Maj 2, 0)
  CL : QChar 'L' (Maj 2, 1)
  CM : QChar 'M' (Maj 2, 2)
  CN : QChar 'N' (Maj 2, 3)
  CO : QChar 'O' (Maj 2, 4)
  CP : QChar 'P' (Maj 2, 5)
  CQ : QChar 'Q' (Maj 2, 6)
  CR : QChar 'R' (Maj 2, 7)
  CS : QChar 'S' (Maj 2, 8)
  CT : QChar 'T' (Maj 2, 9)
  CU : QChar 'U' (Maj 3, 0)
  CV : QChar 'V' (Maj 3, 1)
  CW : QChar 'W' (Maj 3, 2)
  CX : QChar 'X' (Maj 3, 3)
  CY : QChar 'Y' (Maj 3, 4)
  CZ : QChar 'Z' (Maj 3, 5)

---------------------------------------------------------------------------------------------------
-- [DecEq] ----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
decEqQChar0 : (x, y : QChar v i) -> Dec (x = y)
decEqQChar0 C_ C_ = Yes Refl
decEqQChar0 C' C' = Yes Refl
decEqQChar0 Cstop Cstop = Yes Refl
decEqQChar0 C0 C0 = Yes Refl
decEqQChar0 C1 C1 = Yes Refl
decEqQChar0 C2 C2 = Yes Refl
decEqQChar0 C3 C3 = Yes Refl
decEqQChar0 C4 C4 = Yes Refl
decEqQChar0 C5 C5 = Yes Refl
decEqQChar0 C6 C6 = Yes Refl
decEqQChar0 C7 C7 = Yes Refl
decEqQChar0 C8 C8 = Yes Refl
decEqQChar0 C9 C9 = Yes Refl
decEqQChar0 Ca Ca = Yes Refl
decEqQChar0 Cb Cb = Yes Refl
decEqQChar0 Cc Cc = Yes Refl
decEqQChar0 Cd Cd = Yes Refl
decEqQChar0 Ce Ce = Yes Refl
decEqQChar0 Cf Cf = Yes Refl
decEqQChar0 Cg Cg = Yes Refl
decEqQChar0 Ch Ch = Yes Refl
decEqQChar0 Ci Ci = Yes Refl
decEqQChar0 Cj Cj = Yes Refl
decEqQChar0 Ck Ck = Yes Refl
decEqQChar0 Cl Cl = Yes Refl
decEqQChar0 Cm Cm = Yes Refl
decEqQChar0 Cn Cn = Yes Refl
decEqQChar0 Co Co = Yes Refl
decEqQChar0 Cp Cp = Yes Refl
decEqQChar0 Cq Cq = Yes Refl
decEqQChar0 Cr Cr = Yes Refl
decEqQChar0 Cs Cs = Yes Refl
decEqQChar0 Ct Ct = Yes Refl
decEqQChar0 Cu Cu = Yes Refl
decEqQChar0 Cv Cv = Yes Refl
decEqQChar0 Cw Cw = Yes Refl
decEqQChar0 Cx Cx = Yes Refl
decEqQChar0 Cy Cy = Yes Refl
decEqQChar0 Cz Cz = Yes Refl
decEqQChar0 CA CA = Yes Refl
decEqQChar0 CB CB = Yes Refl
decEqQChar0 CC CC = Yes Refl
decEqQChar0 CD CD = Yes Refl
decEqQChar0 CE CE = Yes Refl
decEqQChar0 CF CF = Yes Refl
decEqQChar0 CG CG = Yes Refl
decEqQChar0 CH CH = Yes Refl
decEqQChar0 CI CI = Yes Refl
decEqQChar0 CJ CJ = Yes Refl
decEqQChar0 CK CK = Yes Refl
decEqQChar0 CL CL = Yes Refl
decEqQChar0 CM CM = Yes Refl
decEqQChar0 CN CN = Yes Refl
decEqQChar0 CO CO = Yes Refl
decEqQChar0 CP CP = Yes Refl
decEqQChar0 CQ CQ = Yes Refl
decEqQChar0 CR CR = Yes Refl
decEqQChar0 CS CS = Yes Refl
decEqQChar0 CT CT = Yes Refl
decEqQChar0 CU CU = Yes Refl
decEqQChar0 CV CV = Yes Refl
decEqQChar0 CW CW = Yes Refl
decEqQChar0 CX CX = Yes Refl
decEqQChar0 CY CY = Yes Refl
decEqQChar0 CZ CZ = Yes Refl

export
implementation DecEq (QChar v i) where
  decEq = decEqQChar0

export
decEqQChar : {v,w : Char} -> {i,j : (CharKind, Nat)}
          -> (x : QChar v i) -> (y : QChar w j) -> Dec (x = y)
decEqQChar {v} {w} {i} {j} x y with (decEq v w)
  decEqQChar {v} {w} {i} {j} x y | No neq = No (contra neq) where
    contra : {x' : QChar v' i'} -> {y' : QChar w' j'} -> (c1 : Not (v' = w')) -> Not (x' = y')
    contra c1 Refl = c1 Refl
  decEqQChar {v} {w = v} {i} {j} x y | Yes Refl with (decEq i j)
    decEqQChar {v} {w = v} {i} {j} x y | Yes Refl | No neq = No (contra neq) where
      contra : {x' : QChar v' i'} -> {y' : QChar v' j'} -> (c1 : Not (i' = j')) -> Not (x' = y')
      contra c1 Refl = c1 Refl
    decEqQChar {v} {w = v} {i} {j = i} x y | Yes Refl | Yes Refl = decEqQChar0 x y

---------------------------------------------------------------------------------------------------
-- [Cast] -----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
fromCharQChar : (x : Char) -> Maybe (kn : (CharKind, Nat) ** (QChar x kn))
fromCharQChar '_' = Just ((Sym, 0) ** C_)
fromCharQChar '\'' = Just ((Sym, 1) ** C')
fromCharQChar '.' = Just ((Sym, 2) ** Cstop)
fromCharQChar '0' = Just ((Num, 0) ** C0)
fromCharQChar '1' = Just ((Num, 1) ** C1)
fromCharQChar '2' = Just ((Num, 2) ** C2)
fromCharQChar '3' = Just ((Num, 3) ** C3)
fromCharQChar '4' = Just ((Num, 4) ** C4)
fromCharQChar '5' = Just ((Num, 5) ** C5)
fromCharQChar '6' = Just ((Num, 6) ** C6)
fromCharQChar '7' = Just ((Num, 7) ** C7)
fromCharQChar '8' = Just ((Num, 8) ** C8)
fromCharQChar '9' = Just ((Num, 9) ** C9)
fromCharQChar 'a' = Just ((Min 1, 0) ** Ca)
fromCharQChar 'b' = Just ((Min 1, 1) ** Cb)
fromCharQChar 'c' = Just ((Min 1, 2) ** Cc)
fromCharQChar 'd' = Just ((Min 1, 3) ** Cd)
fromCharQChar 'e' = Just ((Min 1, 4) ** Ce)
fromCharQChar 'f' = Just ((Min 1, 5) ** Cf)
fromCharQChar 'g' = Just ((Min 1, 6) ** Cg)
fromCharQChar 'h' = Just ((Min 1, 7) ** Ch)
fromCharQChar 'i' = Just ((Min 1, 8) ** Ci)
fromCharQChar 'j' = Just ((Min 1, 9) ** Cj)
fromCharQChar 'k' = Just ((Min 2, 0) ** Ck)
fromCharQChar 'l' = Just ((Min 2, 1) ** Cl)
fromCharQChar 'm' = Just ((Min 2, 2) ** Cm)
fromCharQChar 'n' = Just ((Min 2, 3) ** Cn)
fromCharQChar 'o' = Just ((Min 2, 4) ** Co)
fromCharQChar 'p' = Just ((Min 2, 5) ** Cp)
fromCharQChar 'q' = Just ((Min 2, 6) ** Cq)
fromCharQChar 'r' = Just ((Min 2, 7) ** Cr)
fromCharQChar 's' = Just ((Min 2, 8) ** Cs)
fromCharQChar 't' = Just ((Min 2, 9) ** Ct)
fromCharQChar 'u' = Just ((Min 3, 0) ** Cu)
fromCharQChar 'v' = Just ((Min 3, 1) ** Cv)
fromCharQChar 'w' = Just ((Min 3, 2) ** Cw)
fromCharQChar 'x' = Just ((Min 3, 3) ** Cx)
fromCharQChar 'y' = Just ((Min 3, 4) ** Cy)
fromCharQChar 'z' = Just ((Min 3, 5) ** Cz)
fromCharQChar 'A' = Just ((Maj 1, 0) ** CA)
fromCharQChar 'B' = Just ((Maj 1, 1) ** CB)
fromCharQChar 'C' = Just ((Maj 1, 2) ** CC)
fromCharQChar 'D' = Just ((Maj 1, 3) ** CD)
fromCharQChar 'E' = Just ((Maj 1, 4) ** CE)
fromCharQChar 'F' = Just ((Maj 1, 5) ** CF)
fromCharQChar 'G' = Just ((Maj 1, 6) ** CG)
fromCharQChar 'H' = Just ((Maj 1, 7) ** CH)
fromCharQChar 'I' = Just ((Maj 1, 8) ** CI)
fromCharQChar 'J' = Just ((Maj 1, 9) ** CJ)
fromCharQChar 'K' = Just ((Maj 2, 0) ** CK)
fromCharQChar 'L' = Just ((Maj 2, 1) ** CL)
fromCharQChar 'M' = Just ((Maj 2, 2) ** CM)
fromCharQChar 'N' = Just ((Maj 2, 3) ** CN)
fromCharQChar 'O' = Just ((Maj 2, 4) ** CO)
fromCharQChar 'P' = Just ((Maj 2, 5) ** CP)
fromCharQChar 'Q' = Just ((Maj 2, 6) ** CQ)
fromCharQChar 'R' = Just ((Maj 2, 7) ** CR)
fromCharQChar 'S' = Just ((Maj 2, 8) ** CS)
fromCharQChar 'T' = Just ((Maj 2, 9) ** CT)
fromCharQChar 'U' = Just ((Maj 3, 0) ** CU)
fromCharQChar 'V' = Just ((Maj 3, 1) ** CV)
fromCharQChar 'W' = Just ((Maj 3, 2) ** CW)
fromCharQChar 'X' = Just ((Maj 3, 3) ** CX)
fromCharQChar 'Y' = Just ((Maj 3, 4) ** CY)
fromCharQChar 'Z' = Just ((Maj 3, 5) ** CZ)
fromCharQChar  _  = Nothing
