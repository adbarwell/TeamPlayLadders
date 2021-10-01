module IdrisUtils.Data.String.AsSInt

import public Data.Vect

import public IdrisUtils.Data.Integer.SInt
import public IdrisUtils.Data.String.AsNat

%default total

---------------------------------------------------------------------------------------------------
-- [Helper Definition and Decision Proceudre] -----------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data SignAllNumeral : (xs : List Char) -> Type where
  Vacuous : SignAllNumeral []
  Pos : (nums : AllNumeral (x :: xs)) -> SignAllNumeral (x :: xs)
  Neg : (nums : AllNumeral xs) -> SignAllNumeral ('-' :: xs)

decSignAllNumeral : (xs : List Char) -> Dec (SignAllNumeral xs)
decSignAllNumeral [] = Yes Vacuous
decSignAllNumeral (x :: xs) with (decAllNumeral xs)
  decSignAllNumeral (x :: xs) | No nnums = No (contra nnums) where
    contra : (c1 : Not (AllNumeral xs')) -> Not (SignAllNumeral (x' :: xs'))
    contra c1 (Pos (num :: nums)) = c1 nums
    contra c1 (Neg nums) = c1 nums
  decSignAllNumeral (x :: xs) | Yes nums with (decEq x '-')
    decSignAllNumeral (x :: xs) | Yes nums | No neq
      with (isElem x ['0','1','2','3','4','5','6','7','8','9'])
        decSignAllNumeral (x :: xs) | Yes nums | No neq | No nnum = No (contra neq nnum) where
          contra : (c1 : Not (x' = '-'))
                -> (c2 : Not (Elem x' ['0','1','2','3','4','5','6','7','8','9']))
                -> Not (SignAllNumeral (x' :: xs'))
          contra c1 c2 (Pos (num :: nums)) = c2 num
          contra c1 c2 (Neg nums) = c1 Refl
        decSignAllNumeral (x :: xs) | Yes nums | No neq | Yes num = Yes (Pos (num :: nums))
    decSignAllNumeral (x :: xs) | Yes nums | Yes eq = Yes (rewrite eq in Neg nums)

totalTest : (x : Char) -> Dec (x = 'b')
totalTest x = decEq x 'b'

---------------------------------------------------------------------------------------------------
-- [Definition] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data StringAsSInt : (s : String) -> (k : SInt) -> Type where
  MkNat : AllSignNumeral (unpack s) -> StringAsSInt s (cast s)

---------------------------------------------------------------------------------------------------
-- [Decision Procedure] ---------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
decStringAsSInt : (s : String) -> Dec (n : SInt ** StringAsSInt s n)
decStringAsSInt s with (decSignAllNumeral (unpack s))
  | No nnums = No (\(_ ** MkNat nums) => nnums nums)
  | Yes nums = Yes (cast s ** MkNat nums)
