module IdrisUtils.Data.String.AsNat

import public Data.Vect

%default total

---------------------------------------------------------------------------------------------------
-- [Helper Definition and Decision Proceudre] -----------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data AllNumeral : (xs : List Char) -> Type where
  Nil  : AllNumeral []
  (::) : Elem x ['0','1','2','3','4','5','6','7','8','9'] -> AllNumeral xs -> AllNumeral (x :: xs)

export
decAllNumeral : (xs : List Char) -> Dec (AllNumeral xs)
decAllNumeral [] = Yes Nil
decAllNumeral (x :: xs) with (isElem x ['0','1','2','3','4','5','6','7','8','9'])
  | No nnum = No (\(num :: _) => nnum num)
  | Yes num with (decAllNumeral xs)
    | No nnums = No (\(_ :: nums) => nnums nums)
    | Yes nums = Yes (num :: nums)

---------------------------------------------------------------------------------------------------
-- [Definition] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data StringAsNat : (s : String) -> (k : Nat) -> Type where
  MkNat : AllNumeral (unpack s) -> StringAsNat s (cast s)

---------------------------------------------------------------------------------------------------
-- [Decision Procedure] ---------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
decStringAsNat : (s : String) -> Dec (n : Nat ** StringAsNat s n)
decStringAsNat s with (decAllNumeral (unpack s))
  | No nnums = No (\(_ ** MkNat nums) => nnums nums)
  | Yes nums = Yes (cast s ** MkNat nums)
