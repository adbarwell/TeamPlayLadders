module SearchEq

import public IdrisUtils.Error
import public Rewrite

%default total

---------------------------------------------------------------------------------------------------
-- [Search] ---------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
searchEq0 : (Show c, DecEq c)
         => {nvars : Nat}
         -> (depth : Nat)
         -> (e,f : AExp c nvars)
         -> (seen : List (AExp c nvars))
         -> ErrorOr (Rewrite e f)
searchEq0 Z e f t = Err (StdErr (show t))
searchEq0 (S d) e f t = bfs d t (gen e) where
  inChldn : {f : AExp c nvars}
         -> (chldn : List (h ** Rewrite e h)) -> ErrorOr (Rewrite e f)
  inChldn [] = Err (StdErr (show t))
  inChldn {f} ((h ** rw) :: rest) with (decEq h f)
    inChldn {f} ((f ** rw) :: rest) | Yes Refl = Just rw
    inChldn {f} ((h ** rw) :: rest) | No neq = inChldn rest

  getGndChldn : List (g ** Rewrite e g) -> List (h ** Rewrite e h)
  getGndChldn [] = []
  getGndChldn ((g ** rw) :: rest) =
    (map (\(h ** r) => (h ** Trans rw r)) (gen g)) ++ getGndChldn rest
  
  bfs : (depth : Nat)
     -> (seen : List (AExp c nvars))
     -> (xs : List (h ** Rewrite e h))
     -> ErrorOr (Rewrite e f)
  bfs Z seen xs = inChldn xs
  bfs (S k) seen xs with (inChldn xs)
    bfs (S k) seen xs | Err err = bfs k (seen ++ map fst xs) (getGndChldn xs)
    bfs (S k) seen xs | Just rw = Just rw

export
searchEq : (Show c, DecEq c)
        => {nvars : Nat} -> (depth : Nat) -> (e,f : AExp c nvars) -> ErrorOr (Rewrite e f)
searchEq d e f with (decEq e f)
  searchEq d e e | Yes Refl = Just Refl
  searchEq d e f | No neq = searchEq0 d e f []
