module SearchSt

import public IdrisUtils.Error
import public Rewrite
import public Lang.Substitution
import public Lang.Prop.DecEq
import public SearchEq
import public Generalise


%default total

---------------------------------------------------------------------------------------------------
-- [Search] ---------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
searchSt0 : (Show c, DecEq c)
         => {nvars : Nat}
         -> (depth : Nat)
         -> (e,f : AExp c nvars)
         -> (seen : List (AExp c nvars))
         -> ErrorOr (g ** (Rewrite e g, SubTerm f g))
searchSt0 Z e f t = Err (StdErr (show t))
searchSt0 (S d) e f t = bfs d t (gen e) where
  inChldn : {f : AExp c nvars}
         -> (chldn : List (h ** Rewrite e h)) -> ErrorOr (g ** (Rewrite e g, SubTerm f g))
  inChldn [] = Err (StdErr (show t))
  inChldn {f} ((h ** rw) :: rest) with (decSubTerm f h)
    inChldn {f} ((h ** rw) :: rest) | Yes st = Just (h ** (rw, st))
    inChldn {f} ((h ** rw) :: rest) | No neq = inChldn rest

  getGndChldn : List (g ** Rewrite e g) -> List (h ** Rewrite e h)
  getGndChldn [] = []
  getGndChldn ((g ** rw) :: rest) =
    (map (\(h ** r) => (h ** Trans rw r)) (gen g)) ++ getGndChldn rest
  
  bfs : (depth : Nat)
     -> (seen : List (AExp c nvars))
     -> (xs : List (h ** Rewrite e h))
     -> ErrorOr (g ** (Rewrite e g, SubTerm f g))
  bfs Z seen xs = inChldn xs
  bfs (S k) seen xs with (inChldn xs)
    bfs (S k) seen xs | Err err = bfs k (seen ++ map fst xs) (getGndChldn xs)
    bfs (S k) seen xs | Just rw = Just rw

export
searchSt : (Show c, DecEq c)
        => {nvars : Nat} 
        -> (depth : Nat) 
        -> (x : AExp c nvars)
        -> (a,b : AExp c nvars)
        -> (e,f : AExp c nvars)
        -> ErrorOr (g ** (Rewrite a b, Rewrite e g, SubTerm f g, (g' ** Eq3 g g')))
searchSt d x a b e f with (searchEq d a b)
  searchSt d x a b e f | Just eqn1 with (decEq e f)
    searchSt d x a b e e | Just eqn1 | Yes Refl = 
      case swapE x e e of 
        g' => 
         let p1 = elemL e e 
             p2 = elemL x g'
             p3 = elemL x e 
             p4 = elemL e g'
         in 
          case (decEq (toElemSimple p1) (toElemSimple p2)) of 
                Yes prf =>
                  case (decEq (toElemSimple p3) (toElemSimple p4)) of
                    Yes prf2 => 
                      case searchEq d e g' of
                        Just gPrf => Just (e ** (eqn1, Refl, Refl, (g' ** MkEq3 p1 p2 prf p3 p4 prf2 gPrf)))
                        Err err   => Err err
                    No contra2 => Err ?hole3
                No contra => ?hole2
    searchSt d x a b e f | Just eqn1 | No neq with (searchSt0 d e f [])
      searchSt d x a b e f | Just eqn1 | No neq | Just (e' ** (eqn2, sub)) =
        case swapE x f e' of 
          g' => 
            let p1 = elemL f e' 
                p2 = elemL x g' 
                p3 = elemL x e' 
                p4 = elemL f g'
            in
              case (decEq (toElemSimple p1) (toElemSimple p2)) of 
                Yes prf =>
                  case (decEq (toElemSimple p3) (toElemSimple p4)) of
                    Yes prf2 => 
                      case searchEq d e' g' of
                        Just gPrf => Just (e' ** (eqn1, eqn2, sub, (g' ** MkEq3 p1 p2 prf p3 p4 prf2 gPrf)))
                        Err err   => Err err
                    No contra2 => Err ?hole33
                No contra => Err (TyErr ((toElemSimple p1),(toElemSimple p2)))


-- Just (e' ** (eqn1, eqn2, sub))
      searchSt d x a b e f | Just eqn1 | No neq | Err err2 = Err err2 
  searchSt d x a b e f | Err err = Err err

{-
  MkEq3 :  
           (p1:  ElemLamA lam g)
        -> (p2 : ElemLamA x g')
        -> (p3 : toElemSimple p1 = toElemSimple p2)
        -> (p4 : ElemLamA x g)
        -> (p5 : ElemLamA lam g')
        -> (p6 : toElemSimple p4 = toElemSimple p5)
        -> Rewrite g g'
        -> Eq3 g g'
-}

{-
  data AExp : (c : Type) -> (nvars : Nat) -> Type where
    Lit : (n : c) -> AExp c nvars
    Var : (x : Fin nvars) -> AExp c nvars
    BinOp : (op : BOp) -> (e1,e2 : AExp c nvars) -> AExp c nvars
    UniOp : (op : UOp) -> (e1 : AExp c nvars) -> AExp c nvars
  -}




---------------------------------------------------------------------------------------------------
-- [Experimental Search] --------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data Flip : (var : Fin nvars) -> (x,y,st,f1,f2 : AExp c nvars) -> Type where
  |||
  ||| @p1   st is a subterm in f1 (points to one occurrence in f1)
  ||| @p2   (Var v) is a subterm in f2 (points to all occurrences in f2)
  ||| @q1   f2 = f1[st -> y], where y ≠ Var v
  ||| @q2   f3 = f2[Var v -> x]
  MkFlip : (p1 : SubTerm st f1)
        -> (p2 : SubTermAll (Var v) f2)
        -> (q0 : Not (y = Var v))
        -> (q1 : SubstituteOne y f1 f2 p1)
        -> (q2 : SubstituteAll x f2 f3 p2)
        -> Flip v x y st f1 f3

||| Find some f1 and f2 that are equivalent to the expression og s.t. f1 has st as a subterm, and
||| f2 = f1[Var v -> x; st -> y]
searchSt1 : (Show c, DecEq c)
         => {nvars : Nat} -> (depth : Nat) -> (v : Fin nvars) -> (og,st,x,y : AExp c nvars)
         -> ErrorOr (f1 ** (f2 ** (Rewrite og f1, Rewrite og f2, Flip v x y st f1 f2)))
