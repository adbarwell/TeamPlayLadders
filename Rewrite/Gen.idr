module Rewrite.Gen

import public Rewrite.Base

%default total

---------------------------------------------------------------------------------------------------
-- [ARewrite] -------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
genAAssoc : DecEq c
         => (ok : IsAssociative op)
         -> (e,f : AExp c nvars)
         -> List (g : AExp c nvars ** Either (ARewrite (BinOp op e f) g) (ARewrite g (BinOp op e f)))
genAAssoc PlusIsAssoc (Lit _) f = []
genAAssoc PlusIsAssoc (Var _) f = []
genAAssoc PlusIsAssoc (UniOp _ _) f = []
genAAssoc PlusIsAssoc (BinOp Plus g h) f =
  [(BinOp Plus g (BinOp Plus h f) ** Right (Associative PlusIsAssoc))]
genAAssoc PlusIsAssoc (BinOp Mult _ _) f = []
genAAssoc MultIsAssoc (Lit _) f = []
genAAssoc MultIsAssoc (Var _) f = []
genAAssoc MultIsAssoc (UniOp _ _) f = []
genAAssoc MultIsAssoc (BinOp Plus g h) f = []
genAAssoc MultIsAssoc (BinOp Mult g h) f =
  [(BinOp Mult g (BinOp Mult h f) ** Right (Associative MultIsAssoc))]

genAAssoc PlusIsAssoc e (Lit _) = []
genAAssoc PlusIsAssoc e (Var _) = []
genAAssoc PlusIsAssoc e (UniOp _ _) = []
genAAssoc PlusIsAssoc e (BinOp Plus g h) =
  [(BinOp Plus (BinOp Plus e g) h ** Left (Associative PlusIsAssoc))]
genAAssoc PlusIsAssoc e (BinOp Mult _ _) = []
genAAssoc MultIsAssoc e (Lit _) = []
genAAssoc MultIsAssoc e (Var _) = []
genAAssoc MultIsAssoc e (UniOp _ _) = []
genAAssoc MultIsAssoc e (BinOp Plus g h) = []
genAAssoc MultIsAssoc e (BinOp Mult g h) =
  [(BinOp Mult (BinOp Mult e g) h ** Left (Associative MultIsAssoc))]

||| Given an expression, e, return all expressions, f, that are reachable via ARewrite.
|||
||| TODO: Do we need a proof that genA produces *all* reachable expressions?
export
genA : DecEq c => (e : AExp c nvars) -> List (f ** (Either (ARewrite e f) (ARewrite f e)))
genA (Lit _) = []
genA (Var _) = []
genA (UniOp Neg e) = []
genA (UniOp Square e) = [(BinOp Mult e e ** Left SqIsMult)]
genA (BinOp Plus e f) =
  (BinOp Plus f e ** Left (Commutative PlusIsComm)) :: genAAssoc PlusIsAssoc e f
genA (BinOp Mult e f) =
  ((BinOp Mult f e ** Left (Commutative MultIsComm)) :: genAAssoc MultIsAssoc e f) ++
    case decEq e f of
      No neq => []
      Yes Refl => [(UniOp Square e ** Right SqIsMult)]

---------------------------------------------------------------------------------------------------
-- [Rewrite] --------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
fromAtomic : (r : Either (ARewrite e f) (ARewrite f e)) -> Rewrite e f
fromAtomic (Left r) = Fun r
fromAtomic (Right r) = Sym (Fun r)

export
genCongRW : DecEq c => (e : AExp c nvars) -> List (f : AExp c nvars ** Rewrite e f)
genCongRW (Lit n) = []
genCongRW (Var i) = []
genCongRW (UniOp op e) =
  map (\(f ** rw) => (UniOp op f ** CongU (fromAtomic rw))) (genA e) ++
  map (\(f ** rw) => (UniOp op f ** CongU rw)) (genCongRW e)
genCongRW (BinOp op e f) =
  map (\(g ** rw) => (BinOp op g f ** CongB1 (fromAtomic rw))) (genA e) ++
  map (\(g ** rw) => (BinOp op e g ** CongB2 (fromAtomic rw))) (genA f) ++
  congL ++ congR
    where
      congL : List (g' : AExp c nvars ** Rewrite (BinOp op e f) g')
      congL = map (\(g ** rw) => (BinOp op g f ** CongB1 rw)) (genCongRW e)
      
      congR : List (g' : AExp c nvars ** Rewrite (BinOp op e f) g')
      congR = map (\(g ** rw) => (BinOp op e g ** CongB2 rw)) (genCongRW f)

export
gen : DecEq c => (e : AExp c nvars) -> List (f : AExp c nvars ** Rewrite e f)
gen e = map (\(f ** rw) => (f ** fromAtomic rw)) (genA e) ++
        genCongRW e

