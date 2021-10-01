module Rewrite.Base

import public Lang

%default total

---------------------------------------------------------------------------------------------------
-- [Rewrite] --------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Rewrite rules.
public export
data ARewrite : (e, f : AExp c nvars) -> Type where
  SqIsMult : ARewrite (UniOp Square e) (BinOp Mult e e)
  Commutative : {op : BOp} -> IsCommutative op -> ARewrite (BinOp op e f) (BinOp op f e)
  Associative : {op : BOp} -> IsAssociative op
             -> ARewrite (BinOp op e (BinOp op f g)) (BinOp op (BinOp op e f) g)

||| Reflexive-Symmetric-Transitive Closure of ARewrite
public export
data Rewrite : (e,f : AExp c nvars) -> Type where
  Refl  : Rewrite e e
  Fun   : ARewrite e f -> Rewrite e f
  Sym   : Rewrite f e -> Rewrite e f
  Trans : {f : AExp c nvars} -> Rewrite e f -> Rewrite f g -> Rewrite e g

  CongU  : Rewrite e f -> Rewrite (UniOp op e) (UniOp op f)
  CongB1 : Rewrite e f -> Rewrite (BinOp op e g) (BinOp op f g)
  CongB2 : Rewrite f g -> Rewrite (BinOp op e f) (BinOp op e g)
