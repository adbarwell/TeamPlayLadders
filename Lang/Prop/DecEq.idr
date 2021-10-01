module Lang.Prop.DecEq

import public Lang.Base

%default total

---------------------------------------------------------------------------------------------------
-- [DecEq Implementations] ------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
implementation Uninhabited (Lit n = Var i) where
  uninhabited Refl impossible
export
implementation Uninhabited (Lit n = BinOp _ e f) where
  uninhabited Refl impossible
export
implementation Uninhabited (Lit n = UniOp _ e) where
  uninhabited Refl impossible
export
implementation Uninhabited (Var i = BinOp _ e f) where
  uninhabited Refl impossible
export
implementation Uninhabited (Var i = UniOp _ e) where
  uninhabited Refl impossible
export
implementation Uninhabited (BinOp _ e f = UniOp _ g) where
  uninhabited Refl impossible

export
congLit : (0 eq : Lit n = Lit m) -> n = m
congLit Refl = Refl

export
congVar : (0 eq : Var x = Var y) -> x = y
congVar Refl = Refl

export
congBinOp : (0 eq : BinOp p x y = BinOp q v w) -> (p = q, x = v, y = w)
congBinOp Refl = (Refl, Refl, Refl)

export
congUniOp : (0 eq : UniOp p x = UniOp q y) -> (p = q, x = y)
congUniOp Refl = (Refl, Refl)

export
decEqAExp : (decEqC : (v,w : c) -> Dec (v = w)) -> (x,y : AExp c nvars) -> Dec (x = y)
decEqAExp decEqC (Lit n) (Lit m) with (decEqC n m)
  decEqAExp decEqC (Lit n) (Lit n) | Yes Refl = Yes Refl
  decEqAExp decEqC (Lit n) (Lit m) | No neq_lit = No (\eq => neq_lit (congLit eq))
decEqAExp decEqC (Var v) (Var w) with (decEq v w)
  decEqAExp decEqC (Var w) (Var w) | Yes Refl = Yes Refl
  decEqAExp decEqC (Var v) (Var w) | No neq_var = No (\eq => neq_var (congVar eq))
decEqAExp decEqC (BinOp p e f) (BinOp q g h) with (decEq p q)
  decEqAExp decEqC (BinOp p e f) (BinOp q g h) | No neq_op = No (\eq => neq_op (fst (congBinOp eq)))
  decEqAExp decEqC (BinOp p e f) (BinOp p g h) | Yes Refl
    with (decEqAExp decEqC e g, decEqAExp decEqC f h)
      decEqAExp decEqC (BinOp p e g) (BinOp p e g) | Yes Refl | (Yes Refl, Yes Refl) = Yes Refl
      decEqAExp decEqC (BinOp p e f) (BinOp p g h) | Yes Refl | (_, No fNEQh) =
        No (\eq => fNEQh (snd (snd (congBinOp eq))))
      decEqAExp decEqC (BinOp p e f) (BinOp p g h) | Yes Refl | (No eNEQg, _) =
        No (\eq => eNEQg (fst (snd (congBinOp eq))))
decEqAExp decEqC (UniOp p e) (UniOp q f) with (decEq p q)
  decEqAExp decEqC (UniOp p e) (UniOp q f) | No neq_op = No (\eq => neq_op (fst (congUniOp eq)))
  decEqAExp decEqC (UniOp p e) (UniOp p f) | Yes Refl with (decEqAExp decEqC e f)
    decEqAExp decEqC (UniOp p e) (UniOp p f) | Yes Refl | No neq_ef =
      No (\eq => neq_ef (snd (congUniOp eq)))
    decEqAExp decEqC (UniOp p e) (UniOp p e) | Yes Refl | Yes Refl = Yes Refl
decEqAExp decEqC (Lit n) (Var v) = No absurd
decEqAExp decEqC (Lit n) (BinOp op e f) = No absurd
decEqAExp decEqC (Lit n) (UniOp op e) = No absurd
decEqAExp decEqC (Var v) (Lit n) = No (\eq => absurd (sym eq))
decEqAExp decEqC (Var v) (BinOp op e f) = No absurd
decEqAExp decEqC (Var v) (UniOp op e) = No absurd
decEqAExp decEqC (BinOp op e f) (Lit n) = No (\eq => absurd (sym eq))
decEqAExp decEqC (BinOp op e f) (Var v) = No (\eq => absurd (sym eq))
decEqAExp decEqC (BinOp p e f) (UniOp q g) = No absurd
decEqAExp decEqC (UniOp op e) (Lit n) = No (\eq => absurd (sym eq))
decEqAExp decEqC (UniOp op e) (Var _) = No (\eq => absurd (sym eq))
decEqAExp decEqC (UniOp op e) (BinOp _ _ _) = No (\eq => absurd (sym eq))

export
implementation DecEq c => DecEq (AExp c nvars) where
  decEq = decEqAExp decEq

---------------------------------------------------------------------------------------------------
-- [Eq Implementations] ---------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
implementation DecEq c => Eq (AExp c nvars) where
  e == f with (decEqAExp decEq e f)
    e == e | Yes Refl = True
    e == f | No _ = False

