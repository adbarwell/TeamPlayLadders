module Lang.Prop.TotalOrdering

import public Lang.Base
import public Lang.Prop.DecEq

%default total

---------------------------------------------------------------------------------------------------
-- [Total Ordering] -------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data LTAExp : (x,y : AExp) -> Type where
  LitLTLit      : (lt : LTNat n m) -> LTAExp (Lit n) (Lit m)
  LitLTVar      : LTAExp (Lit n) (Var v)
  LitLTBinOp    : LTAExp (Lit n) (BinOp op e f)
  LitLTUniOp    : LTAExp (Lit n) (UniOp op e)
  VarLTVar      : (lt : LTPString v w) -> LTAExp (Var v) (Var w)
  VarLTBinOp    : LTAExp (Var v) (BinOp op e f)
  VarLTUniOp    : LTAExp (Var v) (UniOp op e)
  BinOpLTBinOpF : (pLTq : LTBOp p q) -> LTAExp (BinOp p e f) (BinOp q g h)
  BinOpLTBinOpL : (eLTg : LTAExp e g) -> LTAExp (BinOp op e f) (BinOp op g h)
  BinOpLTBinOpR : (fLTh : LTAExp f h) -> LTAExp (BinOp op e f) (BinOp op e h)
  BinOpLTUniOp  : LTAExp (BinOp op e f) (UniOp _ g)
  UniOpLTUniOpF : (lt : LTUOp p q) -> LTAExp (UniOp p e) (UniOp q f)
  UniOpLTUniOpL : (lt : LTAExp e f) -> LTAExp (UniOp op e) (UniOp op f)

-- [Decision Procedure] ---------------------------------------------------------------------------

{-
export
implementation Uninhabited (LTAExp (Var _) (Lit _)) where
  uninhabited _ impossible
export
implementation Uninhabited (LTAExp (BinOp _ _ _) (Lit _)) where
  uninhabited _ impossible
export
implementation Uninhabited (LTAExp (BinOp _ _ _) (Var _)) where
  uninhabited _ impossible
export
implementation Uninhabited (LTAExp (UniOp _ _) (Lit _)) where
  uninhabited _ impossible
export
implementation Uninhabited (LTAExp (UniOp _ _) (Var _)) where
  uninhabited _ impossible
export
implementation Uninhabited (LTAExp (UniOp _ _) (BinOp _ _ _)) where
  uninhabited _ impossible

export
decLTAExp : (x,y : AExp) -> Dec (LTAExp x y)
decLTAExp (Lit n) (Lit m) with (decLTNat n m)
  decLTAExp (Lit n) (Lit m) | Yes lt = Yes (LitLTLit lt)
  decLTAExp (Lit n) (Lit m) | No gte = No (\(LitLTLit lt) => gte lt)
decLTAExp (Lit n) (Var v) = Yes LitLTVar
decLTAExp (Lit n) (BinOp op e f) = Yes LitLTBinOp
decLTAExp (Lit n) (UniOp op e) = Yes LitLTUniOp
decLTAExp (Var v) (Lit m) = No absurd
decLTAExp (Var v) (Var w) with (decLTPString v w)
  decLTAExp (Var v) (Var w) | Yes lt = Yes (VarLTVar lt)
  decLTAExp (Var v) (Var w) | No gte = No (\(VarLTVar lt) => gte lt)
decLTAExp (Var v) (BinOp _ _ _) = Yes VarLTBinOp
decLTAExp (Var v) (UniOp _ _) = Yes VarLTUniOp
decLTAExp (BinOp p e f) (Lit v) = No absurd
decLTAExp (BinOp p e f) (Var v) = No absurd
decLTAExp (BinOp p e f) (BinOp q g h) with (trichoLTOp p q)
  decLTAExp (BinOp p e f) (BinOp q g h) | IsBinR_yRx s nr neq = No (absurd_0 s nr neq) where
    absurd_0 : (s'   : LTOp q' p')
            -> (nr'  : Not (LTOp p' q'))
            -> (neq' : Not (p' = q'))
            -> Not (LTAExp (BinOp p' e' f') (BinOp q' g' h'))
    absurd_0 s' c1 c2 (BinOpLTBinOpF lt) = c1 lt
    absurd_0 s' c1 c2 (BinOpLTBinOpL lt) = c2 Refl
    absurd_0 s' c1 c2 (BinOpLTBinOpR lt) = c2 Refl
  decLTAExp (BinOp p e f) (BinOp q g h) | IsBinR_xRy r ns neq = Yes (BinOpLTBinOpF r)
  decLTAExp (BinOp p e f) (BinOp p g h) | IsEq irr with (decLTAExp e g)
    decLTAExp (BinOp p e f) (BinOp p g h) | IsEq irr | Yes lt_l = Yes (BinOpLTBinOpL lt_l)
    decLTAExp (BinOp p e f) (BinOp p g h) | IsEq irr | No gte_l with (decLTAExp f h)
      decLTAExp (BinOp p e f) (BinOp p g h) | IsEq irr | No gte_l | Yes lt_r with (decEq e g)
        decLTAExp (BinOp p e f) (BinOp p e h) | IsEq irr | No gte_l | Yes lt_r | Yes Refl =
          Yes (BinOpLTBinOpR lt_r)
        decLTAExp (BinOp p e f) (BinOp p g h) | IsEq irr | No gte_l | Yes lt_r | No neq =
          No (absurd_1 irr gte_l neq) where
            absurd_1 : (c1 : Not (LTOp p' p'))
                    -> (c2 : Not (LTAExp e' g'))
                    -> (c3 : Not (e' = g'))
                    -> Not (LTAExp (BinOp p' e' f') (BinOp p' g' h'))
            absurd_1 c1 c2 c3 (BinOpLTBinOpF lt) = c1 lt
            absurd_1 c1 c2 c3 (BinOpLTBinOpL lt) = c2 lt
            absurd_1 c1 c2 c3 (BinOpLTBinOpR lt) = c3 Refl
      decLTAExp (BinOp p e f) (BinOp p g h) | IsEq irr | No gte_l | No gte_r =
        No (absurd_2 irr gte_l gte_r) where
          absurd_2 : (c1 : Not (LTOp p' p'))
                  -> (c2 : Not (LTAExp e' g'))
                  -> (c3 : Not (LTAExp f' h'))
                  -> Not (LTAExp (BinOp p' e' f') (BinOp p' g' h'))
          absurd_2 c1 c2 c3 (BinOpLTBinOpF lt) = c1 lt
          absurd_2 c1 c2 c3 (BinOpLTBinOpL lt) = c2 lt
          absurd_2 c1 c2 c3 (BinOpLTBinOpR lt) = c3 lt
decLTAExp (BinOp p e f) (UniOp q g) = Yes (BinOpLTUniOp)
decLTAExp (UniOp op e) (Lit m) = No absurd
decLTAExp (UniOp op e) (Var v) = No absurd
decLTAExp (UniOp p e) (BinOp q f g) = No absurd
decLTAExp (UniOp p e) (UniOp q f) with (trichoLTUOp p q)
  decLTAExp (UniOp p e) (UniOp q f) | IsBinR_xRy r ns neq = Yes (UniOpLTUniOpF r)
  decLTAExp (UniOp p e) (UniOp q f) | IsBinR_yRx s nr neq = No (absurd_0 s nr neq) where
    absurd_0 : (c1 : LTUOp q' p')
            -> (c2 : Not (LTUOp p' q'))
            -> (c3 : Not (p' = q'))
            -> Not (LTAExp (UniOp p' e') (UniOp q' f'))
    absurd_0 c1 c2 c3 (UniOpLTUniOpF lt) = c2 lt
    absurd_0 c1 c2 c3 (UniOpLTUniOpL lt) = c3 Refl
  decLTAExp (UniOp p e) (UniOp p f) | IsEq irr with (decLTAExp e f)
    decLTAExp (UniOp p e) (UniOp p f) | IsEq irr | No gte = No (absurd_0 irr gte) where
      absurd_0 : (c1 : Not (LTUOp p' p'))
              -> (c2 : Not (LTAExp e' f'))
              -> Not (LTAExp (UniOp p' e') (UniOp p' f'))
      absurd_0 c1 c2 (UniOpLTUniOpF lt) = c1 lt
      absurd_0 c1 c2 (UniOpLTUniOpL lt) = c2 lt
    decLTAExp (UniOp p e) (UniOp p f) | IsEq irr | Yes lt = Yes (UniOpLTUniOpL lt)

-- [Asymmetry] ------------------------------------------------------------------------------------

asymLTAExp : (x,y : AExp) -> (p : LTAExp x y) -> Not (LTAExp y x)
asymLTAExp (Lit x) (Lit y) (LitLTLit p) (LitLTLit q) = asymLTNat x y p q
asymLTAExp (Var x) (Var y) (VarLTVar p) (VarLTVar q) = asymLTPString x y p q
asymLTAExp (BinOp r e f) (BinOp s g h) (BinOpLTBinOpF p) (BinOpLTBinOpF q) = asymLTOp r s p q
asymLTAExp (BinOp r e f) (BinOp r g h) (BinOpLTBinOpF p) (BinOpLTBinOpL q) = irreflLTOp r p
asymLTAExp (BinOp r e f) (BinOp r e h) (BinOpLTBinOpF p) (BinOpLTBinOpR q) = irreflLTOp r p
asymLTAExp (BinOp r e f) (BinOp r g h) (BinOpLTBinOpL p) (BinOpLTBinOpF q) = irreflLTOp r q
asymLTAExp (BinOp r e f) (BinOp r g h) (BinOpLTBinOpL p) (BinOpLTBinOpL q) = asymLTAExp e g p q
asymLTAExp (BinOp r e f) (BinOp r e h) (BinOpLTBinOpL p) (BinOpLTBinOpR q) = asymLTAExp e e p p
asymLTAExp (BinOp r e f) (BinOp r e h) (BinOpLTBinOpR p) (BinOpLTBinOpF q) = irreflLTOp r q
asymLTAExp (BinOp r e f) (BinOp r e h) (BinOpLTBinOpR p) (BinOpLTBinOpL q) = asymLTAExp e e q q
asymLTAExp (BinOp r e f) (BinOp r e h) (BinOpLTBinOpR p) (BinOpLTBinOpR q) = asymLTAExp f h p q
asymLTAExp (UniOp r e) (UniOp s f) (UniOpLTUniOpF p) (UniOpLTUniOpF q) = asymLTUOp r s p q
asymLTAExp (UniOp r e) (UniOp r f) (UniOpLTUniOpF p) (UniOpLTUniOpL q) = irreflLTUOp r p
asymLTAExp (UniOp r e) (UniOp r f) (UniOpLTUniOpL p) (UniOpLTUniOpF q) = irreflLTUOp r q
asymLTAExp (UniOp r e) (UniOp r f) (UniOpLTUniOpL p) (UniOpLTUniOpL q) = asymLTAExp e f p q

irreflLTAExp : (x : AExp) -> Not (LTAExp x x)
irreflLTAExp x p = asymLTAExp x x p p

-- [Transitivity] ---------------------------------------------------------------------------------

transLTAExp : (x,y,z : AExp) -> (p : LTAExp x y) -> (q : LTAExp y z) -> LTAExp x z
transLTAExp (Lit x) (Lit y) (Lit z) (LitLTLit p) (LitLTLit q) = LitLTLit (transLTNat x y z p q)
transLTAExp (Lit x) (Lit y) (Var z) (LitLTLit p) LitLTVar = LitLTVar
transLTAExp (Lit x) (Lit y) (BinOp op e f) (LitLTLit p) LitLTBinOp = LitLTBinOp
transLTAExp (Lit x) (Lit y) (UniOp op e) (LitLTLit p) LitLTUniOp = LitLTUniOp
transLTAExp (Lit x) (Var y) _ LitLTVar (VarLTVar q) = LitLTVar
transLTAExp (Lit x) (Var y) _ LitLTVar VarLTBinOp = LitLTBinOp
transLTAExp (Lit x) (Var y) _ LitLTVar VarLTUniOp = LitLTUniOp
transLTAExp (Lit x) (BinOp op e f) _ LitLTBinOp (BinOpLTBinOpF _) = LitLTBinOp
transLTAExp (Lit x) (BinOp op e f) _ LitLTBinOp (BinOpLTBinOpL _) = LitLTBinOp
transLTAExp (Lit x) (BinOp op e f) _ LitLTBinOp (BinOpLTBinOpR _) = LitLTBinOp
transLTAExp (Lit x) (BinOp op e f) _ LitLTBinOp BinOpLTUniOp = LitLTUniOp
transLTAExp (Lit x) (UniOp op e) _ LitLTUniOp (UniOpLTUniOpF _) = LitLTUniOp
transLTAExp (Lit x) (UniOp op e) _ LitLTUniOp (UniOpLTUniOpL _) = LitLTUniOp
transLTAExp (Var x) (Var y) (Var z) (VarLTVar p) (VarLTVar q) = VarLTVar (transLTPString x y z p q)
transLTAExp (Var x) (Var y) (BinOp r e f) (VarLTVar p) VarLTBinOp = VarLTBinOp
transLTAExp (Var x) (Var y) (UniOp op e) (VarLTVar p) VarLTUniOp = VarLTUniOp
transLTAExp (Var x) (BinOp r e f) (BinOp s g h) VarLTBinOp (BinOpLTBinOpF q) = VarLTBinOp
transLTAExp (Var x) (BinOp r e f) (BinOp r g h) VarLTBinOp (BinOpLTBinOpL q) = VarLTBinOp
transLTAExp (Var x) (BinOp r e f) (BinOp r e h) VarLTBinOp (BinOpLTBinOpR q) = VarLTBinOp
transLTAExp (Var x) (BinOp r e f) (UniOp s g) VarLTBinOp BinOpLTUniOp = VarLTUniOp
transLTAExp (Var x) (UniOp r e) (UniOp q f) VarLTUniOp _ = VarLTUniOp
transLTAExp (BinOp r e f) (BinOp s g h) (BinOp t i j) (BinOpLTBinOpF p) (BinOpLTBinOpF q) =
  BinOpLTBinOpF (transLTOp r s t p q)
transLTAExp (BinOp r e f) (BinOp s g h) (BinOp s i j) (BinOpLTBinOpF p) (BinOpLTBinOpL q) =
  BinOpLTBinOpF p
transLTAExp (BinOp r e f) (BinOp s g h) (BinOp s g j) (BinOpLTBinOpF p) (BinOpLTBinOpR q) =
  BinOpLTBinOpF p
transLTAExp (BinOp r e f) (BinOp s g h) (UniOp t i) (BinOpLTBinOpF p) BinOpLTUniOp = BinOpLTUniOp
transLTAExp (BinOp r e f) (BinOp r g h) (BinOp t i j) (BinOpLTBinOpL p) (BinOpLTBinOpF q) =
  BinOpLTBinOpF q
transLTAExp (BinOp r e f) (BinOp r g h) (BinOp r i j) (BinOpLTBinOpL p) (BinOpLTBinOpL q) =
  BinOpLTBinOpL (transLTAExp e g i p q)
transLTAExp (BinOp r e f) (BinOp r g h) (BinOp r g j) (BinOpLTBinOpL p) (BinOpLTBinOpR q) =
  BinOpLTBinOpL p
transLTAExp (BinOp r e f) (BinOp r g h) (UniOp s i) (BinOpLTBinOpL p) BinOpLTUniOp = BinOpLTUniOp
transLTAExp (BinOp r e f) (BinOp r e h) (BinOp t i j) (BinOpLTBinOpR p) (BinOpLTBinOpF q) =
  BinOpLTBinOpF q
transLTAExp (BinOp r e f) (BinOp r e h) (BinOp r i j) (BinOpLTBinOpR p) (BinOpLTBinOpL q) =
  BinOpLTBinOpL q
transLTAExp (BinOp r e f) (BinOp r e h) (BinOp r e j) (BinOpLTBinOpR p) (BinOpLTBinOpR q) =
  BinOpLTBinOpR (transLTAExp f h j p q)
transLTAExp (BinOp r e f) (BinOp r e h) (UniOp s i) (BinOpLTBinOpR p) BinOpLTUniOp = BinOpLTUniOp
transLTAExp (BinOp r e f) (UniOp s g) (UniOp t h) BinOpLTUniOp _ = BinOpLTUniOp
transLTAExp (UniOp r e) (UniOp s f) (UniOp t g) (UniOpLTUniOpF p) (UniOpLTUniOpF q) =
  UniOpLTUniOpF (transLTUOp r s t p q)
transLTAExp (UniOp r e) (UniOp s f) (UniOp s g) (UniOpLTUniOpF p) (UniOpLTUniOpL q) =
  UniOpLTUniOpF p
transLTAExp (UniOp r e) (UniOp r f) (UniOp s g) (UniOpLTUniOpL p) (UniOpLTUniOpF q) =
  UniOpLTUniOpF q
transLTAExp (UniOp r e) (UniOp r f) (UniOp r g) (UniOpLTUniOpL p) (UniOpLTUniOpL q) =
  UniOpLTUniOpL (transLTAExp e f g p q)
-}

-- [Trichotomy] -----------------------------------------------------------------------------------

{-
trichoLTAExp : (x,y : AExp) -> Trichotomy (PropEqSetoid AExp Lang.decEqAExp) LTAExp x y
trichoLTAExp (Var x) (Var y) with (trichoLTNat x y)
  trichoLTAExp (Var x) (Var x) | IsEq irr = IsEq (irreflLTAExp (Var x))
  trichoLTAExp (Var x) (Var y) | IsBinR_xRy p nq neq =
    IsBinR_xRy (VarLTVar p) (asymLTAExp (Var x) (Var y) (VarLTVar p)) (\Refl => neq Refl)
  trichoLTAExp (Var x) (Var y) | IsBinR_yRx q np neq =
    IsBinR_yRx (VarLTVar q) (asymLTAExp (Var y) (Var x) (VarLTVar q)) (\Refl => neq Refl)
trichoLTAExp (Var x) (BinOp op e f) =
  IsBinR_xRy VarLTBinOp (asymLTAExp (Var x) (BinOp op e f) VarLTBinOp) absurd
trichoLTAExp (Var x) (UniOp op e) =
  IsBinR_xRy VarLTUniOp (asymLTAExp (Var x) (UniOp op e) VarLTUniOp) absurd
trichoLTAExp (BinOp r e f) (Var y) =
  IsBinR_yRx VarLTBinOp (asymLTAExp (Var y) (BinOp r e f) VarLTBinOp) (absurd . sym)
trichoLTAExp (BinOp r e f) (BinOp s g h) with (trichoLTOp r s)
  trichoLTAExp (BinOp r e f) (BinOp r g h) | IsEq irr with (trichoLTAExp e g)
    trichoLTAExp (BinOp r e f) (BinOp r e h) | IsEq irr | IsEq irr' with (trichoLTAExp f h)
      trichoLTAExp (BinOp r e f) (BinOp r e f) | IsEq irr | IsEq irr' | IsEq irr'' =
        IsEq (irreflLTAExp (BinOp r e f))
      trichoLTAExp (BinOp r e f) (BinOp r e h) | IsEq irr | IsEq irr' | IsBinR_xRy p nq neq =
        IsBinR_xRy (BinOpLTBinOpR p)
                   (asymLTAExp (BinOp r e f) (BinOp r e h) (BinOpLTBinOpR p))
                   (\Refl => neq Refl)
      trichoLTAExp (BinOp r e f) (BinOp r e h) | IsEq irr | IsEq irr' | IsBinR_yRx q np neq =
        IsBinR_yRx (BinOpLTBinOpR q)
                   (asymLTAExp (BinOp r e h) (BinOp r e f) (BinOpLTBinOpR q))
                   (\Refl => neq Refl)
    trichoLTAExp (BinOp r e f) (BinOp r g h) | IsEq irr | IsBinR_xRy p nq neq =
      IsBinR_xRy (BinOpLTBinOpL p)
                 (asymLTAExp (BinOp r e f) (BinOp r g h) (BinOpLTBinOpL p))
                 (\Refl => neq Refl)
    trichoLTAExp (BinOp r e f) (BinOp r g h) | IsEq irr | IsBinR_yRx q np neq =
      IsBinR_yRx (BinOpLTBinOpL q)
                 (asymLTAExp (BinOp r g h) (BinOp r e f) (BinOpLTBinOpL q))
                 (\Refl => neq Refl)
  trichoLTAExp (BinOp r e f) (BinOp s g h) | IsBinR_xRy p nq neq =
    IsBinR_xRy (BinOpLTBinOpF p)
               (asymLTAExp (BinOp r e f) (BinOp s g h) (BinOpLTBinOpF p))
               (\Refl => neq Refl)
  trichoLTAExp (BinOp r e f) (BinOp s g h) | IsBinR_yRx q np neq =
    IsBinR_yRx (BinOpLTBinOpF q)
               (asymLTAExp (BinOp s g h) (BinOp r e f) (BinOpLTBinOpF q))
               (\Refl => neq Refl)
trichoLTAExp (BinOp r e f) (UniOp s g) =
  IsBinR_xRy BinOpLTUniOp (asymLTAExp (BinOp r e f) (UniOp s g) BinOpLTUniOp) absurd
trichoLTAExp (UniOp op e) (Var x) =
  IsBinR_yRx VarLTUniOp (asymLTAExp (Var x) (UniOp op e) VarLTUniOp) (absurd . sym)
trichoLTAExp (UniOp p e) (BinOp q f g) =
  IsBinR_yRx BinOpLTUniOp (asymLTAExp (BinOp q f g) (UniOp p e) BinOpLTUniOp) (absurd . sym)
trichoLTAExp (UniOp r e) (UniOp s f) with (trichoLTUOp r s)
  trichoLTAExp (UniOp r e) (UniOp s f) | IsBinR_xRy p nq neq =
    IsBinR_xRy (UniOpLTUniOpF p)
               (asymLTAExp (UniOp r e) (UniOp s f) (UniOpLTUniOpF p))
               (\Refl => neq Refl)
  trichoLTAExp (UniOp r e) (UniOp s f) | IsBinR_yRx q np neq =
    IsBinR_yRx (UniOpLTUniOpF q)
               (asymLTAExp (UniOp s f) (UniOp r e) (UniOpLTUniOpF q))
               (\Refl => neq Refl)
  trichoLTAExp (UniOp r e) (UniOp r f) | IsEq irr with (trichoLTAExp e f)
    trichoLTAExp (UniOp r e) (UniOp r f) | IsEq irr | IsBinR_xRy p nq neq =
      IsBinR_xRy (UniOpLTUniOpL p)
                 (asymLTAExp (UniOp r e) (UniOp r f) (UniOpLTUniOpL p))
                 (\Refl => neq Refl)
    trichoLTAExp (UniOp r e) (UniOp r f) | IsEq irr | IsBinR_yRx q np neq =
      IsBinR_yRx (UniOpLTUniOpL q)
                 (asymLTAExp (UniOp r f) (UniOp r e) (UniOpLTUniOpL q))
                 (\Refl => neq Refl)
    trichoLTAExp (UniOp r e) (UniOp r e) | IsEq irr | IsEq irr' = IsEq (irreflLTAExp (UniOp r e))

-- [Singleton] ------------------------------------------------------------------------------------

singLTAExp : (x,y : AExp) -> (p,q : LTAExp x y) -> p = q
singLTAExp (Var x) (Var y) (VarLTVar p) (VarLTVar q) = rewrite singLTNat x y p q in Refl
singLTAExp (Var x) (BinOp op e f) VarLTBinOp VarLTBinOp = Refl
singLTAExp (Var x) (UniOp op e) VarLTUniOp VarLTUniOp = Refl
singLTAExp (BinOp r e f) (BinOp s g h) (BinOpLTBinOpF p) (BinOpLTBinOpF q) with (singLTOp r s p q)
  singLTAExp (BinOp r e f) (BinOp s g h) (BinOpLTBinOpF p) (BinOpLTBinOpF p) | Refl = Refl
singLTAExp (BinOp r e f) (BinOp r g h) (BinOpLTBinOpF p) (BinOpLTBinOpL q) with (irreflLTOp r p)
  singLTAExp (BinOp r e f) (BinOp r g h) (BinOpLTBinOpF p) (BinOpLTBinOpL q) | _ impossible
singLTAExp (BinOp r e f) (BinOp r e h) (BinOpLTBinOpF p) (BinOpLTBinOpR q) with (irreflLTOp r p)
  singLTAExp (BinOp r e f) (BinOp r e h) (BinOpLTBinOpF p) (BinOpLTBinOpR q) | _ impossible
singLTAExp (BinOp r e f) (BinOp r g h) (BinOpLTBinOpL p) (BinOpLTBinOpF q) with (irreflLTOp r q)
  singLTAExp (BinOp r e f) (BinOp r g h) (BinOpLTBinOpL p) (BinOpLTBinOpF q) | _ impossible
singLTAExp (BinOp r e f) (BinOp r g h) (BinOpLTBinOpL p) (BinOpLTBinOpL q) with (singLTAExp e g p q)
  singLTAExp (BinOp r e f) (BinOp r g h) (BinOpLTBinOpL p) (BinOpLTBinOpL p) | Refl = Refl
singLTAExp (BinOp r e f) (BinOp r e h) (BinOpLTBinOpL p) (BinOpLTBinOpR q) with (irreflLTAExp e p)
  singLTAExp (BinOp r e f) (BinOp r e h) (BinOpLTBinOpL p) (BinOpLTBinOpR q) | _ impossible
singLTAExp (BinOp r e f) (BinOp r e h) (BinOpLTBinOpR p) (BinOpLTBinOpF q) with (irreflLTOp r q)
  singLTAExp (BinOp r e f) (BinOp r e h) (BinOpLTBinOpR p) (BinOpLTBinOpF q) | _ impossible
singLTAExp (BinOp r e f) (BinOp r e h) (BinOpLTBinOpR p) (BinOpLTBinOpL q) with (irreflLTAExp e q)
  singLTAExp (BinOp r e f) (BinOp r e h) (BinOpLTBinOpR p) (BinOpLTBinOpL q) | _ impossible
singLTAExp (BinOp r e f) (BinOp r e h) (BinOpLTBinOpR p) (BinOpLTBinOpR q) with (singLTAExp f h p q)
  singLTAExp (BinOp r e f) (BinOp r e h) (BinOpLTBinOpR p) (BinOpLTBinOpR p) | Refl = Refl
singLTAExp (BinOp r e f) (UniOp s g) BinOpLTUniOp BinOpLTUniOp = Refl
singLTAExp (UniOp r e) (UniOp s f) (UniOpLTUniOpF p) (UniOpLTUniOpF q) with (singLTUOp r s p q)
  singLTAExp (UniOp r e) (UniOp s f) (UniOpLTUniOpF p) (UniOpLTUniOpF p) | Refl = Refl
singLTAExp (UniOp r e) (UniOp r f) (UniOpLTUniOpF p) (UniOpLTUniOpL q) with (irreflLTUOp r p)
  singLTAExp (UniOp r e) (UniOp r f) (UniOpLTUniOpF p) (UniOpLTUniOpL q) | _ impossible
singLTAExp (UniOp r e) (UniOp r f) (UniOpLTUniOpL p) (UniOpLTUniOpF q) with (irreflLTUOp r q)
  singLTAExp (UniOp r e) (UniOp r f) (UniOpLTUniOpL p) (UniOpLTUniOpF q) | _ impossible
singLTAExp (UniOp r e) (UniOp r f) (UniOpLTUniOpL p) (UniOpLTUniOpL q) with (singLTAExp e f p q)
  singLTAExp (UniOp r e) (UniOp r f) (UniOpLTUniOpL p) (UniOpLTUniOpL p) | Refl = Refl

-- [TotalOrdering] --------------------------------------------------------------------------------

StrictTotalOrderingAExp : StrictTotalOrdering AExp
StrictTotalOrderingAExp =
  MkSTOrdering decEqAExp
               (MkSTOrderingS (MkSTOrderingT LTAExp asymLTAExp transLTAExp trichoLTAExp decLTAExp)
                              singLTAExp)

implementation StrictTotalOrder AExp where
  theOrder = StrictTotalOrderingAExp

---------------------------------------------------------------------------------------------------
-- [Soundness] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

implementation LTSound AExp where
  lt_sound {x = Var w} (VarLTVar p) IsEq = asymLTNat w w p p
  lt_sound {x = Var v} {y = Var w} (VarLTVar p) (IsLT (VarLTVar q)) = asymLTNat v w p q
  lt_sound VarLTBinOp (IsLT q) = absurd q
  lt_sound VarLTUniOp (IsLT q) = absurd q
  lt_sound {x = BinOp op e f} (BinOpLTBinOpF p) IsEq = irreflLTOp op p
  lt_sound {x = BinOp x e f} {y = BinOp y g h} (BinOpLTBinOpF p) (IsLT (BinOpLTBinOpF q)) =
    asymLTOp x y p q
  lt_sound {x = BinOp op e f} (BinOpLTBinOpF p) (IsLT (BinOpLTBinOpL q)) = irreflLTOp op p
  lt_sound {x = BinOp op e f} (BinOpLTBinOpF p) (IsLT (BinOpLTBinOpR q)) = irreflLTOp op p
  lt_sound {x = BinOp op e f} (BinOpLTBinOpL p) IsEq = irreflLTAExp e p
  lt_sound {x = BinOp op e f} (BinOpLTBinOpL p) (IsLT (BinOpLTBinOpF q)) = irreflLTOp op q
  lt_sound {x = BinOp op e f} {y = BinOp op g h} (BinOpLTBinOpL p) (IsLT (BinOpLTBinOpL q)) =
    asymLTAExp e g p q
  lt_sound {x = BinOp op e f} (BinOpLTBinOpL p) (IsLT (BinOpLTBinOpR q)) = irreflLTAExp e p
  lt_sound {x = BinOp op e f} (BinOpLTBinOpR p) IsEq = irreflLTAExp f p
  lt_sound {x = BinOp op e f} (BinOpLTBinOpR p) (IsLT (BinOpLTBinOpF q)) = irreflLTOp op q
  lt_sound {x = BinOp op e f} (BinOpLTBinOpR p) (IsLT (BinOpLTBinOpL q)) = irreflLTAExp e q
  lt_sound {x = BinOp op e f} {y = BinOp op e h} (BinOpLTBinOpR p) (IsLT (BinOpLTBinOpR q)) =
    asymLTAExp f h p q
  lt_sound BinOpLTUniOp (IsLT q) = absurd q
  lt_sound {x = UniOp op e} (UniOpLTUniOpF p) IsEq = irreflLTUOp op p
  lt_sound {x = UniOp r e} {y = UniOp s f} (UniOpLTUniOpF p) (IsLT (UniOpLTUniOpF q)) =
    asymLTUOp r s p q
  lt_sound {x = UniOp op e} (UniOpLTUniOpF p) (IsLT (UniOpLTUniOpL q)) = irreflLTUOp op p
  lt_sound {x = UniOp op e} (UniOpLTUniOpL p) IsEq = irreflLTAExp e p
  lt_sound {x = UniOp op e} (UniOpLTUniOpL p) (IsLT (UniOpLTUniOpF q)) = irreflLTUOp op q
  lt_sound {x = UniOp op e} {y = UniOp op f} (UniOpLTUniOpL p) (IsLT (UniOpLTUniOpL q)) =
    asymLTAExp e f p q

  gte_sound {x} IsEq q = irreflLTAExp x q
  gte_sound {x} {y} (IsLT p) q = asymLTAExp x y q p
-}

