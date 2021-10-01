module Lang.Semantics

import public Data.Vect
import public Data.Vect.Elem

import public IdrisUtils.Data.Integer.SInt

import public Lang.Base

---------------------------------------------------------------------------------------------------
-- [Denotational Domain] --------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- For now, this is Integers; it really needs to be a generic field.

||| Field operations for Integers with arguments.
||| Represents functions over integers; i.e. 
||| `(\x1 => \x2 => ... \xn => e) : Int -> Int -> ... Int -> Int`
public export
data IntExp : (nvars : Nat) -> Type where
  NLit : (n : SInt) -> IntExp nvars
  NVar : (i : Fin nvars) -> IntExp nvars
  NNeg : (x : IntExp nvars) -> IntExp nvars
  NAdd : (x,y : IntExp nvars) -> IntExp nvars
  NMul : (x,y : IntExp nvars) -> IntExp nvars
  NSqu : (x : IntExp nvars) -> IntExp nvars

||| Given some context, we can reduce an integer expression 
||| This is akin to applying functions over integers (represented by IntExp).
export
reify : (ctx : Vect nvars SInt) -> (1 x : IntExp nvars) -> SInt
reify ctx (NLit n) = n
reify ctx (NVar x) = index x ctx
reify ctx (NNeg x) = negate (reify ctx x)
reify ctx (NAdd x y) = plus (reify ctx x) (reify ctx y)
reify ctx (NMul x y) = mult (reify ctx x) (reify ctx y)
reify ctx (NSqu x) = power (reify ctx x) 2

-- [Extending basic proofs over IntExp] -----------------------------------------------------------

export
plusIECommutative : (ctx : Vect nvars SInt) 
                 -> (l,r : IntExp nvars)
                 -> (reify ctx (NAdd l r) = reify ctx (NAdd r l))
plusIECommutative ctx x y = rewrite plusCommutative (reify ctx x) (reify ctx y) in Refl

export
multIECommutative : (ctx : Vect nvars SInt) -> (l,r : IntExp nvars)
                 -> (reify ctx (NMul l r) = reify ctx (NMul r l))
multIECommutative ctx x y = rewrite multCommutative (reify ctx x) (reify ctx y) in Refl

export
squareEqMult : (ctx : Vect nvars SInt) 
            -> (e : IntExp nvars)
            -> (reify ctx (NSqu e) = reify ctx (NMul e e))
squareEqMult ctx e with (reify ctx e)
  squareEqMult ctx e | Pos Z = Refl
  squareEqMult ctx e | Pos (S x) = rewrite multOneRightNeutral x in Refl
  squareEqMult ctx e | Neg Z = Refl
  squareEqMult ctx e | Neg (S x) = rewrite multOneRightNeutral x in Refl

-- [Equality] -------------------------------------------------------------------------------------

||| Extensional equality over IntExp (i.e. functions over integers).
public export
data EquivIE : (e,f : IntExp nvars) -> Type where
  AreEquivIE : {e,f : IntExp nvars}
            -> (ok : (ctx : Vect nvars SInt) -> reify ctx e = reify ctx f) 
            -> EquivIE e f

export
reflEquivIE : {e : IntExp nvars} -> EquivIE e e
reflEquivIE = AreEquivIE (\ctx => Refl)

export
symEquivIE : EquivIE e f -> EquivIE f e
symEquivIE (AreEquivIE p) = AreEquivIE (\ctx => sym (p ctx))

export
transEquivIE : EquivIE e f -> EquivIE f g -> EquivIE e g
transEquivIE (AreEquivIE p) (AreEquivIE q) = AreEquivIE (\ctx => trans (p ctx) (q ctx))

---------------------------------------------------------------------------------------------------
-- [Denotational Semantics] -----------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Maps arithmetic expressions into functions over integers.
public export
data SmAExp : (e : AExp nvars) -> (f : IntExp nvars) -> Type where
  SmLit : SmAExp (Lit n) (NLit (Pos n))
  SmVar : SmAExp (Var i) (NVar i)
  SmNeg : (r1 : SmAExp e x) -> SmAExp (UniOp Neg e) (NNeg x)
  SmAdd : (r1 : SmAExp l x) -> (r2 : SmAExp r y) -> SmAExp (BinOp Plus l r) (NAdd x y)
  SmMul : (r1 : SmAExp l x) -> (r2 : SmAExp r y) -> SmAExp (BinOp Mult l r) (NMul x y)
  SmSqu : (r1 : SmAExp e x) -> SmAExp (UniOp Square e) (NSqu x)

export
denoteAExp : (e : AExp nvars) -> (f : IntExp nvars ** SmAExp e f)
denoteAExp (Lit n) = (NLit (Pos n) ** SmLit)
denoteAExp (Var i) = (NVar i ** SmVar)
denoteAExp (UniOp Neg e) with (denoteAExp e)
  denoteAExp (UniOp Neg e) | (x ** r1) = (NNeg x ** SmNeg r1)
denoteAExp (UniOp Square e) with (denoteAExp e)
  denoteAExp (UniOp Square e) | (x ** r1) = (NSqu x ** SmSqu r1)
denoteAExp (BinOp Plus e f) with (denoteAExp e)
  denoteAExp (BinOp Plus e f) | (x ** r1) with (denoteAExp f)
    denoteAExp (BinOp Plus e f) | (x ** r1) | (y ** r2) = (NAdd x y ** SmAdd r1 r2)
denoteAExp (BinOp Mult e f) with (denoteAExp e)
  denoteAExp (BinOp Mult e f) | (x ** r1) with (denoteAExp f)
    denoteAExp (BinOp Mult e f) | (x ** r1) | (y ** r2) = (NMul x y ** SmMul r1 r2)


-- [Injectiveness] --------------------------------------------------------------------------------

export
injSmAExp : (p : SmAExp e f) -> (q : SmAExp e g) -> f = g
injSmAExp SmLit SmLit = Refl
injSmAExp SmVar SmVar = Refl
injSmAExp (SmNeg p) (SmNeg q) = rewrite injSmAExp p q in Refl
injSmAExp (SmAdd p1 p2) (SmAdd q1 q2) = rewrite injSmAExp p1 q1 in rewrite injSmAExp p2 q2 in Refl
injSmAExp (SmMul p1 p2) (SmMul q1 q2) = rewrite injSmAExp p1 q1 in rewrite injSmAExp p2 q2 in Refl
injSmAExp (SmSqu p) (SmSqu q) = rewrite injSmAExp p q in Refl

