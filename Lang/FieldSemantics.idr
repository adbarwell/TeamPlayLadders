module Lang.FieldSemantics

import public Data.Vect
import public Data.Vect.Elem

import public IdrisUtils.Algebra

import public Lang.Base

---------------------------------------------------------------------------------------------------
-- [Denotational Domain] --------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Represents functions over some field; i.e. 
||| `(\x1 => \x2 => ... \xn => e) : c -> c -> ... c -> c`
public export
data FieldExp : {c : Type}
             -> {add,mul : c -> c -> c}
             -> {zero,one : c}
             -> {addinv,mulinv : c -> c}
             -> (field : Field c add mul zero one addinv mulinv)
             -> (nvars : Nat)
             -> Type where
  ||| Literal values.
  FLit : (n : c) -> FieldExp {c} field nvars
  ||| Variables -- de Bruijn indices.
  FVar : {field : Field c add mul zero one addinv mulinv}
      -> (i : Fin nvars) -> FieldExp field nvars
  ||| (-) -- Additive inverse.
  FNeg : (x : FieldExp field nvars) -> FieldExp field nvars
  ||| (^{-1}) -- Multiplicative inverse.
  FInv : (x : FieldExp field nvars) -> FieldExp field nvars
  ||| (+) -- Addition.
  FAdd : (x,y : FieldExp field nvars) -> FieldExp field nvars
  ||| (*) -- Multiplication.
  FMul : (x,y : FieldExp field nvars) -> FieldExp field nvars

||| Given some context, we can reduce an expression.
||| This is akin to applying functions over c (represented by FieldExp).
export
reify : {add,mul : c -> c -> c}
     -> {zero,one : c}
     -> {addinv,mulinv : c -> c}
     -> {field : Field c add mul zero one addinv mulinv}
     -> (ctx : Vect nvars c) -> FieldExp {c} field nvars -> c
reify ctx (FLit n) = n
reify ctx (FVar i) = index i ctx
reify {addinv} ctx (FNeg x) = addinv (reify ctx x)
reify {mulinv} ctx (FInv x) = mulinv (reify ctx x)
reify {add} ctx (FAdd x y) = add (reify ctx x) (reify ctx y)
reify {mul} ctx (FMul x y) = mul (reify ctx x) (reify ctx y)

-- [Extending basic proofs over FieldExp] ---------------------------------------------------------

export
plusFECommutative : {add,mul : c -> c -> c}
                 -> {zero,one : c}
                 -> {addinv,mulinv : c -> c}
                 -> {field : Field c add mul zero one addinv mulinv}
                 -> (ctx : Vect nvars c) 
                 -> (x,y : FieldExp field nvars)
                 -> reify ctx (FAdd x y) = reify ctx (FAdd y x)
plusFECommutative {field} ctx x y =
  rewrite opCommutative (addIsCommGroup (isRing (isCommRing field))) (reify ctx x) (reify ctx y) in
    Refl

export
multFECommutative : {add,mul : c -> c -> c}
                 -> {zero,one : c}
                 -> {addinv,mulinv : c -> c}
                 -> {field : Field c add mul zero one addinv mulinv}
                 -> (ctx : Vect nvars c) 
                 -> (x,y : FieldExp field nvars)
                 -> reify ctx (FMul x y) = reify ctx (FMul y x)
multFECommutative {field} ctx x y =
  rewrite mulCommutative (isCommRing field) (reify ctx x) (reify ctx y) in Refl

-- [Equality] -------------------------------------------------------------------------------------

||| Extensional equality over FieldExp (i.e. functions over a field).
public export
data EquivFE : (e,f : FieldExp field nvars) -> Type where
  AreEquivFE : {e,f : FieldExp {c} field nvars}
            -> (ok : (ctx : Vect nvars c) -> reify ctx e = reify ctx f) -> EquivFE e f

export
reflEquivFE : {e : FieldExp field nvars} -> EquivFE e e
reflEquivFE = AreEquivFE (\ctx => Refl)

export
symEquivFE : EquivFE e f -> EquivFE f e
symEquivFE (AreEquivFE p) = AreEquivFE (\ctx => sym (p ctx))

export
transEquivFE : EquivFE e f -> EquivFE f g -> EquivFE e g
transEquivFE (AreEquivFE p) (AreEquivFE q) = AreEquivFE (\ctx => trans (p ctx) (q ctx))

{-
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
-}
