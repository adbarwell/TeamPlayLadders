module Lang.CRingSemantics

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
data CRingExp : {c        : Type}
             -> {add,mul  : c -> c -> c}
             -> {zero,one : c}
             -> {neg      : c -> c}
             -> (ring     : CommRing c add mul zero one neg)
             -> (nvars    : Nat)
             -> Type where
  ||| Literal values.
  RLit : (n : c) -> CRingExp {c} ring nvars
  ||| Variables -- de Bruijn indices.
  RVar : {ring : CommRing c add mul zero one neg}
      -> (i : Fin nvars) -> CRingExp ring nvars
  ||| (-) -- Additive inverse.
  RNeg : (x : CRingExp ring nvars) -> CRingExp ring nvars
  ||| (+) -- Addition.
  RAdd : (x,y : CRingExp ring nvars) -> CRingExp ring nvars
  ||| (*) -- Multiplication.
  RMul : (x,y : CRingExp ring nvars) -> CRingExp ring nvars

||| Given some context, we can reduce an expression.
||| This is akin to applying functions over c (represented by CRingExp).
public export
reify : {add,mul  : c -> c -> c}
     -> {zero,one : c}
     -> {neg      : c -> c}
     -> {ring     : CommRing c add mul zero one neg}
     -> (ctx      : Vect nvars c)
     -> CRingExp {c} ring nvars -> c
reify ctx (RLit n) = n
reify ctx (RVar i) = index i ctx
reify {neg} ctx (RNeg x) = neg (reify ctx x)
reify {add} ctx (RAdd x y) = add (reify ctx x) (reify ctx y)
reify {mul} ctx (RMul x y) = mul (reify ctx x) (reify ctx y)

-- [Extending basic proofs over CRingExp] ---------------------------------------------------------

export
plusRECommutative : {ring : CommRing c add mul zero one neg}
                 -> (ctx : Vect nvars c) 
                 -> (x,y : CRingExp ring nvars)
                 -> reify ctx (RAdd x y) = reify ctx (RAdd y x)
plusRECommutative {ring} ctx x y =
  rewrite opCommutative (addIsCommGroup (isRing ring)) (reify ctx x) (reify ctx y) in
    Refl

export
multRECommutative : {ring : CommRing c add mul zero one neg}
                 -> (ctx : Vect nvars c) 
                 -> (x,y : CRingExp ring nvars)
                 -> reify ctx (RMul x y) = reify ctx (RMul y x)
multRECommutative {ring} ctx x y =
  rewrite mulCommutative ring (reify ctx x) (reify ctx y) in Refl

-- [Equality] -------------------------------------------------------------------------------------

||| Extensional equality over CRingExp (i.e. functions over a ring).
public export
data EquivRE : (e,f : CRingExp ring nvars) -> Type where
  AreEquivRE : {e,f : CRingExp {c} ring nvars}
            -> (ok : (ctx : Vect nvars c) -> reify ctx e = reify ctx f) -> EquivRE e f

export
reflEquivRE : {e : CRingExp ring nvars} -> EquivRE e e
reflEquivRE = AreEquivRE (\ctx => Refl)

export
symEquivRE : EquivRE e f -> EquivRE f e
symEquivRE (AreEquivRE p) = AreEquivRE (\ctx => sym (p ctx))

export
transEquivRE : EquivRE e f -> EquivRE f g -> EquivRE e g
transEquivRE (AreEquivRE p) (AreEquivRE q) = AreEquivRE (\ctx => trans (p ctx) (q ctx))

-- In order to generalise the congurence proofs we would need a separate relation that states
-- how some {g : CRingExp r n -> CRingExp r n} relates to some {f : c -> c} enabling the lemma
-- (reify ctx (g e) = f (reify ctx e))
-- Easier for now to do them individually.

export
congNegEquivRE : {ring : CommRing c add mul zero one neg}
              -> {e,f : CRingExp ring nvars} -> EquivRE e f -> EquivRE (RNeg e) (RNeg f)
congNegEquivRE {neg} (AreEquivRE p) = AreEquivRE (\ctx => cong neg (p ctx))

export
congAddLEquivRE : {ring : CommRing c add mul zero one neg}
               -> {e,f,g : CRingExp ring nvars} -> EquivRE e f -> EquivRE (RAdd e g) (RAdd f g)
congAddLEquivRE (AreEquivRE p) = AreEquivRE (\ctx => rewrite p ctx in Refl)

export
congAddREquivRE : {ring : CommRing c add mul zero one neg}
               -> {e,f,g : CRingExp ring nvars} -> EquivRE f g -> EquivRE (RAdd e f) (RAdd e g)
congAddREquivRE (AreEquivRE p) = AreEquivRE (\ctx => rewrite p ctx in Refl)

export
congMulLEquivRE : {ring : CommRing c add mul zero one neg}
               -> {e,f,g : CRingExp ring nvars} -> EquivRE e f -> EquivRE (RMul e g) (RMul f g)
congMulLEquivRE (AreEquivRE p) = AreEquivRE (\ctx => rewrite p ctx in Refl)

export
congMulREquivRE : {ring : CommRing c add mul zero one neg}
               -> {e,f,g : CRingExp ring nvars} -> EquivRE f g -> EquivRE (RMul e f) (RMul e g)
congMulREquivRE (AreEquivRE p) = AreEquivRE (\ctx => rewrite p ctx in Refl)

export
congSquREquivRE : {ring : CommRing c add mul zero one neg}
               -> {e,f : CRingExp ring nvars} -> EquivRE e f -> EquivRE (RMul e e) (RMul f f)
congSquREquivRE (AreEquivRE p) = AreEquivRE (\ctx => rewrite p ctx in Refl)

--

export
addREAssociative : {ring : CommRing c add mul zero one neg}
                -> (x,y,z : CRingExp ring nvars)
                -> EquivRE (RAdd x (RAdd y z)) (RAdd (RAdd x y) z)
addREAssociative {ring} x y z =
  AreEquivRE (\ctx => rewrite opAssociative (isSemigroup (isMonoid (isGroup (addIsCommGroup (isRing ring))))) (reify ctx x) (reify ctx y) (reify ctx z) in Refl)

export
mulREAssociative : {ring : CommRing c add mul zero one neg}
                -> (x,y,z : CRingExp ring nvars)
                -> EquivRE (RMul x (RMul y z)) (RMul (RMul x y) z)
mulREAssociative {ring} x y z =
  AreEquivRE (\ctx => rewrite opAssociative (isSemigroup (mulIsMonoid (isRing ring))) (reify ctx x) (reify ctx y) (reify ctx z) in Refl)

---------------------------------------------------------------------------------------------------
-- [Denotational Semantics] -----------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Maps arithmetic expressions into functions over commutative rings.
public export
data SmAExp : (e : AExp c nvars) -> (f : CRingExp {c} ring nvars) -> Type where
  SmLit : SmAExp (Lit n) (RLit n)
  SmVar : SmAExp (Var i) (RVar i)
  SmNeg : (r1 : SmAExp e x) -> SmAExp (UniOp Neg e) (RNeg x)
  SmAdd : (r1 : SmAExp l x) -> (r2 : SmAExp r y) -> SmAExp (BinOp Plus l r) (RAdd x y)
  SmMul : (r1 : SmAExp l x) -> (r2 : SmAExp r y) -> SmAExp (BinOp Mult l r) (RMul x y)
  SmSqu : (r1 : SmAExp e x) -> SmAExp (UniOp Square e) (RMul x x)

export
denoteAExp : {ring : CommRing c add mul zero one neg}
          -> (e : AExp c nvars) -> (f : CRingExp ring nvars ** SmAExp e f)
denoteAExp (Lit n) = (RLit n ** SmLit)
denoteAExp (Var i) = (RVar i ** SmVar)
denoteAExp (UniOp Neg e) with (denoteAExp e)
  denoteAExp (UniOp Neg e) | (x ** r1) = (RNeg x ** SmNeg r1)
denoteAExp (UniOp Square e) with (denoteAExp e)
  denoteAExp (UniOp Square e) | (x ** r1) = (RMul x x ** SmSqu r1)
denoteAExp (BinOp Plus e f) with (denoteAExp e)
  denoteAExp (BinOp Plus e f) | (x ** r1) with (denoteAExp f)
    denoteAExp (BinOp Plus e f) | (x ** r1) | (y ** r2) = (RAdd x y ** SmAdd r1 r2)
denoteAExp (BinOp Mult e f) with (denoteAExp e)
  denoteAExp (BinOp Mult e f) | (x ** r1) with (denoteAExp f)
    denoteAExp (BinOp Mult e f) | (x ** r1) | (y ** r2) = (RMul x y ** SmMul r1 r2)


-- [Injectiveness] --------------------------------------------------------------------------------

export
injSmAExp : (p : SmAExp e f) -> (q : SmAExp e g) -> f = g
injSmAExp SmLit SmLit = Refl
injSmAExp SmVar SmVar = Refl
injSmAExp (SmNeg p) (SmNeg q) = rewrite injSmAExp p q in Refl
injSmAExp (SmAdd p1 p2) (SmAdd q1 q2) = rewrite injSmAExp p1 q1 in rewrite injSmAExp p2 q2 in Refl
injSmAExp (SmMul p1 p2) (SmMul q1 q2) = rewrite injSmAExp p1 q1 in rewrite injSmAExp p2 q2 in Refl
injSmAExp (SmSqu p) (SmSqu q) = rewrite injSmAExp p q in Refl
