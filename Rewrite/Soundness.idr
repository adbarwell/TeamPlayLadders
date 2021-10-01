module Rewrite.Soundness

import public Rewrite.Base

%default total

---------------------------------------------------------------------------------------------------
-- [Rewrite Definitions (Denotational Domain)] ----------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Rewrites defined over the denotational domain. (Here on functions over c equipped with a ring.)
public export
data ARewriteRE : (x,y : CRingExp ring nvars) -> Type where
  AddCommRE : ARewriteRE (RAdd x y) (RAdd y x)
  MulCommRE : ARewriteRE (RMul x y) (RMul y x)
  NegCongRE : ARewriteRE x y -> ARewriteRE (RNeg x) (RNeg y)
  AddCong1RE : ARewriteRE x y -> ARewriteRE (RAdd x z) (RAdd y z)
  AddCong2RE : ARewriteRE y z -> ARewriteRE (RAdd x y) (RAdd x z)
  MulCong1RE : ARewriteRE x y -> ARewriteRE (RMul x z) (RMul y z)
  MulCong2RE : ARewriteRE y z -> ARewriteRE (RMul x y) (RMul x z)

---------------------------------------------------------------------------------------------------
-- [Soundness] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
soundARewriteRE : {ring : CommRing c add mul zero one neg}
               -> (x,y : CRingExp ring nvars) -> (r : ARewriteRE x y) -> EquivRE x y
soundARewriteRE (RAdd x y) (RAdd y x) AddCommRE = AreEquivRE (\ctx => plusRECommutative ctx x y)
soundARewriteRE (RMul x y) (RMul y x) MulCommRE = AreEquivRE (\ctx => multRECommutative ctx x y)
soundARewriteRE (RNeg x) (RNeg y) (NegCongRE r) with (soundARewriteRE x y r)
  soundARewriteRE (RNeg x) (RNeg y) (NegCongRE r) | (AreEquivRE p) =
    AreEquivRE (\ctx => rewrite p ctx in Refl)
soundARewriteRE (RAdd x z) (RAdd y z) (AddCong1RE r) with (soundARewriteRE x y r)
  soundARewriteRE (RAdd x z) (RAdd y z) (AddCong1RE r) | (AreEquivRE p) =
    AreEquivRE (\ctx => rewrite p ctx in Refl)
soundARewriteRE (RAdd x y) (RAdd x z) (AddCong2RE r) with (soundARewriteRE y z r)
  soundARewriteRE (RAdd x y) (RAdd x z) (AddCong2RE r) | (AreEquivRE p) =
    AreEquivRE (\ctx => rewrite p ctx in Refl)
soundARewriteRE (RMul x z) (RMul y z) (MulCong1RE r) with (soundARewriteRE x y r)
  soundARewriteRE (RMul x z) (RMul y z) (MulCong1RE r) | (AreEquivRE p) =
    AreEquivRE (\ctx => rewrite p ctx in Refl)
soundARewriteRE (RMul x y) (RMul x z) (MulCong2RE r) with (soundARewriteRE y z r)
  soundARewriteRE (RMul x y) (RMul x z) (MulCong2RE r) | (AreEquivRE p) =
    AreEquivRE (\ctx => rewrite p ctx in Refl)

export
soundARAssoc : {ring : CommRing c add mul zero one neg}
            -> {op : BOp}
            -> {e,f,g : AExp c nvars}
            -> (x,y : CRingExp ring nvars)
            -> (s1  : SmAExp (BinOp op e (BinOp op f g)) x)
            -> (s2  : SmAExp (BinOp op (BinOp op e f) g) y)
            -> (ok : IsAssociative op)
            -> EquivRE x y
soundARAssoc (RAdd v (RAdd w x)) (RAdd (RAdd y1 y2) z) (SmAdd s1 (SmAdd s2 s3)) (SmAdd (SmAdd s4 s5) s6) PlusIsAssoc =
  rewrite injSmAExp s1 s4 in rewrite injSmAExp s2 s5 in rewrite injSmAExp s3 s6 in
    addREAssociative y1 y2 z
soundARAssoc (RMul v (RMul w x)) (RMul (RMul y1 y2) z) (SmMul s1 (SmMul s2 s3)) (SmMul (SmMul s4 s5) s6) MultIsAssoc =
  rewrite injSmAExp s1 s4 in rewrite injSmAExp s2 s5 in rewrite injSmAExp s3 s6 in
    mulREAssociative y1 y2 z
-- Need this for the totality checker. Don't ask me why, it's a mystery to me too.
soundARAssoc (RAdd v (RAdd w x)) (RAdd (RLit y) z) (SmAdd s1 (SmAdd s2 s3)) (SmAdd _ s6) PlusIsAssoc impossible

export
soundARewrite : {ring : CommRing c add mul zero one neg}
             -> (e,f : AExp c nvars)
             -> (x,y : CRingExp ring nvars)
             -> (s1  : SmAExp e x)
             -> (s2  : SmAExp f y)
             -> (r   : ARewrite e f)
             -> EquivRE x y
soundARewrite (UniOp Square e) (BinOp Mult e e)
              (RMul x x) (RMul y z)
              (SmSqu s1) (SmMul s2 s3) SqIsMult =
  rewrite injSmAExp s1 s2 in rewrite injSmAExp s2 s3 in symEquivRE (AreEquivRE (\ctx => Refl))
soundARewrite (BinOp Plus e f) (BinOp Plus f e)
              (RAdd w x) (RAdd y z)
              (SmAdd s1 s2) (SmAdd s3 s4) (Commutative PlusIsComm) =
  rewrite injSmAExp s1 s4 in rewrite injSmAExp s2 s3 in
    soundARewriteRE (RAdd z y) (RAdd y z) AddCommRE
soundARewrite (BinOp Mult e f) (BinOp Mult f e)
              (RMul w x) (RMul y z)
              (SmMul s1 s2) (SmMul s3 s4) (Commutative MultIsComm) =
  rewrite injSmAExp s1 s4 in rewrite injSmAExp s2 s3 in
    soundARewriteRE (RMul z y) (RMul y z) MulCommRE
soundARewrite (BinOp op e (BinOp op f g)) (BinOp op (BinOp op e f) g)
              x y
              s1 s2 (Associative ok) = soundARAssoc x y s1 s2 ok

export
soundRewrite : {ring : CommRing c add mul zero one neg}
            -> (e,f  : AExp c nvars)
            -> (x,y  : CRingExp ring nvars)
            -> (s1   : SmAExp e x)
            -> (s2   : SmAExp f y)
            -> (r    : Rewrite e f)
            -> EquivRE x y
soundRewrite e e x y s1 s2 Refl = rewrite injSmAExp s1 s2 in reflEquivRE
soundRewrite e f x y s1 s2 (Fun r) = soundARewrite e f x y s1 s2 r
soundRewrite e f x y s1 s2 (Sym r) with (soundRewrite f e y x s2 s1 r)
  soundRewrite e f x y s1 s2 (Sym r) | p = symEquivRE p
soundRewrite e f x y s1 s2 (Trans {f=g} r1 r2) with (denoteAExp g)
  soundRewrite e f x y s1 s2 (Trans {f=g} r1 r2) | (z ** s3) with (soundRewrite e g x z s1 s3 r1)
    soundRewrite e f x y s1 s2 (Trans {f=g} r1 r2) | (z ** s3) | p with (soundRewrite g f z y s3 s2 r2)
      soundRewrite e f x y s1 s2 (Trans {f=g} r1 r2) | (z ** s3) | p | q = transEquivRE p q
soundRewrite (UniOp Neg e) (UniOp Neg f) (RNeg x) (RNeg y) (SmNeg s1) (SmNeg s2) (CongU r) =
  congNegEquivRE (soundRewrite e f x y s1 s2 r)
soundRewrite (UniOp Square e) (UniOp Square f) (RMul x x) (RMul y y) (SmSqu s1) (SmSqu s2) (CongU r) =
  congSquREquivRE (soundRewrite e f x y s1 s2 r)
soundRewrite (BinOp Plus e g) (BinOp Plus f g) (RAdd x z) (RAdd y w) (SmAdd s1 s2) (SmAdd s3 s4) (CongB1 r) =
  rewrite injSmAExp s2 s4 in congAddLEquivRE (soundRewrite e f x y s1 s3 r)
soundRewrite (BinOp Mult e g) (BinOp Mult f g) (RMul x z) (RMul y w) (SmMul s1 s2) (SmMul s3 s4) (CongB1 r) =
  rewrite injSmAExp s2 s4 in congMulLEquivRE (soundRewrite e f x y s1 s3 r)
soundRewrite (BinOp Plus e f) (BinOp Plus e g) (RAdd x z) (RAdd y w) (SmAdd s1 s2) (SmAdd s3 s4) (CongB2 r) =
  rewrite injSmAExp s1 s3 in congAddREquivRE (soundRewrite f g z w s2 s4 r)
soundRewrite (BinOp Mult e f) (BinOp Mult e g) (RMul x z) (RMul y w) (SmMul s1 s2) (SmMul s3 s4) (CongB2 r) =
  rewrite injSmAExp s1 s3 in congMulREquivRE (soundRewrite f g z w s2 s4 r)

