module Generalise

import public IdrisUtils.Error
import public IdrisUtils.Data.Integer
import public Rewrite
import public Lang.Substitution
import public Lang.Base
import public Lang.Prop.DecEq


%default total

export
weakenAExp : (e : AExp c nvars)
          -> AExp c (S nvars)
weakenAExp (Lit n) = Lit n
weakenAExp (Var x) = Var (weaken x)
weakenAExp (BinOp op e1 e2) = 
    case weakenAExp e1 of 
        e1' => 
          case weakenAExp e2 of 
            e2' => BinOp op e1' e2'
weakenAExp (UniOp op e1) = 
    case weakenAExp e1 of 
        e1' => UniOp op e1'

export       
generalise : (DecEq c)
          => (vars : Fin nvars)
          -> (e, f : AExp c nvars)
        --  -> SubTerm e f -- e is a subterm of f
          -> Either (AExp c nvars) (x : Fin (S nvars) ** (AExp c (S nvars)))
generalise vars (Lit n) (Lit m) with (decEq n m)
    generalise vars (Lit n) (Lit n) | Yes Refl = Right (FS vars ** (Var (FS vars)))
    generalise vars (Lit n) (Lit m) | No con  = Left (Lit m)
generalise vars (Lit n) (BinOp op e1 e2) = 
    case generalise vars (Lit n) e1 of 
        Left e1' => 
           case generalise vars (Lit n) e2 of
             Left e2' => Left (BinOp op e1' e2')
             Right (x ** e2') => Right (x ** BinOp op (weakenAExp e1') e2')
                            
        Right (x ** e1') => case generalise vars (Lit n) e2 of 
            Left e2' => Right (x ** BinOp op e1' (weakenAExp e2'))
            Right (x ** e2') => Right (x ** BinOp op e1' e2')         
generalise vars (Lit n) (UniOp op e1) = 
    case generalise vars (Lit n) e1 of 
        Left e1' => Left (UniOp op e1')
        Right (x ** e1') => Right (x ** UniOp op e1')
generalise vars (Var x) (Var y) with (decEq x y)
  generalise vars (Var x) (Var x) | Yes Refl = Left (Var x)
  generalise vars (Var x) (Var y) | No contra = Left (Var y)
generalise _ (Var _) (Lit n) = Left (Lit n)
generalise vars (Var x) (BinOp op e1 e2) = 
    case generalise vars (Var x) e1 of 
        Left e1' => 
           case generalise vars (Var x) e2 of
             Left e2' => Left (BinOp op e1' e2')
             Right (x ** e2') => Right (x ** BinOp op (weakenAExp e1') e2')                      
        Right (z ** e1') => case generalise vars (Var x) e2 of 
            Left e2' => Right (z ** BinOp op e1' (weakenAExp e2'))
            Right (y ** e2') => Right (y ** BinOp op e1' e2')
generalise vars (Var x) (UniOp op e1) =
    case generalise vars (Var x) e1 of 
        Left e1' => Left (UniOp op e1')
        Right (x ** e1') => Right (x ** UniOp op e1')
generalise vars (BinOp op e1 e2) (BinOp op1 e3 e4) = 
    case decEq op op1 of 
        Yes Refl => 
         case decEq e1 e3 of 
            Yes Refl => 
              case decEq e2 e4 of 
                Yes Refl => Right (FS vars ** Var (FS vars))
                No _ =>  
                 case generalise vars (BinOp op e1 e2) e3 of 
                    Left e3' => 
                       case generalise vars (BinOp op e1 e2) e4 of 
                         Left e4' => Left (BinOp op e3' e4')
                         Right (x ** e4') => Right (x ** BinOp op (weakenAExp e3') e4')
                    Right (x ** e3') => 
                       case generalise vars (BinOp op e1 e2) e4 of 
                         Left e4' => Right (x ** BinOp op e3' (weakenAExp e4'))
                         Right (y ** e4') => Right (y ** BinOp op e3' e4') 
            No _ =>  
             case generalise vars (BinOp op e1 e2) e3 of 
                Left e3' => 
                   case generalise vars (BinOp op e1 e2) e4 of 
                     Left e4' => Left (BinOp op e3' e4')
                     Right (x ** e4') => Right (x ** BinOp op (weakenAExp e3') e4')
                Right (x ** e3') => 
                   case generalise vars (BinOp op e1 e2) e4 of 
                     Left e4' => Right (x ** BinOp op e3' (weakenAExp e4'))
                     Right (y ** e4') => Right (y ** BinOp op e3' e4')         
        No c => 
          case generalise vars (BinOp op e1 e2) e3 of 
            Left e3' => 
               case generalise vars (BinOp op e1 e2) e4 of 
                 Left e4' => Left (BinOp op e3' e4')
                 Right (x ** e4') => Right (x ** BinOp op (weakenAExp e3') e4')
            Right (x ** e3') => 
               case generalise vars (BinOp op e1 e2) e4 of 
                 Left e4' => Right (x ** BinOp op e3' (weakenAExp e4'))
                 Right (y ** e4') => Right (y ** BinOp op e3' e4')
generalise vars (BinOp op e1 e2) (Lit m) = Left (Lit m)
generalise vars (BinOp op e1 e2) (Var x) = Left (Var x)
generalise vars (BinOp op e1 e2) (UniOp op2 e3) = 
    case generalise vars (BinOp op e1 e2) e3 of 
        Left e1' => Left (UniOp op2 e1')
        Right (x ** e1') => Right (x ** UniOp op2 e1')
generalise vars (UniOp op e1) (UniOp op2 e2) = 
    case decEq op op2 of 
        Yes Refl => 
          case decEq e1 e2 of 
            Yes Refl => Right (FS vars ** (Var (FS vars)))
            No _ => 
              case generalise vars (UniOp op e1) e2 of
                Left e2' => Left (UniOp op2 e2')
                Right (x ** e2') => Right (x ** UniOp op2 e2')
        No _ => 
          case generalise vars (UniOp op e1) e2 of
            Left e2' => Left (UniOp op2 e2')
            Right (x ** e2') => Right (x ** UniOp op2 e2')
generalise vars (UniOp op e1) (Lit n) = Left (Lit n) 
generalise vars (UniOp op e1) (Var x) = Left (Var x)
generalise vars (UniOp op e1) (BinOp op2 e2 e3) =
    case generalise vars (UniOp op e1) e2 of 
        Left e1' => 
           case generalise vars (UniOp op e1) e3 of
             Left e2' => Left (BinOp op2 e1' e2')
             Right (x ** e2') => Right (x ** BinOp op2 (weakenAExp e1') e2')                      
        Right (x ** e1') => case generalise vars (UniOp op e1) e3 of 
            Left e2' => Right (x ** BinOp op2 e1' (weakenAExp e2'))
            Right (y ** e2') => Right (y ** BinOp op2 e1' e2')
generalise _ (Lit _) (Var x) = Left (Var x)

{-
swap(e) = (e[x->x->y, y->lambda->y->x], e[x->x, y->lambda->y]) (second part of tuple needed for eclipse...)
need a way to represent at type level

see elemS in IdrisUtils/Data/Vect/Elem.idr

use searchEq e[x->x->y, y->lambda->y->x] lambda[x -> epsilon]

we can assume we have the 'x'

-}

public export
swap : (x : Fin nvars) 
    -> (y : Fin nvars)
    -> (e : AExp c nvars)
    -> AExp c nvars 
swap x y (Lit m) = Lit m
swap x y (Var v) with (decEq x v)
  swap x y (Var x) | Yes Refl = Var y
  swap x y (Var v) | No contra with (decEq y v)
    swap x y (Var y) | No contra | Yes Refl = Var x
    swap x y (Var v) | No contra | No contra2 = Var v
swap x y (BinOp op e1 e2) = BinOp op (swap x y e1) (swap x y e2)
swap x y (UniOp op e1) = UniOp op (swap x y e1)

public export
swapE : DecEq c =>
        (x : AExp c nvars)
     -> (y : AExp c nvars) 
     -> (e : AExp c nvars)
     -> AExp c nvars 
swapE x y (Lit m) = Lit m
swapE x y (Var v) =
 case (decEq x (Var v)) of
   Yes Refl => y
   No contra => 
      case (decEq y (Var v)) of 
        Yes Refl => x
        No _ => (Var v)
swapE x y (BinOp op e1 e2) =
 case (decEq x (BinOp op e1 e2)) of
  Yes Refl => y
  No contra => 
    case decEq y (BinOp op e1 e2) of 
      Yes Refl => x 
      No _ => BinOp op (swapE x y e1) (swapE x y e2)
swapE x y (UniOp op e1) =
  case (decEq x (UniOp op e1)) of
    Yes Refl => y
    No contra => 
      case decEq y (UniOp op e1) of 
        Yes Refl => x 
        No _ => UniOp op (swapE x y e1)

public export
swapAndGeneralise :  (varA : Fin nvars)
                  -> (varX : Fin nvars) 
                  -> (lam : AExp SInt nvars)
                  -> (e : AExp SInt nvars)
                  -> Maybe (AExp SInt (S nvars))
swapAndGeneralise varA varX lam e with (generalise varA lam e)
  swapAndGeneralise varA varX lamX e | Left e' = Nothing 
  swapAndGeneralise varA varX lamX e | Right (x ** e') with (weaken varX) 
    swapAndGeneralise varA varX lamX e | Right (x ** e') | var' = Just (swap x var' e')

public export 
data ElemA : (x : Fin nvars) 
          -> (ys : AExp c nvars)
          -> Type where
  JustHereVar : ElemA x (Var x) 
  JustNotVar  : ElemA x (Var y )
  JustNotLit  : ElemA x (Lit n)
  JustBinOp   : (there1 : ElemA x e1)
             -> (there2 : ElemA x e2)
             -> ElemA x (BinOp op e1 e2)
  JustUniOp   : (there1: ElemA x e1) 
             -> ElemA x (UniOp op e1)          

public export
data ElemLamA : (lam : AExp c nvars) 
             -> (ys : AExp c nvars)
             -> Type where 
  JustHereL : ElemLamA lam lam 
  JustNotHereL : ElemLamA lam y 
  JustBinOpL : (there1 : ElemLamA lam e1) 
           -> (there2 : ElemLamA lam e2) 
           -> ElemLamA lam (BinOp op e1 e2) 
  JustBinOpLRight : (there1 : ElemLamA lam e2) 
            -> ElemLamA lam (BinOp op e1 e2)

  JustUniOpL : (there : ElemLamA lam e1)
           -> ElemLamA lam (UniOp op e1)

public export 
data ElemLamSimple : Type where 
  JustHereS : ElemLamSimple 
  JustNotHereS : ElemLamSimple
  JustBinOpS : (e1 : ElemLamSimple)
            -> (e2 : ElemLamSimple)
            -> ElemLamSimple 
  JustBinOpSRight : (e1 : ElemLamSimple)
            -> ElemLamSimple 
  JustUniOpS : (e1 : ElemLamSimple)
            -> ElemLamSimple

public export
toElemSimple : (a : ElemLamA lam ys) -> ElemLamSimple 
toElemSimple JustHereL = JustHereS 
toElemSimple JustNotHereL = JustNotHereS 
toElemSimple (JustBinOpL t1 t2) = JustBinOpS (toElemSimple t1) (toElemSimple t2)
toElemSimple (JustBinOpLRight t1) = JustBinOpSRight (toElemSimple t1)
toElemSimple (JustUniOpL t1) = JustUniOpS (toElemSimple t1)

noJust : JustHereS = JustNotHereS -> Void 
noJust Refl impossible

noJust2 : JustHereS = (JustBinOpS _ _) -> Void
noJust2 Refl impossible

noJust3 : JustHereS = (JustBinOpSRight _) -> Void 
noJust3 Refl impossible

noJust4 : JustHereS = (JustUniOpS _) -> Void 
noJust4 Refl impossible

noJust5 : JustNotHereS = JustHereS -> Void 
noJust5 Refl impossible

noJust6 : JustNotHereS = (JustBinOpS _ _) -> Void 
noJust6 Refl impossible

noJust7 : JustNotHereS = (JustBinOpSRight _) -> Void 
noJust7 Refl impossible

noJust8 : JustNotHereS = (JustUniOpS _) -> Void 
noJust8 Refl impossible

noJust9 : (JustBinOpS a b) = JustHereS -> Void 
noJust9 Refl impossible

noJust10 : (JustBinOpS a b) = JustNotHereS -> Void 
noJust10 Refl impossible

noJust11 : (JustBinOpS a b) = (JustBinOpSRight _) -> Void 
noJust11 Refl impossible

noJust12 : (JustBinOpSRight _) = JustHereS -> Void 
noJust12 Refl impossible

noJust13 : (JustBinOpSRight _) = JustNotHereS -> Void 
noJust13 Refl impossible

noJust14 : (JustBinOpSRight _) = (JustBinOpS _ _) -> Void 
noJust14 Refl impossible

noJust15 : (JustUniOpS _) = JustHereS -> Void 
noJust15 Refl impossible

noJust16 : (JustUniOpS _) = JustNotHereS -> Void 
noJust16 Refl impossible

noJust17 : (JustBinOpS _ _ ) = (JustUniOpS _) -> Void 
noJust17 Refl impossible

noJust18 : (JustBinOpSRight a) = (JustUniOpS b) -> Void 
noJust18 Refl impossible

noJust19: (JustUniOpS _) = (JustBinOpS _ _) -> Void 
noJust19 Refl impossible

noJust20 : (JustUniOpS _) = (JustBinOpSRight _) -> Void 
noJust20 Refl impossible

decElem1 : ElemLamA a a -> ElemLamA c c 
decElem1 = ?h

public export
implementation DecEq ElemLamSimple where 
  decEq JustHereS JustHereS = Yes Refl
  decEq JustHereS JustNotHereS = No noJust
  decEq JustHereS (JustBinOpS _ _) = No noJust2
  decEq JustHereS (JustBinOpSRight _) = No noJust3 
  decEq JustHereS (JustUniOpS _) = No noJust4

  decEq JustNotHereS JustHereS = No noJust5 
  decEq JustNotHereS JustNotHereS = Yes Refl 
  decEq JustNotHereS (JustBinOpS _ _) = No noJust6
  decEq JustNotHereS (JustBinOpSRight _) = No noJust7 
  decEq JustNotHereS (JustUniOpS _) = No noJust8

  decEq (JustBinOpS a b) JustHereS = No noJust9 
  decEq (JustBinOpS a b) JustNotHereS = No noJust10 
  decEq (JustBinOpS a b) (JustBinOpS c d) with (decEq a c) 
    decEq (JustBinOpS a b) (JustBinOpS a d) | Yes Refl with (decEq b d)
      decEq (JustBinOpS a b) (JustBinOpS a b) | Yes Refl | Yes Refl = Yes Refl 
      decEq (JustBinOpS a b) (JustBinOpS a d) | Yes Refl | No contra = No (\Refl => contra Refl)
    decEq (JustBinOpS a b) (JustBinOpS c d) | No contra = No (\Refl => contra Refl)
  decEq (JustBinOpS a b) (JustBinOpSRight _) = No noJust11
  decEq (JustBinOpS a b) (JustUniOpS _) = No noJust17

  decEq (JustBinOpSRight _) JustHereS = No noJust12
  decEq (JustBinOpSRight _) JustNotHereS = No noJust13
  decEq (JustBinOpSRight _) (JustBinOpS _ _) = No noJust14

  decEq (JustBinOpSRight a) (JustBinOpSRight b) with (decEq a b) 
    decEq (JustBinOpSRight a) (JustBinOpSRight a) | Yes Refl = Yes Refl 
    decEq (JustBinOpSRight a) (JustBinOpSRight b) | No contra = No (\Refl => contra Refl)

  decEq (JustBinOpSRight a) (JustUniOpS b) = No noJust18

  decEq (JustUniOpS _) JustHereS = No noJust15
  decEq (JustUniOpS _) JustNotHereS = No noJust16
  decEq (JustUniOpS a) (JustUniOpS b) with (decEq a b)
    decEq (JustUniOpS a) (JustUniOpS a) | Yes Refl = Yes Refl 
    decEq (JustUniOpS a) (JustUniOpS b) | No contra = No (\Refl => contra Refl)

  decEq (JustUniOpS _) (JustBinOpS _ _) = No noJust19
  decEq (JustUniOpS _) (JustBinOpSRight _) = No noJust20 


public export
elemA : (x : Fin nvars) -> (ys : AExp c nvars) -> ElemA x ys
elemA x (Lit n) = JustNotLit 
elemA x (Var y) with (decEq x y)
  elemA x (Var x) | Yes Refl = JustHereVar 
  elemA x (Var y) | No contra = JustNotVar
elemA x (BinOp op e1 e2) with (elemA x e1) 
  elemA x (BinOp op e1 e2) | there1 with (elemA x e2) 
    elemA x (BinOp op e1 e2) | there1 | there2 = JustBinOp there1 there2
elemA x (UniOp op e1) with (elemA x e1) 
  elemA x (UniOp op e1) | there = JustUniOp there

public export 
elemL : (DecEq c) => (lam : AExp c nvars) -> (ys : AExp c nvars) -> ElemLamA lam ys 
elemL (Lit n) (Lit m) with (decEq n m) 
  elemL (Lit n) (Lit n) | Yes Refl = JustHereL 
  elemL (Lit n) (Lit m) | No contra = JustNotHereL
elemL (Lit n) (Var x) = JustNotHereL 
elemL (Lit n) (BinOp op e1 e2) with (elemL (Lit n) e1)
  elemL (Lit n) (BinOp op e1 e2) | there1 with (elemL (Lit n) e2) 
    elemL (Lit n) (BinOp op e1 e2) | there1 | there2 = JustBinOpL there1 there2
elemL (Lit n) (UniOp op e1) with (elemL (Lit n) e1) 
  elemL (Lit n) (UniOp op e1) | there1 = JustUniOpL there1
elemL (Var x) (Lit n) = JustNotHereL 
elemL (Var x) (Var y) with (decEq x y) 
  elemL (Var x) (Var x) | Yes Refl = JustHereL 
  elemL (Var x) (Var y) | No contra = JustNotHereL 
elemL (Var x) (BinOp op e1 e2) with (decEq (Var x) e1) 
  elemL (Var x) (BinOp op (Var x) e2) | Yes Refl = JustBinOpL JustHereL JustNotHereL
  elemL (Var x) (BinOp op e1 e2) | No _ with (decEq (Var x) e2)
    elemL (Var x) (BinOp op e1 (Var x)) | No _ | Yes Refl = JustBinOpL JustNotHereL JustHereL
    elemL (Var x) (BinOp op e1 e2) | No _ | No _ = JustNotHereL

-- with (elemL (Var x) e1)
--  elemL (Var x) (BinOp op e1 e2) | there1 with (elemL (Var x) e2) 
--    elemL (Var x) (BinOp op e1 e2) | there1 | there2 = JustBinOpL there1 there2 
elemL (Var x) (UniOp op e1) with (elemL (Var x) e1) 
  elemL (Var x) (UniOp op e1) | there1 = JustUniOpL there1
elemL (BinOp op e1 e2) (Lit n) = JustNotHereL 
elemL (BinOp op e1 e2) (Var x) = JustNotHereL 
elemL (BinOp op e1 e2) (UniOp op2 e3) with (elemL (BinOp op e1 e2) e3)
  elemL (BinOp op e1 e2) (UniOp op2 e3) | there1 = JustUniOpL there1 
elemL (BinOp op e1 e2) (BinOp op2 e3 e4) with (decEq op op2) 
  elemL (BinOp op e1 e2) (BinOp op e3 e4) | Yes Refl with (decEq e1 e3) 
    elemL (BinOp op e1 e2) (BinOp op e1 e4) | Yes Refl | Yes Refl with (decEq e2 e4) 
      elemL (BinOp op e1 e2) (BinOp op e1 e2) | Yes Refl | Yes Refl | Yes Refl = JustHereL 
      elemL (BinOp op e1 e2) (BinOp op e1 e4) | Yes Refl | Yes Refl | No contra = 
          case elemL (BinOp op e1 e2) e4 of 
            there1 => JustBinOpLRight there1
    elemL (BinOp op e1 e2) (BinOp op e3 e4) | Yes Refl | No contra = 
          case elemL (BinOp op e1 e2) e3 of 
            there1 => 
              case elemL (BinOp op e1 e2) e4 of 
                there2 => JustBinOpL there1 there2 
  elemL (BinOp op e1 e2) (BinOp op2 e3 e4) | No contra = 
          case elemL (BinOp op e1 e2) e3 of 
            there1 => 
              case elemL (BinOp op e1 e2) e4 of 
                there2 => JustBinOpL there1 there2
elemL (UniOp op e1) (Lit n) = JustNotHereL
elemL (UniOp op e1) (Var x) = JustNotHereL 
elemL (UniOp op e1) (BinOp op2 e2 e3) with (elemL (UniOp op e1) e2) 
  elemL (UniOp op e1) (BinOp op2 e2 e3) | there1 with (elemL (UniOp op e1) e3)
  elemL (UniOp op e1) (BinOp op2 e2 e3) | there1 | there2 = JustBinOpL there1 there2 
elemL (UniOp op e1) (UniOp op2 e2) with (decEq op op2) 
  elemL (UniOp op e1) (UniOp op e2) | Yes Refl with (decEq e1 e2) 
    elemL (UniOp op e1) (UniOp op e1) | Yes Refl | Yes Refl = JustHereL 
    elemL (UniOp op e1) (UniOp op e2) | Yes Refl | No contra with (elemL (UniOp op e1) e2)
    elemL (UniOp op e1) (UniOp op e2) | Yes Refl | No contra | there1 = JustUniOpL there1 
  elemL (UniOp op e1) (UniOp op2 e2) | No contra with (elemL (UniOp op e1) e2)
    elemL (UniOp op e1) (UniOp op2 e2) | No contra | there1 = JustUniOpL there1
-- elemL _ _ = ?a


public export 
data Eq3 : (g  : AExp c nvars) 
        -> (g' : AExp c nvars)
        -> Type where
  MkEq3 :  
           (p1:  ElemLamA lam g)
        -> (p2 : ElemLamA x g')
        -> (p3 : toElemSimple p1 = toElemSimple p2)
        -> (p4 : ElemLamA x g)
        -> (p5 : ElemLamA lam g')
        -> (p6 : toElemSimple p4 = toElemSimple p5)
        -> Rewrite g g'
        -> Eq3 g g'
