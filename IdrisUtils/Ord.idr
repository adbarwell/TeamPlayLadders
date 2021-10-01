module IdrisUtils.Ord

import public IdrisUtils.Decidability
import public IdrisUtils.Ord.OrdS

%default total

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Propositional equality.
public export
propEq : (x,y : c) -> Type
propEq x y = x = y

||| Symmetry of propositional equality.
public export
sym' : (x,y : a) -> (rule : x = y) -> y = x
sym' x x Refl = Refl

||| Transitivity of propositional equality.
public export
trans' : (x,y,z : c) -> (l : x = y) -> (r : y = z) -> x = z
trans' x x x Refl Refl = Refl

public export
PropEqSetoid : (c : Type) -> (decEq : (x,y : c) -> Dec (x = y)) -> SetoidT c
PropEqSetoid c decEq = MkSetoid {c=c} propEq sym' trans' decEq

||| A strict total ordering over a given carrier type where the equivalence relation is
||| propositional equality (=).
public export
record StrictTotalOrdering (c : Type) where
  constructor MkSTOrdering
  decEq : (x,y : c) -> Dec (x = y)
  ordS : StrictTotalOrderingS c (PropEqSetoid c decEq)

---------------------------------------------------------------------------------------------------
-- [Projections] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
proj_LT : StrictTotalOrdering c -> (c -> c -> Type)
proj_LT ord = proj_LT (ordS ord)

public export
proj_Asym : (ord : StrictTotalOrdering c)
         -> ((x,y : c) -> proj_LT ord x y -> Not (proj_LT ord y x))
proj_Asym ord = proj_Asym (ordS ord)

public export
proj_Trans : (ord : StrictTotalOrdering c)
          -> ((x,y,z : c) -> proj_LT ord x y -> proj_LT ord y z -> proj_LT ord x z)
proj_Trans ord = proj_Trans (ordS ord)

public export
proj_Tricho : (ord : StrictTotalOrdering c)
           -> (x,y : c)
           -> Trichotomy (PropEqSetoid c (decEq ord)) (proj_LT ord) (proj_Asym ord) x y
proj_Tricho ord = proj_Tricho (ordS ord)

public export
proj_decLT : (ord : StrictTotalOrdering c) -> ((x,y : c) -> Dec (proj_LT ord x y))
proj_decLT ord = proj_decLT (ordS ord)

---------------------------------------------------------------------------------------------------
-- [LTE (Derived)] --------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data LTE : (ord : StrictTotalOrdering c) -> (x : c) -> (y : c) -> Type where
  IsEq : LTE ord x x
  IsLT : (lt : proj_LT ord x y) -> LTE ord x y

public export
proj_LTE : (ord : StrictTotalOrdering c) -> ((x : c) -> (y : c) -> Type)
proj_LTE = LTE

export
decLTE_gt : (neq : Not (x = y)) -> (gt : Not (proj_LT ord x y)) -> Not (LTE ord x y)
decLTE_gt neq gt IsEq = neq Refl
decLTE_gt neq gt (IsLT lt) = gt lt

export
decLTE : (ord : StrictTotalOrdering c) -> (x : c) -> (y : c) -> Dec (proj_LTE ord x y)
decLTE ord x y with (decEq ord x y)
  decLTE ord x x | Yes Refl = Yes IsEq
  decLTE ord x y | No  neq  with (proj_decLT ord x y)
    decLTE ord x y | No neq | Yes lt = Yes (IsLT lt)
    decLTE ord x y | No neq | No  gt = No (decLTE_gt neq gt)

---------------------------------------------------------------------------------------------------
-- [Interfaces] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
interface StrictTotalOrder c where
  theOrder : StrictTotalOrdering c

---------------------------------------------------------------------------------------------------
-- [Positive Decidability] ------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
PropLT : (ord : StrictTotalOrdering c)
      -> (x,y : c)
      -> (soundP : proj_LT ord x y -> Not (LTE ord y x))
      -> (soundQ : LTE ord y x -> Not (proj_LT ord x y))
      -> Prop
PropLT ord x y soundP soundQ =
  MkProp (proj_LT ord x y) (LTE ord y x) (proj_decLT ord x y) (decLTE ord y x) soundP soundQ

public export
interface StrictTotalOrder c => DecPLT c where
  lt_sound  : {x,y : c} -> proj_LT (Ord.theOrder) x y -> Not (LTE (Ord.theOrder) y x)
  gte_sound : {x,y : c} -> LTE (Ord.theOrder) y x -> Not (proj_LT (Ord.theOrder) x y)

export
decPLT : DecPLT c => (x,y : c) -> PDec (PropLT Ord.theOrder x y Ord.lt_sound Ord.gte_sound)
decPLT x y with (proj_Tricho theOrder x y)
  decPLT x x | IsEq Refl = No IsEq
  decPLT x y | IsBinR_xRy lt = Yes lt
  decPLT x y | IsBinR_yRx gt = No (IsLT gt)
