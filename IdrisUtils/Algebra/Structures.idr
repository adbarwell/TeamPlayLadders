module IdrisUtils.Algebra.Structures

%default total

---------------------------------------------------------------------------------------------------
-- [Group-like Structures] ------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Magma] ----------------------------------------------------------------------------------------

||| A carrier type equipped with a binary operation.
|||
public export
data Magma : (c : Type) -> (op : c -> c -> c) -> Type where
  MkMagma : {c : Type} -> (op : c -> c -> c) -> Magma c op

-- [Semigroup] ------------------------------------------------------------------------------------

||| An associative magma.
|||
public export
record Semigroup (c : Type) (op : c -> c -> c) where
  constructor MkSemigroup
  isMagma : Magma c op
  opAssociative : (x,y,z : c) -> op (op x y) z = op x (op y z)

-- [Monoid] ---------------------------------------------------------------------------------------

||| A semigroup with an identity element.
|||
public export
record Monoid (c : Type) (op : c -> c -> c) (e : c) where
  constructor MkMonoid
  isSemigroup : Semigroup c op
  opLeftIdentity : (x : c) -> op e x = x
  opRightIdentity : (x : c) -> op x e = x

-- [Group] ----------------------------------------------------------------------------------------

||| A monoid with a unary operation (inverse), giving rise to inverse elements.
|||
public export
record Group (c : Type) (op : c -> c -> c) (e : c) (inv : c -> c) where
  constructor MkGroup
  isMonoid : Monoid c op e
  opLeftInverse : (x : c) -> op x (inv x) = e
  opRightInverse : (x : c) -> op (inv x) x = e

-- [Abelian Group] --------------------------------------------------------------------------------

||| A group whose binary operation is commutative.
|||
public export
record CommGroup (c : Type) (op : c -> c -> c) (e : c) (inv : c -> c) where
  constructor MkCommGroup
  isGroup : Group c op e inv
  opCommutative : (x,y : c) -> op x y = op y x

---------------------------------------------------------------------------------------------------
-- [Ring-like Structures] -------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Semiring] -------------------------------------------------------------------------------------

||| A carrier type equipped with two operations, addition and multiplication, s.t. addition forms
||| a commutative monoid with an identity element, and multiplication is a monoid with an
||| identity element. Multiplication left and right distributes over addition, and the additive
||| identity is an absorbing element.
|||
public export
record Semiring (c : Type) (add, mul : c -> c -> c) (zero, one : c) where
  constructor MkSemiring
  addIsMonoid : Monoid c add zero
  addCommutative : (x,y : c) -> add x y = add y x
  mulIsMonoid : Monoid c mul one
  leftDistrib : (x,y,z : c) -> mul x (add y z) = add (mul x y) (mul x z)
  rightDistrib : (x,y,z : c) -> mul (add x y) z = add (mul x z) (mul y z)
  zeroLeftAbsorb : (x : c) -> mul zero x = zero
  zeroRightAbsorb : (x : c) -> mul x zero = zero

-- [Ring] -----------------------------------------------------------------------------------------

||| A semiring whose additive monoid is an abelian group.
|||
public export
record Ring (c : Type) (add, mul : c -> c -> c) (zero, one : c) (inv : c -> c) where
  constructor MkRing
  addIsCommGroup : CommGroup c add zero inv
  mulIsMonoid : Monoid c mul one
  leftDistrib : (x,y,z : c) -> mul x (add y z) = add (mul x y) (mul x z)
  rightDistrib : (x,y,z : c) -> mul (add x y) z = add (mul x z) (mul y z)

-- [Commutative Ring] -----------------------------------------------------------------------------

||| A ring in which the multiplication operation is commutative.
|||
public export
record CommRing (c : Type) (add, mul : c -> c -> c) (zero, one : c) (inv : c -> c) where
  constructor MkCommRing
  isRing : Ring c add mul zero one inv
  mulCommutative : (x,y : c) -> mul x y = mul y x

-- [Field] -----------------------------------------------------------------------------------------

||| A commutative ring which contains a multiplicative inverse for every non-zero element.
|||
public export
record Field (c : Type) (add, mul : c -> c -> c) (zero, one : c) (addinv, mulinv : c -> c) where
  constructor MkField
  isCommRing : CommRing c add mul zero one addinv
  zeroNeqOne : Not (zero = one)
  nonZeroInvertible : (x : c) -> Not (x = zero) -> mul x (mulinv x) = one
  
