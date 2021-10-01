module Input

import public IdrisUtils.Data.Integer -- Carrier type representation
import public Derivation -- The rewrite system

---------------------------------------------------------------------------------------------------
-- [Functions] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
varX : Fin 3
varX = FZ

export
varY : Fin 3
varY = FS FZ

export
varA : Fin 3
varA = FS (FS FZ)

||| epsilon(x) = x^3 mod n
export
epsilon : (x : AExp SInt 3) -> AExp SInt 3
epsilon x = UniOp Square x

||| lambda(x) = a*x mod n
export
lambda : (x : AExp SInt 3) -> AExp SInt 3
lambda x = BinOp Mult (Var varA) x

---------------------------------------------------------------------------------------------------
-- [interface] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| The maximum depth to which we grow/search the trees.
||| (Effectively, maximum length of rewrite steps.)
d : Nat
d = 30

main : IO ()
main = putStrLn $ show (deriveF d (lambda (Var varX)) (epsilon (Var varX)))
