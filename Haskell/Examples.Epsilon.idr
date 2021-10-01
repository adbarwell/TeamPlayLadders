module Examples.Epsilon

import public IdrisUtils.Data.Integer
import public Lang
import public SearchEq
import public SearchSt
import public Generalise
import public Lang.Prop.DecEq
import public Lang.Base
import public Examples.Vars


epsilon : AExp SInt 3
epsilon = UniOp Square (Var varX)
