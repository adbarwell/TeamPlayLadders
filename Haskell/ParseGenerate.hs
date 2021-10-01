module ParseGenerate where

import Parsing
import Data.Char

data Exp =
          Num Int 
        | Var String 
        | Plus String String 
        | Mul Exp Exp 
    deriving Show

parseExp :: Parser Exp 
parseExp = do x <- identifier
              symbol "*"
              y <- identifier
              return (Plus x y) 

ucfirst x = (toUpper $ head x) : (toLower <$> tail x)

header :: String -> String
header f = "module Examples." ++ f ++ "\n\nimport public IdrisUtils.Data.Integer\nimport public Lang\nimport public SearchEq\nimport public SearchSt\nimport public Generalise\nimport public Lang.Prop.DecEq\nimport public Lang.Base\nimport public Examples.Vars\n\n\n"

generate :: String -> Exp -> String 
generate f (Plus x y) = 
    if ( x == y) then f ++ " : AExp SInt 3\n" ++ f ++ " = " ++ "UniOp Square (Var var" ++ (map toUpper x) ++ ")\n"  
                 else f ++ " : AExp SInt 3\n"++ f ++ " = " ++ "BinOp Mult (Var var" ++ (map toUpper x) ++ ") (Var var" ++ (map toUpper x) ++ ") \n" 


run file = do
                    x <- readFile file
                    let p = parse parseExp x
                    let g = ((header (ucfirst file)) ++ generate file (fst (head p)))
                    writeFile ("Examples."++(ucfirst file)++".idr") g
