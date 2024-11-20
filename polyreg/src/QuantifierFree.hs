module QuantifierFree where


data BinOp  = Conj | Disj | Impl | Equiv deriving (Show, Eq)

binOpSemantics :: BinOp -> Bool -> Bool -> Bool
binOpSemantics Conj  = (&&)
binOpSemantics Disj  = (||)
binOpSemantics Impl  = \x y -> not x || y
binOpSemantics Equiv = (==)

prettyPrintBin :: BinOp -> String
prettyPrintBin Conj  = "∧"
prettyPrintBin Disj  = "∨"
prettyPrintBin Impl  = "⇒"
prettyPrintBin Equiv = "⇔"



data TestOp = Eq | Neq | Lt | Le | Gt | Ge deriving (Show, Eq)

prettyPrintOp :: TestOp -> String
prettyPrintOp Eq  = "="
prettyPrintOp Neq = "≠"
prettyPrintOp Lt  = "<"
prettyPrintOp Le  = "≤"
prettyPrintOp Gt  = ">"
prettyPrintOp Ge  = "≥"

testOpSemantics :: TestOp -> Int -> Int -> Bool
testOpSemantics Eq  = (==)
testOpSemantics Neq = (/=)
testOpSemantics Lt  = (<)
testOpSemantics Le  = (<=)
testOpSemantics Gt  = (>)
testOpSemantics Ge  = (>=)
