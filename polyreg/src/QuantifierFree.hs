module QuantifierFree where

data BinOp  = Conj | Disj | Impl | Equiv deriving (Show, Eq, Ord)

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

-- TODO: add "having the same character" as a test.
data TestOp = Eq | Neq | Lt | Le | Gt | Ge deriving (Show, Eq, Ord)

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
