module HighLevelForPrograms where

import Control.Monad.State
import Control.Monad.Reader

type VarName = String

data VType alphabet = 
      TChar alphabet
    | TList (Type alphabet)

data PosType alphabet = PosType (VExpression alphabet)

data Type alphabet = 
      TBool
    | TVal (VType alphabet)
    | TPos (VExpression alphabet)

data Function alphabet = Function {
    name :: String,
    args :: [(VarName, Type alphabet)],
    body :: (StatementBlock alphabet)
}

-- A Statement Block is a list of statements, together with a list of variables that are defined for the block.
data StatementBlock a = StatementBlock [VarName] [Statement a] (VType a)

data VarNameOrPlaceHolder =
          Actual VarName
        | PlaceHolder

data Statement a = 
      For VarNameOrPlaceHolder VarNameOrPlaceHolder (VExpression a) (StatementBlock a)
    | If (BoolExpr a) [Statement a] [Statement a]
    | Yield (VExpression a)
    | Let VarName (VExpression a) (Statement a)
    | SetTrue VarName


-- Expressions of type VType
data VExpression alphabet = 
            ListLiteral [VExpression alphabet]
          | ListExpression (StatementBlock alphabet)
          | EmptyList (Type alphabet)
          | VVar VarName
          | VFunctionCall String [VExpression alphabet]

data BoolExpr a = 
      BVar String 
    | BinOp BinOpT (BoolExpr a) (BoolExpr a) 
    | BNot (BoolExpr a)
    | BLit Bool 
    -- BEqVal compares together two strings. 
    -- This is only allowed if the left-hand side is the value of a for iterator, and the right-hand side is a ListLiteral 
    | BEqVal (VExpression a) (VExpression a)
    | BAnd (BoolExpr a) (BoolExpr a)
    | BOr (BoolExpr a) (BoolExpr a)

data BinOpT = And | Or | Implies
    

