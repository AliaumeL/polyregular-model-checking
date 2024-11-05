module HighLevelForPrograms where

type VarName = String

data VType = 
      TChar
    | TList VType
  deriving (Show, Eq)

data VValue alphabet = 
      VChar alphabet
    | VList [VValue alphabet]
  deriving (Show, Eq)

data PosType alphabet = PosType (VExpression alphabet)

data ArgType alphabet = 
      TVal (VType)
    | TPos (VExpression alphabet)
  deriving (Show, Eq)

data Function alphabet = Function {
    name :: String,
    args :: [(VarName, ArgType alphabet)],
    body :: (StatementBlock alphabet)
} deriving (Show, Eq)

-- A Statement Block is a list of statements, together with a list of variables that are defined for the block.
data StatementBlock a = StatementBlock [VarName] [Statement a] VType
  deriving (Show, Eq)

data Statement a = 
      For VarName VarName (VExpression a) (StatementBlock a)
    | If (BoolExpr a) [Statement a] [Statement a]
    | Yield (VExpression a)
    | Let VarName (VExpression a) (Statement a)
    | SetTrue VarName
  deriving(Show, Eq)

-- Expressions of type VType
data VExpression alphabet = 
            ListLiteral (VValue alphabet) (VType)
          | ListConstructor [VExpression alphabet]
          | ListExpression (StatementBlock alphabet)
          | VVar VarName
          | VRev (VExpression alphabet)
          | VFunctionCall String [Expression alphabet]
  deriving (Show, Eq)

data BoolExpr a = 
      BVar String 
    | BinOp BinOpT (BoolExpr a) (BoolExpr a) 
    | BNot (BoolExpr a)
    | BLit Bool 
    -- BEqVal compares together two strings. 
    -- This is only allowed if the left-hand side is the value of a for iterator, and the right-hand side is a ListLiteral 
    | BEqVal (VExpression a) (VExpression a)
    | BPosBinOp PosBinOpT VarName VarName
  deriving (Show, Eq)

data BinOpT = And | Or | Implies
  deriving (Show, Eq)
data PosBinOpT = PosEq | PosNeq | PosLeq | PosGeq | PosLt | PosGt
  deriving (Show, Eq)

data Expression a = BoolExpr (BoolExpr a) | PosExpr VarName | ValExpr (VExpression a)  
  deriving (Show, Eq)
    

