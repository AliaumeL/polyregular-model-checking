-- File generated by the BNF Converter (bnfc 2.9.5).

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | The abstract syntax of language SimpleForProgram.

module Parser.SimpleForProgram.Abs where

import Prelude (Char, String)
import qualified Prelude as C (Eq, Ord, Show, Read)
import qualified Data.String

data Program = Program VarStmt
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data VarStmt = VarStmt [Ident] [Stmt] | NoVarStmt [Stmt]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data FORInput = FInput | FRevInput
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Stmt
    = SFor Ident FORInput VarStmt
    | SSetTrue Ident
    | SIfElse BExpr [Stmt] [Stmt]
    | SIf BExpr [Stmt]
    | SPrintChar Char
    | SPrintLabel Ident
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data BExpr
    = BTrue
    | BFalse
    | BVar Ident
    | BNot BExpr
    | BTest Ident BTest Ident
    | BLabelAt Ident Char
    | BAnd BExpr BExpr
    | BOr BExpr BExpr
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data BTest = TLe | TLt | TGe | TGt | TEq | TNeq
  deriving (C.Eq, C.Ord, C.Show, C.Read)

newtype Ident = Ident String
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)
