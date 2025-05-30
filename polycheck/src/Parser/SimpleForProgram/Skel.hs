-- File generated by the BNF Converter (bnfc 2.9.5).

-- Templates for pattern matching on abstract syntax

{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module Parser.SimpleForProgram.Skel where

import Prelude (($), Either(..), String, (++), Show, show)
import qualified Parser.SimpleForProgram.Abs

type Err = Either String
type Result = Err String

failure :: Show a => a -> Result
failure x = Left $ "Undefined case: " ++ show x

transIdentHash :: Parser.SimpleForProgram.Abs.IdentHash -> Result
transIdentHash x = case x of
  Parser.SimpleForProgram.Abs.IdentHash string -> failure x

transProgram :: Parser.SimpleForProgram.Abs.Program -> Result
transProgram x = case x of
  Parser.SimpleForProgram.Abs.Program varstmt -> failure x

transVarStmt :: Parser.SimpleForProgram.Abs.VarStmt -> Result
transVarStmt x = case x of
  Parser.SimpleForProgram.Abs.VarStmt identhashs stmts -> failure x
  Parser.SimpleForProgram.Abs.NoVarStmt stmts -> failure x

transFORInput :: Parser.SimpleForProgram.Abs.FORInput -> Result
transFORInput x = case x of
  Parser.SimpleForProgram.Abs.FInput -> failure x
  Parser.SimpleForProgram.Abs.FRevInput -> failure x

transStmt :: Parser.SimpleForProgram.Abs.Stmt -> Result
transStmt x = case x of
  Parser.SimpleForProgram.Abs.SFor identhash forinput varstmt -> failure x
  Parser.SimpleForProgram.Abs.SSetTrue identhash -> failure x
  Parser.SimpleForProgram.Abs.SIfElse bexpr stmts1 stmts2 -> failure x
  Parser.SimpleForProgram.Abs.SIf bexpr stmts -> failure x
  Parser.SimpleForProgram.Abs.SPrintChar char -> failure x
  Parser.SimpleForProgram.Abs.SPrintLabel identhash -> failure x
  Parser.SimpleForProgram.Abs.SSkip -> failure x

transBExpr :: Parser.SimpleForProgram.Abs.BExpr -> Result
transBExpr x = case x of
  Parser.SimpleForProgram.Abs.BTrue -> failure x
  Parser.SimpleForProgram.Abs.BFalse -> failure x
  Parser.SimpleForProgram.Abs.BVar identhash -> failure x
  Parser.SimpleForProgram.Abs.BNot bexpr -> failure x
  Parser.SimpleForProgram.Abs.BTest identhash1 btest identhash2 -> failure x
  Parser.SimpleForProgram.Abs.BLabelAt identhash char -> failure x
  Parser.SimpleForProgram.Abs.BAnd bexpr1 bexpr2 -> failure x
  Parser.SimpleForProgram.Abs.BOr bexpr1 bexpr2 -> failure x

transBTest :: Parser.SimpleForProgram.Abs.BTest -> Result
transBTest x = case x of
  Parser.SimpleForProgram.Abs.TLe -> failure x
  Parser.SimpleForProgram.Abs.TLt -> failure x
  Parser.SimpleForProgram.Abs.TGe -> failure x
  Parser.SimpleForProgram.Abs.TGt -> failure x
  Parser.SimpleForProgram.Abs.TEq -> failure x
  Parser.SimpleForProgram.Abs.TNeq -> failure x
