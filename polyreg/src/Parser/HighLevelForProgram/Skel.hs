-- File generated by the BNF Converter (bnfc 2.9.5).

-- Templates for pattern matching on abstract syntax

{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module Parser.HighLevelForProgram.Skel where

import Prelude (($), Either(..), String, (++), Show, show)
import qualified Parser.HighLevelForProgram.Abs

type Err = Either String
type Result = Err String

failure :: Show a => a -> Result
failure x = Left $ "Undefined case: " ++ show x

transIdent :: Parser.HighLevelForProgram.Abs.Ident -> Result
transIdent x = case x of
  Parser.HighLevelForProgram.Abs.Ident string -> failure x

transProgram :: Parser.HighLevelForProgram.Abs.Program -> Result
transProgram x = case x of
  Parser.HighLevelForProgram.Abs.ProgramC funcs -> failure x

transFunc :: Parser.HighLevelForProgram.Abs.Func -> Result
transFunc x = case x of
  Parser.HighLevelForProgram.Abs.FuncC ident argds type_ stmts -> failure x

transStmt :: Parser.HighLevelForProgram.Abs.Stmt -> Result
transStmt x = case x of
  Parser.HighLevelForProgram.Abs.SFor ident1 ident2 expr stmts -> failure x
  Parser.HighLevelForProgram.Abs.SIf expr stmts -> failure x
  Parser.HighLevelForProgram.Abs.SIfE expr stmts1 stmts2 -> failure x
  Parser.HighLevelForProgram.Abs.SYield expr -> failure x
  Parser.HighLevelForProgram.Abs.SReturn expr -> failure x
  Parser.HighLevelForProgram.Abs.SLetIn ident type_ expr stmt -> failure x
  Parser.HighLevelForProgram.Abs.SLetBIn ident type_ stmt -> failure x
  Parser.HighLevelForProgram.Abs.SLetSetTrue ident -> failure x

transExpr :: Parser.HighLevelForProgram.Abs.Expr -> Result
transExpr x = case x of
  Parser.HighLevelForProgram.Abs.VEChar char -> failure x
  Parser.HighLevelForProgram.Abs.VEString string -> failure x
  Parser.HighLevelForProgram.Abs.VEListConstr exprs -> failure x
  Parser.HighLevelForProgram.Abs.VEGen type_ stmt -> failure x
  Parser.HighLevelForProgram.Abs.VEVal ident -> failure x
  Parser.HighLevelForProgram.Abs.VERev expr -> failure x
  Parser.HighLevelForProgram.Abs.VEFunc ident veargs -> failure x
  Parser.HighLevelForProgram.Abs.BETrue -> failure x
  Parser.HighLevelForProgram.Abs.BEFalse -> failure x
  Parser.HighLevelForProgram.Abs.BENot expr -> failure x
  Parser.HighLevelForProgram.Abs.BEBinOp expr1 binop expr2 -> failure x
  Parser.HighLevelForProgram.Abs.BEAnd expr1 expr2 -> failure x
  Parser.HighLevelForProgram.Abs.BEOr expr1 expr2 -> failure x

transType :: Parser.HighLevelForProgram.Abs.Type -> Result
transType x = case x of
  Parser.HighLevelForProgram.Abs.TChar -> failure x
  Parser.HighLevelForProgram.Abs.TList type_ -> failure x
  Parser.HighLevelForProgram.Abs.TBool -> failure x

transVEArg :: Parser.HighLevelForProgram.Abs.VEArg -> Result
transVEArg x = case x of
  Parser.HighLevelForProgram.Abs.VEArgSole expr -> failure x
  Parser.HighLevelForProgram.Abs.VEArgWithPoses expr idents -> failure x

transArgD :: Parser.HighLevelForProgram.Abs.ArgD -> Result
transArgD x = case x of
  Parser.HighLevelForProgram.Abs.ArgDSole ident type_ -> failure x
  Parser.HighLevelForProgram.Abs.ArgDWithPoses ident type_ idents -> failure x

transBinOp :: Parser.HighLevelForProgram.Abs.BinOp -> Result
transBinOp x = case x of
  Parser.HighLevelForProgram.Abs.BinOpEq -> failure x
  Parser.HighLevelForProgram.Abs.BinOpNeq -> failure x
  Parser.HighLevelForProgram.Abs.BinOpLeq -> failure x
  Parser.HighLevelForProgram.Abs.BinOpLt -> failure x
  Parser.HighLevelForProgram.Abs.BinOpGeq -> failure x
  Parser.HighLevelForProgram.Abs.BinOpGt -> failure x
  Parser.HighLevelForProgram.Abs.BinOpVEq -> failure x
  Parser.HighLevelForProgram.Abs.BinOpVNe -> failure x
