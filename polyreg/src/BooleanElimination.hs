module BooleanElimination (hasBooleanGen, removeBooleanGen) where

import ForPrograms
import ForProgramsTyping

-- In this module, we try to remove *boolean generators*
-- from the AST.
--
-- We assume that
-- 1. there are no "BLitEq" except for chars
-- 2. there are no "BApp"
--


hasBooleanGen :: Program v t -> Bool
hasBooleanGen (Program funcs m) = any hasBooleanGenStmtFun funcs

hasBooleanGenStmtFun :: StmtFun v t -> Bool
hasBooleanGenStmtFun (StmtFun _ _ stmt _) = hasBooleanGenStmt stmt

hasBooleanGenStmt :: Stmt v t -> Bool
hasBooleanGenStmt (SYield o _) = hasBooleanGenOExpr o
hasBooleanGenStmt (SOReturn o _) = hasBooleanGenOExpr o
hasBooleanGenStmt (SBReturn b _) = hasBooleanGenBExpr b
hasBooleanGenStmt (SIf b s1 s2 _) = hasBooleanGenBExpr b || hasBooleanGenStmt s1 || hasBooleanGenStmt s2
hasBooleanGenStmt (SLetOutput _ o s _) = hasBooleanGenOExpr o || hasBooleanGenStmt s
hasBooleanGenStmt (SLetBoolean _ s _) = hasBooleanGenStmt s
hasBooleanGenStmt (SSetTrue _ _) = False
hasBooleanGenStmt (SFor _ v s _) = hasBooleanGenOExpr v || hasBooleanGenStmt s
hasBooleanGenStmt (SSeq ss _) = any hasBooleanGenStmt ss

hasBooleanGenOExpr :: OExpr v t -> Bool
hasBooleanGenOExpr (OVar _ _) = False
hasBooleanGenOExpr (OConst _ _) = False
hasBooleanGenOExpr (OList os _) = any hasBooleanGenOExpr os
hasBooleanGenOExpr (ORev o _) = hasBooleanGenOExpr o
hasBooleanGenOExpr (OIndex o p _) = hasBooleanGenOExpr o
hasBooleanGenOExpr (OApp _ os _) = any (hasBooleanGenOExpr . fst) os
hasBooleanGenOExpr (OGen s _) = hasBooleanGenStmt s

hasBooleanGenBExpr :: BExpr v t -> Bool
hasBooleanGenBExpr (BConst _ _) = False
hasBooleanGenBExpr (BNot b _) = hasBooleanGenBExpr b
hasBooleanGenBExpr (BOp _ b1 b2 _) = hasBooleanGenBExpr b1 || hasBooleanGenBExpr b2
hasBooleanGenBExpr (BComp _ p1 p2 _) = False
hasBooleanGenBExpr (BVar _ _) = False
hasBooleanGenBExpr (BGen s _) = True


-- To remove boolean generators, we need to *inline* the generators
-- into the expressions where they are used.
removeBooleanGen :: Program v t -> Program v t
removeBooleanGen = undefined



