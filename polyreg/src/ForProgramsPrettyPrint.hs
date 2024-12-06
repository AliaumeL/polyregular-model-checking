module ForProgramsPrettyPrint (prettyPrintProgram) where

import ForPrograms
import ForProgramsTyping
import Parser.HighLevelForProgram.Print (printTree)
import qualified Parser.HighLevelForProgram.Abs as A
import Parser.HighLevelForProgram.Abs (Ident(..))

-- To pretty print, we convert the program to 
-- an abstract syntax tree and then print it
-- using the (printTree) function from the parser


toAbsType :: ValueType -> A.Type
toAbsType (TBool) = A.TBool
toAbsType (TOutput t) = toAbsOutputType t
toAbsType (TConst t) = toAbsOutputType t
toAbsType (TPos _) = error "Positional types should not appear in the abstract syntax tree"



toAbsComp :: Comp -> A.BinOp
toAbsComp Eq = A.BinOpEq
toAbsComp Neq = A.BinOpNeq
toAbsComp Lt = A.BinOpLt
toAbsComp Gt = A.BinOpGt
toAbsComp Leq = A.BinOpLeq
toAbsComp Geq = A.BinOpGeq

toAbsOutputType :: OutputType -> A.Type
toAbsOutputType (TOList t) = A.TList (toAbsOutputType t)
toAbsOutputType (TOChar) = A.TChar


toAbsProgram :: Program String ValueType -> A.Program
toAbsProgram (Program stmts _) = A.ProgramC (map toAbsStmtFun stmts)

toAbsStmtFun :: StmtFun String ValueType -> A.Func 
toAbsStmtFun (StmtFun name args stmt t) = A.FuncC (Ident name) 
                                                  (map toAbsArgD args) 
                                                  (toAbsType t)
                                                  (toAbsStmt stmt)


toAbsArgD :: (String, ValueType, [String]) -> A.ArgD
toAbsArgD (name, t, []) = A.ArgDSole (Ident name) (toAbsType t)
toAbsArgD (name, t, args) = A.ArgDWithPoses (Ident name) (toAbsType t) (map Ident args)

toAbsStmt :: Stmt String ValueType -> [A.Stmt]
toAbsStmt (SYield o _) = pure $ A.SYield (toAbsOExpr o)
toAbsStmt (SOReturn o _) = pure $ A.SReturn (toAbsOExpr o)
toAbsStmt (SBReturn b _) = pure $ A.SReturn (toAbsBExpr b)
toAbsStmt (SIf b s1 s2 _) = pure $ A.SIfE (toAbsBExpr b) (toAbsStmt s1) (toAbsStmt s2)
toAbsStmt (SLetOutput (v, t) o s _) = pure $ A.SLetIn (Ident v) (toAbsType t) (toAbsOExpr o) [s']
    where 
        s' = case toAbsStmt s of
                [x] -> x
                _ -> error "(toAbsStmt) let output should have a single statement"
toAbsStmt (SLetBoolean v s _) = pure $ A.SLetBIn (Ident v) [s']
    where
        s' = case toAbsStmt s of
                [x] -> x
                _ -> error "(toAbsStmt) let boolean should have a single statement"
toAbsStmt (SSetTrue v _) = pure $ A.SLetSetTrue (Ident v)
toAbsStmt (SFor (i, e, t) v s _) = pure $ A.SFor (Ident i) (Ident e) (toAbsType t) (toAbsOExpr v) (toAbsStmt s)
toAbsStmt (SSeq ss _) = concatMap toAbsStmt ss

toAbsOExpr :: OExpr String ValueType -> A.Expr
toAbsOExpr (OVar v _) = A.VEVal (Ident v)
toAbsOExpr (OConst c _) = toAbsCExpr c
toAbsOExpr (OList os _) = A.VEListConstr (map toAbsOExpr os)
toAbsOExpr (ORev o _) = A.VERev (toAbsOExpr o)
toAbsOExpr (OIndex o p _) = A.VEFunc (Ident "index") [toAbsArgA (o, [p])]
toAbsOExpr (OApp v os _) = A.VEFunc (Ident v) (map toAbsArgA os)
toAbsOExpr (OGen s _) = A.VEGen s'
    where
        s' = case toAbsStmt s of
                [x] -> x
                _ -> error "(toAbsOExpr) generator should have a single statement"

cexprToString :: CExpr String ValueType -> String
cexprToString (CChar c _) = [c]
cexprToString (CList s _) = concatMap cexprToString s

toAbsCExpr :: CExpr String ValueType -> A.Expr
toAbsCExpr (CChar c _) = A.VEChar c
toAbsCExpr s@(CList _ (TOutput (TOList TOChar))) = A.VEString (cexprToString s)
toAbsCExpr (CList s _) = A.VEListConstr (map toAbsCExpr s)

toAbsPExpr :: PExpr String ValueType -> Ident
toAbsPExpr (PVar v _) = Ident v

toAbsBExpr :: BExpr String ValueType -> A.Expr
toAbsBExpr (BApp v os _) = A.VEFunc (Ident v) (map toAbsArgA os)
toAbsBExpr (BLitEq t c o _) = A.VEFunc (Ident "lit_eq") (map toAbsArgA [(OConst c t, []), (o, [])])
toAbsBExpr (BConst b _) = if b then A.BETrue else A.BEFalse
toAbsBExpr (BNot b _) = A.BENot (toAbsBExpr b)
toAbsBExpr (BOp And b1 b2 _) = A.BEAnd (toAbsBExpr b1) (toAbsBExpr b2)
toAbsBExpr (BOp Or b1 b2 _) = A.BEOr (toAbsBExpr b1) (toAbsBExpr b2)
toAbsBExpr (BOp Impl b1 b2 _) = A.BEOr (A.BENot (toAbsBExpr b1)) (toAbsBExpr b2)
toAbsBExpr (BOp Iff b1 b2 _) = A.BEAnd (A.BEOr (A.BENot (toAbsBExpr b1)) (toAbsBExpr b2)) (A.BEOr (toAbsBExpr b1) (A.BENot (toAbsBExpr b2)))
toAbsBExpr (BComp comp p1 p2 _) = A.BEBinOp (A.VEVal (toAbsPExpr p1))
                                            (toAbsComp comp)
                                            (A.VEVal (toAbsPExpr p2))
toAbsBExpr (BVar v _) = A.VEVal (Ident v)
toAbsBExpr (BGen s _) = A.VEGen s'
    where
        s' = case toAbsStmt s of
                [x] -> x
                _ -> error "(toAbsBExpr) generator should have a single statement"


toAbsArgA :: (OExpr String ValueType, [PExpr String ValueType]) -> A.VEArg
toAbsArgA (c, []) = A.VEArgSole (toAbsOExpr c)
toAbsArgA (c, ps) = A.VEArgWithPoses (toAbsOExpr c) (map toAbsPExpr ps)

prettyPrintProgram :: Program String ValueType -> String
prettyPrintProgram = printTree . toAbsProgram
