module ForPrograms.HighLevel.PrettyPrint  where

import ForPrograms.HighLevel
import ForPrograms.HighLevel.Typing
import Parser.HighLevelForProgram.Print (printTree)
import qualified Parser.HighLevelForProgram.Abs as A
import Parser.HighLevelForProgram.Abs (Ident(..))

import Logic.QuantifierFree

-- To pretty print, we convert the program to 
-- an abstract syntax tree and then print it
-- using the (printTree) function from the parser


toAbsType :: ValueType -> A.Type
toAbsType (TBool) = A.TBool
toAbsType (TOutput t) = toAbsOutputType t
toAbsType (TPos _) = error "Positional types should not appear in the abstract syntax tree"



toAbsComp :: TestOp -> A.BinOp
toAbsComp Eq = A.BinOpEq
toAbsComp Neq = A.BinOpNeq
toAbsComp Lt = A.BinOpLt
toAbsComp Gt = A.BinOpGt
toAbsComp Le = A.BinOpLeq
toAbsComp Ge = A.BinOpGeq

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
toAbsStmt (SLetOutput (v, t) o s _) = pure $ A.SLetIn (Ident v) (toAbsOExpr o) (toAbsStmt s)
toAbsStmt (SLetBoolean v s _) = pure $ A.SLetBIn (Ident v) (toAbsStmt s)
toAbsStmt (SSetTrue v _) = pure $ A.SLetSetTrue (Ident v)
toAbsStmt (SFor Forward (i, e, t) v s _) = pure $ A.SFor (Ident i) (Ident e) (toAbsOExpr v) (toAbsStmt s)
toAbsStmt (SFor Backward (i, e, t) v s _) = pure $ A.SRFor (Ident i) (Ident e) (toAbsOExpr v) (toAbsStmt s)
toAbsStmt (SSeq ss _) = concatMap toAbsStmt ss

toAbsOExpr :: OExpr String ValueType -> A.Expr
toAbsOExpr (OVar v _) = A.VEVal (Ident v)
toAbsOExpr (OConst c _) = toAbsCExpr c
toAbsOExpr (OList os _) = A.VEListConstr (map toAbsOExpr os)
toAbsOExpr (OApp v os _) = A.VEFunc (Ident v) (map toAbsArgA os)
toAbsOExpr (OGen s _) = A.VEGen (toAbsStmt s)

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
toAbsBExpr (BOp Conj b1 b2 _) = A.BEAnd (toAbsBExpr b1) (toAbsBExpr b2)
toAbsBExpr (BOp Disj b1 b2 _) = A.BEOr (toAbsBExpr b1) (toAbsBExpr b2)
toAbsBExpr (BOp Impl b1 b2 _) = A.BEOr (A.BENot (toAbsBExpr b1)) (toAbsBExpr b2)
toAbsBExpr (BOp Equiv b1 b2 _) = A.BEAnd (A.BEOr (A.BENot (toAbsBExpr b1)) (toAbsBExpr b2)) (A.BEOr (toAbsBExpr b1) (A.BENot (toAbsBExpr b2)))
toAbsBExpr (BComp comp p1 p2 _) = A.BEBinOp (A.VEVal (toAbsPExpr p1))
                                            (toAbsComp comp)
                                            (A.VEVal (toAbsPExpr p2))
toAbsBExpr (BVar v _) = A.VEVal (Ident v)
toAbsBExpr (BGen s _) = A.VEGen (toAbsStmt s)


toAbsArgA :: (OExpr String ValueType, [PExpr String ValueType]) -> A.VEArg
toAbsArgA (c, []) = A.VEArgSole (toAbsOExpr c)
toAbsArgA (c, ps) = A.VEArgWithPoses (toAbsOExpr c) (map toAbsPExpr ps)

prettyPrintProgram :: Program String ValueType -> String
prettyPrintProgram = printTree . toAbsProgram

prettyPrintStmt :: Stmt String ValueType -> String
prettyPrintStmt = printTree . toAbsStmt

prettyPrintT :: ValueType -> String
prettyPrintT = printTree . toAbsType

prettyPrintOExpr :: OExpr String ValueType -> String
prettyPrintOExpr = printTree . toAbsOExpr

prettyPrintBExpr :: BExpr String ValueType -> String
prettyPrintBExpr = printTree . toAbsBExpr

prettyPrintComp :: TestOp -> String
prettyPrintComp = printTree . toAbsComp

prettyPrintCExpr :: CExpr String ValueType -> String
prettyPrintCExpr = printTree . toAbsCExpr

prettyPrintPExpr :: PExpr String ValueType -> String
prettyPrintPExpr = printTree . toAbsPExpr

--- Here we make another version of pretty printing, that uses indentations and newlines to make the code more readable. 
--- For now we use the default printing of Expressions. 

indent :: Int -> String
indent n = replicate (n * 2) ' '

stripFinalNewLine :: String -> String
stripFinalNewLine [] = []
stripFinalNewLine x = if last x == '\n' then init x else x

prettyPrintOExprWithNls :: Int -> OExpr String ValueType -> String
prettyPrintOExprWithNls indent (OVar v t) = v
prettyPrintOExprWithNls indent (OConst c t) = prettyPrintCExpr c
prettyPrintOExprWithNls indent (OList os t) = "[" ++ unwords (map (\o -> prettyPrintOExprWithNls indent o) os) ++ "]"
prettyPrintOExprWithNls indent (OApp v os t) = v ++ "(" ++ unwords (map (\(o, ps) -> prettyPrintOExprWithNls indent o ++ unwords (map prettyPrintPExpr ps)) os) ++ ")"
prettyPrintOExprWithNls i (OGen s t) = "{\n" ++ prettyPrintStmtWithNls (i + 1) s ++ "\n" ++ indent i  ++ "}"


prettyPrintOExprWithNlsTyped i o = prettyPrintOExprWithNls i o ++ " : " ++ prettyPrintT (getType o)

condParens :: Bool -> String -> String 
condParens True s = "(" ++ s ++ ")"
condParens False s = s


prettyPrintBExprWithNls :: Int -> Int -> BExpr String ValueType -> String
prettyPrintBExprWithNls indent priority (BConst b t) = show b
prettyPrintBExprWithNls indent priority (BNot (BVar v _) _) = "!" ++ v
prettyPrintBExprWithNls indent priority (BNot b t) = "!(" ++ prettyPrintBExprWithNls indent 0 b ++ ")"
prettyPrintBExprWithNls indent priority (BOp Conj b1 b2 t) = "(" ++ b1' ++ " and " ++ b2' ++ ")" 
    --if priority > 1 then "(" ++ b1' ++ " and " ++ b2' ++ ")" else b1' ++ " and " ++ b2'
    where b1' = prettyPrintBExprWithNls indent 1 b1
          b2' = prettyPrintBExprWithNls indent 1 b2
prettyPrintBExprWithNls indent priority (BOp Disj b1 b2 t) = "(" ++ b1' ++ " or " ++ b2' ++ ")"
    -- if priority > 0 then "(" ++ b1' ++ " or " ++ b2' ++ ")" else b1' ++ " or " ++ b2'
    where b1' = prettyPrintBExprWithNls indent 0 b1
          b2' = prettyPrintBExprWithNls indent 0 b2
prettyPrintBExprWithNls indent priority (BOp Impl b1 b2 t) = if priority > 0 then "(" ++ b1' ++ " => " ++ b2' ++ ")" else b1' ++ " => " ++ b2'
    where b1' = prettyPrintBExprWithNls indent 0 b1
          b2' = prettyPrintBExprWithNls indent 0 b2
prettyPrintBExprWithNls indent priority (BOp Equiv b1 b2 t) = if priority > 0 then "(" ++ b1' ++ " <=> " ++ b2' ++ ")" else b1' ++ " <=> " ++ b2'
    where b1' = prettyPrintBExprWithNls indent 0 b1
          b2' = prettyPrintBExprWithNls indent 0 b2
prettyPrintBExprWithNls indent priority (BComp comp p1 p2 t) = prettyPrintPExpr p1 ++ " " ++ prettyPrintComp comp ++ " " ++ prettyPrintPExpr p2
prettyPrintBExprWithNls indent priority (BVar v t) = v
prettyPrintBExprWithNls i priority (BGen s t) = "{\n" ++ prettyPrintStmtWithNls (i + 1) s ++ "\n" ++ indent i ++ "}"
prettyPrintBExprWithNls i priority (BApp v es t) = v ++ "(" ++ unwords (map (\(e, ps) -> prettyPrintOExpr e ++ unwords (map prettyPrintPExpr ps)) es) ++ ")"
prettyPrintBExprWithNls i priority (BLitEq t c e _) = prettyPrintOExpr e ++ " === " ++ prettyPrintCExpr c


prettyPrintStmtWithNls :: Int -> Stmt String ValueType -> String
prettyPrintStmtWithNls i s = prettyPrintStmtWithNlsSub i s  ++ " :: " ++ prettyPrintT (getType s)

prettyPrintStmtWithNlsSub :: Int -> Stmt String ValueType -> String
prettyPrintStmtWithNlsSub n (SIf b s1 (SSeq [] _) _) = indent n ++ "if " ++ prettyPrintBExprWithNls n 0 b ++ " then\n" ++ prettyPrintStmtWithNls (n + 1) s1 ++ "\n" ++ indent n ++ "endif"
prettyPrintStmtWithNlsSub n (SIf b s1 s2 _) = indent n ++ "if " ++ prettyPrintBExprWithNls n 0 b ++ " then\n" ++ prettyPrintStmtWithNls (n + 1) s1 ++ "\n" ++ indent n ++ "else\n" ++ prettyPrintStmtWithNls (n + 1) s2 ++ "\n" ++ indent n ++ "endif"
prettyPrintStmtWithNlsSub n (SLetOutput (v, t) o s _) = indent n ++ "let " ++ v ++ " : " ++ prettyPrintT t ++ " := " ++ prettyPrintOExprWithNlsTyped n o ++ " in\n" ++ prettyPrintStmtWithNls n s
prettyPrintStmtWithNlsSub n (SLetBoolean v s _) = indent n ++ "let mut " ++ v ++ ": Bool := False in \n" ++ prettyPrintStmtWithNls n s
prettyPrintStmtWithNlsSub n (SFor Forward (i, e, t) v s _) = indent n ++ "for (" ++ i ++ ", " ++ e ++ " : " ++ prettyPrintT t ++ ") in enumerate(" ++ prettyPrintOExprWithNlsTyped n v ++ ") do\n" ++ prettyPrintStmtWithNls (n + 1) s ++ "\n" ++ indent n ++  "done"
prettyPrintStmtWithNlsSub n (SFor Backward (i, e, t) v s _) = indent n ++ "for (" ++ i ++ ", " ++ e ++ " : " ++ prettyPrintT t ++ ") in reversed(enumerate(" ++ prettyPrintOExprWithNlsTyped n v ++ ")) do\n" ++ prettyPrintStmtWithNls (n + 1) s ++ "\n" ++ indent n ++  "done"
prettyPrintStmtWithNlsSub n (SSeq ss _) = stripFinalNewLine $ unlines $ map (prettyPrintStmtWithNls n) ss
prettyPrintStmtWithNlsSub n (SYield o _) = indent n ++ "yield " ++ prettyPrintOExprWithNlsTyped n o
prettyPrintStmtWithNlsSub n (SOReturn o _) = indent n ++ "return " ++ prettyPrintOExprWithNlsTyped n o
prettyPrintStmtWithNlsSub n (SBReturn b _) = indent n ++ "return " ++ prettyPrintBExprWithNls n 0 b
prettyPrintStmtWithNlsSub n (SSetTrue v _) = indent n ++ "setTrue " ++ v

prettyPrintFunctionWithNls :: StmtFun String ValueType -> String
prettyPrintFunctionWithNls (StmtFun name args stmt t) = "def " ++ name ++ "(" ++ unwords (map (\(a, t, _) -> a ++ " : " ++ prettyPrintT t) args) ++ ") : " ++ prettyPrintT t ++ " := \n" ++ prettyPrintStmtWithNls 1 stmt ++ "\n"

prettyPrintProgramWithNls :: Program String ValueType -> String
prettyPrintProgramWithNls (Program stmts _) = stripFinalNewLine $ stripFinalNewLine $ unlines $ map prettyPrintFunctionWithNls stmts


-- This is the equivaalent of pretty print program with newlines, but ignores types. 
prettyPrintProgramWithNoTypes :: Program String t -> String
prettyPrintProgramWithNoTypes (Program stmts _) = stripFinalNewLine $ unlines $ map prettyPrintFunctionWithNlsNoTypes stmts

prettyPrintFunctionWithNlsNoTypes :: StmtFun String t -> String
prettyPrintFunctionWithNlsNoTypes (StmtFun name args stmt t) = "def " ++ name ++ "(" ++ unwords (map (\(a, _, _) -> a) args) ++ ") := \n" ++ prettyPrintStmtWithNlsNoTypes 1 stmt ++ "\n"

prettyPrintStmtWithNlsNoTypes :: Int -> Stmt String t -> String
prettyPrintStmtWithNlsNoTypes n (SIf b s1 (SSeq [] _) _ ) = indent n ++ "if " ++ prettyPrintBExprWithNlsNoTypes n 0 b ++ " then\n" ++ prettyPrintStmtWithNlsNoTypes (n + 1) s1 ++ "\n" ++ indent n ++ "endif"
prettyPrintStmtWithNlsNoTypes n (SIf b s1 s2 _) = indent n ++ "if " ++ prettyPrintBExprWithNlsNoTypes n 0 b ++ " then\n" ++ prettyPrintStmtWithNlsNoTypes (n + 1) s1 ++ "\n" ++ indent n ++ "else\n" ++ prettyPrintStmtWithNlsNoTypes (n + 1) s2 ++ "\n" ++ indent n ++ "endif"
prettyPrintStmtWithNlsNoTypes n (SLetOutput (v, t) o s _) = indent n ++ "let " ++ v ++ " := " ++ prettyPrintOExprWithNlsNoTypes n o ++ " in\n" ++ prettyPrintStmtWithNlsNoTypes n s
prettyPrintStmtWithNlsNoTypes n (SLetBoolean v s _) = indent n ++ "let mut " ++ v ++ " := False in \n" ++ prettyPrintStmtWithNlsNoTypes n s
prettyPrintStmtWithNlsNoTypes n (SFor Forward (i, e, t) v s _) = indent n ++ "for (" ++ i ++ ", " ++ e ++ ") in enumerate(" ++ prettyPrintOExprWithNlsNoTypes n v ++ ") do\n" ++ prettyPrintStmtWithNlsNoTypes (n + 1) s ++ "\n" ++ indent n ++  "done"
prettyPrintStmtWithNlsNoTypes n (SFor Backward (i, e, t) v s _) = indent n ++ "for (" ++ i ++ ", " ++ e ++ ") in reversed(enumerate(" ++ prettyPrintOExprWithNlsNoTypes n v ++ ")) do\n" ++ prettyPrintStmtWithNlsNoTypes (n + 1) s ++ "\n" ++ indent n ++  "done"
prettyPrintStmtWithNlsNoTypes n (SSeq ss _) = stripFinalNewLine $ unlines $ map (prettyPrintStmtWithNlsNoTypes n) ss
prettyPrintStmtWithNlsNoTypes n (SYield o _) = indent n ++ "yield " ++ prettyPrintOExprWithNlsNoTypes n o
prettyPrintStmtWithNlsNoTypes n (SOReturn o _) = indent n ++ "return " ++ prettyPrintOExprWithNlsNoTypes n o
prettyPrintStmtWithNlsNoTypes n (SBReturn b _) = indent n ++ "return " ++ prettyPrintBExprWithNlsNoTypes n 0 b
prettyPrintStmtWithNlsNoTypes n (SSetTrue v _) = indent n ++ "setTrue " ++ v



prettyPrintOExprWithNlsNoTypes :: Int -> OExpr String t -> String
prettyPrintOExprWithNlsNoTypes indent (OVar v _) = v
prettyPrintOExprWithNlsNoTypes indent (OConst c _) = prettyPrintCExprWithNlsNoTypes c
prettyPrintOExprWithNlsNoTypes indent (OList os _) = "[" ++ unwords (map (\o -> prettyPrintOExprWithNlsNoTypes indent o) os) ++ "]"
prettyPrintOExprWithNlsNoTypes indent (OApp v os _) = v ++ "(" ++ unwords (map (\(o, ps) -> prettyPrintOExprWithNlsNoTypes indent o ++ unwords (map prettyPrintPExprWithNlsNoTypes ps)) os) ++ ")"
prettyPrintOExprWithNlsNoTypes i (OGen s _) = "{\n" ++ prettyPrintStmtWithNlsNoTypes (i + 1) s ++ "\n" ++ indent i  ++ "}"

prettyPrintBExprWithNlsNoTypes :: Int -> Int -> BExpr String t -> String
prettyPrintBExprWithNlsNoTypes indent priority (BConst b _) = show b
prettyPrintBExprWithNlsNoTypes indent priority (BNot (BVar v _) _) = "!" ++ v
prettyPrintBExprWithNlsNoTypes indent priority (BNot b _) = "!(" ++ prettyPrintBExprWithNlsNoTypes indent 0 b ++ ")"
prettyPrintBExprWithNlsNoTypes indent priority (BOp Conj b1 b2 _) = "(" ++ b1' ++ " and " ++ b2' ++ ")" 
    where b1' = prettyPrintBExprWithNlsNoTypes indent 1 b1
          b2' = prettyPrintBExprWithNlsNoTypes indent 1 b2
prettyPrintBExprWithNlsNoTypes indent priority (BOp Disj b1 b2 _) = "(" ++ b1' ++ " or " ++ b2' ++ ")"
    where b1' = prettyPrintBExprWithNlsNoTypes indent 0 b1
          b2' = prettyPrintBExprWithNlsNoTypes indent 0 b2
prettyPrintBExprWithNlsNoTypes indent priority (BOp Impl b1 b2 _) = if priority > 0 then "(" ++ b1' ++ " => " ++ b2' ++ ")" else b1' ++ " => " ++ b2'
    where b1' = prettyPrintBExprWithNlsNoTypes indent 0 b1
          b2' = prettyPrintBExprWithNlsNoTypes indent 0 b2
prettyPrintBExprWithNlsNoTypes indent priority (BOp Equiv b1 b2 _) = if priority > 0 then "(" ++ b1' ++ " <=> " ++ b2' ++ ")" else b1' ++ " <=> " ++ b2'
    where b1' = prettyPrintBExprWithNlsNoTypes indent 0 b1
          b2' = prettyPrintBExprWithNlsNoTypes indent 0 b2
prettyPrintBExprWithNlsNoTypes indent priority (BComp comp p1 p2 _) = prettyPrintPExprWithNlsNoTypes p1 ++ " " ++ prettyPrintComp comp ++ " " ++ prettyPrintPExprWithNlsNoTypes p2
prettyPrintBExprWithNlsNoTypes indent priority (BVar v _) = v
prettyPrintBExprWithNlsNoTypes i priority (BGen s _) = "{\n" ++ prettyPrintStmtWithNlsNoTypes (i + 1) s ++ "\n" ++ indent i ++ "}"
prettyPrintBExprWithNlsNoTypes i priority (BApp v es _) = v ++ "(" ++ unwords (map (\(e, ps) -> prettyPrintOExprWithNlsNoTypes i e ++ unwords (map prettyPrintPExprWithNlsNoTypes ps)) es) ++ ")"
prettyPrintBExprWithNlsNoTypes i priority (BLitEq _ c e _) = prettyPrintOExprWithNlsNoTypes i e ++ " === " ++ prettyPrintCExprWithNlsNoTypes c

prettyPrintCExprWithNlsNoTypes :: CExpr String t -> String
prettyPrintCExprWithNlsNoTypes (CChar c _) = "'" ++ [c] ++ "'"
prettyPrintCExprWithNlsNoTypes (CList s _) = "[" ++ unwords (map prettyPrintCExprWithNlsNoTypes s) ++ "]"

prettyPrintPExprWithNlsNoTypes :: PExpr String t -> String
prettyPrintPExprWithNlsNoTypes (PVar v _) = v

