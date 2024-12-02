module Parser.ParsedToForProgram where

import Control.Monad

import qualified Parser.HighLevelForProgram.Abs as P
import ForPrograms 

type M a = Either String a

parsedToForProgram :: P.Program -> M (Program String ())
parsedToForProgram (P.ProgramC fs) = do 
    progs <- forM fs parsedToFunction
    return $ Program progs "main" ()


identToString :: P.Ident -> String
identToString (P.Ident s) = s

identsToStrings :: [P.Ident] -> [String]
identsToStrings = map identToString

parsedToArgD :: P.ArgD -> (String, [String])
parsedToArgD (P.ArgDSole (P.Ident name) t) = (name, [])
parsedToArgD (P.ArgDWithPoses (P.Ident name) t poses) = (name, identsToStrings poses)

data RetContext = RBool | RVal

typeToRetContext :: P.Type -> RetContext
typeToRetContext P.TBool = RBool
typeToRetContext _ = RVal

parsedToFunction :: P.Func -> M (StmtFun String ())
parsedToFunction (P.FuncC (P.Ident name) args retType stmts) = do 
    let ctx = typeToRetContext retType
    stmts' <- forM stmts (parsedToStmt ctx)
    let fstmt = SSeq stmts' ()
    return $ StmtFun name (map parsedToArgD args) fstmt ()

parsedToStmt :: RetContext -> P.Stmt -> M (Stmt String ())
parsedToStmt ctx (P.SFor i v list stmts) = do
    list' <- parsedToOutputExpr list
    stmts' <- forM stmts (parsedToStmt ctx)
    return $ SFor (identToString i, identToString v) list' (SSeq stmts' ()) ()
parsedToStmt ctx (P.SIf cond stmts) = do
    cond' <- parsedToBoolExpr cond
    stmts' <- forM stmts (parsedToStmt ctx)
    return $ SIf cond' (SSeq stmts' ()) (SSeq [] ()) ()
parsedToStmt ctx (P.SIfE cond stmts1 stmts2) = do
    cond' <- parsedToBoolExpr cond
    stmts1' <- forM stmts1 (parsedToStmt ctx)
    stmts2' <- forM stmts2 (parsedToStmt ctx)
    return $ SIf cond' (SSeq stmts1' ()) (SSeq stmts2' ()) ()
parsedToStmt RBool (P.SYield e) = Left "Cannot yield in a boolean function"
parsedToStmt RVal (P.SYield e) = do
    e' <- parsedToOutputExpr e
    return $ SYield e' ()
parsedToStmt RVal (P.SReturn e) = do
    e' <- parsedToOutputExpr e
    return $ SOReturn e' ()
parsedToStmt RBool (P.SReturn e) = do 
    e' <- parsedToBoolExpr e
    return $ SBReturn e' ()
parsedToStmt ctx (P.SLetIn i t e stmt) = do 
    stmt' <- parsedToStmt ctx stmt
    e' <- parsedToOutputExpr e
    case typeToRetContext t of 
        RVal ->   do
            e' <- parsedToOutputExpr e
            return $ SLetOutput (identToString i) e' stmt' ()
        RBool -> do
            e' <- parsedToBoolExpr e
            return $ SLetBoolean (identToString i) stmt' ()
parsedToStmt ctx (P.SLetBIn i t stmt) = do
    stmt' <- parsedToStmt ctx stmt
    return $ SLetBoolean (identToString i) stmt' ()
parsedToStmt ctx (P.SLetSetTrue i) = return $ SSetTrue (identToString i) ()

isVBinOpVal :: P.BinOp -> Bool
isVBinOpVal P.BinOpVEq = True
isVBinOpVal P.BinOpVNe = True
isVBinOpVal _ = False

binOpPToComp :: P.BinOp -> Comp
binOpPToComp P.BinOpEq = Eq
binOpPToComp P.BinOpNeq = Neq
binOpPToComp P.BinOpLeq = Leq
binOpPToComp P.BinOpLt = Lt
binOpPToComp P.BinOpGeq = Geq
binOpPToComp P.BinOpGt = Gt
binOpPToComp _ = error "Not a comparison operator"

expectVar :: P.Expr -> M String
expectVar (P.VEVal i) = return $ identToString i
expectVar x = Left $ "Expected a variable name, got" ++ show x

parsedToConstExpr :: P.Expr -> M (CExpr String ())
parsedToConstExpr (P.VEChar c) = return $ CChar c ()
parsedToConstExpr (P.VEString s) = return $ CList (map (\c -> CChar c ()) s) ()
parsedToConstExpr (P.VEListConstr es) = do
    es' <- forM es parsedToConstExpr
    return $ CList es' ()
parsedToConstExpr x = Left $ "Expected a constant expression, got" ++ show x

parsedToArg :: P.VEArg -> M (OExpr String (), [PExpr String ()])
parsedToArg (P.VEArgSole e) = do 
    e' <- parsedToOutputExpr e 
    return (e', [])
parsedToArg (P.VEArgWithPoses e poses) = do 
    e' <- parsedToOutputExpr e
    return (e', map (\x -> PVar x ()) $ identsToStrings poses)

parsedToBoolExpr :: P.Expr -> M (BExpr String ())
parsedToBoolExpr (P.VEChar a) = Left "Char in boolean expression"
parsedToBoolExpr (P.VEString a) = Left "String in boolean expression"
parsedToBoolExpr (P.VEListConstr a) = Left "List in boolean expression"
parsedToBoolExpr (P.VEGen t stmt) = do 
    stmt' <- parsedToStmt RBool stmt
    return $ BGen stmt' ()
parsedToBoolExpr (P.VEVal i) = return $ BVar (identToString i) ()
parsedToBoolExpr (P.VERev e) = Left "Rev in boolean expression"
parsedToBoolExpr (P.VEFunc i args) = do 
    args <- forM args parsedToArg
    return $ BApp (identToString i) args () 
parsedToBoolExpr P.BETrue = Left "Error: Boolean literals not supported"
parsedToBoolExpr P.BEFalse = Left "Error: Boolean literals not supported"
parsedToBoolExpr (P.BENot e) = do 
    e' <- parsedToBoolExpr e
    return $ BNot e' ()
parsedToBoolExpr (P.BEBinOp e1 op e2) = 
    if isVBinOpVal op then do
        e1 <- parsedToOutputExpr e1
        e2 <- parsedToConstExpr e2
        if op == P.BinOpVEq then
            return $ BLitEq e2 e1 ()
        else
            return $ BNot (BLitEq e2 e1 ()) ()
    else do 
        e1' <- expectVar e1
        e2' <- expectVar e2
        return $ BComp (binOpPToComp op) (PVar e1' ()) (PVar e2' ()) ()
parsedToBoolExpr (P.BEAnd e1 e2) = do 
    e1' <- parsedToBoolExpr e1
    e2' <- parsedToBoolExpr e2
    return $ BOp And e1' e2' ()
parsedToBoolExpr (P.BEOr e1 e2) = do
    e1' <- parsedToBoolExpr e1
    e2' <- parsedToBoolExpr e2
    return $ BOp Or e1' e2' ()

parsedToOutputExpr :: P.Expr -> M (OExpr String ())
parsedToOutputExpr (P.VEChar c) = return $ OConst (CChar c ()) ()
parsedToOutputExpr (P.VEString s) = return $ OConst (CList (map (\c -> CChar c ()) s) ()) ()
parsedToOutputExpr (P.VEListConstr es) = do
    es' <- forM es parsedToOutputExpr
    return $ OList es' ()
parsedToOutputExpr (P.VEGen t stmt) = do
    stmt' <- parsedToStmt RVal stmt
    return $ OGen stmt' ()
parsedToOutputExpr (P.VEVal i) = return $ OVar (identToString i) ()
parsedToOutputExpr (P.VERev e) = do
    e' <- parsedToOutputExpr e
    return $ ORev e' ()
parsedToOutputExpr (P.VEFunc i args) = do 
    args <- forM args parsedToArg
    return $ OApp (identToString i) args ()
parsedToOutputExpr _ = Left "Expected an output expression"