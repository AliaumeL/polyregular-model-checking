module Parser.ParsedToForProgram where

import Control.Monad

import qualified Parser.HighLevelForProgram.Abs as P
import ForPrograms 

type M a = Either String a

type PType = P.Type 


-- Partially annotated program 
type PAProgram = Program String (Maybe PType)
type PABExpr = BExpr String (Maybe PType)
type PACExpr = CExpr String (Maybe PType)
type PAOExpr = OExpr String (Maybe PType)
type PAPExpr = PExpr String (Maybe PType)
type PAStmt = Stmt String (Maybe PType)
type PAStmtFun = StmtFun String (Maybe PType)


parsedToForProgram :: P.Program -> M PAProgram
parsedToForProgram (P.ProgramC fs) = do 
    progs <- forM fs parsedToFunction
    return $ Program progs "main" Nothing


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

parsedToFunction :: P.Func -> M PAStmtFun 
parsedToFunction (P.FuncC (P.Ident name) args retType stmts) = do 
    let ctx = typeToRetContext retType
    stmts' <- forM stmts (parsedToStmt ctx)
    let fstmt = SSeq stmts' (Just retType)
    return $ StmtFun name (map parsedToArgD args) fstmt (Just retType)

annotateTypeOExpr :: PAOExpr -> PType -> PAOExpr
annotateTypeOExpr (OVar v _) t = OVar v (Just t)
annotateTypeOExpr (OConst c _) t = OConst c (Just t)
annotateTypeOExpr (OList es _) t = OList (map (`annotateTypeOExpr` t) es) (Just t)
annotateTypeOExpr (ORev e _) t = ORev e (Just t)
annotateTypeOExpr (OIndex e p _) t = OIndex e p (Just t)
annotateTypeOExpr (OApp f args _) t = OApp f args (Just t)
annotateTypeOExpr (OGen stmt _) t = OGen stmt (Just t)

annotateTypeBExpr :: PABExpr -> PABExpr
annotateTypeBExpr (BVar v _) = BVar v (Just P.TBool)
annotateTypeBExpr (BLitEq e1 e2 _) = BLitEq e1 e2 (Just P.TBool)
annotateTypeBExpr (BComp c e1 e2 _) = BComp c e1 e2 (Just P.TBool)
annotateTypeBExpr (BOp op e1 e2 _) = BOp op e1 e2 (Just P.TBool)
annotateTypeBExpr (BNot e _) = BNot e (Just P.TBool)
annotateTypeBExpr (BGen stmt _) = BGen stmt (Just P.TBool)
annotateTypeBExpr (BApp f args _) = BApp f args (Just P.TBool)


parsedToStmt :: RetContext -> P.Stmt -> M PAStmt
parsedToStmt ctx (P.SFor i v list stmts) = do
    list' <- parsedToOutputExpr list
    stmts' <- forM stmts (parsedToStmt ctx)
    return $ SFor (identToString i, identToString v) list' (SSeq stmts' Nothing) Nothing
parsedToStmt ctx (P.SIf cond stmts) = do
    cond' <- parsedToBoolExpr cond
    stmts' <- forM stmts (parsedToStmt ctx)
    return $ SIf cond' (SSeq stmts' Nothing) (SSeq [] Nothing) Nothing
parsedToStmt ctx (P.SIfE cond stmts1 stmts2) = do
    cond' <- parsedToBoolExpr cond
    stmts1' <- forM stmts1 (parsedToStmt ctx)
    stmts2' <- forM stmts2 (parsedToStmt ctx)
    return $ SIf cond' (SSeq stmts1' Nothing) (SSeq stmts2' Nothing) Nothing
parsedToStmt RBool (P.SYield e) = Left "Cannot yield in a boolean function"
parsedToStmt RVal (P.SYield e) = do
    e' <- parsedToOutputExpr e
    return $ SYield e' Nothing
parsedToStmt RVal (P.SReturn e) = do
    e' <- parsedToOutputExpr e
    return $ SOReturn e' Nothing
parsedToStmt RBool (P.SReturn e) = do 
    e' <- parsedToBoolExpr e
    return $ SBReturn e' Nothing
parsedToStmt ctx (P.SLetIn i t e stmt) = do 
    stmt' <- parsedToStmt ctx stmt
    case typeToRetContext t of 
        RVal ->   do
            e' <- parsedToOutputExpr e
            let e'' = annotateTypeOExpr e' t
            return $ SLetOutput (identToString i) e'' stmt' Nothing
        RBool -> do
            Left "Boolean non-mut variables not supported"
            -- e' <- parsedToBoolExpr e
            -- let e'' = annotateTypeBExpr e'
            -- return $ SLetBoolean (identToString i) stmt' Nothing
parsedToStmt ctx (P.SLetBIn i t stmt) = do
    stmt' <- parsedToStmt ctx stmt
    return $ SLetBoolean (identToString i) stmt' Nothing
parsedToStmt ctx (P.SLetSetTrue i) = return $ SSetTrue (identToString i) Nothing

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

parsedToConstExpr :: P.Expr -> M PACExpr 
parsedToConstExpr (P.VEChar c) = return $ CChar c (Just P.TChar)
parsedToConstExpr (P.VEString s) = return $ CList (map (\c -> CChar c (Just P.TChar)) s) (Just $ P.TList P.TChar)
parsedToConstExpr (P.VEListConstr es) = do
    es' <- forM es parsedToConstExpr
    return $ CList es' Nothing
parsedToConstExpr x = Left $ "Expected a constant expression, got" ++ show x

parsedToArg :: P.VEArg -> M (PAOExpr, [PAPExpr])
parsedToArg (P.VEArgSole e) = do 
    e' <- parsedToOutputExpr e 
    return (e', [])
parsedToArg (P.VEArgWithPoses e poses) = do 
    e' <- parsedToOutputExpr e
    return (e', map (\x -> PVar x Nothing) $ identsToStrings poses)

parsedToBoolExpr :: P.Expr -> M PABExpr
parsedToBoolExpr (P.VEChar a) = Left "Char in boolean expression"
parsedToBoolExpr (P.VEString a) = Left "String in boolean expression"
parsedToBoolExpr (P.VEListConstr a) = Left "List in boolean expression"
parsedToBoolExpr (P.VEGen t stmt) = do 
    stmt' <- parsedToStmt RBool stmt
    return $ BGen stmt' (Just P.TBool)
parsedToBoolExpr (P.VEVal i) = return $ BVar (identToString i) (Just P.TBool)
parsedToBoolExpr (P.VERev e) = Left "Rev in boolean expression"
parsedToBoolExpr (P.VEFunc i args) = do 
    args <- forM args parsedToArg
    return $ BApp (identToString i) args (Just P.TBool)
parsedToBoolExpr P.BETrue = Left "Error: Boolean literals not supported"
parsedToBoolExpr P.BEFalse = Left "Error: Boolean literals not supported"
parsedToBoolExpr (P.BENot e) = do 
    e' <- parsedToBoolExpr e
    return $ BNot e' (Just P.TBool)
parsedToBoolExpr (P.BEBinOp e1 op e2) = 
    if isVBinOpVal op then do
        e1 <- parsedToOutputExpr e1
        e2 <- parsedToConstExpr e2
        if op == P.BinOpVEq then
            return $ BLitEq e2 e1 (Just P.TBool)
        else
            return $ BNot (BLitEq e2 e1 (Just P.TBool)) (Just P.TBool)
    else do 
        e1' <- expectVar e1
        e2' <- expectVar e2
        return $ BComp (binOpPToComp op) (PVar e1' Nothing) (PVar e2' Nothing) (Just P.TBool)
parsedToBoolExpr (P.BEAnd e1 e2) = do 
    e1' <- parsedToBoolExpr e1
    e2' <- parsedToBoolExpr e2
    return $ BOp And e1' e2' (Just P.TBool)
parsedToBoolExpr (P.BEOr e1 e2) = do
    e1' <- parsedToBoolExpr e1
    e2' <- parsedToBoolExpr e2
    return $ BOp Or e1' e2' (Just P.TBool)

parsedToOutputExpr :: P.Expr -> M PAOExpr
parsedToOutputExpr (P.VEChar c) = return $ OConst (CChar c (Just P.TChar)) (Just P.TChar)
parsedToOutputExpr (P.VEString s) = return $ OConst (CList (map (\c -> CChar c (Just P.TChar)) s) (Just $ P.TList P.TChar)) (Just $ P.TList P.TChar)
parsedToOutputExpr (P.VEListConstr es) = do
    es' <- forM es parsedToOutputExpr
    return $ OList es' Nothing
parsedToOutputExpr (P.VEGen t stmt) = do
    stmt' <- parsedToStmt RVal stmt
    return $ OGen stmt' (Just t)
parsedToOutputExpr (P.VEVal i) = return $ OVar (identToString i) Nothing
parsedToOutputExpr (P.VERev e) = do
    e' <- parsedToOutputExpr e
    return $ ORev e' Nothing
parsedToOutputExpr (P.VEFunc i args) = do 
    args <- forM args parsedToArg
    return $ OApp (identToString i) args Nothing
parsedToOutputExpr _ = Left "Expected an output expression"