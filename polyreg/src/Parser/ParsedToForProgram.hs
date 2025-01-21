module Parser.ParsedToForProgram where

import Control.Monad

import qualified Parser.HighLevelForProgram.Abs as P
import qualified ForPrograms.HighLevel.Typing as T
import ForPrograms.HighLevel 
import Logic.QuantifierFree

import Control.Monad.Except

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


parsedToForProgramRaw :: P.Program -> M PAProgram
parsedToForProgramRaw (P.ProgramC fs) = do 
    progs <- forM fs parsedToFunction
    return $ Program progs "main" 

parsedToForProgram :: P.Program -> M (Program String (Maybe T.ValueType))
parsedToForProgram p = parsedToForProgramRaw p >>= typeRemap

identToString :: P.Ident -> String
identToString (P.Ident s) = s

identsToStrings :: [P.Ident] -> [String]
identsToStrings = map identToString

parsedToArgD :: P.ArgD -> (String, Maybe PType, [String])
parsedToArgD (P.ArgDSole (P.Ident name) t) = (name, Just t, [])
parsedToArgD (P.ArgDWithPoses (P.Ident name) t poses) = (name, Just t,  identsToStrings poses)

data RetContext = RBool | RVal

typeToRetContext :: P.Type -> RetContext
typeToRetContext P.TBool = RBool
typeToRetContext _ = RVal

returnDefaultValue :: P.Type -> Stmt String (Maybe PType)
returnDefaultValue P.TBool = SBReturn (BConst False (Just P.TBool)) (Just P.TBool)
returnDefaultValue P.TChar = SOReturn (OConst (CChar '🎁' (Just P.TChar)) (Just P.TChar)) (Just P.TChar)
returnDefaultValue (P.TList t) = SOReturn (OConst (CList [] (Just $ P.TList t)) (Just $ P.TList t)) (Just $ P.TList t)


parsedToFunction :: P.Func -> M PAStmtFun 
parsedToFunction (P.FuncC (P.Ident name) args retType stmts) = do 
    let ctx = typeToRetContext retType
    stmts' <- forM stmts (parsedToStmt ctx)
    let retValue = returnDefaultValue retType
    let fstmt = SSeq (stmts' ++ [retValue]) (Just retType)
    return $ StmtFun name (map parsedToArgD args) fstmt (Just retType)


annotateTypeOExpr :: PAOExpr -> PType -> PAOExpr
annotateTypeOExpr (OVar v _) t = OVar v (Just t)
annotateTypeOExpr (OConst c _) t = OConst c (Just t)
annotateTypeOExpr (OList es _) t = OList (map (`annotateTypeOExpr` t) es) (Just t)
annotateTypeOExpr (OApp f args _) t = OApp f args (Just t)
annotateTypeOExpr (OGen stmt _) t = OGen stmt (Just t)

parsedToStmt :: RetContext -> P.Stmt -> M PAStmt
parsedToStmt ctx (P.SFor i v list stmts) = do
    list' <- parsedToOutputExpr list
    stmts' <- forM stmts (parsedToStmt ctx)
    return $ SFor Forward (identToString i, identToString v, Nothing) list' (SSeq stmts' Nothing) Nothing
parsedToStmt ctx (P.SRFor i v list stmts) = do
    list' <- parsedToOutputExpr list
    stmts' <- forM stmts (parsedToStmt ctx)
    return $ SFor Backward (identToString i, identToString v, Nothing) list' (SSeq stmts' Nothing) Nothing
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
parsedToStmt ctx (P.SLetIn i e stmts) = do 
    stmt' <- mapM (parsedToStmt ctx) stmts
    e' <- parsedToOutputExpr e
    return $ SLetOutput (identToString i, Nothing) e' (SSeq stmt' Nothing) Nothing
parsedToStmt ctx (P.SLetBIn i stmts) = do
    stmt' <- mapM (parsedToStmt ctx) stmts
    return $ SLetBoolean (identToString i) (SSeq stmt' Nothing) Nothing
parsedToStmt ctx (P.SLetSetTrue i) = return $ SSetTrue (identToString i) Nothing

binOpPToComp :: P.BinOp -> TestOp
binOpPToComp P.BinOpEq = Eq
binOpPToComp P.BinOpNeq = Neq
binOpPToComp P.BinOpLeq = Le
binOpPToComp P.BinOpLt = Lt
binOpPToComp P.BinOpGeq = Ge
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
parsedToBoolExpr (P.VEGen stmts) = do 
    stmts' <- mapM (parsedToStmt RBool) stmts
    return $ BGen (SSeq stmts' $ Just P.TBool) (Just P.TBool)
parsedToBoolExpr (P.VEVal i) = return $ BVar (identToString i) (Just P.TBool)
parsedToBoolExpr (P.VEFunc i args) = do 
    args <- forM args parsedToArg
    return $ BApp (identToString i) args (Just P.TBool)
parsedToBoolExpr (P.BETrue)  = return $ BConst True (Just P.TBool)
parsedToBoolExpr (P.BEFalse) = return $ BConst False (Just P.TBool)
parsedToBoolExpr (P.BENot e) = do 
    e' <- parsedToBoolExpr e
    return $ BNot e' (Just P.TBool)
parsedToBoolExpr (P.BEBinOp e1 op e2) =
    case op of 
        P.BinOpVEqT t -> do
            e1' <- parsedToOutputExpr e1
            e2' <- parsedToConstExpr e2 
            return $ BLitEq (Just t) e2' e1' (Just P.TBool)
        P.BinOpVEq -> do 
            e1' <- parsedToOutputExpr e1
            e2' <- parsedToConstExpr e2
            return $ BLitEq Nothing e2' e1' (Just P.TBool)
        P.BinOpVNe -> do 
            e1' <- parsedToOutputExpr e1
            e2' <- parsedToConstExpr e2
            return $ BNot (BLitEq Nothing e2' e1' (Just P.TBool)) (Just P.TBool)
        op -> do
            e1' <- expectVar e1
            e2' <- expectVar e2
            return $ BComp (binOpPToComp op) (PVar e1' Nothing) (PVar e2' Nothing) (Just P.TBool)
parsedToBoolExpr (P.BEAnd e1 e2) = do 
    e1' <- parsedToBoolExpr e1
    e2' <- parsedToBoolExpr e2
    return $ BOp Conj e1' e2' (Just P.TBool)
parsedToBoolExpr (P.BEOr e1 e2) = do
    e1' <- parsedToBoolExpr e1
    e2' <- parsedToBoolExpr e2
    return $ BOp Disj e1' e2' (Just P.TBool)

parsedToOutputExpr :: P.Expr -> M PAOExpr
parsedToOutputExpr (P.VEChar c) = return $ OConst (CChar c (Just P.TChar)) (Just P.TChar)
parsedToOutputExpr (P.VEString s) = return $ OConst (CList (map (\c -> CChar c (Just P.TChar)) s) (Just $ P.TList P.TChar)) (Just $ P.TList P.TChar)
parsedToOutputExpr (P.VEListConstr es) = do
    es' <- forM es parsedToOutputExpr
    return $ OList es' Nothing
parsedToOutputExpr (P.VEGen stmts) = do
    stmts' <- mapM (parsedToStmt RVal) stmts
    return $ OGen (SSeq stmts' Nothing) Nothing
parsedToOutputExpr (P.VEVal i) = return $ OVar (identToString i) Nothing
parsedToOutputExpr (P.VEFunc i args) = do 
    args <- forM args parsedToArg
    return $ OApp (identToString i) args Nothing
parsedToOutputExpr _ = Left "Expected an output expression"


data InvalidTypeWritten = InvalidTypeWritten PType deriving (Show)

translateListType :: PType -> M T.OutputType
translateListType (P.TList t) = T.TOList <$> translateListType t
translateListType (P.TChar) = return T.TOChar
translateListType t =  throwError . show $ InvalidTypeWritten t

translateType :: PType -> M T.ValueType
translateType P.TChar = T.TOutput <$> translateListType (P.TChar)
translateType (P.TList t) = T.TOutput <$> translateListType (P.TList t)
translateType P.TBool = return T.TBool

translateMaybeType :: Maybe PType -> M (Maybe T.ValueType)
translateMaybeType Nothing = return Nothing
translateMaybeType (Just t) = Just <$> translateType t

typeRemap :: PAProgram -> M (Program String (Maybe T.ValueType))
typeRemap p = mapM translateMaybeType p


