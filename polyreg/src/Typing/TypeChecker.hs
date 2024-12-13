{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Typing.TypeChecker (typeCheckProgram) where

import ForPrograms 
import ForProgramsTyping
import qualified Data.Map as M

import Control.Monad
import Control.Monad.Reader 

import ForProgramsPrettyPrint

class (Monad m) => TypeCheckingMonad m where 
    getVarType :: String -> m ValueType 
    getFuncType :: String -> m (ValueType, [(ValueType, Int)])
    withVar :: String -> ValueType -> m a -> m a
    withVars :: [(String, ValueType)] -> m a -> m a
    withFunc :: String -> (ValueType,  [(ValueType, Int)]) -> m a -> m a
    throwError :: String -> m a

data TypeCheckerData = TypeCheckerData {
    variables :: M.Map String ValueType,
    functions :: M.Map String (ValueType, [(ValueType, Int)])
}

newtype TypeChecker a = TypeChecker (ReaderT TypeCheckerData (Either String) a)
    deriving (Functor, Applicative, Monad, MonadReader TypeCheckerData)

runTypeChecker :: TypeChecker a -> TypeCheckerData -> Either String a
runTypeChecker (TypeChecker m) = runReaderT m

instance TypeCheckingMonad TypeChecker where
    getVarType x = do
        m <- asks variables
        case M.lookup x m of
            Just t -> return t
            Nothing -> throwError $ "Variable " ++ x ++ " not found"
    getFuncType x = do
        m <- asks functions
        case M.lookup x m of
            Just t -> return t
            Nothing -> throwError $ "Function " ++ x ++ " not found"
    withVar x t (TypeChecker m) = TypeChecker $ local (\s -> s { variables = M.insert x t (variables s) }) m
    withVars [] m = m
    withVars ((x, t):xs) m = withVar x t (withVars xs m)
    withFunc x t (TypeChecker m) = TypeChecker $ local (\s -> s { functions = M.insert x t (functions s) }) m
    throwError = TypeChecker . lift . Left


typeCheckProgram :: Program String ValueType -> Either String ()
typeCheckProgram p = runTypeChecker (typeCheckProgramM p) (TypeCheckerData M.empty M.empty)

typeCheckProgramM :: (TypeCheckingMonad m) => Program String ValueType -> m ()
typeCheckProgramM (Program [] _) = return ()
typeCheckProgramM (Program (f:fs) x) = do
    typeCheckFunctionM f
    withFunc (getFunctionName f) (getFunctionType f) $
        typeCheckProgramM (Program fs x)

getFunctionType :: StmtFun String ValueType -> (ValueType, [(ValueType, Int)])
getFunctionType (StmtFun _ args _ t) = (t, map getType args)
    where 
        getType (_, t, i) = (t, length i)

getFunctionName :: StmtFun String ValueType -> String
getFunctionName (StmtFun n _ _ _) = n

typeCheckFunctionM :: (TypeCheckingMonad m) =>  StmtFun String ValueType -> m ()
typeCheckFunctionM (StmtFun _ args s t) =
    void $ withVars (prepareArgs args) $ typeCheckStmtM s

prepareArgs :: [(String, ValueType, [String])] -> [(String, ValueType)]
prepareArgs l = mainArgs ++ posArgs 
    where 
        mainArgs = [(x, t) | (x, t, []) <- l]
        posArgs = concat [[(p, TPos $ Position $ OVar x ()) | p <- ps ] | (x, t, ps) <- l]

typeCheckStmtM :: (TypeCheckingMonad m) => Stmt String ValueType -> m ValueType
typeCheckStmtM (SIf b s1 s2 t) = do
    typeCheckBExprM b
    t1 <- typeCheckStmtM s1
    t2 <- typeCheckStmtM s2
    guardOrError (t1 == t) $ "Left branch of if statement has type " ++ show t1 ++ " but expected " ++ show t
    guardOrError (t2 == t) $ "Right branch of if statement has type " ++ show t2 ++ " but expected " ++ show t
    return t
typeCheckStmtM (SYield o t) = do
    t' <- expectOutputType t
    t'' <- expectListType t'
    t1 <- typeCheckOExprM o
    guardOrError (t1 ==  t'') $ "Yield statement has type " ++ show t1 ++ " but expected " ++ show t''
    return t
typeCheckStmtM (SOReturn o t) = do
    t' <- expectOutputType t
    t1 <- typeCheckOExprM o
    guardOrError (t1 == t') $ "Return statement has type " ++ show t1 ++ " but expected " ++ show t'
    return t
typeCheckStmtM (SBReturn b t) = do
    expectBool t
    typeCheckBExprM b
    return TBool
typeCheckStmtM (SLetOutput (v, t) o s t') = do
    t1 <- typeCheckOExprM o
    guardOrError (TOutput t1 == t) $ "Let output expression has type " ++ show (TOutput t1) ++ " but expected " ++ show t
    t2 <- withVar v t $ typeCheckStmtM s 
    guardOrError (t2 == t') $ "Let output statement has type " ++ show t2 ++ " but expected " ++ show t'
    return t'
typeCheckStmtM (SLetBoolean v s t) = do
    t1 <- withVar v TBool $ typeCheckStmtM s
    guardOrError (t1 == t) $ "Let boolean statement has type " ++ show t1 ++ " but expected " ++ show t
    return t
typeCheckStmtM (SSetTrue v t) = do
    t' <- getVarType v
    guardOrError (t' == TBool) $ "Set true statement has type " ++ show t' ++ " but expected " ++ show TBool
    return t
typeCheckStmtM (SFor _ (v1, v2, telem) e s t) = do
    t1 <- typeCheckOExprM e
    expectListType t1
    telem' <- expectOutputType telem
    guardOrError (TOList telem' == t1 ) $ "For expression has type " ++ show t1 ++ " but expected " ++ show (TOList telem')
    let posVarType = TPos $ Position $ fmap (const ()) e 
    ans <- withVar v1 posVarType $ withVar v2 telem $ typeCheckStmtM s
    guardOrError (ans == t) $ "For statement has type " ++ show ans ++ " but expected " ++ show t
    return t
typeCheckStmtM (SSeq ss t) = do 
    forM_ ss $ \s -> do 
        t' <- typeCheckStmtM s
        guardOrError (t' == t) $ "The following of SSeq statement has type " ++ show t' ++ " but expected " ++ show t ++ ":\n" ++ prettyPrintStmtWithNlsNoTypes 0 s
    return t

expectBool :: (TypeCheckingMonad m) => ValueType -> m ()
expectBool TBool = return ()
expectBool t = throwError $ "Expected boolean type but got " ++ show t

expectOutputType :: (TypeCheckingMonad m) => ValueType -> m OutputType
expectOutputType (TOutput t) = return t
expectOutputType t = throwError $ "Expected output type but got " ++ show t

expectListType :: (TypeCheckingMonad m) => OutputType -> m OutputType
expectListType (TOList t) = return t
expectListType t = throwError $ "Expected list type but got " ++ show t

expectPositionType :: (TypeCheckingMonad m) => ValueType -> m Position
expectPositionType (TPos p) = return p
expectPositionType t = throwError $ "Expected position type but got " ++ show t

guardOrError :: (TypeCheckingMonad m) => Bool -> String -> m ()
guardOrError True _ = return ()
guardOrError False s = throwError s

typeCheckBExprM :: (TypeCheckingMonad m) => BExpr String ValueType -> m ()
typeCheckBExprM (BConst _ t) = do
    guardOrError (t == TBool) $ "Boolean constant typed as " ++ show t
    return ()
typeCheckBExprM (BNot b t) = do
    guardOrError (t == TBool) $ "Boolean negation typed as " ++ show t
    typeCheckBExprM b
typeCheckBExprM (BOp _ e1 e2 t) = do 
    guardOrError (t == TBool) $ "Boolean operation typed as " ++ show t
    typeCheckBExprM e1
    typeCheckBExprM e2
typeCheckBExprM (BComp _ p1 p2 t) = do
    guardOrError (t == TBool) $ "Boolean comparison typed as " ++ show t
    t1 <- typeCheckPExprM p1
    t2 <- typeCheckPExprM p2
    guardOrError (t1 == t2) $ "Comparison between " ++ show t1 ++ " and " ++ show t2
typeCheckBExprM (BVar x t) = do
    t' <- getVarType x
    expectBool t' 
    guardOrError (t == TBool) $ "Boolean variable " ++ x ++ " typed as " ++ show t
typeCheckBExprM (BGen s t) = do
    t' <- typeCheckStmtM s
    expectBool t'
    guardOrError (t' == t) $ "Boolean generator typed as " ++ show t   
typeCheckBExprM (BApp x es t) = do
    (t', args) <- getFuncType x
    guardOrError (t' == TBool) $ "In Boolean application, called function " ++ x ++ " which returns " ++ show t'
    guardOrError (t == TBool) $ "Boolean application typed as " ++ show t
    guardOrError (length es == length args) $ "Boolean application has " ++ show (length es) ++ " arguments but expected " ++ show (length args)
    forM_ (zip es args) $ \((e, ps), (t, pn)) -> do
        t1 <- typeCheckOExprM e
        guardOrError (TOutput t1 == t) $ "Boolean application argument " ++ show e ++ " has type " ++ show t1 ++ " but expected " ++ show t
        guardOrError (length ps == pn) $ "Boolean application argument " ++ show e ++ " has " ++ show (length ps) ++ " positional arguments but expected " ++ show pn
        forM_ ps $ \p -> do
            t2 <- typeCheckPExprM p
            guardOrError (t2 == Position (fmap (const ()) e)) $ "Argument " ++ show p ++ " has type " ++ show t2 ++ " but expected " ++ show (Position (fmap (const ()) e))
typeCheckBExprM (BLitEq t' c e t) = do
    guardOrError (t == TBool) $ "Equality comparison typed as " ++ show t
    t1 <- typeCheckCExprM c
    t2 <- typeCheckOExprM e
    guardOrError (TOutput t1 == t') $ "Constant in equality comparison has type " ++ show t1 ++ " but expected " ++ show t'
    guardOrError (TOutput t2 == t') $ "Expression in equality  comparison has type " ++ show t2 ++ " but expected " ++ show t'

typeCheckOExprM :: (TypeCheckingMonad m) => OExpr String ValueType -> m OutputType
typeCheckOExprM (OVar x t) = do
    t' <- getVarType x
    t'' <- expectOutputType t
    guardOrError (t' == t) $ "Variable " ++ x ++ " has type " ++ show t' ++ " but expected " ++ show t''
    return t''
typeCheckOExprM (OConst cexpr t) = do
    t' <- expectOutputType t
    t1 <- typeCheckCExprM cexpr
    guardOrError (t1 == t') $ "Constant expression has type " ++ show t1 ++ " but expected " ++ show t'
    return t'
typeCheckOExprM (OList es t) = do
    t' <- expectOutputType t
    t'' <- expectListType t' 
    t1 <- forM es $ \e -> do
        t1 <- typeCheckOExprM e
        guardOrError (t1 == t') $ "List element has type " ++ show t1 ++ " but expected " ++ show t'
    return t'
typeCheckOExprM (OApp x es t) = do
    (t', args) <- getFuncType x
    guardOrError (t' == t) $ "Function application has type " ++ show t' ++ " but expected " ++ show t
    guardOrError (length es == length args) $ "Function application has " ++ show (length es) ++ " arguments but expected " ++ show (length args)
    forM_ (zip es args) $ \((e, ps), (t, pn)) -> do
        t1 <- typeCheckOExprM e
        guardOrError (TOutput t1 == t) $ "Function application argument " ++ show e ++ " has type " ++ show t1 ++ " but expected " ++ show t
        guardOrError (length ps == pn) $ "Function application argument " ++ show e ++ " has " ++ show (length ps) ++ " positional arguments but expected " ++ show pn
        forM_ ps $ \p -> do
            t2 <- typeCheckPExprM p
            guardOrError (t2 == Position (fmap (const ()) e)) $ "Argument " ++ show p ++ " has type " ++ show t2 ++ " but expected " ++ show (Position (fmap (const ()) e))
    ans <- expectOutputType t
    return ans
typeCheckOExprM (OGen s t) = do
    t' <- typeCheckStmtM s
    ans <- expectOutputType t
    guardOrError (t' == t) $ "Generator has type " ++ show t' ++ " but expected " ++ show t
    return ans


typeCheckPExprM :: (TypeCheckingMonad m) => PExpr String ValueType -> m Position 
typeCheckPExprM (PVar x _) = do
    t <- getVarType x
    tp <- expectPositionType t
    return tp 

typeCheckCExprM :: (TypeCheckingMonad m) => CExpr String ValueType -> m OutputType 
typeCheckCExprM (CChar _ t) = do
    t' <- expectOutputType t
    guardOrError (t' == TOChar) $ "Character constant has type " ++ show t' ++ " but expected " ++ show TOChar
    return t'
typeCheckCExprM (CList es t) = do
    t' <- expectOutputType t
    t'' <- expectListType t'
    t1 <- forM es $ \e -> do
        t1 <- typeCheckCExprM e
        guardOrError (t1 == t') $ "List element has type " ++ show t1 ++ " but expected " ++ show t'
    return t'
