{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module ForProgramsTyping where

-- This module is doing the typecheck
-- of typed ForPrograms.


import ForPrograms

import Data.Map    (Map)
import qualified Data.Map as Map
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad (forM)

import Data.Tuple.Extra

-------
-- As a first step, we need to go from typed AST to untyped AST.
-- This is needed because the type of a *position* is the
-- *origin* of this position in terms of *untyped AST*.
-------

eraseTypesO :: OExpr v t -> OExpr v ()
eraseTypesO p = fmap (const ()) p

data OutputType = TOList OutputType
                | TOChar
                deriving (Show, Eq)

data Position = Position (OExpr String ())
    deriving (Show, Eq)

unPosition :: Position -> OExpr String ()
unPosition (Position o) = o

data Argument = Argument OutputType Int 
    deriving (Show, Eq)

data FunctionType = FProd [Argument] ValueType
    deriving (Show, Eq)

data ValueType = TBool | TPos Position | TOutput OutputType
    deriving (Show, Eq)


type TProgram = Program String ValueType

class HasType a where
    getType :: a -> ValueType

instance HasType (Stmt String ValueType) where
    getType (SIf _ _ _ t) = t
    getType (SYield _ t) = t
    getType (SOReturn _ t) = t
    getType (SBReturn _ t) = t
    getType (SLetOutput _ _ _ t) = t
    getType (SLetBoolean _ _ t) = t
    getType (SSetTrue _ t) = t
    getType (SFor _ _ _ t) = t
    getType (SSeq _ t) = t

instance HasType (BExpr String ValueType) where
    getType (BConst _ t) = t
    getType (BNot _ t) = t
    getType (BOp _ _ _ t) = t
    getType (BComp _ _ _ t) = t
    getType (BVar _ t) = t
    getType (BGen _ t) = t
    getType (BApp _ _ t) = t
    getType (BLitEq _ _ _ t) = t

instance HasType (PExpr String ValueType) where
    getType (PVar _ t) = t

instance HasType (CExpr String ValueType) where
    getType (CChar _ t) = t
    getType (CList _ t) = t

instance HasType (OExpr String ValueType) where
    getType (OVar _ t) = t
    getType (OConst _ t) = t
    getType (OList _ t) = t
    getType (ORev _ t) = t
    getType (OIndex _ _ t) = t
    getType (OApp _ _ t) = t
    getType (OGen _ t) = t

instance HasType (StmtFun String ValueType) where
    getType (StmtFun _ _ _ t) = t


data TypingContext = TypingContext {
    funcs :: Map String FunctionType,
    vars  :: Map String ValueType
} deriving (Show, Eq)

data TypeError = TypeError {
    message :: String,
    context :: TypingContext
} deriving (Show, Eq)

class (Monad m, MonadReader TypingContext m, MonadError TypeError m) => MonadTyping m where
    withCtx :: (TypingContext -> TypingContext) -> m a -> m a
    withNewVar :: String -> ValueType -> m a -> m a
    withNewVars :: [(String, ValueType)] -> m a -> m a
    withNewFunc :: String -> FunctionType -> m a -> m a
    getFuncProd :: String -> m FunctionType
    getConst    :: String -> m OutputType
    getPos      :: String -> m Position
    getOutput   :: String -> m OutputType
    getBool     :: String -> m ()

guardOrThrow :: MonadTyping m => Bool -> String -> m ()
guardOrThrow True  _ = return ()
guardOrThrow False s = do
    ctx <- ask
    throwError (TypeError ("Guard: " ++ s) ctx)

throwWithCtx :: MonadTyping m => String -> m a
throwWithCtx s = do
    ctx <- ask
    throwError (TypeError s ctx)

newtype TypeMonad a = TypeMonad (ReaderT TypingContext (Except TypeError) a)
    deriving (Functor, Applicative, Monad, MonadError TypeError, MonadReader TypingContext)

runTypeMonad :: TypeMonad a -> Either TypeError a
runTypeMonad (TypeMonad m) = runExcept (runReaderT m ctx)
    where
        ctx = TypingContext Map.empty Map.empty

instance MonadFail TypeMonad where
    fail s = do
        ctx <- ask
        throwError (TypeError s ctx)

instance MonadTyping TypeMonad where
    withCtx f m = local f m

    withNewVar v t m = do
        ctx <- ask
        guardOrThrow (Map.notMember v (vars ctx)) ("Variable " ++ v ++ " already declared")
        let ctx' = TypingContext (funcs ctx) (Map.insert v t (vars ctx))
        local (const ctx') m

    withNewVars vs m = do
        ctx <- ask
        let newVars = Map.fromList vs
        guardOrThrow (Map.null (Map.intersection newVars (vars ctx))) $ "Some of those variables is already declared" ++ show vs
        let ctx' = TypingContext (funcs ctx) (Map.union newVars (vars ctx))
        local (const ctx') m

    withNewFunc v t m = do
        ctx <- ask
        guardOrThrow (Map.notMember v (funcs ctx)) ("Function " ++ v ++ " already declared")
        let ctx' = TypingContext (Map.insert v t (funcs ctx)) (vars ctx)
        local (const ctx') m

    getBool v = do
        ctx <- ask
        case Map.lookup v (vars ctx) of
            Just TBool -> return ()
            Just (_)   -> throwError (TypeError ("Variable " ++ v ++ " is not a boolean") ctx)
            _          -> throwError (TypeError ("Variable " ++ v ++ " not found") ctx)


    getFuncProd v = do
        ctx <- ask
        case Map.lookup v (funcs ctx) of
            Just x  -> return x
            Nothing -> throwError (TypeError ("Function " ++ v ++ " not found") ctx)


    getConst v = do
        ctx <- ask
        case Map.lookup v (vars ctx) of
            Just (TConst t) -> return t
            Just (_)        -> throwError (TypeError ("Constant " ++ v ++ " is not a constant") ctx)
            _               -> throwError (TypeError ("Constant " ++ v ++ " not found") ctx)

    getPos v = do
        ctx <- ask
        case Map.lookup v (vars ctx) of
            Just (TPos p) -> return p
            Just (_)      -> throwError (TypeError ("Position " ++ v ++ " is not a position") ctx)
            _             -> throwError (TypeError ("Position " ++ v ++ " not found") ctx)

    getOutput v = do
        ctx <- ask
        case Map.lookup v (vars ctx) of
            Just (TOutput t) -> return t
            Just (_)         -> throwError (TypeError ("Output " ++ v ++ " is not an output") ctx)
            _                -> throwError (TypeError ("Output " ++ v ++ " not found") ctx)
        

introduceArgument :: (String, OutputType, [String]) -> [(String, ValueType)]
introduceArgument (v, t, ps) = do 
    (v, TOutput t) : zip ps (repeat (TPos (Position (OVar v ()))))

introduceArguments :: [(String, OutputType, [String])] -> [(String, ValueType)]
introduceArguments = concatMap introduceArgument

inferFunctionM :: StmtFun String (Maybe ValueType) -> TypeMonad (StmtFun String ValueType)
inferFunctionM (StmtFun name args s (Just t)) = do
    typedArgs <- forM args $ \(v, t, ps) -> 
            case t of
                Just (TOutput t') -> return (v, t', ps)
                Just t' -> throwWithCtx $ "(inferFunctionM) Argument " ++ v ++ " has invalid type annotation " ++ show t'
                Nothing ->
                    throwWithCtx $ "(inferFunctionM) Argument " ++ v ++ " has no type annotation"
    let newVars = introduceArguments typedArgs
    withNewVars newVars $ do
        s' <- inferStmtM s t
        let wrappedTypedArgs = map (\(v, t, ps) -> (v, TOutput t, ps)) typedArgs
        return (StmtFun name wrappedTypedArgs s' t)
inferFunctionM (StmtFun n _ _ Nothing) =
    throwWithCtx $ "(inferFunctionM) Function " ++ n ++ " has no type annotation"

inferProgramM :: [StmtFun String (Maybe ValueType)] -> TypeMonad [StmtFun String ValueType]
inferProgramM [] = return []
inferProgramM (f : fs) = do
    f' <- inferFunctionM f
    let (StmtFun n args _ t) = f'
    let args' = map (\(_, TOutput t, l) -> Argument t (length l)) args
    ts <- withNewFunc n (FProd args' t) $ inferProgramM fs
    return (f' : ts)

-- Inference can be made top->down. That is, we know the types 
-- of the functions, and generators, so we can infer
-- the types of the rest of the program propagating those.
--
-- inferXXX :: XXX -> TypeMonad XXXWithType
--
-- except for statements, where we know the expected type.
--
-- inferStmtM :: Stmt String (Maybe ValueType) -> ValueType -> TypeMonad (Stmt String ValueType)
--
inferBoolM :: BExpr String (Maybe ValueType) -> TypeMonad (BExpr String ValueType)
inferBoolM (BConst b _) = return (BConst b TBool)
inferBoolM (BNot e _) = do
    e' <- inferBoolM e
    return (BNot e' TBool)
inferBoolM (BOp op e1 e2 _) = do
    e1' <- inferBoolM e1
    e2' <- inferBoolM e2
    return (BOp op e1' e2' TBool)
inferBoolM (BComp c e1 e2 _) = do
    e1' <- inferPosM e1
    e2' <- inferPosM e2
    guardOrThrow (getType e1' == getType e2') ("Comparing positions of different types " ++ show e1' ++ " and " ++ show e2')
    return (BComp c e1' e2' TBool)
inferBoolM (BVar v _) = do
    getBool v
    return (BVar v TBool)
inferBoolM (BGen s (Just t)) = do
    s' <- inferStmtM s t
    return (BGen s' TBool)
inferBoolM (BApp v args _) = do
    (FProd argsTs t) <- getFuncProd v
    guardOrThrow (t == TBool) ("Function " ++ v ++ " has return type " ++ show t ++ " but expected Bool")
    args' <- inferArgsM argsTs args
    return (BApp v args' TBool)
inferBoolM (BLitEq (Just t'@(TOutput t)) c o _) = do
    c' <- inferConstM t c
    o' <- inferOutputM t o
    return (BLitEq t' c' o' TBool)
inferBoolM x = do
    ctx <- ask
    throwError (TypeError ("Invalid boolean expression" ++ show x) ctx)

inferPosM :: (PExpr String (Maybe ValueType)) -> TypeMonad (PExpr String ValueType)
inferPosM (PVar v _) = do
    (Position o) <- getPos v
    return (PVar v (TPos (Position o)))

checkPosM :: (OExpr String ()) -> PExpr String (Maybe ValueType) -> TypeMonad (PExpr String ValueType)
checkPosM o (PVar v _) = do
    (Position o') <- getPos v
    guardOrThrow (o == o') ("Variable " ++ v ++ " is bound to " ++ show o' ++ " but expected to be bound to" ++ show o)
    return (PVar v (TPos (Position o)))

inferConstM :: OutputType -> CExpr String (Maybe ValueType) ->  TypeMonad (CExpr String ValueType)
inferConstM TOChar (CChar c _)  = return (CChar c (TConst TOChar))
inferConstM (TOList t) (CList xs _) = do
    xs' <- mapM (inferConstM t) xs
    return (CList xs' (TConst (TOList t)))
inferConstM t x = throwWithCtx $ "(inferConstM) Invalid constant expression" ++ show x ++ " of alleged type " ++ show t

inferOutputM :: OutputType -> OExpr String (Maybe ValueType) -> TypeMonad (OExpr String ValueType)
inferOutputM t' (OVar v _) = do
    t <- getOutput v
    guardOrThrow (t == t') ("Variable " ++ v ++ " has type " ++ show t ++ " but expected " ++ show t')
    return (OVar v (TOutput t))
inferOutputM t (OConst c _) = do
    c' <- inferConstM t c
    return (OConst c' (TOutput t))
inferOutputM (TOList t) (OList xs _) = do
    xs' <- mapM (inferOutputM t) xs
    return (OList xs' (TOutput (TOList t)))
inferOutputM t@(TOList t') (ORev o _) = do
    o' <- inferOutputM t o
    return (ORev o' (TOutput t))
inferOutputM t (OIndex o p _) = do
    o' <- inferOutputM (TOList t) o
    p' <- checkPosM (eraseTypesO o') p
    return (OIndex o' p' (TOutput t))
inferOutputM t (OApp v args _) = do
    (FProd argsTs value)  <- getFuncProd v
    guardOrThrow (value == (TOutput t)) ("Function " ++ v ++ " has return type " ++ show value ++ " but expected " ++ show t)
    args'' <- inferArgsM argsTs args
    return (OApp v args'' (TOutput t))
inferOutputM t (OGen s _) = do
    s' <- inferStmtM s (TOutput t)
    return (OGen s' (TOutput t))
inferOutputM t x = do
    ctx <- ask
    throwError (TypeError ("Invalid output expression" ++ show x) ctx)


inferStmtM :: Stmt String (Maybe ValueType) -> ValueType -> TypeMonad (Stmt String ValueType)
inferStmtM (SIf e s1 s2 _) t = do
    e' <- inferBoolM e
    s1' <- inferStmtM s1 t
    s2' <- inferStmtM s2 t
    return (SIf e' s1' s2' t)
inferStmtM (SYield o _) t'@(TOutput (TOList t)) = do
    o' <- inferOutputM t o
    return (SYield o' t')
inferStmtM (SOReturn o _) (TOutput t) = do
    o' <- inferOutputM t o
    return (SOReturn o' (TOutput t))
inferStmtM (SBReturn b _) TBool = do
    b' <- inferBoolM b
    return (SBReturn b' TBool)
inferStmtM (SBReturn _ _) t = do
    throwWithCtx ("(inferStmtM) Invalid return type for SBReturn " ++ show t)    
inferStmtM (SLetOutput (v, Just (TOutput tv)) o s _) t = do
    o' <- inferOutputM tv o
    withNewVar v (TOutput tv) $ do
        s' <- inferStmtM s t
        return (SLetOutput (v, TOutput tv) o' s' t)
inferStmtM (SLetBoolean v s _) t = do
    withNewVar v TBool $ do
        s' <- inferStmtM s t
        return (SLetBoolean v s' t)
inferStmtM (SSetTrue v _) t = do
    getBool v
    return (SSetTrue v t)
inferStmtM (SFor (v1, v2, Just (TOutput v2t)) o s _) t = do
    o' <- inferOutputM (TOList v2t) o
    let v1t = TPos (Position (eraseTypesO o))
    withNewVars [(v1, v1t), (v2, TOutput v2t)] $ do
        s' <- inferStmtM s t
        return (SFor (v1, v2, TOutput v2t) o' s' t)
inferStmtM (SSeq ss _) t = do
    ss' <- mapM (\s -> inferStmtM s t) ss
    return (SSeq ss' t)
inferStmtM s _ = 
    throwWithCtx $ "Invalid statement " ++ show s


inferArgM :: Argument -> (OExpr String (Maybe ValueType), [PExpr String (Maybe ValueType)]) -> TypeMonad (OExpr String ValueType, [PExpr String ValueType])
inferArgM (Argument t l) (o, ps) = do
    guardOrThrow (l == length ps) ("Argument " ++ show o ++ " has " ++ show l ++ " positions but " ++ show (length ps) ++ " were given")
    o' <- inferOutputM t o
    ps' <- mapM (checkPosM (eraseTypesO o)) ps
    return (o', ps')

zipWithM :: Monad m => (a -> b -> m c) -> [a] -> [b] -> m [c]
zipWithM f xs ys = sequence (zipWith f xs ys)

inferArgsM :: [Argument] -> [(OExpr String (Maybe ValueType), [PExpr String (Maybe ValueType)])] -> TypeMonad ([(OExpr String ValueType, [PExpr String ValueType])])
inferArgsM ts os = zipWithM inferArgM ts os 

inferProgram :: (Program String (Maybe ValueType)) -> Either TypeError (Program String ValueType)
inferProgram (Program p v) = Program <$> runTypeMonad (inferProgramM p) <*> pure v
