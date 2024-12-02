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

-------
-- As a first step, we need to go from typed AST to untyped AST.
-- This is needed because the type of a *position* is the
-- *origin* of this position in terms of *untyped AST*.
-------

eraseTypes :: Stmt v t -> Stmt v ()
eraseTypes (SIf b s1 s2 _) = SIf (eraseTypesB b) (eraseTypes s1) (eraseTypes s2) ()
eraseTypes (SYield e _) = SYield (eraseTypesO e) ()
eraseTypes (SOReturn e _) = SOReturn (eraseTypesO e) ()
eraseTypes (SBReturn b _) = SBReturn (eraseTypesB b) ()
eraseTypes (SLetOutput v e s _) = SLetOutput v (eraseTypesO e) (eraseTypes s) ()
eraseTypes (SLetBoolean v s _) = SLetBoolean v (eraseTypes s) ()
eraseTypes (SSetTrue v _) = SSetTrue v ()
eraseTypes (SFor (v, v') e s _) = SFor (v, v') (eraseTypesO e) (eraseTypes s) ()
eraseTypes (SSeq ss _) = SSeq (map eraseTypes ss) ()

eraseTypesB :: BExpr v t -> BExpr v ()
eraseTypesB (BConst b _) = BConst b ()
eraseTypesB (BNot e _) = BNot (eraseTypesB e) ()
eraseTypesB (BOp op e1 e2 _) = BOp op (eraseTypesB e1) (eraseTypesB e2) ()
eraseTypesB (BComp c e1 e2 _) = BComp c (eraseTypesP e1) (eraseTypesP e2) ()
eraseTypesB (BVar v _) = BVar v ()
eraseTypesB (BGen s _) = BGen (eraseTypes s) ()
eraseTypesB (BApp v args _) = BApp v (map (\(o, ps) -> (eraseTypesO o, map eraseTypesP ps)) args) ()
eraseTypesB (BLitEq c o _) = BLitEq (eraseTypesC c) (eraseTypesO o) ()

eraseTypesP :: PExpr v t -> PExpr v ()
eraseTypesP (PVar v _) = PVar v ()

eraseTypesC :: CExpr v t -> CExpr v ()
eraseTypesC (CChar c _) = CChar c ()
eraseTypesC (CUnit _) = CUnit ()
eraseTypesC (CList xs _) = CList (map eraseTypesC xs) ()

eraseTypesO :: OExpr v t -> OExpr v ()
eraseTypesO (OVar v _) = OVar v ()
eraseTypesO (OConst c _) = OConst (eraseTypesC c) ()
eraseTypesO (OList xs _) = OList (map eraseTypesO xs) ()
eraseTypesO (ORev o _) = ORev (eraseTypesO o) ()
eraseTypesO (OIndex o p _) = OIndex (eraseTypesO o) (eraseTypesP p) ()
eraseTypesO (OApp v args _) = OApp v (map (\(o, ps) -> (eraseTypesO o, map eraseTypesP ps)) args) ()
eraseTypesO (OGen s _) = OGen (eraseTypes s) ()



data OutputType = TUnit
                | TOList OutputType
                | TOChar
                deriving (Show, Eq)

data Position = Position (OExpr String ())
    deriving (Show, Eq)

unPosition :: Position -> OExpr String ()
unPosition (Position o) = o

data Argument = Argument OutputType Int 
    deriving (Show, Eq)

data FunctionType = FProd [Argument] OutputType
                  | FPred [Argument]
    deriving (Show, Eq)


data ValueType = TBool | TPos Position | TOutput OutputType | TConst OutputType | TFun FunctionType
    deriving (Show, Eq)


-- Checks if two types are compatible.
-- This is needed because of the possibly empty lists
-- in the output type.
isCompatibleOutput :: OutputType -> OutputType -> Bool
isCompatibleOutput TUnit TUnit = True
isCompatibleOutput TUnit (TOList _) = True
isCompatibleOutput (TOList _) TUnit = True
isCompatibleOutput (TOList t1) (TOList t2) = isCompatibleOutput t1 t2
isCompatibleOutput TOChar TOChar = True
isCompatibleOutput _ _ = False

isCompatibleArgument :: Argument -> Argument -> Bool
isCompatibleArgument (Argument t1 n1) (Argument t2 n2) = t1 `isCompatibleOutput` t2 && n1 == n2

areCompatibleArguments :: [Argument] -> [Argument] -> Bool
areCompatibleArguments x y = all (uncurry isCompatibleArgument) (zip x y)



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
    getFuncPred :: String -> m [Argument]
    getFuncProd :: String -> m ([Argument], OutputType)
    getConst    :: String -> m OutputType
    getPos      :: String -> m Position
    getOutput   :: String -> m OutputType
    getBool     :: String -> m ()

guardOrThrow :: MonadTyping m => Bool -> String -> m ()
guardOrThrow True  _ = return ()
guardOrThrow False s = do
    ctx <- ask
    throwError (TypeError ("Guard: " ++ s) ctx)

newtype TypeMonad a = TypeMonad (ReaderT TypingContext (Except TypeError) a)
    deriving (Functor, Applicative, Monad, MonadError TypeError, MonadReader TypingContext)

instance MonadFail TypeMonad where
    fail s = do
        ctx <- ask
        throwError (TypeError s ctx)

instance MonadTyping TypeMonad where
    withCtx f m = do
        ctx <- ask
        let ctx' = f ctx
        local (const ctx') m

    getBool v = do
        ctx <- ask
        case Map.lookup v (vars ctx) of
            Just TBool -> return ()
            Just (_)   -> throwError (TypeError ("Variable " ++ v ++ " is not a boolean") ctx)
            _          -> throwError (TypeError ("Variable " ++ v ++ " not found") ctx)

    getFuncPred v = do
        ctx <- ask
        case Map.lookup v (funcs ctx) of
            Just (FPred args) -> return args
            Just (_)          -> throwError (TypeError ("Function " ++ v ++ " is not a predicate") ctx)
            _                 -> throwError (TypeError ("Function " ++ v ++ " not found") ctx)

    getFuncProd v = do
        ctx <- ask
        case Map.lookup v (funcs ctx) of
            Just (FProd args t) -> return (args, t)
            Just (_)            -> throwError (TypeError ("Function " ++ v ++ " is not a product") ctx)
            _                   -> throwError (TypeError ("Function " ++ v ++ " not found") ctx)


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
        



typeCheckBoolM :: BExpr String ValueType -> TypeMonad ()
typeCheckBoolM (BConst _ TBool) = return ()
typeCheckBoolM (BNot e TBool) = typeCheckBoolM e
typeCheckBoolM (BOp _ e1 e2 TBool) = do
    typeCheckBoolM e1
    typeCheckBoolM e2
typeCheckBoolM (BComp _ e1 e2 TBool) = do
    (Position o1) <- typeCheckPosM e1
    (Position o2) <- typeCheckPosM e2
    guardOrThrow (o1 == o2) $ "(BComp) Positions " ++ show o1 ++ " and "++ show o2 ++ "do not have the same origin"
typeCheckBoolM (BVar v TBool) = getBool v
typeCheckBoolM (BGen s TBool) = do
    t' <- typeCheckStmtM s
    guardOrThrow (t' == TBool) $ "(BGen) Types do not match between " ++ show t' ++ " and " ++ show TBool
typeCheckBoolM (BApp v args TBool) = do
    args' <- getFuncPred v
    targs <- typeCheckArgsM  args
    guardOrThrow (args' == targs) $ "(BApp) Arguments do not match between " ++ show args' ++ " and " ++ show targs
typeCheckBoolM (BLitEq c o TBool) = do
    t1 <- typeCheckConstM c
    t2 <- typeCheckOutputM o
    guardOrThrow (t1 == t2) $ "(BLitEq) Types do not match between " ++ show t1 ++ " and " ++ show t2
typeCheckBoolM x = do
    ctx <- ask
    throwError (TypeError ("Invalid boolean expression" ++ show x) ctx)


typeCheckPosM :: PExpr String ValueType -> TypeMonad Position
typeCheckPosM (PVar v t) = getPos v

typeCheckConstM :: CExpr String ValueType -> TypeMonad OutputType
typeCheckConstM (CChar _ (TConst TOChar)) = return TOChar
typeCheckConstM (CUnit (TConst TUnit)) = return TUnit
typeCheckConstM (CList xs (TConst (TOList t))) = do
    ts <- mapM (typeCheckConstM) xs
    guardOrThrow (all (isCompatibleOutput t) ts) $ "(CList) Types do not match between " ++ show t ++ " and " ++ show ts
    return (TOList t)

typeCheckOutputM :: OExpr String ValueType -> TypeMonad OutputType
typeCheckOutputM (OVar v (TOutput t)) = getOutput v
typeCheckOutputM (OConst c (TOutput t)) = do
    t' <- typeCheckConstM c
    guardOrThrow (t == t') $ "(OConst) Types do not match between " ++ show t ++ " and " ++ show t'
    return t
typeCheckOutputM (OList xs (TOutput (TOList t))) = do
    ts <- mapM (typeCheckOutputM) xs
    guardOrThrow (all (isCompatibleOutput t) ts) $ "(OList) Types do not match between " ++ show t ++ " and " ++ show ts
    return (TOList t)
typeCheckOutputM (ORev o (TOutput t)) = do
    t' <- typeCheckOutputM o
    guardOrThrow (t == t') $ "(ORev) Types do not match between " ++ show t ++ " and " ++ show t'
    return t
typeCheckOutputM (OIndex o p (TOutput t)) = do
    t' <- typeCheckOutputM o
    (Position t'') <- typeCheckPosM p
    let o' = eraseTypesO o
    guardOrThrow (t == t')  $ "(OIndex) Types do not match between " ++ show t ++ " and " ++ show t'
    guardOrThrow (o' == t'') $ "(OIndex) Origins do not match between " ++ show o ++ " and " ++ show t''
    return t
typeCheckOutputM (OApp v args (TOutput t)) = do
    (args', t') <- getFuncProd v
    targs <- typeCheckArgsM args
    guardOrThrow (areCompatibleArguments args' targs) $ "(OApp) Arguments do not match between " ++ show args' ++ " and " ++ show targs
    return t
typeCheckOutputM (OGen s (TOutput t)) = do
    TOutput t' <- typeCheckStmtM s
    guardOrThrow (t `isCompatibleOutput` t') $ "(OGen) Types do not match between " ++ show t ++ " and " ++ show t'
    return t
typeCheckOutputM x = do
    ctx <- ask
    throwError (TypeError ("Invalid output expression" ++ show x) ctx)

typeCheckStmtM :: Stmt String ValueType -> TypeMonad ValueType
typeCheckStmtM (SIf e s1 s2 t) = do
    typeCheckBoolM e
    t1 <- typeCheckStmtM s1
    t2 <- typeCheckStmtM s2
    guardOrThrow (t1 == t2) $ "(SIf) Branches type do not match between " ++ show t1 ++ " and " ++ show t2
    guardOrThrow (t == t1) $ "(SIf) Branches do not match the global type " ++ show t ++ " and " ++ show t1
    return t
-- x : τ 
-- -----
-- yield x : [τ]
typeCheckStmtM (SYield o t) = do
    t' <- typeCheckOutputM o
    guardOrThrow (t == TOutput (TOList t')) $ "(SYield) Types do not match between " ++ show t ++ " and " ++ show t'
    return t
typeCheckStmtM (SOReturn o t) = do
    t' <- typeCheckOutputM o
    guardOrThrow (t == TOutput t') $ "(SOReturn) Types do not match between " ++ show t ++ " and " ++ show t'
    return t
typeCheckStmtM (SBReturn b t) = do
    typeCheckBoolM b
    guardOrThrow (t == TBool) $ "(SBReturn) Types do not match between " ++ show t ++ " and " ++ show TBool
    return t
typeCheckStmtM (SLetOutput v o s t) = do
    t' <- typeCheckOutputM o
    ctx <- ask
    let ctx' = TypingContext (funcs ctx) (Map.insert v (TOutput t') (vars ctx))
    typeCheckStmtM s
typeCheckStmtM (SLetBoolean v s t) = do
    ctx <- ask
    let ctx' = TypingContext (funcs ctx) (Map.insert v TBool (vars ctx))
    withCtx (const ctx') $ typeCheckStmtM s
typeCheckStmtM (SSetTrue v t) = do
    getBool v
    guardOrThrow (t == TBool) $ "(SSetTrue) Types do not match between " ++ show t ++ " and " ++ show TBool
    return t
typeCheckStmtM (SFor (v1, v2) o s t) = do
    ctx <- ask
    (TOList t) <- typeCheckOutputM o
    let v1t = TPos (Position (eraseTypesO o))
    let v2t = TOutput t
    let newVars = Map.insert v1 v1t (Map.insert v2 v2t (vars ctx))
    let ctx' = TypingContext (funcs ctx) newVars
    withCtx (const ctx') $ typeCheckStmtM s
typeCheckStmtM (SSeq ss t) = do
    ts <- mapM typeCheckStmtM ss
    guardOrThrow (all (== t) ts) $ "(SSeq) Types do not match between " ++ show t ++ " and " ++ show ts
    return t
    
-- We check if all the arguments have as origin the given value, and return
-- the corresponding type
typeCheckArgM :: OExpr String ValueType -> [PExpr String ValueType] -> TypeMonad Argument
typeCheckArgM o ps = do
    t <- typeCheckOutputM o
    ts <- mapM typeCheckPosM ps
    let o' = eraseTypesO o
    guardOrThrow (all ((==) o' . unPosition) ts) $ "(typeCheckArgM) Types do not match between " ++ show t ++ " and " ++ show ts
    return (Argument t (length ps))

typeCheckArgsM :: [(OExpr String ValueType, [PExpr String ValueType])] -> TypeMonad [Argument]
typeCheckArgsM = mapM (uncurry typeCheckArgM)

typeCheckFunctionM :: StmtFun String ValueType -> TypeMonad FunctionType
typeCheckFunctionM (StmtFun v args s (TFun t)) = do
    ctx <- ask
    let ctx' = TypingContext (funcs ctx) Map.empty
    TFun t' <- withCtx (const ctx') $ typeCheckStmtM s
    guardOrThrow (t == t') $ "(typeCheckFunctionM) Types do not match between " ++ show t ++ " and " ++ show t'
    return t
typeCheckFunctionM _ = do
    ctx <- ask
    throwError (TypeError "(typeCheckFunctionM) Invalid function type"  ctx)


typeCheckProgramM :: [StmtFun String ValueType] -> TypeMonad ()
typeCheckProgramM (f : fs) = do
    t <- typeCheckFunctionM f
    oldFuncs <- asks funcs
    let newFuncs = Map.insert (funName f) t oldFuncs
    withCtx (\ctx -> ctx {funcs = newFuncs}) $ typeCheckProgramM fs
typeCheckProgramM [] = return ()

