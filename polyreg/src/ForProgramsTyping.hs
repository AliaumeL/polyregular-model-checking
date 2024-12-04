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
    getType (BLitEq _ _ t) = t

instance HasType (PExpr String ValueType) where
    getType (PVar _ t) = t

instance HasType (CExpr String ValueType) where
    getType (CChar _ t) = t
    getType (CUnit t) = t
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
typeCheckPosM (PVar v t) = do
    t' <- getPos v
    guardOrThrow (t == TPos t') $ "(PVar) Types do not match between " ++ show t ++ " and " ++ show t'
    return t'

typeCheckConstM :: CExpr String ValueType -> TypeMonad OutputType
typeCheckConstM (CChar _ (TConst TOChar)) = return TOChar
typeCheckConstM (CUnit (TConst TUnit)) = return TUnit
typeCheckConstM (CList xs (TConst (TOList t))) = do
    ts <- mapM (typeCheckConstM) xs
    guardOrThrow (all (isCompatibleOutput t) ts) $ "(CList) Types do not match between " ++ show t ++ " and " ++ show ts
    return (TOList t)
typeCheckConstM x = do
    ctx <- ask
    throwError (TypeError ("Invalid constant expression" ++ show x) ctx)

typeCheckOutputM :: OExpr String ValueType -> TypeMonad OutputType
typeCheckOutputM (OVar v (TOutput t)) = do
    t' <- getOutput v
    guardOrThrow (t == t') $ "(OVar) Types do not match between " ++ show t ++ " and " ++ show t'
    return t
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
    guardOrThrow (t == t') $ "(OApp) Types do not match between " ++ show t ++ " and " ++ show t'
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
    withCtx (const ctx') $ do
        t'' <- typeCheckStmtM s
        guardOrThrow (t == t'') $ "(SLetOutput) Types do not match between " ++ show t ++ " and " ++ show t''
        return t
typeCheckStmtM (SLetBoolean v s t) = do
    ctx <- ask
    let ctx' = TypingContext (funcs ctx) (Map.insert v TBool (vars ctx))
    withCtx (const ctx') $ do
        t' <- typeCheckStmtM s
        guardOrThrow (t == t') $ "(SLetBoolean) Types do not match between " ++ show t ++ " and " ++ show t'
        return t
typeCheckStmtM (SSetTrue v t) = do
    getBool v
    guardOrThrow (t == TBool) $ "(SSetTrue) Types do not match between " ++ show t ++ " and " ++ show TBool
    return t
typeCheckStmtM (SFor (v1, v2) o s t) = do
    ctx <- ask
    (TOList to) <- typeCheckOutputM o
    let v1t = TPos (Position (eraseTypesO o))
    let v2t = TOutput to
    let newVars = Map.insert v1 v1t (Map.insert v2 v2t (vars ctx))
    let ctx' = TypingContext (funcs ctx) newVars
    withCtx (const ctx') $ do
        t' <- typeCheckStmtM s
        guardOrThrow (t == t') $ "(SFor) Types do not match between " ++ show t ++ " and " ++ show t'
        return t
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


alignArgument :: (String, [String]) -> Argument -> [(String, ValueType)]
alignArgument (v, ps) (Argument t n) = (v, TOutput t) : zip ps (take n (repeat (TPos (Position (OVar v ())))))

alignArguments :: [(String, [String])] -> [Argument] -> [(String, ValueType)]
alignArguments args args' = concatMap (uncurry alignArgument) (zip args args')

typeCheckFunctionM :: StmtFun String ValueType -> TypeMonad FunctionType
typeCheckFunctionM (StmtFun _ args s (TFun (FProd args' t))) = do
    ctx <- ask
    let newVars = Map.fromList (alignArguments args args')
    let ctx' = TypingContext (funcs ctx) newVars
    withCtx (const ctx') $ do
        t' <- typeCheckStmtM s
        guardOrThrow (TOutput t == t') $ "(typeCheckFunctionM) Types do not match between " ++ show t ++ " and " ++ show t'
        return (FProd args' t)
typeCheckFunctionM (StmtFun _ args s (TFun (FPred args'))) = do
    ctx <- ask
    let newVars = Map.fromList (alignArguments args args')
    let ctx' = TypingContext (funcs ctx) newVars
    withCtx (const ctx') $ do
        t <- typeCheckStmtM s
        guardOrThrow (t == TBool) $ "(typeCheckFunctionM) Types do not match between " ++ show t ++ " and " ++ show TBool
        return (FPred args')
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


--- Now that we have Type Checking
-- we will add some Type Inference Program.
--
-- It reads a program with *Partial Types*,
-- i.e., Maybe ValueType, and infers the types
-- of the rest of the program (if possible).

-- In order to "unify" types of lists, we rely on the
-- following partial ordering: 

class PartialOrder a where
    isCompatible :: a -> a -> Bool
    precompares  :: a -> a -> Maybe Ordering

maybeMaximalElem :: (PartialOrder a) => [a] -> Maybe a
maybeMaximalElem [] = Nothing
maybeMaximalElem (x : xs) = foldl f (Just x) xs
    where 
        f Nothing _ = Nothing
        f (Just x) y = case precompares x y of
            Just GT -> Just x
            Just EQ -> Just x
            Just LT -> Just y
            Nothing -> Nothing

instance PartialOrder OutputType where
    isCompatible = isCompatibleOutput

    precompares TUnit TUnit = Just EQ
    precompares TUnit (TOList _) = Just LT
    precompares (TOList _) TUnit = Just GT
    precompares (TOList t1) (TOList t2) = precompares t1 t2
    precompares TOChar TOChar = Just EQ
    precompares _ _ = Nothing


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
    return (BComp c e1' e2' TBool)
inferBoolM (BVar v _) = do
    getBool v
    return (BVar v TBool)
inferBoolM (BGen s (Just t)) = do
    s' <- inferStmtM s t
    return (BGen s' TBool)
inferBoolM (BApp v args _) = do
    args' <- inferArgsM args
    return (BApp v args' TBool)
inferBoolM (BLitEq c o _) = do
    c' <- inferConstM c
    o' <- inferOutputM o
    return (BLitEq c' o' TBool)
inferBoolM x = do
    ctx <- ask
    throwError (TypeError ("Invalid boolean expression" ++ show x) ctx)

inferPosM :: PExpr String (Maybe ValueType) -> TypeMonad (PExpr String ValueType)
inferPosM (PVar v _) = do
    t <- getPos v
    return (PVar v (TPos t))

inferConstM :: CExpr String (Maybe ValueType) -> TypeMonad (CExpr String ValueType)
inferConstM (CChar c _) = return (CChar c (TConst TOChar))
inferConstM (CUnit _) = return (CUnit (TConst TUnit))
inferConstM (CList xs _) = do
    xs' <- mapM inferConstM xs
    let ts = map getType xs'
    Just t <- maybeMaximalElem <$> mapM (\(TConst x) -> return x) ts
    return (CList xs' (TConst (TOList t)))

inferOutputM :: OExpr String (Maybe ValueType) -> TypeMonad (OExpr String ValueType)
inferOutputM (OVar v _) = do
    t <- getOutput v
    return (OVar v (TOutput t))
inferOutputM (OConst c _) = do
    c' <- inferConstM c
    TConst t <- return (getType c')
    return (OConst c' (TOutput t))
inferOutputM (OList xs _) = do
    xs' <- mapM inferOutputM xs
    let ts = map getType xs'
    Just t <- maybeMaximalElem <$> mapM (\(TOutput x) -> return x) ts
    return (OList xs' (TOutput (TOList t)))
inferOutputM (ORev o _) = do
    o' <- inferOutputM o
    return (ORev o' (getType o'))
inferOutputM (OIndex o p _) = do
    o' <- inferOutputM o
    p' <- inferPosM p
    TOutput (TOList t) <- return (getType o')
    return (OIndex o' p' (TOutput t))
inferOutputM (OApp v args _) = do
    (_, t) <- getFuncProd v
    args'' <- inferArgsM args
    return (OApp v args'' (TOutput t))
inferOutputM (OGen s (Just t)) = do
    s' <- inferStmtM s t
    return (OGen s' t)
inferOutputM x = do
    ctx <- ask
    throwError (TypeError ("Invalid output expression" ++ show x) ctx)


inferStmtM :: Stmt String (Maybe ValueType) -> ValueType -> TypeMonad (Stmt String ValueType)
inferStmtM (SIf e s1 s2 _) t = do
    e' <- inferBoolM e
    s1' <- inferStmtM s1 t
    s2' <- inferStmtM s2 t
    return (SIf e' s1' s2' t)
inferStmtM (SYield o _) t = do
    o' <- inferOutputM o
    return (SYield o' t)
inferStmtM (SOReturn o _) t = do
    o' <- inferOutputM o
    return (SOReturn o' t)
inferStmtM (SBReturn b _) _ = do
    b' <- inferBoolM b
    return (SBReturn b' TBool)
inferStmtM (SLetOutput v o s _) t = do
    ctx <- ask
    o' <- inferOutputM o
    let ctx' = TypingContext (funcs ctx) (Map.insert v (getType o') (vars ctx))
    withCtx (const ctx') $ do
        s' <- inferStmtM s t
        return (SLetOutput v o' s' t)
inferStmtM (SLetBoolean v s _) t = do
    ctx <- ask
    let ctx' = TypingContext (funcs ctx) (Map.insert v TBool (vars ctx))
    withCtx (const ctx') $ do
        s' <- inferStmtM s t
        return (SLetBoolean v s' t)
inferStmtM (SSetTrue v _) t = do
    return (SSetTrue v t)
inferStmtM (SFor (v1, v2) o s _) t = do
    ctx <- ask
    o' <- inferOutputM o
    let v1t = TPos (Position (eraseTypesO o))
    let v2t = getType o'
    let newVars = Map.insert v1 v1t (Map.insert v2 v2t (vars ctx))
    let ctx' = TypingContext (funcs ctx) newVars
    withCtx (const ctx') $ do
        s' <- inferStmtM s t
        return (SFor (v1, v2) o' s' t)
inferStmtM (SSeq ss _) t = do
    ss' <- mapM (\s -> inferStmtM s t) ss
    return (SSeq ss' t)


inferArgM :: OExpr String (Maybe ValueType) -> [PExpr String (Maybe ValueType)] -> TypeMonad (OExpr String ValueType, [PExpr String ValueType])
inferArgM o ps = do
    o' <- inferOutputM o
    ps' <- mapM inferPosM ps
    return (o', ps')

inferArgsM :: [(OExpr String (Maybe ValueType), [PExpr String (Maybe ValueType)])] -> TypeMonad ([(OExpr String ValueType, [PExpr String ValueType])])
inferArgsM = mapM (uncurry inferArgM)

inferFunctionM :: StmtFun String (Maybe ValueType) -> TypeMonad (StmtFun String ValueType)
inferFunctionM (StmtFun v args s (Just (TFun (FProd args' t)))) = do
    ctx <- ask
    let newVars = Map.fromList (alignArguments args args')
    let ctx' = TypingContext (funcs ctx) newVars
    withCtx (const ctx') $ do
        s' <- inferStmtM s (TOutput t)
        return (StmtFun v args s' (TFun (FProd args' t)))
inferFunctionM (StmtFun v args s (Just (TFun (FPred args')))) = do
    ctx <- ask
    let newVars = Map.fromList (alignArguments args args')
    let ctx' = TypingContext (funcs ctx) newVars
    withCtx (const ctx') $ do
        s' <- inferStmtM s TBool
        return (StmtFun v args s' (TFun (FPred args')))
inferFunctionM (StmtFun v _ _ _) = do
    ctx <- ask
    throwError (TypeError ("(inferFunctionM) Impossible to infer function type " ++ v)  ctx)

inferProgramM :: [StmtFun String (Maybe ValueType)] -> TypeMonad [StmtFun String ValueType]
inferProgramM [] = return []
inferProgramM (f : fs) = do
    f' <- inferFunctionM f
    oldFuncs <- asks funcs
    TFun (FProd args t) <- return (getType f')
    let newFuncs = Map.insert (funName f) (FProd args t) oldFuncs
    ts <- withCtx (\ctx -> ctx {funcs = newFuncs}) $ inferProgramM fs
    return (f' : ts)



inferProgram :: (Program String (Maybe ValueType)) -> Either TypeError (Program String ValueType)
inferProgram (Program p v) = Program <$> runTypeMonad (inferProgramM p) <*> pure v

typecheckProgram :: (Program String ValueType) -> Either TypeError ()
typecheckProgram (Program p v) =  runTypeMonad (typeCheckProgramM p)
