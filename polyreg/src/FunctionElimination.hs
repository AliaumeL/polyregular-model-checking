{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
module FunctionElimination (eliminateFunctionCalls, hasFunctionCall, substStmt, substOExpr, substBExpr, SubstMap(..)) where

import ForPrograms
import ForProgramsTyping

import Control.Monad
import Control.Monad.State
import Control.Monad.Except

import Data.Map (Map)
import qualified Data.Map as M

import Data.Set (Set)
import qualified Data.Set as S

import Data.Tuple.Extra


--
-- We want to eliminate function calls from the program.
-- First we design a verifier for this property.
--
hasFunctionCall :: Program String t ->  Bool
hasFunctionCall (Program funcs _) = any (\(StmtFun _ _ s _) -> hasFunctionCallStmt s) funcs

hasFunctionCallStmt :: Stmt String t -> Bool
hasFunctionCallStmt  (SYield o _) = hasFunctionCallOExpr o
hasFunctionCallStmt  (SOReturn o _) = hasFunctionCallOExpr o
hasFunctionCallStmt  (SBReturn b _) = hasFunctionCallBExpr b
hasFunctionCallStmt  (SIf b s1 s2 _) = hasFunctionCallBExpr b || hasFunctionCallStmt s1 || hasFunctionCallStmt s2
hasFunctionCallStmt  (SLetOutput _ o s _) = hasFunctionCallOExpr o || hasFunctionCallStmt s
hasFunctionCallStmt  (SLetBoolean _ s _) = hasFunctionCallStmt s
hasFunctionCallStmt  (SSetTrue _ _) = False
hasFunctionCallStmt  (SFor _ o s _) = hasFunctionCallOExpr o || hasFunctionCallStmt s
hasFunctionCallStmt  (SSeq ss _) = any hasFunctionCallStmt ss

hasFunctionCallBExpr :: BExpr String t -> Bool
hasFunctionCallBExpr (BConst _ _) = False
hasFunctionCallBExpr (BNot b _) = hasFunctionCallBExpr b
hasFunctionCallBExpr (BOp _ b1 b2 _) = hasFunctionCallBExpr b1 || hasFunctionCallBExpr b2
hasFunctionCallBExpr (BComp _ p1 p2 _) = hasFunctionCallPExpr p1 || hasFunctionCallPExpr p2
hasFunctionCallBExpr (BVar v _) = False
hasFunctionCallBExpr (BGen s _) = hasFunctionCallStmt s
hasFunctionCallBExpr (BApp v ops _) = True
hasFunctionCallBExpr (BLitEq _ c o _) = hasFunctionCallOExpr o

hasFunctionCallPExpr :: PExpr String t -> Bool
hasFunctionCallPExpr (PVar _ _) = False

hasFunctionCallCExpr :: CExpr String t -> Bool
hasFunctionCallCExpr x = False

hasFunctionCallOExpr :: OExpr String t -> Bool
hasFunctionCallOExpr (OVar _ _) = False
hasFunctionCallOExpr (OConst _ _) = False
hasFunctionCallOExpr (OList os _) = any hasFunctionCallOExpr os
hasFunctionCallOExpr (ORev o _) = hasFunctionCallOExpr o
hasFunctionCallOExpr (OIndex o p _) = hasFunctionCallOExpr o || hasFunctionCallPExpr p
hasFunctionCallOExpr (OApp _ ops _) = True
hasFunctionCallOExpr (OGen s _) = hasFunctionCallStmt s


-- And now for the elimination procedure

class (Monad m) => MonadElim m where
    withFreshVar     :: String -> m a -> m a
    withFreshVars    :: [String] -> m a -> m a
    getVar           :: String -> m String

    -- sets the identity mapping for the local variables
    -- provided, and removes them after the computation
    withLocalVars   :: [String] -> m a -> m a

    withFunction     :: StmtFun String ValueType -> m a -> m a
    getFunctionBody  :: String -> m (StmtFun String ValueType)

    throwElimError   :: String -> m a
    guardElim        :: Bool -> String -> m ()


data ElimState = ElimState {
    counter :: Int, -- counter for the new variable names
    varMap  :: Map String String, -- map from old variable names to new variable names
    funMap  :: Map String (StmtFun String ValueType) -- map from function names to their bodies
} deriving (Eq, Show)

data ElimError = ElimError String ElimState
    deriving (Eq, Show)

newtype ElimM a = ElimM (StateT ElimState (Except ElimError) a)
    deriving (Functor, Applicative, Monad, MonadState ElimState, MonadError ElimError)

runElimM :: ElimM a -> a
runElimM (ElimM m) = case runExcept (runStateT m (ElimState 0 M.empty M.empty)) of
    Left e -> error $ show e
    Right (a, _) -> a

instance MonadElim ElimM where
    withLocalVars ss m = do
        let names = zip ss ss
        let subst = M.fromList names
        modify (\st -> st { varMap = M.union subst (varMap st) })
        a <- m
        modify (\st -> st { varMap = foldr M.delete (varMap st) ss })
        return a
        
    withFreshVar s m = do
        c <- gets counter
        let name = s ++ "#" ++ show c
        modify (\st -> st { counter = c + 1, varMap = M.insert s name (varMap st) })
        a <- m
        modify (\st -> st { varMap = M.delete s (varMap st) })
        return a

    withFreshVars ss m = do
        c <- gets counter
        let names = zipWith (\s i -> s ++ "#" ++ show i) ss [c..]
        modify (\st -> st { counter = c + length ss, varMap = M.union (M.fromList $ zip ss names) (varMap st) })
        a <- m
        modify (\st -> st { varMap = foldr M.delete (varMap st) ss })
        return a

    getVar s = do 
        m <- gets varMap
        case M.lookup s m of
            Nothing -> throwElimError $ "Variable not found: " ++ s
            Just v  -> return v

    withFunction f@(StmtFun v _ _ _) m = do 
        modify (\st -> st { funMap = M.insert v f (funMap st) })
        a <- m
        modify (\st -> st { funMap = M.delete v (funMap st) })
        return a

    getFunctionBody v = do
        m <- gets funMap
        case M.lookup v m of
            Nothing -> throwElimError $ "Function not found: " ++ v
            Just f  -> return f

    throwElimError s = do
        ctx <- get
        throwError $ ElimError s ctx

    guardElim b s = unless b $ throwElimError s


-- | 
-- Our first goal is to globally refresh the variables names in a given program.
-- This means: every variable name that is *quantified* should be 
-- replaced by a fresh name. 
-- On unquantified variables, we hard error.
-- |

refreshBExpr :: (MonadElim m) => BExpr String ValueType -> m (BExpr String ValueType)
refreshBExpr (BConst b t) = pure $ BConst b t
refreshBExpr (BNot b t) = do
    b' <- refreshBExpr b
    return $ BNot b' t
refreshBExpr (BOp op b1 b2 t) = do
    b1' <- refreshBExpr b1
    b2' <- refreshBExpr b2
    return $ BOp op b1' b2' t
refreshBExpr (BComp c p1 p2 t) = do
    p1' <- refreshPExpr p1
    p2' <- refreshPExpr p2
    return $ BComp c p1' p2' t
refreshBExpr (BVar v t) = do
    v' <- getVar v
    return $ BVar v' t
refreshBExpr (BGen stmt t) = do
    stmt' <- refreshStmt stmt
    return $ BGen stmt' t
refreshBExpr (BApp v ops t) = do
    ops' <- mapM (\(o, ps) -> do
            o' <- refreshOExpr o
            ps' <- mapM refreshPExpr ps
            return (o', ps')
        ) ops
    return $ BApp v ops' t
refreshBExpr (BLitEq t c o t') = do
    c' <- refreshCExpr c
    o' <- refreshOExpr o
    return $ BLitEq t c' o' t'

refreshPExpr :: (MonadElim m) => PExpr String ValueType -> m (PExpr String ValueType)
refreshPExpr (PVar v t) = do
    v' <- getVar v
    return $ PVar v' t

refreshCExpr :: (MonadElim m) => CExpr String ValueType -> m (CExpr String ValueType)
refreshCExpr x = pure x

refreshOExpr :: (MonadElim m) => OExpr String ValueType -> m (OExpr String ValueType)
refreshOExpr (OVar v t) = do
    v' <- getVar v
    return $ OVar v' t
refreshOExpr (OConst c t) = pure (OConst c t)
refreshOExpr (OList os t) = do
    os' <- mapM refreshOExpr os
    return $ OList os' t
refreshOExpr (ORev o t) = do
    o' <- refreshOExpr o
    return $ ORev o' t
refreshOExpr (OIndex o p t) = do
    o' <- refreshOExpr o
    p' <- refreshPExpr p
    return $ OIndex o' p' t
refreshOExpr (OApp v ops t) = do
    ops' <- mapM (\(o, ps) -> do
            o' <- refreshOExpr o
            ps' <- mapM refreshPExpr ps
            return (o', ps')
        ) ops
    return $ OApp v ops' t
refreshOExpr (OGen stmt t) = do
    stmt' <- refreshStmt stmt
    return $ OGen stmt' t

refreshStmt :: (MonadElim m) => Stmt String ValueType -> m (Stmt String ValueType)
refreshStmt (SYield o t) = do
    o' <- refreshOExpr o
    return $ SYield o' t
refreshStmt (SOReturn o t) = do
    o' <- refreshOExpr o
    return $ SOReturn o' t
refreshStmt (SBReturn b t) = do
    b' <- refreshBExpr b
    return $ SBReturn b' t
refreshStmt (SIf b s1 s2 t) = do
    b' <- refreshBExpr b
    s1' <- refreshStmt s1
    s2' <- refreshStmt s2
    return $ SIf b' s1' s2' t
refreshStmt (SLetOutput (v, t') o s t) = do
    o' <- refreshOExpr o
    withFreshVar v $ do
        v' <- getVar v
        s' <- refreshStmt s
        return $ SLetOutput (v', t') o' s' t
refreshStmt (SLetBoolean v s t) = do
    withFreshVar v $ do
        v' <- getVar v
        s' <- refreshStmt s
        return $ SLetBoolean v' s' t
refreshStmt (SSetTrue v t) = do
    v' <- getVar v
    return $ SSetTrue v' t
refreshStmt (SFor (i, e, t') v s t) = do
    v' <- refreshOExpr v
    withFreshVars [i, e] $ do
        i' <- getVar i
        e' <- getVar e
        s' <- refreshStmt s
        return $ SFor (i', e', t') v' s' t
refreshStmt (SSeq ss t) = do
    ss' <- mapM refreshStmt ss
    return $ SSeq ss' t

-- | 
-- Now, we can eliminate functions as follows.
-- Whenever we encounter a function call, we replace
-- it by a generator with the body of the function.
--
-- BApp f [(o1, [p1, p2]), (o2, [p3, p4])] t
-- ->
-- OGen ( substitute (body f) σ) t 
-- where
-- σ maps the arguments of f to the values of the arguments
--
-- |

-- First we code the actual substitution operation,
-- without any check.
-- We cannot error: if something is not in the
-- substitution map, we just leave it as is.
-- Furthermore, because we are only going to
-- substitute function arguments, we will 
-- only need to substitute PExpr and OExpr.
data SubstMap = SubstMap {
    pVars :: Map String (PExpr String ValueType),
    oVars :: Map String (OExpr String ValueType)
} deriving(Show, Eq)

substBExpr :: SubstMap -> BExpr String ValueType -> BExpr String ValueType
substBExpr _ (BConst b t) = BConst b t
substBExpr s (BNot b t) = BNot (substBExpr s b) t
substBExpr s (BOp op b1 b2 t) = BOp op (substBExpr s b1) (substBExpr s b2) t
substBExpr s (BComp c p1 p2 t) = BComp c (substPExpr s p1) (substPExpr s p2) t
substBExpr _ (BVar v t) = BVar v t
substBExpr s (BGen stmt t) = BGen (substStmt s stmt) t
substBExpr s (BApp v ops t) = BApp v (map (\(o, ps) -> (substOExpr s o, map (substPExpr s) ps)) ops) t
substBExpr s (BLitEq t' c o t) = BLitEq t' (substCExpr s c) (substOExpr s o) t

substPExpr :: SubstMap -> PExpr String ValueType -> PExpr String ValueType
substPExpr s (PVar v t) = case M.lookup v (pVars s) of
    Nothing -> (PVar v t)
    Just p -> p

substCExpr :: SubstMap -> CExpr String ValueType -> CExpr String ValueType
substCExpr _ x = x

substOExpr :: SubstMap -> OExpr String ValueType -> OExpr String ValueType
substOExpr s (OVar v t) = case M.lookup v (oVars s) of
    Nothing -> OVar v t
    Just o -> o
substOExpr s (OConst c t) = OConst (substCExpr s c) t
substOExpr s (OList os t) = OList (map (substOExpr s) os) t
substOExpr s (ORev o t) = ORev (substOExpr s o) t
substOExpr s (OIndex o p t) = OIndex (substOExpr s o) (substPExpr s p) t
substOExpr s (OApp v ops t) = OApp v (map (\(o, ps) -> (substOExpr s o, map (substPExpr s) ps)) ops) t
substOExpr s (OGen stmt t) = OGen (substStmt s stmt) t

substStmt :: SubstMap -> Stmt String ValueType -> Stmt String ValueType
substStmt s (SYield o t) = SYield (substOExpr s o) t
substStmt s (SOReturn o t) = SOReturn (substOExpr s o) t
substStmt s (SBReturn b t) = SBReturn (substBExpr s b) t
substStmt s (SIf b s1 s2 t) = SIf (substBExpr s b) (substStmt s s1) (substStmt s s2) t
substStmt s (SLetOutput (v, t') o stmt t) = SLetOutput (v, t') (substOExpr s o) (substStmt s stmt) t
substStmt s (SLetBoolean v stmt t) = SLetBoolean v (substStmt s stmt) t
substStmt _ (SSetTrue v t) = SSetTrue v t
substStmt s (SFor (i, e, t') v stmt t) = SFor (i, e, t') (substOExpr s v) (substStmt s stmt) t
substStmt s (SSeq ss t) = SSeq (map (substStmt s) ss) t


makeArguments :: [(String, ValueType, [String])] -> [(OExpr String ValueType, [PExpr String ValueType])] -> SubstMap
makeArguments names values = SubstMap {
    pVars = M.fromList $ zip (concatMap thd3 names) (concatMap snd values),
    oVars = M.fromList $ zip (map fst3 names) (map fst values)
}


elimBExpr :: (MonadElim m) => BExpr String ValueType -> m (BExpr String ValueType)
elimBExpr (BConst b t) = pure $ BConst b t
elimBExpr (BNot b t) = do
    b' <- elimBExpr b
    return $ BNot b' t
elimBExpr (BOp op b1 b2 t) = do
    b1' <- elimBExpr b1
    b2' <- elimBExpr b2
    return $ BOp op b1' b2' t
elimBExpr (BComp c p1 p2 t) = do
    p1' <- elimPExpr p1
    p2' <- elimPExpr p2
    return $ BComp c p1' p2' t
elimBExpr (BVar v t) = pure $ BVar v t
elimBExpr (BGen stmt t) = do
    stmt' <- elimStmt stmt
    return $ BGen stmt' t
elimBExpr (BApp v ops t) = do
    (StmtFun _ args body _) <- getFunctionBody v
    let argsmap = makeArguments args ops
    body' <- refreshStmt . substStmt argsmap $ body
    return $ BGen body' t
elimBExpr (BLitEq t' c o t) = do
    c' <- elimCExpr c
    o' <- elimOExpr o
    return $ BLitEq t' c' o' t


elimPExpr :: (MonadElim m) => PExpr String ValueType -> m (PExpr String ValueType)
elimPExpr x = pure x

elimCExpr :: (MonadElim m) => CExpr String ValueType -> m (CExpr String ValueType)
elimCExpr x = pure x

elimOExpr :: (MonadElim m) => OExpr String ValueType -> m (OExpr String ValueType)
elimOExpr (OVar v t) = pure $ OVar v t
elimOExpr (OConst c t) = pure $ OConst c t
elimOExpr (OList os t) = do
    os' <- mapM elimOExpr os
    return $ OList os' t
elimOExpr (ORev o t) = do
    o' <- elimOExpr o
    return $ ORev o' t
elimOExpr (OIndex o p t) = do
    o' <- elimOExpr o
    p' <- elimPExpr p
    return $ OIndex o' p' t
-- Applications
-- 1. get the function body
-- 2. eliminate function calls in the arguments
-- 3. substitute the arguments in the body
-- 4. freshen the variables in the body
-- 5. create a generator with the new body
elimOExpr (OApp v ops t) = do
    (StmtFun _ args body _) <- getFunctionBody v
    ops' <- mapM (\(o, ps) -> do
            o' <- elimOExpr o
            ps' <- mapM elimPExpr ps
            return (o', ps')
        ) ops
    let freeVars = freeVarsStmt body
    let argsmap = makeArguments args ops'
    let bodyWithoutVars = substStmt argsmap body
    body' <- refreshStmt bodyWithoutVars
    return $ OGen body' t
elimOExpr (OGen stmt t) = do
    stmt' <- elimStmt stmt
    return $ OGen stmt' t

elimStmt :: (MonadElim m) => Stmt String ValueType -> m (Stmt String ValueType)
elimStmt (SYield o t) = do
    o' <- elimOExpr o
    return $ SYield o' t
elimStmt (SOReturn o t) = do
    o' <- elimOExpr o
    return $ SOReturn o' t
elimStmt (SBReturn b t) = do
    b' <- elimBExpr b
    return $ SBReturn b' t
elimStmt (SIf b s1 s2 t) = do
    b' <- elimBExpr b
    s1' <- elimStmt s1
    s2' <- elimStmt s2
    return $ SIf b' s1' s2' t
elimStmt (SLetOutput (v,tv) o stmt t) = do
    o' <- elimOExpr o
    withLocalVars [v] $ do
        stmt' <- elimStmt stmt
        return $ SLetOutput (v,tv) o' stmt' t
elimStmt (SLetBoolean v stmt t) = do
    stmt' <- elimStmt stmt
    withLocalVars [v] $ do 
        return $ SLetBoolean v stmt' t
elimStmt (SSetTrue v t) = pure $ SSetTrue v t
elimStmt (SFor (i, e, t') v stmt t) = do
    v' <- elimOExpr v
    withLocalVars [i,e] $ do 
        stmt' <- elimStmt stmt
        return $ SFor (i, e, t') v' stmt' t
elimStmt (SSeq ss t) = do
    ss' <- mapM elimStmt ss
    return $ SSeq ss' t

elimProgramFuncsM :: (MonadElim m) => [StmtFun String ValueType] -> m [StmtFun String ValueType]
elimProgramFuncsM [] = pure []
elimProgramFuncsM (StmtFun v args stmt t : fs) = do
    let outArgs = map fst3 args
    let posArgs = concatMap thd3 args
    stmt' <- withLocalVars (outArgs ++ posArgs) $ elimStmt stmt
    withFunction (StmtFun v args stmt' t) $ do
        fs' <- elimProgramFuncsM fs
        return $ StmtFun v args stmt' t : fs'

elimProgramM :: (MonadElim m) => TProgram -> m TProgram
elimProgramM (Program funcs m) = do
    newFuncs <- elimProgramFuncsM funcs
    return $ Program newFuncs m

eliminateFunctionCalls :: TProgram -> TProgram
eliminateFunctionCalls p = runElimM $ elimProgramM p
