{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module FunctionElimination (eliminateFunctionCalls, hasFunctionCall)
where

import ForPrograms
import ForProgramsTyping

import Control.Monad
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as M

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



class (Monad m) => MonadElim m where
    introduceVar     :: String -> m String
    translateVar     :: String -> m String
    getFunctionBody  :: String -> m (StmtFun String ValueType)
    putFunctionBody  :: (StmtFun String ValueType) -> m ()
    resetVariables   :: m ()

type ElimM = State (Int, Map String String, (Map String (StmtFun String ValueType)))

instance MonadElim ElimM where
    introduceVar s = do
        (i, m, f) <- get
        put (i + 1, M.insert s (s ++ "#" ++ show i) m, f)
        return $ s ++ "#" ++ show i
    translateVar s = do
        (_, m, _) <- get
        case M.lookup s m of
            Nothing -> error $ "Variable not found: " ++ s
            Just s' -> return s'
    resetVariables = do
        (c, _, f) <- get
        put (c, M.empty, f)
    getFunctionBody s = do
        (_, _, f) <- get
        case M.lookup s f of
            Nothing -> error $ "Function not found: " ++ s
            Just stmt -> return stmt
    putFunctionBody stmt = do
        (c, m, f) <- get
        put (c, m, M.insert (funName stmt) stmt f)


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
    v' <- translateVar v
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
    v' <- translateVar v
    return $ BApp v' ops' t
refreshBExpr (BLitEq t c o t') = do
    c' <- refreshCExpr c
    o' <- refreshOExpr o
    return $ BLitEq t c' o' t'

refreshPExpr :: (MonadElim m) => PExpr String ValueType -> m (PExpr String ValueType)
refreshPExpr (PVar v t) = do
    v' <- translateVar v
    return $ PVar v' t

refreshCExpr :: (MonadElim m) => CExpr String ValueType -> m (CExpr String ValueType)
refreshCExpr x = pure x

refreshOExpr :: (MonadElim m) => OExpr String ValueType -> m (OExpr String ValueType)
refreshOExpr (OVar v t) = do
    v' <- translateVar v
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
    v' <- translateVar v
    return $ OApp v' ops' t
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
    v' <- introduceVar v
    s' <- refreshStmt s
    return $ SLetOutput (v', t') o' s' t
refreshStmt (SLetBoolean v s t) = do
    v' <- introduceVar v
    s' <- refreshStmt s
    return $ SLetBoolean v' s' t
refreshStmt (SSetTrue v t) = do
    v' <- translateVar v
    return $ SSetTrue v' t
refreshStmt (SFor (i, e, t') v s t) = do
    v' <- refreshOExpr v
    i' <- introduceVar i
    e' <- introduceVar e
    s' <- refreshStmt s
    return $ SFor (i', e', t') v' s' t
refreshStmt (SSeq ss t) = do
    ss' <- mapM refreshStmt ss
    return $ SSeq ss' t


refreshAndReset :: (MonadElim m) => Stmt String ValueType -> m (Stmt String ValueType)
refreshAndReset stmt = do
    stmt' <-  refreshStmt stmt
    resetVariables
    return stmt'

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
    Nothing -> error $ "(substPexpr) Variable not found: " ++ v
    Just p -> p

substCExpr :: SubstMap -> CExpr String ValueType -> CExpr String ValueType
substCExpr _ x = x

substOExpr :: SubstMap -> OExpr String ValueType -> OExpr String ValueType
substOExpr s (OVar v t) = case M.lookup v (oVars s) of
    Nothing -> error $ "(substOExpr) Variable not found: " ++ v ++ " in " ++ show s
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
    body' <- refreshAndReset . substStmt argsmap $ body
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
elimOExpr (OApp v ops t) = do
    (StmtFun _ args body _) <- getFunctionBody v
    ops' <- mapM (\(o, ps) -> do
            o' <- elimOExpr o
            ps' <- mapM elimPExpr ps
            return (o', ps')
        ) ops
    let argsmap = makeArguments args ops'
    body' <- refreshAndReset . substStmt argsmap $ body
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
elimStmt (SLetOutput v o stmt t) = do
    o' <- elimOExpr o
    stmt' <- elimStmt stmt
    return $ SLetOutput v o' stmt' t
elimStmt (SLetBoolean v stmt t) = do
    stmt' <- elimStmt stmt
    return $ SLetBoolean v stmt' t
elimStmt (SSetTrue v t) = pure $ SSetTrue v t
elimStmt (SFor (i, e, t') v stmt t) = do
    v' <- elimOExpr v
    stmt' <- elimStmt stmt
    return $ SFor (i, e, t') v' stmt' t
elimStmt (SSeq ss t) = do
    ss' <- mapM elimStmt ss
    return $ SSeq ss' t


elimProgramM :: (MonadElim m) => TProgram -> m TProgram
elimProgramM (Program funcs m) = do
    newFuncs <- forM funcs $ \(StmtFun v args stmt t) -> do
                    stmt' <- elimStmt stmt
                    putFunctionBody (StmtFun v args stmt' t) 
                    return $ StmtFun v args stmt' t
    return $ Program newFuncs m

eliminateFunctionCalls :: TProgram -> TProgram
eliminateFunctionCalls p = evalState (elimProgramM p :: ElimM TProgram) (0, M.empty, M.empty)
