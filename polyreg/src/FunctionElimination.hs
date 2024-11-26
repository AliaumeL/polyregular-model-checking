{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module FunctionElimination where

import ForPrograms

import Control.Monad
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as M


class (Monad m) => MonadElim m where
    introduceVar     :: String -> m String
    translateVar     :: String -> m String
    getFunctionBody  :: String -> m (StmtFun String ())
    putFunctionBody  :: (StmtFun String ()) -> m ()
    resetVariables   :: m ()

type ElimM = State (Int, Map String String, (Map String (StmtFun String ())))

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


refreshBExpr :: (MonadElim m) => BExpr String () -> m (BExpr String ())
refreshBExpr (BConst b ()) = pure $ BConst b ()
refreshBExpr (BNot b ()) = do
    b' <- refreshBExpr b
    return $ BNot b' ()
refreshBExpr (BOp op b1 b2 ()) = do
    b1' <- refreshBExpr b1
    b2' <- refreshBExpr b2
    return $ BOp op b1' b2' ()
refreshBExpr (BComp c p1 p2 ()) = do
    p1' <- refreshPExpr p1
    p2' <- refreshPExpr p2
    return $ BComp c p1' p2' ()
refreshBExpr (BVar v ()) = do
    v' <- translateVar v
    return $ BVar v' ()
refreshBExpr (BGen stmt ()) = do
    stmt' <- refreshStmt stmt
    return $ BGen stmt' ()
refreshBExpr (BApp v ops ()) = do
    ops' <- mapM (\(o, ps) -> do
            o' <- refreshOExpr o
            ps' <- mapM refreshPExpr ps
            return (o', ps')
        ) ops
    v' <- translateVar v
    return $ BApp v' ops' ()
refreshBExpr (BLitEq c o ()) = do
    c' <- refreshCExpr c
    o' <- refreshOExpr o
    return $ BLitEq c' o' ()

refreshPExpr :: (MonadElim m) => PExpr String () -> m (PExpr String ())
refreshPExpr (PVar v ()) = do
    v' <- translateVar v
    return $ PVar v' ()

refreshCExpr :: (MonadElim m) => CExpr String () -> m (CExpr String ())
refreshCExpr x = pure x

refreshOExpr :: (MonadElim m) => OExpr String () -> m (OExpr String ())
refreshOExpr (OVar v ()) = do
    v' <- translateVar v
    return $ OVar v' ()
refreshOExpr (OConst c ()) = pure (OConst c ())
refreshOExpr (OList os ()) = do
    os' <- mapM refreshOExpr os
    return $ OList os' ()
refreshOExpr (ORev o ()) = do
    o' <- refreshOExpr o
    return $ ORev o' ()
refreshOExpr (OIndex o p ()) = do
    o' <- refreshOExpr o
    p' <- refreshPExpr p
    return $ OIndex o' p' ()
refreshOExpr (OApp v ops ()) = do
    ops' <- mapM (\(o, ps) -> do
            o' <- refreshOExpr o
            ps' <- mapM refreshPExpr ps
            return (o', ps')
        ) ops
    v' <- translateVar v
    return $ OApp v' ops' ()
refreshOExpr (OGen stmt ()) = do
    stmt' <- refreshStmt stmt
    return $ OGen stmt' ()

refreshStmt :: (MonadElim m) => Stmt String () -> m (Stmt String ())
refreshStmt (SYield o ()) = do
    o' <- refreshOExpr o
    return $ SYield o' ()
refreshStmt (SOReturn o ()) = do
    o' <- refreshOExpr o
    return $ SOReturn o' ()
refreshStmt (SBReturn b ()) = do
    b' <- refreshBExpr b
    return $ SBReturn b' ()
refreshStmt (SIf b s1 s2 ()) = do
    b' <- refreshBExpr b
    s1' <- refreshStmt s1
    s2' <- refreshStmt s2
    return $ SIf b' s1' s2' ()
refreshStmt (SLetOutput v o s ()) = do
    o' <- refreshOExpr o
    v' <- introduceVar v
    s' <- refreshStmt s
    return $ SLetOutput v' o' s' ()
refreshStmt (SLetBoolean v s ()) = do
    v' <- introduceVar v
    s' <- refreshStmt s
    return $ SLetBoolean v' s' ()
refreshStmt (SSetTrue v ()) = do
    v' <- translateVar v
    return $ SSetTrue v' ()
refreshStmt (SFor (i, e) v s ()) = do
    v' <- refreshOExpr v
    i' <- introduceVar i
    e' <- introduceVar e
    s' <- refreshStmt s
    return $ SFor (i', e') v' s' ()
refreshStmt (SSeq ss ()) = do
    ss' <- mapM refreshStmt ss
    return $ SSeq ss' ()


refreshAndReset :: (MonadElim m) => Stmt String () -> m (Stmt String ())
refreshAndReset stmt = do
    stmt' <-  refreshStmt stmt
    resetVariables
    return stmt'

data SubstMap = SubstMap {
    pVars :: Map String (PExpr String ()),
    oVars :: Map String (OExpr String ())
} deriving(Show, Eq)


substBExpr :: SubstMap -> BExpr String () -> BExpr String ()
substBExpr _ (BConst b ()) = BConst b ()
substBExpr s (BNot b ()) = BNot (substBExpr s b) ()
substBExpr s (BOp op b1 b2 ()) = BOp op (substBExpr s b1) (substBExpr s b2) ()
substBExpr s (BComp c p1 p2 ()) = BComp c (substPExpr s p1) (substPExpr s p2) ()
substBExpr _ (BVar v ()) = BVar v ()
substBExpr s (BGen stmt ()) = BGen (substStmt s stmt) ()
substBExpr s (BApp v ops ()) = BApp v (map (\(o, ps) -> (substOExpr s o, map (substPExpr s) ps)) ops) ()
substBExpr s (BLitEq c o ()) = BLitEq (substCExpr s c) (substOExpr s o) ()

substPExpr :: SubstMap -> PExpr String () -> PExpr String ()
substPExpr s (PVar v ()) = case M.lookup v (pVars s) of
    Nothing -> error $ "(substPexpr) Variable not found: " ++ v
    Just p -> p

substCExpr :: SubstMap -> CExpr String () -> CExpr String ()
substCExpr _ x = x

substOExpr :: SubstMap -> OExpr String () -> OExpr String ()
substOExpr s (OVar v ()) = case M.lookup v (oVars s) of
    Nothing -> error $ "(substOExpr) Variable not found: " ++ v
    Just o -> o
substOExpr s (OConst c ()) = OConst (substCExpr s c) ()
substOExpr s (OList os ()) = OList (map (substOExpr s) os) ()
substOExpr s (ORev o ()) = ORev (substOExpr s o) ()
substOExpr s (OIndex o p ()) = OIndex (substOExpr s o) (substPExpr s p) ()
substOExpr s (OApp v ops ()) = OApp v (map (\(o, ps) -> (substOExpr s o, map (substPExpr s) ps)) ops) ()
substOExpr s (OGen stmt ()) = OGen (substStmt s stmt) ()

substStmt :: SubstMap -> Stmt String () -> Stmt String ()
substStmt s (SYield o ()) = SYield (substOExpr s o) ()
substStmt s (SOReturn o ()) = SOReturn (substOExpr s o) ()
substStmt s (SBReturn b ()) = SBReturn (substBExpr s b) ()
substStmt s (SIf b s1 s2 ()) = SIf (substBExpr s b) (substStmt s s1) (substStmt s s2) ()
substStmt s (SLetOutput v o stmt ()) = SLetOutput v (substOExpr s o) (substStmt s stmt) ()
substStmt s (SLetBoolean v stmt ()) = SLetBoolean v (substStmt s stmt) ()
substStmt _ (SSetTrue v ()) = SSetTrue v ()
substStmt s (SFor (i, e) v stmt ()) = SFor (i, e) (substOExpr s v) (substStmt s stmt) ()
substStmt s (SSeq ss ()) = SSeq (map (substStmt s) ss) ()


makeArguments :: [(String, [String])] -> [(OExpr String (), [PExpr String ()])] -> SubstMap
makeArguments names values = SubstMap {
    pVars = M.fromList $ zip (concatMap snd names) (concatMap snd values),
    oVars = M.fromList $ zip (map fst names) (map fst values)
}


elimBExpr :: (MonadElim m) => BExpr String () -> m (BExpr String ())
elimBExpr (BConst b ()) = pure $ BConst b ()
elimBExpr (BNot b ()) = do
    b' <- elimBExpr b
    return $ BNot b' ()
elimBExpr (BOp op b1 b2 ()) = do
    b1' <- elimBExpr b1
    b2' <- elimBExpr b2
    return $ BOp op b1' b2' ()
elimBExpr (BComp c p1 p2 ()) = do
    p1' <- elimPExpr p1
    p2' <- elimPExpr p2
    return $ BComp c p1' p2' ()
elimBExpr (BVar v ()) = pure $ BVar v ()
elimBExpr (BGen stmt ()) = do
    stmt' <- elimStmt stmt
    return $ BGen stmt' ()
elimBExpr (BApp v ops ()) = do
    (StmtFun _ args body _) <- getFunctionBody v
    let argsmap = makeArguments args ops
    body' <- refreshAndReset . substStmt argsmap $ body
    return $ BGen body' ()
elimBExpr (BLitEq c o ()) = do
    c' <- elimCExpr c
    o' <- elimOExpr o
    return $ BLitEq c' o' ()


elimPExpr :: (MonadElim m) => PExpr String () -> m (PExpr String ())
elimPExpr x = pure x

elimCExpr :: (MonadElim m) => CExpr String () -> m (CExpr String ())
elimCExpr x = pure x

elimOExpr :: (MonadElim m) => OExpr String () -> m (OExpr String ())
elimOExpr (OVar v ()) = pure $ OVar v ()
elimOExpr (OConst c ()) = pure $ OConst c ()
elimOExpr (OList os ()) = do
    os' <- mapM elimOExpr os
    return $ OList os' ()
elimOExpr (ORev o ()) = do
    o' <- elimOExpr o
    return $ ORev o' ()
elimOExpr (OIndex o p ()) = do
    o' <- elimOExpr o
    p' <- elimPExpr p
    return $ OIndex o' p' ()
elimOExpr (OApp v ops ()) = do
    (StmtFun _ args body _) <- getFunctionBody v
    ops' <- mapM (\(o, ps) -> do
            o' <- elimOExpr o
            ps' <- mapM elimPExpr ps
            return (o', ps')
        ) ops
    let argsmap = makeArguments args ops'
    body' <- refreshAndReset . substStmt argsmap $ body
    return $ OGen body' ()
elimOExpr (OGen stmt ()) = do
    stmt' <- elimStmt stmt
    return $ OGen stmt' ()

elimStmt :: (MonadElim m) => Stmt String () -> m (Stmt String ())
elimStmt (SYield o ()) = do
    o' <- elimOExpr o
    return $ SYield o' ()
elimStmt (SOReturn o ()) = do
    o' <- elimOExpr o
    return $ SOReturn o' ()
elimStmt (SBReturn b ()) = do
    b' <- elimBExpr b
    return $ SBReturn b' ()
elimStmt (SIf b s1 s2 ()) = do
    b' <- elimBExpr b
    s1' <- elimStmt s1
    s2' <- elimStmt s2
    return $ SIf b' s1' s2' ()
elimStmt (SLetOutput v o stmt ()) = do
    o' <- elimOExpr o
    stmt' <- elimStmt stmt
    return $ SLetOutput v o' stmt' ()
elimStmt (SLetBoolean v stmt ()) = do
    stmt' <- elimStmt stmt
    return $ SLetBoolean v stmt' ()
elimStmt (SSetTrue v ()) = pure $ SSetTrue v ()
elimStmt (SFor (i, e) v stmt ()) = do
    v' <- elimOExpr v
    stmt' <- elimStmt stmt
    return $ SFor (i, e) v' stmt' ()
elimStmt (SSeq ss ()) = do
    ss' <- mapM elimStmt ss
    return $ SSeq ss' ()


elimProgramM :: (MonadElim m) => UProgram -> m UProgram
elimProgramM (Program funcs m ()) = do
    newFuncs <- forM funcs $ \(StmtFun v args stmt _) -> do
                    stmt' <- elimStmt stmt
                    putFunctionBody (StmtFun v args stmt' ()) 
                    return $ StmtFun v args stmt' ()
    return $ Program newFuncs m ()

elimProgram :: UProgram -> UProgram
elimProgram p = evalState (elimProgramM p :: ElimM UProgram) (0, M.empty, M.empty)
