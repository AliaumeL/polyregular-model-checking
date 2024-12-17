{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module LetBoolsToTop(bringLetBoolsToTopAndRefresh) where 

import Control.Monad.State

import Data.Map (Map)
import qualified Data.Map as M

import ForPrograms 

bringLetBoolsToTopAndRefresh :: Program String t -> Program String t
bringLetBoolsToTopAndRefresh = bringLetBoolsToTop . refreshBoolsProg


bringLetBoolsToTop :: Program s t -> Program s t
bringLetBoolsToTop (Program fs main) = Program (map bringLetBoolsToTopFun fs) main

bringLetBoolsToTopFun :: StmtFun s t -> StmtFun s t 
bringLetBoolsToTopFun (StmtFun n args s t) =
    let (s', vars) = bringLetBoolsToTopStmt s in
    let s'' = withVars vars s' in
    StmtFun n args s'' t

getLabel :: Stmt s t -> t
getLabel (SIf _ _ _ t) = t
getLabel (SYield _ t) = t
getLabel (SOReturn _ t) = t
getLabel (SBReturn _ t) = t
getLabel (SLetOutput _ _ _ t) = t
getLabel (SLetBoolean _ _ t) = t
getLabel (SSetTrue _ t) = t
getLabel (SFor _ _ _ _ t) = t
getLabel (SSeq _ t) = t


withVars :: [s] -> Stmt s t -> Stmt s t 
withVars [] s = s 
withVars (v : vs) s = SLetBoolean v (withVars vs s) (getLabel s)

bringLetBoolsToTopStmt :: Stmt s t -> (Stmt s t, [s])
bringLetBoolsToTopStmt (SIf b s1 s2 t) =
    let (s1', v1) = bringLetBoolsToTopStmt s1 in
    let (s2', v2) = bringLetBoolsToTopStmt s2 in
    let b' = bringLetBoolsToTopBExpr b in
    (SIf b' s1' s2' t, v1 ++ v2)
bringLetBoolsToTopStmt (SYield e t) =
    let e' = bringLetBoolsToTopOExpr e in
    (SYield e' t, [])
bringLetBoolsToTopStmt (SOReturn e t) =
    let e' = bringLetBoolsToTopOExpr e in
    (SOReturn e' t, [])
bringLetBoolsToTopStmt (SBReturn b t) = 
    let b' = bringLetBoolsToTopBExpr b in
    (SBReturn b' t, [])
bringLetBoolsToTopStmt (SLetOutput n e s t) =
    let (s', v) = bringLetBoolsToTopStmt s in
    let e' = bringLetBoolsToTopOExpr e in
    (SLetOutput n e' s' t, v)
bringLetBoolsToTopStmt (SLetBoolean n s t) =
    let (s',  v) = bringLetBoolsToTopStmt s in
    (s', n : v)
bringLetBoolsToTopStmt s@(SSetTrue n t) = 
    (s, [])
bringLetBoolsToTopStmt (SSeq ss t) = 
    let ans = map bringLetBoolsToTopStmt ss in
    let s' = SSeq (map fst ans) t in
    let vs = concat $ map snd ans in
    (s', vs) 
bringLetBoolsToTopStmt (SFor d (i, v, ti) e s t) =
    let (s', vars) = bringLetBoolsToTopStmt s in
    let s'' = withVars vars s' in
    let e' = bringLetBoolsToTopOExpr e in
    (SFor d (i, v, ti) e' s'' t, [])

bringLetBoolsToTopOExpr :: OExpr s t -> OExpr s t
bringLetBoolsToTopOExpr e@(OVar _ _) = e
bringLetBoolsToTopOExpr e@(OConst _ _) = e
bringLetBoolsToTopOExpr (OList es t) =
    OList (map bringLetBoolsToTopOExpr es) t
bringLetBoolsToTopOExpr (OApp f args t) =
    let args' = map (\(e, ps) -> (bringLetBoolsToTopOExpr e, ps)) args in
    OApp f args' t
bringLetBoolsToTopOExpr (OGen stmt t) = 
    let (stmt', vs) = bringLetBoolsToTopStmt stmt in
    let stmt'' = withVars vs stmt' in
    OGen stmt'' t

bringLetBoolsToTopBExpr :: BExpr s t -> BExpr s t
bringLetBoolsToTopBExpr e@(BConst _ _) = e
bringLetBoolsToTopBExpr (BNot b t) = BNot (bringLetBoolsToTopBExpr b) t
bringLetBoolsToTopBExpr (BOp op b1 b2 t) = BOp op (bringLetBoolsToTopBExpr b1) (bringLetBoolsToTopBExpr b2) t
bringLetBoolsToTopBExpr e@(BComp _ e1 e2 _) = e
bringLetBoolsToTopBExpr e@(BVar _ _) = e
bringLetBoolsToTopBExpr (BApp f args t) =
    let args' = map (\(e, ps) -> (bringLetBoolsToTopOExpr e, ps)) args in
    BApp f args' t
bringLetBoolsToTopBExpr (BLitEq t c e tb) =
    let e' = bringLetBoolsToTopOExpr e in
    BLitEq t c e' tb
bringLetBoolsToTopBExpr (BGen stmt t) =
    let (stmt', vs) = bringLetBoolsToTopStmt stmt in
    let stmt'' = withVars vs stmt' in
    BGen stmt'' t






--- REFRESH BOOLEANS, ONE MORE TIME.

class (Monad m) => MonadRefreshBools m where
    withBool :: String -> m a -> m a
    getBool  :: String -> m String

data RefreshState = RefreshState {
    varMap  :: Map String String,
    nextVar :: Int
} deriving (Eq,Show)

newtype RefreshBools a = RefreshBoolsT (State RefreshState a) 
    deriving (Functor, Applicative, Monad, MonadState RefreshState)

instance MonadRefreshBools RefreshBools where
    withBool v m = do
        counter <- gets nextVar
        let newVarName = "b#refresh#" ++ show counter
        modify (\s -> s { varMap = M.insert v newVarName (varMap s), nextVar = counter + 1 })
        output <- m
        modify (\s -> s { varMap = M.delete v (varMap s) })
        return output

    getBool v = do
        m <- gets varMap
        case M.lookup v m of
            Just v' -> return v'
            Nothing -> error $ "Variable not found" ++ show m


runRefreshBools :: RefreshBools a -> a
runRefreshBools (RefreshBoolsT m) = evalState m (RefreshState M.empty 0)

refreshBoolsProg :: Program String t -> Program String t
refreshBoolsProg = runRefreshBools . refreshBoolsProgM

refreshBoolsProgM :: Program String t -> RefreshBools (Program String t)
refreshBoolsProgM (Program fs main) = do
    fs' <- mapM refreshBoolsFun fs
    return $ Program fs' main

refreshBoolsFun :: StmtFun String t -> RefreshBools (StmtFun String t)
refreshBoolsFun (StmtFun n args s t) = do
    s' <- refreshBoolsStmt s
    return $ StmtFun n args s' t

refreshBoolsStmt :: Stmt String t -> RefreshBools (Stmt String t)
refreshBoolsStmt (SIf b s1 s2 t) = do
    b' <- refreshBoolsBExpr b
    s1' <- refreshBoolsStmt s1
    s2' <- refreshBoolsStmt s2
    return $ SIf b' s1' s2' t
refreshBoolsStmt (SYield e t) = do
    e' <- refreshBoolsOExpr e
    return $ SYield e' t
refreshBoolsStmt (SOReturn e t) = do
    e' <- refreshBoolsOExpr e
    return $ SOReturn e' t
refreshBoolsStmt (SBReturn b t) = do
    b' <- refreshBoolsBExpr b
    return $ SBReturn b' t
refreshBoolsStmt (SLetOutput n e s t) = do
    e' <- refreshBoolsOExpr e
    s' <- refreshBoolsStmt s
    return $ SLetOutput n e' s' t
refreshBoolsStmt (SLetBoolean n s t) = do
    withBool n $ do
        n' <- getBool n
        s' <- refreshBoolsStmt s
        return $ SLetBoolean n' s' t
refreshBoolsStmt (SSetTrue n t) = do
    n' <- getBool n
    return $ SSetTrue n' t
refreshBoolsStmt (SSeq ss t) = do
    ss' <- mapM refreshBoolsStmt ss
    return $ SSeq ss' t
refreshBoolsStmt (SFor d (i, v, ti) e s t) = do
    e' <- refreshBoolsOExpr e
    s' <- refreshBoolsStmt s
    return $ SFor d (i, v, ti) e' s' t


refreshBoolsOExpr :: OExpr String t -> RefreshBools (OExpr String t)
refreshBoolsOExpr e@(OVar _ _) = return e
refreshBoolsOExpr e@(OConst _ _) = return e
refreshBoolsOExpr (OList es t) = do
    es' <- mapM refreshBoolsOExpr es
    return $ OList es' t
refreshBoolsOExpr (OApp f args t) = do
    args' <- mapM (\(e, ps) -> do
        e' <- refreshBoolsOExpr e
        return (e', ps)) args
    return $ OApp f args' t
refreshBoolsOExpr (OGen stmt t) = do
    stmt' <- refreshBoolsStmt stmt
    return $ OGen stmt' t

refreshBoolsBExpr :: BExpr String t -> RefreshBools (BExpr String t)
refreshBoolsBExpr e@(BConst _ _) = return e
refreshBoolsBExpr (BNot b t) = do
    b' <- refreshBoolsBExpr b
    return $ BNot b' t
refreshBoolsBExpr (BOp op b1 b2 t) = do
    b1' <- refreshBoolsBExpr b1
    b2' <- refreshBoolsBExpr b2
    return $ BOp op b1' b2' t
refreshBoolsBExpr e@(BComp _ _ _ _) = return e
refreshBoolsBExpr (BVar v t) = BVar <$> getBool v <*> pure t
refreshBoolsBExpr (BApp f args t) = do
    args' <- mapM (\(e, ps) -> do
        e' <- refreshBoolsOExpr e
        return (e', ps)) args
    return $ BApp f args' t
refreshBoolsBExpr (BLitEq t c e tb) = do
    e' <- refreshBoolsOExpr e
    return $ BLitEq t c e' tb
refreshBoolsBExpr (BGen stmt t) = do
    stmt' <- refreshBoolsStmt stmt
    return $ BGen stmt' t


