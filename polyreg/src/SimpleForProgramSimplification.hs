{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SimpleForProgramSimplification where 

import SimpleForPrograms 

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad

import QuantifierFree


iterateToFix :: (Eq a) => (a -> a) -> a -> a 
iterateToFix f a
    | f a == a = a 
    | otherwise = iterateToFix f (f a)

oneSimplification :: ForProgram -> ForProgram 
oneSimplification =  bconstSimplForProgram . staticVarCompForProgramFO

-- | Boolean constant simplification -- in this step we propagate constants, and eliminate dead code 

bconstSimplForProgram :: ForProgram -> ForProgram
bconstSimplForProgram (ForProgram vars stmts) = ForProgram vars $ bconstSimplStmt stmts

bconstSimplStmt :: ForStmt -> ForStmt
bconstSimplStmt (Seq stmts) = Seq $ map bconstSimplStmt stmts
bconstSimplStmt (If e s1 s2) =
    case bconstSimplExpr e of 
        BConst True -> bconstSimplStmt s1
        BConst False -> bconstSimplStmt s2
        e -> If e (bconstSimplStmt s1) (bconstSimplStmt s2)
bconstSimplStmt s = s

bconstSimplExpr :: BoolExpr -> BoolExpr 
bconstSimplExpr e@(BTest op e1 e2) 
    | e1 == e2 && opTrueWhenEqual op = BConst True
    | e1 == e2 && not (opTrueWhenEqual op) = BConst False
    | otherwise = e
bconstSimplExpr (BNot (BConst b)) = BConst $ not b
bconstSimplExpr (BBin Conj (BConst True) e) = bconstSimplExpr e
bconstSimplExpr (BBin Conj e (BConst True)) = bconstSimplExpr e
bconstSimplExpr (BBin Conj (BConst False) _) = BConst False
bconstSimplExpr (BBin Conj _ (BConst False)) = BConst False
bconstSimplExpr (BBin Disj (BConst True) _) = BConst True
bconstSimplExpr (BBin Disj _ (BConst True)) = BConst True
bconstSimplExpr (BBin Disj (BConst False) e) = bconstSimplExpr e
bconstSimplExpr (BBin Disj e (BConst False)) = bconstSimplExpr e
bconstSimplExpr (BBin Impl (BConst True) e) = bconstSimplExpr e
bconstSimplExpr (BBin Impl (BConst False) e) = BConst True 
bconstSimplExpr (BBin Impl e (BConst True)) = BConst True
bconstSimplExpr (BBin Impl e (BConst False)) = BNot e
bconstSimplExpr (BBin Equiv (BConst True) e) = bconstSimplExpr e
bconstSimplExpr (BBin Equiv (BConst False) e) = BNot e
bconstSimplExpr (BBin Equiv e (BConst True)) = bconstSimplExpr e
bconstSimplExpr (BBin Equiv e (BConst False)) = BNot e
bconstSimplExpr e = e 

opTrueWhenEqual :: TestOp -> Bool
opTrueWhenEqual Eq = True
opTrueWhenEqual Neq = False 
opTrueWhenEqual Lt = False
opTrueWhenEqual Le = True
opTrueWhenEqual Gt = False
opTrueWhenEqual Ge = True


--- Static variable computation -- in this step we try to compute the value of each variable at each position.
--- Each variable is either equal to True, False, or Unknown (in case we cannot determine its value). 

data VarValue = VTrue | VFalse | VUnknown deriving (Show, Eq)

type VarValues = M.Map BName VarValue 

class (Monad m) => StaticVarComputationMonad m where
    getVarValue :: BName -> m VarValue
    setVarValue :: BName -> VarValue -> m ()  
    getVars :: m (M.Map BName VarValue)
    withNewVar :: BName -> m a -> m a
    withVars :: M.Map BName VarValue -> m a -> m a

newtype StaticVarComputationMonadT a = StaticVarComputationMonadT (State VarValues a) deriving (Functor, Applicative, Monad, MonadState VarValues)

instance StaticVarComputationMonad StaticVarComputationMonadT where 
    getVarValue v = do 
        vars <- get
        case M.lookup v vars of 
            Just val -> return val
            Nothing -> error $ "No such variable " ++ show v
    setVarValue v val = do 
        vars <- get
        put $ M.insert v val vars
    getVars = get
    withNewVar v m = do 
        old <- get
        put $ M.insert v VFalse old
        res <- m 
        put old 
        return res
    withVars vars m = do 
        oldVars <- getVars
        put vars
        res <- m
        put oldVars
        return res 

runStaticVarComputationMonadT :: StaticVarComputationMonadT a -> a 
runStaticVarComputationMonadT (StaticVarComputationMonadT x) = evalState x M.empty

withNewVars :: (StaticVarComputationMonad m) => [BName] -> m a -> m a
withNewVars [] m = m
withNewVars (v:vs) m = withNewVar v $ withNewVars vs m

ifFalseSetUnknown :: (StaticVarComputationMonad m) => BName -> m ()
ifFalseSetUnknown v = do 
    vval <- getVarValue v
    case vval of 
        VFalse -> setVarValue v VUnknown
        _ -> return ()

staticVarCompForProgramFO :: ForProgram -> ForProgram 
staticVarCompForProgramFO = runStaticVarComputationMonadT . staticVarCompForSProgram

staticVarCompForSProgram :: (StaticVarComputationMonad m) => ForProgram -> m ForProgram
staticVarCompForSProgram (ForProgram vars stmt) = do 
    forM vars $ \v -> setVarValue v VFalse
    stmt' <- staticVarCompStmt stmt
    return $ ForProgram vars stmt'

staticVarCompStmt :: (StaticVarComputationMonad m) =>  ForStmt -> m ForStmt
staticVarCompStmt (Seq stmts) = do 
    stmts' <- mapM staticVarCompStmt stmts
    return $ Seq stmts'
staticVarCompStmt (If e s1 s2) = do
    e' <- staticVarCompExpr e
    vars <- getVars
    (s1', vars1') <- withVars vars $ do 
        s1' <- staticVarCompStmt s1
        vars1' <- getVars
        return (s1', vars1')
    (s2', vars2') <- withVars vars $ do
        s2' <- staticVarCompStmt s2
        vars2' <- getVars
        return (s2', vars2')
    forM_ (M.keys vars) $ \v -> do 
        let vval1 = vars1' M.! v
        let vval2 = vars2' M.! v
        case (vval1, vval2) of 
            (VTrue, VTrue) -> setVarValue v VTrue
            (VFalse, VFalse) -> setVarValue v VFalse
            _ -> setVarValue v VUnknown
    return $ If e' s1' s2'
staticVarCompStmt forStmt@(For v d vars s) = do
    let mv = getModifiedVars forStmt
    -- Here we use the assumption about the FO. 
    forM_ mv ifFalseSetUnknown
    s' <- withNewVars vars $ staticVarCompStmt s
    return $ For v d vars s'
staticVarCompStmt (SetTrue v) = do 
    vval <- getVarValue v
    setVarValue v VTrue
    case vval of 
        VTrue -> return $ Seq []
        _ -> return $ SetTrue v
staticVarCompStmt s = return s

staticVarCompExpr :: (StaticVarComputationMonad m) => BoolExpr -> m BoolExpr
staticVarCompExpr (BVar v) = do 
    vval <- getVarValue v
    case vval of 
        VTrue -> return $ BConst True
        VFalse -> return $ BConst False
        VUnknown -> return $ BVar v
staticVarCompExpr (BNot e) = BNot <$> staticVarCompExpr e
staticVarCompExpr (BBin op e1 e2) = BBin op <$> staticVarCompExpr e1 <*> staticVarCompExpr e2
staticVarCompExpr e = return e

getModifiedVars :: ForStmt -> S.Set BName
getModifiedVars (Seq stmts) = S.unions $ map getModifiedVars stmts
getModifiedVars (If _ s1 s2) = getModifiedVars s1 `S.union` getModifiedVars s2
getModifiedVars (For _ _ vars s) = getModifiedVars s `S.difference` (S.fromList vars)
getModifiedVars (SetTrue v) = S.singleton v
getModifiedVars _ = S.empty
