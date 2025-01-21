{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module ForPrograms.Simple.Optimization (simplifyForProgram, eliminateUnusedVars, eliminateInconsequentialStmts, bconstSimplForProgram, staticVarCompForProgramFO) where 

import ForPrograms.Simple

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad

import Debug.Trace

import QuantifierFree

iterateToFix :: (Eq a) => (a -> a) -> a -> a 
iterateToFix f a
    | f a == a = a 
    | otherwise = iterateToFix f (f a)

oneSimplification :: ForProgram -> ForProgram 
oneSimplification =  simplifyConditionalSets . eliminateUnusedVars . bconstSimplForProgram . staticVarCompForProgramFO . eliminateInconsequentialStmts 
--eliminateUnusedVars . eliminateInconsequentialStmts . bconstSimplForProgram . staticVarCompForProgramFO

simplifyForProgram :: ForProgram -> ForProgram
simplifyForProgram = iterateToFix oneSimplification

-- | Boolean constant simplification -- in this step we propagate constants, and eliminate dead code 

bconstSimplForProgram :: ForProgram -> ForProgram
bconstSimplForProgram (ForProgram vars stmts) = ForProgram vars $ bconstSimplStmt stmts

bconstSimplStmt :: ForStmt -> ForStmt
bconstSimplStmt (Seq stmts) =
    let stmts' = filter (not . isEmpty) $ map bconstSimplStmt stmts in
    case stmts' of
        [stmt] -> stmt
        _ -> Seq stmts'
bconstSimplStmt (If e s1 s2) = 
    let s1' = bconstSimplStmt s1 in 
    let s2' = bconstSimplStmt s2 in 
    if s1' == s2' then s1' else
    case bconstSimplExprRec e of 
        BConst True -> bconstSimplStmt s1
        BConst False -> bconstSimplStmt s2
        BNot e' -> If e' (bconstSimplStmt s2) (bconstSimplStmt s1)
        e' -> If e' (bconstSimplStmt s1) (bconstSimplStmt s2)
bconstSimplStmt (For v d vars s) = 
    let s' = bconstSimplStmt s in
    if isEmpty s' then Seq [] else
    For v d vars $ bconstSimplStmt s
bconstSimplStmt s = s

isEmpty :: ForStmt -> Bool
isEmpty (Seq []) = True
isEmpty _ = False

bconstSimplExprRec :: BoolExpr -> BoolExpr
bconstSimplExprRec e@(BBin op e1 e2) = bconstSimplExpr $ BBin op (bconstSimplExprRec e1) (bconstSimplExprRec e2)
bconstSimplExprRec e@(BTest _ _ _) = bconstSimplExpr e
bconstSimplExprRec (BNot e) = bconstSimplExpr $ BNot $ bconstSimplExprRec e
bconstSimplExprRec e = e 


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

setVarsFromBooleanValuation :: (StaticVarComputationMonad m) => BoolExpr -> Bool -> m ()
setVarsFromBooleanValuation (BVar v) b = setVarValue v $ if b then VTrue else VFalse
setVarsFromBooleanValuation (BNot e) b = setVarsFromBooleanValuation e (not b)
setVarsFromBooleanValuation (BBin Conj e1 e2) True = do 
    setVarsFromBooleanValuation e1 True 
    setVarsFromBooleanValuation e2 True
setVarsFromBooleanValuation (BBin Disj e1 e2) False = do
    setVarsFromBooleanValuation e1 False
    setVarsFromBooleanValuation e2 False
setVarsFromBooleanValuation (BBin Impl e1 e2) False = do
    setVarsFromBooleanValuation e1 True
    setVarsFromBooleanValuation e2 False
setVarsFromBooleanValuation _ _ = return ()

staticVarCompStmt :: (StaticVarComputationMonad m) =>  ForStmt -> m ForStmt
staticVarCompStmt (Seq stmts) = do 
    stmts' <- mapM staticVarCompStmt stmts
    return $ Seq stmts'
staticVarCompStmt (If e s1 s2) = do
    e' <- staticVarCompExpr e
    vars <- getVars
    (s1', vars1') <- withVars vars $ do
        setVarsFromBooleanValuation e' True 
        s1' <- staticVarCompStmt s1
        vars1' <- getVars
        return (s1', vars1')
    (s2', vars2') <- withVars vars $ do
        setVarsFromBooleanValuation e' False
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

-- Now we eliminate unused variables. 

eliminateUnusedVars :: ForProgram -> ForProgram
eliminateUnusedVars (ForProgram vars stmt) = 
    let (stmt', usedVars) = eliminateUnusedAndComputeUsedStmt stmt in
    let newVars = filter (`S.member` usedVars) vars in
    ForProgram newVars stmt'

eliminateUnusedAndComputeUsedStmt :: ForStmt -> (ForStmt, S.Set BName)
eliminateUnusedAndComputeUsedStmt (Seq stmts) = 
    let (stmts', usedVars) = unzip $ map eliminateUnusedAndComputeUsedStmt stmts in
    (Seq stmts', S.unions usedVars)
eliminateUnusedAndComputeUsedStmt (If e s1 s2) =
    let varsE = getTestedVarsExpr e in
    let (s1', usedVars1) = eliminateUnusedAndComputeUsedStmt s1 in
    let (s2', usedVars2) = eliminateUnusedAndComputeUsedStmt s2 in
    (If e s1' s2', S.unions [varsE, usedVars1, usedVars2])
eliminateUnusedAndComputeUsedStmt (For v d vars s) =
    let (s', usedVars) = eliminateUnusedAndComputeUsedStmt s in
    let newVars = S.fromList vars `S.intersection` usedVars in
    (For v d (S.toList newVars) s', usedVars `S.difference` S.fromList vars)
eliminateUnusedAndComputeUsedStmt (SetTrue v) = (SetTrue v, S.singleton v)
eliminateUnusedAndComputeUsedStmt s = (s, S.empty)

getTestedVarsExpr :: BoolExpr -> S.Set BName
getTestedVarsExpr (BVar v) = S.singleton v
getTestedVarsExpr (BNot e) = getTestedVarsExpr e
getTestedVarsExpr (BBin _ e1 e2) = S.union (getTestedVarsExpr e1) (getTestedVarsExpr e2)
getTestedVarsExpr _ = S.empty

-- Finally, we show how to eliminate inconsequential statements -- a statement is inconsequential if it modifies a variable after all tests on it have been performed.

eliminateInconsequentialStmts :: ForProgram -> ForProgram
eliminateInconsequentialStmts (ForProgram vars stmt) = ForProgram vars $ fst $ eliminateInconsequentialStmtAndComputeTested (S.fromList vars) stmt

eliminateInconsequentialStmtAndComputeTested :: S.Set BName -> ForStmt -> (ForStmt, S.Set BName)
eliminateInconsequentialStmtAndComputeTested vars s@(Seq stmts) = (ans, testedVars) 
  where 
    (stmts'', _, testedVars) = foldl f ([], vars, S.empty) (reverse stmts)
    f (stmts, inconsequentialVars, testedVars ) stmt = 
        let (stmt', tested) = eliminateInconsequentialStmtAndComputeTested inconsequentialVars stmt in
        (stmt' : stmts, inconsequentialVars `S.difference` tested, testedVars `S.union` tested)
    ans = Seq $ stmts''
eliminateInconsequentialStmtAndComputeTested vars (If e s1 s2) = (stmt', tested)
    where
        (s1', vars1) = eliminateInconsequentialStmtAndComputeTested vars s1
        (s2', vars2) = eliminateInconsequentialStmtAndComputeTested vars s2
        stmt' = If e s1' s2'
        tested = vars1 `S.union` vars2 `S.union` getTestedVarsExpr e
eliminateInconsequentialStmtAndComputeTested vars (For v d newVars s) =
    let testedVars = getTestedVarsStmt s in -- TODO : Might be inefficient
    let newInconsequential = (vars `S.difference` testedVars) `S.union` (S.fromList newVars) in
    let (s', _) = eliminateInconsequentialStmtAndComputeTested newInconsequential s in
    (For v d newVars s', testedVars `S.difference` S.fromList newVars)
eliminateInconsequentialStmtAndComputeTested vars (SetTrue v)
    | S.member v vars = (Seq [], S.empty)
    | otherwise = (SetTrue v, S.empty)
eliminateInconsequentialStmtAndComputeTested _ s = (s, S.empty)

getTestedVarsStmt :: ForStmt -> S.Set BName
getTestedVarsStmt (Seq stmts) = S.unions $ map getTestedVarsStmt stmts
getTestedVarsStmt (If e s1 s2) = getTestedVarsExpr e `S.union` getTestedVarsStmt s1 `S.union` getTestedVarsStmt s2
getTestedVarsStmt (For _ _ vars s) = getTestedVarsStmt s `S.difference` S.fromList vars
getTestedVarsStmt _ = S.empty


---- In this simplification we change if not b then b := true else skip to b := true.
---- And similarly if b then skip else b := true to b := true.
---- Also if b then b := true else skip to skip.
simplifyConditionalSets :: ForProgram -> ForProgram
simplifyConditionalSets (ForProgram vars stmt) = ForProgram vars $ simplifyConditionalSetsStmt stmt

simplifyConditionalSetsStmt :: ForStmt -> ForStmt
simplifyConditionalSetsStmt (Seq stmts) = Seq $ map simplifyConditionalSetsStmt stmts
simplifyConditionalSetsStmt s@(If (BNot (BVar v1)) (SetTrue v2) (Seq []))
    | v1 == v2 = SetTrue v1
    | otherwise = s
simplifyConditionalSetsStmt s@(If (BVar v1) (Seq []) (SetTrue v2))
    | v1 == v2 = SetTrue v1
    | otherwise = s
simplifyConditionalSetsStmt s@(If (BVar v1) (SetTrue v2) (Seq []))
    | v1 == v2 = Seq []
    | otherwise = s
simplifyConditionalSetsStmt s@(If e s1 s2) = If e (simplifyConditionalSetsStmt s1) (simplifyConditionalSetsStmt s2)
simplifyConditionalSetsStmt (For v d vars s) = For v d vars $ simplifyConditionalSetsStmt s
simplifyConditionalSetsStmt s = s

