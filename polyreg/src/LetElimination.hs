-- We enable some extensions 
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module LetElimination where

import Control.Monad 
import Control.Monad.Reader
import qualified Data.Map as M

import ForPrograms
import ForProgramsTyping

class (Monad m) => LetEliminationMonad m where 
    withVarVal :: String -> OExpr String ValueType  -> m a -> m a
    getVarVal :: String -> ValueType -> m (OExpr String ValueType)

data LetEliminationState = LetEliminationState { varVals :: M.Map String (OExpr String ValueType) }

newtype LetEliminationM a = LetEliminationM (Reader LetEliminationState a)
    deriving (  Functor, Applicative, Monad, MonadReader LetEliminationState)

instance LetEliminationMonad LetEliminationM where
    withVarVal v e m = do
        LetEliminationState varVals <- ask
        let varVals' = M.insert v e varVals
        local (\_ -> LetEliminationState varVals') m
    getVarVal v t = do
        LetEliminationState varVals <- ask
        case M.lookup v varVals of
            Just e -> return e
            Nothing -> return $ OVar v t


runLetEliminationM :: LetEliminationM a -> a
runLetEliminationM (LetEliminationM m)= runReader m (LetEliminationState M.empty)

eliminateLetProgram :: Program String ValueType -> Program String ValueType
eliminateLetProgram p = runLetEliminationM $ eliminateLetProgramM p

eliminateLetProgramM :: (LetEliminationMonad m) =>  Program String ValueType -> m (Program String ValueType)
eliminateLetProgramM (Program funcs n) = do
    funcs' <- mapM eliminateLetFuncM funcs
    return $ Program funcs' n

eliminateLetFuncM :: (LetEliminationMonad m) => StmtFun String ValueType -> m (StmtFun String ValueType)
eliminateLetFuncM (StmtFun n args body t) = do
    body' <- eliminateLetStmtM body
    return $ StmtFun n args body' t

eliminateLetStmtM :: (LetEliminationMonad m) => Stmt String ValueType -> m (Stmt String ValueType)
eliminateLetStmtM (SIf b s1 s2 t) = do
    b' <- eliminateLetBexprM b
    s1' <- eliminateLetStmtM s1
    s2' <- eliminateLetStmtM s2
    return $ SIf b' s1' s2' t
eliminateLetStmtM (SYield e t) = do
    e' <- eliminateLetOexprM e
    return $ SYield e' t
eliminateLetStmtM (SOReturn e t) = do
    e' <- eliminateLetOexprM e
    return $ SOReturn e' t
eliminateLetStmtM (SBReturn b t) = do
    b' <- eliminateLetBexprM b
    return $ SBReturn b' t
eliminateLetStmtM (SLetOutput (v, t1) e s t2) = do
    e' <- eliminateLetOexprM e
    withVarVal v e' $ do
        s' <- eliminateLetStmtM s
        return $ s'
eliminateLetStmtM (SLetBoolean v s t) = do
    s' <- eliminateLetStmtM s
    return $ SLetBoolean v s' t
eliminateLetStmtM (SSetTrue v t) = return $ SSetTrue v t
eliminateLetStmtM (SFor dir (i, v, t1) e s t2) = do
    e' <- eliminateLetOexprM e
    s' <- eliminateLetStmtM s
    return $ SFor dir (i, v, t1) e' s' t2
eliminateLetStmtM (SSeq ss t) = do
    ss' <- mapM eliminateLetStmtM ss
    return $ SSeq ss' t

eliminateLetBexprM :: (LetEliminationMonad m) => BExpr String ValueType -> m (BExpr String ValueType)
eliminateLetBexprM (BConst b t) = return $ BConst b t
eliminateLetBexprM (BNot b t) = do
    b' <- eliminateLetBexprM b
    return $ BNot b' t
eliminateLetBexprM (BOp op b1 b2 t) = do
    b1' <- eliminateLetBexprM b1
    b2' <- eliminateLetBexprM b2
    return $ BOp op b1' b2' t
eliminateLetBexprM (BVar v t) = return $ BVar v t
eliminateLetBexprM (BGen g t) = do 
    g' <- eliminateLetStmtM g
    return $ BGen g' t
eliminateLetBexprM (BComp op e1 e2 t) = do
    e1' <- eliminateLetPexprM e1
    e2' <- eliminateLetPexprM e2
    return $ BComp op e1' e2' t
eliminateLetBexprM (BApp f args t) = do
    args' <- forM args $ \(v, ps) -> do 
        v' <- eliminateLetOexprM v 
        ps' <- mapM eliminateLetPexprM ps 
        return $ (v', ps')
    return $ BApp f args' t  
eliminateLetBexprM (BLitEq t c e t2) = do 
    e' <- eliminateLetOexprM e 
    return $ BLitEq t c e' t2  

eliminateLetPexprM :: (LetEliminationMonad m) => PExpr String ValueType -> m (PExpr String ValueType)
eliminateLetPexprM (PVar v (TPos (Position e))) = do 
    -- A hack not to duplicate code where types are ()
    let et = fmap (const TBool) e
    e' <- eliminateLetOexprM et
    return $ PVar v (TPos (Position $ eraseTypesO e'))
eliminateLetPexprM e = return e



eliminateLetOexprM :: (LetEliminationMonad m) => OExpr String ValueType -> m (OExpr String ValueType)
eliminateLetOexprM (OVar v t) = getVarVal v t
eliminateLetOexprM (OConst v t) = return $ OConst v t
eliminateLetOexprM (OList l t) = do 
    l' <- mapM eliminateLetOexprM l 
    return $ OList l' t 
eliminateLetOexprM (OApp f args t) = do 
    args' <- forM args $ \(v, ps) -> do 
        v' <- eliminateLetOexprM v 
        ps' <- mapM eliminateLetPexprM ps 
        return $ (v', ps')
    return $ OApp f args' t 
eliminateLetOexprM (OGen s t) = do 
    s' <- eliminateLetStmtM s 
    return $ OGen s' t


