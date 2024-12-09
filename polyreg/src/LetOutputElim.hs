{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module LetOutputElim where

import ForPrograms
import QuantifierFree
import ForProgramsTyping (ValueType(..))

import Data.Map (Map)
import qualified Data.Map as M

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except


import Debug.Trace

class Monad m => MonadOutputElim m where
    withOutputVar :: String -> OExpr String ValueType -> m a -> m a
    getOutputVar  :: String -> m (Maybe (OExpr String ValueType))

    throwWithCtx :: String -> m a
    guardWithCtx :: Bool -> String -> m ()

data LetOutputElimState = LetOutputElimState { 
    outputVars :: Map String (OExpr String ValueType) 
} deriving (Eq,Show)

data LetOutputElimError = LetOutputElimError String deriving (Eq,Show)

newtype LetOutputElimM a = LetOutputElimM (ReaderT LetOutputElimState (Except LetOutputElimError) a)
    deriving (Functor, Applicative, Monad, MonadReader LetOutputElimState, MonadError LetOutputElimError)


runLetOutputElimM :: LetOutputElimM a -> Either LetOutputElimError a
runLetOutputElimM (LetOutputElimM m) = runExcept $ runReaderT m (LetOutputElimState M.empty)


instance MonadOutputElim LetOutputElimM where
    withOutputVar n v m = do
        local (\s -> s { outputVars = M.insert n v (outputVars s) }) m
    getOutputVar n = do
        vars <- asks outputVars
        return $ M.lookup n vars

    throwWithCtx s = throwError $ LetOutputElimError s
    guardWithCtx b s = unless b $ throwWithCtx s
    


eliminateLetOutput :: Program String ValueType -> Either LetOutputElimError (Program String ValueType)
eliminateLetOutput p = runLetOutputElimM $ eliminateLetOutputM p

eliminateLetOutputM :: (MonadOutputElim m) => 
                       Program String ValueType -> m (Program String ValueType)
eliminateLetOutputM (Program fs m) = Program <$> mapM eliminateLetOutputFunM fs <*> pure m

eliminateLetOutputFunM :: (MonadOutputElim m) => 
                          StmtFun String ValueType -> m (StmtFun String ValueType)
eliminateLetOutputFunM (StmtFun n args s t) = StmtFun n args <$> (eliminateLetOutputStmtM s) <*> pure t

eliminateLetOutputStmtM :: (MonadOutputElim m) => 
                           Stmt String ValueType -> m (Stmt String ValueType)
eliminateLetOutputStmtM (SLetOutput (n, t) e s t') = do
    e' <- eliminateLetOutputOExprM e
    withOutputVar n e' $ do
        s' <- eliminateLetOutputStmtM s
        return s'
eliminateLetOutputStmtM (SIf b s1 s2 t) = SIf b <$> eliminateLetOutputStmtM s1 <*> eliminateLetOutputStmtM s2 <*> pure t
eliminateLetOutputStmtM (SYield o t) = SYield <$> eliminateLetOutputOExprM o <*> pure t
eliminateLetOutputStmtM (SOReturn o t) = SOReturn <$> eliminateLetOutputOExprM o <*> pure t
eliminateLetOutputStmtM (SBReturn b t) = SBReturn <$> eliminateLetOutputBExprM b <*> pure t
eliminateLetOutputStmtM (SLetBoolean v s t) = SLetBoolean v <$> eliminateLetOutputStmtM s <*> pure t
eliminateLetOutputStmtM (SSetTrue v t) = return $ SSetTrue v t
eliminateLetOutputStmtM (SFor (i, v, t) o s t') = SFor (i, v, t) <$> eliminateLetOutputOExprM o <*> eliminateLetOutputStmtM s <*> pure t'
eliminateLetOutputStmtM (SSeq ss t) = SSeq <$> mapM eliminateLetOutputStmtM ss <*> pure t

eliminateLetOutputOExprM :: (MonadOutputElim m) => 
                            OExpr String ValueType -> m (OExpr String ValueType)
eliminateLetOutputOExprM (OVar v t) = do
    mv <- getOutputVar v
    case mv of
        Just e  -> return e
        Nothing -> return $ OVar v t
eliminateLetOutputOExprM (OConst c t) = return $ OConst c t
eliminateLetOutputOExprM (OList es t) = OList <$> mapM eliminateLetOutputOExprM es <*> pure t
eliminateLetOutputOExprM (ORev e t) = ORev <$> eliminateLetOutputOExprM e <*> pure t
eliminateLetOutputOExprM (OIndex e p t) = OIndex <$> eliminateLetOutputOExprM e <*> pure p <*> pure t
eliminateLetOutputOExprM (OApp f args t) = OApp f <$> mapM (\(e, t) -> flip (,) t <$> eliminateLetOutputOExprM e) args <*> pure t
eliminateLetOutputOExprM (OGen s t) = OGen <$> eliminateLetOutputStmtM s <*> pure t

eliminateLetOutputBExprM :: (MonadOutputElim m) => 
                            BExpr String ValueType -> m (BExpr String ValueType)
eliminateLetOutputBExprM (BConst b t) = return $ BConst b t
eliminateLetOutputBExprM (BNot b t) = BNot <$> eliminateLetOutputBExprM b <*> pure t
eliminateLetOutputBExprM (BOp op b1 b2 t) = BOp op <$> eliminateLetOutputBExprM b1 <*> eliminateLetOutputBExprM b2 <*> pure t
eliminateLetOutputBExprM (BComp op e1 e2 t) = return $ BComp op e1 e2 t
eliminateLetOutputBExprM (BVar v t) = return $ BVar v t
eliminateLetOutputBExprM (BGen s t) = BGen <$> eliminateLetOutputStmtM s <*> pure t
eliminateLetOutputBExprM (BApp f args t) = BApp f <$> mapM (\(e, t) -> flip (,) t <$> eliminateLetOutputOExprM e) args <*> pure t
eliminateLetOutputBExprM (BLitEq t c o t') = BLitEq t c <$> eliminateLetOutputOExprM o <*> pure t'


    



