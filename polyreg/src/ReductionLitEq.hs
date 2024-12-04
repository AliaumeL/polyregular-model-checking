{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module ReductionLitEq where

import ForPrograms

import Control.Monad.State

-- This module removes literal equality
-- of the form (BLitEq (CExpr v t) (OExpr v t) t)
-- whenever the CExpr is *not* a character literal

class (Monad m) => MonadFresh m where
    fresh :: String -> m String

type FreshM = State Int

instance MonadFresh FreshM where
    fresh s = do
        i <- get
        put (i + 1)
        return $ s ++ "#" ++ show i

unlitEq :: (MonadFresh m) => (CExpr String ()) -> (OExpr String ()) -> m (BExpr String ())
unlitEq (CChar c _) v = pure $ BLitEq (CChar c ()) v ()
unlitEq (CUnit _) v = unlitEq (CList [] ()) v
unlitEq (CList xs _) v = do
        let n = length xs
        vars  <- mapM (\i -> fresh ("b" ++ show i)) [0..n+1]
        e     <- fresh "v"
        i     <- fresh "i"
        tests <- mapM (\x -> unlitEq x (OVar e ())) xs
        let ifs = makeIfs tests vars
        let body = SFor (i, e) v ifs ()
        return . (\x -> BGen x ()) . letBooleans vars $ SSeq [ body, SBReturn (BConst True ()) () ] ()

-- makeIfs v cexprs bvars 
makeIfs :: [BExpr String ()] -> [String] -> Stmt String ()
makeIfs [] [b] = SIf cond truePart falsePart ()
    where 
        cond = BNot (BVar b ()) ()
        truePart  = SSetTrue b ()
        falsePart = SBReturn (BConst False ()) ()
makeIfs (t : ts) (b : bs) = SIf cond (SSeq trueBranch ()) falseBranch ()
    where
        cond = BNot (BVar b ()) ()
        falseBranch = makeIfs ts bs
        trueBranch = [ SSetTrue b ()
                     , SIf (BNot t ())
                           (SBReturn (BConst False ()) ())
                           (SSeq [] ())
                           ()
                     ]
makeIfs _ _ = error "makeIfs: incompatible lists of arguments"


unlitEqBExpr :: (MonadFresh m) => BExpr String () -> m (BExpr String ())
unlitEqBExpr (BLitEq c o ()) = unlitEq c o
unlitEqBExpr (BConst b ()) = pure $ BConst b ()
unlitEqBExpr (BNot b ()) = do
    b' <- unlitEqBExpr b
    return $ BNot b' ()
unlitEqBExpr (BOp op b1 b2 ()) = do
    b1' <- unlitEqBExpr b1
    b2' <- unlitEqBExpr b2
    return $ BOp op b1' b2' ()
unlitEqBExpr (BComp comp p1 p2 ()) = pure $ BComp comp p1 p2 ()
unlitEqBExpr (BVar v ()) = pure $ BVar v ()
unlitEqBExpr (BGen stmt ()) = do
    stmt' <- unlitEqStmt stmt
    return $ BGen stmt' ()
unlitEqBExpr (BApp v oes ()) = pure $ BApp v oes ()

unlitEqOExpr :: (MonadFresh m) => OExpr String () -> m (OExpr String ())
unlitEqOExpr (OVar v ()) = pure $ OVar v ()
unlitEqOExpr (OConst c ()) = pure $ OConst c ()
unlitEqOExpr (OList os ()) = pure $ OList os ()
unlitEqOExpr (ORev o ()) = pure $ ORev o ()
unlitEqOExpr (OIndex o p ()) = pure $ OIndex o p ()
unlitEqOExpr (OApp v oes ()) = pure $ OApp v oes ()
unlitEqOExpr (OGen stmt ()) = do
    stmt' <- unlitEqStmt stmt
    return $ OGen stmt' ()

unlitEqStmt :: (MonadFresh m) => Stmt String () -> m (Stmt String ())
unlitEqStmt (SYield o ())   = SYield   <$> unlitEqOExpr o <*> pure ()
unlitEqStmt (SOReturn o ()) = SOReturn <$> unlitEqOExpr o <*> pure ()
unlitEqStmt (SBReturn b ()) = SBReturn <$> unlitEqBExpr b <*> pure ()
unlitEqStmt (SIf b s1 s2 ()) = SIf <$> unlitEqBExpr b 
                                   <*> unlitEqStmt s1 
                                   <*> unlitEqStmt s2 
                                   <*> pure ()
unlitEqStmt (SLetOutput v o s ()) = do
    s' <- unlitEqStmt s
    return $ SLetOutput v o s' ()
unlitEqStmt (SLetBoolean v s ()) = do
    s' <- unlitEqStmt s
    return $ SLetBoolean v s' ()
unlitEqStmt (SSetTrue v ()) = pure $ SSetTrue v ()
unlitEqStmt (SFor (i, e) v s ()) = do
    v' <- unlitEqOExpr v
    s' <- unlitEqStmt s
    return $ SFor (i, e) v' s' ()
unlitEqStmt (SSeq ss ()) = SSeq <$> mapM unlitEqStmt ss <*> pure ()

unlitEqFunction :: (MonadFresh m) => StmtFun String () -> m (StmtFun String ())
unlitEqFunction (StmtFun v args stmt ()) = do
    stmt' <- unlitEqStmt stmt
    return $ StmtFun v args stmt' ()


unlitEqProgram :: UProgram -> UProgram
unlitEqProgram (Program funcs m) = Program newFuncs' m
    where
        newFuncs :: FreshM [StmtFun String ()]
        newFuncs = mapM unlitEqFunction funcs

        newFuncs' :: [StmtFun String ()]
        newFuncs' = evalState newFuncs 0

