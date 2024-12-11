{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module ReductionLitEq (removeBLitEq, hasLitEq)
where

import ForPrograms
import ForProgramsTyping

import Control.Monad.State

-- This module removes literal equality
-- of the form (BLitEq (CExpr v t) (OExpr v t) t)
-- whenever the CExpr is *not* a character literal
--

-- First, we create a function that tests whether
-- BLitEq is inside a program and involves a non character

hasLitEq :: Program String t -> Bool
hasLitEq (Program funcs m) = any hasLitEqStmtFun funcs

hasLitEqStmtFun :: StmtFun String t -> Bool
hasLitEqStmtFun (StmtFun _ _ stmt _) = hasLitEqStmt stmt

hasLitEqStmt :: Stmt String t -> Bool
hasLitEqStmt (SYield o _) = hasLitEqOExpr o
hasLitEqStmt (SOReturn o _) = hasLitEqOExpr o
hasLitEqStmt (SBReturn b _) = hasLitEqBExpr b
hasLitEqStmt (SIf b s1 s2 _) = hasLitEqBExpr b || hasLitEqStmt s1 || hasLitEqStmt s2
hasLitEqStmt (SLetOutput _ o s _) = hasLitEqOExpr o || hasLitEqStmt s
hasLitEqStmt (SLetBoolean _ s _) = hasLitEqStmt s
hasLitEqStmt (SSetTrue _ _) = False
hasLitEqStmt (SFor _ v s _) = hasLitEqOExpr v || hasLitEqStmt s
hasLitEqStmt (SSeq ss _) = any hasLitEqStmt ss

-- BLitEq with a constant char is ok, everything else is not
hasLitEqBExpr :: BExpr String t -> Bool
hasLitEqBExpr (BLitEq _ (CChar _ _) _ _) = False
hasLitEqBExpr (BLitEq _ _ _ _) = True
hasLitEqBExpr (BConst _ _) = False
hasLitEqBExpr (BNot b _) = hasLitEqBExpr b
hasLitEqBExpr (BOp _ b1 b2 _) = hasLitEqBExpr b1 || hasLitEqBExpr b2
hasLitEqBExpr (BComp _ p1 p2 _) = False
hasLitEqBExpr (BVar _ _) = False
hasLitEqBExpr (BGen s _) = hasLitEqStmt s
hasLitEqBExpr (BApp _ oes _) = any hasLitEqOExpr . map fst $ oes
    
hasLitEqOExpr :: OExpr String t -> Bool
hasLitEqOExpr (OVar _ _) = False
hasLitEqOExpr (OConst _ _) = False
hasLitEqOExpr (OList os _) = any hasLitEqOExpr os
hasLitEqOExpr (ORev o _) = hasLitEqOExpr o
hasLitEqOExpr (OIndex o p _) = hasLitEqOExpr o
hasLitEqOExpr (OApp _ oes _) = any hasLitEqOExpr . map fst $ oes
hasLitEqOExpr (OGen s _) = hasLitEqStmt s

class (Monad m) => MonadFresh m where
    fresh :: String -> m String

type FreshM = State Int


-- replaceHashPart "a#..." 13 = "a#13"
-- replaceHashPart "abc" 123 = "abc#123"
replaceHashPart :: Int -> String -> String
replaceHashPart i s = case break (=='#') s of
    (a, '#':b) -> a ++ "#" ++ show i
    (a, b)     -> a ++ "#" ++ show i

instance MonadFresh FreshM where
    fresh s = do
        i <- get
        put (i + 1)
        return . replaceHashPart i $ s

safeLast :: [a] -> Maybe a
safeLast [] = Nothing
safeLast xs = Just $ last xs

unlitEq :: (MonadFresh m) => (CExpr String ValueType) -> (OExpr String ValueType) -> m (BExpr String ValueType)
unlitEq (CChar c t) v = pure $ BLitEq t (CChar c t) v TBool
unlitEq (CList xs (TConst (TOList t))) v = do
        let n = length xs
        vars  <- mapM (\i -> fresh ("b" ++ show i)) [0..(n-1)]
        e     <- fresh "v"
        i     <- fresh "i"
        tests <- mapM (\x -> unlitEq x (OVar e (TOutput t))) xs
        let ifs = makeIfs tests vars
        let body = SFor (i, e, (TOutput t)) v ifs TBool
        let lastVarOrTrue = case safeLast vars of
                Just x -> BVar x TBool
                Nothing -> BConst True TBool
        let returnLastVar = SBReturn lastVarOrTrue TBool
        return . (\x -> BGen x TBool) . letBooleans TBool vars $ SSeq [ body, returnLastVar ] TBool
unlitEq a b = error $ "unlitEq: incompatible arguments " ++ show a ++ " " ++ show b

-- makeIfs v cexprs bvars 
makeIfs :: [BExpr String ValueType] -> [String] -> Stmt String ValueType
makeIfs [] [] = SBReturn (BConst False TBool) TBool
makeIfs (t : ts) (b : bs) = SIf cond (SSeq trueBranch TBool) falseBranch TBool
    where
        cond = BNot (BVar b TBool) TBool
        falseBranch = makeIfs ts bs
        trueBranch = [ SSetTrue b TBool
                     , SIf (BNot t TBool)
                           (SBReturn (BConst False TBool) TBool)
                           (SSeq [] TBool)
                           TBool
                     ]
makeIfs a b = error $ "makeIfs: incompatible lists of arguments" ++ show a ++ " " ++ show b


unlitEqBExpr :: (MonadFresh m) => BExpr String ValueType -> m (BExpr String ValueType)
unlitEqBExpr (BLitEq _ c o _) = unlitEq c o
unlitEqBExpr (BConst b t) = pure $ BConst b t
unlitEqBExpr (BNot b t) = do
    b' <- unlitEqBExpr b
    return $ BNot b' t
unlitEqBExpr (BOp op b1 b2 t) = do
    b1' <- unlitEqBExpr b1
    b2' <- unlitEqBExpr b2
    return $ BOp op b1' b2' t
unlitEqBExpr (BComp comp p1 p2 t) = pure $ BComp comp p1 p2 t
unlitEqBExpr (BVar v t) = pure $ BVar v t
unlitEqBExpr (BGen stmt t) = do
    stmt' <- unlitEqStmt stmt
    return $ BGen stmt' t
unlitEqBExpr (BApp v oes t) = pure $ BApp v oes t

unlitEqOExpr :: (MonadFresh m) => OExpr String ValueType -> m (OExpr String ValueType)
unlitEqOExpr (OVar v t) = pure $ OVar v t
unlitEqOExpr (OConst c t) = pure $ OConst c t
unlitEqOExpr (OList os t) = pure $ OList os t
unlitEqOExpr (ORev o t) = pure $ ORev o t
unlitEqOExpr (OIndex o p t) = pure $ OIndex o p t
unlitEqOExpr (OApp v oes t) = pure $ OApp v oes t
unlitEqOExpr (OGen stmt t) = do
    stmt' <- unlitEqStmt stmt
    return $ OGen stmt' t

unlitEqStmt :: (MonadFresh m) => Stmt String ValueType -> m (Stmt String ValueType)
unlitEqStmt (SYield o t)   = SYield   <$> unlitEqOExpr o <*> pure t
unlitEqStmt (SOReturn o t) = SOReturn <$> unlitEqOExpr o <*> pure t
unlitEqStmt (SBReturn b t) = SBReturn <$> unlitEqBExpr b <*> pure t
unlitEqStmt (SIf b s1 s2 t) = SIf <$> unlitEqBExpr b 
                                   <*> unlitEqStmt s1 
                                   <*> unlitEqStmt s2 
                                   <*> pure t
unlitEqStmt (SLetOutput v o s t) = do
    s' <- unlitEqStmt s
    return $ SLetOutput v o s' t
unlitEqStmt (SLetBoolean v s t) = do
    s' <- unlitEqStmt s
    return $ SLetBoolean v s' t
unlitEqStmt (SSetTrue v t) = pure $ SSetTrue v t
unlitEqStmt (SFor (i, e, t) v s t') = do
    v' <- unlitEqOExpr v
    s' <- unlitEqStmt s
    return $ SFor (i, e, t) v' s' t'
unlitEqStmt (SSeq ss t) = SSeq <$> mapM unlitEqStmt ss <*> pure t

unlitEqFunction :: (MonadFresh m) => StmtFun String ValueType -> m (StmtFun String ValueType)
unlitEqFunction (StmtFun v args stmt t) = do
    stmt' <- unlitEqStmt stmt
    return $ StmtFun v args stmt' t


removeBLitEq :: Program String ValueType -> Program String ValueType
removeBLitEq (Program funcs m) = Program newFuncs' m
    where
        newFuncs :: FreshM [StmtFun String ValueType]
        newFuncs = mapM unlitEqFunction funcs

        newFuncs' :: [StmtFun String ValueType]
        newFuncs' = evalState newFuncs 0

