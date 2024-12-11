{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module ReturnElimination where

-- This module is used to remove return statements
-- from a program. This is done by using the following 
-- rules 
--
-- 1. yield { s } : Char 
--  => let mut has_returned := False in s [ return x -> if not has_returned then setTrue has_returned; yield x ]
--
-- 2. yield { s } : List τ 
--  => let mut ... in 
--     s [
--        return x -> if not has_returned then has_returned := True ; for (i, v) in x do yield v 
--        yield  x -> if not has_returned then yield x
--       ]

import ForPrograms
import ForProgramsTyping
import Control.Monad

import Control.Monad.State


retElimProgram :: Program String ValueType -> Program String ValueType
retElimProgram p = runFresh $ retElimProgramM p

class Monad m => MonadFresh m where
    fresh :: String -> m String

newtype Fresh a = Fresh (State Int a)
    deriving (Functor, Applicative, Monad, MonadState Int)

-- replaceHashPart "a#..." 13 = "a#13"
-- replaceHashPart "abc" 123 = "abc#123"
replaceHashPart :: Int -> String -> String
replaceHashPart i s = case break (=='#') s of
    (a, '#':b) -> a ++ "#ret-elim#" ++ show i
    (a, b)     -> a ++ "#ret-elim#" ++ show i

instance MonadFresh Fresh where
    fresh s = do
        i <- get
        put (i + 1)
        return $ replaceHashPart i s

runFresh :: Fresh a -> a
runFresh (Fresh m) = evalState m 0

retElimProgramM :: (MonadFresh m) => Program String ValueType -> m (Program String ValueType)
retElimProgramM (Program fs main) = Program <$> mapM retElimFuncM fs <*> pure main

retElimFuncM :: (MonadFresh m) => StmtFun String ValueType -> m (StmtFun String ValueType)
retElimFuncM (StmtFun name args s t@(TOutput TOChar)) = do
    has_returned <- fresh (name <> "_has_returned")
    let stmt' = SLetBoolean has_returned (updateReturnsChar has_returned s) t
    stmt''  <- retElimStmt stmt'
    return $ StmtFun name args stmt'' t
retElimFuncM (StmtFun name args s t@(TOutput (TOList _))) = do
    has_returned <- fresh (name <> "_has_returned")
    updated <- updateReturnsList has_returned s
    let stmt' = SLetBoolean has_returned updated t
    stmt''  <- retElimStmt stmt'
    return $ StmtFun name args stmt'' t
retElimFuncM (StmtFun name args s t) = do
    stmt'  <- retElimStmt s
    return $ StmtFun name args stmt' t



ifHasNotReturnedYield :: String -> Stmt String ValueType -> Stmt String ValueType
ifHasNotReturnedYield has_returned s = SIf (BNot (BVar has_returned TBool) TBool) s (SSeq [] t) t
    where
        t = getType s

ifHasNotReturnedRet :: String -> Stmt String ValueType -> Stmt String ValueType
ifHasNotReturnedRet has_returned s = SIf (BNot (BVar has_returned TBool) TBool) 
                                       (SSeq [s, SSetTrue has_returned t] t)
                                       (SSeq [] t)
                                       t
    where
        t = getType s

retElimStmt :: (MonadFresh m) => Stmt String ValueType -> m (Stmt String ValueType)
retElimStmt s@(SYield (OConst _ _) _) = pure s
retElimStmt s@(SYield (OVar _ _) _) = pure s
retElimStmt (SYield (OGen s (TOutput TOChar)) t) = do 
    has_returned <- fresh "has_returned"
    return $ SLetBoolean has_returned (updateReturnsChar has_returned s) t
retElimStmt (SYield (OGen s (TOutput (TOList _))) t) = do
    has_returned <- fresh "has_returned"
    updated <- updateReturnsList has_returned s
    return $ SLetBoolean has_returned updated t
retElimStmt (SYield x _) = error $ "(retElimStmt)qInvalid type for yield" ++ show x
retElimStmt (SIf b s1 s2 t) = SIf b <$> (retElimStmt s1) <*> (retElimStmt s2) <*> pure t
retElimStmt (SOReturn x t) = error $ "SOReturn ret" ++ show x --  SOReturn <$> (retElimOExpr x) <*> pure t
retElimStmt (SBReturn x t) = pure $ SBReturn x t
retElimStmt (SLetOutput v x s t) = SLetOutput v <$> (retElimOExpr x) <*> (retElimStmt s) <*> pure t
retElimStmt (SLetBoolean x s t) = SLetBoolean x <$> (retElimStmt s) <*> pure t
retElimStmt (SSetTrue x t) = pure $ SSetTrue x t
retElimStmt (SFor dir (v1, v2, t) x s t') = SFor dir (v1, v2, t) <$> (retElimOExpr x) <*> (retElimStmt s) <*> pure t'
retElimStmt (SSeq ss t) = SSeq <$> (mapM retElimStmt ss) <*> pure t

retElimOExpr :: (MonadFresh m) => OExpr String ValueType -> m (OExpr String ValueType)
retElimOExpr (OVar x t) = pure $ OVar x t
retElimOExpr (OConst c t) = pure $ OConst c t
retElimOExpr (OList xs t) = OList <$> (mapM retElimOExpr xs) <*> pure t
retElimOExpr (OApp x xs t) = OApp x <$> (mapM (\(x, ys) -> (,) <$> (retElimOExpr x) <*> pure ys) xs) <*> pure t
retElimOExpr (OGen s (TOutput TOChar)) = do
    has_returned <- fresh "g-has_returned"
    let stmt' = updateReturnsChar has_returned s
    stmt'' <- retElimStmt stmt'
    let new_stmt = SLetBoolean has_returned stmt'' (TOutput TOChar)
    return $ OGen new_stmt (TOutput TOChar)
retElimOExpr (OGen s (TOutput (TOList t))) = do
    has_returned <- fresh "g-has_returned"
    stmt' <- updateReturnsList has_returned s
    stmt'' <- retElimStmt stmt'
    let new_stmt = SLetBoolean has_returned stmt'' (TOutput (TOList t))
    return $ OGen new_stmt (TOutput (TOList t))
retElimOExpr (OGen s t) = error $ "Invalid type for generator" ++ show s ++ " " ++ show t


-- this function substitutes the return statements with the appropriate
-- code to handle the return statements
updateReturnsChar :: String -> Stmt String ValueType -> Stmt String ValueType
updateReturnsChar has_returned s@(SYield _ _) = error $ "(updateReturnsChar) Invalid type for yield" ++ show s
updateReturnsChar has_returned (SOReturn o t) = ifHasNotReturnedRet has_returned (SYield o t)
updateReturnsChar has_returned (SIf b s1 s2 t) = SIf b (updateReturnsChar has_returned s1) (updateReturnsChar has_returned s2) t
updateReturnsChar has_returned (SLetOutput v x s t) = SLetOutput v x (updateReturnsChar has_returned s) t
updateReturnsChar has_returned (SLetBoolean v s t) = SLetBoolean v (updateReturnsChar has_returned s) t
updateReturnsChar has_returned (SSetTrue v t) = SSetTrue v t
updateReturnsChar has_returned (SFor dir (v1, v2, t) x s t') = SFor dir (v1, v2, t) x (updateReturnsChar has_returned s) t'
updateReturnsChar has_returned (SSeq ss t) = SSeq (map (updateReturnsChar has_returned) ss) t
updateReturnsChar has_returned (SBReturn x t) = SBReturn x t


updateReturnsList :: (MonadFresh m) => String -> Stmt String ValueType -> m (Stmt String ValueType)
updateReturnsList has_returned s@(SYield _ _) = pure $ ifHasNotReturnedYield has_returned s
updateReturnsList has_returned (SOReturn o t@(TOutput (TOList tinside))) = do
    i <- fresh "i-return"
    v <- fresh "v-return"
    let it = TOutput tinside
    let s = SFor Forward (i, v, it) o (SYield (OVar v it) t) t
    pure $ ifHasNotReturnedRet has_returned s
updateReturnsList has_returned (SOReturn o t) = error $ "SO return List " ++ show o 
updateReturnsList has_returned (SBReturn x t) = pure $ SBReturn x t
updateReturnsList has_returned (SIf b s1 s2 t) = SIf b <$> (updateReturnsList has_returned s1) <*> (updateReturnsList has_returned s2) <*> pure t
updateReturnsList has_returned (SLetOutput v x s t) = SLetOutput v x <$> (updateReturnsList has_returned s) <*> pure t
updateReturnsList has_returned (SLetBoolean v s t) = SLetBoolean v <$> (updateReturnsList has_returned s) <*> pure t
updateReturnsList has_returned (SSetTrue v t) = pure $ SSetTrue v t
updateReturnsList has_returned (SFor dir (v1, v2, t) x s t') = SFor dir (v1, v2, t) x <$> (updateReturnsList has_returned s) <*> pure t'
updateReturnsList has_returned (SSeq ss t) = SSeq <$> (mapM (updateReturnsList has_returned) ss) <*> pure t



