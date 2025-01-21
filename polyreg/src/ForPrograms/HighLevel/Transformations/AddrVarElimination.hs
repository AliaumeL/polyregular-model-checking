{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
module ForPrograms.HighLevel.Transformations.AddrVarElimination --(StmtZip(..), ExtVars(..), eliminateExtVarsProg)
where

-- In this module, we expand for loops
-- on generators, so that the *only* for loops
-- that exist are on variables or reverse variables.

import Logic.QuantifierFree
import ForPrograms.HighLevel
import ForPrograms.HighLevel.Typing

-- addresses in generator expressions
data StmtZip v t = 
                 ZIfL (StmtZip v t )
               | ZIfR (StmtZip v t )
               | ZFor Direction v t (StmtZip v t)
               | ZSeq Int Int (StmtZip v t ) 
               | ZBegin
               deriving (Show, Eq, Functor, Foldable, Traversable)


mapVariablesZip :: (a -> b) -> StmtZip a t -> StmtZip b t 
mapVariablesZip f (ZIfL x) = ZIfL (mapVariablesZip f x)
mapVariablesZip f (ZIfR x) = ZIfR (mapVariablesZip f x)
mapVariablesZip f (ZSeq a b x) = ZSeq a b (mapVariablesZip f x)
mapVariablesZip f (ZFor dir n t x) = ZFor dir (f n) t (mapVariablesZip f x)
mapVariablesZip _ ZBegin = ZBegin

mapVariablesZipM :: (Monad m) => (a -> m b) -> StmtZip a t -> m (StmtZip b t)
mapVariablesZipM f (ZIfL x) = ZIfL <$> (mapVariablesZipM f x)
mapVariablesZipM f (ZIfR x) = ZIfR <$> (mapVariablesZipM f x)
mapVariablesZipM f (ZSeq a b x) = ZSeq a b <$> (mapVariablesZipM f x)
mapVariablesZipM f (ZFor dir n t x) = do
    n' <- f n
    x' <- mapVariablesZipM f x
    return $ ZFor dir n' t x'
mapVariablesZipM _ ZBegin = return ZBegin

reverseStmtZip :: StmtZip v t -> StmtZip v t
reverseStmtZip x = reverseStmtZip' x ZBegin
 where 
    reverseStmtZip' :: StmtZip v t -> StmtZip v t -> StmtZip v t
    reverseStmtZip' (ZIfL a) b = reverseStmtZip' a (ZIfL b)
    reverseStmtZip' (ZIfR a) b = reverseStmtZip' a (ZIfR b)
    reverseStmtZip' (ZFor dir v t a) b = reverseStmtZip' a (ZFor dir v t b)
    reverseStmtZip' (ZSeq i l a) b = reverseStmtZip' a (ZSeq i l b)
    reverseStmtZip' ZBegin b = b
    
data ExtVars v t = OldVar v | AddrVar (StmtZip v t) | AddrRevVar (StmtZip v t)
    deriving (Show, Eq, Functor, Foldable, Traversable)

makeNonReverse :: StmtZip v t -> StmtZip v t
makeNonReverse (ZIfL a) = ZIfL (makeNonReverse a)
makeNonReverse (ZIfR a) = ZIfR (makeNonReverse a)
makeNonReverse (ZFor dir v t a) = ZFor dir v t (makeNonReverse a)
makeNonReverse (ZSeq i j a) = ZSeq (j-i) j (makeNonReverse a)
makeNonReverse ZBegin = ZBegin

compareEqZip  :: t -> StmtZip v t -> StmtZip v t -> BExpr v t
compareEqZip t (ZFor _ v _ a) (ZFor _ v' _ b) = BOp Conj veqv' (compareEqZip t a b) t
    where
        veqv' = BComp Eq (PVar v t) (PVar v' t) t
compareEqZip t (ZIfL a) x = compareEqZip t (ZSeq 0 1 a) x
compareEqZip t (ZIfR a) x = compareEqZip t (ZSeq 1 1 a) x
compareEqZip t x (ZIfL a) = compareEqZip t x (ZSeq 0 1 a)
compareEqZip t x (ZIfR a) = compareEqZip t x (ZSeq 1 1 a)
compareEqZip t (ZSeq i _ a) (ZSeq j _ b) | i == j = compareEqZip t a b
compareEqZip t ZBegin ZBegin = BConst True t
compareEqZip t _ _ = BConst False t

compareLeZip :: t -> StmtZip v t -> StmtZip v t -> BExpr v t
compareLeZip t (ZFor Forward v _ a) (ZFor Forward v' _ b) = BOp Disj smallerAfter smallerNow t
    where
        smallerAfter = BOp Conj veqv' (compareLeZip t a b) t
        veqv' = BComp Eq (PVar v t) (PVar v' t) t
        smallerNow = BComp Lt (PVar v t) (PVar v' t) t
compareLeZip t (ZFor Backward v _ a) (ZFor Backward v' _ b) = BOp Disj smallerAfter smallerNow t
    where
        smallerAfter = BOp Conj veqv' (compareLeZip t a b) t
        veqv' = BComp Eq (PVar v t) (PVar v' t) t
        smallerNow = BComp Gt (PVar v t) (PVar v' t) t
compareLeZip t (ZFor _ _ _ _) (ZFor _ _ _ _) = error $ "compareLeZip: incompatible directions"
compareLeZip t (ZIfL a) x = compareLeZip t (ZSeq 0 1 a) x
compareLeZip t (ZIfR a) x = compareLeZip t (ZSeq 1 1 a) x
compareLeZip t x (ZIfL a) = compareLeZip t x (ZSeq 0 1 a)
compareLeZip t x (ZIfR a) = compareLeZip t x (ZSeq 1 1 a)
compareLeZip t (ZSeq i _ a) (ZSeq j _ b) | i == j = compareLeZip t a b
compareLeZip t (ZSeq i _ a) (ZSeq j _ b) | i < j  = BConst True t
compareLeZip t _ _ = BConst False t



eliminateExtVarsProg :: (Show v, Show t) => Program (ExtVars v t) t -> Program v t
eliminateExtVarsProg (Program fs (OldVar m)) = Program (map eliminateExtVarsFun fs) m

eliminateExtVarsFun :: (Show v, Show t) => StmtFun (ExtVars v t) t -> StmtFun v t
eliminateExtVarsFun (StmtFun (OldVar n) args s t) = StmtFun n args' (eliminateExtVarsStmt s) t
    where
        args' = map (\(v, t, ps) -> (eliminateExtVarsVar v, t, map eliminateExtVarsVar ps)) args
eliminateExtVarsFun x = error $ "eliminateExtVarsFun: invalid function" ++ show x

eliminateExtVarsVar :: (Show v, Show t) => ExtVars v t -> v
eliminateExtVarsVar (OldVar v) = v
eliminateExtVarsVar (AddrVar _) = error "AddrVar in eliminateExtVarsVar"

eliminateExtVarsStmt :: (Show v, Show t) => Stmt (ExtVars v t) t -> Stmt v t
eliminateExtVarsStmt (SYield o t) = SYield (eliminateExtVarsOExpr o) t
eliminateExtVarsStmt (SOReturn o t) = SOReturn (eliminateExtVarsOExpr o) t
eliminateExtVarsStmt (SBReturn b t) = SBReturn (eliminateExtVarsBExpr b) t
eliminateExtVarsStmt (SIf b s1 s2 t) = SIf (eliminateExtVarsBExpr b) (eliminateExtVarsStmt s1) (eliminateExtVarsStmt s2) t
eliminateExtVarsStmt (SLetOutput (OldVar v, t) e s t') = SLetOutput (v, t) (eliminateExtVarsOExpr e) (eliminateExtVarsStmt s) t'
eliminateExtVarsStmt (SLetBoolean (OldVar v) s t) = SLetBoolean v (eliminateExtVarsStmt s) t
eliminateExtVarsStmt (SSetTrue (OldVar v) t) = SSetTrue v t
eliminateExtVarsStmt (SFor dir (OldVar i, OldVar e, t) o s t') = SFor dir (i, e, t) (eliminateExtVarsOExpr o) (eliminateExtVarsStmt s) t'
eliminateExtVarsStmt (SSeq ss t) = SSeq (map eliminateExtVarsStmt ss) t
eliminateExtVarsStmt x = error $ "eliminateExtVarsStmt: invalid statement" ++ show x


eliminateExtVarsBExpr :: (Show v, Show t) => BExpr (ExtVars v t) t -> BExpr v t
eliminateExtVarsBExpr (BComp op (PVar (AddrVar p1) t1) (PVar (AddrVar p2) t2) t) = opToFunc t op p1 p2
    where
        opToFunc :: (Show v, Show t) => t -> TestOp -> StmtZip v t -> StmtZip v t -> BExpr v t
        opToFunc t Eq  a b = compareEqZip t a b
        opToFunc t Lt  a b = compareLeZip t a b
        opToFunc t Le  a b = BOp Disj (compareEqZip t a b) (compareLeZip t a b) t
        opToFunc t Gt  a b = BNot (opToFunc t Le a b) t
        opToFunc t Ge  a b = BNot (opToFunc t Lt a b) t
eliminateExtVarsBExpr (BComp op (PVar (AddrRevVar p1) t1) (PVar (AddrRevVar p2) t2) t) = 
    eliminateExtVarsBExpr (BComp op (PVar (AddrVar (makeNonReverse p1)) t1) (PVar (AddrVar (makeNonReverse p2)) t2) t)
eliminateExtVarsBExpr (BComp op (PVar (AddrRevVar p1) t1) (PVar (AddrVar p2) t2) t) = 
    eliminateExtVarsBExpr (BComp op (PVar (AddrVar (makeNonReverse p1)) t1) (PVar (AddrVar p2) t2) t)
eliminateExtVarsBExpr (BComp op (PVar (AddrVar p1) t1) (PVar (AddrRevVar p2) t2) t) = 
    eliminateExtVarsBExpr (BComp op (PVar (AddrVar p1) t1) (PVar (AddrVar (makeNonReverse p2)) t2) t)
    
eliminateExtVarsBExpr (BComp op (PVar (OldVar v) t) (PVar (OldVar v') t') t'') = BComp op (PVar v t) (PVar v' t') t''
eliminateExtVarsBExpr s@(BComp _ _ _ _) =  error $ "BComp incompatible values in eliminateExtVarsBExpr" ++ show s
eliminateExtVarsBExpr (BConst b t) = BConst b t
eliminateExtVarsBExpr (BNot b t) = BNot (eliminateExtVarsBExpr b) t
eliminateExtVarsBExpr (BOp op b1 b2 t) = BOp op (eliminateExtVarsBExpr b1) (eliminateExtVarsBExpr b2) t
eliminateExtVarsBExpr (BVar (OldVar v) t) = BVar v t
eliminateExtVarsBExpr (BGen _ _) = error "BGen in eliminateExtVarsBExpr"
eliminateExtVarsBExpr (BApp _ _ _) = error "BApp in eliminateExtVarsBExpr"
eliminateExtVarsBExpr (BLitEq t c o t') = BLitEq t (eliminateExtVarsCExpr c) (eliminateExtVarsOExpr o) t'

eliminateExtVarsOExpr :: (Show v, Show t) => OExpr (ExtVars v t) t -> OExpr v t
eliminateExtVarsOExpr (OVar (OldVar v) t) = OVar v t
eliminateExtVarsOExpr (OConst c t) = OConst (eliminateExtVarsCExpr c) t
eliminateExtVarsOExpr (OList os t) = OList (map eliminateExtVarsOExpr os) t
eliminateExtVarsOExpr (OApp _ _ _) = error "OApp in eliminateExtVarsOExpr"
eliminateExtVarsOExpr (OGen s t) = OGen (eliminateExtVarsStmt s) t
eliminateExtVarsOExpr x = error $ "eliminateExtVarsOExpr: invalid expression" ++ show x

eliminateExtVarsPEpxr :: (Show v, Show t) => PExpr (ExtVars v t) t -> PExpr v t
eliminateExtVarsPEpxr (PVar (OldVar v) t) = PVar v t
eliminateExtVarsPEpxr (PVar (AddrVar p) t) =  error "PVar AddrVar in eliminateExtVarsPEpxr"

eliminateExtVarsCExpr :: (Show v, Show t) => CExpr (ExtVars v t) t -> CExpr v t
eliminateExtVarsCExpr (CChar c t) = CChar c t
eliminateExtVarsCExpr (CList cs t) = CList (map eliminateExtVarsCExpr cs) t

