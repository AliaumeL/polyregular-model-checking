{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
module AddrVarElimination --(StmtZip(..), ExtVars(..), eliminateExtVarsProg)
where

-- In this module, we expand for loops
-- on generators, so that the *only* for loops
-- that exist are on variables or reverse variables.

import QuantifierFree
import ForPrograms
import ForProgramsTyping

-- addresses in generator expressions
data StmtZip v t = 
                 ZIfL (StmtZip v t )
               | ZIfR (StmtZip v t )
               | ZFor v t (StmtZip v t)
               | ZSeq Int (StmtZip v t ) 
               | ZBegin
               deriving (Show, Eq, Functor, Foldable, Traversable)

reverseStmtZip :: StmtZip v t -> StmtZip v t
reverseStmtZip x = reverseStmtZip' x ZBegin
 where 
    reverseStmtZip' :: StmtZip v t -> StmtZip v t -> StmtZip v t
    reverseStmtZip' (ZIfL a) b = reverseStmtZip' a (ZIfL b)
    reverseStmtZip' (ZIfR a) b = reverseStmtZip' a (ZIfR b)
    reverseStmtZip' (ZFor v t a) b = reverseStmtZip' a (ZFor v t b)
    reverseStmtZip' (ZSeq i a) b = reverseStmtZip' a (ZSeq i b)
    reverseStmtZip' ZBegin b = b
    
data ExtVars v t = OldVar v | AddrVar v (StmtZip v t) 
    deriving (Show, Eq, Functor, Foldable, Traversable)

compareEqZip  :: t -> StmtZip v t -> StmtZip v t -> BExpr v t
compareEqZip t (ZFor v _ a) (ZFor v' _ b) = BOp Conj veqv' (compareEqZip t a b) t
    where
        veqv' = BComp Eq (PVar v t) (PVar v' t) t
compareEqZip t (ZIfL a) x = compareEqZip t (ZSeq 0 a) x
compareEqZip t (ZIfR a) x = compareEqZip t (ZSeq 1 a) x
compareEqZip t x (ZIfL a) = compareEqZip t x (ZSeq 0 a)
compareEqZip t x (ZIfR a) = compareEqZip t x (ZSeq 1 a)
compareEqZip t (ZSeq i a) (ZSeq j b) | i == j = compareEqZip t a b
compareEqZip t ZBegin ZBegin = BConst True t
compareEqZip t _ _ = BConst False t

compareLeZip :: t -> StmtZip v t -> StmtZip v t -> BExpr v t
compareLeZip t (ZFor v _ a) (ZFor v' _ b) = BOp Disj smallerAfter smallerNow t
    where
        smallerAfter = BOp Conj veqv' (compareLeZip t a b) t
        veqv' = BComp Eq (PVar v t) (PVar v' t) t
        smallerNow = BComp Lt (PVar v t) (PVar v' t) t
compareLeZip t (ZIfL a) x = compareLeZip t (ZSeq 0 a) x
compareLeZip t (ZIfR a) x = compareLeZip t (ZSeq 1 a) x
compareLeZip t x (ZIfL a) = compareLeZip t x (ZSeq 0 a)
compareLeZip t x (ZIfR a) = compareLeZip t x (ZSeq 1 a)
compareLeZip t (ZSeq i a) (ZSeq j b) | i == j = compareLeZip t a b
compareLeZip t (ZSeq i a) (ZSeq j b) | i < j  = BConst True t
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
eliminateExtVarsVar (AddrVar v _) = error "AddrVar in eliminateExtVarsVar"

eliminateExtVarsStmt :: (Show v, Show t) => Stmt (ExtVars v t) t -> Stmt v t
eliminateExtVarsStmt (SYield o t) = SYield (eliminateExtVarsOExpr o) t
eliminateExtVarsStmt (SOReturn o t) = SOReturn (eliminateExtVarsOExpr o) t
eliminateExtVarsStmt (SBReturn b t) = SBReturn (eliminateExtVarsBExpr b) t
eliminateExtVarsStmt (SIf b s1 s2 t) = SIf (eliminateExtVarsBExpr b) (eliminateExtVarsStmt s1) (eliminateExtVarsStmt s2) t
eliminateExtVarsStmt (SLetOutput (OldVar v, t) e s t') = SLetOutput (v, t) (eliminateExtVarsOExpr e) (eliminateExtVarsStmt s) t'
eliminateExtVarsStmt (SLetBoolean (OldVar v) s t) = SLetBoolean v (eliminateExtVarsStmt s) t
eliminateExtVarsStmt (SSetTrue (OldVar v) t) = SSetTrue v t
eliminateExtVarsStmt (SFor (OldVar i, OldVar e, t) o s t') = SFor (i, e, t) (eliminateExtVarsOExpr o) (eliminateExtVarsStmt s) t'
eliminateExtVarsStmt (SFor (OldVar i, OldVar e, t) o s t') = SFor (i, e, t) (eliminateExtVarsOExpr o) (eliminateExtVarsStmt s) t'
eliminateExtVarsStmt (SSeq ss t) = SSeq (map eliminateExtVarsStmt ss) t
eliminateExtVarsStmt x = error $ "eliminateExtVarsStmt: invalid statement" ++ show x


eliminateExtVarsBExpr :: (Show v, Show t) => BExpr (ExtVars v t) t -> BExpr v t
eliminateExtVarsBExpr (BComp op (PVar (AddrVar _ p1) t1) (PVar (AddrVar _ p2) t2) t) = opToFunc t op p1 p2
    where
        opToFunc :: (Show v, Show t) => t -> TestOp -> StmtZip v t -> StmtZip v t -> BExpr v t
        opToFunc t Eq  a b = compareEqZip t a b
        opToFunc t Lt  a b = compareLeZip t a b
        opToFunc t Le  a b = BOp Disj (compareEqZip t a b) (compareLeZip t a b) t
        opToFunc t Gt  a b = BNot (opToFunc t Le a b) t
        opToFunc t Ge  a b = BNot (opToFunc t Lt a b) t
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
eliminateExtVarsOExpr (ORev o t) = ORev (eliminateExtVarsOExpr o) t
eliminateExtVarsOExpr (OConst c t) = OConst (eliminateExtVarsCExpr c) t
eliminateExtVarsOExpr (OList os t) = OList (map eliminateExtVarsOExpr os) t
eliminateExtVarsOExpr (OIndex o p t) = OIndex (eliminateExtVarsOExpr o) (eliminateExtVarsPEpxr p) t
eliminateExtVarsOExpr (OApp _ _ _) = error "OApp in eliminateExtVarsOExpr"
eliminateExtVarsOExpr (OGen s t) = OGen (eliminateExtVarsStmt s) t
eliminateExtVarsOExpr x = error $ "eliminateExtVarsOExpr: invalid expression" ++ show x

eliminateExtVarsPEpxr :: (Show v, Show t) => PExpr (ExtVars v t) t -> PExpr v t
eliminateExtVarsPEpxr (PVar (OldVar v) t) = PVar v t
eliminateExtVarsPEpxr (PVar (AddrVar v p) t) =  error "PVar AddrVar in eliminateExtVarsPEpxr"

eliminateExtVarsCExpr :: (Show v, Show t) => CExpr (ExtVars v t) t -> CExpr v t
eliminateExtVarsCExpr (CChar c t) = CChar c t
eliminateExtVarsCExpr (CList cs t) = CList (map eliminateExtVarsCExpr cs) t

