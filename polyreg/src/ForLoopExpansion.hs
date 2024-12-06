{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
module ForLoopExpansion where

-- In this module, we expand for loops
-- on generators, so that the *only* for loops
-- that exist are on variables or reverse variables.

import ForPrograms
import ForProgramsTyping

import Control.Monad
import Control.Monad.Except

import Data.Map (Map)
import qualified Data.Map as M



data StmtZip v t = ZIfL (StmtZip v t )
               | ZIfR (StmtZip v t )
               | ZLetBoolean (StmtZip v t )
               | ZFor v t (StmtZip v t )
               | ZSeqL Int (StmtZip v t ) 
               | ZBegin
               deriving (Show, Eq, Functor, Foldable, Traversable)


compareZip :: t -> StmtZip v t -> StmtZip v t -> BExpr (ExtVars v t) t
compareZip t (ZIfL a) (ZIfL b) = compareZip t a b
compareZip t (ZIfR a) (ZIfR b) = compareZip t a b
compareZip t (ZIfL a) (ZIfR b) = BConst True t
compareZip t (ZIfR a) (ZIfL b) = BConst False t
compareZip t (ZLetBoolean a) (ZLetBoolean b) = compareZip t a b
compareZip t (ZFor v t' a) (ZFor v' t'' b) = BOp And 
                                              (BComp Leq (PVar (OldVar v) t') 
                                                         (PVar (OldVar v') t'') 
                                                      t)
                                              (compareZip t a b)
                                              t
compareZip t (ZSeqL i a) (ZSeqL j b) | i == j = compareZip t a b
compareZip t (ZSeqL i a) (ZSeqL j b) | i <  i = BConst True t
compareZip t (ZSeqL i a) (ZSeqL j b) | i >  i = BConst False t
compareZip t ZBegin ZBegin = BConst True t
compareZip _ _ _ = error "compareZip: incompatible zips"


data ExtVars v t = OldVar v | AddrVar v (StmtZip v t) 
    deriving (Show, Eq, Functor, Foldable, Traversable)

data ForParams v t = ForParams {
    forIndexVar  :: v,
    forDataVar   :: v,
    forDataExpr  :: OExpr (ExtVars v t) t,
    forIndexAddr :: StmtZip v t
} deriving (Eq,Show)

substOVarStmt :: (Eq v) => ForParams v t -> Stmt (ExtVars v t) t -> Stmt (ExtVars v t) t
substOVarStmt p (SYield o' t) = SYield (substOVarOExpr p o') t
substOVarStmt _ (SOReturn _ _) = error "SOReturn in substOVarStmt"
substOVarStmt _ (SBReturn _ _) = error "SBReturn in substOVarStmt"
substOVarStmt p (SIf b s1 s2 t) = SIf (substOVarBExpr p b) (substOVarStmt p s1) (substOVarStmt p s2) t
substOVarStmt _ (SLetOutput _ _ _ _) = error "SLetOutput in substOVarStmt"
substOVarStmt p (SLetBoolean v' s t) = SLetBoolean v' (substOVarStmt p s) t
substOVarStmt p (SSetTrue v' t) = SSetTrue v' t
substOVarStmt p (SFor (i, e, t) v' s t') = SFor (i, e, t) v' (substOVarStmt p s) t'
substOVarStmt p (SSeq ss t) = SSeq (map (substOVarStmt p) ss) t


substOVarOExpr :: (Eq v) => ForParams v t -> OExpr (ExtVars v t) t -> OExpr (ExtVars v t) t
substOVarOExpr p (OVar (OldVar v') t) | forDataVar p == v' = forDataExpr p
substOVarOExpr p (OVar v' t) = OVar v' t
substOVarOExpr _ (OConst _ _) = error "OConst in substOVarOExpr"
substOVarOExpr _ (OList _ _) = error "OList in substOVarOExpr"
substOVarOExpr p (ORev o t) = ORev (substOVarOExpr p o) t
substOVarOExpr _ (OIndex _ _ _) = error "OIndex in substOVarOExpr"
substOVarOExpr _ (OApp _ _ _) = error "OApp in substOVarOExpr"
substOVarOExpr p (OGen s t) = OGen (substOVarStmt p s) t

substOVarBExpr :: (Eq v) => ForParams v t -> BExpr (ExtVars v t) t -> BExpr (ExtVars v t) t
substOVarBExpr p (BConst b t) = BConst b t
substOVarBExpr p (BNot b t) = BNot (substOVarBExpr p b) t
substOVarBExpr p (BOp op b1 b2 t) = BOp op (substOVarBExpr p b1) (substOVarBExpr p b2) t
substOVarBExpr p (BComp comp p1 p2 t) = BComp comp (substOVarPExpr p p1) (substOVarPExpr p p2) t
substOVarBExpr p (BVar v' t) = BVar v' t
substOVarBExpr p (BGen s t) = BGen (substOVarStmt p s) t

substOVarPExpr :: (Eq v) => ForParams v t -> PExpr (ExtVars v t) t -> PExpr (ExtVars v t) t
substOVarPExpr p (PVar (OldVar v) t) | forDataVar p == v = PVar (AddrVar v (forIndexAddr p)) t
substOVarPExpr p (PVar v t) = PVar v t




-- subYieldStmt addr i e body statement -> expanded statement
subYieldStmt :: (Eq v) => StmtZip v t -> v -> v -> Stmt (ExtVars v t) t -> Stmt (ExtVars v t) t -> Stmt (ExtVars v t) t
subYieldStmt z v1 v2 s (SYield o t) = substOVarStmt (ForParams v1 v2 o z) s
subYieldStmt _ _ _ _   (SOReturn o t) = error "SOReturn in subYield"
subYieldStmt _ _ _ _   (SBReturn b t) = error "SBReturn in subYield"
subYieldStmt z v1 v2 s (SIf b s1 s2 t) = SIf b (subYieldStmt zleft v1 v2 s s1) (subYieldStmt zright v1 v2 s s2) t
    where
        zleft  = ZIfL z
        zright = ZIfR z
subYieldStmt _ _ _ _ (SLetOutput _ _ _ _) = error "SLetOutput in subYield"
subYieldStmt z v1 v2 s (SLetBoolean v s' t) = SLetBoolean v (subYieldStmt (ZLetBoolean z) v1 v2 s s') t
subYieldStmt _ _ _ _ x@(SSetTrue _ _) = x
subYieldStmt z v1 v2 s (SFor (OldVar i, OldVar e, t) v s' t') = SFor (OldVar i, OldVar e, t) v (subYieldStmt (ZFor i t z) v1 v2 s s') t'
subYieldStmt z v1 v2 s (SSeq ss t) = SSeq [ subYieldStmt (ZSeqL i z) v1 v2 s s' | (i, s') <- zip [0..] ss ] t
subYieldStmt _ _ _ _ _ = error "subYieldStmt: invalid statement"



expandGenStmt :: (Eq v) => Stmt (ExtVars v t) t -> Stmt (ExtVars v t) t
expandGenStmt (SYield o t)   = SYield o t
expandGenStmt (SOReturn _ _) = error $ "SOReturn in expandGenStmt"
expandGenStmt (SBReturn _ _) = error $ "SBReturn in expandGenStmt"
expandGenStmt (SIf b s1 s2 t) = SIf b (expandGenStmt s1) (expandGenStmt s2) t
expandGenStmt (SLetOutput _ _ _ _) = error $ "SLetOutput in expandGenStmt"
expandGenStmt (SLetBoolean v s t) = SLetBoolean v (expandGenStmt s) t
expandGenStmt (SSetTrue v t) = SSetTrue v t
expandGenStmt (SFor (OldVar i, OldVar e, t) (OGen stmt t'') body t') = expanded
    where
        stmt' = expandGenStmt stmt
        body' = expandGenStmt body
        expanded = subYieldStmt ZBegin i e body' stmt'
expandGenStmt (SFor (OldVar i, OldVar e, t) oexpr body t') = SFor (OldVar i, OldVar e, t) oexpr (expandGenStmt body) t'
expandGenStmt (SSeq ss t) = SSeq (map expandGenStmt ss) t
expandGenStmt _ = error "expandGenStmt: invalid statement"
