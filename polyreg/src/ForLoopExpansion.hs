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

mapVarsProgram :: (va -> vb) -> Program va t -> Program vb t
mapVarsProgram f (Program fs m) = Program (map (mapVarsFun f) fs) (f m)

mapVarsFun :: (va -> vb) -> StmtFun va t -> StmtFun vb t
mapVarsFun f (StmtFun v args s t) = StmtFun (f v) newargs (mapVars f s) t
    where
        newargs = [ (f v, t, map f x) | (v, t, x) <- args ]

mapVars :: (va -> vb) -> Stmt va t -> Stmt vb t
mapVars f (SYield o t) = SYield (mapVarsOExpr f o) t
mapVars f (SOReturn o t) = SOReturn (mapVarsOExpr f o) t
mapVars f (SBReturn b t) = SBReturn (mapVarsBExpr f b) t
mapVars f (SIf b s1 s2 t) = SIf (mapVarsBExpr f b) (mapVars f s1) (mapVars f s2) t
mapVars f (SLetOutput (v, t) o s t') = SLetOutput (f v, t) (mapVarsOExpr f o) (mapVars f s) t'
mapVars f (SLetBoolean v s t) = SLetBoolean (f v) (mapVars f s) t
mapVars f (SSetTrue v t) = SSetTrue (f v) t
mapVars f (SFor (v, t, t'') o s t') = SFor (f v, f t, t'') (mapVarsOExpr f o) (mapVars f s) t'
mapVars f (SSeq ss t) = SSeq (map (mapVars f) ss) t
    
mapVarsOExpr :: (va -> vb) -> OExpr va t -> OExpr vb t
mapVarsOExpr f (OVar v t) = OVar (f v) t
mapVarsOExpr f (OConst c t) = OConst (mapVarsCExpr f c) t
mapVarsOExpr f (OList os t) = OList (map (mapVarsOExpr f) os) t
mapVarsOExpr f (ORev o t) = ORev (mapVarsOExpr f o) t
mapVarsOExpr f (OIndex o p t) = OIndex (mapVarsOExpr f o) (mapVarsPExpr f p) t
mapVarsOExpr f (OApp v os t) = OApp (f v) (mapVarsArgs f os) t
mapVarsOExpr f (OGen s t) = OGen (mapVars f s) t
    
mapVarsBExpr :: (va -> vb) -> BExpr va t -> BExpr vb t
mapVarsBExpr f (BConst b t) = BConst b t
mapVarsBExpr f (BNot b t) = BNot (mapVarsBExpr f b) t
mapVarsBExpr f (BOp op b1 b2 t) = BOp op (mapVarsBExpr f b1) (mapVarsBExpr f b2) t
mapVarsBExpr f (BComp comp p1 p2 t) = BComp comp (mapVarsPExpr f p1) (mapVarsPExpr f p2) t
mapVarsBExpr f (BVar v t) = BVar (f v) t
mapVarsBExpr f (BGen s t) = BGen (mapVars f s) t

mapVarsPExpr :: (va -> vb) -> PExpr va t -> PExpr vb t
mapVarsPExpr f (PVar v t) = PVar (f v) t

mapVarsCExpr :: (va -> vb) -> CExpr va t -> CExpr vb t
mapVarsCExpr f (CChar c t) = CChar c t
mapVarsCExpr f (CList cs t) = CList (map (mapVarsCExpr f) cs) t

mapVarsArgs :: (va -> vb) -> [(OExpr va t, [PExpr va t])] -> [(OExpr vb t, [PExpr vb t])]
mapVarsArgs f = map (\(o, ps) -> (mapVarsOExpr f o, map (mapVarsPExpr f) ps))


data StmtZip v t = 
                 ZIfL (StmtZip v t )
               | ZIfR (StmtZip v t )
               | ZFor v t (StmtZip v t )
               | ZSeqL Int (StmtZip v t ) 
               | ZBegin
               deriving (Show, Eq, Functor, Foldable, Traversable)


-- Comparison of the positions in two zips,
-- note that "ifs" and "sequences" behave the same.
compareZip :: t -> StmtZip v t -> StmtZip v t -> BExpr (ExtVars v t) t
compareZip t (ZIfL a) (ZIfL b) = compareZip t a b
compareZip t (ZIfR a) (ZIfR b) = compareZip t a b
compareZip t (ZIfL a) (ZIfR b) = BConst True t
compareZip t (ZIfR a) (ZIfL b) = BConst False t
compareZip t (ZFor v t' a) (ZFor v' t'' b) = BOp And 
                                              (BComp Leq (PVar (OldVar v) t') 
                                                         (PVar (OldVar v') t'') 
                                                      t)
                                              (compareZip t a b)
                                              t
compareZip t (ZSeqL i a) (ZSeqL j b) | i == j = compareZip t a b
compareZip t (ZSeqL i a) (ZSeqL j b) | i <  i = BConst True t
compareZip t (ZSeqL i a) (ZSeqL j b) | i >  i = BConst False t
compareZip t (ZIfL a) (ZSeqL 0 b) = compareZip t a b
compareZip t (ZIfR a) (ZSeqL 1 b) = compareZip t a b
compareZip t (ZSeqL 0 a) (ZIfL b) = compareZip t a b
compareZip t (ZSeqL 1 a) (ZIfR b) = compareZip t a b
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
subYieldStmt z v1 v2 s (SLetBoolean v s' t) = SLetBoolean v (subYieldStmt z v1 v2 s s') t
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
expandGenStmt (SFor (OldVar i, OldVar e, t) (ORev (OGen stmt _) t') body t'') = expanded
    where
        stmt' = expandGenStmt stmt
        body' = expandGenStmt body
        stmtRevSimpl = reverseAndSimplify stmt' 
        copyOfI = i -- TODO: make this unique
        guardedBody = (SIf (BComp Eq (PVar (OldVar i) t) (PVar (OldVar copyOfI) t) t) body' (SSeq [] t'') t'')

        expandRev = subYieldStmt ZBegin copyOfI e guardedBody stmtRevSimpl
        expanded = subYieldStmt ZBegin i e expandRev stmt'
expandGenStmt (SFor (OldVar i, OldVar e, t) oexpr body t') = SFor (OldVar i, OldVar e, t) oexpr (expandGenStmt body) t'
expandGenStmt (SSeq ss t) = SSeq (map expandGenStmt ss) t
expandGenStmt _ = error "expandGenStmt: invalid statement"


-- Reverses all the generators (and checks that they are only on variables)
-- removes all "letBool" and "setTrue" statements,
-- and turns `ifs` into sequences.
reverseAndSimplify :: Stmt (ExtVars v t) t -> Stmt (ExtVars v t) t
reverseAndSimplify (SYield o t) = SYield o t
reverseAndSimplify (SOReturn _ _) = error "SOReturn in reverseAndSimplify"
reverseAndSimplify (SBReturn _ _) = error "SBReturn in reverseAndSimplify"
reverseAndSimplify (SIf b s1 s2 t) = SSeq [reverseAndSimplify s1, reverseAndSimplify s2] t
reverseAndSimplify (SLetOutput _ _ _ _) = error "SLetOutput in reverseAndSimplify"
reverseAndSimplify (SLetBoolean _ s t) = reverseAndSimplify s
reverseAndSimplify (SSetTrue _ t) = SSeq [] t
reverseAndSimplify (SSeq ss t) = SSeq (map reverseAndSimplify ss) t
reverseAndSimplify (SFor (OldVar i, OldVar e, t) (OVar v t') body t'') = simplified
    where
        body' = reverseAndSimplify body
        simplified = SFor (OldVar i, OldVar e, t) (ORev (OVar v t') t') body' t''
reverseAndSimplify (SFor (OldVar i, OldVar e, t) (ORev oexpr t') body t'') = simplified
    where
        body' = reverseAndSimplify body
        simplified = SFor (OldVar i, OldVar e, t) oexpr body' t''
reverseAndSimplefy (SFor _ _ _ _) = error "SFor in reverseAndSimplify"
